#!/usr/bin/env python3
"""
telemetry.py — HUMAN-SIDE run accounting for the Polygon-π refinement loop.

The harness plan claimed per-model-call token and dollar accounting was not
obtainable from inside this harness. That is wrong: Claude Code writes a
per-turn transcript to

    ~/.claude/projects/<project-slug>/<session-id>.jsonl

and every `assistant` record carries `model`, `timestamp`, `isSidechain`, and a
full `usage` block (input, output, cache-creation split by TTL, cache-read). So
this script reports real LLM call counts and real dollar cost, not estimates.

Sources joined here:

  transcripts        LLM calls, tokens, cost, wall-clock, main-loop vs subagent
  results/sprint_markers.jsonl   sprint boundaries (written by the driver)
  Refinement_Log/log.jsonl       Lean compile wall/CPU/RSS per candidate
  environment/                   hardware and toolchain configuration

Outputs `results/telemetry.json` and `results/telemetry.md`.

Cost note: prices are per million tokens. Cache *writes* are billed at a
multiple of the input rate that depends on TTL — 1.25x at the 5-minute TTL and
2x at the 1-hour TTL — and the transcript reports the two separately under
`usage.cache_creation`, so each is priced correctly rather than blended. Cache
*reads* are 0.1x input.
"""

from __future__ import annotations

import json
import os
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "results"
MARKERS = OUT / "sprint_markers.jsonl"
LEAN_LOG = ROOT / "ProofRefinement" / "PolygonPi" / "Refinement_Log" / "log.jsonl"
ENVDIR = ROOT / "environment"
PROJECT_SLUG = "-home-user-pi-polygon"
TRANSCRIPT_DIR = Path.home() / ".claude" / "projects" / PROJECT_SLUG

# USD per million tokens. Cache-write multipliers: 1.25x (5m TTL), 2x (1h TTL).
# Cache read: 0.1x input.
PRICING = {
    "claude-opus-5":     {"in": 5.00, "out": 25.00},
    "claude-opus-4-8":   {"in": 5.00, "out": 25.00},
    "claude-opus-4-7":   {"in": 5.00, "out": 25.00},
    "claude-sonnet-5":   {"in": 3.00, "out": 15.00},
    "claude-sonnet-4-6": {"in": 3.00, "out": 15.00},
    "claude-haiku-4-5":  {"in": 1.00, "out":  5.00},
    "claude-fable-5":    {"in": 10.00, "out": 50.00},
}
CACHE_WRITE_1H = 2.00
CACHE_WRITE_5M = 1.25
CACHE_READ = 0.10
MTOK = 1_000_000


def parse_ts(s: str) -> datetime:
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def load_calls() -> list[dict]:
    """Every assistant turn across all transcripts for this project."""
    calls: list[dict] = []
    if not TRANSCRIPT_DIR.exists():
        return calls
    for path in sorted(TRANSCRIPT_DIR.rglob("*.jsonl")):
        for line in path.read_text(errors="replace").splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if rec.get("type") != "assistant":
                continue
            msg = rec.get("message") or {}
            usage = msg.get("usage") or {}
            if not usage:
                continue
            cc = usage.get("cache_creation") or {}
            calls.append({
                "ts": rec.get("timestamp"),
                "model": msg.get("model") or "unknown",
                "sidechain": bool(rec.get("isSidechain")),
                "session": rec.get("sessionId") or rec.get("session_id"),
                "uuid": rec.get("uuid"),
                "in": usage.get("input_tokens", 0),
                "out": usage.get("output_tokens", 0),
                "cache_read": usage.get("cache_read_input_tokens", 0),
                "cache_write_1h": cc.get("ephemeral_1h_input_tokens", 0),
                "cache_write_5m": cc.get("ephemeral_5m_input_tokens", 0),
                "cache_write_total": usage.get("cache_creation_input_tokens", 0),
            })
    calls.sort(key=lambda c: c["ts"] or "")
    return calls


def cost_of(call: dict) -> float:
    p = PRICING.get(call["model"])
    if not p:
        return 0.0
    w1h, w5m = call["cache_write_1h"], call["cache_write_5m"]
    # Fall back to the undifferentiated total if the split is absent.
    if not (w1h or w5m) and call["cache_write_total"]:
        w1h = call["cache_write_total"]
    return (
        call["in"] * p["in"]
        + call["out"] * p["out"]
        + w1h * p["in"] * CACHE_WRITE_1H
        + w5m * p["in"] * CACHE_WRITE_5M
        + call["cache_read"] * p["in"] * CACHE_READ
    ) / MTOK


def blank_bucket() -> dict:
    return {
        "llm_calls": 0, "llm_calls_main": 0, "llm_calls_subagent": 0,
        "input_tokens": 0, "output_tokens": 0,
        "cache_write_1h_tokens": 0, "cache_write_5m_tokens": 0,
        "cache_read_tokens": 0, "cost_usd": 0.0,
        "by_model": defaultdict(lambda: {"calls": 0, "output_tokens": 0, "cost_usd": 0.0}),
    }


def add(bucket: dict, call: dict) -> None:
    c = cost_of(call)
    bucket["llm_calls"] += 1
    bucket["llm_calls_subagent" if call["sidechain"] else "llm_calls_main"] += 1
    bucket["input_tokens"] += call["in"]
    bucket["output_tokens"] += call["out"]
    bucket["cache_write_1h_tokens"] += call["cache_write_1h"]
    bucket["cache_write_5m_tokens"] += call["cache_write_5m"]
    bucket["cache_read_tokens"] += call["cache_read"]
    bucket["cost_usd"] += c
    m = bucket["by_model"][call["model"]]
    m["calls"] += 1
    m["output_tokens"] += call["out"]
    m["cost_usd"] += c


def finalize(bucket: dict) -> dict:
    bucket["cost_usd"] = round(bucket["cost_usd"], 4)
    bucket["by_model"] = {
        k: {**v, "cost_usd": round(v["cost_usd"], 4)}
        for k, v in sorted(bucket["by_model"].items())
    }
    bucket["total_tokens"] = (
        bucket["input_tokens"] + bucket["output_tokens"]
        + bucket["cache_write_1h_tokens"] + bucket["cache_write_5m_tokens"]
        + bucket["cache_read_tokens"]
    )
    return bucket


def load_markers() -> list[dict]:
    if not MARKERS.exists():
        return []
    out = []
    for line in MARKERS.read_text().splitlines():
        line = line.strip()
        if line:
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return out


def hardware() -> dict:
    def read(name: str) -> str:
        p = ENVDIR / name
        return p.read_text().strip() if p.exists() else ""

    lscpu = read("lscpu.txt")

    def field(label: str) -> str:
        m = re.search(rf"^{re.escape(label)}:\s*(.+)$", lscpu, re.MULTILINE)
        return m.group(1).strip() if m else ""

    mem = read("memory.txt")
    total_mem = ""
    for line in mem.splitlines():
        if line.startswith("Mem:"):
            total_mem = line.split()[1]
            break
    return {
        "cpu_model": field("Model name"),
        "cpu_cores": field("CPU(s)"),
        "threads_per_core": field("Thread(s) per core"),
        "sockets": field("Socket(s)"),
        "cpu_max_mhz": field("CPU max MHz"),
        "memory_total": total_mem,
        "kernel": read("uname.txt"),
        "lean": read("lean_version.txt"),
        "lake": read("lake_version.txt"),
        "elan": read("elan_version.txt"),
        "mathlib_commit": read("mathlib_commit.txt"),
        "python": read("python_version.txt"),
        "uv": read("uv_version.txt"),
    }


def lean_metrics() -> list[dict]:
    if not LEAN_LOG.exists():
        return []
    out = []
    for line in LEAN_LOG.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        out.append({
            "candidate": r.get("candidate"),
            "pass": r.get("pass"),
            "score": r.get("score"),
            "compile_elapsed_s": r.get("compile_elapsed_s"),
            "user_cpu_s": r.get("user_cpu_s"),
            "sys_cpu_s": r.get("sys_cpu_s"),
            "max_rss_kb": r.get("max_rss_kb"),
            "typecheck_elapsed_s": r.get("typecheck_elapsed_s"),
            "timestamp_utc": r.get("timestamp_utc"),
        })
    return out


def main() -> None:
    calls = load_calls()
    markers = load_markers()

    # Sprint windows: [start, end) pairs from the marker file.
    windows = []
    open_start = None
    for m in markers:
        if m.get("event") == "sprint_start":
            open_start = m
        elif m.get("event") == "sprint_end" and open_start is not None:
            windows.append({
                "sprint": open_start.get("sprint"),
                "start": open_start.get("ts"),
                "end": m.get("ts"),
                "outcome": m.get("outcome", ""),
                "note": m.get("note", ""),
            })
            open_start = None
    if open_start is not None:
        windows.append({
            "sprint": open_start.get("sprint"), "start": open_start.get("ts"),
            "end": None, "outcome": "in_progress", "note": "",
        })

    per_sprint = []
    for w in windows:
        b = blank_bucket()
        t0 = parse_ts(w["start"]) if w["start"] else None
        t1 = parse_ts(w["end"]) if w["end"] else datetime.now(timezone.utc)
        for c in calls:
            if not c["ts"]:
                continue
            t = parse_ts(c["ts"])
            if t0 and t0 <= t < t1:
                add(b, c)
        wall = (t1 - t0).total_seconds() if t0 else None
        per_sprint.append({**w, "wall_clock_s": round(wall, 1) if wall else None,
                           **finalize(b)})

    # Whole-run totals over the sprint windows only (excludes build-out work).
    run = blank_bucket()
    for w in windows:
        t0 = parse_ts(w["start"]) if w["start"] else None
        t1 = parse_ts(w["end"]) if w["end"] else datetime.now(timezone.utc)
        for c in calls:
            if c["ts"] and t0 and t0 <= parse_ts(c["ts"]) < t1:
                add(run, c)
    run = finalize(run)

    # Session-wide totals, including the harness build-out.
    session = blank_bucket()
    for c in calls:
        add(session, c)
    session = finalize(session)

    report = {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "pricing_usd_per_mtok": {
            **{k: v for k, v in PRICING.items()},
            "_cache_write_multiplier_1h": CACHE_WRITE_1H,
            "_cache_write_multiplier_5m": CACHE_WRITE_5M,
            "_cache_read_multiplier": CACHE_READ,
        },
        "hardware": hardware(),
        "sprints": per_sprint,
        "run_totals_sprints_only": run,
        "session_totals_including_harness_buildout": session,
        "lean_compiles": lean_metrics(),
        "transcript_files": [str(p) for p in sorted(TRANSCRIPT_DIR.rglob("*.jsonl"))]
        if TRANSCRIPT_DIR.exists() else [],
    }

    (OUT / "telemetry.json").write_text(json.dumps(report, indent=2) + "\n")

    # ── markdown
    hw = report["hardware"]
    L: list[str] = []
    L.append("# Polygon-π run telemetry\n")
    L.append(f"Generated {report['generated_utc']}.\n")

    L.append("\n## Hardware and toolchain\n")
    L.append("| | |")
    L.append("|---|---|")
    L.append(f"| CPU | {hw['cpu_model']} |")
    L.append(f"| Logical CPUs | {hw['cpu_cores']} ({hw['threads_per_core']} thread/core, {hw['sockets']} socket) |")
    L.append(f"| CPU max MHz | {hw['cpu_max_mhz']} |")
    L.append(f"| Memory | {hw['memory_total']} |")
    L.append(f"| Kernel | `{hw['kernel']}` |")
    L.append(f"| Lean | {hw['lean']} |")
    L.append(f"| Lake | {hw['lake']} |")
    L.append(f"| Mathlib | `{hw['mathlib_commit']}` |")
    L.append(f"| Python / uv | {hw['python']} / {hw['uv']} |")

    L.append("\n## Per-sprint\n")
    if per_sprint:
        L.append("| sprint | wall clock | LLM calls | main | subagent | output tok | cache read tok | cost USD | outcome |")
        L.append("|---|---:|---:|---:|---:|---:|---:|---:|---|")
        for s in per_sprint:
            wc = f"{s['wall_clock_s'] / 60:.1f} min" if s["wall_clock_s"] else "-"
            L.append(
                f"| {s['sprint']} | {wc} | {s['llm_calls']} | {s['llm_calls_main']} "
                f"| {s['llm_calls_subagent']} | {s['output_tokens']:,} "
                f"| {s['cache_read_tokens']:,} | ${s['cost_usd']:.2f} | {s['outcome']} |"
            )
    else:
        L.append("_No sprint markers recorded yet._")

    L.append("\n## Run totals (sprint windows only)\n")
    L.append("| metric | value |")
    L.append("|---|---:|")
    L.append(f"| sprints | {len(per_sprint)} |")
    L.append(f"| LLM calls | {run['llm_calls']} |")
    L.append(f"| — main loop | {run['llm_calls_main']} |")
    L.append(f"| — subagents | {run['llm_calls_subagent']} |")
    L.append(f"| input tokens | {run['input_tokens']:,} |")
    L.append(f"| output tokens | {run['output_tokens']:,} |")
    L.append(f"| cache-write tokens (1h) | {run['cache_write_1h_tokens']:,} |")
    L.append(f"| cache-write tokens (5m) | {run['cache_write_5m_tokens']:,} |")
    L.append(f"| cache-read tokens | {run['cache_read_tokens']:,} |")
    L.append(f"| total tokens | {run['total_tokens']:,} |")
    L.append(f"| **cost** | **${run['cost_usd']:.2f}** |")
    if run["by_model"]:
        L.append("\nBy model:\n")
        L.append("| model | calls | output tok | cost USD |")
        L.append("|---|---:|---:|---:|")
        for m, v in run["by_model"].items():
            L.append(f"| `{m}` | {v['calls']} | {v['output_tokens']:,} | ${v['cost_usd']:.2f} |")

    L.append("\n## Lean compute\n")
    lm = [x for x in report["lean_compiles"] if x.get("compile_elapsed_s")]
    if lm:
        L.append("| candidate | pass | score | compile s | user CPU s | sys CPU s | max RSS MB |")
        L.append("|---|---|---|---:|---:|---:|---:|")
        for x in lm:
            rss = f"{x['max_rss_kb'] / 1024:.0f}" if x.get("max_rss_kb") else "-"
            L.append(
                f"| `{Path(x['candidate']).stem}` | {x['pass']} | {x['score']} "
                f"| {x['compile_elapsed_s']} | {x.get('user_cpu_s', '-')} "
                f"| {x.get('sys_cpu_s', '-')} | {rss} |"
            )
        tot = sum(x["compile_elapsed_s"] for x in lm)
        cpu = sum(x.get("user_cpu_s") or 0 for x in lm) + sum(x.get("sys_cpu_s") or 0 for x in lm)
        L.append(f"\nTotal Lean compile wall clock {tot:.1f} s; CPU {cpu:.1f} s.")
    else:
        L.append("_No compile metrics logged yet._")

    L.append("\n## Session totals, including the harness build-out\n")
    L.append(
        f"{session['llm_calls']} LLM calls, {session['output_tokens']:,} output tokens, "
        f"**${session['cost_usd']:.2f}** total. This covers everything in the project's "
        "transcripts — designing and building the harness as well as running sprints — so "
        "it is the number to quote for total project cost, not per-sprint cost."
    )

    L.append("\n## Method and caveats\n")
    L.append(
        "- Token counts and models are read from Claude Code's own per-turn transcripts, "
        "so LLM call counts and token totals are exact rather than estimated."
    )
    L.append(
        "- Dollar figures are computed from published per-MTok list prices and are therefore "
        "an accurate reconstruction of list cost, not a billing record. Any negotiated rate, "
        "subscription bundling, or free-tier allowance is not reflected."
    )
    L.append(
        "- Cache writes are priced by TTL (2x input at 1h, 1.25x at 5m) using the split the "
        "transcript reports; cache reads at 0.1x input."
    )
    L.append(
        "- Sprint attribution is by wall-clock window from `results/sprint_markers.jsonl`. "
        "Anything running concurrently in the same project would land in the same window."
    )
    L.append(
        "- Lean compile CPU and RSS come from `/usr/bin/time -v` around `lake build`, "
        "recorded per evaluation in `log.jsonl`."
    )

    (OUT / "telemetry.md").write_text("\n".join(L) + "\n")
    print(f"wrote {OUT / 'telemetry.json'} and {OUT / 'telemetry.md'}")
    print(f"sprints: {len(per_sprint)}  run cost: ${run['cost_usd']:.2f}  "
          f"session cost: ${session['cost_usd']:.2f}")


if __name__ == "__main__":
    main()
