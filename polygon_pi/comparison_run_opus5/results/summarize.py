#!/usr/bin/env python3
"""
summarize.py — HUMAN-SIDE reporting for the Polygon-π refinement run.

Not part of the loop, and never written by an agent. Reads

  ProofRefinement/PolygonPi/Refinement_Log/log.jsonl     the evaluator's records
  ProofRefinement/PolygonPi/Refinement_Log/verdict_*.md  rung type and side
  validation-private/floor.json                          the analytic floors

and writes `results/frontier.csv`, `results/summary.md`, and a
`results/human_effort.csv` skeleton.

The floor constants live outside the workspace on purpose: `gap_to_floor` is a
human-side column, so nothing agent-visible reveals the target.
"""

from __future__ import annotations

import csv
import json
import math
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOG = ROOT / "ProofRefinement" / "PolygonPi" / "Refinement_Log" / "log.jsonl"
VERDICT_DIR = ROOT / "ProofRefinement" / "PolygonPi" / "Refinement_Log"
CONTRACT_DIR = ROOT / "ProofRefinement" / "PolygonPi" / "Sprint_Contracts"
FLOOR = ROOT / "validation-private" / "floor.json"
OUT = ROOT / "results"

BENCHMARK_DEPTH = 10


def frac(s) -> Fraction:
    s = str(s).strip()
    if "/" in s:
        n, d = s.split("/", 1)
        return Fraction(int(n), int(d))
    return Fraction(int(s))


def load_records() -> list[dict]:
    if not LOG.exists():
        return []
    out = []
    for line in LOG.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            out.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    return out


def load_floors() -> dict:
    if not FLOOR.exists():
        return {}
    return json.loads(FLOOR.read_text())


_FIELD_RE = {
    "rung_type": re.compile(r"^\s*\*{0,2}Rung type:?\*{0,2}\s*`?([a-z]+)`?", re.MULTILINE | re.IGNORECASE),
    "side": re.compile(r"^\s*\*{0,2}Side:?\*{0,2}\s*`?([a-z]+)`?", re.MULTILINE | re.IGNORECASE),
}


def sprint_metadata() -> dict[str, dict[str, str]]:
    """Map candidate stem -> {rung_type, side, sprint} from verdicts and contracts."""
    meta: dict[str, dict[str, str]] = {}
    for path in sorted(VERDICT_DIR.glob("verdict_*.md")) + sorted(CONTRACT_DIR.glob("sprint_*.md")):
        text = path.read_text()
        cands = re.findall(r"Candidates/(\w+)\.lean", text)
        sprint = re.search(r"(sprint_\d+[\w-]*)", path.name)
        entry = {
            "sprint": sprint.group(1) if sprint else "",
            "rung_type": "",
            "side": "",
        }
        for key, rx in _FIELD_RE.items():
            m = rx.search(text)
            if m:
                entry[key] = m.group(1).lower()
        for c in set(cands):
            meta.setdefault(c, {"sprint": "", "rung_type": "", "side": ""})
            for k, v in entry.items():
                if v and not meta[c].get(k):
                    meta[c][k] = v
    return meta


def main() -> None:
    records = load_records()
    floors = load_floors()
    meta = sprint_metadata()
    OUT.mkdir(exist_ok=True)

    kap_floor = Fraction(floors["kappa_floor"]) if floors.get("kappa_floor") else None
    lam_ceil = Fraction(floors["lambda_ceiling"]) if floors.get("lambda_ceiling") else None
    score_floor = Fraction(floors["score_floor"]) if floors.get("score_floor") else None

    rows = []
    best = None
    for rec in records:
        stem = Path(rec.get("candidate", "")).stem
        m = meta.get(stem, {})
        row = {
            "sprint": m.get("sprint", ""),
            "candidate": rec.get("candidate", ""),
            "pass": rec.get("pass"),
            "reason": rec.get("reason", ""),
            "kappa_exact": rec.get("kappa", ""),
            "lambda_exact": rec.get("lambda", ""),
            "score_exact": rec.get("score", ""),
            "score_decimal": "",
            "interval_width_depth10_exact": rec.get("interval_width_at_depth10", ""),
            "interval_width_depth10_decimal": "",
            "gap_to_floor": "",
            "neg_log10_gap": "",
            "kappa_gap_to_floor": "",
            "lambda_gap_to_ceiling": "",
            "score_depth10": rec.get("score_secondary", ""),
            "rung_type": m.get("rung_type", ""),
            "side": m.get("side", ""),
            "strict_improvement": rec.get("strict_improvement", ""),
            "compile_s": rec.get("compile_elapsed_s", ""),
            "max_rss_mb": (
                round(rec["max_rss_kb"] / 1024, 1) if rec.get("max_rss_kb") else ""
            ),
            "axioms": ";".join(rec.get("axioms_used", []) or []),
            "sha256": rec.get("sha256", ""),
        }
        if rec.get("pass") and rec.get("score"):
            s = frac(rec["score"])
            row["score_decimal"] = f"{float(s):.12f}"
            if rec.get("interval_width_at_depth10"):
                row["interval_width_depth10_decimal"] = (
                    f"{float(frac(rec['interval_width_at_depth10'])):.6e}"
                )
            if score_floor is not None:
                gap = s - score_floor
                row["gap_to_floor"] = f"{float(gap):.12f}"
                if gap > 0:
                    row["neg_log10_gap"] = f"{-math.log10(float(gap)):.3f}"
            if kap_floor is not None and rec.get("kappa"):
                row["kappa_gap_to_floor"] = f"{float(frac(rec['kappa']) - kap_floor):.12f}"
            if lam_ceil is not None and rec.get("lambda"):
                row["lambda_gap_to_ceiling"] = f"{float(lam_ceil - frac(rec['lambda'])):.12f}"
            if best is None or s < frac(best["score"]):
                best = rec
        rows.append(row)

    # ── frontier.csv
    fields = list(rows[0].keys()) if rows else []
    with (OUT / "frontier.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    # ── human_effort.csv skeleton
    effort_path = OUT / "human_effort.csv"
    if not effort_path.exists():
        with effort_path.open("w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["phase", "activity", "hours", "estimated", "notes"])
            w.writerow(["0", "bootstrap: Mathlib copy, stripping, git init", "", "yes", ""])
            w.writerow(["1", "trusted Lean surface", "", "yes", ""])
            w.writerow(["2", "V0 baseline proof", "", "yes", ""])
            w.writerow(["3", "reachability references", "", "yes", ""])
            w.writerow(["4", "harness infrastructure", "", "yes", ""])
            w.writerow(["5", "pilot sprint", "", "yes", ""])
            w.writerow(["6", "long run supervision", "", "yes", ""])
            w.writerow(["7", "reporting", "", "yes", ""])

    # ── summary.md
    passing = [r for r in records if r.get("pass")]
    failing = [r for r in records if not r.get("pass")]
    by_rung: dict[str, int] = {}
    by_side: dict[str, int] = {}
    for r in rows:
        if r["pass"] and r["strict_improvement"] is True:
            by_rung[r["rung_type"] or "unlabelled"] = by_rung.get(r["rung_type"] or "unlabelled", 0) + 1
            by_side[r["side"] or "unlabelled"] = by_side.get(r["side"] or "unlabelled", 0) + 1

    lines: list[str] = []
    lines.append("# Polygon-π refinement — results summary\n")
    lines.append(f"Generated from `{LOG.relative_to(ROOT)}`.\n")
    lines.append(f"Benchmark depth {BENCHMARK_DEPTH} — the inscribed regular "
                 f"{2 ** (BENCHMARK_DEPTH + 2)}-gon.\n")

    lines.append("\n## Headline\n")
    if best:
        s = frac(best["score"])
        width = frac(best.get("interval_width_at_depth10", "0"))
        lines.append(f"- best candidate: `{best.get('candidate')}`")
        lines.append(f"- `kappa = {best.get('kappa')}`, `lambda = {best.get('lambda')}`")
        lines.append(f"- score `kappa - lambda = {best.get('score')}` = {float(s):.12f}")
        lines.append(f"- reported interval width = `{width}` = {float(width):.6e}")
        if score_floor is not None:
            lines.append(f"- gap to analytic floor = {float(s - score_floor):.12f}")
            lines.append(f"- improvement over the baseline score of 1: "
                         f"{float(1 / s):.4f}x")
            lines.append(f"- of a total available headroom of "
                         f"{float(1 / score_floor):.4f}x")
        lines.append(f"- axiom closure: `{', '.join(best.get('axioms_used', []))}`")
    else:
        lines.append("- no passing candidate yet")

    lines.append("\n## The reported theorem\n")
    if best:
        lines.append("```")
        lines.append("polygonLower 10 + lambda / 4 ^ 10  <  π  <  polygonLower 10 + kappa / 4 ^ 10")
        lines.append(f"lambda = {best.get('lambda')}")
        lines.append(f"kappa  = {best.get('kappa')}")
        lines.append(f"width  = {best.get('interval_width_at_depth10')}")
        lines.append("```")

    lines.append("\n## Sprint counts\n")
    lines.append(f"- log records: {len(records)}")
    lines.append(f"- passing: {len(passing)}")
    lines.append(f"- failing: {len(failing)}")
    if by_rung:
        lines.append("- improvements by rung type: " +
                     ", ".join(f"{k} {v}" for k, v in sorted(by_rung.items())))
    if by_side:
        lines.append("- improvements by side: " +
                     ", ".join(f"{k} {v}" for k, v in sorted(by_side.items())))

    if failing:
        lines.append("\n## Failure modes\n")
        tally: dict[str, int] = {}
        for r in failing:
            tally[r.get("reason", "unknown")] = tally.get(r.get("reason", "unknown"), 0) + 1
        for reason, count in sorted(tally.items(), key=lambda kv: -kv[1]):
            lines.append(f"- {count}x {reason}")

    lines.append("\n## Frontier trajectory\n")
    lines.append("| candidate | kappa | lambda | score | width @ depth 10 | rung | side | improved |")
    lines.append("|---|---|---|---|---|---|---|---|")
    for r in rows:
        if not r["pass"]:
            continue
        lines.append(
            f"| `{Path(r['candidate']).stem}` | {r['kappa_exact']} | {r['lambda_exact']} "
            f"| {r['score_exact']} | {r['interval_width_depth10_decimal']} "
            f"| {r['rung_type']} | {r['side']} | {r['strict_improvement']} |"
        )

    lines.append("\n## Replay\n")
    lines.append("```bash")
    lines.append("./ProofRefinement/PolygonPi/scripts/verify_all.sh")
    lines.append("```")

    lines.append("\n## Known limitation\n")
    lines.append(
        "Per-model-call token and dollar accounting is not obtainable from inside "
        "this harness, so cost reporting is wall-clock and Lean-compile CPU only."
    )

    (OUT / "summary.md").write_text("\n".join(lines) + "\n")

    print(f"wrote {OUT / 'frontier.csv'} ({len(rows)} rows)")
    print(f"wrote {OUT / 'summary.md'}")
    if best:
        print(f"best score: {best.get('score')}  width: {best.get('interval_width_at_depth10')}")


if __name__ == "__main__":
    main()
