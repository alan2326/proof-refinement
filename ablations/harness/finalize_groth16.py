#!/usr/bin/env python3
"""Write summary.json for a hard-killed sprint-016 arm from its events.jsonl.

Only needed if a runner was SIGKILLed before its own SIGTERM handler could
call Run.finish() (the runners finalize themselves on SIGTERM).

Usage: python3 harness/finalize_groth16.py <run_id> [<run_id> ...]
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
sys.path.insert(0, str(ROOT / "harness"))
from groth_common import best_score  # noqa: E402


def finalize(run_id: str):
    d = ROOT / "runs" / run_id
    if (d / "summary.json").exists():
        print(f"[finalize] {run_id}: summary.json already present, skipping")
        return
    manifest = json.loads((d / "manifest.json").read_text())
    ws = Path(manifest["workspace"])
    tot = {"in": 0, "out": 0, "cr": 0, "cw": 0}
    usd = 0.0
    calls = evals = fails = 0
    wall = 0.0
    for line in (d / "events.jsonl").read_text().splitlines():
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        wall = max(wall, e.get("elapsed_s", 0.0))
        mu_all = e.get("model_usage") or {}
        for mu in mu_all.values():
            tot["in"] += mu.get("inputTokens", 0)
            tot["out"] += mu.get("outputTokens", 0)
            tot["cr"] += mu.get("cacheReadInputTokens", 0)
            tot["cw"] += mu.get("cacheCreationInputTokens", 0)
        if not mu_all and e.get("usage"):
            u = e["usage"]
            tot["in"] += u.get("input_tokens", 0)
            tot["out"] += u.get("output_tokens", 0)
            tot["cr"] += u.get("cache_read_input_tokens", 0)
            tot["cw"] += u.get("cache_creation_input_tokens", 0)
        usd += e.get("cost_usd") or 0.0
        calls += e.get("num_turns") or 0
        if e.get("kind") in ("sprint", "iteration"):
            evals = max(evals, e.get("evaluator_runs") or 0)
            fails = max(fails, e.get("evaluator_failures") or 0)
    summary = {
        "run_id": run_id, "arm": manifest.get("arm"),
        "terminal_label": "D5",
        "evidence": ("hard-killed at the 1x matched wall-clock window "
                     f"(finalized post-hoc from events.jsonl); best="
                     f"{best_score(ws)}"),
        "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "best_score": str(best_score(ws)),
        "wall_clock_s": wall,
        "output_tokens": tot["out"], "input_tokens": tot["in"],
        "cache_read_tokens": tot["cr"], "cache_creation_tokens": tot["cw"],
        "model_calls_turns": calls, "usd_total": round(usd, 4),
        "evaluator_runs": evals, "failed_attempts": fails,
        "_finalized_by": "finalize_groth16.py",
    }
    (d / "summary.json").write_text(json.dumps(summary, indent=2))
    print(f"[finalize] {run_id}: wrote summary ({summary['terminal_label']}, "
          f"best={summary['best_score']})")


if __name__ == "__main__":
    for rid in sys.argv[1:]:
        finalize(rid)
