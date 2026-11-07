#!/usr/bin/env python3
"""Recompute Arm A's totals and the ablation budget, correctly.

Two corrections to the first pass:

1. TOKEN ACCOUNTING.  `claude -p --output-format json` reports a top-level
   `usage` block covering only the driver's own final turn; every subagent is
   excluded.  For this harness that under-counts output tokens ~50x
   (4,592 vs 230,815).  Totals are recomputed from `modelUsage`, which
   aggregates across the planner / generator / evaluator subagents.

2. WALL-CLOCK FLOOR.  Arm A solved the anchor in ONE sprint (3,285 s), faster
   than the original 2026-05-05 run needed for the same c-push (sprints 084-088,
   04:00:25 -> 06:19:07 = 8,322 s).  Taking 3x the faster of two independent
   measurements would hand the ablations less budget than the framework itself
   originally consumed -- the opposite of the stated intent to give the
   ablations every chance.  The reference wall-clock is therefore floored at
   the original run's measured band.

Both raw numbers are retained so either budget can be recomputed.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
RUN = ROOT / "runs" / "korenblum-armA-01"

# Original 2026-05-05 anchor band, sprints 084-088 (contract 084 written ->
# verdict 088 written).  Recoverable from file mtimes; see design sect. 2.1.
ORIGINAL_BAND_S = 2 * 3600 + 18 * 60 + 42          # 8322 s
MULT = 3.0


def main():
    sprints = sorted(RUN.glob("sprint_*_result.json"))
    tot = {"in": 0, "out": 0, "cr": 0, "cw": 0, "usd": 0.0}
    per_model: dict[str, dict] = {}
    turns = 0
    for p in sprints:
        d = json.loads(p.read_text())
        turns += d.get("num_turns", 0) or 0
        for m, mu in (d.get("modelUsage") or {}).items():
            t = per_model.setdefault(
                m, {"in": 0, "out": 0, "cr": 0, "cw": 0, "usd": 0.0})
            for a, b in (("in", "inputTokens"), ("out", "outputTokens"),
                         ("cr", "cacheReadInputTokens"),
                         ("cw", "cacheCreationInputTokens")):
                t[a] += mu.get(b, 0)
                tot[a] += mu.get(b, 0)
            t["usd"] += mu.get("costUSD", 0.0)
            tot["usd"] += mu.get("costUSD", 0.0)

    summary = json.loads((RUN / "summary.json").read_text())
    wall = summary["wall_clock_s"]

    corrected = {
        **summary,
        "output_tokens": tot["out"],
        "input_tokens": tot["in"],
        "cache_read_tokens": tot["cr"],
        "cache_creation_tokens": tot["cw"],
        "model_calls_turns": turns,
        "usd_total": round(tot["usd"], 4),
        "per_model": per_model,
        "_correction": ("output/input/cache token totals recomputed from "
                        "modelUsage; the top-level `usage` block excludes "
                        "subagents and under-counted output tokens "
                        f"{summary['output_tokens']} vs {tot['out']}"),
    }
    (RUN / "summary.json").write_text(json.dumps(corrected, indent=2))

    t_ref_eff = max(wall, ORIGINAL_BAND_S)
    budget = {
        "T_ref_s": t_ref_eff,
        "O_ref_output_tokens": tot["out"],
        "usd_ref": round(tot["usd"], 4),
        "source_run": "korenblum-armA-01",
        "terminal_label": summary["terminal_label"],
        "multiplier": MULT,
        "T_budget_s": t_ref_eff * MULT,
        "O_budget_output_tokens": tot["out"] * MULT,
        "provenance": {
            "armA_measured_wall_s": wall,
            "armA_sprints_to_goal": len(sprints),
            "original_run_band_s": ORIGINAL_BAND_S,
            "original_run_band": "2026-05-05 sprints 084-088, 04:00:25->06:19:07",
            "wall_clock_floored_at_original": t_ref_eff > wall,
            "why": ("Arm A beat the original run's 5-sprint result in 1 sprint, "
                    "so 3x its wall-clock would give the ablations less time "
                    "than the framework itself originally used. Floored at the "
                    "original band to keep the ablations generously resourced."),
            "token_reference_note": ("No token data survives for the original "
                                     "run (transcripts purged), so O_ref comes "
                                     "solely from Arm A's measured modelUsage."),
        },
    }
    (ROOT / "runs" / "reference_budget.json").write_text(json.dumps(budget, indent=2))

    print(json.dumps(budget, indent=2))
    print(f"\ncorrected Arm A: out={tot['out']:,} tok  in={tot['in']:,}  "
          f"cache_read={tot['cr']:,}  ${tot['usd']:.2f}  turns={turns}")
    print(f"ablation budget: {budget['T_budget_s']/3600:.2f} h  AND  "
          f"{budget['O_budget_output_tokens']:,.0f} output tokens")


if __name__ == "__main__":
    main()
