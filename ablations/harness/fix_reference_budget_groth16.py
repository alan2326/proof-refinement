#!/usr/bin/env python3
"""Recompute sprint-016 Arm A totals from modelUsage and write the matched
1x budget (sect. 10c corrections + sect. 13 user decisions).

  T_ref = max(armA wall, 2,360 s original band [S0^16 -> verdict_017 salvage])
  Budget rule (user decision 2026-07-29): B and C run CONCURRENTLY with A and
  stop at wall > 1.0 x T_ref (time-gated matched window). Token totals are
  recorded for the report but do not gate (they are unknowable mid-flight).
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
RUN = ROOT / "runs" / "grothendieck016-armA-01"

ORIGINAL_BAND_S = 2360
MULT = 1.0


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
        "_correction": ("token totals recomputed from modelUsage; the "
                        "top-level `usage` block excludes subagents "
                        f"({summary['output_tokens']} vs {tot['out']})"),
    }
    (RUN / "summary.json").write_text(json.dumps(corrected, indent=2))

    t_ref_eff = max(wall, ORIGINAL_BAND_S)
    budget = {
        "T_ref_s": t_ref_eff,
        "O_ref_output_tokens": tot["out"],
        "usd_ref": round(tot["usd"], 4),
        "source_run": "grothendieck016-armA-01",
        "terminal_label": summary["terminal_label"],
        "multiplier": MULT,
        "T_budget_s": t_ref_eff * MULT,
        "O_budget_output_tokens": tot["out"] * MULT,
        "gating": "TIME ONLY (concurrent matched window); tokens recorded",
        "provenance": {
            "armA_measured_wall_s": wall,
            "armA_sprints_to_goal": len(sprints),
            "original_run_band_s": ORIGINAL_BAND_S,
            "original_run_band": ("2026-04-30 sprints 016+017(salvage), git "
                                  "commits 5db00044 (07:40:56Z) -> 410a45c1 "
                                  "(08:20:16Z); corrects sect. 13.1's 1,837 s "
                                  "draft (verdict_016 alone, which was a G3 "
                                  "FAIL)"),
            "wall_clock_floored_at_original": t_ref_eff > wall,
            "why": ("never hand the ablations less wall clock than the "
                    "original framework consumed for the anchor (sect. 10c "
                    "correction 2); 1x multiplier + concurrency: user "
                    "decision 2026-07-29"),
        },
    }
    (ROOT / "runs" / "reference_budget_groth16.json").write_text(
        json.dumps(budget, indent=2))
    print(json.dumps(budget, indent=2))


if __name__ == "__main__":
    main()
