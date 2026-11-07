#!/usr/bin/env python3
"""Combine grothendieck016-armA-01 and -02 into the final matched 1x budget.

-01 lost sprint attempts 2..8 to the claude.ai session limit; -02 (the
continuation, run_arm_a_groth16_cont.py) granted the remaining attempts with
limit stalls excluded from its wall clock.  The reference wall is therefore

  T_A = wall(-01, as published: 4310.4 s, error-burn tail included)
      + wall(-02, active only: stalls already subtracted by the runner)
  T_ref = max(T_A, 2360 s original band)

Keeping -01's error-burn tail (~1000 s in which A could do nothing) is
deliberate: B and C already consumed that window concurrently, so removing
it retroactively would shrink T_ref below time the comparison arms were
actually given.  It is generous to B/C, i.e. conservative for any claim
about A.  Token totals are recomputed from modelUsage across every sprint
and stall result file of both runs (sect. 10c: top-level `usage` excludes
subagents).

Run AFTER -02 finishes, BEFORE any B/C window extension.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
RUNS = [ROOT / "runs" / "grothendieck016-armA-01",
        ROOT / "runs" / "grothendieck016-armA-02"]

ORIGINAL_BAND_S = 2360
MULT = 1.0


def main():
    tot = {"in": 0, "out": 0, "cr": 0, "cw": 0, "usd": 0.0}
    per_model: dict[str, dict] = {}
    turns = 0
    walls, labels, sprint_counts = {}, {}, {}
    for run in RUNS:
        files = sorted(run.glob("sprint_*_result.json")) + \
                sorted(run.glob("stall_*_result.json"))
        sprint_counts[run.name] = len(list(run.glob("sprint_*_result.json")))
        for p in files:
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
        s = json.loads((run / "summary.json").read_text())
        walls[run.name] = s["wall_clock_s"]
        labels[run.name] = s["terminal_label"]

    t_a = round(sum(walls.values()), 1)
    t_ref_eff = max(t_a, ORIGINAL_BAND_S)
    label = labels["grothendieck016-armA-02"]      # the completed attempt set

    budget = {
        "T_ref_s": t_ref_eff,
        "O_ref_output_tokens": tot["out"],
        "usd_ref": round(tot["usd"], 4),
        "source_run": "grothendieck016-armA-01 + grothendieck016-armA-02",
        "terminal_label": label,
        "multiplier": MULT,
        "T_budget_s": t_ref_eff * MULT,
        "O_budget_output_tokens": tot["out"] * MULT,
        "gating": "TIME ONLY (matched window); tokens recorded",
        "provenance": {
            "armA_wall_s_by_run": walls,
            "armA_sprint_files_by_run": sprint_counts,
            "armA_combined_wall_s": t_a,
            "interruption": (
                "-01 sprints 2..8 starved by the claude.ai session limit "
                "(reset 19:30 UTC 2026-07-29); -02 granted the remaining "
                "attempts, limit stalls excluded from its wall clock "
                "(stall_total_s in its summary)"),
            "error_burn_tail_kept": (
                "-01's post-limit error-burn tail stays in T_ref because "
                "B/C already consumed that window concurrently; generous "
                "to B/C, conservative for A"),
            "original_run_band_s": ORIGINAL_BAND_S,
            "wall_clock_floored_at_original": t_ref_eff > t_a,
            "why": ("never hand the ablations less wall clock than the "
                    "original framework consumed for the anchor (sect. 10c "
                    "correction 2); 1x multiplier: user decision 2026-07-29"),
        },
    }
    (ROOT / "runs" / "reference_budget_groth16.json").write_text(
        json.dumps(budget, indent=2))
    print(json.dumps(budget, indent=2))


if __name__ == "__main__":
    main()
