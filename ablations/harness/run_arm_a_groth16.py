#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm A -- the full, unmodified proof-refinement
harness, driven headlessly sprint by sprint until an accepted candidate
reaches the BAR (sect. 13.2 uniform bar), a max-sprint cap, or a hard cap.

The workspace itself is untouched S0^16 (the framework is not told the BAR;
its own Bulletin cadence already demands Cr reduction every sprint -- the
harness simply keeps invoking sprints until the bar is crossed). Wall clock
and modelUsage output tokens become T_ref / O_ref for the matched-window
budgets of Arms B and C.

Usage:  python3 harness/run_arm_a_groth16.py [--max-sprints N]
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth16_common import (ROOT, Run, bar, bar_reached, best_score,  # noqa: E402
                            count_log_rows, improved, reap_orphaned_claude,
                            ORIGINAL_BAND_S)
from run_arm_a_groth import run_one_sprint, DRIVER_PROMPT  # noqa: E402

REF_BUDGET = ROOT / "runs" / "reference_budget_groth16.json"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armA"))
    ap.add_argument("--run-id", default="grothendieck016-armA-01")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--max-sprints", type=int, default=8)
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    a = ap.parse_args()

    n = reap_orphaned_claude()
    if n:
        print(f"[armA16] reaped {n} orphaned claude proc(s)")
    ws = Path(a.workspace)
    assert ws.exists(), f"workspace missing: {ws}"

    run = Run(a.run_id, "A", ws, meta_extra={
        "role": "reference",
        "driver": DRIVER_PROMPT,
        "driver_model": a.model,
        "subagent_models": {"planner": "opus", "generator": "opus",
                            "evaluator": "sonnet"},
        "stopping_rule": "accepted Cr_val <= BAR, or max-sprints/hard cap",
        "budget": {"rule": "this arm DEFINES T_ref and O_ref",
                   "max_sprints": a.max_sprints},
    })
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    print(f"[armA16] run_id={a.run_id} ws={ws}")
    print(f"[armA16] start score={best_score(ws)}  BAR={bar()} "
          f"(~{float(bar()):.3g})")

    prev_best = best_score(ws)
    label, evidence = "D5", "stopped without reaching BAR"
    for k in range(1, a.max_sprints + 1):
        if run.wall > a.hard_cap_h * 3600:
            label, evidence = "D5", f"hard cap {a.hard_cap_h}h"
            break

        t0 = time.time()
        print(f"[armA16] sprint attempt {k} (elapsed {run.wall/60:.1f} min, "
              f"${run.usd:.2f}, out_tok={run.tok_out})", flush=True)
        try:
            res, _ = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
        except subprocess.TimeoutExpired:
            run.emit("driver_timeout", attempt=k, timeout_min=a.sprint_timeout_min)
            run.failed += 1
            continue

        run.account(res)
        evals, fails = count_log_rows(ws)
        run.evals, run.failed = evals - base_evals, fails - base_fails
        run.emit("sprint", attempt=k,
                 session_id=res.get("session_id"),
                 is_error=res.get("is_error"),
                 num_turns=res.get("num_turns"),
                 duration_ms=res.get("duration_ms"),
                 cost_usd=res.get("total_cost_usd"),
                 usage=res.get("usage"),
                 model_usage=res.get("modelUsage"),
                 permission_denials=res.get("permission_denials"),
                 wall_s=round(time.time() - t0, 1),
                 best_score_after=str(best_score(ws)),
                 evaluator_runs=evals - base_evals,
                 evaluator_failures=fails - base_fails,
                 result_tail=(res.get("result") or "")[-1500:])
        (run.dir / f"sprint_{k:03d}_result.json").write_text(json.dumps(res, indent=2))
        print(f"       -> turns={res.get('num_turns')} "
              f"${res.get('total_cost_usd', 0):.3f} "
              f"score={best_score(ws)} evals=+{evals-base_evals} "
              f"fails=+{fails-base_fails}", flush=True)
        run.snapshot_transcripts()

        cur = best_score(ws)
        if cur is not None and cur != prev_best:
            run.emit("new_best", attempt=k, score=str(cur),
                     score_float=float(cur), wall_s=round(run.wall, 1),
                     output_tokens=run.tok_out, usd=round(run.usd, 3),
                     below_bar=bool(cur <= bar()))
            print(f"[armA16] NEW BEST: {cur} = {float(cur):.3e} "
                  f"(BAR {float(bar()):.3e})", flush=True)
            prev_best = cur

        if bar_reached(ws):
            label = "S"
            evidence = (f"evaluator accepted score {best_score(ws)} <= BAR "
                        f"{bar()} after {k} sprint(s)")
            print(f"[armA16] BAR REACHED: {evidence}")
            break
    else:
        label, evidence = "D5", (f"max sprints ({a.max_sprints}) reached; "
                                 f"best={best_score(ws)}")
        if improved(ws):
            evidence += " (within-envelope improvement only)"

    summary = run.finish(label, evidence)
    print(json.dumps(summary, indent=2))

    ref = {"T_ref_s": max(summary["wall_clock_s"], ORIGINAL_BAND_S),
           "T_armA_measured_s": summary["wall_clock_s"],
           "O_ref_output_tokens": summary["output_tokens"],
           "usd_ref": summary["usd_total"],
           "source_run": a.run_id,
           "terminal_label": label,
           "floor_note": f"T_ref floored at original band {ORIGINAL_BAND_S}s"}
    REF_BUDGET.write_text(json.dumps(ref, indent=2))
    print(f"[armA16] wrote {REF_BUDGET.name}: {ref}")


if __name__ == "__main__":
    main()
