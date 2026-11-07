#!/usr/bin/env python3
"""Arm C -- agentic system KEPT, partial formalization ABLATED.

Identical driver to Arm A (`/run-next-korenblum-sprint`, same planner /
generator / evaluator, same tools, same MCP servers, Wang 2025 and web search
available) pointed at the armC workspace, where the Lean surface is only the
Bergman A^2 definition of the constant plus the previous bound as one axiom.

Differs from Arm A only in the stopping rule: it runs to the 3x budget rather
than defining it.

Usage:  python3 harness/run_arm_c.py [--budget-mult 3.0]
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from common import (ROOT, Run, best_score, count_log_rows, goal_reached,  # noqa: E402
                    ANCHOR_PARENT_SCORE, ELAN, is_fatal_api_error,
                    reap_orphaned_claude)
from run_arm_a import run_one_sprint  # noqa: E402  (same driver, verbatim)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "armC"))
    ap.add_argument("--run-id", default="korenblum-armC-01")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--budget-mult", type=float, default=3.0)
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--max-sprints", type=int, default=1000)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    # Resume support: a prior run's real work is carried forward so the budget
    # accounts for it rather than restarting the clock.
    ap.add_argument("--carry-wall-s", type=float, default=0.0)
    ap.add_argument("--carry-out-tokens", type=int, default=0)
    ap.add_argument("--carry-usd", type=float, default=0.0)
    ap.add_argument("--carry-from", default="")
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armC] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    ref = json.loads((ROOT / "runs" / "reference_budget.json").read_text())
    t_budget = ref["T_ref_s"] * a.budget_mult
    o_budget = ref["O_ref_output_tokens"] * a.budget_mult

    run = Run(a.run_id, "C", ws, meta_extra={
        "role": "ablation: partial formalization removed, agentic system kept",
        "driver": "/run-next-korenblum-sprint",
        "driver_model": a.model,
        "subagent_models": {"planner": "opus", "generator": "opus",
                            "evaluator": "sonnet"},
        "kept_deliberately": ["full agent system", "all tools incl. MCP",
                              "Wang 2025 pdf+txt", "web search/fetch"],
        "ablated": ["KorenblumPaper/* (19 modules)", "Proof/Reduction.lean",
                    "Section2Assumptions bundle", "Numerical_Library/",
                    "all V1+ candidates", "sprint history"],
        "reference_budget": ref,
        "stopping_rule": (f"run until wall_clock > {a.budget_mult}x T_ref AND "
                          f"output_tokens > {a.budget_mult}x O_ref"),
        "budget": {"T_budget_s": t_budget, "O_budget_tokens": o_budget},
    })
    # carry forward the prior run's measured usage
    run.t0 -= a.carry_wall_s
    run.tok_out += a.carry_out_tokens
    run.usd += a.carry_usd
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    if a.carry_wall_s or a.carry_out_tokens:
        run.manifest["carried_forward"] = {
            "from_run": a.carry_from, "wall_s": a.carry_wall_s,
            "output_tokens": a.carry_out_tokens, "usd": a.carry_usd,
            "note": ("prior run was cut short by API credit exhaustion, not by "
                     "the budget rule; its completed sprints are carried "
                     "forward so the 3x budget covers total real work")}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    print(f"[armC] ws={ws}")
    print(f"[armC] start score={best_score(ws)} target > {ANCHOR_PARENT_SCORE}")
    print(f"[armC] budget: {t_budget/3600:.2f} h AND {o_budget} output tokens")

    label, evidence = "D5", "budget exhausted"
    for n in range(1, a.max_sprints + 1):
        over_time = run.wall > t_budget
        over_tok = run.tok_out > o_budget
        if over_time and over_tok:
            label, evidence = "D5", (f"3x budget exhausted: {run.wall/3600:.2f}h "
                                     f"> {t_budget/3600:.2f}h and {run.tok_out} "
                                     f"> {o_budget} output tokens")
            break
        if run.wall > a.hard_cap_h * 3600:
            label, evidence = "D5", f"hard cap {a.hard_cap_h}h"
            break

        t0 = time.time()
        print(f"[armC] sprint {n} (elapsed {run.wall/60:.1f}m / {t_budget/60:.0f}m, "
              f"out_tok {run.tok_out}/{o_budget}, ${run.usd:.2f})", flush=True)
        try:
            res, _ = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
        except subprocess.TimeoutExpired:
            run.emit("driver_timeout", attempt=n, timeout_min=a.sprint_timeout_min)
            continue

        if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
            label = "D7"
            evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
            run.emit("fatal_api", attempt=n, result=res.get("result"))
            print(f"[armC] ABORT (D7): {evidence}", flush=True)
            break

        run.account(res)
        evals, fails = count_log_rows(ws)
        run.evals, run.failed = evals - base_evals, fails - base_fails
        run.emit("sprint", attempt=n,
                 session_id=res.get("session_id"),
                 is_error=res.get("is_error"),
                 stop_reason=res.get("stop_reason"),
                 terminal_reason=res.get("terminal_reason"),
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
        (run.dir / f"sprint_{n:03d}_result.json").write_text(json.dumps(res, indent=2))
        print(f"       -> turns={res.get('num_turns')} "
              f"${res.get('total_cost_usd', 0):.3f} score={best_score(ws)} "
              f"evals=+{evals-base_evals} fails=+{fails-base_fails}", flush=True)
        run.snapshot_transcripts()

        if goal_reached(ws):
            label = "S"
            evidence = (f"evaluator accepted {best_score(ws)} > "
                        f"{ANCHOR_PARENT_SCORE} after {n} sprint(s)")
            print(f"[armC] GOAL REACHED: {evidence}")
            break

    print(json.dumps(run.finish(label, evidence), indent=2))


if __name__ == "__main__":
    main()
