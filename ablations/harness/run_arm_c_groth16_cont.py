#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm C'' -- CONTINUATION of grothendieck016-armC-01.

-01 did real work through sprint attempt 3 (elapsed 4119.9 s), then the
claude.ai session limit starved attempts 4..20 until the window closed at
4311.2 s.  With armA-02 extending A's wall clock, C gets the matched
difference (1x window, user decision reaffirmed 2026-07-29 evening).
USED_S counts only -01's productive time (through attempt 3): the starved
tail is excluded here for the same reason armA-02 freezes its clock over
stalls -- starved time is not window.

Same live window rule and stall policy as run_arm_b_groth16_cont.py; same
driver, success criterion, and verdict logic as run_arm_c_groth16.py.

Usage:  python3 harness/run_arm_c_groth16_cont.py
"""
from __future__ import annotations

import argparse
import json
import signal
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import groth_common as _g12  # noqa: E402  (best_score reads the same log path)
from groth16_common import (ROOT, Run, count_log_rows,  # noqa: E402
                            is_fatal_api_error, load_envelope,
                            reap_orphaned_claude)
from run_arm_a_groth import run_one_sprint, DRIVER_PROMPT  # noqa: E402
from run_arm_a_groth16_cont import is_limit_error, seconds_until_reset  # noqa: E402
from run_arm_c_groth16 import ARM_C_PARENT, krivine_interval  # noqa: E402
from run_arm_b_groth16_cont import live_t_ref  # noqa: E402

PRIOR_RUN = "grothendieck016-armC-01"
USED_S = 4119.9                # -01 productive wall: through sprint attempt 3


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armC"))
    ap.add_argument("--run-id", default="grothendieck016-armC-02")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0)
    ap.add_argument("--max-sprints", type=int, default=1000)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armC16c] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    k_lo, k_hi = krivine_interval()
    load_envelope()

    def c_best(ws_: Path):
        return _g12.best_score(ws_)

    def verdict(b: Fraction | None) -> str:
        if b is None or b >= ARM_C_PARENT:
            return "none"
        if b < k_lo:
            return "S"                    # strictly below Krivine: real advance
        if b < k_hi:
            return "REVIEW"               # inside the interval: manual review
        return "within_slack"             # < seed but >= Krivine: treadmill

    run = Run(a.run_id, "C", ws, meta_extra={
        "role": "ablation: partial formalization removed, agentic system kept",
        "continues": PRIOR_RUN,
        "continuation_reason": (
            "-01 attempts 4..20 starved by the claude.ai session limit; "
            "armA-02 is extending A's wall clock and C gets the matched "
            "difference (1x window, user decision reaffirmed 2026-07-29 "
            "evening)"),
        "used_s_prior": USED_S,
        "used_s_note": ("-01 productive time only (through attempt 3, "
                        "elapsed 4119.9 s); the limit-starved tail to "
                        "4311.2 s is excluded, mirroring the stall-freeze "
                        "rule of the continuation runners"),
        "window_rule": (
            "USED_S + active wall vs live T_ref = max(4310.4 + "
            "wall(armA-02), 2360); concurrent while armA-02 runs; checked "
            "per sprint; limit stalls frozen out of the clock"),
        "driver": DRIVER_PROMPT,
        "driver_model": a.model,
        "subagent_models": {"planner": "opus", "generator": "opus",
                            "evaluator": "sonnet"},
        "statement_level": "outermost (K_G), sect. 9.3 / 12.5 / 13.2",
        "seed": "axiom hKrivine : GrothendieckIneq KrivineBound (exact real)",
        "arm_c_parent": str(ARM_C_PARENT),
        "success_criterion": ("accepted rational K_val < KrivineBound, "
                              f"interval [{float(k_lo):.15f}, "
                              f"{float(k_hi):.15f}] (50-digit certified); "
                              "within-slack re-certifications are progress, "
                              "not success (sect. 13.2)"),
        "stopping_rule": "matched window rule above; hard caps as backstop",
    })
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    def _term(_sig, _frm):
        raise SystemExit(143)
    signal.signal(signal.SIGTERM, _term)

    print(f"[armC16c] ws={ws} (continues {PRIOR_RUN}, used {USED_S}s)")
    print(f"[armC16c] seed={ARM_C_PARENT}; success iff accepted K_val < "
          f"{float(k_lo):.12f}")

    prev_best = c_best(ws)
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped at matched window"
    try:
        for n in range(1, a.max_sprints + 1):
            t_ref = live_t_ref()
            if t_ref is not None and USED_S + run.wall > t_ref:
                b = c_best(ws)
                label = "D5"
                evidence = (f"matched window closed: {USED_S:.0f}s (-01) + "
                            f"{run.wall:.0f}s (-02 active) > T_ref "
                            f"{t_ref:.0f}s; best={b} ({verdict(b)})")
                break
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h (active)"
                break
            if stall_total > a.stall_cap_h * 3600:
                label = "D5"
                evidence = f"stall cap {a.stall_cap_h}h exhausted waiting on limits"
                break

            t0 = time.time()
            print(f"[armC16c] sprint {n} (active {run.wall/60:.1f}m, stalled "
                  f"{stall_total/60:.1f}m, out_tok {run.tok_out}, "
                  f"${run.usd:.2f})", flush=True)
            try:
                res, _ = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
            except subprocess.TimeoutExpired:
                run.emit("driver_timeout", attempt=n,
                         timeout_min=a.sprint_timeout_min)
                continue

            if is_limit_error(res):
                run.account(res)
                stalls += 1
                wait = seconds_until_reset(res.get("result") or "")
                run.emit("usage_limit_stall", attempt=n, stall_no=stalls,
                         wait_s=round(wait, 1),
                         result_tail=(res.get("result") or "")[-300:])
                (run.dir / f"stall_{stalls:03d}_result.json").write_text(
                    json.dumps(res, indent=2))
                print(f"[armC16c] limit stall #{stalls}: sleeping "
                      f"{wait/60:.1f} min (clock frozen)", flush=True)
                time.sleep(wait)
                run.t0 += wait
                stall_total += wait
                continue
            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", attempt=n, result=res.get("result"))
                print(f"[armC16c] ABORT (D7): {evidence}", flush=True)
                break

            run.account(res)
            evals, fails = count_log_rows(ws)
            run.evals, run.failed = evals - base_evals, fails - base_fails
            run.emit("sprint", attempt=n,
                     session_id=res.get("session_id"),
                     is_error=res.get("is_error"),
                     num_turns=res.get("num_turns"),
                     duration_ms=res.get("duration_ms"),
                     cost_usd=res.get("total_cost_usd"),
                     usage=res.get("usage"),
                     model_usage=res.get("modelUsage"),
                     permission_denials=res.get("permission_denials"),
                     wall_s=round(time.time() - t0, 1),
                     best_score_after=str(c_best(ws)),
                     best_verdict=verdict(c_best(ws)),
                     evaluator_runs=evals - base_evals,
                     evaluator_failures=fails - base_fails,
                     result_tail=(res.get("result") or "")[-1500:])
            (run.dir / f"sprint_{n:03d}_result.json").write_text(
                json.dumps(res, indent=2))
            print(f"       -> turns={res.get('num_turns')} "
                  f"${res.get('total_cost_usd', 0):.3f} best={c_best(ws)} "
                  f"({verdict(c_best(ws))})", flush=True)
            run.snapshot_transcripts()

            b = c_best(ws)
            if b is not None and b != prev_best and b < ARM_C_PARENT:
                run.emit("new_best", attempt=n, score=str(b),
                         score_float=float(b), classification=verdict(b),
                         wall_s=round(run.wall, 1),
                         output_tokens=run.tok_out, usd=round(run.usd, 3))
                print(f"[armC16c] NEW BEST: {b} ({verdict(b)})", flush=True)
                prev_best = b

            if verdict(c_best(ws)) == "S":
                label = "S"
                evidence = (f"accepted K_val {c_best(ws)} < KrivineBound "
                            f"(interval lower {float(k_lo):.15f}) -- "
                            "a genuine advance; validate per sect. 13.5")
                print(f"[armC16c] BELOW KRIVINE: {evidence}")
                break
            if verdict(c_best(ws)) == "REVIEW":
                run.emit("interval_review", score=str(c_best(ws)))
        else:
            label, evidence = "D5", f"max sprints ({a.max_sprints})"
    except SystemExit as e:
        if label != "S":
            b = c_best(ws)
            label = "D5"
            evidence = (f"terminated at matched window (SIGTERM {e.code}); "
                        f"best={b} ({verdict(b)})")

    summary = run.finish(label, evidence)
    summary["stall_total_s"] = round(stall_total, 1)
    summary["stalls"] = stalls
    summary["continues"] = PRIOR_RUN
    summary["used_s_prior"] = USED_S
    (run.dir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
