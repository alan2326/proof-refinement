#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm A -- CONTINUATION of grothendieck016-armA-01.

The -01 run lost sprints 2..8 to the claude.ai session limit ("You've hit
your session limit -- resets 7:30pm (UTC)"): sprint 1 completed cleanly
(V12 accepted at 7/1000), sprint attempt 2 died 4 turns in, attempts 3..8
were instant api_error results that burned the sprint budget without doing
any work.  This runner grants the remaining 7 of the pre-registered 8 sprint
attempts, in the same workspace, under run id grothendieck016-armA-02.

Differences from run_arm_a_groth16.py, and nothing else:

  * a session/usage-limit api_error does NOT consume a sprint attempt: the
    runner sleeps until the advertised reset (or 15 min if unparseable) and
    retries; the sleep is subtracted from the run clock (t0 is shifted), so
    stall time never inflates T_ref for the matched B/C windows.  Partial
    work done before the limit hit stays on the clock and in the token
    totals (accounted from modelUsage as usual).
  * the reference budget file is NOT written here -- after this run,
    fix_reference_budget_groth16_cont.py combines -01 and -02 into the
    final T_ref.

Usage:  python3 harness/run_arm_a_groth16_cont.py [--max-sprints N]
"""
from __future__ import annotations

import argparse
import calendar
import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth16_common import (ROOT, Run, bar, bar_reached, best_score,  # noqa: E402
                            count_log_rows, improved, reap_orphaned_claude)
from run_arm_a_groth import run_one_sprint, DRIVER_PROMPT  # noqa: E402

PRIOR_RUN = "grothendieck016-armA-01"
PRIOR_WALL_S = 4310.4          # published -01 wall; the combined fixer adds ours
PRIOR_CLEAN_SPRINTS = 1

LIMIT_RE = re.compile(r"(session|usage|rate)[ _]limit", re.I)
RESET_RE = re.compile(r"resets\s+(\d{1,2})(?::(\d{2}))?\s*(am|pm)", re.I)


def is_limit_error(res: dict) -> bool:
    return bool(res.get("is_error")) and bool(LIMIT_RE.search(res.get("result") or ""))


def seconds_until_reset(msg: str, default_s: float = 900.0) -> float:
    """Parse 'resets 7:30pm (UTC)' into a wait; fall back to a 15-min poll."""
    m = RESET_RE.search(msg or "")
    if not m:
        return default_s
    hh, mm, ap = int(m.group(1)), int(m.group(2) or 0), m.group(3).lower()
    if ap == "pm" and hh != 12:
        hh += 12
    if ap == "am" and hh == 12:
        hh = 0
    now = time.time()
    lt = time.gmtime(now)
    target = calendar.timegm((lt.tm_year, lt.tm_mon, lt.tm_mday, hh, mm, 0,
                              0, 0, 0))              # UTC reset time, today
    wait = target - now + 180                        # 3-min buffer
    if wait <= 0 or wait > 6 * 3600:                 # stale/garbled message
        return default_s
    return wait


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armA"))
    ap.add_argument("--run-id", default="grothendieck016-armA-02")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--max-sprints", type=int, default=8 - PRIOR_CLEAN_SPRINTS)
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0,
                    help="give up after this much cumulative limit-stall time")
    a = ap.parse_args()

    n = reap_orphaned_claude()
    if n:
        print(f"[armA16c] reaped {n} orphaned claude proc(s)")
    ws = Path(a.workspace)
    assert ws.exists(), f"workspace missing: {ws}"

    run = Run(a.run_id, "A", ws, meta_extra={
        "role": "reference-continuation",
        "continues": PRIOR_RUN,
        "continuation_reason": (
            "-01 sprint attempts 2..8 starved by the claude.ai session limit "
            "(reset 19:30 UTC); only sprint 1 ran cleanly. This run grants "
            f"the remaining {a.max_sprints} of the pre-registered 8 attempts "
            "in the same (untouched) workspace."),
        "prior_best": str(best_score(ws)),
        "prior_wall_s": PRIOR_WALL_S,
        "stall_policy": (
            "limit-pattern api_error => sleep to advertised reset (else 15 "
            "min), retry without consuming the attempt; sleep subtracted "
            "from the run clock so T_ref only counts active time"),
        "driver": DRIVER_PROMPT,
        "driver_model": a.model,
        "subagent_models": {"planner": "opus", "generator": "opus",
                            "evaluator": "sonnet"},
        "stopping_rule": "accepted Cr_val <= BAR, or max-sprints/hard cap",
        "budget": {"rule": "this arm (combined -01+-02) DEFINES T_ref and O_ref",
                   "max_sprints": a.max_sprints,
                   "combined_via": "fix_reference_budget_groth16_cont.py"},
    })
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    print(f"[armA16c] run_id={a.run_id} ws={ws} (continues {PRIOR_RUN})")
    print(f"[armA16c] start score={best_score(ws)}  BAR={bar()} "
          f"(~{float(bar()):.3g})")

    prev_best = best_score(ws)
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped without reaching BAR"
    for k in range(1, a.max_sprints + 1):
        while True:                       # limit-stall retry loop, one attempt
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h (active)"
                break
            if stall_total > a.stall_cap_h * 3600:
                label = "D5"
                evidence = f"stall cap {a.stall_cap_h}h exhausted waiting on limits"
                break

            t0 = time.time()
            print(f"[armA16c] sprint attempt {k} (active {run.wall/60:.1f} min, "
                  f"stalled {stall_total/60:.1f} min, ${run.usd:.2f}, "
                  f"out_tok={run.tok_out})", flush=True)
            try:
                res, _ = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
            except subprocess.TimeoutExpired:
                run.emit("driver_timeout", attempt=k,
                         timeout_min=a.sprint_timeout_min)
                run.failed += 1
                break                     # consumes the attempt, as in -01

            run.account(res)              # partial work is real usage either way

            if is_limit_error(res):
                stalls += 1
                wait = seconds_until_reset(res.get("result") or "")
                run.emit("usage_limit_stall", attempt=k, stall_no=stalls,
                         wait_s=round(wait, 1),
                         result_tail=(res.get("result") or "")[-300:])
                (run.dir / f"stall_{stalls:03d}_result.json").write_text(
                    json.dumps(res, indent=2))
                print(f"[armA16c] limit stall #{stalls}: sleeping "
                      f"{wait/60:.1f} min (attempt {k} not consumed)", flush=True)
                time.sleep(wait)
                run.t0 += wait            # freeze the run clock over the stall
                stall_total += wait
                continue                  # retry the same attempt

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
            (run.dir / f"sprint_{k:03d}_result.json").write_text(
                json.dumps(res, indent=2))
            print(f"       -> turns={res.get('num_turns')} "
                  f"${res.get('total_cost_usd', 0):.3f} "
                  f"score={best_score(ws)} evals=+{evals-base_evals} "
                  f"fails=+{fails-base_fails}", flush=True)
            run.snapshot_transcripts()
            break                         # attempt finished (ok or non-limit err)

        if "cap" in evidence:
            break                         # a cap fired inside the retry loop

        cur = best_score(ws)
        if cur is not None and cur != prev_best:
            run.emit("new_best", attempt=k, score=str(cur),
                     score_float=float(cur), wall_s=round(run.wall, 1),
                     output_tokens=run.tok_out, usd=round(run.usd, 3),
                     below_bar=bool(cur <= bar()))
            print(f"[armA16c] NEW BEST: {cur} = {float(cur):.3e} "
                  f"(BAR {float(bar()):.3e})", flush=True)
            prev_best = cur

        if bar_reached(ws):
            label = "S"
            evidence = (f"evaluator accepted score {best_score(ws)} <= BAR "
                        f"{bar()} after {PRIOR_CLEAN_SPRINTS}+{k} sprint(s) "
                        f"(-01 + continuation)")
            print(f"[armA16c] BAR REACHED: {evidence}")
            break
    else:
        label = "D5"
        evidence = (f"max sprints ({PRIOR_CLEAN_SPRINTS}+{a.max_sprints} "
                    f"combined) reached; best={best_score(ws)}")
        if improved(ws):
            evidence += " (within-envelope improvement only)"

    summary = run.finish(label, evidence)
    summary["stall_total_s"] = round(stall_total, 1)
    summary["stalls"] = stalls
    summary["continues"] = PRIOR_RUN
    (run.dir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    print("[armA16c] NOTE: run fix_reference_budget_groth16_cont.py to write "
          "the combined -01+-02 reference budget before extending B/C.")


if __name__ == "__main__":
    main()
