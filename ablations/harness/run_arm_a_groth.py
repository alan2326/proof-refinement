#!/usr/bin/env python3
"""Grothendieck Arm A -- the full, unmodified proof-refinement harness.

Drives `/run-next-sprint` (the Lemma54 driver skill; NOT
`/run-grothendieck-sprint`, which belongs to the separate GrothendieckHarness
asymptotics loop) headlessly, sprint by sprint, and instruments every sprint.
Wall-clock and output-token totals become T_ref / O_ref for the 3x budget.

Usage:  python3 harness/run_arm_a_groth.py [--max-sprints N] [--hard-cap-h H]
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth_common import (ROOT, Run, best_score, count_log_rows, goal_reached,  # noqa: E402
                          ANCHOR_PARENT_SCORE, ELAN, reap_orphaned_claude)

DRIVER_PROMPT = "/run-next-sprint"
REF_BUDGET = ROOT / "runs" / "reference_budget_groth.json"


def run_one_sprint(ws: Path, model: str, timeout_s: int) -> tuple[dict, str]:
    """One headless driver invocation.  Returns (parsed result json, raw)."""
    import os
    # Bill to the claude.ai subscription, not API credits (design sect. 10d).
    env = {**os.environ, "PATH": ELAN + os.pathsep + os.environ["PATH"]}
    env.pop("ANTHROPIC_API_KEY", None)
    env.pop("ANTHROPIC_AUTH_TOKEN", None)
    cmd = ["claude", "-p", DRIVER_PROMPT,
           "--output-format", "json",
           "--model", model,
           "--permission-mode", "bypassPermissions"]
    p = subprocess.run(cmd, cwd=ws, capture_output=True, text=True,
                       env=env, timeout=timeout_s)
    raw = p.stdout
    i = raw.find("{")
    if i < 0:
        return {"is_error": True, "result": raw[-2000:] or p.stderr[-2000:],
                "_parse_failed": True}, raw
    try:
        return json.loads(raw[i:]), raw
    except json.JSONDecodeError:
        return {"is_error": True, "result": raw[-2000:], "_parse_failed": True}, raw


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth_armA"))
    ap.add_argument("--run-id", default="grothendieck-armA-01")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--max-sprints", type=int, default=40)
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armA] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    assert ws.exists(), f"workspace missing: {ws}  (run harness/make_arm_ws_groth.sh)"

    run = Run(a.run_id, "A", ws, meta_extra={
        "role": "reference",
        "driver": DRIVER_PROMPT,
        "driver_model": a.model,
        "subagent_models": {"planner": "opus", "generator": "opus",
                            "evaluator": "sonnet"},
        "stopping_rule": "goal reached, or hard cap",
        "budget": {"rule": "this arm DEFINES T_ref and O_ref"},
    })
    # S0 carries 25 reconstructed pre-anchor evaluator rows; report deltas only.
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    print(f"[armA] run_id={a.run_id} ws={ws}")
    print(f"[armA] start score={best_score(ws)}  target < {ANCHOR_PARENT_SCORE}")
    print(f"[armA] baseline evaluator rows={base_evals} failures={base_fails}")

    label, evidence = "D5", "hard cap reached with no Cr improvement"
    for n in range(1, a.max_sprints + 1):
        if run.wall > a.hard_cap_h * 3600:
            label, evidence = "D5", f"hard cap {a.hard_cap_h}h"
            break

        t0 = time.time()
        print(f"[armA] sprint attempt {n} (elapsed {run.wall/60:.1f} min, "
              f"${run.usd:.2f}, out_tok={run.tok_out})", flush=True)
        try:
            res, raw = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
        except subprocess.TimeoutExpired:
            run.emit("driver_timeout", attempt=n, timeout_min=a.sprint_timeout_min)
            run.failed += 1
            continue

        run.account(res)
        evals, fails = count_log_rows(ws)
        run.evals, run.failed = evals - base_evals, fails - base_fails
        run.emit("sprint",
                 attempt=n,
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
              f"${res.get('total_cost_usd', 0):.3f} "
              f"score={best_score(ws)} evals=+{evals-base_evals} "
              f"fails=+{fails-base_fails}", flush=True)

        run.snapshot_transcripts()

        if goal_reached(ws):
            label = "S"
            evidence = (f"evaluator accepted score {best_score(ws)} "
                        f"< {ANCHOR_PARENT_SCORE} after {n} sprint(s)")
            print(f"[armA] GOAL REACHED: {evidence}")
            break
    else:
        label, evidence = "D5", f"max sprints ({a.max_sprints}) reached"

    summary = run.finish(label, evidence)
    print(json.dumps(summary, indent=2))

    ref = {"T_ref_s": summary["wall_clock_s"],
           "O_ref_output_tokens": summary["output_tokens"],
           "usd_ref": summary["usd_total"],
           "source_run": a.run_id,
           "terminal_label": label}
    REF_BUDGET.write_text(json.dumps(ref, indent=2))
    print(f"[armA] wrote {REF_BUDGET.name}: {ref}")


if __name__ == "__main__":
    main()
