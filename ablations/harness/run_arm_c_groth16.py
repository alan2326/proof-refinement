#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm C'' -- agentic system KEPT, partial
formalization ABLATED, statement level = outermost (K_G), exact-real seed.

Identical driver to Arm A (`/run-next-sprint`) pointed at groth16_armC.
Success (sect. 13.2): an evaluator-accepted candidate whose rational K_val is
STRICTLY BELOW KrivineBound = pi/(2*log(1+sqrt 2)), decided against a
50-digit certified interval. By the contract's monotonicity lemma nothing
below KrivineBound is derivable from the seed, so any S is mathematics beyond
the published state of the art. Rational re-certifications of the Krivine
frontier (K_val >= KrivineBound) log as within-slack progress, not success.

Stopping (user decision 2026-07-29): concurrent with Arm A; exits when the
matched window closes (runs/groth16_deadline.json, t_ref_s = max(T_armA,
2360 s)); hard caps as backstop.
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

ARM_C_PARENT = Fraction(1782214, 1000000)   # the rational seed score

# 50-digit certified interval for KrivineBound (mpmath, dps 60; directed
# widening by 1e-52 on each side, orders beyond mpmath's error at dps 60).
def krivine_interval() -> tuple[Fraction, Fraction]:
    import mpmath as mp
    mp.mp.dps = 60
    k = mp.pi / (2 * mp.log(1 + mp.sqrt(2)))
    lo = Fraction(mp.nstr(k - mp.mpf("1e-52"), 55, strip_zeros=False))
    hi = Fraction(mp.nstr(k + mp.mpf("1e-52"), 55, strip_zeros=False))
    assert lo < hi
    return lo, hi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armC"))
    ap.add_argument("--run-id", default="grothendieck016-armC-01")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--deadline-file",
                    default=str(ROOT / "runs" / "groth16_deadline.json"))
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--max-sprints", type=int, default=1000)
    ap.add_argument("--sprint-timeout-min", type=float, default=90.0)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armC16] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    dl_file = Path(a.deadline_file)
    k_lo, k_hi = krivine_interval()
    env = load_envelope()

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
        "stopping_rule": ("matched wall-clock window (deadline file, "
                          "t_ref_s = max(T_armA, 2360 s)); user decision "
                          "2026-07-29"),
    })
    base_evals, base_fails = count_log_rows(ws)
    run.manifest["baseline_log_rows"] = {"evaluator_runs": base_evals,
                                         "failures": base_fails}
    (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))

    def _term(_sig, _frm):
        raise SystemExit(143)
    signal.signal(signal.SIGTERM, _term)

    print(f"[armC16] ws={ws}")
    print(f"[armC16] seed={ARM_C_PARENT}; success iff accepted K_val < "
          f"{float(k_lo):.12f}")

    prev_best = c_best(ws)
    label, evidence = "D5", "stopped at matched window"
    try:
        for n in range(1, a.max_sprints + 1):
            if dl_file.exists():
                t_ref = json.loads(dl_file.read_text())["t_ref_s"]
                if run.wall > t_ref:
                    b = c_best(ws)
                    label = "D5"
                    evidence = (f"1x matched wall-clock window closed: "
                                f"{run.wall:.0f}s > T_ref {t_ref:.0f}s; "
                                f"best={b} ({verdict(b)})")
                    break
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h"
                break

            t0 = time.time()
            print(f"[armC16] sprint {n} (elapsed {run.wall/60:.1f}m, "
                  f"out_tok {run.tok_out}, ${run.usd:.2f})", flush=True)
            try:
                res, _ = run_one_sprint(ws, a.model, int(a.sprint_timeout_min * 60))
            except subprocess.TimeoutExpired:
                run.emit("driver_timeout", attempt=n,
                         timeout_min=a.sprint_timeout_min)
                continue

            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", attempt=n, result=res.get("result"))
                print(f"[armC16] ABORT (D7): {evidence}", flush=True)
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
                print(f"[armC16] NEW BEST: {b} ({verdict(b)})", flush=True)
                prev_best = b

            if verdict(c_best(ws)) == "S":
                label = "S"
                evidence = (f"accepted K_val {c_best(ws)} < KrivineBound "
                            f"(interval lower {float(k_lo):.15f}) -- "
                            "a genuine advance; validate per sect. 13.5")
                print(f"[armC16] BELOW KRIVINE: {evidence}")
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

    print(json.dumps(run.finish(label, evidence), indent=2))


if __name__ == "__main__":
    main()
