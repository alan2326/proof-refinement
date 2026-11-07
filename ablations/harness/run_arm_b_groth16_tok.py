#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm B'' -- TOKEN-PARITY ADDENDUM (-03).

The pre-registered §13 budget rule is time-gated (1x matched wall-clock
window; tokens recorded but not gating), and B has already received its
full time window across -01 + -02.  This addendum answers a separate
question (user decision 2026-07-29 ~23:55 UTC): what does B do with OUTPUT
TOKEN parity as well?  A's combined O_ref = 544,294 output tokens; B's
recorded total is 399,015 (-01: 212,510, -02: 186,505), so this run grants
the remaining ~145k.

Gate: before each iteration, stop if PRIOR_OUT + this run's recorded
output tokens >= O_REF.  Overshoot of one in-flight iteration is possible
and recorded, mirroring the time-gate convention.  Recorded tokens are the
only usable measure -- calls that time out leave server-side generation
unrecorded (B's -02 lost ~45 min to one), which is disclosed, not repaired.

Quote this run ONLY as the §13.8 token-parity addendum, never as the
primary time-matched result (that is -01 + -02, label D1).  Disclosures:
runs solo (no concurrent A/C CPU contention -- favourable to B), and B's
static context now legitimately includes its own -02 artifacts, among them
the failed Lemma54_Paper_Pderiv_Direct.lean fused-oracle module (workspace
state is B's own work product).

Usage:  python3 harness/run_arm_b_groth16_tok.py
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import signal
import subprocess
import sys
import time
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth16_common import (ROOT, Run, ANCHOR_PARENT_SCORE, bar,  # noqa: E402
                            bar_reached, best_score, count_log_rows,
                            is_fatal_api_error, load_envelope,
                            reap_orphaned_claude)
from run_arm_b_groth import CAND_RE, apply_files, build_and_eval, call_model  # noqa: E402
from run_arm_b_groth16 import (MODEL, HISTORY_K, L54,  # noqa: E402
                               build_static_context, system_for)
from run_arm_a_groth16_cont import is_limit_error, seconds_until_reset  # noqa: E402
from run_arm_b_groth16_cont import RESUME_FEEDBACK  # noqa: E402

PRIOR_RUNS = ["grothendieck016-armB-01", "grothendieck016-armB-02"]
PRIOR_OUT = 212_510 + 186_505          # recorded output tokens, -01 + -02
O_REF = 544_294                        # armA-01 + armA-02 combined output


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armB"))
    ap.add_argument("--run-id", default="grothendieck016-armB-03")
    ap.add_argument("--hard-cap-h", type=float, default=6.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0)
    ap.add_argument("--max-iters", type=int, default=100)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armB16t] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    env = load_envelope()

    run = Run(a.run_id, "B", ws, meta_extra={
        "role": "TOKEN-PARITY ADDENDUM -- not the primary time-matched result",
        "protocol": "token_parity_addendum",
        "continues": PRIOR_RUNS,
        "addendum_reason": (
            "the pre-registered §13 window is time-gated and already "
            "satisfied (-01 + -02, label D1); this run additionally grants "
            "B output-token parity with A (user decision 2026-07-29 ~23:55 "
            "UTC)"),
        "token_gate": {"O_ref": O_REF, "prior_recorded_out": PRIOR_OUT,
                       "granted_here": O_REF - PRIOR_OUT,
                       "rule": ("stop before an iteration once prior + this "
                                "run's recorded output tokens >= O_ref; "
                                "one-iteration overshoot possible, recorded"),
                       "caveat": ("timed-out calls leave server-side "
                                  "generation unrecorded (-02 lost one such "
                                  "call); recorded tokens are the gate")},
        "disclosures": [
            "runs solo: no concurrent A/C CPU contention (favourable to B)",
            "static context includes B's own -02 artifacts, including the "
            "failed Proof/Lib/Lemma54_Paper_Pderiv_Direct.lean",
        ],
        "history_note": ("fresh conversation; earlier history not carried, "
                         "workspace state is"),
        "model": MODEL, "resolved_model": "claude-opus-5",
        "invocation": "claude -p, tools disallowed, subscription auth",
        "limitation": ("runs inside Claude Code, so its agentic system prompt "
                       "is present and some tools remain visible though "
                       "blocked; weaker than an SDK bare-model call, and "
                       "biased in the ablation's favour (sect. 10d)"),
        "history_window": HISTORY_K,
        "tools": "none (no tool use, no subagents, no file access)",
        "bar_in_prompt": env["BAR"][0],
        "stopping_rule": ("success (accepted Cr_val <= BAR), or output-token "
                          "parity with A per the token gate"),
    })
    base_evals, base_fails = count_log_rows(ws)

    def _term(_sig, _frm):
        raise SystemExit(143)
    signal.signal(signal.SIGTERM, _term)

    def current_state():
        cur = best_score(ws)
        cur = ANCHOR_PARENT_SCORE if cur is None else cur
        cands = sorted((ws / L54 / "Candidates").glob("V*.lean"),
                       key=lambda q: int(re.findall(r"V(\d+)", q.stem)[0]))
        best_n = int(re.findall(r"V(\d+)", cands[-1].stem)[0]) if cands else 11
        return cur, best_n

    static = build_static_context(ws)
    (run.dir / "static_context.md").write_text(static)
    print(f"[armB16t] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armB16t] BAR={bar()} (~{float(bar()):.3g}); token gate: "
          f"{PRIOR_OUT} prior + this run >= {O_REF} "
          f"({O_REF - PRIOR_OUT} granted)")

    prev_best = best_score(ws)
    history: deque[tuple[str, str]] = deque(maxlen=HISTORY_K)
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped without reaching BAR"
    last_feedback = RESUME_FEEDBACK

    try:
        for n in range(1, a.max_iters + 1):
            if PRIOR_OUT + run.tok_out >= O_REF:
                label = "D5"
                evidence = (f"token parity reached: {PRIOR_OUT} (-01+-02) + "
                            f"{run.tok_out} (-03) >= O_ref {O_REF}")
                if best_score(ws) is not None and best_score(ws) < ANCHOR_PARENT_SCORE:
                    evidence += (f" (within-envelope best {best_score(ws)}, "
                                 f"above BAR {bar()})")
                break
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h (active)"
                break
            if stall_total > a.stall_cap_h * 3600:
                label = "D5"
                evidence = f"stall cap {a.stall_cap_h}h exhausted waiting on limits"
                break

            hist = "".join(
                f"\n### Earlier attempt {i}\nFiles you emitted: {w}\nResult:\n```\n{r}\n```\n"
                for i, (w, r) in enumerate(history, 1))
            prompt = (static
                      + f"\n# Recent attempts (most recent last, window={HISTORY_K})\n"
                      + (hist or "(none this session)")
                      + f"\n\n# Latest result\n\n```\n{last_feedback}\n```\n"
                      + "\n# Now\n\nEmit the next full candidate file "
                        "(and any supporting files).")

            t0 = time.time()
            print(f"[armB16t] iter {n} (tok {PRIOR_OUT + run.tok_out}/{O_REF}, "
                  f"active {run.wall/60:.1f}m, stalled {stall_total/60:.1f}m, "
                  f"${run.usd:.2f})", flush=True)
            cur, best_n = current_state()
            try:
                res = call_model(prompt, int(45 * 60), system_for(cur, best_n))
            except subprocess.TimeoutExpired:
                run.emit("llm_timeout", iteration=n)
                print("       ! model call timed out", flush=True)
                continue

            if is_limit_error(res):
                run.account(res)
                stalls += 1
                wait = seconds_until_reset(res.get("result") or "")
                run.emit("usage_limit_stall", iteration=n, stall_no=stalls,
                         wait_s=round(wait, 1),
                         result_tail=(res.get("result") or "")[-300:])
                print(f"[armB16t] limit stall #{stalls}: sleeping "
                      f"{wait/60:.1f} min (clock frozen)", flush=True)
                time.sleep(wait)
                run.t0 += wait
                stall_total += wait
                continue
            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", iteration=n, result=res.get("result"))
                print(f"[armB16t] ABORT (D7): {evidence}", flush=True)
                break
            if res.get("is_error"):
                run.emit("llm_error", iteration=n,
                         error=(res.get("result") or "")[:500])
                print(f"       ! error: {(res.get('result') or '')[:160]}", flush=True)
                time.sleep(20)
                continue

            text = res.get("result") or ""
            run.account(res)
            u = res.get("usage") or {}
            written, refused = apply_files(ws, text)
            (run.dir / f"iter_{n:04d}_response.md").write_text(text)

            if not written:
                last_feedback = ("You emitted no writable file. Emit a complete "
                                 "file in a fenced block whose info string "
                                 "contains `path=<workspace-relative path>`."
                                 + (f" Refused: {refused}" if refused else ""))
                run.emit("iteration", iteration=n, written=[], refused=refused,
                         usage=u, wall_s=round(time.time() - t0, 1),
                         no_files=True)
                history.append(("(none)", last_feedback))
                continue

            cands = [c for c in written if CAND_RE.fullmatch(c)]
            if not cands:
                checks = []
                for rel in written:
                    if not rel.endswith(".py") or "/Numerical_Library/" not in rel:
                        continue
                    mod = Path(rel).stem
                    import os
                    pr = subprocess.run(
                        [str(ws / ".venv" / "bin" / "python"), "-c",
                         f"import sys; sys.path.insert(0, '{L54}'); "
                         f"import importlib; importlib.import_module("
                         f"'Numerical_Library.{mod}'); "
                         f"print('import OK: Numerical_Library.{mod}')"],
                        cwd=ws, capture_output=True, text=True,
                        env={**os.environ},
                        timeout=900)
                    checks.append(f"$ python -c 'import Numerical_Library.{mod}'\n"
                                  f"{(pr.stdout + pr.stderr)[-2500:]}")
                last_feedback = (
                    ("\n\n".join(checks) + "\n\n" if checks else "")
                    + "No candidate was emitted this turn, so `lake build` and "
                      "`Evaluator.py` did not run -- they need a file at\n"
                      f"`{L54}/Candidates/V<N>.lean`.\n"
                      "Nothing is scored until you emit one.")
                run.emit("iteration", iteration=n, written=written,
                         refused=refused, usage=u,
                         wall_s=round(time.time() - t0, 1),
                         no_candidate=True, feedback_tail=last_feedback[-1500:])
                history.append((", ".join(written), last_feedback))
                continue

            cand = cands[-1]
            run.builds += 1
            try:
                ok, feedback, meta = build_and_eval(ws, cand)
            except subprocess.TimeoutExpired:
                ok, feedback, meta = False, "TIMEOUT after 3600s", {"stage": "timeout"}
            run.evals += 1
            if not ok:
                run.failed += 1

            shutil.copy2(ws / cand, run.dir / f"iter_{n:04d}_{Path(cand).name}")
            evals, fails = count_log_rows(ws)
            run.emit("iteration", iteration=n, written=written, refused=refused,
                     usage=u, session_id=res.get("session_id"),
                     num_turns=res.get("num_turns"),
                     permission_denials=res.get("permission_denials"),
                     wall_s=round(time.time() - t0, 1),
                     stage=meta.get("stage"), passed=ok,
                     best_score_after=str(best_score(ws)),
                     evaluator_runs=evals - base_evals,
                     evaluator_failures=fails - base_fails,
                     feedback_tail=feedback[-1500:])
            print(f"       -> wrote {written} passed={ok} "
                  f"score={best_score(ws)} ${run.usd:.2f}", flush=True)
            last_feedback = feedback
            history.append((", ".join(written), feedback))

            cur2 = best_score(ws)
            if cur2 is not None and cur2 != prev_best and cur2 < ANCHOR_PARENT_SCORE:
                run.emit("new_best", iteration=n, score=str(cur2),
                         score_float=float(cur2), wall_s=round(run.wall, 1),
                         output_tokens=run.tok_out, usd=round(run.usd, 3),
                         below_bar=bool(cur2 <= bar()))
                print(f"[armB16t] NEW BEST: {cur2} = {float(cur2):.3e} "
                      f"(BAR {float(bar()):.3e})", flush=True)
                prev_best = cur2

            if bar_reached(ws):
                label = "S"
                evidence = (f"evaluator accepted {best_score(ws)} <= BAR "
                            f"{bar()} at addendum iteration {n}")
                print(f"[armB16t] BAR REACHED: {evidence}")
                break
        else:
            label, evidence = "D5", f"max iters ({a.max_iters})"
    except SystemExit as e:
        if label != "S":
            label = "D5"
            evidence = f"terminated (SIGTERM {e.code}); best={best_score(ws)}"

    summary = run.finish(label, evidence)
    summary["stall_total_s"] = round(stall_total, 1)
    summary["stalls"] = stalls
    summary["continues"] = PRIOR_RUNS
    summary["protocol"] = "token_parity_addendum"
    summary["token_gate"] = {"O_ref": O_REF, "prior_recorded_out": PRIOR_OUT,
                             "final_total_out": PRIOR_OUT + run.tok_out}
    (run.dir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
