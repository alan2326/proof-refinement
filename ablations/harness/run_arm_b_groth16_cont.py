#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm B'' -- CONTINUATION of grothendieck016-armB-01.

-01 ran its full matched window cleanly (no limit errors, SIGTERM at
deadline + grace, 4490.6 s used, best 3/250).  But the window itself was
defined by an Arm A run that lost sprints 2..8 to the claude.ai session
limit; A's continuation (grothendieck016-armA-02) is extending A's wall
clock, so B is owed the difference (matched 1x window, user decision
2026-07-29 reaffirmed 2026-07-29 evening: B must get as much wall clock as
A).  This runner grants it:

  * window gate: USED_S (4490.6 s from -01) + this run's active wall vs the
    LIVE combined T_ref = max(4310.4 + wall(armA-02 summary), 2360).  While
    armA-02 is still running its summary does not exist and B keeps pace
    concurrently, exactly as in the original concurrent protocol.  Checked
    before each iteration; overshoot of at most one in-flight iteration is
    possible and recorded (no pipeline hard-kill this time).
  * session/usage-limit errors stall-and-retry with the run clock frozen
    (t0 shifted), so stalls never count against B's window.
  * same bare loop, same prompts, fresh conversation: the K=3 history from
    -01 is gone (conversation state is not resumable), but the static
    context is rebuilt from the CURRENT workspace, which carries V12/V13
    and the updated log -- the workspace, not the chat, is the state.

Usage:  python3 harness/run_arm_b_groth16_cont.py
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

PRIOR_RUN = "grothendieck016-armB-01"
USED_S = 4490.6                # -01 productive wall (no limit errors)
PRIOR_A_WALL_S = 4310.4        # published grothendieck016-armA-01 wall
A02_SUMMARY = ROOT / "runs" / "grothendieck016-armA-02" / "summary.json"
ORIGINAL_BAND_S = 2360

RESUME_FEEDBACK = (
    "This run resumes an interrupted study session. The workspace context "
    "above is current and includes every candidate accepted so far; earlier "
    "conversation history is not available. Produce your next candidate.")


def live_t_ref() -> float | None:
    """Combined A window once armA-02 is done; None while A still runs."""
    if not A02_SUMMARY.exists():
        return None
    try:
        w = json.loads(A02_SUMMARY.read_text())["wall_clock_s"]
    except (json.JSONDecodeError, KeyError):
        return None                        # mid-write; try again next iter
    return max(PRIOR_A_WALL_S + w, ORIGINAL_BAND_S)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armB"))
    ap.add_argument("--run-id", default="grothendieck016-armB-02")
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0)
    ap.add_argument("--max-iters", type=int, default=1000)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armB16c] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    env = load_envelope()

    run = Run(a.run_id, "B", ws, meta_extra={
        "role": "ablation: agentic system removed, partial formalization kept",
        "continues": PRIOR_RUN,
        "continuation_reason": (
            "-01's matched window came from an Arm A run starved by the "
            "claude.ai session limit after 1 sprint; armA-02 is extending "
            "A's wall clock, and B gets the matched difference (1x window, "
            "user decision reaffirmed 2026-07-29 evening)"),
        "used_s_prior": USED_S,
        "window_rule": (
            "USED_S + active wall vs live T_ref = max(4310.4 + "
            "wall(armA-02), 2360); concurrent while armA-02 runs; checked "
            "per iteration, overshoot of one iteration possible and "
            "recorded; limit stalls frozen out of the clock"),
        "history_note": ("fresh conversation; -01's K=3 history not "
                         "carried, workspace state is"),
        "model": MODEL, "resolved_model": "claude-opus-5",
        "invocation": "claude -p, tools disallowed, subscription auth",
        "limitation": ("runs inside Claude Code, so its agentic system prompt "
                       "is present and some tools remain visible though "
                       "blocked; weaker than an SDK bare-model call, and "
                       "biased in the ablation's favour (sect. 10d)"),
        "history_window": HISTORY_K,
        "tools": "none (no tool use, no subagents, no file access)",
        "bar_in_prompt": env["BAR"][0],
        "stopping_rule": ("success (accepted Cr_val <= BAR), or the matched "
                          "window rule above"),
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
    print(f"[armB16c] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armB16c] BAR={bar()} (~{float(bar()):.3g}); used {USED_S}s in -01; "
          f"window tracks armA-02 live")

    prev_best = best_score(ws)
    history: deque[tuple[str, str]] = deque(maxlen=HISTORY_K)
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped without reaching BAR"
    last_feedback = RESUME_FEEDBACK

    try:
        for n in range(1, a.max_iters + 1):
            t_ref = live_t_ref()
            if t_ref is not None and USED_S + run.wall > t_ref:
                label = "D5"
                evidence = (f"matched window closed: {USED_S:.0f}s (-01) + "
                            f"{run.wall:.0f}s (-02 active) > T_ref {t_ref:.0f}s")
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
            print(f"[armB16c] iter {n} (active {run.wall/60:.1f}m, stalled "
                  f"{stall_total/60:.1f}m, out_tok {run.tok_out}, "
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
                print(f"[armB16c] limit stall #{stalls}: sleeping "
                      f"{wait/60:.1f} min (clock frozen)", flush=True)
                time.sleep(wait)
                run.t0 += wait
                stall_total += wait
                continue
            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", iteration=n, result=res.get("result"))
                print(f"[armB16c] ABORT (D7): {evidence}", flush=True)
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
                print(f"[armB16c] NEW BEST: {cur2} = {float(cur2):.3e} "
                      f"(BAR {float(bar()):.3e})", flush=True)
                prev_best = cur2

            if bar_reached(ws):
                label = "S"
                evidence = (f"evaluator accepted {best_score(ws)} <= BAR "
                            f"{bar()} at continuation iteration {n}")
                print(f"[armB16c] BAR REACHED: {evidence}")
                break
        else:
            label, evidence = "D5", f"max iters ({a.max_iters})"
    except SystemExit as e:
        if label != "S":
            label = "D5"
            evidence = (f"terminated at matched window (SIGTERM {e.code}); "
                        f"best={best_score(ws)}")

    summary = run.finish(label, evidence)
    summary["stall_total_s"] = round(stall_total, 1)
    summary["stalls"] = stalls
    summary["continues"] = PRIOR_RUN
    summary["used_s_prior"] = USED_S
    (run.dir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
