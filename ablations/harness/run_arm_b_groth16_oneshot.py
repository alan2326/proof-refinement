#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm B-OS -- MEMORYLESS ONE-SHOT best-of-N.

Rationale (user decision 2026-07-30): Arm B's refinement loop -- a rolling
K=3 history, verbatim build/evaluator feedback, and a persistent workspace
that accumulates its own accepted candidates -- is agentic in spirit even
with tools ablated.  The strongest no-agent ablation is a memoryless
one-shot: the model receives the IDENTICAL static context Arm B received
(the full partial formalization + paper + parity extras, built from the
pristine S0^16 anchor) and produces one complete candidate per attempt with
NO feedback, NO history, and NO workspace carry-over.  The Lemma54 tree is
reset to the pristine S0^16 state between attempts, so every attempt is an
independent draw.  The best evaluator-accepted candidate across attempts is
picked at the end (the workspace is left holding it).

Budget (matching Arm B's total grant): attempts repeat until BOTH the
Arm-A-matched wall-clock window (T_ref) AND the output-token budget (O_ref)
from runs/reference_budget_groth16.json are exhausted -- B received its full
time window (-01 + -02) and then token parity (-03), so the strongest-form
one-shot arm gets the same combined envelope.  Gate checked before each
attempt; a one-attempt overshoot is possible and recorded, mirroring the
B conventions.  Usage-limit stalls freeze the clock and consume nothing
(same protocol as the -02/-03 continuation runners).

Everything else is identical to the Arm B setup: same model, same tool-less
`claude -p` invocation, same static-context builder, same write allowlist,
same build+eval gate, same BAR in the system prompt, same 45-min call
timeout.

Usage:  python3 harness/run_arm_b_groth16_oneshot.py
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
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth16_common import (ROOT, Run, ANCHOR_PARENT_SCORE, bar,  # noqa: E402
                            bar_reached, best_score, count_log_rows,
                            is_fatal_api_error, load_envelope,
                            reap_orphaned_claude, _iter_log, _row_passed,
                            _row_score)
from run_arm_b_groth import CAND_RE, apply_files, build_and_eval, call_model  # noqa: E402
from run_arm_b_groth16 import MODEL, L54, SYSTEM_TMPL, build_static_context  # noqa: E402
from run_arm_a_groth16_cont import is_limit_error, seconds_until_reset  # noqa: E402

S0_WS = ROOT / "workspaces" / "S0_grothendieck016"
REF_FILE = ROOT / "runs" / "reference_budget_groth16.json"

# Same system prompt as Arm B except the feedback-loop sentence, which is no
# longer true.  The replace is asserted so drift in the source template fails
# loudly instead of silently shipping the wrong prompt.
_OLD = ("You produce whole files as\n"
        "text; a harness writes them, runs `lake build` and `Evaluator.py`, "
        "and returns\nthe verbatim output to you.")
_NEW = ("You produce whole files as\n"
        "text; a harness writes them, runs `lake build` and `Evaluator.py` "
        "once, and\nrecords the result. THIS IS A ONE-SHOT ATTEMPT: no "
        "output ever comes back to\nyou, there is no second turn, and no "
        "other attempt sees your work.")
assert _OLD in SYSTEM_TMPL, "Arm B SYSTEM_TMPL drifted; re-derive the one-shot edit"
SYSTEM_TMPL_OS = SYSTEM_TMPL.replace(_OLD, _NEW)

ONESHOT_TAIL = """
# Now

This is your single attempt: one response, no feedback, no memory. The
harness will write the files you emit, run `lake build` and `Evaluator.py`
once, and record the score; the best evaluator-accepted candidate across
independent one-shot attempts is selected at the end. Emit the complete
candidate file (and ALL supporting files it needs -- oracle module,
`Numerical_Library/__init__.py` re-export, `lemma.toml` -- in this same
response). A candidate that fails to build or verify scores nothing.
"""


def system_for_oneshot(cur, best_n: int) -> str:
    b = bar()
    return SYSTEM_TMPL_OS.format(cur=cur, bestn=best_n, nextn=best_n + 1,
                                 bar=f"{b.numerator}/{b.denominator}")


def rsync_tree(src: Path, dst: Path):
    subprocess.run(["rsync", "-a", "--delete", str(src) + "/", str(dst) + "/"],
                   check=True, timeout=600)


def reset_lemma54(ws: Path):
    """Restore the writable surface (all of Lemma54) to the pristine S0^16
    state.  The write allowlist confines the model to Lemma54 subpaths and
    the evaluator log lives there too, so this reset makes attempts
    independent; .lake build caches and the venv are untouched."""
    rsync_tree(S0_WS / L54, ws / L54)


def new_log_rows(ws: Path, base_n: int) -> list[dict]:
    return list(_iter_log(ws))[base_n:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armBos"))
    ap.add_argument("--run-id", default="grothendieck016-armBos-01")
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0)
    ap.add_argument("--max-attempts", type=int, default=500)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armBos] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    env = load_envelope()
    ref = json.loads(REF_FILE.read_text())
    t_ref = float(ref["T_ref_s"])
    o_ref = int(ref["O_ref_output_tokens"])

    run = Run(a.run_id, "Bos", ws, meta_extra={
        "role": ("ablation: agentic system removed, partial formalization "
                 "kept, MEMORYLESS ONE-SHOT best-of-N (strongest no-agent "
                 "form: Arm B's feedback/history/workspace loop is agentic "
                 "in spirit; user decision 2026-07-30)"),
        "protocol": "oneshot_best_of_n",
        "memoryless": ("no history window, no build/evaluator feedback, "
                       "fresh conversation per attempt; the Lemma54 tree is "
                       "rsync-reset to the pristine S0^16 state between "
                       "attempts, so every attempt is an independent draw "
                       "from the identical prompt"),
        "selection": ("best evaluator-accepted candidate across attempts; "
                      "the workspace is left holding the winning attempt's "
                      "Lemma54 tree"),
        "model": MODEL, "resolved_model": "claude-opus-5",
        "invocation": "claude -p, tools disallowed, subscription auth",
        "limitation": ("runs inside Claude Code, so its agentic system prompt "
                       "is present and some tools remain visible though "
                       "blocked; weaker than an SDK bare-model call, and "
                       "biased in the ablation's favour (sect. 10d)"),
        "history_window": 0,
        "tools": "none (no tool use, no subagents, no file access)",
        "bar_in_prompt": env["BAR"][0],
        "budget": {"T_ref_s": t_ref, "O_ref_output_tokens": o_ref,
                   "source": str(REF_FILE),
                   "rule": ("stop before an attempt once active wall > T_ref "
                            "AND recorded output tokens > O_ref; B received "
                            "both grants (-01/-02 time window + -03 token "
                            "parity), so the one-shot arm gets the same "
                            "combined envelope; one-attempt overshoot "
                            "possible, recorded"),
                   "caveat": ("timed-out calls leave server-side generation "
                              "unrecorded; recorded tokens are the gate "
                              "(same convention as B)")},
        "stopping_rule": ("success (accepted Cr_val <= BAR), or BOTH budgets "
                          "exhausted: active wall > T_ref and recorded "
                          "output tokens > O_ref"),
        "disclosures": [
            "runs solo: no concurrent A/C CPU contention (favourable to Bos)",
            "static context is built from the pristine S0^16 anchor -- the "
            "same starting context Arm B's -01 received; none of B's later "
            "artifacts are visible",
            "identical prompt every attempt -> later attempts benefit from "
            "prompt-cache reads (cost only; the model sees the same input)",
        ],
    })
    base_rows, base_fails = count_log_rows(ws)

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
    prompt = static + ONESHOT_TAIL
    cur0, best_n0 = current_state()
    system_prompt = system_for_oneshot(cur0, best_n0)
    (run.dir / "system_prompt.md").write_text(system_prompt)
    print(f"[armBos] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armBos] BAR={bar()} (~{float(bar()):.3g}); budget: "
          f"{t_ref:.0f}s AND {o_ref} output tokens (both must exhaust)")
    print(f"[armBos] anchor state: cur={cur0}, best_n=V{best_n0}")

    best_dir = run.dir / "best_lemma54"
    overall_best = None            # best accepted Cr_val < parent, across attempts
    overall_best_attempt = 0
    n_candidates = n_accepted = 0
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped without reaching BAR"

    try:
        for n in range(1, a.max_attempts + 1):
            over_time = run.wall > t_ref
            over_tok = run.tok_out > o_ref
            if over_time and over_tok:
                label = "D5"
                evidence = (f"both budgets exhausted: active wall "
                            f"{run.wall:.0f}s > T_ref {t_ref:.0f}s and "
                            f"{run.tok_out} > O_ref {o_ref} output tokens")
                if overall_best is not None:
                    evidence += (f" (within-envelope best {overall_best} at "
                                 f"attempt {overall_best_attempt}, above BAR "
                                 f"{bar()})")
                break
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h (active)"
                break
            if stall_total > a.stall_cap_h * 3600:
                label = "D5"
                evidence = f"stall cap {a.stall_cap_h}h exhausted waiting on limits"
                break

            t0 = time.time()
            print(f"[armBos] attempt {n} (active {run.wall/60:.1f}m/"
                  f"{t_ref/60:.0f}m, tok {run.tok_out}/{o_ref}, "
                  f"stalled {stall_total/60:.1f}m, ${run.usd:.2f}, "
                  f"best={overall_best})", flush=True)
            try:
                res = call_model(prompt, int(45 * 60), system_prompt)
            except subprocess.TimeoutExpired:
                run.emit("llm_timeout", attempt=n)
                print("       ! model call timed out", flush=True)
                continue

            if is_limit_error(res):
                run.account(res)
                stalls += 1
                wait = seconds_until_reset(res.get("result") or "")
                run.emit("usage_limit_stall", attempt=n, stall_no=stalls,
                         wait_s=round(wait, 1),
                         result_tail=(res.get("result") or "")[-300:])
                print(f"[armBos] limit stall #{stalls}: sleeping "
                      f"{wait/60:.1f} min (clock frozen)", flush=True)
                time.sleep(wait)
                run.t0 += wait
                stall_total += wait
                continue
            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", attempt=n, result=res.get("result"))
                print(f"[armBos] ABORT (D7): {evidence}", flush=True)
                break
            if res.get("is_error"):
                run.emit("llm_error", attempt=n,
                         error=(res.get("result") or "")[:500])
                print(f"       ! error: {(res.get('result') or '')[:160]}", flush=True)
                time.sleep(20)
                continue

            text = res.get("result") or ""
            run.account(res)
            u = res.get("usage") or {}
            written, refused = apply_files(ws, text)
            (run.dir / f"attempt_{n:04d}_response.md").write_text(text)

            if not written:
                run.emit("attempt", attempt=n, written=[], refused=refused,
                         usage=u, session_id=res.get("session_id"),
                         wall_s=round(time.time() - t0, 1), no_files=True)
                print(f"       -> no writable files (refused: {refused})", flush=True)
                reset_lemma54(ws)
                continue

            cands = [c for c in written if CAND_RE.fullmatch(c)]
            if not cands:
                # One-shot: nothing feeds back, so no import-check feedback
                # stage exists; a candidateless attempt simply scores nothing.
                run.emit("attempt", attempt=n, written=written, refused=refused,
                         usage=u, session_id=res.get("session_id"),
                         wall_s=round(time.time() - t0, 1), no_candidate=True)
                print(f"       -> wrote {written} but no candidate; scores "
                      f"nothing", flush=True)
                reset_lemma54(ws)
                continue

            cand = cands[-1]
            n_candidates += 1
            run.builds += 1
            try:
                ok, feedback, meta = build_and_eval(ws, cand)
            except subprocess.TimeoutExpired:
                ok, feedback, meta = False, "TIMEOUT after 3600s", {"stage": "timeout"}
            run.evals += 1
            if not ok:
                run.failed += 1

            adir = run.dir / f"attempt_{n:04d}"
            for rel in written:
                if (ws / rel).is_file():
                    dst = adir / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(ws / rel, dst)
            adir.mkdir(parents=True, exist_ok=True)
            (adir / "eval_output.txt").write_text(feedback)

            rows = new_log_rows(ws, base_rows)
            scores = [s for r in rows if _row_passed(r)
                      and (s := _row_score(r)) is not None]
            attempt_score = min(scores) if scores else None
            if ok:
                n_accepted += 1

            run.emit("attempt", attempt=n, written=written, refused=refused,
                     usage=u, session_id=res.get("session_id"),
                     num_turns=res.get("num_turns"),
                     wall_s=round(time.time() - t0, 1),
                     stage=meta.get("stage"), passed=ok,
                     attempt_score=str(attempt_score),
                     feedback_tail=feedback[-1500:])
            print(f"       -> wrote {written} passed={ok} "
                  f"score={attempt_score} ${run.usd:.2f}", flush=True)

            improved = (ok and attempt_score is not None
                        and attempt_score < ANCHOR_PARENT_SCORE
                        and (overall_best is None or attempt_score < overall_best))
            if improved:
                overall_best, overall_best_attempt = attempt_score, n
                rsync_tree(ws / L54, best_dir)
                run.emit("new_best", attempt=n, score=str(attempt_score),
                         score_float=float(attempt_score),
                         wall_s=round(run.wall, 1), output_tokens=run.tok_out,
                         usd=round(run.usd, 3),
                         below_bar=bool(attempt_score <= bar()))
                print(f"[armBos] NEW BEST: {attempt_score} = "
                      f"{float(attempt_score):.3e} (BAR {float(bar()):.3e})",
                      flush=True)

            if bar_reached(ws):
                label = "S"
                evidence = (f"evaluator accepted {best_score(ws)} <= BAR "
                            f"{bar()} at one-shot attempt {n}")
                print(f"[armBos] BAR REACHED: {evidence}")
                break

            reset_lemma54(ws)
        else:
            label, evidence = "D5", f"max attempts ({a.max_attempts})"
    except SystemExit as e:
        if label != "S":
            label = "D5"
            evidence = f"terminated (SIGTERM {e.code}); best={overall_best}"

    # Pick the best: leave the workspace holding the winning attempt's tree.
    if label != "S" and best_dir.exists():
        rsync_tree(best_dir, ws / L54)

    summary = run.finish(label, evidence)
    summary["protocol"] = "oneshot_best_of_n"
    summary["stall_total_s"] = round(stall_total, 1)
    summary["stalls"] = stalls
    summary["budget"] = {"T_ref_s": t_ref, "O_ref_output_tokens": o_ref}
    summary["attempts_with_candidate"] = n_candidates
    summary["attempts_accepted"] = n_accepted
    summary["best_attempt"] = overall_best_attempt
    summary["best_across_attempts"] = str(overall_best)
    (run.dir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
