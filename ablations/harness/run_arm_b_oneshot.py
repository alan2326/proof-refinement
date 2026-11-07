#!/usr/bin/env python3
"""Korenblum Arm B-OS -- MEMORYLESS ONE-SHOT best-of-N (the "no agent" arm).

Korenblum parity for the graded agent ablation established on sprint-016
Grothendieck (docs/2026-07-30-ablation-writeup.md): the no-agent
configuration keeps the partial formalization but removes the loop
entirely -- independent one-shot samples from an identical prompt, one
response, no feedback, no history, workspace reset between samples, best
evaluator-accepted sample kept.  This mirrors
harness/run_arm_b_groth16_oneshot.py on the Korenblum anchor.

Each attempt receives the IDENTICAL static context Arm B's -01 received
(the full partial formalization + paper + roadmap, built from the pristine
S0_korenblum anchor by run_arm_b.build_static_context).  The
ProofRefinement/Korenblum tree (writable surface + evaluator log) is
rsync-reset to the pristine S0 state between attempts, so every attempt is
an independent draw and every candidate is evaluated against the V64
parent.

Budget (user decision 2026-07-30): the 1x matched window -- attempts
repeat until BOTH active wall > T_ref AND recorded output tokens > O_ref
from runs/reference_budget.json.  Gate checked before each attempt; a
one-attempt overshoot is possible and recorded.  Note T_ref is floored at
the ORIGINAL run's 8322 s band (Arm A's measured wall was 3285.4 s), which
is generous to this arm.  Usage-limit stalls freeze the clock and consume
nothing (same protocol as the grothendieck016 continuation runners).

There is NO early success stop: beating the parent does not end the run
(best-of-N wants the full budget), unlike Arm B's -01 stop-on-success.

Everything else is identical to the Arm B setup: same model, same
tool-less `claude -p` invocation, same static-context builder, same write
allowlist, same build+eval gate, same 45-min call timeout.

Usage:  python3 harness/run_arm_b_oneshot.py
"""
from __future__ import annotations

import argparse
import json
import shutil
import signal
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from common import (ROOT, Run, ANCHOR_PARENT_SCORE, best_score,  # noqa: E402
                    count_log_rows, is_fatal_api_error, reap_orphaned_claude)
from run_arm_b import (MODEL, SYSTEM, CAND_RE, apply_files,  # noqa: E402
                       build_and_eval, build_static_context, call_model)
from run_arm_a_groth16_cont import is_limit_error, seconds_until_reset  # noqa: E402

S0_WS = ROOT / "workspaces" / "S0_korenblum"
REF_FILE = ROOT / "runs" / "reference_budget.json"
KOR = "ProofRefinement/Korenblum"

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
assert _OLD in SYSTEM, "Arm B SYSTEM drifted; re-derive the one-shot edit"
SYSTEM_OS = SYSTEM.replace(_OLD, _NEW)

ONESHOT_TAIL = """
# Now

This is your single attempt: one response, no feedback, no memory. The
harness will write the files you emit, run `lake build` and `Evaluator.py`
once, and record the score; the best evaluator-accepted candidate across
independent one-shot attempts is selected at the end. Emit the complete
candidate file (and ALL supporting files it needs -- the edited
`rigorous_scalar.py` if your candidate cites a new oracle, and the full
`lemma.toml` carrying its matching `[[oracles]]` row -- in this same
response). A candidate that fails to build or verify scores nothing.
"""


def rsync_tree(src: Path, dst: Path):
    subprocess.run(["rsync", "-a", "--delete", str(src) + "/", str(dst) + "/"],
                   check=True, timeout=600)


def reset_korenblum(ws: Path):
    """Restore the writable surface to the pristine S0 state.  The write
    allowlist confines the model to ProofRefinement/Korenblum subpaths and
    the evaluator log (Refinement_Log/log.jsonl) lives there too, so this
    reset makes attempts independent; .lake build caches and the venv are
    untouched."""
    rsync_tree(S0_WS / KOR, ws / KOR)


def new_log_rows(ws: Path, base_n: int) -> list[dict]:
    lj = ws / KOR / "Refinement_Log" / "log.jsonl"
    if not lj.exists():
        return []
    rows = []
    for line in lj.read_text().splitlines():
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return rows[base_n:]


def attempt_best(rows: list[dict]) -> Fraction | None:
    """Highest passing score among this attempt's log rows (c is maximized)."""
    best = None
    for r in rows:
        if not (r.get("pass") and r.get("score")):
            continue
        try:
            v = Fraction(r["score"])
        except (ValueError, ZeroDivisionError):
            continue
        if best is None or v > best:
            best = v
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "armBos"))
    ap.add_argument("--run-id", default="korenblum-armBos-01")
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--stall-cap-h", type=float, default=24.0)
    ap.add_argument("--max-attempts", type=int, default=500)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armBos] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    ref = json.loads(REF_FILE.read_text())
    t_ref = float(ref["T_ref_s"])
    o_ref = int(ref["O_ref_output_tokens"])

    run = Run(a.run_id, "Bos", ws, meta_extra={
        "role": ("ablation: agentic system removed, partial formalization "
                 "kept, MEMORYLESS ONE-SHOT best-of-N (the no-agent "
                 "configuration of docs/2026-07-30-ablation-writeup.md; "
                 "korenblum parity, user decision 2026-07-30)"),
        "protocol": "oneshot_best_of_n",
        "memoryless": ("no history window, no build/evaluator feedback, "
                       "fresh conversation per attempt; the "
                       "ProofRefinement/Korenblum tree is rsync-reset to "
                       "the pristine S0 state between attempts, so every "
                       "attempt is an independent draw from the identical "
                       "prompt and is evaluated against the V64 parent"),
        "selection": ("best evaluator-accepted candidate across attempts; "
                      "the workspace is left holding the winning attempt's "
                      "Korenblum tree"),
        "model": MODEL, "resolved_model": "claude-opus-5",
        "invocation": "claude -p, tools disallowed, subscription auth",
        "limitation": ("runs inside Claude Code, so its agentic system prompt "
                       "is present and some tools remain visible though "
                       "blocked; weaker than an SDK bare-model call, and "
                       "biased in the ablation's favour"),
        "history_window": 0,
        "tools": "none (no tool use, no subagents, no file access)",
        "budget": {"T_ref_s": t_ref, "O_ref_output_tokens": o_ref,
                   "source": str(REF_FILE),
                   "rule": ("1x matched window (user decision 2026-07-30): "
                            "stop before an attempt once active wall > T_ref "
                            "AND recorded output tokens > O_ref; NO early "
                            "success stop; one-attempt overshoot possible, "
                            "recorded"),
                   "provenance_note": ("T_ref is floored at the ORIGINAL "
                                       "run's 8322 s band per "
                                       "reference_budget.json; Arm A's "
                                       "measured wall was 3285.4 s -- the "
                                       "floor is generous to this arm"),
                   "caveat": ("timed-out calls leave server-side generation "
                              "unrecorded; recorded tokens are the gate "
                              "(same convention as B)")},
        "stopping_rule": ("BOTH 1x budgets exhausted: active wall > T_ref "
                          "and recorded output tokens > O_ref (no early "
                          "success stop; best sample kept)"),
        "disclosures": [
            "runs solo: no concurrent A/C CPU contention (favourable to Bos)",
            "static context is built from the pristine S0_korenblum anchor "
            "by run_arm_b.build_static_context -- the same starting context "
            "Arm B's -01 received; none of B's later artifacts are visible",
            "identical prompt every attempt -> later attempts benefit from "
            "prompt-cache reads (cost only; the model sees the same input)",
            "with per-attempt tokens ~125k and the time gate binding, total "
            "recorded tokens will overshoot O_ref severalfold before the "
            "wall budget exhausts -- generous to this arm, disclose "
            "alongside the grothendieck016-armBos overshoot",
        ],
    })
    base_rows, base_fails = count_log_rows(ws)

    def _term(_sig, _frm):
        raise SystemExit(143)
    signal.signal(signal.SIGTERM, _term)

    static = build_static_context(ws)
    (run.dir / "static_context.md").write_text(static)
    prompt = static + ONESHOT_TAIL
    (run.dir / "system_prompt.md").write_text(SYSTEM_OS)
    print(f"[armBos] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armBos] parent {ANCHOR_PARENT_SCORE} = "
          f"{float(ANCHOR_PARENT_SCORE):.6f}; budget: {t_ref:.0f}s AND "
          f"{o_ref} output tokens (both must exhaust)")

    best_dir = run.dir / "best_korenblum"
    overall_best = None            # best accepted score > parent, across attempts
    overall_best_attempt = 0
    n_candidates = n_accepted = 0
    stall_total, stalls = 0.0, 0
    label, evidence = "D5", "stopped without an attempt"

    try:
        for n in range(1, a.max_attempts + 1):
            over_time = run.wall > t_ref
            over_tok = run.tok_out > o_ref
            if over_time and over_tok:
                gate = (f"both 1x budgets exhausted: active wall "
                        f"{run.wall:.0f}s > T_ref {t_ref:.0f}s and "
                        f"{run.tok_out} > O_ref {o_ref} output tokens")
                if overall_best is not None:
                    label = "S"
                    evidence = (f"one-shot best-of-N: best accepted "
                                f"{overall_best} > parent "
                                f"{ANCHOR_PARENT_SCORE} at attempt "
                                f"{overall_best_attempt}; {gate}")
                else:
                    label = "D5"
                    evidence = f"{gate}; no accepted improvement over parent"
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
                res = call_model(prompt, int(45 * 60), SYSTEM_OS)
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
                reset_korenblum(ws)
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
                reset_korenblum(ws)
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

            attempt_score = attempt_best(new_log_rows(ws, base_rows))
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
                        and attempt_score > ANCHOR_PARENT_SCORE
                        and (overall_best is None or attempt_score > overall_best))
            if improved:
                overall_best, overall_best_attempt = attempt_score, n
                rsync_tree(ws / KOR, best_dir)
                run.emit("new_best", attempt=n, score=str(attempt_score),
                         score_float=float(attempt_score),
                         wall_s=round(run.wall, 1), output_tokens=run.tok_out,
                         usd=round(run.usd, 3))
                print(f"[armBos] NEW BEST: {attempt_score} = "
                      f"{float(attempt_score):.6f} (parent "
                      f"{float(ANCHOR_PARENT_SCORE):.6f})", flush=True)

            reset_korenblum(ws)
        else:
            label, evidence = "D5", f"max attempts ({a.max_attempts})"
    except SystemExit as e:
        label = "D5"
        evidence = f"terminated (SIGTERM {e.code}); best={overall_best}"

    # Pick the best: leave the workspace holding the winning attempt's tree.
    if best_dir.exists():
        rsync_tree(best_dir, ws / KOR)

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
