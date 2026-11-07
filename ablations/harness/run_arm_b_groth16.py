#!/usr/bin/env python3
"""Sprint-016 Grothendieck Arm B'' -- partial formalization KEPT, agentic
system ABLATED. Bare base-LLM loop over the S0^16 Lemma54 workspace.

Sect. 13.4: same loop mechanics as the sect. 12 Arm B (whole files in fenced
blocks, write-allowlist, verbatim build+evaluator feedback, K=3 history,
tools disallowed under Claude Code with the sect. 10d disclosure), with the
era context: SearchConfig + the 8-module Lemma54_Paper chain + V11's
LeanProof import closure + V10/V11 + lemma.toml + the whole era
Numerical_Library + ALL 16 pre-anchor Scratch scripts + Bulletin + the
sprint_015 contract + Braverman (2011). No sprint_029 roadmap exists at this
anchor -- none is included (discovery parity, sect. 13.1).

The system prompt states the BAR explicitly (uniform-bar principle): success
is an accepted candidate with Cr_val <= BAR; smaller-but-above-BAR accepted
candidates are logged as within-envelope progress, not success.

Stopping (user decision 2026-07-29): runs concurrently with Arm A; stops at
success, or when the matched wall-clock window closes -- the pipeline writes
runs/groth16_deadline.json with t_ref_s = max(T_armA, 2360 s) once Arm A
finishes, and this runner exits at wall > t_ref_s (checked between
iterations; the pipeline hard-kills after a grace period).
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
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth16_common import (ROOT, Run, ANCHOR_PARENT_SCORE, bar,  # noqa: E402
                            bar_reached, best_score, count_log_rows,
                            is_fatal_api_error, load_envelope,
                            reap_orphaned_claude)
from run_arm_b_groth import (CAND_RE, BRAVERMAN_TXT, DISALLOWED,  # noqa: E402
                             apply_files, build_and_eval, call_model)

MODEL = "opus"
HISTORY_K = 3
L54 = "ProofRefinement/Lemma54"

SYSTEM_TMPL = """You are improving a certified upper bound on the Lemma 5.4 \
inverse-expansion constant C_r (Braverman et al. 2011, sect. 5) inside a Lean 4 \
+ Mathlib workspace. Smaller is better.

The workspace currently certifies `Cr_val = {cur}` via the candidate
`Candidates/V{bestn}.lean`. **Your goal is a candidate that the workspace's
unmodified `Evaluator.py` accepts with `Cr_val <= {bar}`** (the study's
success bar, fixed before this run). An accepted candidate with a smaller
`Cr_val` than the current one is recorded as progress, but only
`Cr_val <= {bar}` counts as success.

You are not an agent. You cannot run commands, read files, or search. Every
input you will ever get is in this conversation. You produce whole files as
text; a harness writes them, runs `lake build` and `Evaluator.py`, and returns
the verbatim output to you.

## How to emit files

Emit each complete file in a fenced block whose info string carries its path:

```lean path=ProofRefinement/Lemma54/Candidates/V{nextn}.lean
<the entire file>
```

You may also emit:
```python path=ProofRefinement/Lemma54/Numerical_Library/<module>.py
```toml path=ProofRefinement/Lemma54/lemma.toml
```

Emit the ENTIRE file every time -- never a diff, never an ellipsis. Files are
written verbatim; a truncated file is a broken file. If a change spans several
coupled files (candidate + oracle module + `Numerical_Library/__init__.py` +
`lemma.toml`), emit ALL of them in the same response.

## The evaluator gate (unmodified)

A candidate passes only if: it declares `theorem lemma_5_4_search` under the
workspace's candidate namespace (`Braverman.PaperV0`, as V11 uses); it
compiles under `lake env lean`; its transitively-used axioms are a subset of
`[seed_axioms].allowed` plus registered `[[oracles]]` axioms; there is no
`sorryAx`; and every used oracle axiom re-verifies.

For an oracle-backed axiom the evaluator IMPORTS AND RUNS the Python function
named in its `[[oracles]]` row -- `importlib.import_module("Numerical_Library")`
then `getattr(mod, oracle_fn)` called with NO arguments -- and checks
`declared <bound_field> >= recomputed .bound`. So to certify a new bound
you emit a new module in `Numerical_Library/`, re-export its function from
`Numerical_Library/__init__.py`, and add the matching `[[oracles]]` row
(`axiom = ...`, `bound_field = ...`, `oracle_fn = ...`). The function must run
at its module-level defaults and return an object with a rational `.bound`
(use `Numerical_Library.types.OracleResult` like the existing oracles). You do
not, and cannot, run anything yourself.

## What does not count

A direct-conclusion axiom is not progress: an axiom whose statement asserts
the sink inequality (the `... <= Cr_val * p ^ 2` conclusion) at your own
candidate's score proves nothing, even if allow-listed. Any new axiom must be
a genuine numerical sub-claim of the same shape as the existing oracle axioms
(a sup-norm bound on an explicit quantity over an explicit domain). The
workspace's trusted analytic axioms (e.g. `h_oracle_domain_contains_image`)
and the locked `SearchConfig` constants must keep their exact meaning: a
candidate that weakens what the trust surface asserts (shrinking the oracle
rectangle, changing r or eta, editing frozen Proof/Lib theorems) is a trust
violation, not progress.

Work in whatever order you judge best. Be concrete: the harness only acts on
the files you emit.
"""


def system_for(cur, best_n: int) -> str:
    b = bar()
    return SYSTEM_TMPL.format(cur=cur, bestn=best_n, nextn=best_n + 1,
                              bar=f"{b.numerator}/{b.denominator}")


def build_static_context(ws: Path) -> str:
    def block(rel: str, lang: str = "lean", label: str | None = None) -> str:
        p = ws / rel
        if not p.exists():
            return ""
        return (f"\n### `{label or rel}`\n\n```{lang}\n"
                f"{p.read_text()}\n```\n")

    parts = ["# The workspace\n",
             "## The search configuration (locked constants r=23/25, eta=1/100)\n",
             block(f"{L54}/Proof/SearchConfig.lean"),
             "\n## The reduction chain (the partial formalization)\n"]
    for p in sorted((ws / L54 / "Proof" / "Lib").glob("*.lean")):
        parts.append(block(f"{L54}/Proof/Lib/{p.name}"))

    parts += ["\n## The paper-side surface (V11's LeanProof import closure)\n",
              block("LeanProof/Lemma54.lean"),
              block("LeanProof/Theorem51.lean"),
              block("LeanProof/Defs/Strip.lean")]

    cand_dir = ws / L54 / "Candidates"
    cand_files = sorted(cand_dir.glob("V*.lean"),
                        key=lambda q: int(re.findall(r"V(\d+)", q.stem)[0]))
    best_cand = cand_files[-1] if cand_files else None
    parts += ["\n## The editable subgoal: the current best candidate\n"]
    if best_cand is not None and best_cand.name not in ("V11.lean", "V10.lean"):
        parts.append(block(f"{L54}/Candidates/{best_cand.name}"))
    parts += [block(f"{L54}/Candidates/V11.lean"),
              block(f"{L54}/Candidates/V10.lean")]

    parts += ["\n## The trust surface\n",
              block(f"{L54}/lemma.toml", "toml"),
              "\n## The numerical library (the evaluator runs these itself)\n"]
    nl = ws / L54 / "Numerical_Library"
    for p in sorted(nl.glob("*.py")):
        parts.append(block(f"{L54}/Numerical_Library/{p.name}", "python"))

    parts += ["\n## The paper (Braverman et al. 2011, extracted text)\n"]
    if BRAVERMAN_TXT.exists():
        parts.append(f"\n```text\n{BRAVERMAN_TXT.read_text()}\n```\n")

    parts += ["\n## Workspace brief\n",
              block(f"{L54}/AGENT_BRIEF.md", "markdown"),
              "\n## Workspace memory (Bulletin.md, whole)\n",
              block(f"{L54}/Bulletin.md", "markdown"),
              "\n## Pre-anchor Scratch scripts (all of them; the same "
              "planner probes the with-agent arm can read)\n"]
    for p in sorted((ws / L54 / "Scratch").glob("*.py")):
        parts.append(block(f"{L54}/Scratch/{p.name}", "python"))

    parts += ["\n## The contract that produced the current candidate (V11)\n",
              block(f"{L54}/Sprint_Contracts/sprint_015.md", "markdown")]
    return "".join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth16_armB"))
    ap.add_argument("--run-id", default="grothendieck016-armB-01")
    ap.add_argument("--deadline-file",
                    default=str(ROOT / "runs" / "groth16_deadline.json"))
    ap.add_argument("--hard-cap-h", type=float, default=12.0)
    ap.add_argument("--max-iters", type=int, default=1000)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armB16] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    dl_file = Path(a.deadline_file)
    env = load_envelope()

    run = Run(a.run_id, "B", ws, meta_extra={
        "role": "ablation: agentic system removed, partial formalization kept",
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
                          "wall-clock window: wall > t_ref_s from "
                          "runs/groth16_deadline.json (= max(T_armA, 2360 s); "
                          "user decision 2026-07-29, 1x matched budget, "
                          "concurrent with Arm A)"),
    })
    base_evals, base_fails = count_log_rows(ws)

    # Graceful SIGTERM: the pipeline sends it at deadline + grace.
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
    print(f"[armB16] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armB16] BAR={bar()} (~{float(bar()):.3g}); deadline file: {dl_file}")

    prev_best = best_score(ws)
    history: deque[tuple[str, str]] = deque(maxlen=HISTORY_K)
    label, evidence = "D5", "stopped without reaching BAR"
    last_feedback = ("No attempt yet. Produce your first candidate.\n"
                     "Remember: emit the ENTIRE file, in a fenced block with "
                     "`path=` in the info string.")

    try:
        for n in range(1, a.max_iters + 1):
            if dl_file.exists():
                t_ref = json.loads(dl_file.read_text())["t_ref_s"]
                if run.wall > t_ref:
                    label = "D5"
                    evidence = (f"1x matched wall-clock window closed: "
                                f"{run.wall:.0f}s > T_ref {t_ref:.0f}s")
                    if best_score(ws) is not None and best_score(ws) < ANCHOR_PARENT_SCORE:
                        evidence += (f" (within-envelope best "
                                     f"{best_score(ws)}, above BAR {bar()})")
                    break
            if run.wall > a.hard_cap_h * 3600:
                label, evidence = "D5", f"hard cap {a.hard_cap_h}h"
                break

            hist = "".join(
                f"\n### Earlier attempt {i}\nFiles you emitted: {w}\nResult:\n```\n{r}\n```\n"
                for i, (w, r) in enumerate(history, 1))
            prompt = (static
                      + f"\n# Recent attempts (most recent last, window={HISTORY_K})\n"
                      + (hist or "(none yet)")
                      + f"\n\n# Latest result\n\n```\n{last_feedback}\n```\n"
                      + "\n# Now\n\nEmit the next full candidate file "
                        "(and any supporting files).")

            t0 = time.time()
            print(f"[armB16] iter {n} (elapsed {run.wall/60:.1f}m, "
                  f"out_tok {run.tok_out}, ${run.usd:.2f})", flush=True)
            cur, best_n = current_state()
            try:
                res = call_model(prompt, int(45 * 60), system_for(cur, best_n))
            except subprocess.TimeoutExpired:
                run.emit("llm_timeout", iteration=n)
                print("       ! model call timed out", flush=True)
                continue

            if res.get("is_error") and is_fatal_api_error(res.get("result") or ""):
                label = "D7"
                evidence = f"fatal API condition: {(res.get('result') or '')[:200]}"
                run.emit("fatal_api", iteration=n, result=res.get("result"))
                print(f"[armB16] ABORT (D7): {evidence}", flush=True)
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
                print(f"[armB16] NEW BEST: {cur2} = {float(cur2):.3e} "
                      f"(BAR {float(bar()):.3e})", flush=True)
                prev_best = cur2

            if bar_reached(ws):
                label = "S"
                evidence = (f"evaluator accepted {best_score(ws)} <= BAR "
                            f"{bar()} at iteration {n}")
                print(f"[armB16] BAR REACHED: {evidence}")
                break
        else:
            label, evidence = "D5", f"max iters ({a.max_iters})"
    except SystemExit as e:
        if label != "S":
            label = "D5"
            evidence = (f"terminated at matched window (SIGTERM {e.code}); "
                        f"best={best_score(ws)}")

    print(json.dumps(run.finish(label, evidence), indent=2))


if __name__ == "__main__":
    main()
