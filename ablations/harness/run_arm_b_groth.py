#!/usr/bin/env python3
"""Grothendieck Arm B -- partial formalization KEPT, agentic system ABLATED.

A bare base-LLM refinement loop over the Lemma 5.4 workspace. One model call
per iteration: text in, text out. No tools, no subagents, no
planner/generator/evaluator, no sprint contracts, no persistent workspace
memory -- only a rolling window of the last K (edit, error) pairs.

The model receives the ENTIRE partial formalization verbatim as prompt-cached
context: SearchConfig, the Lemma54_Paper chain, the LeanProof modules in V24's
import closure, V23+V24, lemma.toml, the whole Numerical_Library, Braverman
et al. (2011) extracted text, and the S0 roadmap (Bulletin + the sprint_029
research summary and probe artifacts). Strictly more than Arm A's generator
holds at once.

Design sect. 12.4. Same documented Claude-Code-invocation limitation as the
korenblum Arm B (sect. 10d): tools disallowed but visible, bias runs in the
ablation's favour.

Usage:  python3 harness/run_arm_b_groth.py [--budget-mult 3.0]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from groth_common import (ROOT, Run, best_score, count_log_rows, goal_reached,  # noqa: E402
                          ANCHOR_PARENT_SCORE, ELAN, is_fatal_api_error,
                          reap_orphaned_claude)

MODEL = "opus"          # resolved by Claude Code; == claude-opus-5
HISTORY_K = 3
L54 = "ProofRefinement/Lemma54"
CAND_RE = re.compile(r"ProofRefinement/Lemma54/Candidates/V\d+\.lean")
BRAVERMAN_TXT = ROOT / "harness" / "braverman2011.txt"

# Files the loop is permitted to write. Anything else the model emits is
# refused and reported back to it (keeps the arm a loop, not a shell).
WRITABLE = (
    f"{L54}/Candidates/",
    f"{L54}/Numerical_Library/",
    f"{L54}/Proof/",
    f"{L54}/Scratch/",
    f"{L54}/lemma.toml",
)

SYSTEM_TMPL = """You are improving a certified upper bound on the Lemma 5.4 \
inverse-expansion constant C_r (Braverman et al. 2011, sect. 5) inside a Lean 4 \
+ Mathlib workspace. Smaller is better.

The workspace currently certifies `Cr_val = {cur}` via the candidate
`Candidates/V{bestn}.lean`. Your task is to produce a candidate that the
workspace's unmodified `Evaluator.py` accepts with a score STRICTLY LESS than
`{cur}`.

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

A candidate passes only if: it declares `theorem lemma_5_4_search` under a
single namespace (convention: `Braverman.PaperV{nextn}`); it compiles under
`lake env lean`; its transitively-used axioms are a subset of
`[seed_axioms].allowed` plus registered `[[oracles]]` axioms; there is no
`sorryAx`; and every used oracle axiom re-verifies.

For an oracle-backed axiom the evaluator IMPORTS AND RUNS the Python function
named in its `[[oracles]]` row -- `importlib.import_module("Numerical_Library")`
then `getattr(mod, oracle_fn)` called with NO arguments -- and checks
`declared <bound_field>_val >= recomputed .bound`. So to certify a new bound
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
(a sup-norm bound on an explicit quantity over an explicit domain).

Work in whatever order you judge best. Be concrete: the harness only acts on
the files you emit.
"""


def system_for(cur, best_n: int) -> str:
    return SYSTEM_TMPL.format(cur=cur, bestn=best_n, nextn=best_n + 1)


# --------------------------------------------------------------- context
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

    parts += ["\n## The paper-side surface (V24's LeanProof import closure)\n",
              block("LeanProof/Lemma54.lean"),
              block("LeanProof/Theorem51.lean"),
              block("LeanProof/Defs/Strip.lean")]

    # The editable subgoal is the HIGHEST-numbered candidate present: on a
    # continuation run that is the arm's own last accepted candidate, not V24.
    cand_dir = ws / L54 / "Candidates"
    cand_files = sorted(cand_dir.glob("V*.lean"),
                        key=lambda q: int(re.findall(r"V(\d+)", q.stem)[0]))
    best_cand = cand_files[-1] if cand_files else None
    parts += ["\n## The editable subgoal: the current best candidate\n"]
    if best_cand is not None and best_cand.name not in ("V24.lean", "V23.lean"):
        parts.append(block(f"{L54}/Candidates/{best_cand.name}"))
    # V24 is the accepted parent; V23 is its latest-content ancestor (V24 is a
    # research-sprint re-issue of V23) -- include both.
    parts += [block(f"{L54}/Candidates/V24.lean"),
              block(f"{L54}/Candidates/V23.lean")]

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
              "\n## Standing roadmap (Bulletin.md at this point in the run)\n",
              block(f"{L54}/Bulletin.md", "markdown"),
              "\n## The sprint_029 research summary "
              "(the roadmap for the next push)\n",
              block(f"{L54}/Scratch/sprint_029_research_summary.md", "markdown")]

    # Roadmap probe artifacts the original planner had on hand: the reusable
    # merged-numerator scanner and the sprint_029 probe scripts + outputs.
    for p in sorted((ws / L54 / "Scratch").glob("sprint_029_*")):
        if p.name == "sprint_029_research_summary.md" or not p.is_file():
            continue
        lang = "python" if p.suffix == ".py" else "text"
        parts.append(block(f"{L54}/Scratch/{p.name}", lang))
    parts.append(block(f"{L54}/Scratch/sprint_022_planner_full_merge.py", "python"))

    parts += ["\n## The contract that produced the current candidate (V24)\n",
              block(f"{L54}/Sprint_Contracts/sprint_029.md", "markdown")]
    return "".join(parts)


# ------------------------------------------------------------ file emission
FENCE = re.compile(r"```(?P<lang>[a-zA-Z0-9_+-]*)\s+path=(?P<path>[^\s`]+)\s*\n"
                   r"(?P<body>.*?)```", re.S)


def apply_files(ws: Path, text: str) -> tuple[list[str], list[str]]:
    written, refused = [], []
    for m in FENCE.finditer(text):
        rel = m.group("path").strip().lstrip("./")
        if not any(rel.startswith(w) for w in WRITABLE):
            refused.append(f"{rel} (not a writable path)")
            continue
        target = (ws / rel).resolve()
        if not str(target).startswith(str(ws.resolve())):
            refused.append(f"{rel} (escapes workspace)")
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(m.group("body"))
        written.append(rel)
    return written, refused


# Same documented limitation as the korenblum Arm B (design sect. 10d).
DISALLOWED = ",".join([
    "Bash", "Read", "Write", "Edit", "MultiEdit", "NotebookEdit", "Glob", "Grep",
    "WebSearch", "WebFetch", "Task", "Agent", "TodoWrite", "Skill", "Workflow",
    "ToolSearch", "ReportFindings", "ScheduleWakeup", "Artifact",
    "AskUserQuestion", "Monitor", "SendMessage", "TaskCreate", "TaskUpdate",
    "TaskList", "TaskGet", "TaskOutput", "TaskStop", "EnterPlanMode",
    "ExitPlanMode", "CronCreate", "CronList", "CronDelete",
])


def call_model(prompt: str, timeout_s: int, system_prompt: str) -> dict:
    """One tool-less model call via `claude -p`, billed to the subscription."""
    env = {**os.environ, "PATH": ELAN + os.pathsep + os.environ["PATH"]}
    env.pop("ANTHROPIC_API_KEY", None)
    env.pop("ANTHROPIC_AUTH_TOKEN", None)
    p = subprocess.run(
        ["claude", "-p", "--output-format", "json", "--model", MODEL,
         "--permission-mode", "bypassPermissions",
         "--disallowed-tools", DISALLOWED,
         "--append-system-prompt", system_prompt],
        input=prompt, cwd="/tmp", capture_output=True, text=True,
        env=env, timeout=timeout_s)
    raw = p.stdout
    i = raw.find("{")
    if i < 0:
        return {"is_error": True, "result": (raw or p.stderr)[-2000:]}
    try:
        return json.loads(raw[i:])
    except json.JSONDecodeError:
        return {"is_error": True, "result": raw[-2000:]}


# ------------------------------------------------------------ build + eval
def build_and_eval(ws: Path, cand_rel: str) -> tuple[bool, str, dict]:
    env = {**os.environ, "PATH": ELAN + os.pathsep + os.environ["PATH"]}
    target = cand_rel.replace(".lean", "").replace("/", ".")

    b = subprocess.run(["lake", "build", target], cwd=ws, capture_output=True,
                       text=True, env=env, timeout=3600)
    if b.returncode != 0:
        tail = (b.stdout + b.stderr)[-6000:]
        return False, f"$ lake build {target}\n[FAILED]\n{tail}", {"stage": "build"}

    # Lemma54's Evaluator prints a bare `PASS` line and exits 0 on full pass,
    # 2 otherwise -- there is no `status:` line. Exit code is the only robust
    # signal. Invoked with the workspace venv (validated by gate_s0) and the
    # repo-root-relative --file path resolved against cwd=ws.
    e = subprocess.run(
        [str(ws / ".venv" / "bin" / "python"),
         f"{L54}/Evaluator.py", "--file", cand_rel],
        cwd=ws, capture_output=True, text=True, env=env, timeout=3600)
    out = (e.stdout + e.stderr)
    ok = e.returncode == 0
    return ok, (f"$ lake build {target}\n[OK]\n\n"
                f"$ Evaluator.py --file {cand_rel}\n{out[-8000:]}"), \
        {"stage": "evaluator", "passed": ok}


# ------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "groth_armB"))
    ap.add_argument("--run-id", default="grothendieck-armB-01")
    ap.add_argument("--budget-mult", type=float, default=3.0)
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--max-iters", type=int, default=1000)
    ap.add_argument("--carry-wall-s", type=float, default=0.0)
    ap.add_argument("--carry-out-tokens", type=int, default=0)
    ap.add_argument("--carry-usd", type=float, default=0.0)
    ap.add_argument("--carry-from", default="")
    ap.add_argument("--start-iter", type=int, default=1)
    ap.add_argument("--continue-after-success", action="store_true")
    ap.add_argument("--t-budget-s", type=float, default=None)
    ap.add_argument("--o-budget-tokens", type=float, default=None)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armB] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    ref = json.loads((ROOT / "runs" / "reference_budget_groth.json").read_text())
    t_budget = a.t_budget_s if a.t_budget_s is not None else ref["T_ref_s"] * a.budget_mult
    o_budget = (a.o_budget_tokens if a.o_budget_tokens is not None
                else ref["O_ref_output_tokens"] * a.budget_mult)

    run = Run(a.run_id, "B", ws, meta_extra={
        "role": "ablation: agentic system removed, partial formalization kept",
        "model": MODEL, "resolved_model": "claude-opus-5",
        "invocation": "claude -p, tools disallowed, subscription auth",
        "limitation": ("runs inside Claude Code, so its agentic system prompt "
                       "is present and some tools remain visible though "
                       "blocked; weaker than an SDK bare-model call, and "
                       "biased in the ablation's favour"),
        "history_window": HISTORY_K,
        "tools": "none (no tool use, no subagents, no file access)",
        "reference_budget": ref,
        "stopping_rule": (f"run until wall_clock > {a.budget_mult}x T_ref AND "
                          f"output_tokens > {a.budget_mult}x O_ref"),
        "budget": {"T_budget_s": t_budget, "O_budget_tokens": o_budget},
    })
    run.t0 -= a.carry_wall_s
    run.tok_out += a.carry_out_tokens
    run.usd += a.carry_usd
    if a.carry_wall_s or a.carry_out_tokens:
        run.manifest["carried_forward"] = {
            "from_run": a.carry_from, "wall_s": a.carry_wall_s,
            "output_tokens": a.carry_out_tokens, "usd": a.carry_usd,
            "note": "prior process cut short externally; work carried forward"}
        (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))
    base_evals, base_fails = count_log_rows(ws)

    def current_state():
        cur = best_score(ws)
        cur = ANCHOR_PARENT_SCORE if cur is None else cur
        cands = sorted((ws / L54 / "Candidates").glob("V*.lean"),
                       key=lambda q: int(re.findall(r"V(\d+)", q.stem)[0]))
        best_n = int(re.findall(r"V(\d+)", cands[-1].stem)[0]) if cands else 24
        return cur, best_n

    static = build_static_context(ws)
    (run.dir / "static_context.md").write_text(static)
    print(f"[armB] static context: {len(static)} chars (~{len(static)//4} tokens)")
    print(f"[armB] budget: {t_budget/3600:.2f} h AND {o_budget} output tokens")

    prev_best = best_score(ws)
    history: deque[tuple[str, str]] = deque(maxlen=HISTORY_K)
    label, evidence = "D5", "budget exhausted"
    last_feedback = ("No attempt yet. Produce your first candidate.\n"
                     "Remember: emit the ENTIRE file, in a fenced block with "
                     "`path=` in the info string.")

    for n in range(a.start_iter, a.start_iter + a.max_iters):
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
        print(f"[armB] iter {n}  (elapsed {run.wall/60:.1f}m / {t_budget/60:.0f}m, "
              f"out_tok {run.tok_out}/{o_budget})", flush=True)
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
            print(f"[armB] ABORT (D7): {evidence}", flush=True)
            break
        if res.get("is_error"):
            run.emit("llm_error", iteration=n, error=(res.get("result") or "")[:500])
            print(f"       ! error: {(res.get('result') or '')[:160]}", flush=True)
            time.sleep(20)
            continue

        text = res.get("result") or ""
        run.account(res)             # modelUsage-based
        u = res.get("usage") or {}

        written, refused = apply_files(ws, text)
        (run.dir / f"iter_{n:04d}_response.md").write_text(text)

        if not written:
            last_feedback = ("You emitted no writable file. Emit a complete file "
                             "in a fenced block whose info string contains "
                             "`path=<workspace-relative path>`."
                             + (f" Refused: {refused}" if refused else ""))
            run.emit("iteration", iteration=n, written=[], refused=refused,
                     usage=u, wall_s=round(time.time() - t0, 1),
                     no_files=True)
            history.append(("(none)", last_feedback))
            continue

        cands = [c for c in written if CAND_RE.fullmatch(c)]
        if not cands:
            # Staged work (numerics first, Lean second) is legitimate; give the
            # same verbatim import signal the evaluator itself would. Import as
            # a package with sys.path at the Lemma54 root, exactly like
            # Evaluator.py does (its types.py shadows stdlib `types` otherwise).
            checks = []
            for rel in written:
                if not rel.endswith(".py") or "/Numerical_Library/" not in rel:
                    continue
                mod = Path(rel).stem
                pr = subprocess.run(
                    [str(ws / ".venv" / "bin" / "python"), "-c",
                     f"import sys; sys.path.insert(0, '{L54}'); "
                     f"import importlib; importlib.import_module("
                     f"'Numerical_Library.{mod}'); "
                     f"print('import OK: Numerical_Library.{mod}')"],
                    cwd=ws, capture_output=True, text=True,
                    env={**os.environ,
                         "PATH": ELAN + os.pathsep + os.environ["PATH"]},
                    timeout=900)
                checks.append(f"$ python -c 'import Numerical_Library.{mod}'\n"
                              f"{(pr.stdout + pr.stderr)[-2500:]}")
            last_feedback = (
                ("\n\n".join(checks) + "\n\n" if checks else "")
                + "No candidate was emitted this turn, so `lake build` and "
                  "`Evaluator.py` did not run -- they need a file at\n"
                  f"`{L54}/Candidates/V<N>.lean`.\n"
                  "Nothing is scored until you emit one.")
            run.emit("iteration", iteration=n, written=written, refused=refused,
                     usage=u, wall_s=round(time.time() - t0, 1),
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
        print(f"       -> wrote {written} passed={ok} score={best_score(ws)} "
              f"${run.usd:.2f}", flush=True)

        last_feedback = feedback
        history.append((", ".join(written), feedback))

        if goal_reached(ws):
            cur = best_score(ws)
            if cur != prev_best:
                run.emit("new_best", iteration=n, score=str(cur),
                         score_float=float(cur), wall_s=round(run.wall, 1),
                         output_tokens=run.tok_out, usd=round(run.usd, 3))
                print(f"[armB] NEW BEST: {cur} = {float(cur):.9f} "
                      f"@ {run.wall/3600:.2f}h / {run.tok_out} tok", flush=True)
                prev_best = cur
            label = "S"
            evidence = (f"evaluator accepted {cur} < {ANCHOR_PARENT_SCORE} "
                        f"at iteration {n}")
            if not a.continue_after_success:
                print(f"[armB] GOAL REACHED: {evidence}")
                break

    print(json.dumps(run.finish(label, evidence), indent=2))


if __name__ == "__main__":
    main()
