#!/usr/bin/env python3
"""Arm B -- partial formalization KEPT, agentic system ABLATED.

A bare base-LLM refinement loop.  One model call per iteration: text in, text
out.  No tools, no subagents, no planner/generator/evaluator, no sprint
contracts, no persistent workspace memory -- only a rolling window of the last
K (edit, error) pairs.

The model receives the ENTIRE partial formalization verbatim as prompt-cached
context (~200K tokens): the contract, Reduction.lean in full, all 19
KorenblumPaper modules, V64 and its derived-theorem files, lemma.toml, the
numerical library, Wang (2025), and the S0 roadmap.  That is strictly more than
Arm A's generator sees at any one moment -- Arm A has to go and read files.

It emits whole files as text.  The loop writes them and runs the unmodified
`lake build` + `Evaluator.py`.  Numerical certification needs no tool: the
evaluator resolves and runs the registered oracle function itself, so a new
certificate is produced by emitting an edited `rigorous_scalar.py` plus a new
`[[oracles]]` row, exactly as Lean is produced by emitting Lean.

Usage:  python3 harness/run_arm_b.py [--budget-mult 3.0]
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
from common import (ROOT, Run, best_score, count_log_rows, goal_reached,  # noqa: E402
                    ANCHOR_PARENT_SCORE, ELAN, is_fatal_api_error,
                    reap_orphaned_claude)


MODEL = "opus"          # resolved by Claude Code; == claude-opus-5
# effort/max_tokens are inherited from the Claude Code session config
# (settings.json: effortLevel=xhigh) rather than set per-call.
HISTORY_K = 3
CANDIDATE = "ProofRefinement/Korenblum/Candidates/V65.lean"
CAND_RE = re.compile(r"ProofRefinement/Korenblum/Candidates/V\d+\.lean")

# Files the loop is permitted to write. Anything else the model emits is
# refused and reported back to it (keeps the arm a loop, not a shell).
WRITABLE = (
    "ProofRefinement/Korenblum/Candidates/",
    "ProofRefinement/Korenblum/Numerical_Library/",
    "ProofRefinement/Korenblum/Proof/",
    "ProofRefinement/Korenblum/lemma.toml",
)

SYSTEM = f"""You are improving a certified lower bound on the Korenblum constant \
inside a Lean 4 + Mathlib workspace.

The workspace currently certifies `c = 35646/100000 = 0.35646` via the candidate
`Candidates/V64.lean`. Your task is to produce a candidate that the workspace's
unmodified `Evaluator.py` accepts with a score STRICTLY GREATER than
`17823/50000`.

You are not an agent. You cannot run commands, read files, or search. Every
input you will ever get is in this conversation. You produce whole files as
text; a harness writes them, runs `lake build` and `Evaluator.py`, and returns
the verbatim output to you.

## How to emit files

Emit each complete file in a fenced block whose info string carries its path:

```lean path=ProofRefinement/Korenblum/Candidates/V65.lean
<the entire file>
```

You may also emit:
```python path=ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py
```toml path=ProofRefinement/Korenblum/lemma.toml
```

Emit the ENTIRE file every time -- never a diff, never an ellipsis. Files are
written verbatim; a truncated file is a broken file.

## The evaluator gate (unmodified)

A candidate passes only if it compiles, type-checks, its transitively-used
axioms are a subset of `[seed_axioms].allowed` plus registered `[[oracles]]`,
there is no `sorryAx`, and `c_value` beats the parent.

For an oracle-backed axiom the evaluator IMPORTS AND RUNS the Python function
named in its `[[oracles]]` row and checks the recomputed bound against the
candidate's declared `bound_field`. So to certify a new `c` you edit
`rigorous_scalar.py` to add a wrapper and add the matching `[[oracles]]` row --
you do not, and cannot, run anything yourself.

## What does not count

A direct-conclusion axiom at a larger `c` is not progress. Adding an axiom that
asserts the very thing to be proved, and allow-listing it, satisfies the letter
of the gate while proving nothing. Any new axiom must be a genuine sub-claim,
strictly weaker than the conclusion.

Work in whatever order you judge best. Be concrete: the harness only acts on
the files you emit.
"""


# --------------------------------------------------------------- context
def build_static_context(ws: Path) -> str:
    def block(rel: str, lang: str = "lean", label: str | None = None) -> str:
        p = ws / rel
        if not p.exists():
            return ""
        return (f"\n### `{label or rel}`\n\n```{lang}\n"
                f"{p.read_text()}\n```\n")

    parts = ["# The workspace\n",
             "## The candidate contract (what must be proved)\n",
             block("ProofRefinement/Korenblum/Proof/CandidateContract.lean"),
             "\n## The reduction chain (the partial formalization)\n",
             block("ProofRefinement/Korenblum/Proof/Reduction.lean"),
             "\n## The paper-side surface (Wang 2025, Section 2, formalized)\n"]

    for p in sorted((ws / "KorenblumPaper").glob("*.lean")):
        parts.append(block(f"KorenblumPaper/{p.name}"))

    # The editable subgoal is the HIGHEST-numbered candidate present: on a
    # continuation run that is the arm's own last accepted candidate, not V64.
    cand_files = sorted((ws / "ProofRefinement/Korenblum/Candidates").glob("V*.lean"),
                        key=lambda q: int(re.findall(r"V(\d+)", q.stem)[0]))
    best_cand = cand_files[-1] if cand_files else None
    parts += ["\n## The editable subgoal: the current best candidate\n"]
    if best_cand is not None and best_cand.name != "V64.lean":
        parts.append(block(f"ProofRefinement/Korenblum/Candidates/{best_cand.name}"))
        sub = ws / "ProofRefinement/Korenblum/Candidates" / best_cand.stem
        if sub.is_dir():
            for q in sorted(sub.glob("*.lean")):
                parts.append(block(f"ProofRefinement/Korenblum/Candidates/{best_cand.stem}/{q.name}"))
    parts += [block("ProofRefinement/Korenblum/Candidates/V64.lean"),
              block("ProofRefinement/Korenblum/Candidates/V64/TauWindowEndpoints.lean")]
    for p in sorted((ws / "ProofRefinement/Korenblum/Candidates/V63").glob("*.lean")):
        parts.append(block(f"ProofRefinement/Korenblum/Candidates/V63/{p.name}"))

    parts += ["\n## The trust surface\n",
              block("ProofRefinement/Korenblum/lemma.toml", "toml"),
              "\n## The numerical library (the evaluator runs these itself)\n",
              block("ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py", "python"),
              "\n## The paper\n",
              block("ProofRefinement/Korenblum/Wang2025.txt", "text"),
              "\n## Workspace brief\n",
              block("ProofRefinement/Korenblum/AGENT_BRIEF.md", "markdown")]

    # The S0 roadmap: exactly what Arm A's planner reads at this point. The
    # ablated factor is agency, not information, so Arm B gets it too.
    bulletin = (ws / "ProofRefinement/Korenblum/Bulletin.md").read_text().splitlines()
    head = "\n".join(bulletin[:1010])
    parts += ["\n## Standing roadmap (from Bulletin.md at this point in the run)\n",
              f"\n```markdown\n{head}\n```\n"]
    c083 = ws / ("ProofRefinement/Korenblum/Sprint_Contracts/"
                 "sprint_083_v64_first_c_push_past_v52_sqrt_endpoints.md")
    if c083.exists():
        parts += ["\n## The contract that produced the current candidate (V64)\n",
                  f"\n```markdown\n{c083.read_text()}\n```\n"]
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


# Claude Code exposes a tool surface even with --allowed-tools "". We disallow
# every tool we can name so none can execute. DOCUMENTED LIMITATION (design
# sect. 3.2): the arm still runs inside Claude Code, so its agentic system
# prompt is present and a handful of tools remain *visible* though blocked.
# This is weaker than the SDK-direct bare-model call the design specifies; it
# was chosen so the run bills to the claude.ai subscription rather than API
# credits. Any residual agency biases the result in the ablation's FAVOUR
# (Arm B looks more capable than a true bare model), so it cannot manufacture
# the "no-agent arm fails" conclusion.
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
    env.pop("ANTHROPIC_API_KEY", None)      # else it overrides the claude.ai login
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
    module = (cand_rel.replace("ProofRefinement/Korenblum/", "")
              .replace(".lean", "").replace("/", "."))
    target = f"ProofRefinement.Korenblum.{module}"

    b = subprocess.run(["lake", "build", target], cwd=ws, capture_output=True,
                       text=True, env=env, timeout=3600)
    if b.returncode != 0:
        tail = (b.stdout + b.stderr)[-6000:]
        return False, f"$ lake build {target}\n[FAILED]\n{tail}", {"stage": "build"}

    e = subprocess.run(
        ["uv", "run", "ProofRefinement/Korenblum/Evaluator.py",
         "--file", cand_rel],
        cwd=ws, capture_output=True, text=True,
        env={**env, "UV_CACHE_DIR": str(ws / ".uv-cache")}, timeout=3600)
    out = (e.stdout + e.stderr)
    ok = "status: PASS" in out
    return ok, f"$ lake build {target}\n[OK]\n\n$ Evaluator.py --file {cand_rel}\n{out[-8000:]}", \
        {"stage": "evaluator", "passed": ok}


# ------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=str(ROOT / "workspaces" / "armB"))
    ap.add_argument("--run-id", default="korenblum-armB-01")
    ap.add_argument("--budget-mult", type=float, default=3.0)
    ap.add_argument("--hard-cap-h", type=float, default=24.0)
    ap.add_argument("--max-iters", type=int, default=1000)
    ap.add_argument("--carry-wall-s", type=float, default=0.0)
    ap.add_argument("--carry-out-tokens", type=int, default=0)
    ap.add_argument("--carry-usd", type=float, default=0.0)
    ap.add_argument("--carry-from", default="")
    ap.add_argument("--start-iter", type=int, default=1)
    # Keep improving after the first success instead of stopping. Turns the arm
    # from "did it succeed?" into "how far can it get on the allotted budget?",
    # which is what the budget-vs-progress curve (design sect. 4.2) needs.
    ap.add_argument("--continue-after-success", action="store_true")
    # Explicit budget overrides. reference_budget.json floors T_ref at the
    # ORIGINAL run's 8322s band (design sect. 10c); when the target is a
    # multiple of Arm A's own MEASURED wall clock instead, set it directly.
    ap.add_argument("--t-budget-s", type=float, default=None)
    ap.add_argument("--o-budget-tokens", type=float, default=None)
    a = ap.parse_args()

    n_reaped = reap_orphaned_claude()
    if n_reaped:
        print(f"[armB] reaped {n_reaped} orphaned claude proc(s)")
    ws = Path(a.workspace)
    ref = json.loads((ROOT / "runs" / "reference_budget.json").read_text())
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
            "note": ("prior process was killed externally (no traceback, no "
                     "summary), not stopped by the budget rule; its completed "
                     "iterations are carried forward")}
        (run.dir / "manifest.json").write_text(json.dumps(run.manifest, indent=2))
    base_evals, base_fails = count_log_rows(ws)

    # The target is whatever the workspace already certifies -- on a
    # continuation run that is the arm's own previous best, not the anchor
    # parent. SYSTEM is rebuilt each iteration so the goal stays current.
    def system_for(cur):
        return SYSTEM.replace("35646/100000 = 0.35646", f"{cur} = {float(cur):.6f}") \
                     .replace("`17823/50000`", f"`{cur}`")

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
        try:
            res = call_model(prompt, int(45 * 60),
                             system_for(best_score(ws) or ANCHOR_PARENT_SCORE))
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
        run.account(res)             # modelUsage-based; see common.account()
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

        # The candidate is the TOP-LEVEL Candidates/V<N>.lean. A path one level
        # deeper (Candidates/V<N>/Helper.lean) is a derived-theorem file, not
        # the candidate -- grading that instead silently evaluates the wrong
        # file and manufactures failures.
        cands = [c for c in written if CAND_RE.fullmatch(c)]
        if not cands:
            # The model legitimately stages work (numerics first, Lean second).
            # Returning only a scolding would leave it blind as to whether its
            # Python even imports -- a harness handicap, NOT the intended
            # "no tools" ablation. Give it the same verbatim signal the design
            # promises: import-check every module it just wrote.
            # Import exactly the way Evaluator.py does (`_resolve_oracle_fn`):
            # as a PACKAGE, `Numerical_Library.<mod>`, with cwd at
            # ProofRefinement/Korenblum. Putting Numerical_Library itself on
            # sys.path makes its legitimate `types.py` shadow the stdlib
            # `types` module and produces a spectacular, entirely fake
            # traceback -- which is what this check did on its first outing.
            checks = []
            korenblum = ws / "ProofRefinement" / "Korenblum"
            for rel in written:
                if not rel.endswith(".py"):
                    continue
                mod = Path(rel).stem
                pr = subprocess.run(
                    ["uv", "run", "python", "-c",
                     f"import importlib; importlib.import_module("
                     f"'Numerical_Library.{mod}'); "
                     f"print('import OK: Numerical_Library.{mod}')"],
                    cwd=korenblum, capture_output=True, text=True,
                    env={**os.environ, "PATH": ELAN + os.pathsep + os.environ["PATH"],
                         "UV_CACHE_DIR": str(ws / ".uv-cache")}, timeout=900)
                checks.append(f"$ python -c 'import Numerical_Library.{mod}'\n"
                              f"{(pr.stdout + pr.stderr)[-2500:]}")
            last_feedback = (
                ("\n\n".join(checks) + "\n\n" if checks else "")
                + "No candidate was emitted this turn, so `lake build` and "
                  "`Evaluator.py` did not run -- they need a file at\n"
                  "`ProofRefinement/Korenblum/Candidates/V<N>.lean`.\n"
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
                         c=float(cur), wall_s=round(run.wall, 1),
                         output_tokens=run.tok_out, usd=round(run.usd, 3))
                print(f"[armB] NEW BEST: {cur} = {float(cur):.6f} "
                      f"@ {run.wall/3600:.2f}h / {run.tok_out} tok", flush=True)
                prev_best = cur
            label = "S"
            evidence = (f"evaluator accepted {cur} > {ANCHOR_PARENT_SCORE} "
                        f"at iteration {n}")
            if not a.continue_after_success:
                print(f"[armB] GOAL REACHED: {evidence}")
                break

    print(json.dumps(run.finish(label, evidence), indent=2))


if __name__ == "__main__":
    main()
