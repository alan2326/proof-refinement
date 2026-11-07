---
name: run-next-sprint
description: Drive one full sprint of the proof refinement harness: spawn the Planner to write a Sprint Contract, spawn the Generator to execute it, spawn the Evaluator to grade it, and report a one-paragraph status. Use when the user runs /run-next-sprint or when /loop fires this command.
---

You are the **driver loop** for the proof refinement harness. Your job
is to run one full sprint end-to-end.

You have NOT been delegated the task of doing proof work yourself.
You orchestrate three sub-agents in sequence. Your context stays
short because each sub-agent gets its own.

## Sequence

### 1. Pre-flight check

Run the pre-flight script. It checks the only loop-internal halt
condition (the harness is candidates-only, so there's no production
regression to worry about within the loop):

```bash
bash scripts/harness_preflight.sh
```

The script fails if the last 3 verdicts on the *same goal* (matched
by sprint title) are all FAIL — the Planner is stuck and needs human
review.

If the script exits non-zero, do not start the next sprint. Report
the halt reason to the user and stop.

### 2. Spawn the Planner

Use the `Agent` tool with `subagent_type: refinement-planner`.

Prompt: a single line with the fully-qualified path to
`ProofRefinement/Lemma54/Bulletin.md` for context. The Planner will
read what it needs.

```
Plan the next sprint. Read Bulletin.md, the last 10 log entries,
the most recent Sprint Contract, STATUS_AND_PLAN.md (priority
sections only), and AGENT_BRIEF.md. Write a single new Sprint
Contract under ProofRefinement/Lemma54/Sprint_Contracts/. Do not
edit Lean.
```

The Planner returns a one-paragraph status naming the new contract
path. Capture that path; you'll need it for the next two steps.

### 3. Spawn the Generator

Use the `Agent` tool with `subagent_type: refinement-generator`.

Prompt:

```
Execute the Sprint Contract at <path>. Read it, make the changes
it specifies, run the per-module lake build the contract names,
and terminate with a STATUS= line. Do not run the full audit or
runner. Do not add any new axioms.
```

The Generator returns with one of:

- `STATUS=READY_FOR_EVALUATION` → proceed to step 4.
- `STATUS=BLOCKED` → write the blocker reason to `Bulletin.md`,
  append a FAIL line to `log.jsonl` with `outcome: BLOCKED`, stop.
- `STATUS=BLOCKED_NEEDS_HUMAN` → same, with `outcome:
  BLOCKED_NEEDS_HUMAN`. Print a clear "human action needed:" line
  in the final summary.

### 4. Spawn the Evaluator

Use the `Agent` tool with `subagent_type: refinement-evaluator`.

Prompt:

```
Evaluate the sprint at <contract-path>. Run the cheap gates always
(G1–G6); run G7–G8 only if the contract's Tier is `checkpoint` or
any production file under ProofGraph/ was changed. Use
scripts/runner_cache_check.sh to skip G8 when inputs are
unchanged. Write the verdict to
ProofRefinement/Lemma54/Refinement_Log/verdict_<NNN>.md, append
one line to log.jsonl, and terminate with a STATUS= line.
```

The Evaluator returns:

- `STATUS=VERDICT_PASS` → great, sprint complete.
- `STATUS=VERDICT_FAIL` → record the failing gate; do not retry
  automatically.

### 5. Update the Bulletin

Append one line to `ProofRefinement/Lemma54/Bulletin.md`:

```
sprint_<NNN> <PASS|FAIL>: <one-line title> [direction: <axis>] [gate: <id-if-fail>]
```

If `Bulletin.md` exceeds 100 lines, replace its body with the last
50 lines (header preserved). The bulletin is volatile signaling, not
historical record — the log is the historical record.

### 5a. Scratch/ is persistent

**Do NOT wipe Scratch/.** It accumulates across sprints as the
harness's research notebook. The Planner and Generator both read
prior `Scratch/sprint_<K>_*.py` files for context on past
calculations. Wiping it loses institutional memory.

If Scratch/ ever gets unwieldy (hundreds of files), trim manually
out-of-loop, not via the skill.

### 6. Return a one-paragraph status

To whoever called you (a human or the `/loop` runner), print a
single paragraph:

```
Sprint <NNN> <PASS|FAIL>: <title>.
Generator status: <STATUS>.
Evaluator outcome: <VERDICT>.
Score: <Cr_val or relevant metric>, axioms: <count>, sorries: <count>.
Verdict: <path>.
<If FAIL: Failing gate: <id>; reason: <one line>.>
```

Then stop. Do not start another sprint; the `/loop` runner does that.

## Important constraints on you (the driver)

- **You do not do proof work.** Spawn sub-agents.
- **You do not pre-read anything.** The sub-agents read their own
  inputs.
- **You don't accumulate context.** Each sub-agent invocation is
  self-contained; you only need the contract path between Planner
  and Generator/Evaluator.
- **You don't second-guess the Evaluator.** If it says FAIL, the
  sprint failed. Don't ask the Generator to retry.

## Failure modes you should handle gracefully

| Symptom | Action |
|---|---|
| Pre-flight halt | Stop; surface the halt reason. Do not spawn agents. |
| Planner returns no contract path | Report `STATUS=PLANNER_DEGRADED`; stop. |
| Generator returns no STATUS line | Treat as `BLOCKED`; record and stop. |
| Evaluator returns no verdict file | Treat as `VERDICT_FAIL`/`G_HARNESS_BUG`; surface to user. |
| Sub-agent crashes mid-run | Same as above; do not retry within this skill invocation. |

The `/loop` runner can re-fire later; don't try to recover here.
