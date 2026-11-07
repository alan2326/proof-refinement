# Korenblum Proof Refinement Harness

This workspace clones the `ProofRefinement/Lemma54` harness structure, but the
optimization target is different: every candidate must prove a **final**
Korenblum lower bound.

This copy lives inside `ProofRefinement/Korenblum/` so a folder-scoped agent
can see the harness implementation without reading repo-root `.claude/` files.

## Contract

Each candidate file `Candidates/V<N>.lean` must export:

- `def c_value : ℝ := <rational>`
- `theorem korenblum_constant_search :
    ProofRefinement.Korenblum.ValidKorenblumBound c_value`

The contract
[`ValidKorenblumBound`](../Proof/CandidateContract.lean)
means:

- `0 < c < 1`, and
- for every Wang Section 2 paper instance at radius `c`,
  `diskExcess ≤ annulusExcess`.

The search space is the full space of Lean proofs of this final theorem. One
convenience bridge from Wang's scalar inequality `(15)` to this final theorem
lives in [`Proof/Reduction.lean`](../Proof/Reduction.lean).

## Seed

[`Candidates/V0.lean`](../Candidates/V0.lean) is the
paper-faithful seed:

- `c_value = 3554 / 10000`
- it uses `KorenblumPaper.PaperAxioms`
- it uses the current seed reduction through equation `(15)`
- it assumes a single seed axiom
  `hEq15_seed_3554 : Eq15ScalarBound K c_value`

This is only the initial seed. Future candidates may prove the final theorem by
other arguments.

The current score is just `c_value`, so **larger is better**.

## Evaluator

Use:

```bash
bash scripts/korenblum_lake_build.sh Candidates/V0.lean
bash scripts/korenblum_eval_candidate.sh Candidates/V0.lean
```

The evaluator checks:

1. `lake build` of the candidate module
2. exact theorem type
3. candidate imports against `lemma.toml`'s `import_policy`
4. all workspace `.lean` imports against `lemma.toml`'s `workspace_import_policy`
5. `#print axioms` closure against `lemma.toml`
6. registered oracle checks, if any are used
7. score extraction and log append

The log file is [`Refinement_Log/log.jsonl`](../Refinement_Log/log.jsonl).

## Workspace Layout

```text
ProofRefinement/Korenblum/
├── Candidates/
├── Proof/
├── Numerical_Library/
├── Proposals/
├── Refinement_Log/
├── Scratch/
├── Sprint_Contracts/
├── AGENT_BRIEF.md
├── Bulletin.md
├── Evaluator.py
├── Experience.md
├── README.md
└── lemma.toml
```

## Sprint Roles

- **Planner** reads `Bulletin.md`, `Experience.md`, recent log entries, and the
  templates, then writes one new sprint contract.
- **Generator** executes the contract, usually by creating a new
  `Candidates/V<N>.lean` and any explicitly named support edits.
- **Evaluator** runs the candidate checks literally and writes a verdict note.

All long-lived state lives in files, not conversation history.

## Driver Loop

Run one full Korenblum sprint with:

```text
/run-next-korenblum-sprint
```

Run the harness autonomously with the host loop runner:

```text
/loop 30m /run-next-korenblum-sprint
```

The folder-local harness wiring for that loop lives here:

- `.claude/skills/run-next-korenblum-sprint/SKILL.md`
- `.claude/agents/korenblum-refinement-planner.md`
- `.claude/agents/korenblum-refinement-generator.md`
- `.claude/agents/korenblum-refinement-evaluator.md`

These `.claude` files are part of the Korenblum harness itself.

Important distinction:

- the autonomous agent loop is provided by the host `/loop` command,
- this repository does not contain a standalone bash or cron scheduler that
  spawns the Korenblum agents by itself,
- `scripts/korenblum_checkpoint_loop.sh` is only for periodic checkpoint
  commits.

## Helper Scripts

- `scripts/korenblum_harness_preflight.sh` halts the loop if the workspace
  import policy has drifted or if the last 3 candidate evaluations all failed.
- `scripts/korenblum_harness_reset.sh` resets the harness to a V0-centered
  state and rewrites the volatile bulletin/notebook files.
- `scripts/korenblum_checkpoint_once.sh` creates one scoped checkpoint commit
  for this workspace.
- `scripts/korenblum_checkpoint_loop.sh` repeats that checkpoint action on a
  timer; it does not spawn planner/generator/evaluator agents.
- `scripts/korenblum_lake_build.sh` runs `lake build` from the repo root while
  taking a candidate path local to this folder.
- `scripts/korenblum_eval_candidate.sh` runs `Evaluator.py` from this folder
  while setting the repo-root environment the evaluator expects.

## Current Trust Boundary

- Trusted external Lean imports are pinned in
  [`lemma.toml`](../lemma.toml) under
  `workspace_import_policy`.
- Seed axioms are listed in
  [`lemma.toml`](../lemma.toml).
- No oracle is registered yet.
- The legacy numerical code from `KorenblumPaper/oracle/` has been
  copied into `Numerical_Library/`, but it is not active until a future sprint
  adds a Lean-facing oracle statement and a matching `[[oracles]]` entry.
- Oracle-shaped additions do not need a human proposal when they are fully
  specified by the sprint contract. Add the new `Numerical_Library` function,
  the matching `lemma.toml` `[[oracles]]` entry, and the Lean-facing axiom/use
  site inline in the sprint.
- Use `Proposals/` only for non-oracle trust-base
  expansions such as new free-floating analytic axioms, major statement
  reformulations, or large import/library moves requiring human review.
