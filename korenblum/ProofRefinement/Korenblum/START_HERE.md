# Start Here

You are working only inside `ProofRefinement/Korenblum/`.

## Hard local rule

- Do not read, search, or inspect files outside this directory unless the human
  explicitly tells you to.
- Do not inspect prior Korenblum proof-search folders or old candidates
  elsewhere in the repo.
- Treat `lemma.toml` import policies as a hard backstop.
- The folder-local harness wiring is part of this workspace:
  `.claude/skills/run-next-korenblum-sprint/SKILL.md`,
  `.claude/agents/korenblum-refinement-*.md`,
  `.claude/settings.json`,
  `docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md`,
  and `scripts/korenblum_*.sh`.

## First reads

1. `AGENT_BRIEF.md`
2. `README.md`
3. `Bulletin.md`
4. `Proof/CandidateContract.lean`
5. `Candidates/V0.lean`
6. `Proof/Reduction.lean`

## First checks

```bash
bash scripts/korenblum_harness_preflight.sh
bash scripts/korenblum_lake_build.sh Candidates/V0.lean
bash scripts/korenblum_eval_candidate.sh Candidates/V0.lean --no-log
```

## Harness loop

Run one full harness sprint with:

```text
/run-next-korenblum-sprint
```

Run autonomously with:

```text
/loop 30m /run-next-korenblum-sprint
```

The separate script `scripts/korenblum_checkpoint_loop.sh` only creates
periodic checkpoint commits. It does not spawn planner/generator/evaluator
agents.

For candidate checks inside a folder-scoped session, use the local wrappers:

```bash
bash scripts/korenblum_lake_build.sh Candidates/V0.lean
bash scripts/korenblum_eval_candidate.sh Candidates/V0.lean --no-log
```

## Goal

Find or execute the next bounded step toward proving a larger valid
Korenblum lower bound:

`theorem korenblum_constant_search : ValidKorenblumBound c_value`

The current seed uses equation `(15)`, but future work is not restricted to
that route.
