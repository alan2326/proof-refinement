# Grothendieck constant

Lean 4 project for the upper bound on the real Grothendieck constant. It has
four parts.

| Directory | Contents |
| --- | --- |
| `LeanProof/` | formalization of Braverman, Makarychev, Makarychev, Naor (2011): the kernel, the partition, Lemmas 4.1 to 5.4, Theorem 4.4, Theorem 5.1, and the main theorem |
| `ProofRefinement/Lemma54/` | the refinement workspace for the remainder constant C_r of Lemma 5.4 (see its own README and `AGENT_BRIEF.md`) |
| `ProofGraph/` | the proof graph: one TOML per node, an axiom audit, and a runner that computes every numerical constant the Lean side declares (`ProofGraph/README.md`) |
| `grothendieck/proof/certified/` | the certified-arb Python pipeline the oracles call |
| `paper_artifacts/` | the plots and proof-graph figures in the paper, with the scripts that produce them |
| `docs/` | harness design, plan, and the ablation write-up |
| `blueprint/` | source of the Lean blueprint (build with `blueprint/build.sh`) |

The final accepted candidate is `ProofRefinement/Lemma54/Candidates/V28.lean`,
which declares `Cr_val := 2/7`. Its verdict is
`ProofRefinement/Lemma54/Refinement_Log/verdict_034.md`.

## Build and check

```bash
lake exe cache get
lake build LeanProof ProofRefinement ProofGraph
lake env lean ProofRefinement/Lemma54/Candidates/V28.lean
uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V28.lean --no-log
```

`ProofRefinement/Lemma54/Scratch/` holds only the modules the truncation-free
oracle imports; the rest of the original scratch directory was exploratory and
is not included.

## Running the loop

The planner, generator, and evaluator are defined in `.claude/agents/`, and
`.claude/skills/run-next-sprint/SKILL.md` drives one sprint. With Claude Code
open in this directory:

```
/run-next-sprint
```

`scripts/harness_preflight.sh` is the halt check the skill runs first;
`scripts/harness_reset.sh` returns the workspace to its V0 state.
