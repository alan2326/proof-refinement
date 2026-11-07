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
lake build ProofRefinement.Lemma54.Candidates.V28
uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V28.lean --no-log
```

## Oracle certificates

The oracles behind V28 read two chunk-certificate files that the evaluator
recomputes against: `Cache/Backups/2026-05-03_production/v26_chunk_certifier_npe16.json`
and `Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json`.
Those files were not retained after the run. The `MANIFEST.sha256` next to each
README records their hashes. Without them the evaluator passes the parse,
compile, and axiom-audit stages and fails the oracle stage, so check V28 with
`--skip-oracle` or regenerate the certificates first. The scripts are in
`ProofRefinement/Lemma54/Scratch/`:

```bash
cd ProofRefinement/Lemma54/Scratch
# production chunks: 64 chunks, 16 Gauss-Legendre nodes per panel; about 3 hours on 96 workers
uv run --with python-flint python -u parallel_chunk_certifier.py --n_per_edge 16 --n_workers 96
# then three corner-subdivision rounds (about 45 minutes in total); the chunk ids
# split in rounds 2 and 3 are listed in Cache/Backups/2026-05-03_subdivision/README.md
uv run --with python-flint python -u corner_subdivision_certifier.py \
    --in_chunks ../Cache/Backups/2026-05-03_production/v26_chunk_certifier_npe16.json \
    --out_chunks ../Cache/Backups/2026-05-03_subdivision/round1_v26_corner_split.json --n_workers 96
```

The run parameters of the original computation are in
`Cache/Backups/2026-05-03_production/README.md`.

`ProofRefinement/Lemma54/Scratch/` holds the modules the truncation-free oracle
imports and the certificate generators above. The rest of the original scratch
directory was exploratory and is not included.

## Running the loop

The planner, generator, and evaluator are defined in `.claude/agents/`, and
`.claude/skills/run-next-sprint/SKILL.md` drives one sprint. With Claude Code
open in this directory:

```
/run-next-sprint
```

`scripts/harness_preflight.sh` is the halt check the skill runs first, and
`scripts/harness_reset.sh` returns the workspace to its V0 state.
