# Korenblum Proof Refinement Workspace — noPF arm

This workspace is the **no-partial-formalization** arm of the Korenblum
ablation experiment. The sibling arm with partial formalization lives at
`korenblum/`. The two share most of the harness mechanics;
the difference is the trust surface.

- each candidate exports a **final lower-bound theorem** for a chosen `c`,
- the score is the candidate's produced lower bound `c_value`,
- larger `c_value` is better.

## Contract

Every candidate must declare:

- `def c_value : ℝ := <rational>`
- `theorem korenblum_constant_search :
    ProofRefinement.Korenblum.ValidKorenblumBound c_value`

The contract itself lives in
[Proof/CandidateContract.lean](ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/CandidateContract.lean).

`ValidKorenblumBound c` is the **function-level Korenblum max principle**:
for every analytic, A²-integrable `f, g : ℂ → ℂ` with `‖f‖ ≤ ‖g‖` on the
outer annulus `c < ‖z‖ < 1`, the Bergman A² inequality
`∫_𝔻 ‖f‖² ≤ ∫_𝔻 ‖g‖²` holds.

There is no Wang Section 2 hypothesis bundle, no equation chain, no
coefficient-level intermediate. The candidate must prove the function-level
statement directly.

## Seed

[Candidates/V0.lean](ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V0.lean)
is the seed at `c = 3554 / 10000 = 0.3554`.

It uses one seed axiom `hKorenblum_published_3554`, asserting the full
Korenblum max principle at `c = 0.3554` (Wang 2025).

That is only the seed route. Future candidates may prove
`ValidKorenblumBound c_value` by any other argument.

## Evaluator

Run:

```bash
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V0.lean
```

The evaluator checks:

1. candidate compile,
2. exact theorem type,
3. direct imports against `lemma.toml`'s `import_policy`,
4. all workspace `.lean` imports against
   `lemma.toml`'s `workspace_import_policy`,
5. axiom surface,
6. registered oracles if any are used (none registered initially in
   this arm),
7. score extraction and log append.

## Layout

```text
ProofRefinement/Korenblum/
├── Candidates/        # V0.lean is the seed; new candidates V1, V2, ...
├── Proof/             # CandidateContract.lean only
├── Proposals/         # trust-base expansion proposals
├── Refinement_Log/    # log.jsonl + verdict_*.md
├── Scratch/           # working notes
├── Sprint_Contracts/  # one .md per sprint
├── AGENT_BRIEF.md
├── Bulletin.md
├── Evaluator.py
├── Experience.md
├── README.md
└── lemma.toml
```

There is no `KorenblumPaper/` directory in this arm and no
`Numerical_Library/` — both are deliberately absent.

## Long-running harness

For the full Korenblum harness, including planner / generator / evaluator
roles, see the folder-local copy at
[docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md](ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/docs/KORENBLUM_PROOF_REFINEMENT_HARNESS.md).

The folder-local harness wiring lives at the workspace root:

- `.claude/agents/korenblum-refinement-planner.md`
- `.claude/agents/korenblum-refinement-generator.md`
- `.claude/agents/korenblum-refinement-evaluator.md`
- `.claude/skills/run-next-korenblum-sprint/SKILL.md`
- `.claude/settings.local.json`

Run one end-to-end sprint with:

```text
/run-next-korenblum-sprint
```

Run autonomously with the host loop runner:

```text
/loop 30m /run-next-korenblum-sprint
```

Important distinction:

- the autonomous agent loop comes from the host `/loop` command invoking
  the local skill above,
- there is no folder-local shell scheduler here that spawns planner /
  generator / evaluator agents by itself,
- `scripts/korenblum_checkpoint_loop.sh` is only a periodic
  checkpoint-commit loop.

Helpful scripts:

- `scripts/korenblum_harness_preflight.sh`
- `scripts/korenblum_harness_reset.sh`
- `scripts/korenblum_checkpoint_once.sh`
- `scripts/korenblum_checkpoint_loop.sh`
- `scripts/korenblum_lake_build.sh`
- `scripts/korenblum_eval_candidate.sh`
