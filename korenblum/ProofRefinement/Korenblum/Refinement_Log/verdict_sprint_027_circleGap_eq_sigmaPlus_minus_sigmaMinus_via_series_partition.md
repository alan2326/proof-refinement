# Verdict: sprint_027_circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition

**Date**: 2026-05-02

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_027_circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V27.lean`

## Outcome

VERDICT_PASS

## Gate Results

| Gate | Result | Detail |
|------|--------|--------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)` — warnings only, no errors |
| 2. `grep -n 'sorry' Candidates/V27.lean` | PASS | No matches (zero sorry occurrences) |
| 3. Evaluator | PASS | `score (maximize): 1777/5000`, `status: PASS` |
| 4. Score >= parent (V26 = 1777/5000) | PASS | 1777/5000 >= 1777/5000 satisfied |

## Score

1777/5000 (c_value = 3554/10000 = 0.3554)

Parent V26 score: 1777/5000. No regression.

## Axiom audit

- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V27.hEq15_seed_3554` (seed, listed in `lemma.toml:[seed_axioms]`)

No new axioms beyond the permitted seed axiom.

## Structural checks satisfied

- `korenblum_constant_search : ValidKorenblumBound c_value` present and proved via `valid_of_eq15`.
- `v27_circleGap_eq_via_series_partition_compiles` present.
- `v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed` present.
- New generic theorem `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` is exercised from `Proof/Reduction.lean` (via the candidate's two witness lemmas, both of which delegate to it directly).

## Reproduction

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V27

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V27.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V27.lean
```
