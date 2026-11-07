# Verdict: sprint_041_annulusSlice_eq_via_series_partition

**Date**: 2026-05-02
**Evaluator**: korenblum-refinement-evaluator (claude-sonnet-4-6)

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_041_annulusSlice_eq_via_series_partition.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V41.lean`

## Outcome

**VERDICT_PASS**

## Gate results

| Gate | Result | Detail |
|------|--------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V41` | PASS | Build completed successfully (8049 jobs); warnings only, no errors |
| 2. `grep -n 'sorry' Candidates/V41.lean` | PASS | No matches |
| 3. Evaluator run | PASS | score = 1777/5000; axiom audit PASS; all sub-checks PASS |
| 4. Score vs parent V40 (>= 1777/5000) | PASS | 1777/5000 >= 1777/5000 |

## Score

`1777/5000` (ties V40 at seed c = 0.3554, as specified by the contract)

## Axioms used

- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V41.hEq15_seed_3554` (seed)

No new free-floating axioms; no oracle entries.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V41

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V41.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V41.lean
```
