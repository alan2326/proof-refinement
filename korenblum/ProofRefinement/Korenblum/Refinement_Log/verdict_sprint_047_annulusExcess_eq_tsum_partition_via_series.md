# Verdict: sprint_047_annulusExcess_eq_tsum_partition_via_series

**Date**: 2026-05-02
**Evaluator**: claude-sonnet-4-6

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_047_annulusExcess_eq_tsum_partition_via_series.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V47.lean`

## Outcome

VERDICT_PASS

## Gate Results

### Gate 1: lake build

PASS — `lake build ProofRefinement.Korenblum.Candidates.V47` completed successfully (8049 jobs, warnings only, no errors).

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V47
```

### Gate 2: sorry check

PASS — `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V47.lean` produced no output.

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V47.lean
```

### Gate 3: Evaluator

PASS — evaluator reports `score = 1777/5000`, `status: PASS`.

Full evaluator output summary:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.61s)
- type-check: PASS (11.04s)
- axiom scan: PASS (13.96s)
- axiom audit: PASS
  - seed propext
  - seed Classical.choice
  - seed Quot.sound
  - seed ProofRefinement.Korenblum.Candidates.V47.hEq15_seed_3554
- oracle audit: PASS
- score (maximize): 1777/5000
- status: PASS

Reproduction:
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V47.lean
```

### Gate 4: Parent score comparison

The contract specifies the score ties V46 at `1777/5000` (structural sprint, no numerical improvement). No strict score improvement gate applies. Score preserved: PASS.

## Score

`1777/5000`

## Axioms used

- propext (seed)
- Classical.choice (seed)
- Quot.sound (seed)
- ProofRefinement.Korenblum.Candidates.V47.hEq15_seed_3554 (seed)

No new axioms, no oracle entries.
