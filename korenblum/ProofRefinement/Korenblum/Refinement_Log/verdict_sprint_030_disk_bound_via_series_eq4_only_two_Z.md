# Verdict: sprint_030_disk_bound_via_series_eq4_only_two_Z

**Date**: 2026-05-02
**Evaluator**: korenblum-refinement-evaluator (claude-sonnet-4-6)

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_030_disk_bound_via_series_eq4_only_two_Z.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V30.lean`

## Outcome

VERDICT_PASS

## Gate Results

### Gate 1: lake build
`lake build ProofRefinement.Korenblum.Candidates.V30`
PASS — Build completed successfully (8049 jobs). Only linter warnings, no errors.

### Gate 2: sorry check
`grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V30.lean`
PASS — No occurrences of `sorry` found.

### Gate 3: Evaluator
`env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V30.lean`
PASS

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.58s)
- type-check: PASS (6.60s)
- axiom scan: PASS (8.38s)
- axiom audit: PASS
  - seed: propext
  - seed: Classical.choice
  - seed: Quot.sound
  - seed: ProofRefinement.Korenblum.Candidates.V30.hEq15_seed_3554
- oracle audit: PASS
- score (maximize): 1777/5000
- status: PASS

### Gate 4: Parent score comparison
Parent: V29, score = 1777/5000. V30 score = 1777/5000.
PASS — Contract requires score >= V29 (structural sprint, no c_value increase expected). Tie satisfied.

## Score

1777/5000

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V30

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V30.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V30.lean
```

## Notes

The new generic theorem `diskExcess_upper_bound_via_series_eq4_only_two_Z` appears
at line 4432 of `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
in V30's two side lemmas. The axiom set is exactly the V0 seed plus standard Lean
axioms, with no new free-floating axioms.
