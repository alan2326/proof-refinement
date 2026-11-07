# Verdict: sprint_017_cauchy_l2_coefficient_estimate

**Date**: 2026-05-07

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_017_cauchy_l2_coefficient_estimate.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V17.lean`

New derived module: `ProofRefinement/Korenblum/Proof/CauchyL2Estimate.lean`

## Outcome

PASS

## Gate results

### Gate 1: `lake build`

PASS — `Build completed successfully (8045 jobs)`. Only non-blocking linter
warnings (unused variables) in pre-existing modules and in
`Proof/CauchyL2Estimate.lean` line 344.

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V17
```

### Gate 2: `grep -n 'sorry'`

PASS — no `sorry` in either `Candidates/V17.lean` or
`Proof/CauchyL2Estimate.lean`.

Reproduction:
```
grep -n 'sorry' \
  ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V17.lean \
  ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/CauchyL2Estimate.lean
```

### Gate 3: Evaluator run

PASS — all sub-checks passed:

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.07s)
- type-check: PASS (5.78s)
- axiom scan: PASS (6.76s)
- axiom audit: PASS (only `propext`, `Classical.choice`, `Quot.sound`,
  `hKorenblum_published_3554`)
- oracle audit: PASS
- score: `1777/5000`
- status: PASS

Reproduction:
```
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V17.lean
```

### Gate 4: Score comparison against parent V16

The sprint contract explicitly states the score is unchanged from V16 and that
this is expected (scaffolding-only sprint). V16 score was `1777/5000`; V17
score is `1777/5000`. No strict improvement was required or claimed.

PASS.

## Acceptance criteria check

1. `lake build` succeeds with no `sorry`, no unauthorized axioms. PASS.
2. Evaluator accepts V17 as well-formed. Score `1777/5000 = 0.3554` unchanged
   from V16. Truthfully reported. PASS.
3. `Proof/CauchyL2Estimate.lean` contains all three required theorems
   (`cauchyPowerSeries_normSq_pow_le_circleMeanSq`,
   `outer_circleMeanSq_dom_of_pointwise_dom`,
   `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq`) as `theorem`
   declarations with no `sorry`, genuinely calling sprint 010's
   `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` for
   theorem (1) and `setIntegral_mono_on` for theorem (2). PASS.
4. `Proof.CauchyL2Estimate` is imported by `V17.lean` (line 20). PASS.
5. Theorem shapes are consistent with the sprint 010/011/015/016 stack. PASS.

## STATUS

VERDICT_PASS
