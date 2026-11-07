# Verdict: sprint_005_radial_split_and_conditional_reduction

**Contract**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_005_radial_split_and_conditional_reduction.md`
**Candidate**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V5.lean`
**Parent candidate**: `Candidates/V4.lean`
**Evaluated**: 2026-05-07

## Outcome

PASS

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V5`

PASS — Build completed successfully (8032 jobs). Only pre-existing lint warnings
in `RadialBergman.lean` (unused variables `hc1`, `hc`); no errors.

Reproduction:
```bash
cd ablations/korenblum_no_partial_formalization && lake build ProofRefinement.Korenblum.Candidates.V5
```

### Gate 2: `grep -n 'sorry' Candidates/V5.lean`

PASS — No `sorry` found in the candidate file.

Reproduction:
```bash
grep -n 'sorry' ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V5.lean
```

### Gate 3: Full evaluator run

PASS — All sub-checks pass.

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.75s)
- type-check: PASS (6.21s)
- axiom scan: PASS (7.56s)
- axiom audit: PASS (axioms: propext, Classical.choice, Quot.sound, hKorenblum_published_3554)
- oracle audit: PASS
- score (maximize): 1777/5000

Reproduction:
```bash
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Evaluator.py \
  --file ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V5.lean
```

### Gate 4: Score comparison against parent

Not enforced. The sprint contract explicitly states the score is unchanged from
V4 (1777/5000 = 3554/10000) and calls this expected and not a failure. No strict
improvement was required.

## Summary

V5 is a scaffolding sprint. Both required lemmas are present in
`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/RadialSplit.lean`
with no `sorry`:

- `radialIntegral_split`: proves the radial integral over `Ioo 0 1` equals
  the sum of integrals over `Ioc 0 c` and `Ioo c 1` via `setIntegral_union`.
- `validKorenblum_of_innerCircleMean_dom`: proves `bergmanNormSq f <= bergmanNormSq g`
  using `radialIntegral_split`, `setIntegral_mono_on` for the inner half, and
  `circleMeanSq_le_of_outerAnnulus_dom` for the outer half.

V5.lean imports `Proof.RadialSplit`, placing it in V5's transitive compile graph.
The only seed axiom is `hKorenblum_published_3554`, unchanged from V4.
