# Verdict: sprint_008_polynomial_parseval

**Date**: 2026-05-07

## Contract

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_008_polynomial_parseval.md`

## Candidate

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V8.lean`

New proof module: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/CirclePolynomialParseval.lean`

## Outcome

**PASS**

All four gates passed. No failing gate.

## Gate Results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V8`

PASS. Build completed successfully (8035 jobs). Only pre-existing warnings
(unused variables in `RadialBergman.lean`; a `ring_nf` suggestion in
`CircleInnerProduct.lean`). No errors.

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V8
```

### Gate 2 — `grep -n 'sorry' <candidate>`

PASS. No `sorry` found in either
`Candidates/V8.lean` or `Proof/CirclePolynomialParseval.lean`.

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V8.lean ProofRefinement/Korenblum/Proof/CirclePolynomialParseval.lean
```

### Gate 3 — Evaluator

PASS. Full evaluator output:

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.42s)
- type-check: PASS (6.49s)
- axiom scan: PASS (7.93s)
- axiom audit: PASS — axioms used: `propext`, `Classical.choice`, `Quot.sound`,
  `ProofRefinement.Korenblum.Candidates.V8.hKorenblum_published_3554` (the
  single allowed seed axiom). No `sorryAx` or unauthorized axioms.
- oracle audit: PASS
- score (maximize): `1777/5000`
- status: PASS

Reproduction:
```
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V8.lean
```

### Gate 4 — Score comparison against parent

Not applicable as a strict-improvement gate. The sprint contract explicitly
declares this sprint scaffolding-only with `c_value = 3554/10000` unchanged
from V7, and states: *"this is expected and not a failure of the sprint"*.

Parent V7 score: `1777/5000`. V8 score: `1777/5000`. Equal, as specified.

## Acceptance Criteria Checklist

1. `lake build ProofRefinement.Korenblum.Candidates.V8` succeeds with no `sorry`,
   no axiom other than `hKorenblum_published_3554` plus standard Lean axioms.
   **SATISFIED.**

2. Evaluator accepts V8 as a well-formed candidate; score `c_value = 3554/10000`
   unchanged from V7. **SATISFIED.**

3. `Proof/CirclePolynomialParseval.lean` contains:
   - `circleMeanInner_add_left`, `circleMeanInner_add_right` (additivity). **PRESENT.**
   - `circleMeanInner_smul_left`, `circleMeanInner_smul_right` (scalar mul, conj-linear
     left / linear right). **PRESENT.**
   - `circleMeanInner_finset_sum_monomial_left`,
     `circleMeanInner_finset_sum_monomial_right` (Finset-sum consumers). **PRESENT.**
   - `circleMeanInner_polynomial_self` — diagonal polynomial Parseval at the
     `ℂ`-valued inner-product level. **PRESENT.**
   - `circleMeanSq_polynomial` — headline real-valued polynomial Parseval. **PRESENT.**
   None are `axiom`; none contain `sorry`. **SATISFIED.**

4. `Proof.CirclePolynomialParseval` is imported by `Candidates/V8.lean` and
   therefore compiled as part of V8's build graph. **SATISFIED.**
