# Verdict: sprint_001_polar_bergman_decomposition

**Evaluated**: 2026-05-07  
**Evaluator**: korenblum-refinement-evaluator (noPF arm)

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_001_polar_bergman_decomposition.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V1.lean`  
(new module also: `ProofRefinement/Korenblum/Proof/PolarBergman.lean`)

## Outcome

**PASS**

## Gate results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V1`

PASS. Build completed successfully (8028 jobs).

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V1
```

### Gate 2 — `grep -n 'sorry' <candidate>`

PASS. No `sorry` found in either `Candidates/V1.lean` or `Proof/PolarBergman.lean`.

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V1.lean
grep -n 'sorry' ProofRefinement/Korenblum/Proof/PolarBergman.lean
```

### Gate 3 — Evaluator

PASS. Full evaluator output:

```
candidate:     ProofRefinement/Korenblum/Candidates/V1.lean
namespace:     ProofRefinement.Korenblum.Candidates.V1
parent:        V0
workspace imports: PASS
import audit:  PASS
compile:       PASS (8.21s)
type-check:    PASS (6.54s)
axiom scan:    PASS (8.88s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V1.hKorenblum_published_3554
oracle audit:  PASS
score (maximize): 1777/5000
status: PASS
```

Reproduction:
```
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V1.lean
```

### Gate 4 — Parent score comparison

NOT APPLICABLE. The contract explicitly specifies this is scaffolding-only and
the score is unchanged from V0 (`c_value = 3554/10000 = 1777/5000` in both V0
and V1). No strict improvement is required.

## Acceptance criteria check

1. `lake build` PASS — no `sorry`, no extra axioms beyond
   `hKorenblum_published_3554` and the standard Lean axioms.
2. Evaluator PASS — score `1777/5000` accepted as well-formed candidate.
3. `Proof/PolarBergman.lean` contains `theorem bergmanNormSq_polar` (not
   `axiom`, no `sorry`) expressing `bergmanNormSq f` as a repeated polar
   integral over `r ∈ Ioo 0 1`, `θ ∈ Ioo (-π) π` with the `r` Jacobian
   factor — PASS.
4. `Proof.PolarBergman` is imported by `Candidates/V1.lean` (line 3), forcing
   the module to compile as part of V1's build graph — PASS.

## Notes

- V1 score equals V0 score (`1777/5000 = 0.3554`); this is expected and
  declared in the contract.
- `PolarBergman.lean` derives `bergmanNormSq_polar` in five steps via
  `Complex.integral_comp_polarCoord_symm` (polar substitution) and
  `setIntegral_prod` (Fubini), entirely within Mathlib. No new axioms
  introduced.
