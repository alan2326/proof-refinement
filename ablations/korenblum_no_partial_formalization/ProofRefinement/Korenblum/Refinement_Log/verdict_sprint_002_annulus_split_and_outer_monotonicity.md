# Verdict: sprint_002_annulus_split_and_outer_monotonicity

**Contract path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_002_annulus_split_and_outer_monotonicity.md`

**Candidate path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V2.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1 — `lake build`

```
lake build ProofRefinement.Korenblum.Candidates.V2
```

Result: `Build completed successfully (8029 jobs).`

### Gate 2 — `grep -n 'sorry'`

```
grep -n 'sorry' Candidates/V2.lean Proof/AnnulusBergman.lean
```

Result: no matches (exit 1). No `sorry` in either file.

### Gate 3 — Evaluator

```
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V2.lean
```

Result:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.55 s)
- type-check: PASS (6.62 s)
- axiom scan: PASS (7.27 s)
- axiom audit: PASS (seed axioms only: `propext`, `Classical.choice`, `Quot.sound`, `hKorenblum_published_3554`)
- oracle audit: PASS
- score (maximize): `1777/5000` (= 3554/10000)
- evaluator status: PASS

### Gate 4 — Score comparison against parent V1

The sprint contract explicitly states this is scaffolding-only and the score is unchanged from V1. No strict improvement is required. Parent V1 score from log: `1777/5000`. V2 score: `1777/5000`. Gate 4 not applicable as a strict-improvement constraint.

---

## Acceptance-criteria checks

1. `lake build` succeeds with no `sorry` and no axioms beyond `hKorenblum_published_3554` plus standard Lean axioms. PASS.
2. Evaluator accepts V2. Score `3554/10000` is unchanged from V1 — expected and reported truthfully. PASS.
3. `Proof/AnnulusBergman.lean` contains `theorem bergmanNormSq_split` (splits `bergmanNormSq f` as inner-disk plus outer-annulus integral) and `theorem outerAnnulus_norm_sq_mono` (monotonicity from pointwise hypothesis). Both are `theorem`, not `axiom`, with no `sorry`. PASS.
4. V2 imports `ProofRefinement.Korenblum.Proof.AnnulusBergman`, forcing the module into the compile graph. PASS.

---

## One-line reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V2

# Gate 2
grep -n 'sorry' ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V2.lean ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/AnnulusBergman.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache uv run ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Evaluator.py --file ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V2.lean
```
