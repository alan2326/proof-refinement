# Verdict: sprint_004_circle_mean_outer_comparison

**Contract**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_004_circle_mean_outer_comparison.md`
**Candidate**: `ProofRefinement/Korenblum/Candidates/V4.lean`
**Parent candidate**: `Candidates/V3.lean`
**Evaluated**: 2026-05-07

## Outcome

PASS

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1. `lake build` | `lake build ProofRefinement.Korenblum.Candidates.V4` | PASS (8031 jobs, warnings only) |
| 2. `grep -n 'sorry'` | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V4.lean` | PASS (no output) |
| 3. Evaluator | `env UV_CACHE_DIR=... uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V4.lean` | PASS |
| 4. Score comparison | Parent V3 score = 1777/5000; V4 score = 1777/5000 (unchanged; no strict improvement required per contract) | N/A — not enforced |

## Evaluator summary

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.07s)
- type-check: PASS (6.44s)
- axiom scan: PASS (8.10s)
- axiom audit: PASS — seed axioms only: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V4.hKorenblum_published_3554`
- oracle audit: PASS
- score (maximize): 1777/5000 (= 3554/10000, unchanged from V3 as expected)

## Acceptance-criteria check

1. `lake build ProofRefinement.Korenblum.Candidates.V4` succeeds with no `sorry`, no extra axioms: PASS
2. Evaluator accepts V4 as a well-formed candidate; score unchanged from V3 (expected, as stated in contract): PASS
3. `Proof/CircleMeanCompare.lean` contains `circleMeanSq_le_of_outerAnnulus_dom` (conclusion `circleMeanSq f r ≤ circleMeanSq g r`) and `outerAnnulus_norm_sq_mono_via_radial` (calls both `outerAnnulus_norm_sq_polar` and `circleMeanSq_le_of_outerAnnulus_dom`); both are `theorem`, no `sorry`: PASS
4. V4 imports `Proof.CircleMeanCompare`, forcing it to compile as part of V4's build graph: PASS

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V4

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V4.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V4.lean
```
