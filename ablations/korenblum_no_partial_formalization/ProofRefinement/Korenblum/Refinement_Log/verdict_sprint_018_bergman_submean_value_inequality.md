# Verdict: sprint_018_bergman_submean_value_inequality

**Date**: 2026-05-07
**Evaluator**: korenblum-refinement-evaluator (claude-sonnet-4-6)

## Contract path

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_018_bergman_submean_value_inequality.md`

## Candidate path

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V18.lean`

## New module path

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/SubMeanValue.lean`

## Outcome

**PASS**

All four evaluator gates cleared.

## Gate results

| Gate | Result | Notes |
|------|--------|-------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V18` | PASS | Build completed successfully (8046 jobs); warnings only (unused variables, ring_nf suggestion) |
| 2. `grep -n 'sorry' Candidates/V18.lean Proof/SubMeanValue.lean` | PASS | No matches |
| 3. Full evaluator run | PASS | `status: PASS`, `score (maximize): 1777/5000` |
| 4. Parent score comparison | N/A — no strict improvement required | Sprint contract explicitly states score is unchanged from V17 (3554/10000 = 1777/5000); this is expected scaffolding-only sprint |

## Score

- V17 parent score: `1777/5000` (3554/10000)
- V18 score: `1777/5000` (3554/10000)
- Score direction: unchanged (scaffolding sprint; no improvement required by contract)

## Axiom audit

Axioms used: `propext`, `Classical.choice`, `Quot.sound`,
`ProofRefinement.Korenblum.Candidates.V18.hKorenblum_published_3554`.
No `sorryAx`. No new axioms beyond the permitted seed.

## Acceptance criteria check

1. `lake build ProofRefinement.Korenblum.Candidates.V18` succeeded with no `sorry` and no forbidden axioms. PASS.
2. Evaluator accepted V18 as a well-formed candidate with `status: PASS`. Score unchanged as expected. PASS.
3. `Proof/SubMeanValue.lean` contains `theorem normSq_zero_le_bergmanNormSq_div_pi` (no `sorry`, no `axiom`), proved via `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` and `Summable.le_tsum`. PASS.
4. Theorem (2) `normSq_pointwise_le_ball_integral` was deferred (Fallback A). The file ships theorem (1) only. Per contract, Fallback A is acceptable. PASS (under Fallback A).
5. `Proof.SubMeanValue` is imported by `Candidates/V18.lean` — it is in V18's transitive compile graph. PASS.
6. Theorem (1) shape is internally consistent: at `f := constant c`, gives `π·‖c‖² ≤ bergmanNormSq (const c) = π·‖c‖²` (equality); at `f := z`, gives `0 ≤ π/2` (strict). PASS.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V18

# Gate 2
grep -n 'sorry' \
  ProofRefinement/Korenblum/Candidates/V18.lean \
  ProofRefinement/Korenblum/Proof/SubMeanValue.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V18.lean
```
