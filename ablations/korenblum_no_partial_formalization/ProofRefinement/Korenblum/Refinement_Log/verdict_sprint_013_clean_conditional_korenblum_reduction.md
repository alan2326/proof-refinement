# Verdict: sprint_013_clean_conditional_korenblum_reduction

**Date**: 2026-05-07
**Evaluator**: korenblum-refinement-evaluator

## Contract

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_013_clean_conditional_korenblum_reduction.md`

## Candidate

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V13.lean`

## New proof modules

- `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/RadialIntegrability.lean`
- `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/CleanConditional.lean`

## Outcome

PASS

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1 | `lake build ProofRefinement.Korenblum.Candidates.V13` | PASS (8041 jobs, warnings only) |
| 2 | `grep -n 'sorry' Candidates/V13.lean` | PASS (no matches) |
| 3 | `uv run ProofRefinement/Korenblum/Evaluator.py --file Candidates/V13.lean` | PASS (status: PASS, score: 1777/5000) |
| 4 | Parent score comparison | N/A — contract explicitly states score unchanged from V12 is expected |

## Evaluator details (Gate 3)

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.21s)
- type-check: PASS (6.55s)
- axiom scan: PASS (7.58s)
- axiom audit: PASS
  - seed axioms used: `propext`, `Classical.choice`, `Quot.sound`
  - candidate axiom: `ProofRefinement.Korenblum.Candidates.V13.hKorenblum_published_3554`
- oracle audit: PASS
- score (maximize): 1777/5000 = 3554/10000 (unchanged from V12, as expected)

## Score comparison

- Parent (V12): 1777/5000
- V13: 1777/5000
- Change: none (scaffolding-only sprint; no strict improvement required per contract)

## One-line reproduction commands

```bash
# Gate 1
cd ablations/korenblum_no_partial_formalization && lake build ProofRefinement.Korenblum.Candidates.V13

# Gate 2
grep -n 'sorry' ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V13.lean

# Gate 3
cd ablations/korenblum_no_partial_formalization && env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V13.lean
```
