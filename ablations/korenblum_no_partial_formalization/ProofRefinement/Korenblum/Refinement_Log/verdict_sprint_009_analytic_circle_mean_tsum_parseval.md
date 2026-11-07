# Verdict: sprint_009_analytic_circle_mean_tsum_parseval

**Date**: 2026-05-07
**Evaluator model**: claude-sonnet-4-6

## Contract

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_009_analytic_circle_mean_tsum_parseval.md`

## Candidate

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V9.lean`

New support file: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/AnalyticParseval.lean`

## Outcome

**VERDICT_PASS**

## Gate results

| Gate | Result | Notes |
|------|--------|-------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V9` | PASS | 8036 jobs, warnings only (unused variables, ring_nf suggestion); no errors |
| 2. `grep -n 'sorry' Candidates/V9.lean` | PASS | No output — zero `sorry` |
| 2. `grep -n 'sorry' Proof/AnalyticParseval.lean` | PASS | No output — zero `sorry` |
| 3. Evaluator run | PASS | score 1777/5000 (= 3554/10000), all sub-checks PASS |
| 4. Strict score improvement check | N/A | Contract explicitly declares score unchanged from V8 (scaffolding-only sprint); no inequality to enforce |

## Evaluator sub-check summary (Gate 3)

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.28 s)
- type-check: PASS (6.43 s)
- axiom scan: PASS (7.90 s)
- axiom audit: PASS — seed axioms only: `propext`, `Classical.choice`, `Quot.sound`, `hKorenblum_published_3554`
- oracle audit: PASS
- score: 1777/5000 (unchanged from V8, as expected)
- status: PASS

## Acceptance criteria check (from contract)

1. `lake build` succeeds with no `sorry`, no extra axioms — PASS.
2. Evaluator accepts V9, score 3554/10000 unchanged from V8 — PASS.
3. `Proof/AnalyticParseval.lean` contains:
   - `circleMeanSq_hasFPowerSeriesOnBall` (theorem, no sorry, uses `circleMeanSq_polynomial`) — PASS.
   - `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` (theorem, no sorry) — PASS.
4. `Proof.AnalyticParseval` imported by V9 and compiled as part of V9's build graph — PASS.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V9

# Gate 2
grep -n 'sorry' ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V9.lean
grep -n 'sorry' ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/AnalyticParseval.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
    --file ProofRefinement/Korenblum/Candidates/V9.lean
```
