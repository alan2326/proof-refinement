# Verdict: sprint_006_annulus_excess_lower_bound_via_outer_pointwise

**Date**: 2026-05-02
**Evaluator**: claude-sonnet-4-6

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_006_annulus_excess_lower_bound_via_outer_pointwise.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V6.lean`

## Outcome

VERDICT_PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V6` | PASS |
| 2. `grep -n 'sorry' Candidates/V6.lean` | PASS (no matches) |
| 3. Evaluator run | PASS — score `1777/5000`, axiom audit clean |
| 4. Parent score comparison (V5 = `1777/5000`, V6 = `1777/5000`) | PASS (`1777/5000 ≥ 1777/5000`) |

## Evaluator summary

- score: `1777/5000`
- axioms_used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V6.hEq15_seed_3554}`
- workspace imports: PASS
- compile: PASS (8.63s)
- type-check: PASS (6.42s)
- axiom scan: PASS (7.56s)
- oracle audit: PASS

## Reproduction

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V6

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V6.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V6.lean
```
