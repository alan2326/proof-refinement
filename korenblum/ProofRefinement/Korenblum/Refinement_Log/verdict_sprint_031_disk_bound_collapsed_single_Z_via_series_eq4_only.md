# Verdict: sprint_031_disk_bound_collapsed_single_Z_via_series_eq4_only

**Evaluated**: 2026-05-02

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_031_disk_bound_collapsed_single_Z_via_series_eq4_only.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V31.lean`

## Outcome

VERDICT_PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V31` | PASS (8049 jobs, no errors) |
| 2. `grep -n 'sorry' Candidates/V31.lean` | PASS (no matches) |
| 3. Evaluator run | PASS (score = 1777/5000) |
| 4. Score vs parent V30 (requires >= 1777/5000) | PASS (1777/5000 = 1777/5000) |

## Evaluator summary

- compile: PASS (8.65s)
- type-check: PASS (6.89s)
- axiom scan: PASS (7.90s)
- axiom audit: PASS — exactly {propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V31.hEq15_seed_3554}
- oracle audit: PASS
- score: 1777/5000
- status: PASS

## Score

1777/5000

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V31

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V31.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V31.lean
```
