# Verdict: sprint_040_disk_bound_via_series_eq3_partition_sigmaPlus_only

**Date**: 2026-05-02

## Contract
`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_040_disk_bound_via_series_eq3_partition_sigmaPlus_only.md`

## Candidate
`korenblum/ProofRefinement/Korenblum/Candidates/V40.lean`

## Outcome
PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V40` | PASS (8049 jobs, warnings only) |
| 2. `grep -n 'sorry' Candidates/V40.lean` | PASS (no matches) |
| 3. Evaluator run | PASS — score `1777/5000`, axiom audit PASS |
| 4. Parent score comparison (V39 = 1777/5000, V40 >= 1777/5000) | PASS (tie: 1777/5000) |

## Evaluator summary
- `compile`: PASS (8.85s)
- `type-check`: PASS (6.01s)
- `axiom scan`: PASS (8.40s)
- `axiom audit`: PASS — axioms used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V40.hEq15_seed_3554}`
- `oracle audit`: PASS
- `score (maximize)`: `1777/5000`
- `status`: PASS

## Score
1777/5000

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V40

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V40.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V40.lean
```
