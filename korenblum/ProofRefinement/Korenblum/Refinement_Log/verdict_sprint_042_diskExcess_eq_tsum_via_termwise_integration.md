# Verdict: sprint_042_diskExcess_eq_tsum_via_termwise_integration

**Contract**: korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_042_diskExcess_eq_tsum_via_termwise_integration.md

**Candidate**: korenblum/ProofRefinement/Korenblum/Candidates/V42.lean

**Outcome**: PASS

**Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V42` | PASS (8049 jobs, warnings only) |
| 2. `grep -n 'sorry' Candidates/V42.lean` | PASS (no matches) |
| 3. Evaluator run | PASS — score 1777/5000 |
| 4. Parent score comparison (V41 = 1777/5000, V42 = 1777/5000, required ≥) | PASS |

## Evaluator summary

- compile: PASS (8.89s)
- type-check: PASS (7.00s)
- axiom scan: PASS (7.75s)
- axiom audit: PASS — seed axioms only: {propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V42.hEq15_seed_3554}
- oracle audit: PASS
- workspace imports: PASS
- import audit: PASS
- score: 1777/5000

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V42

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V42.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V42.lean
```
