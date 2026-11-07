# Verdict: sprint_020_eq10_eq11_straddling_window_sufficient_condition

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_020_eq10_eq11_straddling_window_sufficient_condition.md`

**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V20.lean`

**Parent**: `Candidates/V19.lean` (score `1777/5000`)

**Outcome**: PASS

**Score**: `1777/5000`

**Failing gate**: none — all gates passed

## Gate results

1. **Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V20`**: PASS (8049 jobs, build completed successfully; warnings only, no errors)

2. **Gate 2 — `grep -n 'sorry' Candidates/V20.lean`**: PASS (no matches)

3. **Gate 3 — evaluator run**: PASS
   - workspace imports: PASS
   - import audit: PASS
   - compile: PASS (8.65s)
   - type-check: PASS (6.71s)
   - axiom scan: PASS (7.70s)
   - axiom audit: PASS — axioms exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V20.hEq15_seed_3554}`
   - oracle audit: PASS
   - score (maximize): `1777/5000`
   - status: PASS

4. **Gate 4 — score improvement check**: PASS — V20 score `1777/5000` >= V19 score `1777/5000` (non-strict `>=` satisfied; contract says "scores >= V19")

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V20

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V20.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V20.lean
```
