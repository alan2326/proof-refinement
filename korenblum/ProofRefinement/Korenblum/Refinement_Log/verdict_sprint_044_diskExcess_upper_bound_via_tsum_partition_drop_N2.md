# Verdict: sprint_044_diskExcess_upper_bound_via_tsum_partition_drop_N2

**Contract**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_044_diskExcess_upper_bound_via_tsum_partition_drop_N2.md
**Candidate**: ProofRefinement/Korenblum/Candidates/V44.lean
**Parent candidate**: Candidates/V43.lean
**Outcome**: PASS
**Failing gate**: none

## Gate results

1. `lake build ProofRefinement.Korenblum.Candidates.V44` — PASS (8049 jobs, warnings only)
2. `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V44.lean` — PASS (no matches)
3. Evaluator run — PASS
   - compile: PASS (8.66s)
   - type-check: PASS (6.12s)
   - axiom scan: PASS (8.54s)
   - axiom audit: PASS — axioms used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V44.hEq15_seed_3554}`
   - score: 1777/5000 (ties V43, as specified by contract)
   - status: PASS
4. Parent score comparison — PASS (V44 score 1777/5000 equals V43 score 1777/5000; contract explicitly specifies score is preserved, not improved)

## Score

score = 1777/5000

## Reproduction

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V44

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V44.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V44.lean
```

## STATUS=VERDICT_PASS
