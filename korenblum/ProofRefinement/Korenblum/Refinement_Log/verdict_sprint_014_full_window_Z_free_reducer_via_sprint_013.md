# Verdict: sprint_014_full_window_Z_free_reducer_via_sprint_013

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_014_full_window_Z_free_reducer_via_sprint_013.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V14.lean`
**Parent candidate**: `Candidates/V13.lean` (score: 1777/5000)
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Result | Notes |
|------|--------|-------|
| 1. `lake build` | PASS | Build completed successfully (8049 jobs); only warnings, no errors |
| 2. `grep -n 'sorry'` | PASS | No `sorry` found in candidate |
| 3. Evaluator run | PASS | `score = 1777/5000`; axiom audit clean |
| 4. Score vs parent | PASS | V14 score `1777/5000` >= V13 score `1777/5000` |

## Evaluator summary

- namespace: `ProofRefinement.Korenblum.Candidates.V14`
- parent: `V13`
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.78s)
- type-check: PASS (6.43s)
- axiom scan: PASS (7.65s)
- axiom audit: PASS
  - seed propext
  - seed Classical.choice
  - seed Quot.sound
  - seed ProofRefinement.Korenblum.Candidates.V14.hEq15_seed_3554
- oracle audit: PASS
- score (maximize): `1777/5000`
- status: PASS

## Reproduction commands

```bash
# Gate 1: build
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V14.lean

# Gate 2: sorry check
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V14.lean

# Gate 3: evaluator
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
    --file korenblum/ProofRefinement/Korenblum/Candidates/V14.lean
```
