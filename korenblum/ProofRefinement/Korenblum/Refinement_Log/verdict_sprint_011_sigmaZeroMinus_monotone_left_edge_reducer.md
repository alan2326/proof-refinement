# Verdict: sprint_011_sigmaZeroMinus_monotone_left_edge_reducer

**Date**: 2026-05-02
**Evaluated by**: korenblum-refinement-evaluator

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_011_sigmaZeroMinus_monotone_left_edge_reducer.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V11.lean`

## Outcome

**VERDICT_PASS**

## Gate results

| Gate | Result | Notes |
|------|--------|-------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)`. Warnings only, no errors. |
| 2. `grep -n 'sorry'` | PASS | No matches. |
| 3. Evaluator run | PASS | All sub-checks pass; score = `1777/5000`. |
| 4. Score vs parent (V10) | PASS | V11 score `1777/5000` >= V10 score `1777/5000`. |

## Evaluator detail

```
workspace imports: PASS
import audit:      PASS
compile:           PASS (8.79s)
type-check:        PASS (7.16s)
axiom scan:        PASS (8.41s)
axiom audit:       PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V11.hEq15_seed_3554
oracle audit:      PASS
score (maximize):  1777/5000
status:            PASS
```

## One-line reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V11.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V11.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache uv run korenblum/ProofRefinement/Korenblum/Evaluator.py --file korenblum/ProofRefinement/Korenblum/Candidates/V11.lean
```
