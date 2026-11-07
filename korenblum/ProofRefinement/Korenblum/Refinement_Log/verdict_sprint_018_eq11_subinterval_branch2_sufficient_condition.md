# Verdict: sprint_018_eq11_subinterval_branch2_sufficient_condition

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_018_eq11_subinterval_branch2_sufficient_condition.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V18.lean`
**Parent candidate**: `Candidates/V17.lean` (score: 1777/5000)
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V18` | PASS (8049 jobs, warnings only) |
| 2. `grep -n 'sorry' Candidates/V18.lean` | PASS (no matches) |
| 3. Evaluator run | PASS — score 1777/5000 |
| 4. Score >= parent (V17 = 1777/5000) | PASS — 1777/5000 >= 1777/5000 |

## Evaluator summary

```
compile:       PASS (9.23s)
type-check:    PASS (7.01s)
axiom scan:    PASS (7.68s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V18.hEq15_seed_3554
oracle audit:  PASS
score (maximize): 1777/5000
status: PASS
```

## Reproduction commands

```bash
# Gate 1: build
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V18.lean

# Gate 2: sorry check
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V18.lean

# Gate 3: evaluator
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V18.lean
```

## STATUS=VERDICT_PASS
