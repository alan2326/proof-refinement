# Verdict: sprint_013_disk_bound_via_eq3_eq4_full_window

**Contract path**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_013_disk_bound_via_eq3_eq4_full_window.md`
**Candidate path**: `korenblum/ProofRefinement/Korenblum/Candidates/V13.lean`
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build` | PASS — `Build completed successfully (8049 jobs)` |
| 2. `grep -n 'sorry' Candidates/V13.lean` | PASS — no matches |
| 3. Full evaluator run | PASS — `score (maximize): 1777/5000`, `status: PASS` |
| 4. Parent score comparison (V12 = 1777/5000, V13 = 1777/5000) | PASS — score >= parent score |

## Evaluator summary

- namespace: `ProofRefinement.Korenblum.Candidates.V13`
- parent: `V12`
- score: `1777/5000` (= `c_value` = 3554/10000 = 0.3554)
- axioms used: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V13.hEq15_seed_3554`
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.84s)
- type-check: PASS (6.74s)
- axiom scan: PASS (7.85s)
- axiom audit: PASS
- oracle audit: PASS

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V13.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V13.lean

# Gate 3
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V13.lean
```
