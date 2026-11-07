# Verdict: sprint_017_branch2_singleton_closing_reducer_via_eq6_eq8_eq9

- **Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_017_branch2_singleton_closing_reducer_via_eq6_eq8_eq9.md`
- **Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V17.lean`
- **Parent candidate**: `Candidates/V16.lean` (score: 1777/5000)
- **Outcome**: PASS
- **Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V17` | PASS (8049 jobs, no errors) |
| 2. `grep -n 'sorry' Candidates/V17.lean` | PASS (no matches) |
| 3. Evaluator run | PASS — score 1777/5000 |
| 4. Score vs parent (V16 = 1777/5000, required >=) | PASS (1777/5000 >= 1777/5000) |

## Evaluator summary

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.65s)
- type-check: PASS (6.76s)
- axiom scan: PASS (7.60s)
- axiom audit: PASS — axioms exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V17.hEq15_seed_3554}`
- oracle audit: PASS
- score (maximize): **1777/5000**
- status: PASS

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V17

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V17.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V17.lean
```

## Notes

The candidate ships the workspace's first closing reducer living entirely on the branch-2 sub-regime `(branchSplit c, 1)`, the first closing reducer with no disk-side integrability premise, and the first reducer to consume sprint 016's `eq6`-based disk bound in a closing chain (`valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` in `Proof/Reduction.lean`). The sink theorem is still discharged via `valid_of_eq15` so the score is preserved at 1777/5000.
