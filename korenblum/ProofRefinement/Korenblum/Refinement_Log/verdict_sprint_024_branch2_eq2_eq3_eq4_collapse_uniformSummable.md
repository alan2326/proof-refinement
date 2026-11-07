# Verdict: sprint_024_branch2_eq2_eq3_eq4_collapse_uniformSummable

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_024_branch2_eq2_eq3_eq4_collapse_uniformSummable.md`

**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V24.lean`

**Outcome**: PASS

**Failing gate**: none

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1. lake build | `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V24.lean` | PASS (8049 jobs, no errors) |
| 2. sorry check | `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V24.lean` | PASS (no matches) |
| 3. evaluator | `env UV_CACHE_DIR=korenblum/.uv-cache uv run korenblum/ProofRefinement/Korenblum/Evaluator.py --file korenblum/ProofRefinement/Korenblum/Candidates/V24.lean` | PASS |
| 4. score >= parent | score 1777/5000 >= parent V23 score 1777/5000 | PASS |

## Evaluator output summary

- score (maximize): **1777/5000**
- axioms used: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V24.hEq15_seed_3554`
- import audit: PASS
- workspace imports: PASS
- compile: PASS (9.23s)
- type-check: PASS (7.14s)
- axiom scan: PASS (8.89s)
- oracle audit: PASS

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V24.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V24.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V24.lean
```

## STATUS=VERDICT_PASS
