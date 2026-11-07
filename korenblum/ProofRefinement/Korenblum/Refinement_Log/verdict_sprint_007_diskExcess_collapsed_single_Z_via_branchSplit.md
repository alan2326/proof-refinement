# Verdict: sprint_007_diskExcess_collapsed_single_Z_via_branchSplit

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_007_diskExcess_collapsed_single_Z_via_branchSplit.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V7.lean`
**Parent**: `Candidates/V6.lean` (score 1777/5000)

## Outcome

VERDICT_PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build` | PASS — `Build completed successfully (8049 jobs)`, warnings only |
| 2. `grep -n 'sorry' Candidates/V7.lean` | PASS — no matches |
| 3. Full evaluator run | PASS — score 1777/5000, axiom audit clean |
| 4. Parent score comparison (>= V6 = 1777/5000) | PASS — 1777/5000 >= 1777/5000 |

## Evaluator summary

- compile: PASS
- type-check: PASS
- axiom audit: PASS
  - `propext` (seed)
  - `Classical.choice` (seed)
  - `Quot.sound` (seed)
  - `ProofRefinement.Korenblum.Candidates.V7.hEq15_seed_3554` (seed)
- workspace imports: PASS
- oracle audit: PASS
- **score (maximize): 1777/5000**

## Acceptance-criteria checks

1. `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` appears at exactly one definition site in `Proof/Reduction.lean` (line 596) and its body (lines 610-635) invokes both `diskExcess_upper_bound_of_eq2_eq3_eq4` (line 615) and `sigmaZeroMinus_nonneg_of_pos` (line 618).
2. The body contains no banned identifiers (`paper.eq*`, `scalarCriterion`, `valid_of_eq15`, etc.).
3. `Candidates/V7.lean` invokes the new bound at line 56 inside `v7_diskExcess_collapsed_single_Z_chain_compiles`.
4. `v7_branch_split_witness_at_seed` appears at exactly one definition site (line 67 of V7.lean).
5. Axiom set matches contract spec (no new free-floating axioms).

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V7.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V7.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V7.lean
```
