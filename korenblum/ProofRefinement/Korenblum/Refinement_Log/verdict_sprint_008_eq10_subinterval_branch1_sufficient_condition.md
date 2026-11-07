# Verdict: sprint_008_eq10_subinterval_branch1_sufficient_condition

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_008_eq10_subinterval_branch1_sufficient_condition.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V8.lean`
**Outcome**: PASS
**Failing gate**: none

## Gate results

### Gate 1: lake build
```
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V8.lean
```
Result: "Build completed successfully (8049 jobs)" — PASS (warnings only, no errors)

### Gate 2: sorry check
```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V8.lean
```
Result: no output — PASS

### Gate 3: evaluator
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V8.lean
```
Result: `score = 1777/5000`, `status: PASS` — PASS

Axioms used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V8.hEq15_seed_3554}` — matches expected set exactly.

### Gate 4: parent score comparison
Parent V7 score: `1777/5000`. V8 score: `1777/5000`. Contract requires `≥ V7`. Condition satisfied — PASS

## Acceptance criteria checks

- AC5: `valid_of_eq10_subinterval_branch1` has exactly one definition site in `Reduction.lean` (line 832). Body contains `paper.eq10_branch1_pointwise` (line 926), `mass_mul_le_annulusSlice_of_integral_bound_ae` (line 989), `annulusSlice_add_adjacent` (lines 1009, 1015) — PASS
- AC6: V8.lean references `valid_of_eq10_subinterval_branch1` at lines 57, 64, 82, 90 including the body of `v8_valid_of_eq10_subinterval_branch1_chain_compiles` — PASS
- AC7: No forbidden terms (`paper.eq2_*` through `paper.eq9_*`, `paper.eq11_*`–`paper.eq15_*`, `scalarIntegrand2`, `valid_of_eq15`, etc.) found in the body of the new theorem — PASS
- AC8: `paper.eq10_branch1_pointwise` appears at line 926 inside the new theorem body — PASS
- AC9: `v8_split_lt_one_at_seed` has exactly one definition site at V8.lean line 43 — PASS

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V8.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V8.lean

# Gate 3
cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V8.lean
```

## STATUS=VERDICT_PASS
