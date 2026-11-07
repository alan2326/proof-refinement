# Verdict: sprint_009_collapsed_disk_meets_eq8_eq9_lower

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_009_collapsed_disk_meets_eq8_eq9_lower.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V9.lean`
**Parent**: `Candidates/V8.lean` (score: 1777/5000)

## Outcome: PASS

All gates passed in order.

## Gate Results

### Gate 1: `lake build`
PASS. Build completed successfully (8049 jobs). Warnings only — no errors. Relevant warning: `unused variable 'paper'` in V9 at line 61 (lint only, no build failure).

Reproduction:
```bash
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V9.lean
```

### Gate 2: `grep -n 'sorry' Candidates/V9.lean`
PASS. No `sorry` found.

Reproduction:
```bash
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V9.lean
```

### Gate 3: Full evaluator run
PASS. Score: `1777/5000`. Axiom audit clean.

Axioms used:
- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V9.hEq15_seed_3554` (seed)

No new free-floating axioms introduced.

Reproduction:
```bash
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh \
  korenblum/ProofRefinement/Korenblum/Candidates/V9.lean
```

### Gate 4: Score comparison vs parent
PASS. V9 score `1777/5000 >= V8 score 1777/5000`. Contract required `>= V8`; no strict improvement required.

## Acceptance Criteria Spot-checks

- `valid_of_collapsed_disk_eq8_eq9_lower` appears at exactly one definition site in `Reduction.lean` (line 1082). Body contains exactly one use of `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` (line 1110) and one use of `annulusExcess_lower_bound_of_eq8_eq9` (line 1113), closed by `linarith` (line 1117).
- `valid_of_collapsed_disk_eq8_eq9_lower` is invoked in V9 inside `v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles` (line 78).
- `v9_branch_split_witness_at_seed` appears at exactly one definition site in V9 (line 45).
- No forbidden references (`diskExcess_upper_bound_of_eq2_eq3_eq4`, `circleGap_outer_lower_bound_of_eq8_eq9`, `valid_of_eq15`, etc.) appear in the body of `valid_of_collapsed_disk_eq8_eq9_lower`.

## STATUS: VERDICT_PASS
