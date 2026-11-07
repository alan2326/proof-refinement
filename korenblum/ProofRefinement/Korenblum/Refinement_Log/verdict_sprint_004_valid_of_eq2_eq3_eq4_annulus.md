# Verdict: sprint_004_valid_of_eq2_eq3_eq4_annulus

**Contract**: korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_004_valid_of_eq2_eq3_eq4_annulus.md
**Candidate**: korenblum/ProofRefinement/Korenblum/Candidates/V4.lean
**Parent candidate**: Candidates/V3.lean
**Evaluated**: 2026-05-02

## Outcome: PASS

All gates passed.

## Gate results

### Gate 1: lake build
PASS — `Build completed successfully (8049 jobs)`.
Only warnings (lint style, unused variables); zero errors.

Reproduction:
```
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V4.lean
```

### Gate 2: sorry scan
PASS — `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V4.lean` returned no matches.

Reproduction:
```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V4.lean
```

### Gate 3: evaluator
PASS — evaluator reported `status: PASS`, `score (maximize): 1777/5000`.

Axioms used:
- propext (seed)
- Classical.choice (seed)
- Quot.sound (seed)
- ProofRefinement.Korenblum.Candidates.V4.hEq15_seed_3554 (seed)

No unexpected axioms. Import audit: PASS. Oracle audit: PASS.

Reproduction:
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V4.lean
```

### Gate 4: parent score comparison
PASS — V3 score: 1777/5000; V4 score: 1777/5000. Contract requires `>= V3`; satisfied (equal).

## Score
1777/5000

## STATUS: VERDICT_PASS
