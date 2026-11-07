# Verdict: sprint_056_second_c_push_via_eq15_oracle_at_3562_with_scratch_preverification

**Contract**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_056_second_c_push_via_eq15_oracle_at_3562_with_scratch_preverification.md
**Candidate**: ProofRefinement/Korenblum/Candidates/V50.lean
**Evaluated**: 2026-05-02

## Outcome

VERDICT_PASS

## Gate results

### Gate 1 — lake build

```
lake build ProofRefinement.Korenblum.Candidates.V50
```

Result: PASS (exit 0, "Build completed successfully (8049 jobs)", warnings only, no errors)

### Gate 2 — sorry check

```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V50.lean
```

Result: PASS (no matches)

### Gate 3 — Evaluator

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V50.lean
```

Result: PASS (exit 0)

Key Evaluator output lines:
- `oracle audit:  PASS`
- `  PASS  hEq15_oracle_certified_3562: oracle=1 declared=1`
- `score (maximize): 1781/5000`
- `status: PASS`

Axioms used: propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V50.hEq15_oracle_certified_3562

### Gate 4 — Strict improvement over parent V49

Parent V49 score: 89/250 = 1780/5000 = 0.356000
Candidate V50 score: 1781/5000 = 0.356200
Inequality 1781/5000 > 1780/5000: HOLDS (True)

Result: PASS

## Reproduction commands

```bash
# Gate 1
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V50

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V50.lean

# Gate 3
cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V50.lean

# Gate 4 (strict improvement check)
python3 -c "from fractions import Fraction; assert Fraction('1781/5000') > Fraction('89/250'); print('PASS')"
```
