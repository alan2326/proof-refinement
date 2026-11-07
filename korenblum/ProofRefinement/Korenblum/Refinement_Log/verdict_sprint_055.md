# Verdict: sprint_055_first_c_push_via_eq15_oracle_at_3560

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_055_first_c_push_via_eq15_oracle_at_3560.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V49.lean`
**Outcome**: PASS
**Failing gate**: none

## Gate results

**Gate 1 — lake build**

```
lake build ProofRefinement.Korenblum.Candidates.V49
```
Result: PASS (exit 0; 8049 jobs, warnings only, no errors)

**Gate 2 — no sorry**

```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V49.lean
```
Result: PASS (exit 1, no matches)

**Gate 3 — full evaluator run**

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V49.lean
```
Result: PASS (exit 0)

Key evaluator output lines:
- `oracle audit:  PASS`
- `  PASS  hEq15_oracle_certified_3560: oracle=1 declared=1`
- `score (maximize): 89/250`
- `status: PASS`

Axioms used: `propext`, `Classical.choice`, `Quot.sound`,
`ProofRefinement.Korenblum.Candidates.V49.hEq15_oracle_certified_3560`

No `hEq15_oracle_certified_3554` or `hEq15_seed_3554` in axiom set.

Oracle check: `{axiom: "hEq15_oracle_certified_3560", bound_field: "eq15_lower_bound", declared: "1", oracle_bound: "1", ok: true}`

**Gate 4 — strict score improvement**

Parent candidate: `Candidates/V48.lean`, parent score: `1777/5000 = 0.355400`
New score: `89/250 = 1780/5000 = 0.356000`
Strict improvement check: `1780/5000 > 1777/5000` — PASS

## Reproduction commands

```bash
# Gate 1
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V49

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V49.lean

# Gate 3
cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V49.lean

# Gate 4 (score check)
python3 -c "from fractions import Fraction; assert Fraction('89/250') > Fraction('1777/5000'); print('PASS')"
```

## Summary

V49 proves `ValidKorenblumBound c_value` at `c_value = 1780/5000 = 0.3560`,
the workspace's first c-push above the seed in 55 sprints. The
`hEq15_oracle_certified_3560` axiom is discharged by the registered oracle
`rigorous_scalar.certify_eq15_at_3560` via `certify_eq15(1780, 5000, dps=50,
n_trunc=200)`. Score `89/250 = 1780/5000 > 1777/5000` — strict improvement
confirmed.
