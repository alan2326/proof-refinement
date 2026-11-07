# Verdict: sprint_059

**Contract**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_059_fourth_c_push_via_eq15_oracle_at_hp_35645_finer_denominator.md`

**Candidate**: `ProofRefinement/Korenblum/Candidates/V52.lean`

**Outcome**: PASS

**Failing gate**: none — all four gates passed.

---

## Gate results

### Gate 1: `lake build`

```
lake build ProofRefinement.Korenblum.Candidates.V52
```

Result: `Build completed successfully (8049 jobs)`. Exit code 0.

### Gate 2: `grep -n 'sorry' Candidates/V52.lean`

Result: no matches.

### Gate 3: Full evaluator run

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V52.lean
```

Result:
- `compile:       PASS`
- `type-check:    PASS`
- `axiom scan:    PASS`
- `axiom audit:   PASS` — axioms used: `propext`, `Classical.choice`, `Quot.sound`, `hEq15_oracle_certified_hp_35645` (no stale per-c axioms)
- `oracle audit:  PASS` — `PASS  hEq15_oracle_certified_hp_35645: oracle=1 declared=1`
- `score (maximize): 7129/20000`
- `status: PASS`

### Gate 4: Strict-improvement check

- Parent candidate: `V51` with score `891/2500 = 35640/100000`
- New candidate: `V52` with score `7129/20000 = 35645/100000`
- `7129/20000 > 891/2500`: TRUE (delta = `1/20000` = `+0.00005`)

Strict improvement confirmed.

---

## One-line reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V52

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V52.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V52.lean

# Gate 4
python3 -c "from fractions import Fraction; assert Fraction('7129/20000') > Fraction('891/2500'), 'strict improvement failed'; print('OK')"
```
