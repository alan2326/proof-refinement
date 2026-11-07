# Verdict: sprint_057

**Contract**:
`ProofRefinement/Korenblum/Sprint_Contracts/sprint_057_third_c_push_via_eq15_oracle_with_tiered_envelope_scratch_preverification.md`

**Candidate**:
`ProofRefinement/Korenblum/Candidates/V51.lean`

**Outcome**: PASS

**Failing gate**: none — all four gates passed.

---

## Gate results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V51`

PASS. Build completed successfully (8049 jobs, warnings only — no errors).

Reproduction:

```bash
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V51
```

### Gate 2 — `grep -n 'sorry' Candidates/V51.lean`

PASS. No matches.

Reproduction:

```bash
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V51.lean
```

### Gate 3 — Evaluator

PASS. Full evaluator output:

- `oracle audit:  PASS`
- `  PASS  hEq15_oracle_certified_hp_3564: oracle=1 declared=1`
- `score (maximize): 891/2500`
- `status: PASS`

Reproduction:

```bash
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V51.lean
```

### Gate 4 — Strict score improvement over parent V50

PASS. New score `891/2500 = 1782/5000` is strictly greater than parent V50's score `1781/5000`.

Verification:

```python
from fractions import Fraction
assert Fraction('891/2500') > Fraction('1781/5000')  # True: 0.3564 > 0.3562
```

---

## Summary

V51 proves `korenblum_constant_search : ValidKorenblumBound c_value` at
`c_value = 1782/5000 = 0.3564` (path HP-3564). This is the workspace's third
consecutive c-push. The axiom `hEq15_oracle_certified_hp_3564` is registered
in `lemma.toml` and dispatches to
`Numerical_Library.rigorous_scalar.certify_eq15_at_hp_3564`, which calls
`certify_eq15(1782, 5000, dps=100, n_trunc=500)`. The tiered Scratch
pre-verification confirmed the standard envelope (dps=50, n_trunc=200)
rejected at c=0.3564 (margin -6.89e-04) and the upgraded HP envelope
accepted (margin +1.17e-03). This is the first workspace oracle to use the
upgraded precision envelope (dps=100, n_trunc=500).
