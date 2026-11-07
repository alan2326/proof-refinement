# Verdict: sprint_077_phase0_per_k_alpha_varying_kernel_sweep

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_077_phase0_per_k_alpha_varying_kernel_sweep.md`

**Candidate path**: `ProofRefinement/Korenblum/Candidates/V60.lean`
**Derived-theorem path**: `ProofRefinement/Korenblum/Candidates/V60/PerKAlphaVaryingLiftIdentity.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1: lake build

`lake build ProofRefinement.Korenblum.Candidates.V60` completed with
`Build completed successfully (8051 jobs)`. Warnings only (style lints, unused
variables); no errors.

Reproduction:
```bash
lake build ProofRefinement.Korenblum.Candidates.V60
```

### Gate 2: grep sorry

No `sorry` in `Candidates/V60.lean` or `Candidates/V60/PerKAlphaVaryingLiftIdentity.lean`.

Reproduction:
```bash
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V60.lean
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V60/PerKAlphaVaryingLiftIdentity.lean
```

### Gate 3: full evaluator run

Evaluator exit: `status: PASS`, `score (maximize): 7129/20000`.

Axioms used (byte-for-byte match with V59 envelope modulo namespace prefix):
```
seed  propext
seed  Classical.choice
seed  Quot.sound
seed  ProofRefinement.Korenblum.Candidates.V60.hEq15_oracle_certified_hp_35645
```

Oracle audit: PASS — `hEq15_oracle_certified_hp_35645: oracle=1 declared=1`.

Reproduction:
```bash
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V60.lean
```

### Gate 4: parent score comparison

Contract designates this sprint as "V59-tied" — no strict improvement required.
Parent V59 score: `7129/20000` (confirmed from log). V60 score: `7129/20000`.
Tie is the contracted outcome; Gate 4 not applicable.

---

## Notes

- `Candidates/V60/PerKAlphaVaryingLiftIdentity.lean` is the workspace's first
  per-candidate derived-theorem file with `α : ℕ → ℝ` signature (per-mode
  α(·)), wrapping V54's `lift_identity_per_k` at α := α(k) per index.
- Phase A mpmath sweep returned GO (witness at c=0.3565, `all_over(α0=0.10,
  α_h=1.01)` family, worst margin +2.0e-2 on E5), with structural caveat that
  `max|α(k)| = 1.01 > 1` exits V54's contraction regime. No
  contraction-regime witness exists above c=0.35645 in the structured grid.
- The axiom envelope is identical to V59's modulo the V60 namespace prefix on
  `hEq15_oracle_certified_hp_35645`.
