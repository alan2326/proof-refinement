# Verdict: sprint_020_mobius_disk_automorphism

**Contract path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_020_mobius_disk_automorphism.md`

**Candidate path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V20.lean`

**New module path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/MobiusDisk.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1 — lake build
```
lake build ProofRefinement.Korenblum.Candidates.V20
```
Result: `Build completed successfully (8048 jobs)`. Warnings only (unused variables in older modules, unrelated to V20/MobiusDisk).

### Gate 2 — sorry check
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V20.lean
grep -n 'sorry' ProofRefinement/Korenblum/Proof/MobiusDisk.lean
```
Result: no matches in either file. Exit code 1 (no sorry).

### Gate 3 — evaluator
```
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V20.lean
```
Result:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.17s)
- type-check: PASS (6.14s)
- axiom scan: PASS (6.77s)
- axiom audit: PASS (axioms: propext, Classical.choice, Quot.sound, hKorenblum_published_3554)
- oracle audit: PASS
- score: 1777/5000 (= 3554/10000, unchanged from V19 as expected by contract)
- status: PASS

### Gate 4 — parent score comparison
Contract states the score is unchanged from V19 and that this is expected and not a failure. No strict improvement required. Gate 4 does not apply.

---

## Acceptance criteria check

1. `lake build` succeeded, no sorry, no disallowed axioms. PASS.
2. Evaluator accepted V20. Score 3554/10000 unchanged from V19 — expected per contract. PASS.
3. `Proof/MobiusDisk.lean` contains `noncomputable def mobiusDisk (a z : ℂ) : ℂ := (a - z) / (1 - (starRingEnd ℂ) a * z)` and all five headline theorems (`mobiusDisk_denom_ne_zero`, `mobiusDisk_one_sub_normSq`, `mobiusDisk_mapsTo`, `mobiusDisk_involution`, `mobiusDisk_analyticOn`) as `theorem`s with no `sorry`. Proof of (2) calls `Complex.normSq_sub` and a `field_simp` + `ring` chain. PASS.
4. Theorem (4) `mobiusDisk_involution` is present. PASS (full delivery, no fallback needed).
5. `Proof.MobiusDisk` is imported in V20 (`import ProofRefinement.Korenblum.Proof.MobiusDisk`). PASS.
6. Internal consistency: all five theorems are well-formed and mutually consistent. PASS.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V20

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V20.lean
grep -n 'sorry' ProofRefinement/Korenblum/Proof/MobiusDisk.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V20.lean
```
