# Verdict: sprint_101_monotonicity_aware_lambda_upper_in_two_window_helper

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_101_monotonicity_aware_lambda_upper_in_two_window_helper.md`

**Target file**: `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`

**Candidates evaluated**: `Candidates/V64.lean`, `Candidates/V68.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1 — lake build

- `lake build ProofRefinement.Korenblum.Candidates.V64`: **PASS** (Build completed successfully, warnings only)
- `lake build ProofRefinement.Korenblum.Candidates.V68`: **PASS** (Build completed successfully, warnings only)

### Gate 2 — sorry check

- `grep -n 'sorry' Candidates/V64.lean`: **PASS** (no output)
- `grep -n 'sorry' Candidates/V68.lean`: **PASS** (no output)

### Gate 3 — evaluator run

**V64** (`env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V64.lean`):
- status: PASS
- score: `17823/50000`
- axioms_used (6 entries): `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64`, `ProofRefinement.Korenblum.Candidates.V64.hH2_v64`, `ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt`
- oracle_checks: `h_two_window_mass_certified_at_35646_sqrt` oracle=1 declared=1 ok=true

**V68** (`env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V68.lean`):
- status: PASS
- score: `71313/200000`
- axioms_used (6 entries): `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`, `ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68`, `ProofRefinement.Korenblum.Candidates.V68.hH2_v68`
- oracle_checks: `h_eleven_window_mass_certified_at_356565_modeJ10` oracle=1 declared=1 ok=true

### Gate 4 — score comparison (score-neutral sprint)

Contract requires V64 score = exactly `17823/50000` (= `35646/100000`) and V68 score = exactly `71313/200000`.

- V64 pre-sprint score (log): `17823/50000` — post-sprint score: `17823/50000` — **EQUAL (PASS)**
- V68 pre-sprint score (log): `71313/200000` — post-sprint score: `71313/200000` — **EQUAL (PASS)**

Both axioms_used sets match the pre-sprint log entries set-theoretically.

---

## Dispatch implementation verified

`_two_window_mass_window_lower_arb` in `Numerical_Library/rigorous_scalar.py` (lines 1577–1601) now contains the three-branch dispatch:
- `(rho_hi <= sqrt_c_arb) is True` → single point evaluation at `rho_hi` (K increasing, max at right endpoint)
- `(sqrt_c_arb <= rho_lo) is True` → single point evaluation at `rho_lo` (K decreasing, max at left endpoint)
- else (straddle/undecided) → three-candidate union `Lam_lo.union(Lam_hi).union(Lam_sqrt)`

Helper signature unchanged. `sqrt_c_arb` is passed in from the caller (computed once outside the subdivision loop). K-cache preserved.

Phase 0 witness script present at `Scratch/sprint_101_monotonic_lambda_witness.py`.

---

## Reproduction commands

```bash
# Gate 1 — build
lake build ProofRefinement.Korenblum.Candidates.V64
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2 — sorry check
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V64.lean
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3 — evaluator
env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V64.lean
env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V68.lean
```
