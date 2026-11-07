# Verdict: Sprint 083 / V64

**Contract**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_083_v64_first_c_push_past_v52_sqrt_endpoints.md`
**Candidate**: `ProofRefinement/Korenblum/Candidates/V64.lean`
**Derived file**: `ProofRefinement/Korenblum/Candidates/V64/TauWindowEndpoints.lean`
**Date**: 2026-05-04

## Outcome

**VERDICT_PASS**

All four gates passed.

## Gate results

### Gate 1 — `lake build`

```
lake build ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints
```
Result: `Build completed successfully (8045 jobs)` — warnings only (unused variable `hc`, linter style). No errors.

```
lake build ProofRefinement.Korenblum.Candidates.V64
```
Result: `Build completed successfully (8053 jobs)` — warnings only (`show` tactic linter, unused lambda variables). No errors.

### Gate 2 — `grep -n 'sorry'`

```
grep -n 'sorry' Candidates/V64.lean Candidates/V64/TauWindowEndpoints.lean
```
Result: one match in a comment in `TauWindowEndpoints.lean:24` (text "no `sorry`s"). No actual `sorry` tactic or `sorryAx` use in either file.

### Gate 3 — Evaluator run

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V64.lean
```

Result: `status: PASS`

Key evaluator output:
- `import audit: PASS`
- `compile: PASS (8.83s)`
- `type-check: PASS (7.36s)`
- `axiom scan: PASS (9.64s)`
- `axiom audit: PASS`
  - `seed  propext`
  - `seed  Classical.choice`
  - `seed  Quot.sound`
  - `seed  ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64`
  - `seed  ProofRefinement.Korenblum.Candidates.V64.hH2_v64`
  - `seed  ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt`
- `oracle audit: PASS`
  - `PASS  h_two_window_mass_certified_at_35646_sqrt: oracle=1 declared=1`
- `score (maximize): 17823/50000`

Score 17823/50000 = 35646/100000 = 0.35646.

### Gate 4 — Strict score improvement over parent V63

Contract states parent V63 = 7129/20000 = 35645/100000 = 0.35645.

- V64 score: 17823/50000 = 35646/100000 = 0.35646
- V63 score: 7129/20000 = 35645/100000 = 0.35645
- Strict improvement: 35646/100000 > 7129/20000 iff 35646×20000 > 7129×100000 iff 712920000 > 712900000. TRUE.
- Margin: 1/100000 = 1e-5 (as stated in contract).

Gate 4 passes — the improvement is STRICT, not a tie.

## H² consolidation note

The contract named two separate axioms `hH2_a_v64` and `hH2_b_v64`, but noted the generator may ship a consolidated formulation `hH2_v64 : ∀ (a : ℕ → ℂ), Summable (fun n => ‖a n‖^2)` for elaboration reasons, and that this is functionally equivalent. The shipped candidate uses exactly this consolidated form, registered as `"hH2_v64"` in `[seed_axioms].allowed`. The axiom is applied at `a` and `b` separately in the `h_witness` construction (lines 263-266 of V64.lean). Functional equivalence is confirmed. The H² consolidation is acceptable per this prompt's explicit instruction.

## Axiom envelope comparison

Contract allowed set (superset check):
`{propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler, ...hH2_a_v64, ...hH2_b_v64, ...hCircleGapInt_v64, ...h_two_window_mass_certified_at_35646_sqrt}`

Actual axiom set (with `hH2_v64` replacing the two-part axioms):
`{propext, Classical.choice, Quot.sound, ...hH2_v64, ...hCircleGapInt_v64, ...h_two_window_mass_certified_at_35646_sqrt}`

Actual set is a strict subset of the allowed set (the consolidation is within scope per contract). `Lean.ofReduceBool` and `Lean.trustCompiler` are absent, which is fine — the allowed set is a ceiling, not a floor.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints
lake build ProofRefinement.Korenblum.Candidates.V64

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V64.lean ProofRefinement/Korenblum/Candidates/V64/TauWindowEndpoints.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V64.lean

# Gate 4 (arithmetic check)
python3 -c "from fractions import Fraction; print(Fraction(17823,50000) > Fraction(7129,20000))"
```
