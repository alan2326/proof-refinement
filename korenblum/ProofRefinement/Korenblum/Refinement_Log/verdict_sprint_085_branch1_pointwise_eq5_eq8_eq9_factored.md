# Verdict: sprint_085_branch1_pointwise_eq5_eq8_eq9_factored

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_085_branch1_pointwise_eq5_eq8_eq9_factored.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V65.lean`

(Sprint 085 is a pure DRY refactor of `Proof/Reduction.lean`; no new candidate file ships. V65.lean is the downstream consumer used as the regression check.)

## Outcome

PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V65` | PASS (8053 jobs, warnings only) |
| 2. `grep -n 'sorry' Candidates/V65.lean` | PASS (no output) |
| 3. Evaluator `--file Candidates/V65.lean` | PASS (`status: PASS`, score `17823/50000`) |
| 4. Parent score comparison (DRY refactor, score unchanged) | PASS (17823/50000 == 17823/50000, tie is expected) |

## Evaluator summary

- compile: PASS (8.80s)
- type-check: PASS (7.55s)
- axiom scan: PASS (9.35s)
- axiom audit: PASS
  - seed  propext
  - seed  Classical.choice
  - seed  Quot.sound
  - seed  ProofRefinement.Korenblum.Candidates.V65.hCircleGapInt_v64
  - seed  ProofRefinement.Korenblum.Candidates.V65.hH2_v64
  - seed  ProofRefinement.Korenblum.Candidates.V65.h_two_window_mass_certified_at_35646_sqrt
- oracle audit: PASS
- score (maximize): 17823/50000  (= 35646/100000, matches contract expectation)

Axiom envelope is byte-for-byte identical to the contract's expected set (3 standard Lean axioms + 3 V65-namespaced seeds; no new free axioms).

## Structural deliverables verified

- New theorem `pointwise_branch1_on_Ioo_eq5_eq8_eq9` added at `Proof/Reduction.lean:2522` (Option beta, `Set.Ioo` form per contract).
- Consumer `valid_of_eq5_eq8_eq9_subinterval_branch1` refactored to invoke the new theorem at lines 2686-2693.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V65

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V65.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V65.lean
```
