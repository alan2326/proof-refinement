# Verdict: sprint_086_mixed_kernel_multi_window_reducer

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_086_mixed_kernel_multi_window_reducer.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V65.lean`
**Outcome**: PASS
**Failing gate**: none

## Gate results

### Gate 1 — lake build
```
lake build ProofRefinement.Korenblum.Candidates.V65
```
Result: `Build completed successfully (8053 jobs)`. Warnings only (linter style, unused variables). No errors.

### Gate 2 — sorry check
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V65.lean
```
Result: no output. No sorries present.

### Gate 3 — evaluator
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V65.lean
```
Result:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.57s)
- type-check: PASS (7.38s)
- axiom scan: PASS (9.56s)
- axiom audit: PASS (seed axioms: propext, Classical.choice, Quot.sound, hCircleGapInt_v64, hH2_v64, h_two_window_mass_certified_at_35646_sqrt)
- oracle audit: PASS
- score (maximize): 17823/50000 = 35646/100000
- status: PASS

### Gate 4 — parent score comparison
Not applicable. The contract does not require a strict score improvement over the parent (V65 ties V64 at 35646/100000 by design; the sprint ships structural work in Proof/Reduction.lean, not a c-push).

## New additions in Proof/Reduction.lean confirmed present

- `KernelKind` inductive at line 8837 (modeJ and branch1 constructors)
- `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae` standalone wrapper at line 8854
- `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` reducer at line 8934
- No sorries in Reduction.lean

V66 was not shipped (optional per Stop conditions §2); acceptance criteria 1-6 + 8 satisfied.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V65

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V65.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V65.lean
```
