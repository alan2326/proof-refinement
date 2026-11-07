# Verdict: sprint_084_per_mode_multi_window_reducer_general_m

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_084_per_mode_multi_window_reducer_general_m.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V65.lean`
**Parent**: V64 (score 35646/100000)
**Outcome**: PASS
**Failing gate**: none

## Gate results

- Gate 1 (`lake build`): PASS — `Build completed successfully (8053 jobs)`; warnings only, no errors in `Proof/Reduction.lean` or `Candidates/V65.lean`.
- Gate 2 (`grep sorry`): PASS — no `sorry` in V65.lean (exit 1, no matches).
- Gate 3 (evaluator): PASS
  - workspace imports: PASS
  - import audit: PASS
  - compile: PASS (8.10s)
  - type-check: PASS (8.45s)
  - axiom scan: PASS (10.56s)
  - axiom audit: PASS — axioms are `{propext, Classical.choice, Quot.sound, V65.hCircleGapInt_v64, V65.hH2_v64, V65.h_two_window_mass_certified_at_35646_sqrt}` (byte-for-byte identical to V64's envelope modulo V65 namespace)
  - oracle audit: PASS — `h_two_window_mass_certified_at_35646_sqrt` passes
  - score: `17823/50000 = 35646/100000` (ties V64 as intended)
  - status: PASS
- Gate 4 (parent tie check): Not applicable (contract specifies a tie, not a strict improvement; tie confirmed).

## Key findings

- `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` exists in `Proof/Reduction.lean` at line 8382, using `{n : ℕ}` so `Fin (n+1)` indexing (m = n+1).
- Private helper `sum_annulusSlice_collapse_adjacent` at line 8249 collapses the `Fin (n+1)`-indexed sum of annulus slices via induction — no sorry, clean induction on `Fin.induction`.
- V65 invokes the new general reducer with `n := 1` (Fin 2, m = 2), not the old `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`.
- The sprint-072 `hcEqStart0` rewrite-motive obstruction is not present: the new reducer avoids the pattern-match form that triggered it, using functional-induction (`Fin.induction`) over the chain of adjacency hypotheses instead.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V65

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V65.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V65.lean
```
