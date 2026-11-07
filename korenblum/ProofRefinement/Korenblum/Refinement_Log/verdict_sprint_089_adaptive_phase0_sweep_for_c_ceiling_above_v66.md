# Verdict: sprint_089_adaptive_phase0_sweep_for_c_ceiling_above_v66

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_089_adaptive_phase0_sweep_for_c_ceiling_above_v66.md`

**Candidate path (regression target)**: `ProofRefinement/Korenblum/Candidates/V66.lean`
(This sprint ships no new candidate. Gates run on V66 as the live ceiling.)

**Scratch deliverables**:
- `ProofRefinement/Korenblum/Scratch/sprint_089_adaptive_seven_window_mass_sweep.py` (794 lines)
- `ProofRefinement/Korenblum/Scratch/sprint_089_adaptive_seven_window_mass_sweep.txt` (142 lines)
- `ProofRefinement/Korenblum/Scratch/sprint_089_witness.txt` (22 lines)

**Outcome**: PASS

---

## Gate results

### Gate 1 — `lake build ProofRefinement.Korenblum.Candidates.V66`

Result: **PASS**
Output: `Build completed successfully (8054 jobs)` (style warnings only; no errors).

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V66
```

### Gate 2 — `grep -n 'sorry' Candidates/V66.lean`

Result: **PASS** (no output; zero occurrences of `sorry`).

Reproduction:
```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V66.lean
```

### Gate 3 — Evaluator

Result: **PASS**

Score: `178281/500000` = `356562/1000000` (V66's expected score; no candidate ships this sprint).
Axiom audit: PASS (3 standard Lean axioms + 3 sprint-088 seed axioms, no unexpected entries).
Oracle audit: PASS (`h_seven_window_mass_certified_at_356562_sqrt`: oracle=1 declared=1).

Reproduction:
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V66.lean
```

### Gate 4 — Parent score comparison

Not applicable. Sprint 089 names no new candidate and no strict score improvement claim.
The sprint contract explicitly states "no candidate ships this sprint."

---

## Sprint deliverable checks

All acceptance criteria from the contract confirmed:

1. `.py` file exists, 794 lines (contract estimated ~770).
2. `.txt` file exists, 142 lines (contract estimated ~140); DECISION block is the last non-empty content.
3. DECISION line: **Phase 0 GO**
   - `c_new = 89141/250000 = 0.356564 > 356562/1000000 = 0.356562` (strictly greater, verified arithmetically).
   - `full-envelope margin = 0.0001182999346422620737284` (> 1e-4, verified at dps=80, n_trunc=300).
   - Architecture: `rho_top = 1 - 1e-9`, `delta_lo = 1e-9`, `extra_mode_count = 3` (8-window: 1 Branch.one + 7 per-mode j=7,6,5,4,3,2,1).
4. `sprint_089_witness.txt` exists (GO case confirmed; file present with architecture summary for sprint 090).
5. rho_top feasibility table covers 7 values: `{1-1e-3, 1-1e-4, 1-1e-5, 1-1e-6, 1-1e-7, 1-1e-8, 1-1e-9}`, all feasible (K^2 < 1).
6. Box-split invariance: `max |delta vs 1-box| = 1.75e-46`, invariance check < 1e-15: True.
7. No Lean candidate files created; V66 regression is a no-op pass.
8. Bulletin.md and Experience.md: to be verified by harness (out of evaluator scope; no Lean impact).
