# Verdict — Sprint 091: Phase 0 extended-architecture sweep above V67

**Contract path**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_091_phase0_extended_architecture_sweep_above_v67.md`

**Candidate path**: `korenblum/ProofRefinement/Korenblum/Candidates/V67.lean`
(no new candidate ships this sprint; gates run on the parent V67 per contract instruction)

**Outcome**: PASS

**Failing gate**: none — all gates passed

---

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V67`

PASS. Build completed successfully (8055 jobs). Only style-linter warnings
(long lines, `show` vs `change`), no errors.

Reproduction:
```
lake build ProofRefinement.Korenblum.Candidates.V67
```

### Gate 2: `grep -n 'sorry' Candidates/V67.lean`

PASS. No matches.

Reproduction:
```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V67.lean
```

### Gate 3: Evaluator run

PASS. All sub-checks passed. Final evaluator output:

```
import audit:  PASS
compile:       PASS (75.40s)
type-check:    PASS (65.03s)
axiom scan:    PASS (51.30s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.h_eight_window_mass_certified_at_356564_modeJ7
  seed  ProofRefinement.Korenblum.Candidates.V67.hCircleGapInt_v67
  seed  ProofRefinement.Korenblum.Candidates.V67.hH2_v67
oracle audit:  PASS
  PASS  h_eight_window_mass_certified_at_356564_modeJ7: oracle=1 declared=1
score (maximize): 89141/250000
status: PASS
```

Reproduction:
```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V67.lean
```

### Gate 4: Parent/score comparison

N/A. This sprint ships no new candidate. The contract instructs the evaluator
to confirm V67 passes byte-for-byte at score 89141/250000, which it does.

---

## Summary

V67 builds cleanly, contains no `sorry`, passes all evaluator checks, and
scores `89141/250000` (= 356564/1000000) as expected. The Sprint 091 Phase 0
GO witness (`Scratch/sprint_091_witness.txt`) locates a new ceiling at
`c_new = 71313/200000 = 356565/1000000` (+1e-6 above V67) with full-envelope
margin +1.0048e-4 under an 11-window architecture. Sprint 092 may proceed to
ship V68 at `c_new` per the GO witness.
