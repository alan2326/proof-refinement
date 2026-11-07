# Verdict: sprint_102_interval_arithmetic_oracle_migration_v66_seven_window_sqrt

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_102_interval_arithmetic_oracle_migration_v66_seven_window_sqrt.md`

**Candidate path (primary)**: `ProofRefinement/Korenblum/Candidates/V66.lean`

**Candidate path (regression)**: `ProofRefinement/Korenblum/Candidates/V68.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1 — `lake build`

Both candidates compiled with warnings only (no errors).

```
lake build ProofRefinement.Korenblum.Candidates.V66
# → Build completed successfully (8054 jobs)

lake build ProofRefinement.Korenblum.Candidates.V68
# → Build completed successfully (8055 jobs)
```

### Gate 2 — `grep -n 'sorry'`

No `sorry` tokens found in either candidate.

```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V66.lean  # (no output)
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean  # (no output)
```

### Gate 3 — Evaluator run

**V66**

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V66.lean
```

Result summary:
- compile: PASS (8.70s)
- type-check: PASS (7.15s)
- axiom scan: PASS (10.66s)
- axiom audit: PASS
  - `propext`, `Classical.choice`, `Quot.sound`
  - `ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt`
  - `ProofRefinement.Korenblum.Candidates.V66.hCircleGapInt_v66`
  - `ProofRefinement.Korenblum.Candidates.V66.hH2_v66`
  - (6 entries — set-theoretically identical to pre-sprint set)
- oracle audit: PASS
  - `h_seven_window_mass_certified_at_356562_sqrt`: oracle=1 declared=1 ok=true
- **score: 178281/500000**
- **status: PASS**

**V68 (regression)**

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```

Result summary:
- compile: PASS (8.48s)
- axiom audit: PASS (6 entries, unchanged from sprint 101 baseline)
- oracle audit: PASS — `h_eleven_window_mass_certified_at_356565_modeJ10`: oracle=1 declared=1 ok=true
- **score: 71313/200000**
- **status: PASS**

### Gate 4 — Score comparison against parent

Contract specifies score-neutral migration: V66 pre-sprint and post-sprint scores must be byte-identical at `178281/500000`.

Post-sprint evaluator returned `178281/500000` — exact match. Gate 4 PASS.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V66
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V66.lean
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3 (V66)
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V66.lean

# Gate 3 (V68 regression)
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```
