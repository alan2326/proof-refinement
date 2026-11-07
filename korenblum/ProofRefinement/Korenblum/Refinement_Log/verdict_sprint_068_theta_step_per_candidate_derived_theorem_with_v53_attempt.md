# Verdict: sprint_068_theta_step_per_candidate_derived_theorem_with_v53_attempt

**Contract**:
`ProofRefinement/Korenblum/Sprint_Contracts/sprint_068_theta_step_per_candidate_derived_theorem_with_v53_attempt.md`

**Candidate**:
`ProofRefinement/Korenblum/Candidates/V53.lean`
(plus derived-theorem file `ProofRefinement/Korenblum/Candidates/V53/ThetaStep.lean`)

**Outcome**: PASS

**Parent**: V52, score `7129/20000` (tie contracted; no strict improvement required)

**Score**: `7129/20000` (ties V52 as contracted under Outcome C / Phase B-b)

**Axioms used**:
- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V53.hEq15_oracle_certified_hp_35645` (registered oracle, permitted)

**Gates**:

| Gate | Command | Result |
|------|---------|--------|
| 1 lake build | `lake build ProofRefinement.Korenblum.Candidates.V53` | PASS (8050 jobs, no errors) |
| 2 sorry grep | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V53.lean` | PASS (no matches) |
| 2 sorry grep (ThetaStep) | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V53/ThetaStep.lean` | PASS (no matches) |
| 3 evaluator | see reproduction command below | PASS (`status: PASS`, `score: 7129/20000`) |
| 4 parent score | tie contracted; 7129/20000 == 7129/20000 | N/A (no strict improvement required) |

**Failing gate**: none

**Structural advance**: `Candidates/V53/ThetaStep.lean` ships the first per-candidate
derived-theorem file in the workspace with all three contracted theorems
(`theta_step_raw`, `theta_step`, `theta_step_strict_less_than_one`) proved as
`theorem`s with no new axioms, no oracle, and no edits to `KorenblumPaper/` or
`Reduction.lean`. Axioms for ThetaStep are subset of `{propext, Classical.choice,
Quot.sound}` (seed only).

**Reproduction commands**:

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V53

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V53.lean
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V53/ThetaStep.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V53.lean
```
