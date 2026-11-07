# Verdict: sprint_022_disk_bound_via_eq2_eq3_eq4_branch2_collapse

**Date**: 2026-05-02

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_022_disk_bound_via_eq2_eq3_eq4_branch2_collapse.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V22.lean`

## Outcome

PASS

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V22` | PASS (8049 jobs, no errors) |
| 2. `grep -n 'sorry' Candidates/V22.lean` | PASS (no matches) |
| 3. Evaluator `Evaluator.py --file Candidates/V22.lean` | PASS |
| 4. Score >= parent V21 score (`1777/5000`) | PASS (tied at `1777/5000`) |

## Score

`1777/5000` (ties parent V21 as expected; sink theorem still discharged via `valid_of_eq15`)

## Axiom audit

Exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V22.hEq15_seed_3554}` — matches V21's axiom set.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V22

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V22.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V22.lean
```
