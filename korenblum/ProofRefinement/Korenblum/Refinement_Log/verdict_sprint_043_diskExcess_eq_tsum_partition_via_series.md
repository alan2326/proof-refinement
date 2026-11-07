# Verdict: sprint_043_diskExcess_eq_tsum_partition_via_series

**Date**: 2026-05-02
**Evaluator**: korenblum-refinement-evaluator

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_043_diskExcess_eq_tsum_partition_via_series.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V43.lean`

## Outcome

**VERDICT_PASS**

All four gates passed.

## Gate Results

| Gate | Result | Detail |
|------|--------|--------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)` — warnings only, no errors |
| 2. `grep -n 'sorry'` | PASS | No `sorry` found in candidate |
| 3. Evaluator | PASS | `score = 1777/5000`, `status: PASS` |
| 4. Score vs parent | N/A | Contract requires tie at `1777/5000`; V43 scores `1777/5000` — no regression |

## Evaluator Summary

```
compile:      PASS (8.86s)
type-check:   PASS (6.71s)
axiom scan:   PASS (7.87s)
axiom audit:  PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V43.hEq15_seed_3554
oracle audit: PASS
score (maximize): 1777/5000
status: PASS
```

## Reproduction Commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V43

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V43.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V43.lean
```

## Notes

- New generic theorem `diskExcess_eq_tsum_partition_via_series` appended to
  `Proof/Reduction.lean` at line 6693 (total 6831 lines).
- Two side lemmas in V43: `v43_diskExcess_eq_tsum_partition_compiles` and
  `v43_diskExcess_eq_tsum_partition_recovers_sprint042_at_seed`.
- Sink theorem discharged via `valid_of_eq15` (unchanged from V42).
- No new axioms beyond the V0 seed set.
- No `sorry`.
