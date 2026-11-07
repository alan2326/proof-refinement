# Verdict: sprint_045_valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9

**Contract**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_045_valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window.md
**Candidate**: ProofRefinement/Korenblum/Candidates/V45.lean
**Parent**: Candidates/V44.lean (score 1777/5000)
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V45` | PASS (8049 jobs, warnings only) |
| 2. `grep -n 'sorry' Candidates/V45.lean` | PASS (no sorry) |
| 3. Evaluator run | PASS, score = 1777/5000 |
| 4. Parent score comparison | N/A (contract requires tie, not strict improvement) |

## Evaluator summary

- compile: PASS
- type-check: PASS
- axiom audit: PASS — axioms used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V45.hEq15_seed_3554}`
- oracle audit: PASS (no oracle entries)
- score: 1777/5000

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V45

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V45.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V45.lean
```

## Notes

The new closing reducer `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
was appended to `Proof/Reduction.lean` and is exercised in V45's two side lemmas
(`_compiles` and `_witness_at_seed`). The sink theorem `korenblum_constant_search`
is still discharged via `valid_of_eq15`, preserving the score at 1777/5000. No new
axioms or oracle entries were introduced.
