# Verdict: sprint_021_decoupled_disk_anchor_eq5_annulus_eq8_eq9

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_021_decoupled_disk_anchor_eq5_annulus_eq8_eq9.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V21.lean`
**Parent**: `Candidates/V20.lean` (score: `1777/5000`)
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V21` | PASS |
| 2. `grep -n 'sorry' Candidates/V21.lean` | PASS (no matches) |
| 3. Evaluator run | PASS (score: `1777/5000`) |
| 4. Score >= parent (`1777/5000 >= 1777/5000`) | PASS |

## Score

`1777/5000` (same as parent V20; no regression)

## Axioms used

- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V21.hEq15_seed_3554` (seed, listed in `lemma.toml:[seed_axioms]`)

## Reproduction commands

```bash
cd korenblum
lake build ProofRefinement.Korenblum.Candidates.V21
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V21.lean
env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V21.lean
```

## Notes

The new generic theorem `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`
(in `Proof/Reduction.lean`) compiles cleanly. The two sprint-021 side lemmas
`v21_decoupled_anchor_compiles` and `v21_decoupled_anchor_witness_at_seed`
both type-check without `sorry`. The sink theorem `korenblum_constant_search`
is discharged via `valid_of_eq15` as specified, preserving the score at
`1777/5000`. No unapproved axioms were introduced.
