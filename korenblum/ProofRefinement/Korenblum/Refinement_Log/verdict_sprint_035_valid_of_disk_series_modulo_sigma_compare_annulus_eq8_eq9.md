# Verdict: sprint_035_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9

**Outcome: PASS**

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_035_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V35.lean`

## Gate results

| Gate | Result |
|------|--------|
| 1. `lake build ProofRefinement.Korenblum.Candidates.V35` | PASS |
| 2. `grep -n 'sorry' Candidates/V35.lean` | PASS (no matches) |
| 3. Evaluator run | PASS |
| 4. Parent score comparison (V34 = 1777/5000, V35 = 1777/5000, requirement ≥) | PASS |

## Evaluator summary

- score: `1777/5000`
- axioms_used: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V35.hEq15_seed_3554`
- import audit: PASS
- oracle audit: PASS
- compile: PASS (8.65s)
- type-check: PASS (6.39s)
- axiom scan: PASS (7.74s)

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V35

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V35.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V35.lean
```

## Notes

V35 ships `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window` in `Proof/Reduction.lean` — the workspace's first `valid_of_*` closing reducer with a paper-axiom-free disk-side proof body (modulo the explicit `hSigmaCmp : sigmaPlus a b c ≤ sigmaMinus a b c` witness cell). The sink theorem `korenblum_constant_search` is discharged via `valid_of_eq15` (same as V0–V34), preserving the score at `1777/5000 = 0.3554`. No new free-floating axioms; no oracle entries.
