# Verdict: sprint_011_bergman_parseval_identity

**Date**: 2026-05-07
**Evaluator**: claude-sonnet-4-6

## Contract

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_011_bergman_parseval_identity.md`

## Candidate

`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V11.lean`

New module:
`ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Proof/BergmanParseval.lean`

## Outcome

PASS

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1. lake build | `lake build ProofRefinement.Korenblum.Candidates.V11` | PASS (8038 jobs, warnings only) |
| 2. sorry scan | `grep -n 'sorry' Candidates/V11.lean` | PASS (no output) |
| 2. sorry scan | `grep -n 'sorry' Proof/BergmanParseval.lean` | PASS (no output) |
| 3. evaluator | `uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V11.lean` | PASS (score: 1777/5000) |
| 4. parent score comparison | n/a (scaffolding sprint; contract states score unchanged from V10 = 1777/5000) | N/A |

## Score

- V11 score: `1777/5000` (= 3554/10000 = 0.3554)
- V10 score: `1777/5000` (= 3554/10000 = 0.3554)
- No score improvement required (scaffolding-only sprint, per contract)

## Axioms used

- `propext` (seed)
- `Classical.choice` (seed)
- `Quot.sound` (seed)
- `ProofRefinement.Korenblum.Candidates.V11.hKorenblum_published_3554` (seed, allowed)

No new axioms beyond the permitted seed.

## BergmanParseval.lean content verified

- `cauchyPowerSeries_coeff_norm_radius_invariant`: present, is a `theorem`, no `sorry`
- `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`: present, is a `theorem`, no `sorry`, uses both `bergmanNormSq_radial_polar` and `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` (via `circleMeanSq_eq_tsum_canonical`)
- `bergmanNormSq_termwise_mono`: present, is a `theorem`, no `sorry`

V11 imports `ProofRefinement.Korenblum.Proof.BergmanParseval`, forcing it into V11's compile graph.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V11

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V11.lean
grep -n 'sorry' ProofRefinement/Korenblum/Proof/BergmanParseval.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V11.lean
```
