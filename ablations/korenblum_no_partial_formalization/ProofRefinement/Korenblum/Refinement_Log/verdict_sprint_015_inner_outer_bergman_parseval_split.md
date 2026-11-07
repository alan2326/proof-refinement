# Verdict: sprint_015_inner_outer_bergman_parseval_split

**Contract path**: `ProofRefinement/Korenblum/Sprint_Contracts/sprint_015_inner_outer_bergman_parseval_split.md`

**Candidate path**: `ProofRefinement/Korenblum/Candidates/V15.lean`

**New file**: `ProofRefinement/Korenblum/Proof/AnnulusBergmanParseval.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V15`

PASS. Build completed successfully (8043 jobs). Only linter warnings (unused
variables); no errors.

Reproduction:
```bash
lake build ProofRefinement.Korenblum.Candidates.V15
```

### Gate 2: `grep -n 'sorry' <candidate>`

PASS. No `sorry` found in `Candidates/V15.lean` or
`Proof/AnnulusBergmanParseval.lean`.

Reproduction:
```bash
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V15.lean \
  ProofRefinement/Korenblum/Proof/AnnulusBergmanParseval.lean
```

### Gate 3: Evaluator

PASS. Full evaluator output:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.05s)
- type-check: PASS (5.63s)
- axiom scan: PASS (6.62s)
- axiom audit: PASS (axioms: `propext`, `Classical.choice`, `Quot.sound`,
  `hKorenblum_published_3554` — no forbidden axioms)
- score (maximize): `1777/5000` (= 3554/10000, unchanged from V14 as expected)
- status: PASS

Reproduction:
```bash
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V15.lean
```

### Gate 4: Parent score comparison

Not enforced. The sprint contract explicitly states the score is unchanged
from V14 (`3554/10000`) and that this is expected — the sprint is
scaffolding-only, not a c-push. Both V14 and V15 score `1777/5000`.

---

## Four headline theorems confirmed present

`ProofRefinement/Korenblum/Proof/AnnulusBergmanParseval.lean` (1046 lines)
contains all four required theorems, each a genuine `theorem` with no
`sorry`:

1. `outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries` (line 409)
2. `innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries` (line 558)
3. `outerAnnulus_bergmanNormSq_termwise_mono` (line 718)
4. `innerDisk_bergmanNormSq_termwise_mono` (line 868)

All four proofs genuinely call `outerAnnulus_norm_sq_polar` /
`innerDisk_norm_sq_polar` (sprint 003), `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
(sprint 010), and `cauchyPowerSeries_coeff_norm_radius_invariant` (sprint 011).

`AnnulusBergmanParseval` is imported in `Candidates/V15.lean` (line 18),
forcing it into V15's compile graph.
