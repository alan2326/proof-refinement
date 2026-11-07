# Verdict: sprint_036_circleGap_inner_bound_via_series_only_modulo_sigma_compare

**Outcome**: VERDICT_PASS

## Metadata

- Contract: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_036_circleGap_inner_bound_via_series_only_modulo_sigma_compare.md`
- Candidate: `korenblum/ProofRefinement/Korenblum/Candidates/V36.lean`
- Parent candidate: `Candidates/V35.lean` (score = 1777/5000)
- Score: 1777/5000 (satisfies >= parent score requirement)
- Axioms used: propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V36.hEq15_seed_3554

## Gate results

| Gate | Result | Detail |
|------|--------|--------|
| 1. lake build | PASS | `Build completed successfully (8049 jobs)` |
| 2. grep sorry | PASS | No occurrences found in V36.lean |
| 3. Evaluator | PASS | `status: PASS`, `score (maximize): 1777/5000` |
| 4. Parent score check | PASS | V36 score (1777/5000) >= V35 score (1777/5000) |

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V36

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V36.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V36.lean
```

## Notes

The sprint ships the workspace's first non-integrated, paper-axiom-free two-Z
upper bound on `circleGap a b r` as
`circleGap_inner_bound_via_series_only_modulo_sigma_compare` appended to
`Proof/Reduction.lean`. Two side lemmas in V36.lean materialise the theorem:
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_compiles` and
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15`, preserving the score at 1777/5000.
