# Verdict: sprint_019_eq5_eq8_eq9_subinterval_branch1_derived_pointwise

**Date**: 2026-05-02
**Evaluator**: korenblum-refinement-evaluator

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_019_eq5_eq8_eq9_subinterval_branch1_derived_pointwise.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V19.lean`

## Outcome

**VERDICT_PASS**

## Gate Results

### Gate 1: `lake build`

PASS — `Build completed successfully (8049 jobs)`. No errors; only lint warnings.

Reproduction:
```
bash ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V19.lean
```

### Gate 2: `grep -n 'sorry' Candidates/V19.lean`

PASS — No `sorry` found.

Reproduction:
```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V19.lean
```

### Gate 3: Full evaluator run

PASS

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V19.lean
```

- score (maximize): **1777/5000**
- axioms_used: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V19.hEq15_seed_3554`
- compile: PASS
- type-check: PASS
- axiom audit: PASS
- workspace imports: PASS
- oracle audit: PASS
- status: **PASS**

### Gate 4: Score vs parent V18

PASS — V18 score: `1777/5000`; V19 score: `1777/5000`. V19 >= V18 as required by the sprint contract.

## Summary

All four gates passed. Sprint 019 ships the new generic theorem
`valid_of_eq5_eq8_eq9_subinterval_branch1` in `Proof/Reduction.lean` — the
workspace's first closing reducer that re-derives Wang's pointwise `(10)` from
`(5)+(8)+(9)` via `PaperAxioms.eq10_of_eq5_eq8_eq9` without consuming
`paper.eq10_branch1_pointwise`. V19 also materialises two side lemmas
(`v19_eq5_eq8_eq9_subinterval_branch1_compiles` and
`v19_branch1_window_witness_at_seed`) and discharges the sink theorem via
`valid_of_eq15`, preserving the score at `1777/5000`.
