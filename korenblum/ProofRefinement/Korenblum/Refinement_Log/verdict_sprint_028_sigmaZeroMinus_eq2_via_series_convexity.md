# Verdict: sprint_028_sigmaZeroMinus_eq2_via_series_convexity

**Outcome**: PASS

## Contract

`korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_028_sigmaZeroMinus_eq2_via_series_convexity.md`

## Candidate

`korenblum/ProofRefinement/Korenblum/Candidates/V28.lean`

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1: lake build | `lake build ProofRefinement.Korenblum.Candidates.V28` | PASS (8049 jobs, warnings only) |
| 2: sorry check | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V28.lean` | PASS (no matches) |
| 3: evaluator | `env UV_CACHE_DIR=... uv run Evaluator.py --file Candidates/V28.lean` | PASS |
| 4: score >= parent | V28 score 1777/5000 >= V27 score 1777/5000 | PASS (tie, contract requires >=) |

## Evaluator summary

- score (maximize): `1777/5000`
- axioms used: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V28.hEq15_seed_3554`
- import audit: PASS
- axiom audit: PASS
- oracle audit: PASS
- compile: PASS (9.01s)
- type-check: PASS (7.06s)
- axiom scan: PASS (8.33s)

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V28

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V28.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V28.lean
```
