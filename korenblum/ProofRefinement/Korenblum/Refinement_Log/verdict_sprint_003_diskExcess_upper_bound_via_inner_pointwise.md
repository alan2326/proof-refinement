# Verdict: sprint_003_diskExcess_upper_bound_via_inner_pointwise

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_003_diskExcess_upper_bound_via_inner_pointwise.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V3.lean`
**Parent candidate**: `Candidates/V2.lean` (score 1777/5000)
**Evaluated**: 2026-05-02

## Outcome

**VERDICT_PASS**

All four evaluator gates passed. All eight acceptance criteria satisfied.

## Gate results

| Gate | Result | Detail |
|------|--------|--------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)` |
| 2. `grep -n 'sorry'` | PASS | No matches |
| 3. Evaluator run | PASS | `score = 1777/5000`, `status: PASS` |
| 4. Score >= parent | PASS | 1777/5000 >= 1777/5000 (equal, satisfies >=) |

## Evaluator detail

- `score (maximize)`: `1777/5000`
- `axioms_used`: `propext`, `Classical.choice`, `Quot.sound`, `ProofRefinement.Korenblum.Candidates.V3.hEq15_seed_3554`
- No forbidden axioms. No oracle entries. Import audit: PASS.

## Acceptance criteria (contract items 1-8)

1. `lake build` of V3.lean: PASS
2. Evaluator run: PASS
3. Score `1777/5000` (= V2): PASS (contract says `>= V2`)
4. Axiom set exactly `{propext, Classical.choice, Quot.sound, hEq15_seed_3554}`: PASS
5. Forbidden terms outside `diskExcess_upper_bound_of_eq2_eq3_eq4` body only: PASS (body at lines 316-435 of Reduction.lean contains none of the forbidden substrings)
6. `diskExcess_upper_bound_of_eq2_eq3_eq4` invoked in V3.lean: PASS (line 55)
7. `diskExcess_upper_bound_of_eq2_eq3_eq4` has exactly one definition site in Reduction.lean: PASS (line 303)
8. `circleGap_inner_bound_of_eq2_eq3_eq4` has >= 2 matches in Reduction.lean: PASS (lines 191, 338)

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V3

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V3.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V3.lean
```
