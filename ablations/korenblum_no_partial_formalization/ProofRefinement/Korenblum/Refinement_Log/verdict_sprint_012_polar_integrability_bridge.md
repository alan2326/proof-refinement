# Verdict: sprint_012_polar_integrability_bridge

**Contract**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_012_polar_integrability_bridge.md
**Candidate**: ProofRefinement/Korenblum/Candidates/V12.lean
**Parent candidate**: V11 (score 1777/5000)
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1. lake build | `lake build ProofRefinement.Korenblum.Candidates.V12` | PASS (8039 jobs, no errors) |
| 2. sorry scan | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V12.lean` | PASS (no matches) |
| 3. evaluator | `uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V12.lean` | PASS |
| 4. score comparison | sprint contract does not require strict improvement; score unchanged (1777/5000 = 3554/10000) is expected | N/A |

## Evaluator detail

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.92s)
- type-check: PASS (6.67s)
- axiom scan: PASS (7.53s)
- axiom audit: PASS — only `propext`, `Classical.choice`, `Quot.sound`, `hKorenblum_published_3554`
- oracle audit: PASS
- score: 1777/5000 (unchanged from V11, as expected for this scaffolding sprint)
- evaluator status: PASS

## Acceptance criteria check

1. `lake build ProofRefinement.Korenblum.Candidates.V12` succeeds, no `sorry`, no unauthorized axioms. PASS.
2. Evaluator accepts V12 as well-formed. Score 3554/10000 unchanged from V11 — correctly reported. PASS.
3. `ProofRefinement/Korenblum/Proof/PolarIntegrability.lean` contains:
   - `polar_integrableOn_of_bergmanIntegrable` (theorem, no sorry, uses `Complex.lintegral_comp_polarCoord_symm`). PASS.
   - `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (theorem, no sorry). PASS.
4. V12 imports `ProofRefinement.Korenblum.Proof.PolarIntegrability` — module is in V12's compile graph. PASS.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V12

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V12.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V12.lean
```
