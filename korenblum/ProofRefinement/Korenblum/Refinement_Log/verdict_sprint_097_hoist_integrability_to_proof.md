# Verdict: sprint_097_hoist_integrability_to_proof

**Contract path**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_097_hoist_integrability_to_proof.md
**Candidate path**: ProofRefinement/Korenblum/Candidates/V68.lean
**Outcome**: PASS
**Failing gate**: none

## Gate results

**Gate 1 — lake build**
Command: `lake build ProofRefinement.Korenblum.Candidates.V68`
Result: PASS — "Build completed successfully (8055 jobs)". Warnings only (linter style, unused variables); no errors.

**Gate 2 — sorry scan**
Command: `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean`
Result: PASS — no matches.

**Gate 3 — evaluator**
Command: `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V68.lean`
Result: PASS
- workspace imports: PASS
- import audit: PASS
- compile: PASS (68.53s)
- type-check: PASS (54.98s)
- axiom scan: PASS (43.82s)
- axiom audit: PASS
- oracle audit: PASS
- score (maximize): 71313/200000
- status: PASS

**Gate 4 — score equality check (score-neutral hoist)**
Required score: 71313/200000 (exactly equal, not strictly greater).
Observed score: 71313/200000.
Result: PASS — score is byte-for-byte identical to the pre-hoist score.

Axioms_used set (6 entries, identical to pre-hoist specification):
1. `propext`
2. `Classical.choice`
3. `Quot.sound`
4. `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`
5. `ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68`
6. `ProofRefinement.Korenblum.Candidates.V68.hH2_v68`

No new axioms introduced. No old axioms removed. Audit envelope preserved conjunct-for-conjunct.

V68 imports `ProofRefinement.Korenblum.Proof.Integrability` (hoisted location) and does not import `ProofRefinement.Korenblum.Candidates.V63.Integrability` (pre-hoist location), confirming the import rewrite is complete.

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V68

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V68.lean

# Gate 3 + 4
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V68.lean
```
