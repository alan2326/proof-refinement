# Verdict: sprint_014_inner_radial_dominance_to_validKorenblumBound

**Contract path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Sprint_Contracts/sprint_014_inner_radial_dominance_to_validKorenblumBound.md`

**Candidate path**: `ablations/korenblum_no_partial_formalization/ProofRefinement/Korenblum/Candidates/V14.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1: `lake build ProofRefinement.Korenblum.Candidates.V14`

PASS. Build completed successfully (8042 jobs). Warnings only (unused variables in earlier modules), no errors.

### Gate 2: `grep -n 'sorry' Candidates/V14.lean`

PASS. No `sorry` found.

### Gate 3: Evaluator

PASS. Full evaluator output:

```
compile:       PASS (8.17s)
type-check:    PASS (5.75s)
axiom scan:    PASS (6.89s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V14.hKorenblum_published_3554
oracle audit:  PASS
score (maximize): 1777/5000
status: PASS
```

### Gate 4: Parent score comparison

Not enforced. The contract explicitly states the score `c_value = 3554/10000` is unchanged from V13 (1777/5000), and this is expected — the sprint is scaffolding-only, not a c-push. V13's score is also 1777/5000. The contract requires no strict improvement for this sprint.

---

## Additional acceptance criteria checks

- `Proof/InnerRadialReduction.lean` exists and contains `theorem validKorenblumBound_of_inner_radial_dominance` with conclusion `ValidKorenblumBound c`, no `sorry`, no new axioms. The proof calls `validKorenblum_of_inner_outer_dom_of_analyticOn` exactly once. PASS.
- `Proof/InnerRadialReduction` is imported by `Candidates/V14.lean` and confirmed in the evaluator's workspace-imports audit. PASS.
- `Proposals/proposal_001_replace_seed_with_inner_radial_dominance.md` exists with status `pending`. PASS.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V14

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V14.lean

# Gate 3
env UV_CACHE_DIR=ablations/korenblum_no_partial_formalization/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V14.lean
```
