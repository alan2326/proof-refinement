# Verdict: sprint_023_branch2_closing_reducer_via_eq2_eq3_eq4_collapse

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_023_branch2_closing_reducer_via_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window.md`

**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V23.lean`

**Outcome**: PASS

**Failing gate**: none

---

## Gate results

### Gate 1: lake build

```
lake build ProofRefinement.Korenblum.Candidates.V23
```

Result: PASS — "Build completed successfully (8049 jobs)". Warnings only (linter style), no errors.

### Gate 2: grep sorry

```
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V23.lean
```

Result: PASS — no matches.

### Gate 3: evaluator

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file korenblum/ProofRefinement/Korenblum/Candidates/V23.lean
```

Result: PASS

- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.75s)
- type-check: PASS (6.67s)
- axiom scan: PASS (7.62s)
- axiom audit: PASS (seed axioms only: propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V23.hEq15_seed_3554)
- oracle audit: PASS
- score: **1777/5000**
- status: PASS

### Gate 4: parent score comparison

Parent candidate: `V22`, score from log: `1777/5000`.
V23 score: `1777/5000`.
Contract requires V23 >= V22. Satisfied (equal).

---

## Reproduction commands

```bash
# Gate 1
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V23

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V23.lean

# Gate 3
cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V23.lean
```
