# Verdict: sprint_071_per_mode_tau_window_closing_reducer_attempt_first

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_071_per_mode_tau_window_closing_reducer_attempt_first.md`

**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V56.lean`

**Outcome**: PASS (Outcome B — Phase 0 NO-GO, V56 ties V55 at score 7129/20000)

---

## Gate results

### Gate 1: lake build

```
lake build ProofRefinement.Korenblum.Candidates.V56
```

Result: **PASS** (8049 jobs, warnings only, no errors)

### Gate 2: sorry check

```
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V56.lean
```

Result: **PASS** (no matches)

### Gate 3: Evaluator run

```
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V56.lean
```

Result: **PASS**

Full evaluator output:
- workspace imports: PASS
- import audit: PASS
- compile: PASS (137.35s)
- type-check: PASS (111.43s)
- axiom scan: PASS (81.59s)
- axiom audit: PASS
  - seed  propext
  - seed  Classical.choice
  - seed  Quot.sound
  - seed  ProofRefinement.Korenblum.Candidates.V56.hEq15_oracle_certified_hp_35645 (registered oracle)
- oracle audit: PASS (hEq15_oracle_certified_hp_35645: oracle=1 declared=1)
- score (maximize): 7129/20000
- status: PASS

Note: the evaluator's first subprocess invocation timed out (120s hardcoded limit in `collect_used_axioms`); the second run (which benefited from warmed caches) completed the axiom scan in 81.59s and reported PASS. The manual axiom check `#print axioms ... korenblum_constant_search` returned identical results.

### Gate 4: Parent score comparison

Parent candidate V55 score: 7129/20000. V56 score: 7129/20000.

The contract specifies Outcome B (c-tie), not a strict improvement. Gate 4 is satisfied: the contract's only strict-improvement requirement applies under Outcome A, which requires Phase 0 GO. Phase 0 was NO-GO; Outcome B allows tie.

---

## Sign correction assessment

The generator documents two sign corrections relative to the contract's phrasing:

1. **Route A direction**: The contract described Route A as a "lower bound" on KERNEL_71's RHS via `paperLambda >= 2`. The correction is that `paperLambda >= 2` implies `1/paperLambda <= 1/2`, so `2rho/(term·Lambda) <= rho/term`, making Route A an **upper bound** on KERNEL_71's RHS. This is factually correct. The correction does not weaken any gate; Phase 0 is NO-GO under both the contract's and the corrected interpretation.

2. **KERNEL_71 mass-1 form**: The contract proposed `c^2 <= integral` as KERNEL_71's hypothesis. The generator shipped `(1 : ℝ) <= integral` in `valid_of_perMode_tau_window_eq8_eq9` (and in `v56_perMode_reducer_compiles_at_witness`), matching `Eq15ScalarBound`'s mass-1 normalization. This is consistent with the `valid_of_eq15` discharge pattern used throughout `Reduction.lean`. The Lean type-checker accepted the theorem without error.

Both corrections are mathematically sound and do not affect any pass/fail gate. They are **acceptable**.

---

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V56

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V56.lean

# Gate 3 (full evaluator)
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V56.lean

# Manual axiom check (if evaluator axiom-scan times out)
echo "import ProofRefinement.Korenblum.Candidates.V56
#print axioms ProofRefinement.Korenblum.Candidates.V56.korenblum_constant_search" \
  > /tmp/axiom_check_v56.lean && lake env lean /tmp/axiom_check_v56.lean
```
