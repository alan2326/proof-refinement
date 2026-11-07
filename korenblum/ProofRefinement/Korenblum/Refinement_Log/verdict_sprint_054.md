# Verdict: sprint_054

**Contract**: ProofRefinement/Korenblum/Sprint_Contracts/sprint_054_pin_python_deps_for_oracle_evaluator.md
**Candidate**: ProofRefinement/Korenblum/Candidates/V48.lean
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1 | `lake build ProofRefinement.Korenblum.Candidates.V48` | PASS (8049 jobs, no errors) |
| 2 | `grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V48.lean` | PASS (no matches) |
| 3 | `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V48.lean` | PASS |
| 4 | Score comparison (parent V47 ties; no strict improvement required by contract) | N/A |

## Gate 3 detail

- workspace imports: PASS
- import audit: PASS
- compile: PASS (9.73s)
- type-check: PASS (12.56s)
- axiom scan: PASS (14.60s)
- axiom audit: PASS — axioms_used = {propext, Classical.choice, Quot.sound, hEq15_oracle_certified_3554}; no hEq15_seed_3554 present
- oracle audit: PASS — `hEq15_oracle_certified_3554: oracle=1 declared=1`
- score (maximize): 1777/5000
- status: PASS

## Score

**1777/5000** (ties V47; the deliverable is the trust-surface change, not a score improvement)

## Log entry

The newest log.jsonl row (timestamp 2026-05-02T23:14:06.743197+00:00) records:
- `pass: true`
- `score: "1777/5000"`
- `axioms_used` contains `ProofRefinement.Korenblum.Candidates.V48.hEq15_oracle_certified_3554` (kind: seed)
- `axioms_used` does NOT contain any entry ending in `hEq15_seed_3554`
- `oracle_checks[0]`: axiom=hEq15_oracle_certified_3554, bound_field=eq15_lower_bound, oracle_bound="1", declared="1", ok=true

## Reproduction

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V48

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V48.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V48.lean
```

## Notes

Sprint 054 fixed sprint 053's gate-3 failure by adding a repo-root
`korenblum/pyproject.toml` pinning `mpmath>=1.4` and
`python-flint>=0.8`. The Lean candidate (V48.lean) was unchanged from
sprint 053. The pyproject.toml uses `[tool.uv] package = false` so uv
treats it as a dependency-only manifest. With mpmath and flint available,
the registered oracle `rigorous_scalar.certify_eq15_at_seed` now invokes
successfully, recording oracle_bound=1 against declared=1, and
axioms_used switches from hEq15_seed_3554 (sprint 052 and prior) to
hEq15_oracle_certified_3554 (sprint 053/054).
