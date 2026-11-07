# Verdict: sprint_053

**Date**: 2026-05-02
**Evaluator**: korenblum-refinement-evaluator (claude-sonnet-4-6)

## Contract

`ProofRefinement/Korenblum/Sprint_Contracts/sprint_053_register_eq15_oracle_wrapper_at_seed.md`

## Candidate

`ProofRefinement/Korenblum/Candidates/V48.lean`

## Outcome

**VERDICT_FAIL**

## Failing gate

**Gate 3 — full evaluator run**

The evaluator exits with code 1. The oracle audit step reports:

```
oracle audit:  FAIL
  FAIL  oracle function `rigorous_scalar.certify_eq15_at_seed` not found: No module named 'mpmath'
```

The function `certify_eq15_at_seed` is defined in
`ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py` (line 952),
but the module cannot be imported because `rigorous_scalar.py` has a top-level
`import mpmath as mp` (line 7 of the file) and `mpmath` is not installed in
the uv environment used by the evaluator. The import failure is confirmed by:

```
env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 -c "import mpmath"
# ModuleNotFoundError: No module named 'mpmath'
```

All earlier gates passed:
- Gate 1 (`lake build ProofRefinement.Korenblum.Candidates.V48`): PASS — build succeeded (8049 jobs, exit 0).
- Gate 2 (`grep -n 'sorry' Candidates/V48.lean`): PASS — no sorry found.
- Gate 3 (evaluator): FAIL at oracle audit step.

## Notes

The prior evaluator run recorded in `log.jsonl` (timestamp 2026-05-02T22:59:08)
shows `pass: true`, `score: 1777/5000`, and `oracle_checks` with `ok: true`.
That run pre-dates or was conducted under a different Python environment
configuration than the one found during this evaluation session.

The contract requires all four gates to be run in order and stop on the first
failure. The oracle audit failure in the live gate-3 run is the definitive
result.

## Root cause

`mpmath` is absent from the uv environment. The `pyproject.toml` or
`uv.lock` for the evaluator does not include `mpmath` as a dependency, even
though `rigorous_scalar.py` unconditionally imports it at module level.

## Reproduction

```bash
# Gate 1
cd korenblum && lake build ProofRefinement.Korenblum.Candidates.V48

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V48.lean

# Gate 3 (fails)
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V48.lean

# Confirm missing dependency
env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 -c "import mpmath"
```
