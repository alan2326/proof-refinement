# Verdict: sprint_001_eq12_eq13_bypass_reduction

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_001_eq12_eq13_bypass_reduction.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V1.lean`
**Outcome**: PASS
**Failing gate**: none

## Gate results

| Gate | Command | Result |
|------|---------|--------|
| 1 lake build | `bash ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V1.lean` | PASS (8049 jobs, no errors) |
| 2 no sorry | `grep -n 'sorry' .../Candidates/V1.lean` | PASS (no matches) |
| 3 evaluator | `env UV_CACHE_DIR=... uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V1.lean` | PASS |
| 4 score >= parent | V1 score 1777/5000 >= V0 score 1777/5000 | PASS |

## Evaluator output summary

- score (maximize): `1777/5000`
- axioms_used: `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V1.hEq15_seed_3554}`
- workspace imports: PASS
- import audit: PASS
- compile: PASS (8.84s)
- type-check: PASS (6.54s)
- axiom scan: PASS (7.75s)
- oracle audit: PASS

## Acceptance criteria check

1. lake build succeeded.
2. Evaluator passed.
3. Score = 1777/5000 (matches expected value from contract).
4. axioms_used exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V1.hEq15_seed_3554}` — no new free-floating axioms.
5. `grep -n 'eq14_combined' .../Proof/Reduction.lean` shows substring only at line 73 (inside `eq15_implies_disk_le_annulus`) and in comments; `valid_of_eq12_eq13` proof body (lines 113-183) does not mention `eq14_combined`.
6. `grep -n 'valid_of_eq12_eq13' .../Candidates/V1.lean` returns matches at lines 29, 35, and 45 — V1 invokes the new bridge inside `v1_eq12_eq13_chain_compiles`.

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V1.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V1.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run korenblum/ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V1.lean
```

## STATUS=VERDICT_PASS
