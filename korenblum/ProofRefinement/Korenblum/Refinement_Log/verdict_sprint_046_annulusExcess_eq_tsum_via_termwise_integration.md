# Verdict: sprint_046_annulusExcess_eq_tsum_via_termwise_integration

**Contract**: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_046_annulusExcess_eq_tsum_via_termwise_integration.md`
**Candidate**: `korenblum/ProofRefinement/Korenblum/Candidates/V46.lean`
**Parent candidate**: `Candidates/V45.lean` (score: 1777/5000)
**Evaluated**: 2026-05-02

## Outcome: PASS

## Gate results

| Gate | Result | Detail |
|------|--------|--------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)` — warnings only, no errors |
| 2. `grep -n 'sorry'` | PASS | No `sorry` found in V46.lean |
| 3. Evaluator | PASS | `status: PASS`, `score (maximize): 1777/5000` |
| 4. Parent score comparison | PASS | Contract requires score tie (1777/5000 = 1777/5000); no strict improvement required |

## Evaluator summary

- compile: PASS (8.53s)
- type-check: PASS (11.66s)
- axiom scan: PASS (13.74s)
- axiom audit: PASS — `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V46.hEq15_seed_3554}`
- oracle audit: PASS
- score: `1777/5000`

## Reproduction commands

```bash
# Gate 1
lake build ProofRefinement.Korenblum.Candidates.V46

# Gate 2
grep -n 'sorry' ProofRefinement/Korenblum/Candidates/V46.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache \
  uv run ProofRefinement/Korenblum/Evaluator.py \
  --file ProofRefinement/Korenblum/Candidates/V46.lean
```

## STATUS=VERDICT_PASS
