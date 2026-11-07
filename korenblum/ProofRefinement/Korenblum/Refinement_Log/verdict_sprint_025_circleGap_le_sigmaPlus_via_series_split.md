# Verdict: sprint_025_circleGap_le_sigmaPlus_via_series_split

**Evaluated**: 2026-05-02

## Contract

- Contract path: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_025_circleGap_le_sigmaPlus_via_series_split.md`
- Candidate path: `korenblum/ProofRefinement/Korenblum/Candidates/V25.lean`
- Parent candidate: `Candidates/V24.lean` (score = 1777/5000)

## Outcome

**VERDICT_PASS**

## Gate Results

### Gate 1 — lake build

PASS. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V25.lean` completed with `Build completed successfully (8049 jobs)`. Warnings only (linting style); no errors.

### Gate 2 — sorry check

PASS. `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V25.lean` returned no matches.

### Gate 3 — full evaluator

PASS.

```
candidate:     ProofRefinement/Korenblum/Candidates/V25.lean
namespace:     ProofRefinement.Korenblum.Candidates.V25
parent:        V24
workspace imports: PASS
import audit:  PASS
compile:       PASS (8.79s)
type-check:    PASS (6.67s)
axiom scan:    PASS (7.57s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V25.hEq15_seed_3554
oracle audit:  PASS
score (maximize): 1777/5000
status: PASS
```

### Gate 4 — score comparison against parent

PASS. V25 score `1777/5000 >= V24 score `1777/5000` (equal, satisfying `>=` requirement from contract).

## Score

`1777/5000`

## Failing gate

None.

## Reproduction commands

```bash
# Gate 1
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V25.lean

# Gate 2
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V25.lean

# Gate 3
env UV_CACHE_DIR=korenblum/.uv-cache uv run korenblum/ProofRefinement/Korenblum/Evaluator.py --file korenblum/ProofRefinement/Korenblum/Candidates/V25.lean
```
