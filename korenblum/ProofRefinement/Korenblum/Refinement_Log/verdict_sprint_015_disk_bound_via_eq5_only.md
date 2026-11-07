# Verdict: sprint_015_disk_bound_via_eq5_only

**Outcome: PASS**

## Contract

- Contract path: `korenblum/ProofRefinement/Korenblum/Sprint_Contracts/sprint_015_disk_bound_via_eq5_only.md`
- Candidate path: `korenblum/ProofRefinement/Korenblum/Candidates/V15.lean`
- Parent candidate: V14 (score 1777/5000)

## Gate results

| Gate | Result | Details |
|------|--------|---------|
| 1. `lake build` | PASS | `Build completed successfully (8049 jobs)` — warnings only, no errors |
| 2. `grep -n 'sorry'` | PASS | No `sorry` found in V15.lean |
| 3. Evaluator run | PASS | `status: PASS`, `score (maximize): 1777/5000` |
| 4. Score vs parent | PASS | V15 = 1777/5000 >= V14 = 1777/5000 (contract requires `>=`) |

## Evaluator summary

```
candidate:     ProofRefinement/Korenblum/Candidates/V15.lean
namespace:     ProofRefinement.Korenblum.Candidates.V15
parent:        V14
workspace imports: PASS
import audit:  PASS
compile:       PASS (8.77s)
type-check:    PASS (6.69s)
axiom scan:    PASS (7.72s)
axiom audit:   PASS
  seed  propext
  seed  Classical.choice
  seed  Quot.sound
  seed  ProofRefinement.Korenblum.Candidates.V15.hEq15_seed_3554
oracle audit:  PASS
score (maximize): 1777/5000
status: PASS
```

## Reproduction commands

```bash
# Gate 1: lake build
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V15.lean

# Gate 2: sorry check
grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V15.lean

# Gate 3: evaluator
bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V15.lean
```

## Notes

- `c_value = 3554/10000` unchanged from V0-V14.
- Axiom set is exactly `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V15.hEq15_seed_3554}` — no new free-floating axioms.
- The new theorem `diskExcess_upper_bound_via_eq5` is present in `Proof/Reduction.lean` and both side lemmas (`v15_diskExcess_upper_bound_via_eq5_compiles`, `v15_branch_split_witness_at_seed`) are present in V15.lean.
- Score is 1777/5000 = 0.3554, identical to V14 (this sprint is structural, not a numerical push).
