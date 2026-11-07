# Verdict: sprint_021

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_021.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V16.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V16.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` occurrences found |
| G3 (write scope) | PASS | Changed files: V16.lean (new, contract-named), joint_phi_phip_invD2.py (contract-named), Bulletin.md (always-allowed), Scratch/sprint_021_*.py (always-allowed), Experience.md (always-allowed); no forbidden files touched |
| G4 (no new axioms) | PASS | V16 axiom set is identical to V15: same 3 primitives + 11 F_inv_paper seeds + h_oracle_domain_contains_image + 2 oracle axioms; no new non-oracle axioms |
| G5 (per-cand evaluator) | PASS | `Evaluator.py --file V16.lean` exits 0; pass=true; both oracles verified: h_joint_phi_phip_invD2_oracle declared=1/5000 >= oracle 1/5000, h_uzz_phi_sq_oracle declared=153/1000000 >= oracle 153/1000000 |
| G6 (score) | PASS | Cr_val=1/3500 < 1/2600 (prev); 1*2600=2600 < 3500; improvement factor ~1.346x |

## REPRODUCED-WITH

```
lake commit: 27ffcbc20df5fef18e4f6cdd294c79db81c65ad3
log entry:   {"timestamp":"2026-04-30T09:48:33Z","lemma":"lemma_5_4","candidate":"Candidates/V16.lean","candidate_sha256":"405862fd7710b0cd630a8b27a433494a76ff304ba4c298e383c2bd09bdf451b2","parent":"Candidates/V15.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":3500,"approx":0.00028571428571428574},...}
```
