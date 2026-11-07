# Verdict: sprint_005

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_005.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V3.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V3.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | grep found no `sorry` occurrences |
| G3 (write scope) | PASS | Changed files: V3.lean (new candidate), Experience.md (always-allowed), Bulletin.md (always-allowed) |
| G4 (no new axioms) | PASS | Axiom set identical to parent V2: 3 Lean primitives + 12 trusted analytic seeds + h_M_oracle + h_oracle_domain_contains_image |
| G5 (per-cand evaluator) | PASS | `status: ok`, `score.approx = 1451520000.0`, oracle h_M_oracle passed (declared 432 >= oracle 431.8113) |
| G6 (score) | PASS | new=1451520000.0 < prev=9560055559329.883 (6586x reduction; well below 1.5e9 target) |

## REPRODUCED-WITH

```
lake commit: bf0dfbce11e9750a682cdf03bfacbf4d633b98e4
log entry:   {"timestamp":"2026-04-30T03:20:34Z","lemma":"lemma_5_4","candidate":"Candidates/V3.lean","candidate_sha256":"2a32e250d7f943df0cc95096e33b9efea88b2fbdff353f147fda3fb1de11fa99","parent":"Candidates/V2.lean","status":"ok","score_field":"Cr_val","score":{"numer":1451520000,"denom":1,"approx":1451520000.0},"def_vals":{"M_val":"432/1","delta_val":"163/1000","B_val":"223/200","Cr_val":"1451520000/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"432/1","oracle_bound":"4318113/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":4.92,"axiom_audit":5.91,"oracle":0.07}}
```
