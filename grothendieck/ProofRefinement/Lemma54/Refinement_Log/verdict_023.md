# Verdict: sprint_023

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_023.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V18.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V18.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` matches in V18.lean |
| G3 (write scope) | PASS | Changed files: Candidates/V18.lean (new candidate), Numerical_Library/joint_phi_phip_invD2.py (contract-named), Numerical_Library/uzz_phi_sq.py (contract-named), Bulletin.md (always-allowed), Experience.md (always-allowed); no forbidden paths touched |
| G4 (no new axioms) | PASS | V18 axiom set identical to V17: same 12 seed axioms, same 2 oracle axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle); no new non-oracle axioms introduced |
| G5 (per-cand evaluator) | PASS | Evaluator exit 0, `pass: true`; both oracle axioms verified: joint_phi_phip_invD2_val declared 63/1000000 >= oracle 63/1000000, uzz_phi_sq_val declared 11/250000 >= oracle 11/250000 |
| G6 (score) | PASS | Cr_val = 1/11700 ≈ 8.547e-05 < 1/3500 ≈ 2.857e-04 (parent V17); 3.34x improvement |

## REPRODUCED-WITH

```
lake commit: be86582afba6c9346ffe18801238481e17ba9ff5
log entry:   {"timestamp":"2026-04-30T10:16:32Z","lemma":"lemma_5_4","candidate":"Candidates/V18.lean","candidate_sha256":"5cb57fa9ad4da1fa83792a48e849b645f07030446d8e161d02941f42cf0170dd","parent":"Candidates/V17.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":11700,"approx":8.547008547008547e-05},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"63/1000000","uzz_phi_sq_val":"11/250000","Cr_val":"1/11700"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"63/1000000","oracle_bound":"63/1000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"11/250000","oracle_bound":"11/250000","status":"pass"}],"wall_seconds":{"compile":4.05,"axiom_audit":6.71,"oracle":0.07}}
```
