# Verdict: sprint_024

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_024.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V19.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V19.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` matches in V19.lean |
| G3 (write scope) | PASS | Changed files: V19.lean (new candidate), joint_phi_phip_invD2.py (contract-named), uzz_phi_sq.py (contract-named), Bulletin.md (always-allowed), Experience.md (always-allowed), Scratch/sprint_024_planner_n8192.py (always-allowed); no forbidden paths |
| G4 (no new axioms) | PASS | Axiom set identical to V18 parent: same 12 seed axioms + 2 oracle axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle); no new non-oracle axioms introduced |
| G5 (per-cand evaluator) | PASS | exit 0, `pass: true`; both oracle reverifications pass: h_joint_phi_phip_invD2_oracle declared=3/125000 >= oracle 3/125000; h_uzz_phi_sq_oracle declared=3/200000 >= oracle 3/200000 |
| G6 (score) | PASS | Cr_val = 1/31500 < 1/11700 (V18 parent); 2.692x improvement |

## REPRODUCED-WITH

```
lake commit: d49ac1a3eefc8ce9cc2c47075d72291312009743
log entry:   {"timestamp":"2026-04-30T10:27:14Z","lemma":"lemma_5_4","candidate":"Candidates/V19.lean","candidate_sha256":"1713faa7d3df3c8b4f7dd3bae40c4e9b975e25062e226c8aa9ac106a93b9bb58","parent":"Candidates/V18.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":31500,"approx":3.1746031746031745e-05},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"3/125000","uzz_phi_sq_val":"3/200000","Cr_val":"1/31500"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"3/125000","oracle_bound":"3/125000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"3/200000","oracle_bound":"3/200000","status":"pass"}],"wall_seconds":{"compile":4.18,"axiom_audit":7.29,"oracle":0.1}}
```
