# Verdict: sprint_026

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_026.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V21.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V21.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` matches in V21.lean |
| G3 (write scope) | PASS | Changed files: V21.lean (new candidate), joint_phi_phip_invD2.py (contract-named), uzz_phi_sq.py (contract-named), Bulletin.md (always-allowed), Experience.md (always-allowed), Scratch/* (always-allowed); no forbidden paths |
| G4 (no new axioms) | PASS | V21 axiom set identical to V20: same 12 seeds + 2 oracle axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle); no new non-oracle axioms |
| G5 (per-cand evaluator) | PASS | exit 0, `status: ok`; both oracles pass at new ceilings: joint_phi_phip_invD2_val=11/1000000 >= oracle 11/1000000, uzz_phi_sq_val=29/5000000 >= oracle 29/5000000 |
| G6 (score) | PASS | Cr_val = 1/71900 ≈ 1.391e-05 < 1/66500 ≈ 1.504e-05 (V20 parent); 1.082x improvement as specified |

## REPRODUCED-WITH

```
lake commit: 2542b970938eb7d92d7cbed366277453440b05c4
log entry:   {"timestamp":"2026-04-30T11:12:05Z","lemma":"lemma_5_4","candidate":"Candidates/V21.lean","candidate_sha256":"bf364569982f0089d84b3a7d07163c7d670d0ab04a84816e42cab497c95978f3","parent":"Candidates/V18.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":71900,"approx":1.3908205841446454e-05},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"11/1000000","uzz_phi_sq_val":"29/5000000","Cr_val":"1/71900"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"11/1000000","oracle_bound":"11/1000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"29/5000000","oracle_bound":"29/5000000","status":"pass"}],"wall_seconds":{"compile":3.99,"axiom_audit":7.08,"oracle":0.08}}
```
