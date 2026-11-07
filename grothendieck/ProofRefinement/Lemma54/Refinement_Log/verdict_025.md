# Verdict: sprint_025

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_025.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V20.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V20.lean` exit 0, no error lines (4.1s) |
| G2 (no sorry) | PASS | No matches for `sorry` in V20.lean |
| G3 (write scope) | PASS | Changed paths: V20.lean (new candidate), joint_phi_phip_invD2.py (contract-named), uzz_phi_sq.py (contract-named), Experience.md (always-allowed), Bulletin.md (always-allowed), Scratch/sprint_025_*.py (always-allowed under Scratch/); no forbidden paths |
| G4 (no new axioms) | PASS | Axiom set identical to V19: 12 seeds + 2 oracle-kind axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle); no new unregistered or seed-kind axioms introduced |
| G5 (per-cand evaluator) | PASS | exit 0, `pass: true`; both oracle axioms reverified (joint 3/250000 >= oracle 3/250000, uzz 3/500000 >= oracle 3/500000); Cr_val = 1/66500 |
| G6 (score) | PASS | new = 1/66500 ≈ 1.504e-5 < prev = 1/31500 ≈ 3.175e-5 (2.111x improvement) |

## REPRODUCED-WITH

```
lake commit: 4653d2cf0ac8d2b907d25e6153d137db300b6be2
log entry:   {"timestamp":"2026-04-30T10:52:43Z","lemma":"lemma_5_4","candidate":"Candidates/V20.lean","candidate_sha256":"a394beb507269e1287bb8e860acc60399ac2af38a36d7422122c14979492045b","parent":"Candidates/V19.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":66500,"approx":1.5037593984962406e-05},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"3/250000","uzz_phi_sq_val":"3/500000","Cr_val":"1/66500"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"3/250000","oracle_bound":"3/250000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"3/500000","oracle_bound":"3/500000","status":"pass"}],"wall_seconds":{"compile":4.05,"axiom_audit":7.01,"oracle":0.08}}
```
