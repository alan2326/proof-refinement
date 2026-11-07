# Verdict: sprint_027

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_027.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V22.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V22.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` matches in V22.lean |
| G3 (write scope) | PASS | Changed files: V22.lean (new target), joint_phi_phip_invD2.py (contract-named), uzz_phi_sq.py (contract-named), Bulletin.md (always-allowed), Experience.md (always-allowed); no forbidden paths touched |
| G4 (no new axioms) | PASS | Axiom set identical to V21 parent: same 12 seeds, same 2 oracle axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle), no new non-oracle axioms |
| G5 (per-cand evaluator) | PASS | exit 0, pass=true; both oracles reverified: h_joint_phi_phip_invD2_oracle declared 13/2000000 >= oracle 13/2000000; h_uzz_phi_sq_oracle declared 31/10000000 >= oracle 31/10000000 |
| G6 (score) | PASS | new=1/124000 (~8.065e-6) < prev=1/71900 (~1.391e-5); 1.724x improvement |

## REPRODUCED-WITH

```
lake commit: f0844d97eaf92b21e4e3f989a36b005a0791c00a
log entry:   {"timestamp":"2026-04-30T11:25:26Z","lemma":"lemma_5_4","candidate":"Candidates/V22.lean","candidate_sha256":"8f709eeee11cd8da1e8e7bc94f3f22dce970dbb93dcd704825edd0dc930495b7","parent":"Candidates/V21.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":124000,"approx":8.064516129032258e-06},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"13/2000000","uzz_phi_sq_val":"31/10000000","Cr_val":"1/124000"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"13/2000000","oracle_bound":"13/2000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"31/10000000","oracle_bound":"31/10000000","status":"pass"}],"wall_seconds":{"compile":4.12,"axiom_audit":6.56,"oracle":0.08}}
```
