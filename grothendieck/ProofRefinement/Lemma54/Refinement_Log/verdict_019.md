# Verdict: sprint_019

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_019.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V14.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V14.lean` exit 0, no error lines; `lake build LeanProof` also succeeded with no errors |
| G2 (no sorry) | PASS | grep found no `sorry` matches in V14.lean |
| G3 (write scope) | PASS | All changed files are contract-named (V14.lean, joint_phi_phip_invD2.py, lemma.toml, Lemma54_Paper.lean, Lemma54_Paper_Pderiv_Single.lean, Lemma54_Paper_Main.lean, Numerical_Library/__init__.py), always-allowed (Bulletin.md, Experience.md, Scratch/*), or Planner-created (sprint_019.md created before Generator ran). No forbidden paths touched. |
| G4 (no new axioms) | PASS | New axiom `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` has `kind=oracle`. No new seed or unregistered axioms beyond V13's set. V13 oracles h_M_phi_prime_oracle and h_inv_F_p_z_oracle are orphaned (not in transitive set) — removals are always fine. |
| G5 (per-cand evaluator) | PASS | `Evaluator.py --file V14.lean` exits 0, `pass: true`. All 3 oracle checks pass: h_M_phi_oracle 61/2500 >= 61/2500, h_joint_phi_phip_invD2_oracle 3/10000 >= 3/10000, h_u_zz_oracle 15519/10000 >= 15519/10000. Score: Cr_val = 1/1300 ≈ 0.000769. |
| G6 (score) | PASS | 1/1300 < 1/300: n=1, d=1300, n*300=300 < d=1300. ~4.33x improvement over V13. |

## REPRODUCED-WITH

```
lake commit: 48b2701c8a8a6826d0efef259a68df975c4faaf2
log entry:   {"timestamp":"2026-04-30T09:06:42Z","lemma":"lemma_5_4","candidate":"Candidates/V14.lean","candidate_sha256":"d782515533ce7ceaae230be1318b26fb5a19501ef7e560b87e17893924ccc10f","parent":"Candidates/V13.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":1300,"approx":0.0007692307692307692},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"3/10000","Cr_val":"1/1300"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"61/2500","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"3/10000","oracle_bound":"3/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_u_zz_oracle","kind":"oracle","short":"h_u_zz_oracle","bound_field":"u_zz_bound_val","oracle_fn":"compute_u_zz_bound","declared":"15519/10000","oracle_bound":"15519/10000","status":"pass"}],"wall_seconds":{"compile":4.24,"axiom_audit":7.1,"oracle":0.08}}
```
