# Verdict: sprint_028

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_028.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V23.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V23.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | No matches for `sorry` in V23.lean |
| G3 (write scope) | PASS | Changed files: V23.lean (new candidate), joint_phi_phip_invD2.py (named in contract), uzz_phi_sq.py (named in contract), Bulletin.md (always-allowed), Experience.md (always-allowed); no prior candidate V<K>.lean K<=22 modified |
| G4 (no new axioms) | PASS | V23 axiom set identical to V22: same 12 seed + 2 oracle axioms; two oracle axioms (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle) already existed and have kind=oracle; no new axiom of any kind introduced |
| G5 (per-cand evaluator) | PASS | Exit 0, `pass: true`; oracle reverifications: h_joint_phi_phip_invD2_oracle declared=47/10000000 >= oracle 47/10000000 pass; h_uzz_phi_sq_oracle declared=3/1250000 >= oracle 3/1250000 pass |
| G6 (score) | PASS | Cr_val = 1/169000 ≈ 5.917e-06 < 1/124000 ≈ 8.065e-06 (V22 parent); improvement factor 1.363x |

## REPRODUCED-WITH

```
lake commit: e80593ddda3212f48a396198a7307d39615afe1a
log entry:   {"timestamp":"2026-04-30T11:41:05Z","lemma":"lemma_5_4","candidate":"Candidates/V23.lean","candidate_sha256":"925031118b3aa117ed3a8dc37f011a2a96bf81ec008d504f0d9836d743d253e6","parent":"Candidates/V22.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":169000,"approx":5.917159763313609e-06},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"47/10000000","uzz_phi_sq_val":"3/1250000","Cr_val":"1/169000"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"47/10000000","oracle_bound":"47/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"3/1250000","oracle_bound":"3/1250000","status":"pass"}],"wall_seconds":{"compile":4.1,"axiom_audit":7.06,"oracle":0.08}}
```
