# Verdict: sprint_018

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_018.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V13.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V13.lean` exit 0, no error lines (4.1s); stale .olean cleared before run |
| G2 (no sorry) | PASS | grep found no matches |
| G3 (write scope) | PASS | Only changed tracked file is `ProofRefinement/Lemma54/Experience.md` (always-allowed); V13.lean is a new candidate file (contract-named as new file) |
| G4 (no new axioms) | PASS | V13 axiom set is identical to V12 (17 axioms, same names); no new seed or unregistered axioms; oracle axiom declared values changed but oracle set unchanged |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V13.lean` exit 0, `status: ok`; all 4 oracle checks pass; score 1/300 |
| G6 (score) | PASS | 1/300 ≈ 0.003333 < 1/32 = 0.03125 (previous V12 score); 9.375× reduction confirmed |

## REPRODUCED-WITH

```
lake commit: bcd880437d1a710be9b2c7872afe77976d74a827
log entry:   {"timestamp":"2026-04-30T08:33:26Z","lemma":"lemma_5_4","candidate":"Candidates/V13.lean","candidate_sha256":"00f71e10962bd2c2871a97df00e717f3bb38f439c7c0e39386bb9f97bf1e7f44","parent":"Candidates/V12.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":300,"approx":0.0033333333333333335},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","Cr_val":"1/300"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"61/2500","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_bound","declared":"59/2000","oracle_bound":"59/2000","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_bound","declared":"3407/2000","oracle_bound":"3407/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_u_zz_oracle","kind":"oracle","short":"h_u_zz_oracle","bound_field":"u_zz_bound_val","oracle_fn":"compute_u_zz_bound","declared":"15519/10000","oracle_bound":"15519/10000","status":"pass"}],"wall_seconds":{"compile":4.14,"axiom_audit":7.04,"oracle":0.08}}
```
