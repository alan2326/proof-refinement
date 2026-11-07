# Verdict: sprint_031

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_031.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V26.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V26.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No matches for `sorry` in V26.lean |
| G3 (write scope) | PASS | Changed files: V26.lean (contract item 3), merged_uderiv.py (contract item 2), sprint_031_verify_n524288.txt (contract item 1 + Scratch/), sprint_031_verify_n524288.py (Scratch/ always-allowed), Bulletin.md (always-allowed one-line append); Experience.md (always-allowed). No forbidden paths touched. |
| G4 (no new axioms) | PASS | V26 axiom set identical to V25's last-PASS set. `h_merged_uderiv_oracle` was already `kind=oracle` in V25; its declared rational tightened from `41/5000000` to `37/5000000` but no new axioms of any kind were introduced. |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V26.lean` exit 0, `pass: true`. Oracle reverification: `declared 37/5000000 >= oracle 37/5000000`, status pass. Score: `Cr_val = 1/268000`. |
| G6 (score) | PASS | V26 `Cr_val = 1/268000 ≈ 3.731e-6` < V25 `Cr_val = 1/240000 ≈ 4.167e-6` (1.117× improvement). Inequality holds. |

## REPRODUCED-WITH

```
lake commit: 795940eb3a2ccc455a4fe0ff576295c7e0ed3a75
log entry:   {"timestamp":"2026-04-30T13:44:03Z","lemma":"lemma_5_4","candidate":"Candidates/V26.lean","candidate_sha256":"3bf028ec71ba18e8b7fcf4165031c3450121e19df92ef23aa12c3304858b20ec","parent":"Candidates/V25.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":268000,"approx":3.7313432835820897e-06},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"47/10000000","uzz_phi_sq_val":"3/1250000","merged_uderiv_val":"37/5000000","Cr_val":"1/268000"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_merged_uderiv_oracle","kind":"oracle","short":"h_merged_uderiv_oracle","bound_field":"merged_uderiv_val","oracle_fn":"compute_merged_uderiv_bound","declared":"37/5000000","oracle_bound":"37/5000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":4.11,"axiom_audit":6.42,"oracle":0.08}}
```
