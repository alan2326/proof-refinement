# Verdict: sprint_034

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_034.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V28.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V28.lean` exited 0; no `error:` lines (style warnings only from downstream `Lemma54_Paper_Main.lean`; none from V28 itself except a `show`-vs-`change` style note, not an error) |
| G2 (no sorry) | PASS | `grep -n 'sorry' V28.lean` returned no matches |
| G3 (write scope) | PASS | Changed files since sprint baseline: `Candidates/V28.lean` (contract-named new candidate), `lemma.toml` (contract-named, two oracle_fn rewires), `Bulletin.md` (always-allowed), `Experience.md` (always-allowed), `Scratch/sprint_034_verify_v14.py` (contract-named), `Scratch/sprint_034_verify_v14.txt` (always-allowed Scratch/), `Scratch/sprint_034_planner_v14_baseline.py` (always-allowed Scratch/), `Scratch/sprint_034_planner_v14_baseline.txt` (always-allowed Scratch/), `Scratch/plot_cr_progression.py` (always-allowed Scratch/), `Sprint_Contracts/sprint_034.md` (new sprint contract, not a prior-sprint contract). No forbidden paths: no V<K>.lean for K<=27, no ProofGraph/, no Evaluator.py, no Lean library files. |
| G4 (no new axioms) | PASS | V28 introduces `h_joint_phi_phip_invD2_oracle` (kind=oracle, registered in lemma.toml `[[oracles]]` with `bound_field=joint_phi_phip_invD2_val`) and `h_u_zz_oracle` (kind=oracle, registered with `bound_field=u_zz_bound_val`). Both are oracle kind per the Evaluator classifier; neither is `seed` or `unregistered`. Drops V27's `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_M_pp_oracle`. No new seed axioms. |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V28.lean` exited 0; all 3 oracle axioms `status: pass` (M_phi_val=231143/10000000, joint_phi_phip_invD2_val=609061/10000000, u_zz_bound_val=8342848479/10000000); `Cr_val = 2/7 ≈ 0.285714`; final verdict `PASS` |
| G7 (rigor / no-truncation + audit-floor) | SKIPPED | Tier is `ambitious` (not `checkpoint`) and no production files under `ProofGraph/` were changed; per evaluation instructions G7 runs only for `checkpoint` tier or ProofGraph/ changes |
| G6 (score) | PASS | V28 score `2/7 ≈ 0.2857` < V27 (sprint 033 parent) score `1/3 ≈ 0.3333`; strict improvement of ~16.7% |

## REPRODUCED-WITH

```
lake commit: 30cc9a0ed7469563009d14bf1105dc51dcdefd67
log entry:   {"timestamp":"2026-05-03T04:27:13Z","lemma":"lemma_5_4","candidate":"Candidates/V28.lean","candidate_sha256":"601cbb6a2b4f354559438ba5d36497dda9bab48c40babe4f9e97d309604b6ed6","parent":"Candidates/V11.lean","status":"ok","score_field":"Cr_val","score":{"numer":2,"denom":7,"approx":0.2857142857142857},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"231143/10000000","joint_phi_phip_invD2_val":"609061/10000000","u_zz_bound_val":"8342848479/10000000","Cr_val":"2/7"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_truncfree_bound","declared":"231143/10000000","oracle_bound":"231143/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_truncfree_bound","declared":"609061/10000000","oracle_bound":"609061/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_u_zz_oracle","kind":"oracle","short":"h_u_zz_oracle","bound_field":"u_zz_bound_val","oracle_fn":"compute_u_zz_bound_truncfree_bound","declared":"8342848479/10000000","oracle_bound":"8342848479/10000000","status":"pass"}],"wall_seconds":{"compile":6.31,"axiom_audit":7.41,"oracle":0.08}}
```
