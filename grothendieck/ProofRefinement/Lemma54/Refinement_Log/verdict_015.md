# Verdict: sprint_015

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_015.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V11.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V11.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` found in V11.lean |
| G3 (write scope) | PASS | Changed files: V11.lean (contract-named target), Lemma54_Paper.lean (contract-named), Lemma54_Paper_Pderiv_Single.lean (contract-named), Lemma54_Paper_Main.lean (contract-named), Bulletin.md (always-allowed), Experience.md (always-allowed), Scratch/sprint_015_*.py (always-allowed). Sprint contract created by Planner, not Generator. No forbidden paths touched. |
| G4 (no new axioms) | PASS | New axiom `Braverman.PaperV0.h_M_pp_oracle` has `kind=oracle` and is registered in `lemma.toml` (line 85). No seed or unregistered axioms added. |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V11.lean` exits 0, `pass: true`. All 4 oracles pass: h_M_phi_oracle (declared 239/5000 >= oracle 61/2500), h_M_phi_prime_oracle (declared 543/10000 >= oracle 59/2000), h_M_pp_oracle (declared 1402/25 >= oracle 35048/625), h_inv_F_p_z_oracle (declared 2 >= oracle 3407/2000). |
| G6 (score) | PASS | Cr_val = 1 < 2 (V10 score). Inequality holds: score improved 2x. |

## REPRODUCED-WITH

```
lake commit: 1411f5b62543faa5254d9d9ccd9c719123061f96
log entry:   {"timestamp":"2026-04-30T07:37:00Z","lemma":"lemma_5_4","candidate":"Candidates/V11.lean","candidate_sha256":"e904100fba7fe03f198a491d9a3b23c077d347cb87ed86ecc696bfe30eed6a29","parent":"Candidates/V10.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":1,"approx":1.0},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"239/5000","M_phi_prime_val":"543/10000","inv_F_p_z_val":"2/1","M_pp_val":"1402/25","Cr_val":"1/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"239/5000","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_bound","declared":"543/10000","oracle_bound":"59/2000","status":"pass"},{"name":"Braverman.PaperV0.h_M_pp_oracle","kind":"oracle","short":"h_M_pp_oracle","bound_field":"M_pp_val","oracle_fn":"compute_M_pp_bound","declared":"1402/25","oracle_bound":"35048/625","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_bound","declared":"2/1","oracle_bound":"3407/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.45,"axiom_audit":6.85,"oracle":0.08}}
```
