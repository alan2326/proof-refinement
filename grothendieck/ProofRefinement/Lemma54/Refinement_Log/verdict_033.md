# Verdict: sprint_033

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_033.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V27.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V27.lean` exited 0; no `error:` lines (style warnings only) |
| G2 (no sorry) | PASS | `grep -n 'sorry' V27.lean` returned no matches |
| G3 (write scope) | PASS | Generator changes since contract creation (c593604b): `Candidates/V27.lean` (contract-named), `lemma.toml` (contract-named), `Bulletin.md` (always-allowed), `Experience.md` (always-allowed), `Scratch/sprint_033_verify_round3.py` (always-allowed), `Scratch/sprint_033_verify_round3.txt` (always-allowed), `Scratch/grothendieck_what_if.py` (always-allowed). No forbidden paths touched. |
| G4 (no new axioms) | PASS | Axiom set identical to parent V11: same 12 seed axioms + 4 oracle axioms (`h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_M_pp_oracle`, `h_inv_F_p_z_oracle`); all oracle, no new `seed` or `unregistered` axioms introduced |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V27.lean` exited 0; all 4 oracle axioms `status: pass`; `Cr_val = 1/3 ≈ 0.333333`; PASS |
| G7 (rigor / no-truncation + audit-floor) | SKIPPED | Tier is `ambitious` (not `checkpoint`) and no ProofGraph/ production files changed; per user instructions G7 runs only for `checkpoint` tier or ProofGraph/ changes |
| G6 (score) | PASS | V27 score `1/3 ≈ 0.333` < V11 parent score `1/1 = 1.0`; strict improvement |

## REPRODUCED-WITH

```
lake commit: c1c2cc862ef00197099ec103a772584209865b27
log entry:   {"timestamp":"2026-05-03T03:52:42Z","lemma":"lemma_5_4","candidate":"Candidates/V27.lean","candidate_sha256":"81e97e338c42f336c814da6b556c61c0169054915d7988911560f15b00277562","parent":"Candidates/V11.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":3,"approx":0.3333333333333333},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"231143/10000000","M_phi_prime_val":"905139/2500000","inv_F_p_z_val":"1424571/400000","M_pp_val":"185260647/10000000","Cr_val":"1/3"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_truncfree_bound","declared":"231143/10000000","oracle_bound":"231143/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_truncfree_bound","declared":"905139/2500000","oracle_bound":"905139/2500000","status":"pass"},{"name":"Braverman.PaperV0.h_M_pp_oracle","kind":"oracle","short":"h_M_pp_oracle","bound_field":"M_pp_val","oracle_fn":"compute_M_pp_truncfree_bound","declared":"185260647/10000000","oracle_bound":"185260647/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_truncfree_bound","declared":"1424571/400000","oracle_bound":"1424571/400000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.8,"axiom_audit":6.62,"oracle":0.09}}
```
