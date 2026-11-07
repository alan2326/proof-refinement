# Verdict: sprint_016

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_016.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V12.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION (implied by Experience.md sprint 016 entry completion and Evaluator pre-run showing status=ok)
**Outcome**: FAIL
**Failing gate**: G3 (write scope)
**Failure detail**: `WRITE_SCOPE_VIOLATION` — two files were modified/created during the sprint that are not named in the contract's `Concrete edits expected:` field and are not always-allowed paths:
1. `docs/HARNESS_OPERATOR_TIPS.md` — new file outside the Lemma 5.4 ecosystem (committed at 08:02:42, after sprint_016 contract creation at 07:46:30); not listed in any allowed category.
2. `ProofRefinement/Lemma54/Numerical_Library/__init__.py` — additive import change for the new `u_zz` module; not named in `Concrete edits expected:` (which lists `Numerical_Library/u_zz.py` but not `__init__.py`).

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V12.lean` exits 0, no `error:` lines |
| G2 (no sorry) | PASS | `grep -n 'sorry' V12.lean` returns no matches |
| G3 (write scope) | FAIL | `WRITE_SCOPE_VIOLATION`: `docs/HARNESS_OPERATOR_TIPS.md` (outside Lemma 5.4 ecosystem, not in contract) and `Numerical_Library/__init__.py` (not named in `Concrete edits expected:`) were modified during sprint |
| G4 (no new axioms) | SKIPPED | terminated at G3 |
| G5 (per-cand evaluator) | SKIPPED | terminated at G3 |
| G6 (score) | SKIPPED | terminated at G3 |

## REPRODUCED-WITH

```
lake commit: 7c305773b75897423b60ffe3bcf86cf9c6b16310
log entry:   {"timestamp":"2026-04-30T08:07:20Z","lemma":"lemma_5_4","candidate":"Candidates/V12.lean","candidate_sha256":"df83f864cd150b1e9d8d3627fb9da8d7fa29dda23574421099c7ecacff8fe2b7","parent":"Candidates/V11.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":32,"approx":0.03125},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"239/5000","M_phi_prime_val":"543/10000","inv_F_p_z_val":"2/1","u_zz_bound_val":"2/1","Cr_val":"1/32"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"239/5000","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_bound","declared":"543/10000","oracle_bound":"59/2000","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_bound","declared":"2/1","oracle_bound":"3407/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_u_zz_oracle","kind":"oracle","short":"h_u_zz_oracle","bound_field":"u_zz_bound_val","oracle_fn":"compute_u_zz_bound","declared":"2/1","oracle_bound":"15519/10000","status":"pass"}],"wall_seconds":{"compile":4.11,"axiom_audit":6.95,"oracle":0.07}}
```
