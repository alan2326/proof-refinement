# Verdict: sprint_017

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_017.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V12.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake build ProofRefinement.Lemma54.Candidates.V12` exit 0; no error lines; V12.lean SHA256=df83f864cd150b1e9d8d3627fb9da8d7fa29dda23574421099c7ecacff8fe2b7 matches contract |
| G2 (no sorry) | PASS | grep -n 'sorry' found no matches |
| G3 (write scope) | PASS | Changed files: `docs/HARNESS_OPERATOR_TIPS.md` (contract-listed REMOVE), `ProofRefinement/Lemma54/Bulletin.md` (always-allowed), `ProofRefinement/Lemma54/Experience.md` (always-allowed); `.claude/worktrees/` entries show in git status but have zero diff content (nested-repo dirty state, not Generator writes) |
| G4 (no new axioms) | PASS | New axiom `Braverman.PaperV0.h_u_zz_oracle` has kind=oracle and is registered in lemma.toml `[[oracles]]`; removed `h_M_pp_oracle` (removal is always fine) |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file Candidates/V12.lean` exit 0; all 4 oracle checks pass; `Cr_val: 1/32 ≈ 0.031250`; status: ok |
| G6 (score) | PASS | Cr_val = 1/32 = 0.03125 < parent V11 Cr_val = 1/1 = 1.0 (32x improvement) |

## REPRODUCED-WITH

```
lake commit: a4e2a9bd44b1e7501a8cfc41c03e664ac20e8d51
log entry:   {"timestamp":"2026-04-30T08:19:37Z","lemma":"lemma_5_4","candidate":"Candidates/V12.lean","candidate_sha256":"df83f864cd150b1e9d8d3627fb9da8d7fa29dda23574421099c7ecacff8fe2b7","parent":"Candidates/V11.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":32,"approx":0.03125},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"239/5000","M_phi_prime_val":"543/10000","inv_F_p_z_val":"2/1","u_zz_bound_val":"2/1","Cr_val":"1/32"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"239/5000","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_bound","declared":"543/10000","oracle_bound":"59/2000","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_bound","declared":"2/1","oracle_bound":"3407/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_u_zz_oracle","kind":"oracle","short":"h_u_zz_oracle","bound_field":"u_zz_bound_val","oracle_fn":"compute_u_zz_bound","declared":"2/1","oracle_bound":"15519/10000","status":"pass"}],"wall_seconds":{"compile":3.97,"axiom_audit":7.24,"oracle":0.07}}
```
