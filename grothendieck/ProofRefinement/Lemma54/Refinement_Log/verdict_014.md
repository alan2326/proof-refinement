# Verdict: sprint_014

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_014.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V10.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V10.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` matches in V10.lean |
| G3 (write scope) | PASS | All changed files within allowed scope: V10.lean (new candidate), Lemma54_Paper.lean, Lemma54_Paper_Pderiv_Single.lean, Lemma54_Paper_Main.lean, inv_F_p_z.py (new), lemma.toml (additive), __init__.py (inherent package companion to inv_F_p_z.py), Experience.md, Bulletin.md, Scratch/ files; .claude/scheduled_tasks.lock is an auto-generated system lock not a Generator modification; Lemma54_Paper_Cauchy.lean was reverted in sprint_013 (pre-sprint_014) and not touched in this sprint |
| G4 (no new axioms) | PASS | One new axiom `Braverman.PaperV0.h_inv_F_p_z_oracle` with `kind=oracle`; registered in lemma.toml `[[oracles]]` table as `h_inv_F_p_z_oracle`; oracle-kind additions are exempt per G4 rules |
| G5 (per-cand evaluator) | PASS | Exit 0, `pass: true`; oracles all pass (h_M_phi_oracle: 239/5000 >= 61/2500; h_M_phi_prime_oracle: 543/10000 >= 59/2000; h_inv_F_p_z_oracle: 2 >= 3407/2000); Cr_val=2 |
| G6 (score) | PASS | V10 score 2.0 < V9 score 5.0 — strict improvement |

## REPRODUCED-WITH

```
lake commit: d1e50feefa59e31a4c436af64fc0948ad588532e
log entry:   {"timestamp":"2026-04-30T07:11:33Z","lemma":"lemma_5_4","candidate":"Candidates/V10.lean","candidate_sha256":"6af8b9e9b53b93e7667b0ee26df54b906362f70c3c6c5ac7f51c83e1bddb47ce","parent":"Candidates/V9.lean","status":"ok","score_field":"Cr_val","score":{"numer":2,"denom":1,"approx":2.0},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"239/5000","M_phi_prime_val":"543/10000","inv_F_p_z_val":"2/1","Cr_val":"2/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle","bound_field":"M_phi_val","oracle_fn":"compute_M_phi_bound","declared":"239/5000","oracle_bound":"61/2500","status":"pass"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle","bound_field":"M_phi_prime_val","oracle_fn":"compute_M_phi_prime_bound","declared":"543/10000","oracle_bound":"59/2000","status":"pass"},{"name":"Braverman.PaperV0.h_inv_F_p_z_oracle","kind":"oracle","short":"h_inv_F_p_z_oracle","bound_field":"inv_F_p_z_val","oracle_fn":"compute_inv_F_p_z_bound","declared":"2/1","oracle_bound":"3407/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.57,"axiom_audit":7.13,"oracle":0.07}}
```
