# Verdict: sprint_029

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_029.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V24.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V24.lean` exit 0, no error lines; `lake build ProofRefinement.Lemma54.Candidates.V24` succeeded with warnings only |
| G2 (no sorry) | PASS | No matches for `sorry` in V24.lean |
| G3 (write scope) | PASS | V24.lean (contract-named); Scratch/sprint_029_* (always-allowed under Scratch/); Proposals/proposal_003_wider_analyticity_domain.md (contract-named); Bulletin.md (always-allowed); Experience.md (always-allowed); sprint_029.md (newly-created by Planner before Generator ran — not a Generator modification of an existing contract) |
| G4 (no new axioms) | PASS | Axiom set identical to V23: same 12 seeds + same 2 oracles (h_joint_phi_phip_invD2_oracle, h_uzz_phi_sq_oracle); no new axioms introduced |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V24.lean` exit 0; status=ok; both oracle reverifications PASS (declared 47/10000000 >= oracle 47/10000000; declared 3/1250000 >= oracle 3/1250000) |
| G6 (score) | PASS | Cr_val = 1/169000 (numer=1, denom=169000) — matches contract's expected unchanged score; research sprint with intentionally stable score |

## REPRODUCED-WITH

```
lake commit: 6c7149aa77e669f7b79ad4bab433370e7802fd5b
log entry:   {"timestamp":"2026-04-30T12:07:22Z","lemma":"lemma_5_4","candidate":"Candidates/V24.lean","candidate_sha256":"b614dda2c9fdcb1333b74e5eeef6ce6b68cf54a1f92f3ff00da37f57f00fc642","parent":"Candidates/V23.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":169000,"approx":5.917159763313609e-06},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"61/2500","M_phi_prime_val":"59/2000","inv_F_p_z_val":"3407/2000","u_zz_bound_val":"15519/10000","joint_phi_phip_invD2_val":"47/10000000","uzz_phi_sq_val":"3/1250000","Cr_val":"1/169000"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_joint_phi_phip_invD2_oracle","kind":"oracle","short":"h_joint_phi_phip_invD2_oracle","bound_field":"joint_phi_phip_invD2_val","oracle_fn":"compute_joint_phi_phip_invD2_bound","declared":"47/10000000","oracle_bound":"47/10000000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"},{"name":"Braverman.PaperV0.h_uzz_phi_sq_oracle","kind":"oracle","short":"h_uzz_phi_sq_oracle","bound_field":"uzz_phi_sq_val","oracle_fn":"compute_uzz_phi_sq_bound","declared":"3/1250000","oracle_bound":"3/1250000","status":"pass"}],"wall_seconds":{"compile":3.66,"axiom_audit":7.16,"oracle":0.07}}
```
