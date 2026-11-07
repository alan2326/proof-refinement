# Verdict: sprint_007

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_007.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V5.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V5.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | no matches for `sorry` in V5.lean |
| G3 (write scope) | PASS | only `Experience.md` (always-allowed) modified; V5.lean committed to HEAD |
| G4 (no new axioms) | PASS | axiom set identical to V4: 3 seeds + 12 analytic + h_M_oracle + h_oracle_domain_contains_image |
| G5 (per-cand evaluator) | PASS | exit 0, `pass: true`, score 1153569600.0, oracle h_M_oracle pass |
| G6 (score) | PASS | new=1153569600.0 < prev=1231718400.0 (V4, sprint_006); 6.34% reduction |

## REPRODUCED-WITH

```
lake commit: bc6cbc2c0c90d6a6ba84392870fa26f2ae5226be
log entry:   {"timestamp":"2026-04-30T03:46:51Z","lemma":"lemma_5_4","candidate":"Candidates/V5.lean","candidate_sha256":"ff11a8c45bb876b82106d53101b2d5d03315e8e6d99dab415a032fb5f820915c","parent":"Candidates/V4.lean","status":"ok","score_field":"Cr_val","score":{"numer":1153569600,"denom":1,"approx":1153569600.0},"def_vals":{"M_val":"432/1","delta_val":"163/1000","B_val":"223/200","Cr_val":"1153569600/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"432/1","oracle_bound":"4318113/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.15,"axiom_audit":5.93,"oracle":0.07}}
```
