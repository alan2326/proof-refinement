# Verdict: sprint_006

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_006.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V4.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V4.lean` exited 0, no error lines; `lake build` also succeeded (2951 jobs, 4.6s for V4) |
| G2 (no sorry) | PASS | No matches for `sorry` in V4.lean |
| G3 (write scope) | PASS | Changed files: `Candidates/V4.lean` (contract-named target) and `Experience.md` (always-allowed); no forbidden paths |
| G4 (no new axioms) | PASS | Axiom set is identical to V3: 3 Lean primitives + 12 `Braverman.Paper.*` seeds + `h_M_oracle` + `h_oracle_domain_contains_image`; no `sorryAx`; no new axiom |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V4.lean` exited 0; JSON `status: ok`; oracle `h_M_oracle` passed (declared 432 >= bound 431.8113); `Cr_val = 1231718400` |
| G6 (score) | PASS | `score.approx = 1231718400.0 < 1451520000.0` (V3 parent); reduction 1.178x (≈ 15.1%) |

## REPRODUCED-WITH

```
lake commit: 638abf3fa82f9e33665349683e237a2694b80e96
log entry:   {"timestamp":"2026-04-30T03:32:24Z","lemma":"lemma_5_4","candidate":"Candidates/V4.lean","candidate_sha256":"40f384dc615618c9c71a062b8610dce1e5cd881bf500b3e8c7d4effd9c2ee12b","parent":"Candidates/V3.lean","status":"ok","score_field":"Cr_val","score":{"numer":1231718400,"denom":1,"approx":1231718400.0},"def_vals":{"M_val":"432/1","delta_val":"163/1000","B_val":"223/200","Cr_val":"1231718400/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"432/1","oracle_bound":"4318113/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":5.25,"axiom_audit":6.03,"oracle":0.07}}
```
