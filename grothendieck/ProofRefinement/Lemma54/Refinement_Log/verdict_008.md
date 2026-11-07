# Verdict: sprint_008

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_008.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V6.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V6.lean` exits 0, no error lines |
| G2 (no sorry) | PASS | grep finds no `sorry` in V6.lean |
| G3 (write scope) | PASS | Generator touched only V6.lean (new candidate), m_bound.py (contract-named), Bulletin.md (always-allowed), Scratch/sprint_008_verify.py (always-allowed); other changed paths (README.md, sprint_008.md, AGENT_BRIEF.md, TEMPLATE.md) committed by Planner prior to Generator's V6 commit |
| G4 (no new axioms) | PASS | V6 axiom set identical to V5: {propext, Classical.choice, Quot.sound, 10 Braverman.Paper.* seeds, h_M_oracle, h_oracle_domain_contains_image}; no additions |
| G5 (per-cand evaluator) | PASS | exit 0, status=ok; oracle pass (h_M_oracle: declared M_val=431 >= oracle_bound=215309/500=430.618); score Cr_val=1148240000 |
| G6 (score) | PASS | new score 1148240000 < prev score 1153569600 (V5 parent); reduction 0.462% |

## REPRODUCED-WITH

```
lake commit: 2c86439b843ab15306537c9184b089190f31fed6
log entry:   {"timestamp":"2026-04-30T04:09:49Z","lemma":"lemma_5_4","candidate":"Candidates/V6.lean","candidate_sha256":"5c21f993ae1502d2eb0369d1e3f8a9e288f20701985cbb5304eefe324effbd08","parent":"Candidates/V5.lean","status":"ok","score_field":"Cr_val","score":{"numer":1148240000,"denom":1,"approx":1148240000.0},"def_vals":{"M_val":"431/1","delta_val":"163/1000","B_val":"223/200","Cr_val":"1148240000/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"431/1","oracle_bound":"215309/500","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.11,"axiom_audit":6.13,"oracle":0.07}}
```
