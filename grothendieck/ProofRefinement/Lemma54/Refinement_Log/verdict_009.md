# Verdict: sprint_009

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_009.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V7.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V7.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` found in V7.lean |
| G3 (write scope) | PASS | Generator-changed files: V7.lean (contract-named), m_bound.py (contract-named), Bulletin.md (always-allowed), Scratch/sprint_009_verify.py (always-allowed); post-sprint Planner changes to TEMPLATE.md and .claude/agents/refinement-planner.md are out of Generator scope |
| G4 (no new axioms) | PASS | Axiom set identical to V6's parent: 3 Lean primitives + 12 trusted analytic + h_M_oracle + h_oracle_domain_contains_image; no sorryAx, no new names |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V7.lean` exits 0; `PASS`; oracle gate: declared M_val=428 >= oracle 855827/2000 (427.9135); Cr_val=1132310000 |
| G6 (score) | PASS | V7 score 1132310000.0 < V6 score 1148240000.0 (reduction of ~1.387%); Cr_val < previous confirmed |

## REPRODUCED-WITH

```
lake commit: 17d37fcd71710ba69288b3100f3d4a1842823b67
log entry:   {"timestamp":"2026-04-30T04:41:22Z","lemma":"lemma_5_4","candidate":"Candidates/V7.lean","candidate_sha256":"d0c110e61aebe746a6b77a2924b281e4df9bcd6c55d8ede9c0ef6a556e869276","parent":"Candidates/V6.lean","status":"ok","score_field":"Cr_val","score":{"numer":1132310000,"denom":1,"approx":1132310000.0},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","Cr_val":"1132310000/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"428/1","oracle_bound":"855827/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.13,"axiom_audit":6.58,"oracle":0.09}}
```
