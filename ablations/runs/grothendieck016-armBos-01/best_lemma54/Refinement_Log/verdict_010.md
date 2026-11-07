# Verdict: sprint_010

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_010.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V8.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V8.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | No `sorry` found in V8.lean |
| G3 (write scope) | PASS | Changed files: V8.lean (contract-named target), Lemma54_Paper.lean (named in Concrete edits expected), Bulletin.md (always-allowed), Scratch/planner_010_explore.py (always-allowed under Scratch/), sprint_010.md (new contract created by Planner, not edit of existing); no forbidden-path violations |
| G4 (no new axioms) | PASS | V8 axioms_used: 14 entries; V7 had 15 (including `Braverman.Paper.F_inv_paper_zero`); V8 drops `F_inv_paper_zero` (now a theorem), no new axiom names introduced |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V8.lean` exits 0; status=ok; oracle gate: declared M_val=428 >= oracle 855827/2000; Cr_val=1132310000; F_inv_paper_zero absent from axioms_used |
| G6 (score) | PASS | Contract names no score-reduction inequality (sprint win is axiom count reduction: 15→14 axiom entries, F_inv_paper_zero promoted from axiom to theorem); Cr_val=1132310000 unchanged from V7 as specified; axiom count criterion confirmed by log entry |

## REPRODUCED-WITH

```
lake commit: 0721e0a43239c4acf3ed0b3ea634d57f92b42d64
log entry:   {"timestamp":"2026-04-30T05:06:14Z","lemma":"lemma_5_4","candidate":"Candidates/V8.lean","candidate_sha256":"27801eb7d25042aa3730066a8ab07cf0b7152d42b01e8ee3c15cfc6f1d4b9d13","parent":"Candidates/V7.lean","status":"ok","score_field":"Cr_val","score":{"numer":1132310000,"denom":1,"approx":1132310000.0},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","Cr_val":"1132310000/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"428/1","oracle_bound":"855827/2000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":5.73,"axiom_audit":7.02,"oracle":0.07}}
```
