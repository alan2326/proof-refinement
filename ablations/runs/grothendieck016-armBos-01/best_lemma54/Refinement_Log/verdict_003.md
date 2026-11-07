# Verdict: sprint_003

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_003.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V1.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V1.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | grep found no `sorry` in V1.lean |
| G3 (write scope) | PASS | Changed paths: V1.lean (new candidate, allowed), lemma.toml (contract-named), Experience.md (always-allowed), Bulletin.md (always-allowed), Scratch/ files (always-allowed). No forbidden paths. |
| G4 (no new axioms) | PASS | V1 axioms identical to V0: 3 Lean primitives + 12 trusted analytic axioms + h_M_oracle + h_oracle_domain_contains_image. No new axiom. |
| G5 (per-cand evaluator) | PASS | exit 0, `PASS`; oracle message: `pass Braverman.PaperV0.h_M_oracle: declared M_val=432 ≥ oracle 4318113/10000`; score ≈ 9.56·10¹² |
| G6 (score) | PASS | V1 score ≈ 9.56·10¹² < V0 score ≈ 8.196·10¹⁴; also < 1.0·10¹³ acceptance threshold; ≈ 85.8× reduction |

## REPRODUCED-WITH

```
lake commit: e76713537360f392b997987a82ce1d704a18b996
log entry:   {"timestamp":"2026-04-30T02:41:15Z","lemma":"lemma_5_4","candidate":"Candidates/V1.lean","candidate_sha256":"f00a9651cbf6538ea7b5c9093f7aee57775c1b896dc0320f42c3ffd765b9c73d","parent":"Candidates/V0.lean","status":"ok","score_field":"Cr_val","score":{"numer":18671983514316177408,"denom":1953125,"approx":9560055559329.883},"def_vals":{"M_val":"432/1","delta_val":"163/1000","B_val":"223/200"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"432/1","oracle_bound":"4318113/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":3.9,"axiom_audit":6.72,"oracle":0.07}}
```
