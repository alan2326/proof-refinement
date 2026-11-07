# Verdict: sprint_004

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_004.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V2.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: FAIL
**Failing gate**: G6
**Failure detail**: `SCORE_REGRESSION: new=null prev=9560055559329.883` — the evaluator logged `"score": null` for V2 because `Cr_val := Braverman.Paper.Cr_tight ...` is symbolic (involves `sinh` via `R_val_paper`) and the production cert_compute symbolic evaluator does not recognise `Cr_tight`. The contract's acceptance criterion `score.approx < 2.0e9` cannot be confirmed: no `score.approx` field exists in the log entry.

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V2.lean` exit 0, no error lines |
| G2 (no sorry) | PASS | grep found no `sorry` in V2.lean |
| G3 (write scope) | PASS | Changed paths since sprint_003 verdict: V2.lean (new candidate, allowed), Lemma54_Paper.lean / Lemma54_Paper_Pderiv_Single.lean / Lemma54_Paper_Main.lean (all contract-named), Experience.md / Bulletin.md (always-allowed), Scratch/* (always-allowed), sprint_004.md (new Planner contract, not forbidden). No forbidden paths touched. |
| G4 (no new axioms) | PASS | V2 axioms identical to V1: 3 Lean primitives + 12 trusted analytic (Braverman.Paper.F_inv_paper family) + h_M_oracle + h_oracle_domain_contains_image. No new axiom. |
| G5 (per-cand evaluator) | PASS | exit 0, PASS; oracle pass: declared M_val=432 >= oracle 4318113/10000; score field `Cr_val: <symbolic, could not evaluate>` |
| G6 (score) | FAIL | Log entry has `"score": null` — `Cr_tight` is not recognised by cert_compute symbolic evaluator (depends on `sinh` via `R_val_paper`). Contract requires `score.approx < 2.0e9` but no `score.approx` exists to verify. |

## Notes

The proof itself is correct and well-formed (G1–G5 all pass). The issue is purely in the scoring pipeline: `Cr_val` delegates to `Braverman.Paper.Cr_tight` which internally uses `R_val_paper r = sinh((3 + r) / 4)`, a transcendental that the `_eval_rational` evaluator cannot handle. The production symbolic evaluator (`proof_graph.cert_compute.evaluate_symbolic`) knows about `Cr_paper` but not `Cr_tight`, so it also returns `None`. Numerical verification (mpmath at 50 dps) confirms `Cr_tight ≈ 1.145×10⁹` satisfies the contract criterion, but this is not the gate's basis.

The Planner's next sprint should either:
1. Extend `proof_graph.cert_compute.evaluate_symbolic` to recognise `Cr_tight r M (R_val_paper r)`, OR
2. Have V2 define `Cr_val` as a rational approximation (upper bound) of `Cr_tight` at the fixed parameters, so the evaluator can score it directly, OR
3. Register `Cr_tight` with a dedicated oracle path so the evaluator can certify and score it.

## REPRODUCED-WITH

```
lake commit: a5954b2762ca54d57b4f6a015f0a1ce97b408221
log entry:   {"timestamp":"2026-04-30T03:04:33Z","lemma":"lemma_5_4","candidate":"Candidates/V2.lean","candidate_sha256":"6b23a35b02b20b56c19031df4309654da718aed1b6e25ebbdefcdfe10528a995","parent":"Candidates/V1.lean","status":"ok","score_field":"Cr_val","score":null,"def_vals":{"M_val":"432/1","delta_val":"163/1000","B_val":"223/200"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_zero","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_oracle","kind":"oracle","short":"h_M_oracle","bound_field":"M_val","oracle_fn":"compute_M_bound_tight","declared":"432/1","oracle_bound":"4318113/10000","status":"pass"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":3.91,"axiom_audit":6.6,"oracle":0.07}}
```
