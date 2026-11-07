# Verdict: sprint_012

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_012.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V9.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS (revised 2026-04-30 after G4 spec correction)
**Failing gate**: none
**Failure detail**: n/a — the original FAIL was a harness bug, not a candidate defect. See "Revision" section below.

## Revision (2026-04-30)

The original verdict was FAIL/G4 because the gate as then-specified treated *any* new axiom name as a regression, regardless of whether the new axiom was a human-approved oracle (registered in `lemma.toml`'s `[[oracles]]` table). After the regression on sprint_012, the G4 spec was corrected in both `.claude/agents/refinement-evaluator.md` and `docs/PROOF_REFINEMENT_HARNESS.md` to exempt oracle-kind axioms — they are human-approved at proposal-approval time, and G5 independently re-verifies their numeric content every run.

Under the corrected G4, **V9 passes all gates**:

| Gate | Outcome (revised) | Detail |
|---|---|---|
| G1 | PASS | unchanged |
| G2 | PASS | unchanged |
| G3 | PASS | unchanged |
| G4 | PASS | The two "new" axioms (`h_M_phi_oracle`, `h_M_phi_prime_oracle`) are both `kind = oracle` — registered in `lemma.toml`'s `[[oracles]]` table at proposal_001 approval time. Oracle-kind additions are exempt from G4 under the corrected spec. No new seed or unregistered axiom appears in V9's audit set. |
| G5 | PASS | per-candidate `Evaluator.py` returns `pass: true`, score Cr_val=5; both new oracles independently re-verify (`h_M_phi_oracle`: declared 239/5000 ≥ oracle 61/2500; `h_M_phi_prime_oracle`: declared 543/10000 ≥ oracle 59/2000). |
| G6 | PASS | Cr_val=5 < V8's 1.132·10⁹ — a ~226M× reduction, easily satisfying the contract's `Cr_val < V8` inequality. |

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V9.lean` exits 0, no error: lines; `lake build ProofRefinement.Lemma54.Candidates.V9` also exits 0 with "Build completed successfully (2951 jobs)" |
| G2 (no sorry) | PASS | `grep -n 'sorry' V9.lean` — no matches |
| G3 (write scope) | PASS | `git diff --name-only HEAD` shows only `ProofRefinement/Lemma54/Experience.md` (always-allowed); `git diff HEAD~10 HEAD` shows V9.lean (new candidate), Lemma54_Paper.lean, Lemma54_Paper_Main.lean, Lemma54_Paper_Pderiv_Single.lean (all contract-named), Bulletin.md, Scratch/sprint_012_*.py (always-allowed), sprint_012.md (Planner-created, not Generator-modified) |
| G4 (no new axioms) | FAIL | V9 axiom set contains `Braverman.PaperV0.h_M_phi_oracle` and `Braverman.PaperV0.h_M_phi_prime_oracle`; neither is in V8's last successful audit (14 axioms: 3 kernel + 9 F_inv_paper + h_M_oracle + h_oracle_domain_contains_image). Two new oracle axiom names introduced. |
| G5 (per-cand evaluator) | SKIP | Not run (terminated at G4) |
| G6 (score) | SKIP | Not run (terminated at G4) |

## Notes

The Sprint Contract explicitly authorises these two new oracles as "already registered in `lemma.toml`'s approved `[[oracles]]` entries — re-declaration in V9 is the standard pattern, not a new axiom." However, the harness's G4 gate is unconditional: "Fail: any new axiom name appears" (PROOF_REFINEMENT_HARNESS.md §5, §8.3). The harness documentation §8.3 states "FAIL-`NEW_AXIOM_INTRODUCED`" for any new axiom name regardless of contract authorisation. The Evaluator does not argue with a failing gate. The Planner should either (a) revise the harness to allow contract-sanctioned oracle additions without triggering G4, or (b) accept this verdict and note that the underlying proof (V9) is otherwise sound — G5 would have passed (the evaluator run with full oracles returned PASS, score=5, and verified both new oracle bounds).

For information only (not used in verdict):
- `uv run Evaluator.py --file V9.lean` exits 0, `pass: true`, score Cr_val=5 (log entry timestamp 2026-04-30T06:13:43Z).
- Oracle checks: h_M_phi_oracle declared M_phi_val=239/5000 >= oracle 61/2500 (pass); h_M_phi_prime_oracle declared M_phi_prime_val=543/10000 >= oracle 59/2000 (pass).
- Score 5 < 1132310000 (V8) — G6 would have passed.

## REPRODUCED-WITH

```
lake commit: 7c0ab0a9d5b3ca62432b9743132538919c25be21
log entry:   {"timestamp":"2026-04-30T06:13:43Z","lemma":"lemma_5_4","candidate":"Candidates/V9.lean","candidate_sha256":"ada484d96737ea36357756cc13d4608d2b1d3b73e0332e453902f585a98fa3fa","parent":"Candidates/V8.lean","status":"ok","score_field":"Cr_val","score":{"numer":5,"denom":1,"approx":5.0},"def_vals":{"M_val":"428/1","delta_val":"327/2000","B_val":"223/200","M_phi_val":"239/5000","M_phi_prime_val":"543/10000","Cr_val":"5/1"},"axioms_used":[{"name":"propext","kind":"seed"},{"name":"Classical.choice","kind":"seed"},{"name":"Quot.sound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_R_bound","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_analytic","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_contdiff","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_eq","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_first_deriv_zero","kind":"seed"},{"name":"Braverman.Paper.F_inv_paper_mem_S","kind":"seed"},{"name":"Braverman.Paper.pr_paper","kind":"seed"},{"name":"Braverman.Paper.pr_paper_pos","kind":"seed"},{"name":"Braverman.PaperV0.h_M_phi_oracle","kind":"oracle","short":"h_M_phi_oracle"},{"name":"Braverman.PaperV0.h_M_phi_prime_oracle","kind":"oracle","short":"h_M_phi_prime_oracle"},{"name":"Braverman.PaperV0.h_oracle_domain_contains_image","kind":"seed"}],"wall_seconds":{"compile":6.16,"axiom_audit":7.16}}
```
