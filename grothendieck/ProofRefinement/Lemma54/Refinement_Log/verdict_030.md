# Verdict: sprint_030

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_030.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V25.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V25.lean` exits 0; `lake build ProofRefinement.Lemma54.Candidates.V25` succeeded (2951 jobs); linter warnings only, no `error:` lines |
| G2 (no sorry) | PASS | grep found no `sorry` occurrences in V25.lean |
| G3 (write scope) | PASS | All changed paths are contract-named or always-allowed: `Candidates/V25.lean` (new candidate), `Numerical_Library/merged_uderiv.py` (item 2), `Numerical_Library/__init__.py` (item 3), `lemma.toml` (item 4), `Proof/Lib/Lemma54_Paper.lean` (item 5), `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean` (item 6), `Proof/Lib/Lemma54_Paper_Main.lean` (item 7), `Experience.md` (always-allowed), `Scratch/sprint_030_oracle_run.py` (always-allowed), `Scratch/sprint_030_verify_n262144.txt` (always-allowed); no forbidden paths touched |
| G4 (no new axioms) | PASS | `--skip-oracle` run: only new axiom is `Braverman.PaperV0.h_merged_uderiv_oracle` with `kind=oracle`; all other axioms are seeds inherited from V23; no `seed` or `unregistered` additions |
| G5 (per-cand evaluator) | PASS | Full evaluator exits 0, `status: ok`; oracle `h_merged_uderiv_oracle` passes with `declared=41/5000000 >= oracle_bound=41/5000000`; `Cr_val=1/240000` |
| G6 (score) | PASS | V25 `Cr_val=1/240000 ≈ 4.167e-6` < V23 `Cr_val=1/169000 ≈ 5.917e-6`; contract requires `Cr_val < 1/169000`; margin: 240000 > 169000 |

## REPRODUCED-WITH

```
lake commit: ca5df5bd0e3f42f307097de60e76b97beded75ad
log entry:   {"timestamp":"2026-04-30T12:59:19Z","lemma":"lemma_5_4","candidate":"Candidates/V25.lean","candidate_sha256":"260ec24ec021d479d8268ba30b7e5dee44415c0ec130464b2e9561554315d968","parent":"Candidates/V23.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":240000,"approx":4.166666666666667e-06},...,"axioms_used":[...{"name":"Braverman.PaperV0.h_merged_uderiv_oracle","kind":"oracle","short":"h_merged_uderiv_oracle","bound_field":"merged_uderiv_val","oracle_fn":"compute_merged_uderiv_bound","declared":"41/5000000","oracle_bound":"41/5000000","status":"pass"},...]}
```
