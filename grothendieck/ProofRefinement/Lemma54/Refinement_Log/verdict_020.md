# Verdict: sprint_020

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_020.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V15.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean ProofRefinement/Lemma54/Candidates/V15.lean` exits 0, no `error:` lines |
| G2 (no sorry) | PASS | No `sorry` matches in V15.lean |
| G3 (write scope) | PASS | All changed files are contract-named or always-allowed: `Numerical_Library/uzz_phi_sq.py` (NEW, contract-named), `lemma.toml` (contract-named), `Lemma54_Paper.lean` (contract-named), `Lemma54_Paper_Pderiv_Single.lean` (contract-named), `Lemma54_Paper_Main.lean` (contract-named), `Candidates/V15.lean` (new candidate), `Numerical_Library/__init__.py` (sprint-017-salvage allowlist), `Bulletin.md` (always-allowed), `Scratch/sprint_020_planner_term2_joint.py` (always-allowed), `Experience.md` (always-allowed). No forbidden paths touched. |
| G4 (no new axioms) | PASS | Only new axiom is `Braverman.PaperV0.h_uzz_phi_sq_oracle` with `kind: "oracle"`. Oracles `h_M_phi_oracle` and `h_u_zz_oracle` from V14 are now orphaned (no longer consumed by the sink) — this is acceptable. No new `kind: "seed"` or `kind: "unregistered"` axioms. |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V15.lean` exits 0; `pass: true`; both oracles verified: `h_joint_phi_phip_invD2_oracle` declared `3/10000 >= oracle 3/10000`, `h_uzz_phi_sq_oracle` declared `153/1000000 >= oracle 153/1000000` |
| G6 (score) | PASS | `Cr_val = 1/2600 ≈ 3.846e-4 < 1/1300 ≈ 7.692e-4` (V14 previous score); inequality holds; 2.0x win factor |

## REPRODUCED-WITH

```
lake commit: 4e4c6f3fe8391b4db7369157a471cca98d850a52
log entry:   {"timestamp":"2026-04-30T09:36:00Z","lemma":"lemma_5_4","candidate":"Candidates/V15.lean","candidate_sha256":"578c0e457beaa5613037c8577e90c31ba96d99e043f283d18dddaf7755a864a9","parent":"Candidates/V14.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":2600,"approx":0.0003846153846153846},...}
```
