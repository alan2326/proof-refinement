# Verdict: sprint_022

**Contract**: ProofRefinement/Lemma54/Sprint_Contracts/sprint_022.md
**Candidate**: ProofRefinement/Lemma54/Candidates/V17.lean
**Generator-reported STATUS**: READY_FOR_EVALUATION
**Outcome**: PASS
**Failing gate**: none
**Failure detail**: n/a

## Gates run

| Gate | Outcome | Detail |
|---|---|---|
| G1 (compile) | PASS | `lake env lean V17.lean` exited 0, no error lines (4.2s) |
| G2 (no sorry) | PASS | No `sorry` occurrences in V17.lean |
| G3 (write scope) | PASS | Changed files: `Experience.md` (always-allowed), `Scratch/sprint_022_research_findings.md` (always-allowed — under Scratch/), `Candidates/V17.lean` (named in contract), `Scratch/sprint_022_research.py` (named in contract); `.claude/worktrees/` gitlink entries show `M` in `git status --porcelain` but `git diff --name-only HEAD` confirms no actual diff content — pre-existing gitlink artefact, not a Generator change |
| G4 (no new axioms) | PASS | V17 axiom set identical to V16: same 12 seed axioms + 2 oracle axioms (`h_joint_phi_phip_invD2_oracle`, `h_uzz_phi_sq_oracle`); no new non-oracle axioms introduced |
| G5 (per-cand evaluator) | PASS | `uv run Evaluator.py --file V17.lean` exited 0, `pass: true`, score 1/3500; both oracle axioms verified (declared bound >= oracle bound for both) |
| G6 (score) | PASS | Score 1/3500 preserved as expected for wildcard sprint; no regression vs sprint_021 floor of 1/3500 |

## Notes

This is a wildcard research sprint (every-4-sprints cadence; last wildcard was sprint_017).
V17 is byte-identical to V16 (Cr_val = 1/3500 preserved). The primary deliverable is
`Scratch/sprint_022_research_findings.md` (74 lines, >= 30), which contains a committed
`L1-RUN` recommendation: at n_per_edge=4096, joint drops from 1.9887e-04 to 6.2504e-05
and uzz_phi_sq drops to 4.2885e-05, suggesting sprint_023 should be an
oracle-precision-tightening sprint.

The G5 evaluator had an initial failure due to a stale/missing .olean (the `lake env lean`
pass in G1 does not write the .olean to the cache path). A `lake build` was run to populate
the .olean before the G4/G5 evaluator runs. G1 is confirmed passing (exit 0, no error lines)
independently of the .olean issue.

## REPRODUCED-WITH

```
lake commit: 4af6cf4c5fb07c95efca47779be4a3a14f11c5f8
log entry:   {"timestamp":"2026-04-30T10:04:47Z","lemma":"lemma_5_4","candidate":"Candidates/V17.lean","candidate_sha256":"f81f92d78880506b306bf10a8920afc65c6b5dd62320c1e7bad6948e85a20155","parent":"Candidates/V0.lean","status":"ok","score_field":"Cr_val","score":{"numer":1,"denom":3500,"approx":0.00028571428571428574},...}
```
