# verdict_sprint_003_upper_tan_pi_over_eight

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_003_upper_tan_pi_over_eight.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V3.lean`
  (plus `Candidates/V3/Tan.lean`, `Candidates/V3/Taylor.lean`)
- **Rung type:** `architectural`
- **Side:** `upper`
- **Outcome:** `PASS`
- **Failing gate:** none

## Metrics (from evaluator run of record)

- `score = 151/768` (≈ `0.196614583333`)
- `interval width at depth 10 = 151/805306368` (≈ `1.875063e-07`)
- `incumbent = 5/12` (V2)
- `strict_improvement = True` (contract required `yes` — enforced)

## Axiom closure

Reported as exactly `{propext, Classical.choice, Quot.sound}` — a subset of the
allowed set. No `native_decide`, no project axiom, no `opaque`, no `sorry`.

## Gate log

1. Write scope — PASS.
   `git status --porcelain` shows changes only to permitted paths for this sprint:
   `Candidates/V3.lean`, `Candidates/V3/Tan.lean` (new), `Candidates/V3/Taylor.lean`
   (new), `Experience.md`, `Bulletin.md`. All other diffs (`.claude/agents/*.md`,
   `V1.lean`/`V2.lean` modifications, `V2/Taylor.lean` addition, deleted prior
   sprint contracts/verdicts, prior `log.jsonl` entries) are pre-existing
   harness-reset artifacts per the operator's note and are not attributable to
   this sprint.
2. Build — PASS. `polygonpi_lake_build.sh V3` completed successfully (2162 jobs);
   no Mathlib recompile.
3. Forbidden constructs — PASS. `grep` matches in `V3/Tan.lean:19` and
   `V3/Taylor.lean:18` are inside docstrings explicitly claiming *absence* of
   these constructs; no actual `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/
   `unsafe` occurrences.
4. Evaluator (12 stages) — PASS. All twelve stages green; run logged.
5. Contract-declared inequality — PASS. `strict_improvement=True`; `151/768 <
   320/768 = 5/12`.
6. Axiom closure — PASS. Subset of `{propext, Classical.choice, Quot.sound}`.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V3
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V3 --no-log
```
