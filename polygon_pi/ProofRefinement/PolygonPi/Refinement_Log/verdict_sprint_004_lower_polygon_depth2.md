# Verdict — sprint_004_lower_polygon_depth2

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_004_lower_polygon_depth2.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V4.lean`
  - Support files: `Candidates/V4/Polygon.lean`, `Candidates/V4/Tan.lean`, `Candidates/V4/Taylor.lean`
- **Rung type:** `architectural`
- **Side:** `lower`
- **Outcome:** `PASS`
- **Failing gate:** none

## Gate log

1. **Write scope.** `git status --porcelain` shows the working tree in the fresh
   post-reset state noted by the launching agent. Changes attributable to this
   sprint are only:
   - modified: `ProofRefinement/PolygonPi/Candidates/V4.lean` (target)
   - added:    `ProofRefinement/PolygonPi/Candidates/V4/Polygon.lean`
   - added:    `ProofRefinement/PolygonPi/Candidates/V4/Tan.lean`
   - added:    `ProofRefinement/PolygonPi/Candidates/V4/Taylor.lean`
   - modified: `ProofRefinement/PolygonPi/Experience.md`
   - modified: `ProofRefinement/PolygonPi/Refinement_Log/log.jsonl` (evaluator stage 12)
   - modified: `ProofRefinement/PolygonPi/Bulletin.md` (permitted per harness)

   All other diffs (V1/V2/V3 source, previous-sprint contracts and verdicts,
   `.claude/agents/*.md` `model:` field, deletions under earlier `Candidates/V*/`
   directories) predate this sprint and are attributable to the deliberate
   harness reset — confirmed by the launcher's course-correction note.
   PASS.
2. **Build.** `polygonpi_lake_build.sh V4` — `Build completed successfully (2163 jobs).` PASS.
3. **No forbidden constructs.** `grep` hits are documentation strings ("No `axiom`, ...") inside `/-! ... -/` module docstrings. No real `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, or `unsafe`. PASS.
4. **Full evaluator run — the run of record.** `polygonpi_eval_candidate.sh V4` — all twelve stages PASS.
   - `score = 127/768 = 0.165364583333`
   - `interval width at depth 10 = 127/805306368 ≈ 1.577040e-07`
   - `incumbent = 151/768` (parent V3)
   - `strict_improvement = true`
5. **Contract-declared inequality.** Contract requires `Strict improvement required: yes`. Evaluator reports `strict_improvement=True` (`127/768 < 151/768`). PASS.
6. **Axiom closure.** Reported: `{propext, Classical.choice, Quot.sound}` — exactly the permitted set, nothing else. PASS.

## Reported numbers

| field | value |
|---|---|
| score | `127/768` |
| interval width at depth 10 | `127/805306368 ≈ 1.577040e-07` |
| incumbent (parent) | `151/768` |
| `strict_improvement` | `true` |
| axiom closure | `{propext, Classical.choice, Quot.sound}` |

## Reproduction commands

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V4
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' \
  ProofRefinement/PolygonPi/Candidates/V4.lean \
  ProofRefinement/PolygonPi/Candidates/V4/*.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V4
```
