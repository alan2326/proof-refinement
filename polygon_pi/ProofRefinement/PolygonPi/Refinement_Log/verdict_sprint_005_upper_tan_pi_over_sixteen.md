# Verdict — sprint_005_upper_tan_pi_over_sixteen

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_005_upper_tan_pi_over_sixteen.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V5.lean`
- **Rung type:** architectural
- **Side:** upper
- **Strict improvement required:** yes

## Outcome

**PASS.** All six evaluator gates cleared; all twelve evaluator stages returned
`PASS` (stage 8 legitimately `SKIP` — no secondary contract declared).

## Gate log

1. **Write scope.** Diffs restricted to the target file `Candidates/V5.lean`,
   the newly written `Candidates/V5/{Tan,Polygon,Taylor}.lean` (named in
   `Concrete edits expected`), `Experience.md`, `Bulletin.md`, and evaluator
   artefacts (`Refinement_Log/log.jsonl`). The user-noted expected diffs
   (`.claude/agents/*.md` model field, V1–V4 artefacts relative to HEAD from
   the harness reset) are not attributable to this sprint. No modification to
   `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, an older candidate, or
   a sprint contract. Pass.
2. **Build.** `polygonpi_lake_build.sh V5` — `Build completed successfully
   (2163 jobs).` Pass.
3. **No forbidden constructs.** `grep` matches in V5 subfiles are all inside
   doc-header comments stating the negative claim ("No `axiom`, `opaque`,
   `native_decide`, or `sorry`"). No real occurrences. Pass.
4. **Full evaluator run (logged).** All twelve stages report `PASS`
   (stage 8 `SKIP`, allowed). Pass.
5. **Contract-declared inequality.** Contract requires strict improvement;
   evaluator reports `strict_improvement=True` (score `721/12000` below
   incumbent `127/768`). Pass.
6. **Axiom closure.** Evaluator reports exactly
   `{propext, Classical.choice, Quot.sound}` — a subset of the allowed axiom
   set. Pass.

## Evaluator-reported metrics

- `score`:                       `721/12000 ≈ 0.060083333333`
- `interval width at depth 10`:  `721/12582912000 ≈ 5.729993e-08`
- `incumbent`:                   `127/768`
- `strict_improvement`:          `true`
- `axiom closure`:               `{propext, Classical.choice, Quot.sound}`

Score drop from parent: `127/768 − 721/12000 = 10107/96000 ≈ 0.10528`, a
roughly 63% relative reduction — matches the contract's projection.

Interval width at depth 10 shrinks by factor `≈ 2.75` (V4:
`127/805306368 ≈ 1.577e-07` → V5: `≈ 5.730e-08`).

## Reproduction

```bash
polygon_pi/ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V5
polygon_pi/ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V5
```
