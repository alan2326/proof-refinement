# verdict_sprint_001_upper_cubic_taylor

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_001_upper_cubic_taylor.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V1.lean`
- **Rung type:** `architectural`
- **Side:** `upper`
- **Outcome:** `PASS`
- **Failing gate:** none

## Numbers

- `score = 2/3` (≈ 0.666666666667)
- `interval_width_at_depth10 = 1/1572864` (≈ 6.357829e-07)
- `incumbent = 1` (parent V0)
- `strict_improvement = true` — satisfies the contract's `Strict improvement required: yes`

## Axiom closure

Reported as `{Classical.choice, Quot.sound, propext}` — exactly a subset of the
permitted `{propext, Classical.choice, Quot.sound}`. No project axioms, no
`native_decide`.

## Gate summary

1. Write scope: generator-attributable edits confined to `Candidates/V1.lean`,
   `Experience.md`, `Bulletin.md`, and the new sprint contract file. The
   `.claude/agents/*.md` diffs in `git status` are unrelated `model:` field
   updates (opus-4-7 → sonnet-5) predating the sprint; the mass deletions are
   from a pre-sprint reset that restored the tree to V0. No modification to
   `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, an older candidate, or
   another sprint contract.
2. `lake build V1`: PASS (2160 jobs, no Mathlib recompile).
3. Forbidden-construct grep on `Candidates/V1.lean`: no `sorry`, `admit`,
   `native_decide`, `axiom`, `opaque`, or `unsafe`. No `Candidates/V1/` subdir
   exists.
4. Full evaluator run: all twelve stages PASS (workspace imports, candidate
   imports, transitive closure of 2145 modules, static scan, declarations
   `lambda=0` `kappa=2/3`, compile 2.50s, type check 3.29s, secondary skipped,
   axiom scan+audit PASS, oracle table empty, score/incumbent recorded, log
   appended).
5. Contract inequality: `strict_improvement=true` as required.
6. Axiom closure: subset check PASS.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V1
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' \
  ProofRefinement/PolygonPi/Candidates/V1.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V1
```
