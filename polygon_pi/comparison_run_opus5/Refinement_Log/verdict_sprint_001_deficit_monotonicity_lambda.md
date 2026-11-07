# Verdict — sprint_001_deficit_monotonicity_lambda

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_001_deficit_monotonicity_lambda.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V1.lean` (+ `Candidates/V1/DeficitMonotone.lean`)
- **Rung type:** `architectural`
- **Side:** `lower`
- **Strict improvement required:** yes

## Outcome: PASS

All gates passed in order; no failing gate.

## Gate-by-gate

1. **Write scope.** `git status --porcelain` (repo root `polygon_pi`) shows,
   restricted to files relevant to this candidate:
   - `?? ProofRefinement/PolygonPi/Candidates/V1.lean` (target file)
   - `?? ProofRefinement/PolygonPi/Candidates/V1/` (candidate's own derived-theorem dir,
     contains `DeficitMonotone.lean`)
   - `M  ProofRefinement/PolygonPi/Experience.md` (clean append of the sprint_001 entry)
   - `?? ProofRefinement/PolygonPi/Scratch/` (contains only `AxiomCheckV1.lean`, an
     `#print axioms` scratch check, not part of the candidate)
   - `?? ProofRefinement/PolygonPi/Sprint_Contracts/sprint_001_deficit_monotonicity_lambda.md`
     — this is a **new** file (`??`), not a modification of an existing sprint contract, so
     it does not trip the "modification to a sprint contract" fail condition.
   None of `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, or `Candidates/V0.lean`
   (the older candidate) were touched. PASS for the candidate's write scope.

   **Anomaly noted, not counted against this candidate:** `git status --porcelain` on the
   full repo also shows `M .claude/agents/polygonpi-refinement-{evaluator,generator,planner}.md`
   (a `model:` frontmatter field changed to `claude-opus-4-7`) and three new untracked files
   at repo root, `results/mark.sh`, `results/telemetry.py`, `results/sprint_markers.jsonl`
   (the last of these could not even be listed — `ls results/` was denied by the permission
   system). File mtimes place the `.claude/agents/*.md` edits at `2026-07-27 03:59:13 UTC`,
   which is *before* this sprint's contract file was written (`04:06:05 UTC`) and well before
   the candidate files were produced (`04:11`–`04:15 UTC`); the last git commit on the branch
   is `03:20:13 UTC`. These changes therefore predate this sprint's generator run and are not
   attributable to it — they are pre-existing dirty state in the working tree, outside
   `ProofRefinement/PolygonPi/` entirely, and outside anything this contract names. They are
   flagged here for visibility but did not factor into the PASS verdict below.

2. **Build.** `./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V1` →
   `Build completed successfully (2161 jobs).` PASS.

3. **No forbidden constructs.**
   `grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' Candidates/V1.lean` → no
   matches. The same grep against `Candidates/V1/DeficitMonotone.lean` matches one line, but
   it is the file's own docstring prose ("no `axiom`, no `sorry`, no oracle."), not a tactic
   invocation; confirmed with a word-boundary grep (`\bsorry\b|\badmit\b`) restricted to that
   same single line. PASS.

4. **Full evaluator run (run of record, logged).**
   `./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V1` → all twelve stages
   PASS (stage 8, secondary contract, is SKIP because no `lambdaDepth10`/`kappaDepth10` were
   declared, which is optional and expected). Confirmed appended to
   `Refinement_Log/log.jsonl` with `timestamp_utc: 2026-07-27T04:18:23.143027+00:00`.
   - `score = 71/100`
   - `interval width at depth 10 = 71/104857600 ≈ 6.771088e-07`
   - `incumbent = 1`
   - `strict_improvement = true`

5. **Contract-declared inequality.** Contract declares `Strict improvement required: yes`.
   Logged `strict_improvement = true`. PASS.

6. **Axiom closure.** Evaluator's axiom scan reports exactly `{propext, Classical.choice,
   Quot.sound}` for `polygon_pi_constant_search` — a subset of (in fact equal to) the allowed
   set, and the oracle table is empty. PASS.

## Acceptance-criteria spot check

- `def lambda : ℝ := 29/100` and `def kappa : ℝ := 1`, each single-line; `lambda = 29/100 ≥
  23/100` (candidate took the contract's optional stretch route via `polygonLower 2` rather
  than the required-minimum `polygonLower 1`).
- `DeficitMonotone.lean` contains `theorem deficit_ge_zero_deficit (n : ℕ) : Real.pi -
  polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n)`, proved by `induction n` from
  `deficit_step` (one-step deficit inequality), not a per-`n` Taylor estimate.
- `DeficitMonotone.lean` contains `theorem sin_mul_four_sub_cos_le (y : ℝ) (hy : 0 ≤ y) :
  Real.sin y * (4 - Real.cos y) ≤ 3 * y`, plus a packaged corollary
  `sin_mul_four_sub_cos_le_on_Ioc` on `Set.Ioc 0 (Real.pi / 8)`.
- `score = kappa - lambda = 71/100 ≤ 77/100`, strictly below parent score `1`.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V1
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' ProofRefinement/PolygonPi/Candidates/V1.lean ProofRefinement/PolygonPi/Candidates/V1/DeficitMonotone.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V1
```

STATUS=VERDICT_PASS
