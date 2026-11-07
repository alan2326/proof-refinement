# Verdict — sprint_003_quintic_lower_deficit_bootstrap

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_003_quintic_lower_deficit_bootstrap.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V3.lean` (+ `Candidates/V3/QuinticDeficit.lean`,
  `Candidates/V3/CubicDeficit.lean`, `Candidates/V3/DeficitMonotone.lean`)
- **Rung type:** `architectural`
- **Side:** `lower`
- **Strict improvement required:** yes

## Outcome: PASS

All gates passed in order; no failing gate.

## Gate-by-gate

1. **Write scope.** `git status --porcelain` (repo root `polygon_pi`) shows:
   - `?? ProofRefinement/PolygonPi/Candidates/V3.lean` (target file)
   - `?? ProofRefinement/PolygonPi/Candidates/V3/` (candidate's own derived-theorem dir,
     containing `CubicDeficit.lean`, `DeficitMonotone.lean`, `QuinticDeficit.lean`, all named in
     "Concrete edits expected")
   - `M  ProofRefinement/PolygonPi/Experience.md` (append, named in "Concrete edits expected";
     `git diff` confirms it is a pure append starting after the sprint_002 "Next" note, no
     earlier content touched)
   - `?? ProofRefinement/PolygonPi/Scratch/AxiomCheckV3.lean`,
     `?? ProofRefinement/PolygonPi/Scratch/lower_bootstrap_v3.py` (scratch files, allowed)
   - `?? ProofRefinement/PolygonPi/Sprint_Contracts/sprint_003_quintic_lower_deficit_bootstrap.md`
     — a **new** file (`??`), not a modification of an existing tracked contract (confirmed via
     `git ls-files Sprint_Contracts/`, which lists only `TEMPLATE.md`, `sprint_001_*.md`,
     `sprint_002_*.md` as tracked), so it does not trip the "modification to a sprint contract"
     fail condition; it is this sprint's own contract.
   - `M results/sprint_markers.jsonl` — pre-existing human-side harness bookkeeping, outside
     `ProofRefinement/PolygonPi/`, ignored per instruction.
   None of `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, `lemma.toml`, or any older
   candidate (`Candidates/V0*.lean`, `V1*`, `V2*`) were touched. PASS.

2. **Build.** `./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V3` →
   `Build completed successfully (2163 jobs).` PASS.

3. **No forbidden constructs.**
   `grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' Candidates/V3.lean` → no
   matches. The same grep against `Candidates/V3/CubicDeficit.lean`,
   `Candidates/V3/DeficitMonotone.lean`, and `Candidates/V3/QuinticDeficit.lean` each match one
   line, but all three are the files' own docstring prose ("Theorems and lemmas only — no
   `axiom`, no `sorry`, no oracle."), not a tactic invocation — confirmed by reading the
   surrounding lines. PASS.

4. **Full evaluator run (run of record, logged).**
   `./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V3` → all twelve stages
   PASS (stage 8, secondary contract, is SKIP because no `lambdaDepth10`/`kappaDepth10` were
   declared, which is optional and expected). Confirmed appended to
   `Refinement_Log/log.jsonl` with `timestamp_utc: 2026-07-27T05:00:19.190628+00:00`.
   - `score = 98297/10000000 = 0.0098297`
   - `interval width at depth 10 = 98297/10485760000000 ≈ 9.374332e-09`
   - `incumbent = 329947/10000000` (`V2`'s score)
   - `strict_improvement = true`

5. **Contract-declared inequality.** Contract declares `Strict improvement required: yes`.
   Logged `strict_improvement = true`. PASS.

6. **Axiom closure.** Evaluator's axiom scan (stage 9) reports exactly `{propext,
   Classical.choice, Quot.sound}` for `polygon_pi_constant_search` — equal to the allowed set —
   and the oracle table (stage 10) is empty. PASS.

## Acceptance-criteria spot check

- `def lambda : ℝ := 313165/1000000` and `def kappa : ℝ := 3229947/10000000` (unchanged from
  `V2`), each single-line. Evaluator normalizes `lambda` to the reduced fraction `62633/200000`,
  which is the same rational value (`313165/1000000 = 62633/200000` after dividing by 5).
- `Candidates/V3/QuinticDeficit.lean` contains `theorem sub_sin_le_quintic_div … : Real.sin x ≤
  x - x ^ 3 / 6 + x ^ 5 / 120` (`0 ≤ x`), proved via the half-angle cosine bound and
  `monotone_of_hasDerivAt_nonneg`, with no numeric `π` hypothesis anywhere in the dependency
  chain up to that theorem (verified by reading the file).
- `Candidates/V3/QuinticDeficit.lean` contains `theorem deficit_ge (n : ℕ) : Real.pi ^ 3 /
  (96 * 4 ^ n) - Real.pi ^ 5 / (30720 * 4 ^ n * 4 ^ n) ≤ Real.pi - polygonLower n`, uniform in
  `n`, `π` symbolic.
- A theorem `pi_ge_round_five : 3141592597/1000000000 ≤ Real.pi` exists in
  `Candidates/V3/QuinticDeficit.lean`, produced entirely from the workspace's own trusted
  surface plus the five bootstrap rounds — no dependency on `Mathlib.Analysis.Real.Pi` (import
  policy already enforced by gates 1 and 3 of the evaluator run).
- `lake build ProofRefinement.PolygonPi.Candidates.V3` succeeds (gate 2 above).
- Evaluator passes all twelve stages (gate 4 above).
- Axiom closure is the trusted subset (gate 6 above).
- `strict_improvement = True` and `score = 98297/10000000 = 0.0098297 ≤ 99/10000 = 0.0099`
  (required bar); equivalently `lambda = 0.313165 ≥ 0.31316` with `kappa` unchanged at
  `0.3229947`.
- **Required floor:** `lambda = 313165/1000000 = 0.313165 ≥ 3125/10000 = 0.3125` — satisfied
  with wide margin, well clear of the deeper-radical alternative's ceiling of `0.31190` at
  depth 4.
- Target `lambda = 313165/1000000` and score `98297/10000000 = 0.0098297` were both hit exactly.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V3
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' ProofRefinement/PolygonPi/Candidates/V3.lean ProofRefinement/PolygonPi/Candidates/V3/CubicDeficit.lean ProofRefinement/PolygonPi/Candidates/V3/DeficitMonotone.lean ProofRefinement/PolygonPi/Candidates/V3/QuinticDeficit.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V3
```

STATUS=VERDICT_PASS
