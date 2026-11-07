# Verdict — sprint_004_cosine_anchor_pi_inversion

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_004_cosine_anchor_pi_inversion.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V4.lean` (+ `Candidates/V4/CosineAnchor.lean`,
  `Candidates/V4/QuinticDeficit.lean`, `Candidates/V4/CubicDeficit.lean`,
  `Candidates/V4/DeficitMonotone.lean`)
- **Rung type:** `architectural`
- **Side:** `both` (kappa is the substantive move; lambda is a free literal widening)
- **Strict improvement required:** yes

## Outcome: PASS

All gates passed in order; no failing gate.

## Gate-by-gate

1. **Write scope.** `git status --porcelain` (repo root `polygon_pi`) shows:
   - `?? ProofRefinement/PolygonPi/Candidates/V4.lean` (target file)
   - `?? ProofRefinement/PolygonPi/Candidates/V4/` (candidate's own derived-theorem dir:
     `CosineAnchor.lean`, `CubicDeficit.lean`, `DeficitMonotone.lean`, `QuinticDeficit.lean`, all
     named in "Concrete edits expected")
   - `M ProofRefinement/PolygonPi/Experience.md` and `M ProofRefinement/PolygonPi/Bulletin.md`
     — both explicitly inside the generator's permitted write scope per this task's
     instructions
   - `?? ProofRefinement/PolygonPi/Scratch/AxiomCheckV4.lean`,
     `?? ProofRefinement/PolygonPi/Scratch/CheckAnchor.lean`,
     `?? ProofRefinement/PolygonPi/Scratch/cosine_anchor_v4.py` (scratch files, allowed)
   - `?? ProofRefinement/PolygonPi/Sprint_Contracts/sprint_004_cosine_anchor_pi_inversion.md`
     — a **new** file (`??`), confirmed by `ls Sprint_Contracts/` (sprint_001–004 all present,
     only sprint_004 untracked in `git status`) — this is the sprint's own contract, not a
     modification of an existing tracked one
   - `M results/sprint_markers.jsonl` — pre-existing human-side harness bookkeeping outside
     `ProofRefinement/PolygonPi/`, explicitly flagged as unrelated and ignored per instruction
   None of `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, `lemma.toml`, or any older
   candidate (`V0*`, `V1*`, `V2*`, `V3*`) were touched. PASS.

2. **Build.** `./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V4` →
   `Build completed successfully (2164 jobs).` PASS.

3. **No forbidden constructs.**
   `grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' Candidates/V4.lean
   Candidates/V4/*.lean` → matches only in the four derived files' own docstring prose
   ("Theorems and lemmas only — no `axiom`, no `sorry`, no oracle."), not a tactic invocation or
   declaration — confirmed by reading each surrounding line. `Candidates/V4.lean` itself: no
   matches at all. PASS.

4. **Full evaluator run (run of record, logged).**
   `./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V4` (no `--no-log`) → all
   twelve stages PASS (stage 8, secondary contract, is SKIP because no
   `lambdaDepth10`/`kappaDepth10` were declared, which is optional and expected). Confirmed
   appended to `Refinement_Log/log.jsonl` with `timestamp_utc:
   2026-07-27T05:26:21.915424+00:00`, `candidate: "Candidates/V4.lean"`, `parent: "V3"`.
   - `score = 9816589/1000000000 = 0.009816589`
   - `interval width at depth 10 = 9816589/1048576000000000 ≈ 9.361829e-09`
   - `incumbent = 98297/10000000` (`V3`'s score, `0.0098297`)
   - `strict_improvement = true`

5. **Contract-declared inequality.** Contract declares `Strict improvement required: yes`.
   Logged `strict_improvement = true`. PASS.

6. **Axiom closure.** Evaluator's axiom scan (stage 9) reports exactly `{propext,
   Classical.choice, Quot.sound}` for `polygon_pi_constant_search` — equal to the allowed set,
   with `std` (project) axiom count zero — and the oracle table (stage 10) is empty. PASS.

## Acceptance-criteria spot check

- `def lambda : ℝ := 313165471/1000000000` and `def kappa : ℝ := 32298206/100000000`, both
  single-line. Evaluator normalizes `kappa` to `16149103/50000000`, the same rational value
  (divide by 2).
- Required floor: `kappa = 0.32298206 ≤ 0.3229830` and `lambda = 0.313165471 ≥ 0.313165471` —
  both satisfied (lambda meets the floor exactly).
- The candidate took the contract's **optional stretch** branch: `kappa = 32298206/100000000`
  rather than the base target `3229821/10000000`, valid because `pi_le_sharp` in
  `CosineAnchor.lean` lands exactly at `π ≤ 3.1415926848` and `pi_cube_div_lt_sharp` (checked by
  `norm_num`/`linarith` inside the type-checked proof) certifies `π ^ 3 / 96 < 32298206/100000000`
  with margin `1.62e-9` above the permanent floor — the contract's own pre-stated fallback
  condition. Resulting score `0.009816589` beats the base-target prediction of `0.009816629`,
  both against the theoretical optimum `0.00981651991…`.
- `Candidates/V4/CosineAnchor.lean` contains `theorem pi_le_sharp : Real.pi ≤
  31415926848/10000000000`, proved by `by_contra` + the anchor `cos_pi_div_64_gt` +
  `quartic_antitone` + a rational comparison — no bootstrap iteration, and neither
  `polygonLower` nor `deficit_le` appears anywhere in the file (confirmed by reading the file in
  full; only `cos_le_quartic`, `Real.cos_pi_over_two_pow`, `Real.sqrtTwoAddSeries_succ`/`_one`,
  and `Real.pi_le_four`/`Real.pi_pos` are consumed).
- The five radical stages (`s1_gt` … `s5_gt`) are each stated at twelve decimal places and each
  is a single `nlinarith` with the prescribed three hints (square identity, non-negativity,
  previous stage); no stage needed extra digits beyond the contract's table.
- `Candidates/V4/{DeficitMonotone,CubicDeficit,QuinticDeficit}.lean` are content-identical to
  `V3`'s versions apart from the namespace rename and one added clarifying docstring sentence
  each (`diff` confirms only that one-line prose difference per file; no lemma statement or
  proof term differs).
- `lake build ProofRefinement.PolygonPi.Candidates.V4` succeeds (gate 2 above).
- Evaluator passes all twelve stages (gate 4 above).
- Axiom closure is the trusted subset, oracle table empty (gate 6 above).
- `score = 9816589/1000000000 = 0.009816589 < 98297/10000000 = 0.0098297` (strict improvement,
  enforced by the contract) — satisfied.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V4
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' ProofRefinement/PolygonPi/Candidates/V4.lean ProofRefinement/PolygonPi/Candidates/V4/CosineAnchor.lean ProofRefinement/PolygonPi/Candidates/V4/CubicDeficit.lean ProofRefinement/PolygonPi/Candidates/V4/DeficitMonotone.lean ProofRefinement/PolygonPi/Candidates/V4/QuinticDeficit.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V4
```

STATUS=VERDICT_PASS
