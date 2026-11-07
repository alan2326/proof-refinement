# Verdict — sprint_005_optimality_certificate

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_005_optimality_certificate.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V5.lean` (+ `Candidates/V5/Optimality.lean`,
  `Candidates/V5/CosineAnchor.lean`, `Candidates/V5/QuinticDeficit.lean`,
  `Candidates/V5/CubicDeficit.lean`, `Candidates/V5/DeficitMonotone.lean`)
- **Rung type:** `infrastructure` — the core deliverable is a converse theorem quantified over
  *all* candidates, with no score effect by construction; the gated optional items P2/P3 are
  explicitly labelled precision work (per the contract's "Honesty about the rung type").
- **Side:** `both`
- **Strict improvement required:** no

## Outcome: PASS

All gates passed in order; no failing gate.

## Gate-by-gate

1. **Write scope.** `git status --porcelain` (repo root `polygon_pi`) shows:
   - `?? ProofRefinement/PolygonPi/Candidates/V5.lean` (target file)
   - `?? ProofRefinement/PolygonPi/Candidates/V5/` (candidate's own derived-theorem dir:
     `Optimality.lean` [new, the substance of the sprint], `CosineAnchor.lean`,
     `CubicDeficit.lean`, `DeficitMonotone.lean`, `QuinticDeficit.lean` — all named in
     "Concrete edits expected")
   - `M ProofRefinement/PolygonPi/Experience.md` — explicitly inside the generator's permitted
     write scope; `Bulletin.md` unchanged (not required this sprint)
   - `?? ProofRefinement/PolygonPi/Scratch/AxiomCheckV5.lean`,
     `?? ProofRefinement/PolygonPi/Scratch/optimality_certificate_v5.py` (scratch files, allowed)
   - `?? ProofRefinement/PolygonPi/Sprint_Contracts/sprint_005_optimality_certificate.md` — a
     **new** file (`??`), not a modification of a tracked one. Confirmed by `stat`: the contract's
     mtime (05:45:48) predates `V5.lean`'s mtime (06:04:03) and the derived files' mtimes
     (05:49–05:56), i.e. it was authored by the planner before generator work began, and is
     simply not yet committed to git (sprint_004's contract was only committed as part of the
     sprint_004 commit itself — the same pattern). Not a generator edit.
   - `M results/sprint_markers.jsonl` — pre-existing human-side harness bookkeeping outside
     `ProofRefinement/PolygonPi/`, explicitly flagged as unrelated and ignored per instruction.
   None of `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, `lemma.toml`, or any older
   candidate (`V0*`–`V4*`) were touched. PASS.

2. **Build.** `./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V5` →
   `Build completed successfully (2165 jobs).` PASS.

3. **No forbidden constructs.**
   `grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' Candidates/V5.lean
   Candidates/V5/*.lean` → matches only in each derived file's own docstring prose
   ("Theorems and lemmas only — no `axiom`, no `sorry`, no oracle."), not a tactic invocation or
   declaration — confirmed by reading each surrounding line. `Candidates/V5.lean` itself: no
   matches at all. PASS.

4. **Full evaluator run (run of record, logged).**
   `./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V5` (no `--no-log`) → all
   twelve stages PASS (stage 8, secondary contract, is PASS — `polygon_pi_depth10_search` /
   P3 was declared and type-checks against `ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10`).
   Confirmed appended to `Refinement_Log/log.jsonl` with `timestamp_utc:
   2026-07-27T06:06:26.659265+00:00`, `candidate: "Candidates/V5.lean"`, `parent: "V4"`.
   - `score = 9816533/1000000000 = 0.009816533`
   - `interval width at depth 10 = 9816533/1048576000000000 ≈ 9.361775e-09`
   - `incumbent = 9816589/1000000000` (`V4`'s score, `0.009816589`)
   - `strict_improvement = true`
   - `score_secondary = 11/500000000 = 2.2e-8` (the P3 secondary-frontier interval)

5. **Contract-declared inequality.** Contract declares `Strict improvement required: no`, so this
   gate imposes no obligation. (The candidate happens to report `strict_improvement = true`
   anyway, from the optional P2 anchor, but that is not what this gate checks.) PASS (vacuous).

6. **Axiom closure.** Evaluator's axiom scan (stage 9) reports exactly `{propext,
   Classical.choice, Quot.sound}` — equal to the allowed set, with `std`-class axioms only and
   zero project axioms — and the oracle table (stage 10) is empty. PASS.

## Acceptance-criteria spot check

- `def lambda : ℝ := 313165527/1000000000` and `def kappa : ℝ := 32298206/100000000`, both
  single-line, in `Candidates/V5.lean`. `kappa = 0.32298206 ≤ 0.32298206` (equality, never worse)
  and `lambda = 0.313165527 ≥ 0.313165471` (strictly better) — both required-floor bullets
  satisfied.
- `Candidates/V5/Optimality.lean` contains `admissible_kappa_ge {lam kap : ℝ}
  (h : ValidPolygonBound lam kap) : Real.pi ^ 3 / 96 ≤ kap`, quantified over arbitrary `lam kap`.
  Read the full ten-line proof body (lines 158–175): `by_contra`, `push_neg`, `exists_nat_gt`,
  `nat_le_four_pow`, `deficit_scaled_ge`, `scaled_lt_kappa`, `linarith` — no decimal/numeric
  literal for `π` anywhere in it; every quantity is symbolic (`Real.pi ^ 3`, `Real.pi ^ 5`,
  `30720`, `4 ^ n`), matching the acceptance criterion exactly.
- It also contains `admissible_lambda_lt` (line 190) and `admissible_score_gt_rat` (line 245),
  proving `ValidPolygonBound lam kap → (9816488/1000000000 : ℝ) < kap - lam` — the P2-sharpened
  literal `9816488` (contract §5's P2 branch), consistent with `lambda`'s P2 value.
- It contains `valid_of_bracket` (line 263), and `V5.lean`'s `polygon_pi_constant_search` is
  proved through it in three lines (`valid_of_bracket (by norm_num [lambda]) lambda_lt_ceiling
  (by rw [kappa]; exact pi_cube_div_lt_sharp)`) rather than repeating `V4`'s inline argument.
- `V5.lean` states `optimum_bracket` (lines 153–156), sandwiching
  `Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2)` between `9816488/1000000000` (certified floor,
  `optimum_gt`) and `kappa - lambda` (via `admissible_score_gt polygon_pi_constant_search`).
- `lake build ProofRefinement.PolygonPi.Candidates.V5` succeeds (gate 2 above).
- Evaluator passes all twelve stages with logging (gate 4 above; contract's pre-check text says
  `--no-log`, but this task's instructions require the run-of-record to log, which was honored).
- Axiom closure is the trusted subset, oracle table empty (gate 6 above).
- `score = 9816533/1000000000 ≤ 9816589/1000000000` — satisfied (in fact a strict improvement,
  though not required).
- **P2 landed:** `lambda = 313165527/1000000000`, score `9816533/1000000000` — exactly the
  contract's optional P2 target.
- **P3 landed:** `polygon_pi_depth10_search : ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10`
  type-checks (evaluator stage 8 PASS), with `kappaDepth10 = kappa` and
  `lambdaDepth10 = 322982038/1000000000` — the P2-consistent literal from contract §6.
- `Experience.md` records measured margins for P2 (the four radical-stage margins
  `2.56e-12, 6.71e-13, 1.69e-12, 2.93e-13`) and P3, and a numeric correction to sprint 004's own
  Experience entry (kappa's true margin above the floor is `1.125e-8`, not `1.6e-9`) — read in
  full, confirmed present.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V5
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' ProofRefinement/PolygonPi/Candidates/V5.lean ProofRefinement/PolygonPi/Candidates/V5/Optimality.lean ProofRefinement/PolygonPi/Candidates/V5/CosineAnchor.lean ProofRefinement/PolygonPi/Candidates/V5/CubicDeficit.lean ProofRefinement/PolygonPi/Candidates/V5/DeficitMonotone.lean ProofRefinement/PolygonPi/Candidates/V5/QuinticDeficit.lean
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V5
```

STATUS=VERDICT_PASS
