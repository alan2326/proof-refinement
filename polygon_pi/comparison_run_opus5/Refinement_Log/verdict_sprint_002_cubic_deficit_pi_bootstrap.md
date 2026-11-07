# Verdict — sprint_002_cubic_deficit_pi_bootstrap

- **Contract:** `ProofRefinement/PolygonPi/Sprint_Contracts/sprint_002_cubic_deficit_pi_bootstrap.md`
- **Candidate:** `ProofRefinement/PolygonPi/Candidates/V2.lean` (+ `Candidates/V2/CubicDeficit.lean`,
  `Candidates/V2/DeficitMonotone.lean`)
- **Rung type:** `architectural`
- **Side:** `upper`
- **Strict improvement required:** yes

## Outcome: PASS

All gates passed in order; no failing gate.

## Gate-by-gate

1. **Write scope.** `git status --porcelain` (repo root `polygon_pi`) shows:
   - `?? ProofRefinement/PolygonPi/Candidates/V2.lean` (target file)
   - `?? ProofRefinement/PolygonPi/Candidates/V2/` (candidate's own derived-theorem dir,
     containing `CubicDeficit.lean` and `DeficitMonotone.lean`, both named in "Concrete edits
     expected")
   - `M  ProofRefinement/PolygonPi/Experience.md` (append, named in "Concrete edits expected")
   - `?? ProofRefinement/PolygonPi/Scratch/AxiomCheckV2.lean`,
     `?? ProofRefinement/PolygonPi/Scratch/bootstrap_iteration_v2.py` (scratch files, allowed)
   - `?? ProofRefinement/PolygonPi/Sprint_Contracts/sprint_002_cubic_deficit_pi_bootstrap.md` —
     a **new** file (`??`), not a modification of an existing contract, so it does not trip the
     "modification to a sprint contract" fail condition; it is this sprint's own contract,
     produced by the planner phase.
   - `M results/sprint_markers.jsonl` — pre-existing human-side harness bookkeeping (confirmed
     by `git diff`: it only gained one `sprint_start` marker line for `sprint_002`), outside
     `ProofRefinement/PolygonPi/`, ignored per instruction.
   None of `PolygonCore/`, `Proof/`, `Evaluator.py`, `scripts/`, `lemma.toml`, or any older
   candidate (`Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V1/`) were touched. PASS.

2. **Build.** `./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V2` →
   `Build completed successfully (2162 jobs).` PASS.

3. **No forbidden constructs.**
   `grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' Candidates/V2.lean` → no
   matches. The same grep against `Candidates/V2/CubicDeficit.lean` and
   `Candidates/V2/DeficitMonotone.lean` each match one line, but both are the files' own
   docstring prose ("Theorems and lemmas only — no `axiom`, no `sorry`, no oracle."), not a
   tactic invocation — confirmed by reading the surrounding lines. PASS.
   Also confirmed per the contract's own acceptance criterion: `grep -rn 'sin_gt_sub_cube'`
   over `Candidates/V2.lean` and `Candidates/V2/` returns no matches — the restricted Mathlib
   cubic is genuinely gone from the upper chain.

4. **Full evaluator run (run of record, logged).**
   `./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V2` → all twelve stages
   PASS (stage 8, secondary contract, is SKIP because no `lambdaDepth10`/`kappaDepth10` were
   declared, which is optional and expected). Confirmed appended to
   `Refinement_Log/log.jsonl` with `timestamp_utc: 2026-07-27T04:39:11.990541+00:00`.
   - `score = 329947/10000000 = 0.0329947`
   - `interval width at depth 10 = 329947/10485760000000 ≈ 3.146620e-08`
   - `incumbent = 71/100`
   - `strict_improvement = true`

5. **Contract-declared inequality.** Contract declares `Strict improvement required: yes`.
   Logged `strict_improvement = true`. PASS.

6. **Axiom closure.** Evaluator's axiom scan reports exactly `{propext, Classical.choice,
   Quot.sound}` for `polygon_pi_constant_search` — a subset of (in fact equal to) the allowed
   set, and the oracle table is empty (stage 10). PASS.

## Acceptance-criteria spot check

- `def lambda : ℝ := 29/100` and `def kappa : ℝ := 3229947/10000000`, each single-line;
  `kappa = 0.3229947 ≤ 2/3` (required bar).
- `Candidates/V2/CubicDeficit.lean` contains `theorem deficit_le (n : ℕ) : Real.pi -
  polygonLower n ≤ Real.pi ^ 3 / (96 * 4 ^ n)`, matching the required statement.
- That proof does not mention `Real.sin_gt_sub_cube` and does not use a `π / 2 ^ (n+2) ≤ 1`
  domain hypothesis (verified by reading `deficit_le`'s proof and by the substring grep above).
- `Candidates/V2/CubicDeficit.lean` contains `theorem sub_sin_le_cube_div_six (x : ℝ)
  (hx : 0 ≤ x) : x - Real.sin x ≤ x ^ 3 / 6`, with no upper-bound hypothesis on `x`.
- `lake build ProofRefinement.PolygonPi.Candidates.V2` succeeds (gate 2 above).
- Evaluator passes all twelve stages (gate 4 above).
- Axiom closure is the trusted subset (gate 6 above).
- `score = kappa - lambda = 0.0329947 < 71/100` (required bar).
- **Target met:** `kappa = 0.3229947 ≤ 33/100`, via the staged rational certification
  `polygonLower_two_lt : polygonLower 2 < 31214464/10000000` and five applications of
  `pi_le_bootstrap_step` starting from `Real.pi_le_four` (`pi_le_round_one` through
  `pi_le_round_five`).
- **Stretch met:** `kappa = 3229947/10000000 ≤ 3231/10000` and
  `score = 329947/10000000 ≤ 331/10000`, both satisfied numerically
  (`0.3229947 < 0.3231`, `0.0329947 < 0.0331`) — the candidate reached the stretch bar with
  five bootstrap rounds rather than the three the contract anticipated.

## Reproduction

```bash
./ProofRefinement/PolygonPi/scripts/polygonpi_lake_build.sh V2
grep -n 'sorry\|admit\|native_decide\|^axiom \|opaque \|unsafe ' ProofRefinement/PolygonPi/Candidates/V2.lean ProofRefinement/PolygonPi/Candidates/V2/CubicDeficit.lean ProofRefinement/PolygonPi/Candidates/V2/DeficitMonotone.lean
grep -rn 'sin_gt_sub_cube' ProofRefinement/PolygonPi/Candidates/V2.lean ProofRefinement/PolygonPi/Candidates/V2/
./ProofRefinement/PolygonPi/scripts/polygonpi_eval_candidate.sh V2
```

STATUS=VERDICT_PASS
