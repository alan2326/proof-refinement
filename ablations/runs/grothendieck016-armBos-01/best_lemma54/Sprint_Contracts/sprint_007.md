# Sprint 007: Bound `R_val_paper(23/25) = sinh(49/50)` directly via `Real.exp_bound`, dropping `Cr_val` from `1231718400` to `1153569600`

**Created**: 2026-04-30 03:50 by Planner
**Parent candidate**: `Candidates/V4.lean`
**Target file**: `Candidates/V5.lean`
**Direction**: sinh-direct-tighten (V4 used the loose chain `sinh(49/50) ≤ sinh(1) ≤ 6/5` via `Real.sinh_le_sinh` then `Real.exp_one_lt_d9`. The first step is the dominant slack: the actual `sinh(49/50) ≈ 1.14457` lives ≈ 0.011 below `sinh(1) ≈ 1.17520`, costing ≈ 6% on `R(R+1)`. V5 bounds `sinh(49/50)` *directly* using `Real.exp_bound` on the Taylor-truncated series at `x = 49/50` and `x = -49/50`, capturing that slack with a clean proof technique. Distinct from sprint_006's "R-rationalisation-tighten" axis: that one tightened the `sinh(1) → rational` step; this one removes the unnecessary `sinh(49/50) ≤ sinh(1)` step entirely.)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V5.lean` (parent: V4) that replaces the helper lemma `R_val_paper_le_six_fifths` with a tighter `R_val_paper_le_twentythree_twentieths : R_val_paper SearchConfig.r ≤ 23/20` (proved by directly bounding `sinh(49/50) = (exp(49/50) − exp(−49/50))/2 ≤ 23/20` via `Real.exp_bound` at `n = 10` Taylor truncation, NOT going through `sinh(1)`), redefines `Cr_val := 1153569600` (= `16 · 432² · (23/20) · (43/20) / (2/25)²`), and adapts the monotonicity step in `lemma_5_4_search` to use the new helper — taking `score.approx` from `1.231718·10⁹` to `1.153570·10⁹`, a 1.0677× reduction (≈ 6.34% off the V4 baseline) in one move.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_007_pick_R.py` (mpmath at 50 dps + `Fraction` exact arithmetic) shows `Cr_val = 16·M²·R·(R+1)/(1−r)²` with `M = 432`, `r = 23/25`, `R = 6/5` (V4) gives `1231718400`, while `R = 23/20` gives **exactly** `1153569600` (integer); the analytic floor at `R = sinh(49/50) ≈ 1.144573` is `≈ 1.144·10⁹`, leaving only ≈ 7.65% room — V5 captures `(1231718400 − 1153569600) / (1231718400 − 1144·10⁶) ≈ 89%` of that remaining gap. The bound `sinh(49/50) ≤ 23/20` is provable with comfortable nlinarith margin: `Real.exp_bound` at depth `n = 10` gives `|exp(49/50) − approx_x| ≤ (49/50)¹⁰·11/(10!·10) ≈ 2.48·10⁻⁷` and similarly for `exp(−49/50)`, yielding worst-case `exp(49/50) − exp(−49/50) ≤ 2.289145598... < 23/10 = 2.3` with margin ≈ `0.01085` — verified in the Scratch script's printout `Worst case e^x − e^−x ≤ 2.2891456..., Margin to 2.3: 0.01085`. No new axioms; the audited set stays at 3 Lean primitives + 12 trusted analytic + `h_M_oracle` + `h_oracle_domain_contains_image`, identical to V4.

## Concrete edits expected

- `ProofRefinement/Lemma54/Candidates/V5.lean`: created as a copy of `Candidates/V4.lean` with the following minimal, surgical changes (no structural rewrites):

  1. Header comment block updated: declare `-- @parent Candidates/V4.lean`, `-- @sprint Sprint_Contracts/sprint_007.md`, and explain that V5 replaces V4's `sinh(49/50) ≤ sinh(1) ≤ 6/5` chain with a direct bound `sinh(49/50) ≤ 23/20` via `Real.exp_bound` (depth 10 Taylor on `±49/50`), and that the score drops to `1153569600` (a 6.34% reduction).

  2. Replace the literal `def Cr_val : ℝ := 1231718400` with `def Cr_val : ℝ := 1153569600`. The arithmetic identity `1153569600 = 16 · 432² · (23/20) · (43/20) / (2/25)² = 16 · 186624 · (989/400) / (4/625) = 186624 · 6181.25 = 1153569600` was verified exactly via `Fraction` in `Scratch/planner_007_pick_R.py`. Update the docstring comment to state the new rational decomposition.

  3. `theorem Cr_val_nn` body unchanged structurally (`by unfold Cr_val; norm_num` continues to work since `0 ≤ 1153569600` is `norm_num`-trivial).

  4. **Replace** the helper lemma `R_val_paper_le_six_fifths` with a new helper `R_val_paper_le_twentythree_twentieths`. The recommended proof structure (the Generator may adjust tactic details but should preserve the high-level approach):

     ```
     /-- `R_val_paper (23/25) = sinh (49/50) ≤ 23/20`. Proved by directly
         bounding the two exponentials in `sinh(49/50) = (exp(49/50) − exp(−49/50))/2`
         via `Real.exp_bound` at depth `n = 10` (Taylor truncation tolerance
         ≈ 2.48·10⁻⁷ on each side, sum ≈ 5·10⁻⁷, safely below the
         ≈ 0.011 nlinarith margin against `2.3`). -/
     theorem R_val_paper_le_twentythree_twentieths :
         Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 23 / 20 := by
       unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
       -- Goal: Real.sinh ((3 + 23/25)/4) ≤ 23/20.
       -- Step 0: rewrite the argument as 49/50 (norm_num).
       have h_arg : (3 + (23 : ℝ) / 25) / 4 = 49 / 50 := by norm_num
       rw [h_arg]
       -- Step 1: sinh(49/50) = (exp(49/50) − exp(−49/50)) / 2.
       have h_sinh : Real.sinh (49 / 50 : ℝ) =
           (Real.exp (49 / 50) - Real.exp (-(49 / 50))) / 2 := Real.sinh_eq _
       rw [h_sinh]
       -- Step 2: bound `Real.exp (49/50)` from above via `Real.exp_bound'`
       --   (specialized to `0 ≤ x ≤ 1`, n = 10).
       --   `exp x ≤ ∑_{m<10} x^m/m! + x^10·11/(10!·10)`.
       have hx_nn : (0 : ℝ) ≤ 49 / 50 := by norm_num
       have hx_le_one : (49 : ℝ) / 50 ≤ 1 := by norm_num
       have h_upper :
           Real.exp (49 / 50 : ℝ) ≤
             (Finset.range 10).sum (fun m => (49 / 50 : ℝ) ^ m / m.factorial)
               + (49 / 50 : ℝ) ^ 10 * (10 + 1 : ℝ) / ((Nat.factorial 10 : ℝ) * 10) :=
         Real.exp_bound' hx_nn hx_le_one (by decide : 0 < 10)
       -- Step 3: bound `Real.exp (-(49/50))` from below.
       --   By `Real.exp_bound` at depth 10 with `|−49/50| ≤ 1`:
       --   `|exp(−49/50) − ∑_{m<10} (−49/50)^m/m!| ≤ (49/50)^10·11/(10!·10)`.
       --   The lower-bound side of the absolute inequality gives:
       --   `exp(−49/50) ≥ ∑_{m<10} (−49/50)^m/m! − (49/50)^10·11/(10!·10)`.
       have h_abs_le_one : |(-(49 / 50) : ℝ)| ≤ 1 := by
         rw [abs_neg]; rw [abs_of_nonneg hx_nn]; exact hx_le_one
       have h_bound_neg :
           |Real.exp (-(49 / 50 : ℝ)) -
              (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial)|
             ≤ |(-(49 / 50) : ℝ)| ^ 10 *
                 (Nat.succ 10 / ((Nat.factorial 10 : ℝ) * 10)) :=
         Real.exp_bound h_abs_le_one (by decide : 0 < 10)
       -- Step 4: combine via nlinarith. The two Taylor sums are explicit
       -- rationals; norm_num can pin them down. The tolerance and
       -- 2.3-target both reduce to rational comparisons.
       have h_tol_eq :
           |(-(49 / 50) : ℝ)| ^ 10 *
             (Nat.succ 10 / ((Nat.factorial 10 : ℝ) * 10)) =
           (49 / 50 : ℝ) ^ 10 * 11 / ((Nat.factorial 10 : ℝ) * 10) := by
         rw [abs_neg, abs_of_nonneg hx_nn]; push_cast; ring
       -- Concrete numerical bound: assemble Taylor sums and nlinarith.
       have h_lower :
           (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial)
             - (49 / 50 : ℝ) ^ 10 * 11 / ((Nat.factorial 10 : ℝ) * 10)
             ≤ Real.exp (-(49 / 50 : ℝ)) := by
         have := abs_sub_le_iff.mp (h_tol_eq ▸ h_bound_neg)
         linarith [this.2]
       -- Final: (exp(49/50) - exp(-49/50)) / 2 ≤ 23/20.
       -- Sufficient: exp(49/50) - exp(-49/50) ≤ 23/10. Use h_upper and h_lower:
       --   exp(49/50) ≤ S+ + tol;   -exp(-49/50) ≤ -(S- - tol) = tol - S-.
       --   Sum: ≤ (S+ - S-) + 2·tol.
       --   With S+ - S- = (sum_{m<10} 2·(49/50)^m/m!  for odd m) — this
       --   is a concrete rational that `norm_num` can simplify to a
       --   fraction below 2.3 - 2·tol.
       -- nlinarith with the two bounds and a `norm_num`-computed value
       -- of the rational tail closes the goal.
       have h_two_pos : (0 : ℝ) < 2 := by norm_num
       rw [div_le_iff₀ h_two_pos]
       -- Goal: Real.exp (49/50) - Real.exp (-(49/50)) ≤ 23/20 * 2 = 23/10.
       nlinarith [h_upper, h_lower,
                  Real.exp_pos (49 / 50 : ℝ),
                  Real.exp_pos (-(49 / 50) : ℝ),
                  Nat.factorial_pos 10]
     ```

     If the `norm_num`/`nlinarith` combination cannot evaluate the depth-10 Taylor sums symbolically (they involve `(49/50)^m` for `m = 0..10`, which `norm_num` should handle but may be slow), the Generator may add explicit rational evaluations of `(Finset.range 10).sum (fun m => (49/50)^m / m.factorial)` and the analogous alternating sum as `have` lemmas, then feed the literal rationals to `nlinarith`. The `Nat.factorial 10 = 3628800` is a literal `norm_num` should reduce. **The key constraint: stay at depth 10** — it's the smallest depth where the tolerance (≈ `2.48·10⁻⁷`) fits comfortably below the 0.01085 margin. Lower depths (e.g., `n = 6`, tolerance ≈ `4.6·10⁻⁴`) would still work but have a tighter margin and are more nlinarith-brittle.

  5. In `theorem lemma_5_4_search`: rename the local `hR_le` reference and the auxiliary `hR_le'` re-binding from `R_val_paper_le_six_fifths` / `… ≤ 6/5` to `R_val_paper_le_twentythree_twentieths` / `… ≤ 23/20`. The `unfold Cr_val M_val ... SearchConfig.r` block stays the same; only the literal numbers in the final `nlinarith` call need updating: V4's hints `sq_nonneg (R - 6/5)` etc. become `sq_nonneg (R - 23/20)` (and `nlinarith` should still close the polynomial goal `16·432²·R·(R+1) ≤ 1153569600·(2/25)²` given `0 ≤ R ≤ 23/20`, since `R·(R+1) ≤ (23/20)·(43/20) = 989/400 = 2.4725` is exactly the bound the right-hand side encodes). The `set R := …` and `rw [h_1m]` / `rw [div_le_iff₀ …]` lines remain byte-identical.

  6. **No** edits to `M_val`, `delta_val`, `B_val`, `oracle_domain`, `h_M_oracle`, or `h_oracle_domain_contains_image`. Numeric witnesses unchanged from V1/V2/V3/V4.

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_007` summarising the direct-sinh bound (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V5.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V5.lean` (new) plus optional appends to `Experience.md` / `Bulletin.md`. **No edits** to `Proof/Lib/Lemma54_Paper*.lean`, `Candidates/V0.lean`, `V1.lean`, `V2.lean`, `V3.lean`, `V4.lean`, `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, or `ProofGraph/`.

2. `lake env lean ProofRefinement/Lemma54/Candidates/V5.lean` exits 0 (the file compiles cleanly, no `sorry` survives), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V5.lean` exits 0 with `"status":"ok"` in the appended JSON line.

3. The new entry's `score.approx` is finite and equals `1153569600.0` exactly (i.e. `score.numer/score.denom == 1153569600/1`); the `axioms_used` list contains exactly the 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives (no new axiom, no `sorryAx`). The score is strictly less than V4's `1231718400`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Modify `Proof/Lib/Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, or any other file in `Proof/Lib/`. The `Cr_tight` chain from sprint_004 is shared infrastructure and stays untouched.
- Modify `Candidates/V0.lean` through `V4.lean`, `Sprint_Contracts/sprint_001.md` through `sprint_006.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script.
- Pick a different `R_rat` than `23/20` (so a different `Cr_val` than `1153569600`) without first justifying it numerically in `Scratch/`. Tighter rationals (e.g. `R_rat = 1147/1000` saves an extra ~0.4%) shrink the nlinarith margin from `0.01085` toward `0.0024`, increasing risk of proof brittleness; looser rationals (e.g. `R_rat = 29/25 = 1.16`) sacrifice score. `23/20` is the chosen optimum: clean fraction, integer Cr_val, generous ≈ 0.0108 margin, ≈ 6.34% reduction.
- Use the indirect `sinh(49/50) ≤ sinh(1) ≤ rational` route. The whole point of this sprint is the *direct* bound, which is the new technique. Falling back to the indirect route via `Real.sinh_le_sinh` + `Real.exp_one_lt_d9` would either reproduce V4's `6/5` ceiling or require more work for marginal gain.
- Restructure or factor `lemma_5_4_paper_on_domain_tight`'s proof; treat it as a fixed dependency (same as V4).
- Change the helper lemma name to anything other than `R_val_paper_le_twentythree_twentieths` (or a close variant clearly named for the `23/20` ceiling); the contract's review hooks depend on a recognisably-named helper.

## Time budget

≤ 30 minutes runtime; soft cap 75% of context. (Slightly larger than sprint_006's 25 min budget because the depth-10 Taylor manipulation is more involved than the `sinh(1)` route, but still well within a single Generator pass.)

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
