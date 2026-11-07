# Sprint 006: Tighten the rational `R` upper bound from `4/3` to `6/5` (using `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9`); drop `Cr_val` from `1451520000` to `1231718400`

**Created**: 2026-04-30 04:05 by Planner
**Parent candidate**: `Candidates/V3.lean`
**Target file**: `Candidates/V4.lean`
**Direction**: R-rationalisation-tighten (V3 bounded `R_val_paper(23/25) = sinh(49/50) ≤ sinh(1) ≤ 4/3` using the loose `Real.exp_one_lt_three`. The `4/3` step is the dominant slack: true `sinh(1) ≈ 1.1752` lives well below `4/3 ≈ 1.333`, costing ≈ 18% on `R(R+1)`. Replacing the upper bound with `6/5` — provable from Mathlib's tighter `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9` — captures most of that slack without changing the proof structure, the `Cr_tight` formula, or the rectangle/M-oracle witnesses.)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V4.lean` (parent: V3) that replaces the helper lemma `R_val_paper_le_four_thirds` with a tighter `R_val_paper_le_six_fifths : R_val_paper SearchConfig.r ≤ 6/5` (proved via `Real.sinh_le_sinh` reducing to `sinh(1) ≤ 6/5`, then via `Real.sinh_eq` + `Real.exp_one_lt_d9` + `Real.exp_one_gt_d9`), redefines `Cr_val := 1231718400` (= `16 · 432² · (6/5) · (11/5) / (2/25)²`), and adapts the monotonicity step in `lemma_5_4_search` to use the new helper — taking `score.approx` from `1.45152·10⁹` to `1.231718·10⁹`, a 1.178× reduction (≈ 15.1% off the V3 baseline) in one move.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_R_convexity.py` (mpmath at 50 dps + `Fraction` exact arithmetic) shows `Cr_val = 16·M²·R·(R+1)/(1−r)²` with `M=432`, `r=23/25`, `R=4/3` (V3) gives `1451520000`, while `R=6/5` gives **exactly** `1231718400` (integer); intermediate `R=11/10 ≈ 1.1` would give an even better `1077753600` but is not provable from `Real.exp_one_lt_d9` (since `sinh(1) ≈ 1.17520119 > 11/10`), and `R=59/50 ≈ 1.18` gives `1200178944` with a very tight nlinarith margin (≈ 0.0096 vs `6/5`'s ≈ 0.0496) that risks proof brittleness. The `R=6/5` bound is provable from existing Mathlib lemmas only: `Real.exp_one_lt_d9 : exp 1 < 2.7182818286` and `Real.exp_one_gt_d9 : 2.7182818283 < exp 1` give `e − 1/e < 2.7182818286 − 1/2.7182818286 ≈ 2.3504`, comfortably below the `12/5 = 2.4` threshold required for `(e − 1/e)/2 ≤ 6/5` — verified in the Scratch script's printout `Margin: 2.4 - 2.3504 = 0.0496`. No new axioms; the audited set stays at 3 Lean primitives + 12 trusted analytic + `h_M_oracle` + `h_oracle_domain_contains_image`, the same as V3.

## Concrete edits expected

- `ProofRefinement/Lemma54/Candidates/V4.lean`: created as a copy of `Candidates/V3.lean` with the following minimal, surgical changes (no structural rewrites):
  1. Header comment block updated: declare `-- @parent Candidates/V3.lean`, `-- @sprint Sprint_Contracts/sprint_006.md`, and explain that V4 tightens V3's `R_val_paper ≤ 4/3` rationalisation to `R_val_paper ≤ 6/5` via `Real.exp_one_lt_d9`/`Real.exp_one_gt_d9` (already exposed by Mathlib's `Mathlib.Analysis.Complex.ExponentialBounds` import that V3 already pulls in).
  2. Replace the literal `def Cr_val : ℝ := 1451520000` with `def Cr_val : ℝ := 1231718400`. The arithmetic identity `1231718400 = 16 · 432² · (6/5) · (11/5) / (2/25)² = 16 · 186624 · (66/25) / (4/625) = 186624 · 6600 = 1231718400` was verified exactly via `Fraction` in `Scratch/planner_R_convexity.py`. Keep the docstring style consistent with V3's; update the rational decomposition comment.
  3. `theorem Cr_val_nn` body unchanged structurally (`by unfold Cr_val; norm_num` continues to work since `0 ≤ 1231718400` is `norm_num`-trivial).
  4. **Replace** the helper lemma `R_val_paper_le_four_thirds` with a new helper `R_val_paper_le_six_fifths`. The proof structure mirrors V3's (so the Generator can copy and edit, not rewrite):
     ```
     /-- `R_val_paper (23/25) = sinh (49/50) ≤ 6/5`. Proved via
         `Real.sinh_le_sinh` (monotonicity, since `49/50 ≤ 1`) and
         `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9` (giving
         `sinh 1 = (exp 1 − exp(−1))/2 ≤ (2.7182818286 − 1/2.7182818286)/2
         ≈ 1.1752 ≤ 6/5 = 1.2`). -/
     theorem R_val_paper_le_six_fifths :
         Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 6 / 5 := by
       unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
       have h_le_one : (3 + (23 : ℝ) / 25) / 4 ≤ 1 := by norm_num
       have h_sinh_mono :
           Real.sinh ((3 + (23 : ℝ) / 25) / 4) ≤ Real.sinh 1 :=
         Real.sinh_le_sinh.mpr h_le_one
       have h_sinh_one : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 :=
         Real.sinh_eq 1
       have h_exp_neg : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
       have h_exp_lt_d9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
       have h_exp_gt_d9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
       have h_exp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
       have h_sinh_one_le : Real.sinh 1 ≤ 6 / 5 := by
         rw [h_sinh_one, h_exp_neg]
         rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
         -- Goal: Real.exp 1 - (Real.exp 1)⁻¹ ≤ 6/5 * 2 = 12/5
         have h_e_inv_pos : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr h_exp_pos
         have h_mul : Real.exp 1 * (Real.exp 1)⁻¹ = 1 :=
           mul_inv_cancel₀ (ne_of_gt h_exp_pos)
         -- From e < 2.7182818286 and e > 2.7182818283:
         --   e - 1/e ≤ 2.7182818286 - 1/2.7182818286
         --        = 2.7182818286 - 0.36787944127...
         --        ≈ 2.35040238 < 12/5 = 2.4 ✓ (margin ≈ 0.0496).
         nlinarith [h_exp_lt_d9, h_exp_gt_d9, h_exp_pos, h_e_inv_pos, h_mul,
                    sq_nonneg (Real.exp 1 - 2.7182818286),
                    sq_nonneg (Real.exp 1 - (Real.exp 1)⁻¹)]
       exact le_trans h_sinh_mono h_sinh_one_le
     ```
     If `nlinarith` does not close the goal with the listed hints, the Generator may add `mul_pos h_exp_pos h_exp_pos` or `mul_self_nonneg (Real.exp 1 - 1)` and similar, but should not change the high-level structure. The numerical margin is ≈ 0.05 — well within `nlinarith`'s typical comfort zone.
  5. In `theorem lemma_5_4_search`: rename the local `hR_le` reference and the auxiliary `hR_le'` re-binding from `R_val_paper_le_four_thirds` / `… ≤ 4/3` to `R_val_paper_le_six_fifths` / `… ≤ 6/5`. The `unfold Cr_val M_val ... SearchConfig.r` block stays the same; only the literal numbers in the final `nlinarith` call need updating: V3's hints `sq_nonneg (R - 4/3)` etc. become `sq_nonneg (R - 6/5)` (and `nlinarith` should still close the polynomial goal `16·432²·R·(R+1) ≤ 1231718400·(2/25)²` given `0 ≤ R ≤ 6/5`). The `set R := …` and `rw [h_1m]` / `rw [div_le_iff₀ …]` lines remain byte-identical.
  6. **No** edits to `M_val`, `delta_val`, `B_val`, `oracle_domain`, `h_M_oracle`, or `h_oracle_domain_contains_image`. Numeric witnesses unchanged from V1/V2/V3.

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_006` summarising the R-rationalisation tightening (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V4.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V4.lean` (new) plus optional appends to `Experience.md` / `Bulletin.md`. **No edits** to `Proof/Lib/Lemma54_Paper*.lean`, `Candidates/V0.lean`, `V1.lean`, `V2.lean`, `V3.lean`, `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, or `ProofGraph/`.
2. `lake env lean ProofRefinement/Lemma54/Candidates/V4.lean` exits 0 (the file compiles cleanly, no `sorry` survives), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V4.lean` exits 0 with `"status":"ok"` in the appended JSON line.
3. The new entry's `score.approx` is finite and equals `1231718400.0` exactly (i.e. `score.numer/score.denom == 1231718400/1`); the `axioms_used` list contains exactly the 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives (no new axiom, no `sorryAx`). The score is strictly less than V3's `1451520000`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Modify `Proof/Lib/Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, or any other file in `Proof/Lib/`. The `Cr_tight` chain from sprint_004 is shared infrastructure and stays untouched.
- Modify `Candidates/V0.lean`, `V1.lean`, `V2.lean`, `V3.lean`, `Sprint_Contracts/sprint_001.md` through `sprint_005.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script.
- Pick a different `R_rat` than `6/5` (so a different `Cr_val` than `1231718400`) without first justifying it numerically in `Scratch/`. The `R_rat = 11/10` candidate would yield `Cr_val = 1077753600` (a tighter score) but `sinh(1) ≤ 11/10` is **NOT** provable from current Mathlib (true `sinh(1) ≈ 1.1752 > 11/10`); `R_rat = 59/50` is provable but with a brittle ≈ 0.0096 nlinarith margin. `6/5` is the chosen optimum: a clean rational, safe ≈ 0.0496 margin, and a 1.178× reduction.
- Restructure or factor `lemma_5_4_paper_on_domain_tight`'s proof; treat it as a fixed dependency (same as V3).
- Change the helper lemma name to anything other than `R_val_paper_le_six_fifths` (the contract's acceptance hooks depend on the new helper existing under a name the Generator can document in `Experience.md`).

## Time budget

≤ 25 minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
