# Sprint 005: Define `Cr_val` as the rational upper bound `1451520000` (= `Cr_tight` at `R = 4/3`); recover sprint_004's score gain through a directly-scorable rational

**Created**: 2026-04-30 03:25 by Planner
**Parent candidate**: `Candidates/V2.lean`
**Target file**: `Candidates/V3.lean`
**Direction**: Cr-formula-tighten via rational-rationalisation (sprint_004 added the `Cr_tight` proof chain in shared infra; the score gate failed only because `Cr_val := Cr_tight ... (R_val_paper r)` is symbolically `sinh`-valued and the per-candidate Evaluator's `_eval_rational` cannot evaluate `sinh`. Replace with a literal rational `Cr_val` that the proof shows dominates `Cr_tight` at the chosen tuple.)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V3.lean` (parent: V2) that defines `def Cr_val : ℝ := 1451520000` (a literal rational equal to `16 · M_val² · (4/3) · (4/3 + 1) / (1 - r_val)²`) and proves the sink theorem by chaining `lemma_5_4_paper_on_domain_tight` (from `Proof/Lib/Lemma54_Paper_Main.lean`, already in place) with a one-line monotonicity step `Cr_tight r_val M_val (R_val_paper r_val) ≤ Cr_val`, taking the candidate's logged `score.approx` from `null` (sprint_004's failure) to `1.451520·10⁹` — a 6586× reduction vs V1's 9.560·10¹².

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_Cr_tight_rational_upper.py` (mpmath at 80 dps) computes the true `Cr_tight(r=23/25, M=432, R=sinh(49/50)) ≈ 1.145227·10⁹` and tabulates rational upper bounds: at `R_rat = 4/3` (provable in Lean from `Real.sinh_le_sinh.mpr (49/50 ≤ 1)` and `Real.sinh 1 ≤ (Real.exp 1 - Real.exp(-1))/2 ≤ (3 - 1/3)/2 = 4/3` via `Real.exp_one_lt_three` already in Mathlib), `Cr_val = 16 · 432² · (4/3) · (7/3) / (2/25)² = 1451520000` exactly — a clean integer with relative slack `(1.4515 − 1.1452)/1.1452 ≈ 27%` over the true `Cr_tight` (the looser-but-cheap-to-prove bound costs us ≈ 1.27×, but still gives 6586× reduction vs V1 and a Lean proof using only standard Mathlib lemmas). The sprint_004 verdict explicitly suggests path #2: "Have V2 define `Cr_val` as a rational approximation (upper bound) of `Cr_tight` at the fixed parameters, so the evaluator can score it directly." — and the existing `lemma_5_4_paper_on_domain_tight` in `Proof/Lib/Lemma54_Paper_Main.lean` (added by sprint_004, conclusion `≤ Cr_tight r M (R_val_paper r) * p^2`) plus the standard `mul_le_mul_of_nonneg_right` lets the candidate's sink theorem absorb the rational relaxation in one step. No new axioms; the 3 lean primitives + 12 trusted analytic + `h_M_oracle` + `h_oracle_domain_contains_image` audit set is preserved exactly.

## Concrete edits expected

- `ProofRefinement/Lemma54/Candidates/V3.lean`: created as a copy of `Candidates/V2.lean` with the following minimal, surgical changes:
  1. Header comment block updated: declare `-- @parent Candidates/V2.lean`, `-- @sprint Sprint_Contracts/sprint_005.md`, and explain that V3 replaces V2's symbolic `Cr_val := Cr_tight ... (R_val_paper r)` with a literal rational `1451520000`, justified by `Cr_tight ... ≤ 1451520000` via the upper bound `R_val_paper r ≤ 4/3` (i.e., `Real.sinh (49/50) ≤ 4/3`).
  2. Replace
     ```
     def Cr_val : ℝ :=
       Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
         (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)
     ```
     with
     ```
     def Cr_val : ℝ := 1451520000
     ```
     (The numerator-denominator decomposition is `Cr_val = 16 · 432² · (4/3) · (7/3) / (2/25)² = (16 · 186624 · 4 · 7 · 625) / (3 · 3 · 4) = 1451520000` exactly; the Generator may verify with `norm_num`.)
  3. Replace
     ```
     theorem Cr_val_nn : 0 ≤ Cr_val :=
       Braverman.Paper.Cr_tight_nonneg ...
     ```
     with `theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num` (or equivalent — the conclusion is just `0 ≤ 1451520000`).
  4. Add (after `Cr_val_nn`, before Section 3) a helper lemma:
     ```
     /-- `R_val_paper (23/25) = sinh (49/50) ≤ 4/3`. Proved via
         `Real.sinh_le_sinh` (monotonicity, since `49/50 ≤ 1`) and
         `Real.exp_one_lt_three` (giving `sinh 1 = (e − 1/e)/2 ≤ (3 − 1/3)/2 = 4/3`). -/
     theorem R_val_paper_le_four_thirds :
         Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 4 / 3 := by
       -- proof: unfold R_val_paper, r2, SearchConfig.r;
       -- apply Real.sinh_le_sinh.mpr (norm_num : (49:ℝ)/50 ≤ 1);
       -- chain with sinh 1 ≤ 4/3 from exp_one_lt_three.
       sorry  -- Generator fills in.
     ```
     The Generator implements the proof (no `sorry` in the final candidate). A complete proof sketch:
     ```
     have h_r2 : (3 + (23:ℝ)/25) / 4 = 49/50 := by norm_num
     have h_le_one : (49:ℝ)/50 ≤ 1 := by norm_num
     have h_sinh_mono : Real.sinh (49/50) ≤ Real.sinh 1 :=
       Real.sinh_le_sinh.mpr h_le_one
     -- sinh 1 ≤ 4/3:
     have h_exp_lt : Real.exp 1 < 3 := Real.exp_one_lt_three
     have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos _
     have h_inv_ge : Real.exp (-1) = 1 / Real.exp 1 := by
       rw [Real.exp_neg]
     -- (Real.exp 1 - Real.exp (-1))/2 ≤ (3 - 1/3)/2 = 4/3
     -- because Real.exp 1 < 3 and Real.exp (-1) = 1/Real.exp 1 > 1/3.
     have h_sinh_one_eq : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := Real.sinh_eq 1
     -- closing: nlinarith [h_exp_lt, h_exp_pos, h_inv_ge, h_sinh_one_eq] (or a
     -- short manual chain). Combine with h_sinh_mono.
     ```
     The `R_val_paper`/`r2` unfolding plus `SearchConfig.r = 23/25` is needed to reduce the goal to `Real.sinh (49/50) ≤ 4/3`.
  5. Modify the sink theorem `lemma_5_4_search`. Currently V2 closes with a single delegation
     ```
     := Braverman.Paper.lemma_5_4_paper_on_domain_tight ...
     ```
     producing `≤ Cr_tight r M (R_val_paper r) * p^2`. Restructure as a `by` block:
     ```
     theorem lemma_5_4_search :
         ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
           ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
             ∃ F_inv : ℂ → ℂ, ...
               ‖F_inv z - ... ≤ Cr_val * p ^ 2 := by
       obtain ⟨pr, hpr_pos, h_main⟩ :=
         Braverman.Paper.lemma_5_4_paper_on_domain_tight
           Braverman.SearchConfig.eta Braverman.SearchConfig.r
           Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
           M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle
       refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
       obtain ⟨F_inv, hFinv⟩ := h_main p hp_pos hp_lt z hz
       refine ⟨F_inv, hFinv.1, hFinv.2.1, ?_⟩
       calc ‖F_inv z - Complex.sin z - ↑p * ((z - ...) * Complex.cos z)‖
           ≤ Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
               (Braverman.Paper.R_val_paper Braverman.SearchConfig.r) * p^2 := hFinv.2.2
         _ ≤ Cr_val * p^2 := by
             -- monotonicity in Cr_tight via R ≤ 4/3:
             have hp_sq_nn : 0 ≤ p^2 := sq_nonneg _
             have h_Cr_le : Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
                 (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)
                 ≤ Cr_val := by
               unfold Cr_val Braverman.Paper.Cr_tight
               -- Cr_tight is monotone in R for R ≥ 0; apply R_val_paper_le_four_thirds
               -- and the explicit identity 16·432²·(4/3)·(7/3)/(2/25)² = 1451520000.
               have hR_le : Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 4/3 :=
                 R_val_paper_le_four_thirds
               have hR_nn : 0 ≤ Braverman.Paper.R_val_paper Braverman.SearchConfig.r :=
                 Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos
               -- monotone: x ↦ x · (x + 1) is increasing on x ≥ 0
               -- closing tactic: nlinarith [hR_le, hR_nn, M_val_pos, ...].
               sorry  -- Generator fills in
             exact mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn
     ```
     The Generator fills in the `sorry` placeholders with a complete proof. The structural shape (delegate to `lemma_5_4_paper_on_domain_tight`, then apply monotonicity) is the contract; the Generator owns the local tactic choices (`nlinarith`, `polyrith`, manual chaining — whatever closes the rationals).
  6. **No** edits to `M_val`, `delta_val`, `B_val`, `oracle_domain`, `h_M_oracle`, or `h_oracle_domain_contains_image`. Numeric witnesses unchanged from V1/V2.

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_005` summarising the rational-rationalisation move (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V3.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V3.lean` (new) plus optional appends to `Experience.md` / `Bulletin.md`. **No edits** to `Proof/Lib/Lemma54_Paper*.lean` (the `Cr_tight` chain added by sprint_004 is already in place and is the foundation V3 builds on); no edits to `Candidates/V0.lean`, `V1.lean`, `V2.lean`, `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, or `ProofGraph/`.
2. `lake env lean ProofRefinement/Lemma54/Candidates/V3.lean` exits 0 (the file compiles cleanly, no `sorry` survives), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V3.lean` exits 0 with `"status":"ok"` in the appended JSON line.
3. The new entry's `score.approx` is finite and strictly less than `1.5e9` (concretely `1451520000.0`, i.e. `score.numer/score.denom == 1451520000/1`); equivalently, `score.approx < V1's 9.560e12` by a factor of at least 6000×. The `axioms_used` list contains exactly the 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives (no new axiom, no `sorryAx`).

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Modify `Proof/Lib/Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, or any other file in `Proof/Lib/` (the `Cr_tight` / `F_inv_p_second_deriv_bound_tight` / `lemma_5_4_paper_on_domain_tight` declarations from sprint_004 are already in place and stay untouched).
- Modify `Candidates/V0.lean`, `V1.lean`, `V2.lean`, `Sprint_Contracts/sprint_001.md` through `sprint_004.md`, the `Refinement_Log/log.jsonl` entries, the `verdict_*.md` files, or any historical record.
- Modify `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script.
- Pick a different rational than `1451520000` (i.e. a different `R_rat` than `4/3`) without first justifying it numerically in `Scratch/`. The contract's score target `1.5e9` is calibrated for `R_rat = 4/3` — a tighter rational like `R_rat = 6/5` would lower the score further but require a non-trivial Taylor argument for `sinh(49/50) ≤ 6/5`. Prefer the cheap `4/3` path.
- Restructure or factor `lemma_5_4_paper_on_domain_tight`'s proof; treat it as a fixed dependency.

## Time budget

≤ 30 minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
