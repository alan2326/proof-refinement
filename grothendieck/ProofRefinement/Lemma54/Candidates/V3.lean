/-
  Candidates/V3.lean — replace V2's symbolic `Cr_val := Cr_tight ... (R_val_paper r)`
  with a literal rational `Cr_val := 1451520000`, justified by a one-line
  monotonicity step `Cr_tight r M (R_val_paper r) ≤ Cr_val` resting on
  `R_val_paper (23/25) = sinh (49/50) ≤ 4/3`.

  -- @parent Candidates/V2.lean
  -- @sprint Sprint_Contracts/sprint_005.md

  V2 introduced `Cr_tight` and the sink delegation to
  `lemma_5_4_paper_on_domain_tight`. The score gate failed because the
  per-candidate Evaluator's `_eval_rational` cannot evaluate `Real.sinh`
  symbolically. V3 rationalises: define `Cr_val` as the literal
  `1451520000` (= `16 · 432² · (4/3) · (7/3) / (2/25)²`) and absorb the
  gap via the monotonicity of `Cr_tight r M R = 16 M² R (R+1) / (1-r)²`
  in `R ≥ 0`, applied with the rational bound
  `R_val_paper (23/25) = sinh (49/50) ≤ sinh 1 ≤ (e − 1/e)/2 ≤ 4/3`
  (using `Real.sinh_le_sinh`, `Real.sinh_eq`, `Real.exp_one_lt_three`,
  and `Real.exp_one_gt_two`).

  Score: `Cr_val = 1.45152·10⁹` exactly — a 6586× reduction vs V1's
  ≈ 9.55·10¹². Slack vs the true `Cr_tight ≈ 1.145·10⁹` is ≈ 1.27×,
  the (cheap) cost of using the rational `4/3` upper bound on `sinh 1`.

  Trust base (unchanged from V1/V2):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  No new axioms are introduced; the literalisation only invokes existing
  lemmas in `Lemma54_Paper.lean` plus standard Mathlib facts about
  `Real.sinh` and `Real.exp 1`.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, unchanged from V1/V2) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`.
Set to `432`, the integer ceiling of the certified
`compute_M_bound_tight ≈ 431.81`. -/
def M_val : ℝ := 432

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. -/
def delta_val : ℝ := 163 / 1000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. -/
def B_val : ℝ := 1115 / 1000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-! ## Section 2: Score (literal rational `Cr_val`, dominating `Cr_tight`) -/

/-- `Cr_val := 1451520000`, a literal rational equal to
`16 · M_val² · (4/3) · (4/3 + 1) / (1 − r_val)²` (with `M_val = 432`,
`r_val = 23/25`, so `1 − r_val = 2/25`). The score gate's
`_eval_rational` evaluates `Cr_val` directly without touching
`Real.sinh`. The sink theorem closes via `Cr_tight r M (R_val_paper r)
≤ Cr_val`, justified by `R_val_paper (23/25) ≤ 4/3`. -/
def Cr_val : ℝ := 1451520000

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: the rational upper bound on `R_val_paper` at `r = 23/25` -/

/-- `R_val_paper (23/25) = sinh (49/50) ≤ 4/3`. Proved via
`Real.sinh_le_sinh` (monotonicity, since `49/50 ≤ 1`) and
`Real.exp_one_lt_three` / `Real.exp_one_gt_two` (giving
`sinh 1 = (exp 1 − exp(−1))/2 ≤ (3 − 1/3)/2 = 4/3`). -/
theorem R_val_paper_le_four_thirds :
    Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 4 / 3 := by
  -- unfold to the concrete `sinh ((3 + 23/25)/4) = sinh (49/50)` form
  unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
  -- step 1: monotonicity of sinh on the input, since (3 + 23/25)/4 = 49/50 ≤ 1
  have h_le_one : (3 + (23 : ℝ) / 25) / 4 ≤ 1 := by norm_num
  have h_sinh_mono :
      Real.sinh ((3 + (23 : ℝ) / 25) / 4) ≤ Real.sinh 1 :=
    Real.sinh_le_sinh.mpr h_le_one
  -- step 2: bound `Real.sinh 1 ≤ 4/3` via `Real.exp 1 < 3` and
  -- `Real.exp (-1) = (Real.exp 1)⁻¹` plus `2 < Real.exp 1`.
  have h_sinh_one : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 :=
    Real.sinh_eq 1
  have h_exp_neg : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h_exp_lt : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h_exp_gt_two : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have h_exp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_sinh_one_le : Real.sinh 1 ≤ 4 / 3 := by
    rw [h_sinh_one, h_exp_neg]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3)]
    -- After `div_le_div_iff`, goal is:
    --   (Real.exp 1 - (Real.exp 1)⁻¹) * 3 ≤ 4 * 2
    -- Multiply by `Real.exp 1 > 0` (handled inside nlinarith via the
    -- `mul_inv_cancel₀` hypothesis):  3·(exp 1)² - 3 ≤ 8·exp 1, i.e.
    -- 3·(exp 1)² - 8·exp 1 - 3 ≤ 0; roots at exp 1 = 3 and exp 1 = -1/3,
    -- so true on [-1/3, 3]; we have 2 < exp 1 < 3.
    have h_e_inv_pos : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr h_exp_pos
    have h_mul : Real.exp 1 * (Real.exp 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt h_exp_pos)
    nlinarith [h_exp_lt, h_exp_gt_two, h_exp_pos, h_e_inv_pos, h_mul,
               sq_nonneg (Real.exp 1 - 3), sq_nonneg (Real.exp 1 - 2)]
  exact le_trans h_sinh_mono h_sinh_one_le

/-! ## Section 3: Oracle rectangle (the M-bound domain, unchanged from V1/V2) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, unchanged from V1/V2) -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Certified single-`M` sup-norm bound: `|H_0|, |H_η|, |H_0'|,
|H_η'| ≤ M_val` on the tight rectangle `Ω(163/1000, 1115/1000)`. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V2; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_tight` to
obtain `≤ Cr_tight r M (R_val_paper r) * p^2`, then absorbing into
the literal rational `Cr_val = 1451520000` via the monotonicity
`Cr_tight r M (R_val_paper r) ≤ Cr_val` (driven by
`R_val_paper r ≤ 4/3`). The conclusion's `Cr_val` is a rational that
the per-candidate Evaluator scores directly, yielding the 6586×
reduction vs V1. -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  obtain ⟨pr, hpr_pos, h_main⟩ :=
    Braverman.Paper.lemma_5_4_paper_on_domain_tight
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_tight r M (R_val_paper r) * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  have hR_le :
      Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 4 / 3 :=
    R_val_paper_le_four_thirds
  have hR_nn :
      (0 : ℝ) ≤ Braverman.Paper.R_val_paper Braverman.SearchConfig.r :=
    Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos
  -- Monotonicity step: `Cr_tight r M R ≤ Cr_val` for our parameters.
  have h_Cr_le :
      Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)
        ≤ Cr_val := by
    -- Re-express `hR_le`/`hR_nn` against the literal `23/25` so that they
    -- match the goal after `unfold ... SearchConfig.r`.
    have hR_le' :
        Braverman.Paper.R_val_paper (23 / 25 : ℝ) ≤ 4 / 3 := by
      have := hR_le
      unfold Braverman.SearchConfig.r at this
      exact this
    have hR_nn' :
        (0 : ℝ) ≤ Braverman.Paper.R_val_paper (23 / 25 : ℝ) := by
      have := hR_nn
      unfold Braverman.SearchConfig.r at this
      exact this
    unfold Braverman.Paper.Cr_tight Cr_val M_val Braverman.SearchConfig.r
    -- After unfolds the goal reads (modulo norm_num on (1 - 23/25)):
    --   16 * 432^2 * R * (R + 1) / (1 - 23/25)^2 ≤ 1451520000
    -- where R = R_val_paper (23/25). Replace `1 - 23/25` by `2/25`.
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (2 / 25) ^ 2)]
    -- Goal: 16 * 432^2 * R * (R + 1) ≤ 1451520000 * (2/25)^2
    -- 1451520000 * (2/25)^2 = 1451520000 * 4/625 = 9292800.
    -- And 16 * 432^2 * (4/3) * (7/3) = 16·186624·28/9 = 9292800.
    -- So suffices: R·(R+1) ≤ (4/3)·(7/3) = 28/9 ≈ 3.111, given 0 ≤ R ≤ 4/3.
    nlinarith [hR_le', hR_nn', sq_nonneg (R - 4/3), sq_nonneg R,
               mul_nonneg hR_nn' hR_nn']
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r) * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
