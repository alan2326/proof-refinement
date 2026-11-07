/-
  Candidates/V4.lean — tighten V3's `R_val_paper ≤ 4/3` rationalisation to
  `R_val_paper ≤ 6/5`, dropping `Cr_val` from `1451520000` to `1231718400`.

  -- @parent Candidates/V3.lean
  -- @sprint Sprint_Contracts/sprint_006.md

  V3 bounded `R_val_paper (23/25) = sinh (49/50) ≤ sinh 1 ≤ 4/3` using the
  loose `Real.exp_one_lt_three`. The `4/3` step is the dominant slack: true
  `sinh 1 ≈ 1.1752` lives well below `4/3 ≈ 1.333`, costing ≈ 18% on
  `R(R+1)`. V4 replaces the upper bound with `6/5` — provable from the
  tighter `Real.exp_one_lt_d9 : exp 1 < 2.7182818286` and
  `Real.exp_one_gt_d9 : 2.7182818283 < exp 1` (already exposed by
  `Mathlib.Analysis.Complex.ExponentialBounds`, which V3 already imports).
  This captures most of the slack without changing the proof structure,
  the `Cr_tight` formula, or the rectangle / M-oracle witnesses.

  Score: `Cr_val = 1231718400` exactly
  (= `16 · 432² · (6/5) · (11/5) / (2/25)²`), a 1.178× reduction
  vs V3's `1451520000` (≈ 15.1% off the V3 baseline).

  Trust base (unchanged from V1/V2/V3):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  No new axioms are introduced; the tightening only invokes existing
  Mathlib facts about `Real.sinh` and `Real.exp 1`.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, unchanged from V1/V2/V3) -/

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

/-- `Cr_val := 1231718400`, a literal rational equal to
`16 · M_val² · (6/5) · (6/5 + 1) / (1 − r_val)²`
(with `M_val = 432`, `r_val = 23/25`, so `1 − r_val = 2/25`):
`16 · 186624 · (6/5) · (11/5) / (4/625) = 186624 · 6600 = 1231718400`.
The score gate's `_eval_rational` evaluates `Cr_val` directly without
touching `Real.sinh`. The sink theorem closes via
`Cr_tight r M (R_val_paper r) ≤ Cr_val`, justified by
`R_val_paper (23/25) ≤ 6/5`. -/
def Cr_val : ℝ := 1231718400

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: the tighter rational upper bound on `R_val_paper` at `r = 23/25` -/

/-- `R_val_paper (23/25) = sinh (49/50) ≤ 6/5`. Proved via
`Real.sinh_le_sinh` (monotonicity, since `49/50 ≤ 1`) and
`Real.exp_one_lt_d9` / `Real.exp_one_gt_d9` (giving
`sinh 1 = (exp 1 − exp(−1))/2 ≤ (2.7182818286 − 1/2.7182818286)/2
≈ 1.1752 ≤ 6/5 = 1.2`, margin ≈ 0.0248 on `sinh 1`, ≈ 0.0496 on the
nlinarith-relevant `12/5` threshold). -/
theorem R_val_paper_le_six_fifths :
    Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 6 / 5 := by
  -- unfold to the concrete `sinh ((3 + 23/25)/4) = sinh (49/50)` form
  unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
  -- step 1: monotonicity of sinh on the input, since (3 + 23/25)/4 = 49/50 ≤ 1
  have h_le_one : (3 + (23 : ℝ) / 25) / 4 ≤ 1 := by norm_num
  have h_sinh_mono :
      Real.sinh ((3 + (23 : ℝ) / 25) / 4) ≤ Real.sinh 1 :=
    Real.sinh_le_sinh.mpr h_le_one
  -- step 2: bound `Real.sinh 1 ≤ 6/5` via `Real.exp 1 < 2.7182818286` and
  -- `2.7182818283 < Real.exp 1`.
  have h_sinh_one : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 :=
    Real.sinh_eq 1
  have h_exp_neg : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h_exp_lt_d9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_gt_d9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_sinh_one_le : Real.sinh 1 ≤ 6 / 5 := by
    rw [h_sinh_one, h_exp_neg]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    -- Goal: Real.exp 1 - (Real.exp 1)⁻¹ ≤ 6/5 * 2 = 12/5.
    -- From e < 2.7182818286 and e > 2.7182818283:
    --   e - 1/e ≤ 2.7182818286 - 1/2.7182818286
    --        ≈ 2.7182818286 - 0.36787944127...
    --        ≈ 2.35040238 < 12/5 = 2.4 (margin ≈ 0.0496).
    have h_e_inv_pos : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr h_exp_pos
    have h_mul : Real.exp 1 * (Real.exp 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt h_exp_pos)
    nlinarith [h_exp_lt_d9, h_exp_gt_d9, h_exp_pos, h_e_inv_pos, h_mul,
               sq_nonneg (Real.exp 1 - 2.7182818286),
               sq_nonneg (Real.exp 1 - (Real.exp 1)⁻¹)]
  exact le_trans h_sinh_mono h_sinh_one_le

/-! ## Section 3: Oracle rectangle (the M-bound domain, unchanged from V1/V2/V3) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, unchanged from V1/V2/V3) -/

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

/-- **The candidate's sink theorem.** Same shape as V2/V3; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_tight` to
obtain `≤ Cr_tight r M (R_val_paper r) * p^2`, then absorbing into
the literal rational `Cr_val = 1231718400` via the monotonicity
`Cr_tight r M (R_val_paper r) ≤ Cr_val` (driven by
`R_val_paper r ≤ 6/5`). The conclusion's `Cr_val` is a rational that
the per-candidate Evaluator scores directly, yielding the 1.178×
reduction vs V3 (≈ 15.1%). -/
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
      Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 6 / 5 :=
    R_val_paper_le_six_fifths
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
        Braverman.Paper.R_val_paper (23 / 25 : ℝ) ≤ 6 / 5 := by
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
    --   16 * 432^2 * R * (R + 1) / (1 - 23/25)^2 ≤ 1231718400
    -- where R = R_val_paper (23/25). Replace `1 - 23/25` by `2/25`.
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (2 / 25) ^ 2)]
    -- Goal: 16 * 432^2 * R * (R + 1) ≤ 1231718400 * (2/25)^2
    -- 1231718400 * (2/25)^2 = 1231718400 * 4/625 = 7882997.76
    --                       = 197074944/25.
    -- And 16 * 432^2 * (6/5) * (11/5) = 16·186624·66/25 = 197074944/25.
    -- So suffices: R·(R+1) ≤ (6/5)·(11/5) = 66/25 = 2.64, given 0 ≤ R ≤ 6/5.
    nlinarith [hR_le', hR_nn', sq_nonneg (R - 6/5), sq_nonneg R,
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
