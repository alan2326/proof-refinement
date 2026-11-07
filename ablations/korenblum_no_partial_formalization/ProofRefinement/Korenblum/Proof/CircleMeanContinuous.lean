import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval
import ProofRefinement.Korenblum.Proof.CauchyL2Estimate

/-!
# Sprint 019: continuity of `circleMeanSq f r` + boundary `r → c` Cauchy L²
coefficient bound

This file pins two public theorems:

* `continuousAt_circleMeanSq_of_analyticOn_unitDisk` — the `r ↦ circleMeanSq f r`
  function is continuous at every `r₀ ∈ [0, 1)` for `f : ℂ → ℂ` analytic on
  `UnitDisk`. The proof factors through sprint 010's canonical-witness Parseval
  identity and a Weierstrass M-test on the resulting `tsum`.

* `cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq` — boundary form
  of sprint 017's cross-function Cauchy L² coefficient estimate. Combines (1)
  with sprint 017's `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` via a
  sequential-limit `r ↘ c` passage.

Both theorems are proved without any new axiom, no `sorry`, no oracle.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## Per-`r` summability of `‖a_k‖² · r^(2k)` (re-derivation). -/

/-- Per-`r` summability of `‖(cauchyPowerSeries f 0 R).coeff k‖² · r^(2k)` for
`0 ≤ r < 1` (re-derived inline, since the version in
`Proof/CauchyL2Estimate.lean` is `private`). -/
private lemma summable_coeff_sq_pow_of_lt_one
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)) := by
  set rval : ℝ := (r + 1) / 2 with hrval_def
  have hrval_pos : 0 < rval := by rw [hrval_def]; linarith
  have hrval_lt_one : rval < 1 := by rw [hrval_def]; linarith
  have hr_lt_rval : r < rval := by rw [hrval_def]; linarith
  have hrval_nonneg : 0 ≤ rval := le_of_lt hrval_pos
  set R' : ℝ≥0 := ⟨rval, hrval_nonneg⟩ with hR'_def
  have hR'_pos : (0 : ℝ) < (R' : ℝ) := hrval_pos
  have hR'_lt : (R' : ℝ) < 1 := hrval_lt_one
  have h_subset' : Metric.closedBall (0 : ℂ) (R' : ℝ) ⊆ UnitDisk := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    change z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hR'_lt
  have hf_diff' : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R' : ℝ)) :=
    (hf.mono h_subset').differentiableOn
  have h_fps' : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R') 0 (R' : ℝ≥0∞) :=
    hf_diff'.hasFPowerSeriesOnBall hR'_pos
  have h_radius_ge : (R' : ℝ≥0∞) ≤ (cauchyPowerSeries f 0 R').radius :=
    h_fps'.r_le
  set rNN : ℝ≥0 := ⟨r, hr_nonneg⟩ with hrNN_def
  have hrNN_lt : (rNN : ℝ≥0∞) < (cauchyPowerSeries f 0 R').radius := by
    have h1 : (rNN : ℝ≥0∞) < (R' : ℝ≥0∞) := by
      rw [show ((rNN : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r from
        (ENNReal.ofReal_coe_nnreal).symm]
      rw [show ((R' : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R' : ℝ) from
        (ENNReal.ofReal_coe_nnreal).symm]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mpr hr_lt_rval
    exact lt_of_lt_of_le h1 h_radius_ge
  have h_summable_lin : Summable (fun n : ℕ =>
      ‖cauchyPowerSeries f 0 R' n‖ * (rNN : ℝ) ^ n) :=
    (cauchyPowerSeries f 0 R').summable_norm_mul_pow hrNN_lt
  have hrNN_coe : ((rNN : ℝ≥0) : ℝ) = r := rfl
  have h_summable_lin' : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) := by
    convert h_summable_lin using 1
    funext n
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hrNN_coe]
  have h_tendsto_zero : Tendsto (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) atTop (𝓝 0) :=
    h_summable_lin'.tendsto_atTop_zero
  have h_eventually_le_one : ∀ᶠ n in atTop,
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n ≤ 1 := by
    rw [Metric.tendsto_atTop] at h_tendsto_zero
    obtain ⟨N, hN⟩ := h_tendsto_zero 1 zero_lt_one
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have h_nonneg : 0 ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
      apply mul_nonneg
      · exact norm_nonneg _
      · exact pow_nonneg hr_nonneg n
    rw [abs_of_nonneg h_nonneg] at h
    linarith
  have h_sq_le : ∀ᶠ n in atTop,
      (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2
        ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
    filter_upwards [h_eventually_le_one] with n hn
    have h_nonneg : 0 ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
      apply mul_nonneg
      · exact norm_nonneg _
      · exact pow_nonneg hr_nonneg n
    nlinarith
  have h_summable_sq : Summable (fun n : ℕ =>
      (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2) := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun n =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) h_summable_lin' ?_
    filter_upwards [h_sq_le] with n hn
    have h_nonneg : 0 ≤ (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2 := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    exact hn
  have h_sq_eq : ∀ n : ℕ,
      (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2
        = ‖(cauchyPowerSeries f 0 R').coeff n‖ ^ 2 * r ^ (2 * n) := by
    intro n
    rw [mul_pow]
    congr 1
    rw [← pow_mul]
    congr 1
    ring
  have h_summable_sq' : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ ^ 2 * r ^ (2 * n)) := by
    convert h_summable_sq using 1
    funext n
    rw [h_sq_eq n]
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR'_pos hR'_lt hR_pos hR_lt
  have h_summable_R : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2 * r ^ (2 * n)) := by
    convert h_summable_sq' using 1
    funext n
    rw [h_norm n]
  exact h_summable_R

/-! ## Symmetry: `circleMeanSq f r = circleMeanSq f (-r)`. -/

/-- Symmetry of `circleMeanSq` under sign change of the radius. The polar-symm
point at radius `-r` and angle `θ` equals the polar-symm point at radius `r`
and angle `θ + π`; combined with `2π`-periodicity of the polar pull-back
integrand, the two `θ`-integrals over `Ioo (-π) π` agree. -/
private lemma circleMeanSq_neg
    (f : ℂ → ℂ) (r : ℝ) :
    circleMeanSq f (-r) = circleMeanSq f r := by
  -- Reformulate the integrand at `-r` via `circleMap_neg_radius`-style identity:
  -- `polarCoord.symm (-r, θ) = polarCoord.symm (r, θ + π)`.
  have h_pt : ∀ θ : ℝ,
      (Complex.polarCoord.symm (-r, θ) : ℂ)
        = (Complex.polarCoord.symm (r, θ + Real.pi) : ℂ) := by
    intro θ
    -- Use the exp-bridge.
    rw [polarCoord_symm_eq_exp, polarCoord_symm_eq_exp]
    -- LHS = (-r) * exp(iθ); RHS = r * exp(i(θ+π)) = r * exp(iθ) * exp(iπ)
    --     = r * exp(iθ) * (-1) = -r * exp(iθ).
    push_cast
    have h_split : ((θ : ℂ) + (Real.pi : ℂ)) * Complex.I
        = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by ring
    rw [h_split]
    rw [Complex.exp_add]
    rw [Complex.exp_pi_mul_I]
    ring
  -- Now the integrand at `-r` is `g (θ + π)` where `g θ := ‖f(polarCoord.symm (r, θ))‖²`.
  set g : ℝ → ℝ := fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 with hg_def
  have h_integrand_eq : (fun θ : ℝ => ‖f (Complex.polarCoord.symm (-r, θ))‖ ^ 2)
      = (fun θ => g (θ + Real.pi)) := by
    funext θ
    simp only [hg_def]
    rw [h_pt θ]
  -- Convert both sides to `intervalIntegral`.
  have h_lhs : circleMeanSq f (-r)
      = ∫ θ in (-Real.pi)..Real.pi, g (θ + Real.pi) := by
    unfold circleMeanSq
    rw [h_integrand_eq]
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_nonneg] : -Real.pi ≤ Real.pi)]
  have h_rhs : circleMeanSq f r
      = ∫ θ in (-Real.pi)..Real.pi, g θ := by
    unfold circleMeanSq
    rw [show (fun θ : ℝ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2) = g from rfl]
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_nonneg] : -Real.pi ≤ Real.pi)]
  rw [h_lhs, h_rhs]
  -- Substitute `θ ↦ θ + π` in the LHS interval integral.
  rw [intervalIntegral.integral_comp_add_right g Real.pi]
  -- Now: `∫ x in -π+π..π+π, g x` should equal `∫ x in -π..π, g x`.
  -- After Lean simplification the bounds may appear as `0..π*2`.
  have h_bound1 : (-Real.pi + Real.pi : ℝ) = 0 := by ring
  have h_bound2 : (Real.pi + Real.pi : ℝ) = 2 * Real.pi := by ring
  -- `g θ = ‖f(polarCoord.symm (r, θ))‖²` is `2π`-periodic since `polarCoord.symm (r, θ)` is.
  have h_periodic : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [hg_def]
    congr 2
    rw [polarCoord_symm_eq_exp, polarCoord_symm_eq_exp]
    have h_cast : ((θ + 2 * Real.pi : ℝ) : ℂ)
        = (θ : ℂ) + 2 * (Real.pi : ℂ) := by push_cast; ring
    rw [h_cast]
    have h_split : ((θ : ℂ) + 2 * (Real.pi : ℂ)) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by ring
    rw [h_split]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h_period_int :
      ∫ θ in (0 : ℝ)..(0 : ℝ) + 2 * Real.pi, g θ
        = ∫ θ in (-Real.pi)..(-Real.pi) + 2 * Real.pi, g θ :=
    h_periodic.intervalIntegral_add_eq 0 (-Real.pi)
  have h_zero : (0 : ℝ) + 2 * Real.pi = 2 * Real.pi := by ring
  have h_neg_pi : (-Real.pi : ℝ) + 2 * Real.pi = Real.pi := by ring
  rw [h_zero, h_neg_pi] at h_period_int
  -- Goal: `∫ θ in (-π+π)..(π+π), g θ = ∫ θ in (-π)..π, g θ`.
  -- After `h_bound1` and `h_bound2` the LHS becomes `∫ θ in 0..(2π), g θ`.
  -- Apply periodicity: `∫ θ in 0..(2π), g θ = ∫ θ in (-π)..π, g θ`.
  have h_final : ∫ θ in (-Real.pi + Real.pi)..(Real.pi + Real.pi), g θ
      = ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [h_bound1, h_bound2]
    exact h_period_int
  exact h_final

/-- Sign symmetry: `circleMeanSq f r = circleMeanSq f |r|`. -/
private lemma circleMeanSq_abs
    (f : ℂ → ℂ) (r : ℝ) :
    circleMeanSq f |r| = circleMeanSq f r := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg hr]
    exact circleMeanSq_neg f r

/-! ## (1) Continuity of `r ↦ circleMeanSq f r` on `[0, 1)`. -/

/-- **Continuity of `r ↦ circleMeanSq f r` on the half-open ray `[0, 1)`.**

For `f : ℂ → ℂ` analytic on `UnitDisk` and any `r₀ ∈ [0, 1)`, the function
`r ↦ circleMeanSq f r` is continuous at `r₀`.

The proof routes through sprint 010's canonical-witness Parseval identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`, then applies
Mathlib's Weierstrass M-test (`continuousOn_tsum`) on a compact `Set.Icc 0 ρ`
with bound `‖a_k‖² · ρ^(2k)` (summable by `summable_coeff_sq_pow_of_lt_one`).

For `r₀ = 0`, the boundary case is handled by combining right-continuity at
`0` with the symmetry `circleMeanSq f r = circleMeanSq f |r|` (the integrand
is `2π`-periodic in `θ` and the polar map satisfies
`polarCoord.symm (-r, θ) = polarCoord.symm (r, θ + π)`). -/
theorem continuousAt_circleMeanSq_of_analyticOn_unitDisk
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀_lt : r₀ < 1) :
    ContinuousAt (fun r : ℝ => circleMeanSq f r) r₀ := by
  -- Pick a Cauchy-series radius `R` with `r₀ < (R : ℝ) < 1`.
  set Rval : ℝ := (r₀ + 1) / 2 with hRval_def
  have hRval_pos : 0 < Rval := by rw [hRval_def]; linarith
  have hRval_lt_one : Rval < 1 := by rw [hRval_def]; linarith
  have hr₀_lt_R : r₀ < Rval := by rw [hRval_def]; linarith
  have hRval_nonneg : 0 ≤ Rval := le_of_lt hRval_pos
  set R : ℝ≥0 := ⟨Rval, hRval_nonneg⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := hRval_pos
  have hR_lt : (R : ℝ) < 1 := hRval_lt_one
  have hr₀_lt_R_real : r₀ < (R : ℝ) := hr₀_lt_R
  -- Pick the M-test compact-set radius `ρ` with `r₀ < ρ < (R : ℝ)`.
  set ρ : ℝ := (r₀ + Rval) / 2 with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
  have hρ_lt_R : ρ < Rval := by rw [hρ_def]; linarith
  have hr₀_lt_ρ : r₀ < ρ := by rw [hρ_def]; linarith
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hρ_lt_one : ρ < 1 := lt_trans hρ_lt_R hRval_lt_one
  -- Define the function `g : ℝ → ℝ` as the Parseval tsum.
  set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
  set g : ℝ → ℝ := fun r => ∑' k : ℕ, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
    with hg_def
  -- M-test: `g` is continuous on `Set.Icc 0 ρ`.
  have h_summable_at_ρ : Summable (fun k : ℕ => ‖a k‖ ^ 2 * ρ ^ (2 * k)) := by
    exact summable_coeff_sq_pow_of_lt_one hf hR_pos hR_lt hρ_nonneg hρ_lt_one
  have h_summable_M : Summable (fun k : ℕ =>
      (2 * Real.pi * ρ ^ (2 * k)) * ‖a k‖ ^ 2) := by
    have h_eq : (fun k : ℕ => (2 * Real.pi * ρ ^ (2 * k)) * ‖a k‖ ^ 2)
        = (fun k : ℕ => (2 * Real.pi) * (‖a k‖ ^ 2 * ρ ^ (2 * k))) := by
      funext k; ring
    rw [h_eq]
    exact h_summable_at_ρ.mul_left _
  -- Each summand `r ↦ (2π · r^(2k)) · ‖a k‖²` is continuous on `Set.Icc 0 ρ`.
  have h_cont_summand : ∀ k : ℕ,
      ContinuousOn (fun r : ℝ => (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2)
        (Set.Icc 0 ρ) := by
    intro k
    refine ContinuousOn.mul ?_ continuousOn_const
    refine ContinuousOn.mul continuousOn_const ?_
    exact (continuous_pow (2 * k)).continuousOn
  -- M-bound on `Set.Icc 0 ρ`: `‖(2π · r^(2k)) · ‖a k‖²‖ ≤ (2π · ρ^(2k)) · ‖a k‖²`.
  have h_M_bound : ∀ k : ℕ, ∀ r ∈ Set.Icc (0 : ℝ) ρ,
      ‖(2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2‖
        ≤ (2 * Real.pi * ρ ^ (2 * k)) * ‖a k‖ ^ 2 := by
    intro k r hr
    obtain ⟨hr_nonneg, hr_le_ρ⟩ := hr
    have h_pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
    have h_rk_nn : (0 : ℝ) ≤ r ^ (2 * k) := pow_nonneg hr_nonneg _
    have h_ak_sq_nn : (0 : ℝ) ≤ ‖a k‖ ^ 2 := by positivity
    have h_const_nn : (0 : ℝ) ≤ 2 * Real.pi * r ^ (2 * k) :=
      mul_nonneg h_pi_nn h_rk_nn
    have h_term_nn : (0 : ℝ) ≤ (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 :=
      mul_nonneg h_const_nn h_ak_sq_nn
    rw [Real.norm_eq_abs, abs_of_nonneg h_term_nn]
    have h_pow_le : r ^ (2 * k) ≤ ρ ^ (2 * k) :=
      pow_le_pow_left₀ hr_nonneg hr_le_ρ _
    have h_const_le : 2 * Real.pi * r ^ (2 * k) ≤ 2 * Real.pi * ρ ^ (2 * k) :=
      mul_le_mul_of_nonneg_left h_pow_le h_pi_nn
    exact mul_le_mul_of_nonneg_right h_const_le h_ak_sq_nn
  -- Apply `continuousOn_tsum` to get `ContinuousOn g (Set.Icc 0 ρ)`.
  have h_g_cont_on_Icc : ContinuousOn g (Set.Icc (0 : ℝ) ρ) := by
    have := continuousOn_tsum (f := fun k : ℕ => fun r : ℝ =>
        (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2)
      (s := Set.Icc (0 : ℝ) ρ) (u := fun k : ℕ =>
        (2 * Real.pi * ρ ^ (2 * k)) * ‖a k‖ ^ 2)
      h_cont_summand h_summable_M h_M_bound
    exact this
  -- Bridge: `circleMeanSq f r = g r` for `r ∈ [0, ρ]` (in fact `[0, R)`),
  -- by sprint 010's canonical-witness Parseval identity.
  have h_eq_on_Icc : ∀ r ∈ Set.Icc (0 : ℝ) ρ,
      circleMeanSq f r = g r := by
    intro r hr
    obtain ⟨hr_nonneg, hr_le_ρ⟩ := hr
    have hr_lt_R : r < (R : ℝ) := lt_of_le_of_lt hr_le_ρ hρ_lt_R
    exact circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr_nonneg hr_lt_R
  -- The composed function `r ↦ circleMeanSq f r` agrees with `g ∘ (|·|)`
  -- when `|r| ∈ Set.Icc 0 ρ`.
  -- Strategy: prove `ContinuousAt (g ∘ |·|) r₀` and use the eventual equality
  -- `circleMeanSq f r = g |r|` on a 𝓝-neighborhood of `r₀`.
  have h_g_cont_at_zero : ContinuousWithinAt g (Set.Icc (0 : ℝ) ρ) 0 := by
    apply h_g_cont_on_Icc
    exact ⟨le_refl _, hρ_nonneg⟩
  have h_g_cont_at : ∀ s ∈ Set.Ico (0 : ℝ) ρ,
      ContinuousWithinAt g (Set.Icc (0 : ℝ) ρ) s := by
    intro s hs
    apply h_g_cont_on_Icc
    exact ⟨hs.1, le_of_lt hs.2⟩
  -- Case-split on `r₀ = 0` vs `r₀ > 0`.
  rcases eq_or_lt_of_le hr₀ with hr₀_eq | hr₀_pos
  · -- Case `r₀ = 0`: use the symmetry `circleMeanSq f r = circleMeanSq f |r|`.
    subst hr₀_eq
    -- Goal: `ContinuousAt (fun r => circleMeanSq f r) 0`.
    -- We have `ContinuousWithinAt g (Set.Icc 0 ρ) 0` and the bridge
    -- `circleMeanSq f r = g r` on `[0, ρ]`.
    -- By symmetry `circleMeanSq f r = circleMeanSq f |r|`, and for `|r| ∈ [0, ρ]`,
    -- `circleMeanSq f |r| = g |r|`.
    -- Compose: `r ↦ |r|` is continuous and tends to 0 within `[0, ρ]` as `r → 0`.
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- ContinuousWithinAt at 0 with ε.
    have h_within := Metric.continuousWithinAt_iff.mp h_g_cont_at_zero ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h_within
    -- Pick the actual delta as `min δ ρ` to ensure `|r| ≤ ρ`.
    refine ⟨min δ ρ, lt_min hδ_pos hρ_pos, fun r hr_dist => ?_⟩
    -- We have `dist r 0 < min δ ρ`, i.e., `|r| < δ` and `|r| < ρ` (so `|r| ≤ ρ`).
    have hr_dist_δ : dist r 0 < δ := lt_of_lt_of_le hr_dist (min_le_left _ _)
    have hr_abs_lt_ρ : |r| < ρ := by
      have : dist r 0 < ρ := lt_of_lt_of_le hr_dist (min_le_right _ _)
      rwa [Real.dist_eq, sub_zero] at this
    have hr_abs_le_ρ : |r| ≤ ρ := le_of_lt hr_abs_lt_ρ
    have hr_abs_nonneg : 0 ≤ |r| := abs_nonneg _
    -- Bridge: circleMeanSq f r = circleMeanSq f |r| = g |r|.
    have h_circ_eq : circleMeanSq f r = g |r| := by
      rw [← circleMeanSq_abs]
      exact h_eq_on_Icc |r| ⟨hr_abs_nonneg, hr_abs_le_ρ⟩
    -- Bridge at 0.
    have h_circ_zero_eq : circleMeanSq f 0 = g 0 :=
      h_eq_on_Icc 0 ⟨le_refl _, hρ_nonneg⟩
    rw [h_circ_eq, h_circ_zero_eq]
    -- Apply the within-continuity at 0.
    have h_abs_mem : |r| ∈ Set.Icc (0 : ℝ) ρ := ⟨hr_abs_nonneg, hr_abs_le_ρ⟩
    have h_abs_dist : dist |r| 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      rw [abs_abs]
      have : dist r 0 < δ := hr_dist_δ
      rwa [Real.dist_eq, sub_zero] at this
    exact hδ h_abs_mem h_abs_dist
  · -- Case `r₀ > 0`: use the open neighborhood `Set.Ioo (r₀/2) ρ`.
    -- The function `circleMeanSq f` agrees with `g` on `Set.Ioo (r₀/2) ρ ⊆ Set.Icc 0 ρ`.
    -- And `g` is continuous on `Set.Icc 0 ρ`, hence at `r₀ ∈ Set.Ioo (r₀/2) ρ`.
    have hr₀2_pos : 0 < r₀ / 2 := by linarith
    have hr₀2_lt_r₀ : r₀ / 2 < r₀ := by linarith
    have h_open_nbhd : Set.Ioo (r₀ / 2) ρ ⊆ Set.Icc (0 : ℝ) ρ := by
      intro r hr
      exact ⟨le_of_lt (lt_trans hr₀2_pos hr.1), le_of_lt hr.2⟩
    have hr₀_mem_open : r₀ ∈ Set.Ioo (r₀ / 2) ρ := ⟨hr₀2_lt_r₀, hr₀_lt_ρ⟩
    have h_open : IsOpen (Set.Ioo (r₀ / 2) ρ) := isOpen_Ioo
    -- The set is in 𝓝 r₀.
    have h_nbhd_r₀ : Set.Ioo (r₀ / 2) ρ ∈ 𝓝 r₀ :=
      h_open.mem_nhds hr₀_mem_open
    -- ContinuousAt g r₀ from ContinuousOn g Set.Icc + open subset membership.
    have h_g_continuousOn_open : ContinuousOn g (Set.Ioo (r₀ / 2) ρ) :=
      h_g_cont_on_Icc.mono h_open_nbhd
    have h_g_continuousAt_r₀ : ContinuousAt g r₀ :=
      h_g_continuousOn_open.continuousAt h_nbhd_r₀
    -- circleMeanSq f =ᶠ[𝓝 r₀] g.
    have h_eqOn_open : Set.EqOn (fun r : ℝ => circleMeanSq f r) g
        (Set.Ioo (r₀ / 2) ρ) := by
      intro r hr
      exact h_eq_on_Icc r (h_open_nbhd hr)
    have h_evEq : (fun r : ℝ => circleMeanSq f r) =ᶠ[𝓝 r₀] g := by
      apply Filter.eventuallyEq_of_mem h_nbhd_r₀
      exact h_eqOn_open
    -- Conclude.
    rw [continuousAt_congr h_evEq]
    exact h_g_continuousAt_r₀

/-! ## (2) Boundary form of sprint 017's cross-function Cauchy L² estimate. -/

/-- **Boundary form of the cross-function Cauchy L² coefficient estimate.**

For `f, g : ℂ → ℂ` analytic on `UnitDisk` with `‖f z‖ ≤ ‖g z‖` whenever
`z ∈ UnitDisk` and `c < ‖z‖`, the boundary radius `r = c` satisfies
`(2π) · ‖a_k(f)‖² · c^(2k) ≤ circleMeanSq g c` for every `k : ℕ`,
where `a_k(f) := (cauchyPowerSeries f 0 R).coeff k` for any `R ∈ (0, 1)`.

The proof picks a sequence `r_n := c + (1 - c)/(n + 2)` decreasing to `c`,
applies sprint 017's outer-radius bound at each `r_n`, and passes to the
limit `n → ∞` using continuity of `r ↦ circleMeanSq g r` at `r = c`
(theorem (1) above) and continuity of `r ↦ r^(2k)`. -/
theorem cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * c ^ (2 * k)
      ≤ circleMeanSq g c := by
  -- Sequence `r_n := c + (1 - c)/(n + 2)`.
  set r_seq : ℕ → ℝ := fun n => c + (1 - c) / (n + 2) with hr_seq_def
  -- Verify properties.
  have h_one_sub_c_pos : 0 < 1 - c := by linarith
  have h_n2_pos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := by
    intro n
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h_r_n_gt_c : ∀ n : ℕ, c < r_seq n := by
    intro n
    simp only [hr_seq_def]
    have h_div_pos : 0 < (1 - c) / ((n : ℝ) + 2) :=
      div_pos h_one_sub_c_pos (h_n2_pos n)
    linarith
  have h_r_n_lt_one : ∀ n : ℕ, r_seq n < 1 := by
    intro n
    simp only [hr_seq_def]
    have hn2_ge_two : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h_div_lt : (1 - c) / ((n : ℝ) + 2) ≤ (1 - c) / 2 := by
      apply div_le_div_of_nonneg_left (le_of_lt h_one_sub_c_pos) (by norm_num : (0:ℝ) < 2)
      exact hn2_ge_two
    have h_div_lt_one_sub_c : (1 - c) / 2 < 1 - c := by
      have := h_one_sub_c_pos
      linarith
    linarith
  have h_r_n_pos : ∀ n : ℕ, 0 < r_seq n := fun n => lt_trans hc_pos (h_r_n_gt_c n)
  -- Tendsto: `r_seq n → c`.
  have h_tendsto_r_seq : Tendsto r_seq atTop (𝓝 c) := by
    simp only [hr_seq_def]
    have h_const_tendsto : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have h_div_tendsto : Tendsto (fun n : ℕ => (1 - c) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h_n_tendsto : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
        have h_nat_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h_nat_atTop.atTop_add tendsto_const_nhds
      have h_inv_tendsto : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
        h_n_tendsto.inv_tendsto_atTop
      have h_const_mul : Tendsto (fun n : ℕ => (1 - c) * ((n : ℝ) + 2)⁻¹) atTop
          (𝓝 ((1 - c) * 0)) :=
        h_inv_tendsto.const_mul (1 - c)
      have h_zero : (1 - c) * 0 = 0 := by ring
      rw [h_zero] at h_const_mul
      have h_eq : (fun n : ℕ => (1 - c) / ((n : ℝ) + 2))
          = (fun n : ℕ => (1 - c) * ((n : ℝ) + 2)⁻¹) := by
        funext n; rw [div_eq_mul_inv]
      rw [h_eq]
      exact h_const_mul
    have := h_const_tendsto.add h_div_tendsto
    have h_zero : c + 0 = c := by ring
    rw [h_zero] at this
    exact this
  -- Apply sprint 017 at each `r_seq n`.
  have h_bound : ∀ n : ℕ,
      (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r_seq n) ^ (2 * k)
        ≤ circleMeanSq g (r_seq n) := by
    intro n
    exact cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq
      hf_an hg_an hc_pos hc_lt h_outer hR_pos hR_lt
      (h_r_n_gt_c n) (h_r_n_lt_one n) k
  -- LHS tendsto: `(2π) · ‖a_k‖² · r_seq n^(2k) → (2π) · ‖a_k‖² · c^(2k)`.
  have h_tendsto_lhs : Tendsto
      (fun n => (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
                  * (r_seq n) ^ (2 * k))
      atTop
      (𝓝 ((2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * c ^ (2 * k))) := by
    have h_pow_tendsto : Tendsto (fun n => (r_seq n) ^ (2 * k)) atTop
        (𝓝 (c ^ (2 * k))) := h_tendsto_r_seq.pow (2 * k)
    exact h_pow_tendsto.const_mul _
  -- RHS tendsto: `circleMeanSq g (r_seq n) → circleMeanSq g c`, via continuity at `c`.
  have h_continuousAt_c : ContinuousAt (fun r : ℝ => circleMeanSq g r) c :=
    continuousAt_circleMeanSq_of_analyticOn_unitDisk hg_an (le_of_lt hc_pos) hc_lt
  have h_tendsto_rhs : Tendsto (fun n => circleMeanSq g (r_seq n)) atTop
      (𝓝 (circleMeanSq g c)) :=
    h_continuousAt_c.tendsto.comp h_tendsto_r_seq
  -- Pass to the limit.
  exact le_of_tendsto_of_tendsto' h_tendsto_lhs h_tendsto_rhs h_bound

end ProofRefinement.Korenblum
