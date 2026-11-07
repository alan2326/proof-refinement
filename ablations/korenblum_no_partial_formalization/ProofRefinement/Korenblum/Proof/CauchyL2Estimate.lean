import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.BergmanParseval

/-!
# Sprint 017: Cauchy L² coefficient estimate + outer-annulus cross-function bridge

This file pins three public lemmas in Lean:

* `cauchyPowerSeries_normSq_pow_le_circleMeanSq` — single-coefficient Cauchy
  L² estimate.  For `f` analytic on `UnitDisk`, an NNReal radius `R ∈ (0, 1)`,
  and any `r ∈ (0, 1)`,
  `(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq f r` for every `k : ℕ`,
  where `a_k := (cauchyPowerSeries f 0 R).coeff k`.

* `outer_circleMeanSq_dom_of_pointwise_dom` — outer-annulus circle-mean
  dominance from outer pointwise dominance.  For analytic `f, g` on
  `UnitDisk` with `‖f z‖ ≤ ‖g z‖` whenever `z ∈ UnitDisk` and `c < ‖z‖`,
  every `r ∈ (c, 1)` satisfies `circleMeanSq f r ≤ circleMeanSq g r`.

* `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` — cross-function
  corollary.  Composing (1) at `f` with (2) gives, for every outer radius
  `r ∈ (c, 1)` and every `k`,
  `(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq g r`.

The proof of (1) is a direct **single-summand ≤ tsum** bound on sprint 010's
canonical-witness Parseval identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`.

The proof of (2) is the outer-half radial step from sprint 005's
`validKorenblum_of_innerCircleMean_dom`, lifted to a public lemma:
`setIntegral_mono_on` on the per-θ pointwise comparison
`‖f (polarCoord.symm (r, θ))‖² ≤ ‖g (polarCoord.symm (r, θ))‖²`, with
membership `polarCoord.symm (r, θ) ∈ UnitDisk` and `c < ‖z‖` derived from
`r ∈ (c, 1)`.

The proof of (3) is a one-line composition `le_trans`.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## Per-`r` summability of `‖a_k‖² · r^(2k)`. -/

/-- Per-`r` summability of `‖(cauchyPowerSeries f 0 R).coeff k‖² · r^(2k)`
for `r ∈ [0, 1)`. The argument re-derives the same summability used inside
`Proof/CircleMeanLogConvex.lean` (which is private there): from
`FormalMultilinearSeries.summable_norm_mul_pow` get linear summability on
the helper radius `R' := (r + 1)/2`, then square-bound the
eventually-small terms, then transport from `R'` back to the user-supplied
`R` via radius-invariance of coefficient norms. -/
private lemma summable_coeff_sq_pow
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)) := by
  -- Pick an intermediate radius `R' := (r + 1)/2` strictly between `r` and `1`.
  set rval : ℝ := (r + 1) / 2 with hrval_def
  have hrval_pos : 0 < rval := by
    rw [hrval_def]; linarith
  have hrval_lt_one : rval < 1 := by
    rw [hrval_def]; linarith
  have hr_lt_rval : r < rval := by
    rw [hrval_def]; linarith
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
  -- Move from the helper radius `R'` back to the user-supplied `R` via
  -- the radius-invariance of coefficient norms.
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR'_pos hR'_lt hR_pos hR_lt
  have h_summable_R : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2 * r ^ (2 * n)) := by
    convert h_summable_sq' using 1
    funext n
    rw [h_norm n]
  exact h_summable_R

/-! ## (1) Single-coefficient Cauchy L² estimate. -/

/-- **Single-coefficient Cauchy L² estimate.**

For `f : ℂ → ℂ` analytic on `UnitDisk`, an NNReal radius `R ∈ (0, 1)`,
and any radius `r ∈ (0, 1)`, the squared norm of each Cauchy
power-series coefficient times `r^(2k)` is bounded by the normalized
circle mean:

```
(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq f r
```

where `a_k := (cauchyPowerSeries f 0 R).coeff k`.

The proof rewrites `circleMeanSq f r` via sprint 010's canonical-witness
Parseval identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`, then
extracts the `k`-th summand by `Summable.le_tsum`. -/
theorem cauchyPowerSeries_normSq_pow_le_circleMeanSq
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < 1) (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ circleMeanSq f r := by
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  -- Pick an intermediate radius `R₀ := (r + 1)/2` strictly between `r` and `1`,
  -- so the canonical-witness Parseval applies at radius `r < R₀ < 1`.
  set rval : ℝ := (r + 1) / 2 with hrval_def
  have hrval_pos : 0 < rval := by rw [hrval_def]; linarith
  have hrval_lt_one : rval < 1 := by rw [hrval_def]; linarith
  have hr_lt_rval : r < rval := by rw [hrval_def]; linarith
  have hrval_nonneg : 0 ≤ rval := le_of_lt hrval_pos
  set R₀ : ℝ≥0 := ⟨rval, hrval_nonneg⟩ with hR₀_def
  have hR₀_pos : (0 : ℝ) < (R₀ : ℝ) := hrval_pos
  have hR₀_lt : (R₀ : ℝ) < 1 := hrval_lt_one
  have hr_lt_R₀ : r < (R₀ : ℝ) := hr_lt_rval
  -- Canonical-witness Parseval at the helper radius `R₀` and our `r`.
  have h_eq :
      circleMeanSq f r
        = ∑' j : ℕ,
            (2 * Real.pi * r ^ (2 * j))
              * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR₀_pos hR₀_lt hr_nonneg hr_lt_R₀
  -- Per-`r` summability of the same tsum at radius `R₀`.
  have h_summable_R₀ : Summable (fun j : ℕ =>
      ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 * r ^ (2 * j)) :=
    summable_coeff_sq_pow hf hR₀_pos hR₀_lt hr_nonneg hr_lt
  -- Reshape the summand: pull `(2π)` out of the tsum.
  have h_summable_full : Summable (fun j : ℕ =>
      (2 * Real.pi * r ^ (2 * j))
        * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2) := by
    have h_eq_summand : ∀ j : ℕ,
        (2 * Real.pi * r ^ (2 * j))
            * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2
          = (2 * Real.pi)
              * (‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 * r ^ (2 * j)) := by
      intro j; ring
    have h_summable' : Summable (fun j : ℕ =>
        (2 * Real.pi)
          * (‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 * r ^ (2 * j))) :=
      h_summable_R₀.mul_left _
    convert h_summable' using 1
    funext j; exact h_eq_summand j
  -- Per-summand non-negativity.
  have h_term_nonneg : ∀ j : ℕ,
      0 ≤ (2 * Real.pi * r ^ (2 * j))
            * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 := by
    intro j
    have h_pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
    have h_rpow_nn : (0 : ℝ) ≤ r ^ (2 * j) := pow_nonneg hr_nonneg _
    have h_prod_nn : (0 : ℝ) ≤ 2 * Real.pi * r ^ (2 * j) :=
      mul_nonneg h_pi_nn h_rpow_nn
    have h_sq_nn : (0 : ℝ)
        ≤ ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 := by positivity
    exact mul_nonneg h_prod_nn h_sq_nn
  -- Single-summand ≤ tsum.
  have h_le_tsum :
      (2 * Real.pi * r ^ (2 * k))
          * ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2
        ≤ ∑' j : ℕ,
            (2 * Real.pi * r ^ (2 * j))
              * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 := by
    refine h_summable_full.le_tsum k (fun j _ => h_term_nonneg j)
  -- Bridge from the `R₀`-coefficient to the user-supplied `R`-coefficient
  -- via the radius-invariance of coefficient norms.
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR₀_pos hR₀_lt hR_pos hR_lt
  have h_le_tsum_R :
      (2 * Real.pi * r ^ (2 * k))
          * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ ∑' j : ℕ,
            (2 * Real.pi * r ^ (2 * j))
              * ‖(cauchyPowerSeries f 0 R₀).coeff j‖ ^ 2 := by
    have h_eq_term :
        (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
          = (2 * Real.pi * r ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2 := by
      rw [h_norm k]
    rw [h_eq_term]
    exact h_le_tsum
  -- Rewrite using `h_eq` to conclude.
  rw [h_eq]
  have h_reshape :
      (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
        = (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by ring
  rw [h_reshape]
  exact h_le_tsum_R

/-! ## (2) Outer-annulus circle-mean dominance from outer pointwise dominance. -/

/-- The integrand `θ ↦ ‖f (polarCoord.symm (r, θ))‖²` is integrable on
`Ioo (-π) π` for any `f` analytic on `UnitDisk` and any `r ∈ (0, 1)`.

Proved by composing continuity of `θ ↦ polarCoord.symm (r, θ)` (via
`polarCoord_symm_eq_exp`), continuity of `f` on the closed disk of radius
`r` (which lies inside `UnitDisk`), continuity of squared norm, and
boundedness of `Ioo (-π) π`. -/
private lemma integrableOn_normSq_polarCoord_symm
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < 1) :
    IntegrableOn (fun θ : ℝ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      (Set.Ioo (-Real.pi) Real.pi) volume := by
  -- Continuity of `θ ↦ polarCoord.symm (r, θ) : ℂ` (via the exp form).
  have h_pol_cont : Continuous
      (fun θ : ℝ => (Complex.polarCoord.symm (r, θ) : ℂ)) := by
    refine Continuous.congr (f := fun θ : ℝ =>
        (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ?_ ?_
    · exact continuous_const.mul
        (((Complex.continuous_ofReal).mul continuous_const).cexp)
    · intro θ
      exact (polarCoord_symm_eq_exp r θ).symm
  -- Continuity of `f` on `UnitDisk` from analyticity.
  have h_f_cont : ContinuousOn f UnitDisk := hf.continuousOn
  -- Membership of `polarCoord.symm (r, θ) ∈ UnitDisk` for any θ
  -- (since `r ∈ (0, 1)`).
  have h_mem : ∀ θ : ℝ,
      (Complex.polarCoord.symm (r, θ) : ℂ) ∈ UnitDisk := by
    intro θ; exact (polarCoord_symm_mem_unitDisk_iff hr_pos).mpr hr_lt
  -- The composition `f ∘ polarCoord.symm` is continuous (as a function of θ).
  have h_comp_cont : Continuous
      (fun θ : ℝ => f (Complex.polarCoord.symm (r, θ))) := by
    have h_cont_on_UD : ContinuousOn
        (fun θ : ℝ => f (Complex.polarCoord.symm (r, θ))) Set.univ := by
      have hpol_on : ContinuousOn
          (fun θ : ℝ => (Complex.polarCoord.symm (r, θ) : ℂ)) Set.univ :=
        h_pol_cont.continuousOn
      refine ContinuousOn.comp h_f_cont hpol_on ?_
      intro θ _; exact h_mem θ
    exact continuousOn_univ.mp h_cont_on_UD
  -- The integrand is the square norm of the composition.
  have h_norm_sq_cont : Continuous
      (fun θ : ℝ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2) := by
    refine Continuous.pow ?_ 2
    exact continuous_norm.comp h_comp_cont
  -- Continuous on bounded interval ⇒ integrable on `Ioo (-π) π`.
  exact (h_norm_sq_cont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self

/-- **Outer-annulus circle-mean dominance from outer pointwise dominance.**

If `f, g : ℂ → ℂ` are analytic on `UnitDisk` and `‖f z‖ ≤ ‖g z‖` whenever
`z ∈ UnitDisk` and `c < ‖z‖`, then for every `r ∈ (c, 1)` we have
`circleMeanSq f r ≤ circleMeanSq g r`.

The proof is the outer-half radial step:
`setIntegral_mono_on` on the per-θ pointwise comparison
`‖f (polarCoord.symm (r, θ))‖² ≤ ‖g (polarCoord.symm (r, θ))‖²`, with
`polarCoord.symm (r, θ) ∈ UnitDisk` (since `r < 1`) and `c < ‖z‖ = r`
giving the hypothesis-applicability membership. -/
theorem outer_circleMeanSq_dom_of_pointwise_dom
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {r : ℝ} (hr_gt_c : c < r) (hr_lt : r < 1) :
    circleMeanSq f r ≤ circleMeanSq g r := by
  have hr_pos : 0 < r := lt_trans hc hr_gt_c
  -- Per-θ integrability for both `f` and `g`.
  have hf_int : IntegrableOn
      (fun θ : ℝ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      (Set.Ioo (-Real.pi) Real.pi) volume :=
    integrableOn_normSq_polarCoord_symm hf_an hr_pos hr_lt
  have hg_int : IntegrableOn
      (fun θ : ℝ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      (Set.Ioo (-Real.pi) Real.pi) volume :=
    integrableOn_normSq_polarCoord_symm hg_an hr_pos hr_lt
  -- Unfold `circleMeanSq` and apply `setIntegral_mono_on`.
  unfold circleMeanSq
  refine setIntegral_mono_on hf_int hg_int measurableSet_Ioo ?_
  intro θ _
  -- The polar-symm point lies in `UnitDisk` (since `r < 1`) and has norm `r`,
  -- which exceeds `c`. So the outer pointwise hypothesis applies.
  set z : ℂ := Complex.polarCoord.symm (r, θ) with hz_def
  have h_norm_z : ‖z‖ = r := by
    rw [hz_def, Complex.norm_polarCoord_symm, abs_of_pos hr_pos]
  have h_mem_UD : z ∈ UnitDisk :=
    (polarCoord_symm_mem_unitDisk_iff hr_pos).mpr hr_lt
  have h_c_lt_norm : c < ‖z‖ := by rw [h_norm_z]; exact hr_gt_c
  -- Apply the outer pointwise dominance hypothesis.
  have h_pt : ‖f z‖ ≤ ‖g z‖ := h_outer z h_mem_UD h_c_lt_norm
  -- Square via `pow_le_pow_left₀` on `‖·‖`.
  exact pow_le_pow_left₀ (norm_nonneg _) h_pt 2

/-! ## (3) Cross-function corollary. -/

/-- **Cross-function corollary.**  For `f, g : ℂ → ℂ` analytic on
`UnitDisk` with `‖f z‖ ≤ ‖g z‖` whenever `z ∈ UnitDisk` and `c < ‖z‖`,
every `r ∈ (c, 1)` and every `k : ℕ` satisfy
`(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq g r`,
where `a_k := (cauchyPowerSeries f 0 R).coeff k` for any
`R ∈ (0, 1)`.

The proof chains
`cauchyPowerSeries_normSq_pow_le_circleMeanSq` at `f` with
`outer_circleMeanSq_dom_of_pointwise_dom` via `le_trans`. -/
theorem cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_gt_c : c < r) (hr_lt : r < 1) (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ circleMeanSq g r := by
  have hr_pos : 0 < r := lt_trans hc hr_gt_c
  -- Step (1): single-coefficient L² estimate at f.
  have h1 :
      (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
        ≤ circleMeanSq f r :=
    cauchyPowerSeries_normSq_pow_le_circleMeanSq hf_an hR_pos hR_lt hr_pos hr_lt k
  -- Step (2): outer-annulus circleMean dominance from outer pointwise dominance.
  have h2 : circleMeanSq f r ≤ circleMeanSq g r :=
    outer_circleMeanSq_dom_of_pointwise_dom hf_an hg_an hc hc1 h_outer
      hr_gt_c hr_lt
  -- Compose.
  exact le_trans h1 h2

end ProofRefinement.Korenblum
