import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval

/-!
# Half-disc Bergman A² Parseval expansions (sprint 015)

This file is the **inner / outer Bergman A²-level Parseval consumer**. It
lifts sprint 011's whole-disc Parseval identity

```
bergmanNormSq f = ∑' k, (π / (k + 1)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²
```

to the two halves of the inner-disk / outer-annulus split at radius `c`:

```
∫ z in outerAnnulus c, ‖f z‖² ∂vol
  = ∑' k, (π / (k + 1)) * (1 - c^(2k+2)) * ‖a_k‖²
∫ z in innerDisk c, ‖f z‖² ∂vol
  = ∑' k, (π / (k + 1)) * c^(2k+2) * ‖a_k‖²
```

The proof structure is a direct mirror of sprint 011, with the radial domain
restricted to `Ioo c 1` (outer) or `Ioc 0 c` (inner). The key surface deltas
are:

* Replace `bergmanNormSq_radial_polar` (sprint 003 whole-disc) with
  `outerAnnulus_norm_sq_polar` / `innerDisk_norm_sq_polar` (sprint 003
  half-disc).
* Replace the per-term radial integral
  `∫ r in Ioo 0 1, r^(2k+1) dr = 1/(2k+2)`
  with the half-interval evaluations
  `∫ r in Ioo c 1, r^(2k+1) dr = (1 - c^(2k+2))/(2k+2)`
  `∫ r in Ioc 0 c, r^(2k+1) dr = c^(2k+2)/(2k+2)`,
  both via `intervalIntegral.integral_pow`.

The four headline theorems shipped:

* `outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`
* `innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries`
* `outerAnnulus_bergmanNormSq_termwise_mono`
* `innerDisk_bergmanNormSq_termwise_mono`

The two `_termwise_mono` consumers are the cross-function
half-disc analogues of sprint 011's `bergmanNormSq_termwise_mono`.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## Per-term integrand and integrability on half-intervals. -/

/-- Per-term integrand: `(2π · ‖a k‖²) * r^(2k+1)`. Same shape as sprint 011. -/
private noncomputable def halfRadialTerm
    (a : ℕ → ℂ) (k : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1)

/-- Each per-term radial integrand is integrable on `Ioo c 1` for any `c`. -/
private lemma halfRadialTerm_integrable_Ioo (a : ℕ → ℂ) (k : ℕ) (c : ℝ) :
    IntegrableOn (halfRadialTerm a k) (Set.Ioo c 1) volume := by
  unfold halfRadialTerm
  have hcont : Continuous fun r : ℝ => (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) :=
    continuous_const.mul (continuous_pow _)
  exact (hcont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self

/-- Each per-term radial integrand is integrable on `Ioc 0 c` for any `c`. -/
private lemma halfRadialTerm_integrable_Ioc (a : ℕ → ℂ) (k : ℕ) (c : ℝ) :
    IntegrableOn (halfRadialTerm a k) (Set.Ioc (0 : ℝ) c) volume := by
  unfold halfRadialTerm
  have hcont : Continuous fun r : ℝ => (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) :=
    continuous_const.mul (continuous_pow _)
  exact hcont.integrableOn_Ioc

/-- Each per-term radial integrand is nonneg on a nonneg radius. -/
private lemma halfRadialTerm_nonneg
    (a : ℕ → ℂ) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ halfRadialTerm a k r := by
  unfold halfRadialTerm
  have h_pi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
  have h_ak : 0 ≤ ‖a k‖ ^ 2 := by positivity
  have h_const : 0 ≤ 2 * Real.pi * ‖a k‖ ^ 2 := mul_nonneg h_pi h_ak
  have h_rk : 0 ≤ r ^ (2 * k + 1) := by positivity
  exact mul_nonneg h_const h_rk

/-! ## Per-term half-interval integral evaluations. -/

/-- Per-term integral on `Ioo c 1`:
`∫ r ∈ Ioo c 1, (2π · ‖a k‖²) * r^(2k+1) dr = (π/(k+1)) * (1 - c^(2k+2)) * ‖a k‖²`. -/
private lemma halfRadialTerm_integral_outer
    (a : ℕ → ℂ) (k : ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ r in Set.Ioo c 1, halfRadialTerm a k r
      = (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2 := by
  unfold halfRadialTerm
  rw [integral_const_mul]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [show (∫ r in Set.Ioc c 1, r ^ (2 * k + 1))
      = ∫ r in c..1, r ^ (2 * k + 1) from
        (intervalIntegral.integral_of_le hc1).symm]
  rw [integral_pow]
  have h_pow_one : (1 : ℝ) ^ (2 * k + 1 + 1) = 1 := one_pow _
  rw [h_pow_one]
  -- Goal: `(2π * ‖a k‖²) * ((1 - c^(2k+1+1)) / ((2k+1)+1 : ℕ→ℝ))
  --     = (π/(k+1)) * (1 - c^(2k+2)) * ‖a k‖²`.
  -- `2k+1+1 = 2k+2` arithmetically; cast `(2k+1)+1` to ℝ.
  have hk_ne : ((k : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    linarith
  have h_pow_eq : c ^ (2 * k + 1 + 1) = c ^ (2 * k + 2) := by
    rfl
  rw [h_pow_eq]
  push_cast
  field_simp
  ring

/-- Per-term integral on `Ioc 0 c`:
`∫ r ∈ Ioc 0 c, (2π · ‖a k‖²) * r^(2k+1) dr = (π/(k+1)) * c^(2k+2) * ‖a k‖²`. -/
private lemma halfRadialTerm_integral_inner
    (a : ℕ → ℂ) (k : ℕ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∫ r in Set.Ioc (0 : ℝ) c, halfRadialTerm a k r
      = (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2 := by
  unfold halfRadialTerm
  rw [integral_const_mul]
  rw [show (∫ r in Set.Ioc (0 : ℝ) c, r ^ (2 * k + 1))
      = ∫ r in (0 : ℝ)..c, r ^ (2 * k + 1) from
        (intervalIntegral.integral_of_le hc_nonneg).symm]
  rw [integral_pow]
  have h_pow_zero : (0 : ℝ) ^ (2 * k + 1 + 1) = 0 := by
    apply zero_pow; omega
  rw [h_pow_zero]
  have hk_ne : ((k : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    linarith
  have h_pow_eq : c ^ (2 * k + 1 + 1) = c ^ (2 * k + 2) := by
    rfl
  rw [h_pow_eq]
  push_cast
  field_simp
  ring

/-! ## Pointwise integrand identity (per-`r` Parseval). -/

/-- Pointwise-in-`r ∈ (0,1)` rewrite of the radial integrand
`circleMeanSq f r * r` as a `tsum` of `halfRadialTerm` summands.

This is identical in shape to sprint 011's `integrand_eq_tsum`, but
expressed for any `r ∈ (0, 1)`, which covers both half-intervals. -/
private lemma integrand_eq_tsum_half
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    circleMeanSq f r * r
      = ∑' k : ℕ,
          halfRadialTerm
            (fun k => (cauchyPowerSeries f 0 R).coeff k) k r := by
  -- Use the same canonical-witness Parseval identity at `R'(r) := ⟨(r+1)/2, _⟩`.
  set rval : ℝ := (r + 1) / 2 with hrval_def
  have hrval_pos : 0 < rval := by
    have h1 : 0 < r + 1 := by linarith
    rw [hrval_def]; linarith
  have hrval_lt_one : rval < 1 := by
    rw [hrval_def]; linarith
  have hr_lt_rval : r < rval := by
    rw [hrval_def]; linarith
  have hrval_nonneg : 0 ≤ rval := le_of_lt hrval_pos
  set R' : ℝ≥0 := ⟨rval, hrval_nonneg⟩ with hR'_def
  have hR'_pos : (0 : ℝ) < (R' : ℝ) := hrval_pos
  have hR'_lt : (R' : ℝ) < 1 := hrval_lt_one
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_lt_R' : r < (R' : ℝ) := hr_lt_rval
  rw [circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hf hR'_pos hR'_lt hr_nonneg hr_lt_R']
  -- Canonicalise coefficient norms.
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR'_pos hR'_lt hR_pos hR_lt
  -- Multiply by `r` and reshape.
  rw [← tsum_mul_right]
  refine tsum_congr (fun k => ?_)
  unfold halfRadialTerm
  have h_pow : r ^ (2 * k + 1) = r ^ (2 * k) * r := pow_succ r (2 * k)
  rw [h_pow, h_norm k]
  ring

/-- Per-`r` summability of the `halfRadialTerm` summands for any `r ∈ (0,1)`. -/
private lemma summable_halfRadialTerm_at
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Summable (fun k : ℕ =>
      halfRadialTerm
        (fun k => (cauchyPowerSeries f 0 R).coeff k) k r) := by
  -- Reuse the public summability fact built into sprint 011's
  -- `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
  -- proof. The sprint 011 helper is `private`, so we re-derive directly.
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
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
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
  -- Multiply by `2π * r` to get the `halfRadialTerm` shape.
  have h_summable_2pi : Summable (fun n : ℕ =>
      (2 * Real.pi * r ^ (2 * n))
        * ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2) := by
    have h := h_summable_R.mul_left (2 * Real.pi)
    convert h using 1
    funext n
    ring
  have h_final : Summable (fun n : ℕ =>
      halfRadialTerm
        (fun k => (cauchyPowerSeries f 0 R).coeff k) n r) := by
    have h := h_summable_2pi.mul_right r
    convert h using 1
    funext n
    unfold halfRadialTerm
    rw [show r ^ (2 * n + 1) = r ^ (2 * n) * r from pow_succ r (2 * n)]
    ring
  exact h_final

/-! ## Outer half: integrability of the radial integrand on `Ioo c 1`. -/

/-- Integrability of `r ↦ circleMeanSq f r * r` on `Ioo c 1`, derived from
the polar integrability hypothesis on `Ioo c 1 ×ˢ Ioo (-π) π`. -/
private lemma integrableOn_circleMeanSq_mul_radius_outer
    {f : ℂ → ℂ} {c : ℝ}
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioo c 1) volume := by
  have hf_int : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioo c 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hf_polar
  have h_int_left := hf_int.integral_prod_left
  rw [IntegrableOn]
  refine h_int_left.congr ?_
  refine Filter.Eventually.of_forall (fun r => ?_)
  unfold circleMeanSq
  change (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      = (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2) * r
  rw [integral_const_mul, mul_comm]

/-! ## Inner half: integrability of the radial integrand on `Ioc 0 c`. -/

/-- Integrability of `r ↦ circleMeanSq f r * r` on `Ioc 0 c`, derived from
the polar integrability hypothesis on `Ioo 0 c ×ˢ Ioo (-π) π` (the open
form, since `{c}` has measure zero in the product measure). -/
private lemma integrableOn_circleMeanSq_mul_radius_inner
    {f : ℂ → ℂ} {c : ℝ}
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioc (0 : ℝ) c) volume := by
  -- Convert hypothesis from `Ioo 0 c` to `Ioc 0 c` (extending by a measure-
  -- zero set).
  have h_eq_restrict :
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) c)
        = (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) c) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc
  -- Build the product-measure version.
  have hf_int_Ioo : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) c)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hf_polar
  have hf_int_Ioc : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) c)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [← h_eq_restrict]
    exact hf_int_Ioo
  have h_int_left := hf_int_Ioc.integral_prod_left
  rw [IntegrableOn]
  refine h_int_left.congr ?_
  refine Filter.Eventually.of_forall (fun r => ?_)
  unfold circleMeanSq
  change (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      = (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2) * r
  rw [integral_const_mul, mul_comm]

/-! ## Outer half: Bergman A² Parseval expansion. -/

/-- **Outer-annulus Bergman A² Parseval expansion.**

For `f : ℂ → ℂ` analytic on `UnitDisk`, `c ∈ (0, 1)`, and any chosen NNReal
`R ∈ (0, 1)`, given the polar integrability hypothesis on
`Ioo c 1 ×ˢ Ioo (-π) π`, the outer-annulus integral expands as

```
∫ z in outerAnnulus c, ‖f z‖² ∂vol
  = ∑' k, (π / (k + 1)) * (1 - c^(2k+2)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²
```

The proof mirrors sprint 011's whole-disc Parseval identity, with the
radial domain restricted to `Ioo c 1` and the per-term integral
`(1 - c^(2k+2))/(2k+2)` instead of `1/(2k+2)`. -/
theorem outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
  set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hc1_le : c ≤ 1 := le_of_lt hc1
  -- Step A: rewrite `∫ z in outerAnnulus c, ‖f z‖²` via the radial polar form.
  rw [outerAnnulus_norm_sq_polar f c hc_nonneg hc1 hf_polar]
  -- Step B: integrability of `r ↦ circleMeanSq f r * r` on `Ioo c 1`.
  have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioo c 1) volume :=
    integrableOn_circleMeanSq_mul_radius_outer hf_polar
  -- Step C: nonnegativity on `Ioo c 1`.
  have h_radial_nonneg : ∀ r ∈ Set.Ioo c 1, 0 ≤ circleMeanSq f r * r := by
    intro r hr
    have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
    have h_cm_nonneg : 0 ≤ circleMeanSq f r := by
      unfold circleMeanSq
      exact integral_nonneg (fun _ => sq_nonneg _)
    exact mul_nonneg h_cm_nonneg (le_of_lt hr_pos)
  -- Step D: per-r identity:
  -- circleMeanSq f r * r = ∑' k, halfRadialTerm a k r for r ∈ Ioo c 1.
  have h_pointwise_eq : ∀ r ∈ Set.Ioo c 1,
      circleMeanSq f r * r
        = ∑' k : ℕ, halfRadialTerm a k r := by
    intro r hr
    have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
    exact integrand_eq_tsum_half hf hR_pos hR_lt hr_pos hr.2
  -- Step E: per-r summability.
  have h_summable_r : ∀ r ∈ Set.Ioo c 1,
      Summable (fun k : ℕ => halfRadialTerm a k r) := by
    intro r hr
    have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
    exact summable_halfRadialTerm_at hf hR_pos hR_lt hr_pos hr.2
  -- Step F: term nonnegativity. Each `(π/(k+1)) (1 - c^(2k+2)) ‖a k‖²` ≥ 0.
  have h_pi_summand_nonneg : ∀ k : ℕ,
      0 ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2 := by
    intro k
    have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg Real.pi_nonneg
      positivity
    have h_one_minus : 0 ≤ 1 - c ^ (2 * k + 2) := by
      have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 := by
        exact pow_le_one₀ hc_nonneg hc1_le
      linarith
    have h_const_nn : 0 ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) :=
      mul_nonneg h_pi_div h_one_minus
    exact mul_nonneg h_const_nn (by positivity)
  -- Step G: bound partial sums by the radial integral.
  have h_total_eq : (∫ r in Set.Ioo c 1, circleMeanSq f r * r)
      = ∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ) :=
    (outerAnnulus_norm_sq_polar f c hc_nonneg hc1 hf_polar).symm
  have h_partial_bound : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2)
        ≤ ∫ r in Set.Ioo c 1, circleMeanSq f r * r := by
    intro N
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2
        = ∫ r in Set.Ioo c 1,
            ∑ k ∈ Finset.range N, halfRadialTerm a k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioo a k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_outer a k hc_nonneg hc1_le).symm
    rw [h_finite_sum_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioo a k c)
    · have h_summ_r := h_summable_r r hr
      have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm a k r)
          ≤ ∑' k, halfRadialTerm a k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg a k (le_of_lt hr_pos))
          h_summ_r
      rw [h_pointwise_eq r hr]
      exact h_partial_le
  -- Step H: summability of `fun k => (π/(k+1)) (1 - c^(2k+2)) ‖a k‖²`.
  have h_summable_final : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2) := by
    refine summable_of_sum_range_le
      (c := ∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      h_pi_summand_nonneg ?_
    intro N
    exact (h_partial_bound N).trans (le_of_eq h_total_eq)
  -- Step I: apply `integral_tsum_of_summable_integral_norm`.
  have h_summable_norm_int : Summable (fun k : ℕ =>
      ∫ r in Set.Ioo c 1, ‖halfRadialTerm a k r‖) := by
    have h_eq : ∀ k : ℕ,
        (∫ r in Set.Ioo c 1, ‖halfRadialTerm a k r‖)
          = (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2 := by
      intro k
      rw [show (∫ r in Set.Ioo c 1, ‖halfRadialTerm a k r‖)
          = ∫ r in Set.Ioo c 1, halfRadialTerm a k r from ?_]
      · exact halfRadialTerm_integral_outer a k hc_nonneg hc1_le
      refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
      have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
      have h_nn := halfRadialTerm_nonneg a k (le_of_lt hr_pos)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    refine (h_summable_final).congr (fun k => ?_)
    exact (h_eq k).symm
  have h_integrable_each : ∀ k : ℕ,
      Integrable (halfRadialTerm a k) (volume.restrict (Set.Ioo c 1)) :=
    fun k => halfRadialTerm_integrable_Ioo a k c
  have h_swap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioo c 1))
    (F := halfRadialTerm a)
    h_integrable_each h_summable_norm_int
  -- Step J: combine.
  have h_rhs_eq : (∫ r in Set.Ioo c 1, ∑' k : ℕ, halfRadialTerm a k r)
      = ∫ r in Set.Ioo c 1, circleMeanSq f r * r := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    exact (h_pointwise_eq r hr).symm
  have h_lhs_eq : (∑' k : ℕ,
      ∫ r in Set.Ioo c 1, halfRadialTerm a k r)
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) * ‖a k‖ ^ 2 := by
    refine tsum_congr (fun k => ?_)
    exact halfRadialTerm_integral_outer a k hc_nonneg hc1_le
  rw [← h_rhs_eq, ← h_swap, h_lhs_eq]

/-! ## Inner half: Bergman A² Parseval expansion. -/

/-- **Inner-disk Bergman A² Parseval expansion.**

For `f : ℂ → ℂ` analytic on `UnitDisk`, `c ∈ (0, 1)`, and any chosen NNReal
`R ∈ (0, 1)`, given the polar integrability hypothesis on
`Ioo 0 c ×ˢ Ioo (-π) π`, the inner-disk integral expands as

```
∫ z in innerDisk c, ‖f z‖² ∂vol
  = ∑' k, (π / (k + 1)) * c^(2k+2) * ‖(cauchyPowerSeries f 0 R).coeff k‖²
```

Mirror of the outer half, with `Ioo c 1` replaced by `Ioc 0 c` and
`(1 - c^(2k+2))` replaced by `c^(2k+2)`. The hypothesis is on `Ioo 0 c`
(open), bridged to `Ioc 0 c` at the polar pull-back step via
`Measure.restrict_Ioo_eq_restrict_Ioc` (the boundary point `r = c` has
measure zero). -/
theorem innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
  set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  -- Step A0: bridge hypothesis from `Ioo 0 c ×ˢ ...` to `Ioc 0 c ×ˢ ...`.
  have h_eq_restrict :
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) c)
        = (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) c) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc
  have hf_polar_Ioc : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (Set.Ioc (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
    -- IntegrableOn _ S μ = Integrable _ (μ.restrict S). The two restricts agree.
    have hf_int_Ioo : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioo (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict]
      exact hf_polar
    have hf_int_Ioc : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioc (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [← h_eq_restrict]
      exact hf_int_Ioo
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf_int_Ioc
  -- Step A: rewrite `∫ z in innerDisk c, ‖f z‖²` via the radial polar form.
  rw [innerDisk_norm_sq_polar f c hc_nonneg hc1 hf_polar_Ioc]
  -- Step B: integrability of `r ↦ circleMeanSq f r * r` on `Ioc 0 c`.
  have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioc (0 : ℝ) c) volume :=
    integrableOn_circleMeanSq_mul_radius_inner hf_polar
  -- Step C: nonnegativity on `Ioc 0 c`.
  have h_radial_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) c, 0 ≤ circleMeanSq f r * r := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have h_cm_nonneg : 0 ≤ circleMeanSq f r := by
      unfold circleMeanSq
      exact integral_nonneg (fun _ => sq_nonneg _)
    exact mul_nonneg h_cm_nonneg (le_of_lt hr_pos)
  -- Step D: per-r identity for r ∈ Ioc 0 c (note: r ≤ c < 1 so r < 1).
  have h_pointwise_eq : ∀ r ∈ Set.Ioc (0 : ℝ) c,
      circleMeanSq f r * r
        = ∑' k : ℕ, halfRadialTerm a k r := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_lt_one : r < 1 := lt_of_le_of_lt hr.2 hc1
    exact integrand_eq_tsum_half hf hR_pos hR_lt hr_pos hr_lt_one
  -- Step E: per-r summability.
  have h_summable_r : ∀ r ∈ Set.Ioc (0 : ℝ) c,
      Summable (fun k : ℕ => halfRadialTerm a k r) := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have hr_lt_one : r < 1 := lt_of_le_of_lt hr.2 hc1
    exact summable_halfRadialTerm_at hf hR_pos hR_lt hr_pos hr_lt_one
  -- Step F: term nonnegativity. Each `(π/(k+1)) c^(2k+2) ‖a k‖²` ≥ 0.
  have h_pi_summand_nonneg : ∀ k : ℕ,
      0 ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2 := by
    intro k
    have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg Real.pi_nonneg
      positivity
    have h_pow_nn : 0 ≤ c ^ (2 * k + 2) := by positivity
    have h_const_nn : 0 ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) :=
      mul_nonneg h_pi_div h_pow_nn
    exact mul_nonneg h_const_nn (by positivity)
  -- Step G: bound partial sums by the radial integral.
  have h_total_eq : (∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq f r * r)
      = ∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ) :=
    (innerDisk_norm_sq_polar f c hc_nonneg hc1 hf_polar_Ioc).symm
  have h_partial_bound : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2)
        ≤ ∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq f r * r := by
    intro N
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2
        = ∫ r in Set.Ioc (0 : ℝ) c,
            ∑ k ∈ Finset.range N, halfRadialTerm a k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioc a k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_inner a k hc_nonneg).symm
    rw [h_finite_sum_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioc (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioc a k c)
    · have h_summ_r := h_summable_r r hr
      have hr_pos : 0 < r := hr.1
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm a k r)
          ≤ ∑' k, halfRadialTerm a k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg a k (le_of_lt hr_pos))
          h_summ_r
      rw [h_pointwise_eq r hr]
      exact h_partial_le
  -- Step H: summability.
  have h_summable_final : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2) := by
    refine summable_of_sum_range_le
      (c := ∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      h_pi_summand_nonneg ?_
    intro N
    exact (h_partial_bound N).trans (le_of_eq h_total_eq)
  -- Step I: apply integral_tsum_of_summable_integral_norm.
  have h_summable_norm_int : Summable (fun k : ℕ =>
      ∫ r in Set.Ioc (0 : ℝ) c, ‖halfRadialTerm a k r‖) := by
    have h_eq : ∀ k : ℕ,
        (∫ r in Set.Ioc (0 : ℝ) c, ‖halfRadialTerm a k r‖)
          = (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2 := by
      intro k
      rw [show (∫ r in Set.Ioc (0 : ℝ) c, ‖halfRadialTerm a k r‖)
          = ∫ r in Set.Ioc (0 : ℝ) c, halfRadialTerm a k r from ?_]
      · exact halfRadialTerm_integral_inner a k hc_nonneg
      refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
      have hr_pos : 0 < r := hr.1
      have h_nn := halfRadialTerm_nonneg a k (le_of_lt hr_pos)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    refine (h_summable_final).congr (fun k => ?_)
    exact (h_eq k).symm
  have h_integrable_each : ∀ k : ℕ,
      Integrable (halfRadialTerm a k) (volume.restrict (Set.Ioc (0 : ℝ) c)) :=
    fun k => halfRadialTerm_integrable_Ioc a k c
  have h_swap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) c))
    (F := halfRadialTerm a)
    h_integrable_each h_summable_norm_int
  -- Step J: combine.
  have h_rhs_eq : (∫ r in Set.Ioc (0 : ℝ) c, ∑' k : ℕ, halfRadialTerm a k r)
      = ∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq f r * r := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    exact (h_pointwise_eq r hr).symm
  have h_lhs_eq : (∑' k : ℕ,
      ∫ r in Set.Ioc (0 : ℝ) c, halfRadialTerm a k r)
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) * ‖a k‖ ^ 2 := by
    refine tsum_congr (fun k => ?_)
    exact halfRadialTerm_integral_inner a k hc_nonneg
  rw [← h_rhs_eq, ← h_swap, h_lhs_eq]

/-! ## Termwise comparison consumers. -/

/-- **Outer-annulus termwise comparison consumer.**

For two analytic `f, g : ℂ → ℂ` on `UnitDisk` with the polar integrability
hypotheses on `Ioo c 1 ×ˢ Ioo (-π) π`, if their canonical Cauchy power-
series coefficient norms satisfy `‖a_k‖ ≤ ‖b_k‖` for all `k`, then the
outer-annulus integrals are ordered. -/
theorem outerAnnulus_bergmanNormSq_termwise_mono
    {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk) (hg : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hg_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (h_coeff : ∀ k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖
          ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      ≤ ∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ) := by
  rw [outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries
        hf hc hc1 hR_pos hR_lt hf_polar]
  rw [outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries
        hg hc hc1 hR_pos hR_lt hg_polar]
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hc1_le : c ≤ 1 := le_of_lt hc1
  -- Termwise comparison.
  have h_term_le : ∀ k : ℕ,
      (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
          * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
          * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
    intro k
    have h_pi_div_nonneg : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg Real.pi_nonneg
      positivity
    have h_one_minus : 0 ≤ 1 - c ^ (2 * k + 2) := by
      have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 := pow_le_one₀ hc_nonneg hc1_le
      linarith
    have h_const_nn : 0 ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2)) :=
      mul_nonneg h_pi_div_nonneg h_one_minus
    have h_sq_le : ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h_coeff k) 2
    exact mul_le_mul_of_nonneg_left h_sq_le h_const_nn
  -- Summability of both sides via the Parseval expansion.
  have h_summable_f : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
    -- Each term is nonneg; partial sums are bounded by the outer-annulus
    -- integral (which equals the tsum after shipping).
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
      intro k
      have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
        apply div_nonneg Real.pi_nonneg
        positivity
      have h_one_minus : 0 ≤ 1 - c ^ (2 * k + 2) := by
        have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 := pow_le_one₀ hc_nonneg hc1_le
        linarith
      exact mul_nonneg (mul_nonneg h_pi_div h_one_minus) (by positivity)
    -- Mirror the partial-sum bound from the proof of the Parseval identity.
    set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
    refine summable_of_sum_range_le
      (c := ∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      h_nn ?_
    intro N
    have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
        (Set.Ioo c 1) volume :=
      integrableOn_circleMeanSq_mul_radius_outer hf_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioo c 1,
            ∑ k ∈ Finset.range N, halfRadialTerm a k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioo a k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_outer a k hc_nonneg hc1_le).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioo c 1, circleMeanSq f r * r)
        = ∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ) :=
      (outerAnnulus_norm_sq_polar f c hc_nonneg hc1 hf_polar).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioo a k c)
    · have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
      have h_summ_r := summable_halfRadialTerm_at hf hR_pos hR_lt hr_pos hr.2
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm a k r)
          ≤ ∑' k, halfRadialTerm a k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg a k (le_of_lt hr_pos))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum_half hf hR_pos hR_lt hr_pos hr.2
      rw [h_pt_eq]
      exact h_partial_le
  have h_summable_g : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2) := by
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
      intro k
      have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
        apply div_nonneg Real.pi_nonneg
        positivity
      have h_one_minus : 0 ≤ 1 - c ^ (2 * k + 2) := by
        have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 := pow_le_one₀ hc_nonneg hc1_le
        linarith
      exact mul_nonneg (mul_nonneg h_pi_div h_one_minus) (by positivity)
    set b : ℕ → ℂ := fun k => (cauchyPowerSeries g 0 R).coeff k with hb_def
    refine summable_of_sum_range_le
      (c := ∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ))
      h_nn ?_
    intro N
    have h_radial_int : IntegrableOn (fun r => circleMeanSq g r * r)
        (Set.Ioo c 1) volume :=
      integrableOn_circleMeanSq_mul_radius_outer hg_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
            * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioo c 1,
            ∑ k ∈ Finset.range N, halfRadialTerm b k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioo b k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_outer b k hc_nonneg hc1_le).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioo c 1, circleMeanSq g r * r)
        = ∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ) :=
      (outerAnnulus_norm_sq_polar g c hc_nonneg hc1 hg_polar).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioo b k c)
    · have hr_pos : 0 < r := lt_of_lt_of_le hc (le_of_lt hr.1)
      have h_summ_r := summable_halfRadialTerm_at hg hR_pos hR_lt hr_pos hr.2
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm b k r)
          ≤ ∑' k, halfRadialTerm b k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg b k (le_of_lt hr_pos))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum_half hg hR_pos hR_lt hr_pos hr.2
      rw [h_pt_eq]
      exact h_partial_le
  exact h_summable_f.tsum_le_tsum h_term_le h_summable_g

/-- **Inner-disk termwise comparison consumer.**

For two analytic `f, g : ℂ → ℂ` on `UnitDisk` with the polar integrability
hypotheses on `Ioo 0 c ×ˢ Ioo (-π) π`, if their canonical Cauchy power-
series coefficient norms satisfy `‖a_k‖ ≤ ‖b_k‖` for all `k`, then the
inner-disk integrals are ordered. -/
theorem innerDisk_bergmanNormSq_termwise_mono
    {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk) (hg : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hg_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (h_coeff : ∀ k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖
          ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      ≤ ∫ z in innerDisk c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ) := by
  rw [innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries
        hf hc hc1 hR_pos hR_lt hf_polar]
  rw [innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries
        hg hc hc1 hR_pos hR_lt hg_polar]
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  -- Bridge `Ioo 0 c` polar hypotheses to `Ioc 0 c` for the inner half
  -- partial-sum bound (only needed for re-deriving summability).
  have h_eq_restrict :
      (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) c)
        = (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) c) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc
  have hf_polar_Ioc : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (Set.Ioc (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
    have hf_int_Ioo : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioo (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict]
      exact hf_polar
    have hf_int_Ioc : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioc (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [← h_eq_restrict]
      exact hf_int_Ioo
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf_int_Ioc
  have hg_polar_Ioc : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
      (Set.Ioc (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
    have hg_int_Ioo : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioo (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict]
      exact hg_polar
    have hg_int_Ioc : Integrable
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        ((volume.restrict (Set.Ioc (0 : ℝ) c)).prod
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
      rw [← h_eq_restrict]
      exact hg_int_Ioo
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hg_int_Ioc
  -- Termwise comparison.
  have h_term_le : ∀ k : ℕ,
      (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
          * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
          * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
    intro k
    have h_pi_div_nonneg : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg Real.pi_nonneg
      positivity
    have h_pow_nn : 0 ≤ c ^ (2 * k + 2) := by positivity
    have h_const_nn : 0 ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2) :=
      mul_nonneg h_pi_div_nonneg h_pow_nn
    have h_sq_le : ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h_coeff k) 2
    exact mul_le_mul_of_nonneg_left h_sq_le h_const_nn
  -- Summability of both sides via the Parseval expansion.
  have h_summable_f : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
      intro k
      have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
        apply div_nonneg Real.pi_nonneg
        positivity
      have h_pow_nn : 0 ≤ c ^ (2 * k + 2) := by positivity
      exact mul_nonneg (mul_nonneg h_pi_div h_pow_nn) (by positivity)
    set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
    refine summable_of_sum_range_le
      (c := ∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      h_nn ?_
    intro N
    have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
        (Set.Ioc (0 : ℝ) c) volume :=
      integrableOn_circleMeanSq_mul_radius_inner hf_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioc (0 : ℝ) c,
            ∑ k ∈ Finset.range N, halfRadialTerm a k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioc a k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_inner a k hc_nonneg).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq f r * r)
        = ∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ) :=
      (innerDisk_norm_sq_polar f c hc_nonneg hc1 hf_polar_Ioc).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioc (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioc a k c)
    · have hr_pos : 0 < r := hr.1
      have hr_lt_one : r < 1 := lt_of_le_of_lt hr.2 hc1
      have h_summ_r := summable_halfRadialTerm_at hf hR_pos hR_lt hr_pos hr_lt_one
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm a k r)
          ≤ ∑' k, halfRadialTerm a k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg a k (le_of_lt hr_pos))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum_half hf hR_pos hR_lt hr_pos hr_lt_one
      rw [h_pt_eq]
      exact h_partial_le
  have h_summable_g : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2) := by
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
      intro k
      have h_pi_div : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
        apply div_nonneg Real.pi_nonneg
        positivity
      have h_pow_nn : 0 ≤ c ^ (2 * k + 2) := by positivity
      exact mul_nonneg (mul_nonneg h_pi_div h_pow_nn) (by positivity)
    set b : ℕ → ℂ := fun k => (cauchyPowerSeries g 0 R).coeff k with hb_def
    refine summable_of_sum_range_le
      (c := ∫ z in innerDisk c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ))
      h_nn ?_
    intro N
    have h_radial_int : IntegrableOn (fun r => circleMeanSq g r * r)
        (Set.Ioc (0 : ℝ) c) volume :=
      integrableOn_circleMeanSq_mul_radius_inner hg_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
            * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioc (0 : ℝ) c,
            ∑ k ∈ Finset.range N, halfRadialTerm b k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => halfRadialTerm_integrable_Ioc b k c)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (halfRadialTerm_integral_inner b k hc_nonneg).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq g r * r)
        = ∫ z in innerDisk c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ) :=
      (innerDisk_norm_sq_polar g c hc_nonneg hc1 hg_polar_Ioc).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioc (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => halfRadialTerm_integrable_Ioc b k c)
    · have hr_pos : 0 < r := hr.1
      have hr_lt_one : r < 1 := lt_of_le_of_lt hr.2 hc1
      have h_summ_r := summable_halfRadialTerm_at hg hR_pos hR_lt hr_pos hr_lt_one
      have h_partial_le : (∑ k ∈ Finset.range N, halfRadialTerm b k r)
          ≤ ∑' k, halfRadialTerm b k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => halfRadialTerm_nonneg b k (le_of_lt hr_pos))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum_half hg hR_pos hR_lt hr_pos hr_lt_one
      rw [h_pt_eq]
      exact h_partial_le
  exact h_summable_f.tsum_le_tsum h_term_le h_summable_g

end ProofRefinement.Korenblum
