import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial

/-!
# Bergman A² Parseval identity for analytic functions

This file is the **Bergman-A²-level consumer** of `Proof.CircleMeanRadial`
(sprint 010). It lifts the canonical-witness pointwise-in-`r` Parseval identity

```
circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²
```

(valid on `r ∈ [0, R)` for any NNReal `R ∈ (0, 1)`) to the
**Bergman A² level** by radial integration:

```
bergmanNormSq f = ∑' k, (π / (k + 1)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²
```

(valid for any chosen NNReal `R ∈ (0, 1)`, given the polar integrability
hypothesis required by `bergmanNormSq_radial_polar`).

We expose three theorems:

* `cauchyPowerSeries_coeff_norm_radius_invariant` — the radius-independence
  of coefficient norms via `HasFPowerSeriesAt.eq_formalMultilinearSeries`.

* `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` — the
  headline Bergman Parseval identity, via `bergmanNormSq_radial_polar`
  (sprint 003), sprint 010's canonical-witness identity at each radius
  composed with (1), and `MeasureTheory.integral_tsum_of_summable_integral_norm`
  to swap `∫` and `∑'`.

* `bergmanNormSq_termwise_mono` — the Bergman-level coefficient consumer:
  domination of the canonical Cauchy power-series coefficient norms
  transfers to domination of the Bergman A² norm via `tsum_le_tsum`.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## (1) Radius-independence of coefficient norms. -/

/-- Radius-independence of `cauchyPowerSeries`-coefficient norms.

For `f : ℂ → ℂ` analytic on `UnitDisk` and any two NNReal radii `R₁, R₂`
with `0 < (R_i : ℝ) < 1`, the Cauchy power-series coefficient *norms* at
the origin agree at every index. Internally the formal series themselves
agree by `HasFPowerSeriesAt.eq_formalMultilinearSeries`. -/
theorem cauchyPowerSeries_coeff_norm_radius_invariant
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R₁ R₂ : ℝ≥0}
    (hR₁_pos : 0 < (R₁ : ℝ)) (hR₁_lt : (R₁ : ℝ) < 1)
    (hR₂_pos : 0 < (R₂ : ℝ)) (hR₂_lt : (R₂ : ℝ) < 1) :
    ∀ k : ℕ,
      ‖(cauchyPowerSeries f 0 R₁).coeff k‖
        = ‖(cauchyPowerSeries f 0 R₂).coeff k‖ := by
  have h_subset : ∀ R : ℝ≥0, (R : ℝ) < 1 →
      Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ UnitDisk := by
    intro R hR_lt z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    change z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hR_lt
  have hf_diff : ∀ R : ℝ≥0, (R : ℝ) < 1 →
      DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) := by
    intro R hR_lt
    have h_an : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) :=
      hf.mono (h_subset R hR_lt)
    exact h_an.differentiableOn
  have h_fps₁ : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R₁) 0 (R₁ : ℝ≥0∞) :=
    (hf_diff R₁ hR₁_lt).hasFPowerSeriesOnBall hR₁_pos
  have h_fps₂ : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R₂) 0 (R₂ : ℝ≥0∞) :=
    (hf_diff R₂ hR₂_lt).hasFPowerSeriesOnBall hR₂_pos
  have h_at₁ : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R₁) 0 :=
    h_fps₁.hasFPowerSeriesAt
  have h_at₂ : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R₂) 0 :=
    h_fps₂.hasFPowerSeriesAt
  have h_eq : cauchyPowerSeries f 0 R₁ = cauchyPowerSeries f 0 R₂ :=
    h_at₁.eq_formalMultilinearSeries h_at₂
  intro k
  rw [h_eq]

/-! ## (2) Bergman Parseval identity. -/

/-- Per-term integrand: `(2π · ‖a k‖²) * r^(2k+1)`. -/
private noncomputable def parsevalRadialTerm
    (a : ℕ → ℂ) (k : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1)

/-- Each per-term radial integrand is integrable on `Ioo 0 1`. -/
private lemma parsevalRadialTerm_integrable
    (a : ℕ → ℂ) (k : ℕ) :
    IntegrableOn (parsevalRadialTerm a k) (Set.Ioo (0 : ℝ) 1) volume := by
  unfold parsevalRadialTerm
  have hcont : Continuous fun r : ℝ => (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) :=
    continuous_const.mul (continuous_pow _)
  exact (hcont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self

/-- Each per-term radial integrand is nonneg on `Ioo 0 1`. -/
private lemma parsevalRadialTerm_nonneg
    (a : ℕ → ℂ) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ parsevalRadialTerm a k r := by
  unfold parsevalRadialTerm
  have h_pi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
  have h_ak : 0 ≤ ‖a k‖ ^ 2 := by positivity
  have h_const : 0 ≤ 2 * Real.pi * ‖a k‖ ^ 2 := mul_nonneg h_pi h_ak
  have h_rk : 0 ≤ r ^ (2 * k + 1) := by positivity
  exact mul_nonneg h_const h_rk

/-- Per-term integral on `Ioo 0 1`: `∫ r ∈ Ioo 0 1, (2π · ‖a k‖²) * r^(2k+1) dr
= π/(k+1) * ‖a k‖²`. -/
private lemma parsevalRadialTerm_integral
    (a : ℕ → ℂ) (k : ℕ) :
    ∫ r in Set.Ioo (0 : ℝ) 1, parsevalRadialTerm a k r
      = (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2 := by
  unfold parsevalRadialTerm
  rw [integral_const_mul]
  -- Convert `Ioo` to `Ioc` and then to `intervalIntegral`.
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [show (∫ r in Set.Ioc (0 : ℝ) 1, r ^ (2 * k + 1))
      = ∫ r in (0 : ℝ)..1, r ^ (2 * k + 1) from
        (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm]
  rw [integral_pow]
  -- Simplify `(1^(2k+2) - 0^(2k+2)) / (2k+2) = 1/(2k+2)`.
  have h_pow_one : (1 : ℝ) ^ (2 * k + 1 + 1) = 1 := one_pow _
  have h_pow_zero : (0 : ℝ) ^ (2 * k + 1 + 1) = 0 := by
    apply zero_pow; omega
  rw [h_pow_one, h_pow_zero]
  have hk_ne : ((k : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    linarith
  push_cast
  field_simp
  ring

/-- Pointwise-in-`r ∈ Ioo 0 1` rewrite of `circleMeanSq f r` as a `tsum` of
canonical-radius coefficient terms.

For `f : ℂ → ℂ` analytic on `UnitDisk`, fix any NNReal `R ∈ (0, 1)`. Then
for every `r ∈ Ioo 0 1`, `circleMeanSq f r = ∑' k, (2π · r^(2k)) ‖(cps R).coeff k‖²`
where the witness coefficients are computed at the *fixed* `R`. The
radius-independence (1) is what unlocks this: for each `r ∈ Ioo 0 1` we
apply the canonical-witness identity at `R'(r) := ⟨(r+1)/2, _⟩`, then
canonicalise the coefficient norms. -/
private lemma circleMeanSq_eq_tsum_canonical
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    circleMeanSq f r =
      ∑' k : ℕ,
        (2 * Real.pi * r ^ (2 * k))
          * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
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
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR'_pos hR'_lt hR_pos hR_lt
  refine tsum_congr (fun k => ?_)
  rw [h_norm k]

/-- Pointwise-in-`r ∈ Ioo 0 1` rewrite of the radial integrand
`circleMeanSq f r * r` as a `tsum` of `parsevalRadialTerm` summands. -/
private lemma integrand_eq_tsum
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    circleMeanSq f r * r
      = ∑' k : ℕ,
          parsevalRadialTerm
            (fun k => (cauchyPowerSeries f 0 R).coeff k) k r := by
  rw [circleMeanSq_eq_tsum_canonical hf hR_pos hR_lt hr_pos hr_lt_one]
  rw [← tsum_mul_right]
  refine tsum_congr (fun k => ?_)
  unfold parsevalRadialTerm
  have h_pow : r ^ (2 * k + 1) = r ^ (2 * k) * r := pow_succ r (2 * k)
  rw [h_pow]
  ring

/-- Summability of the canonical-coefficient Parseval terms at each `r ∈ (0, 1)`.

For `f : ℂ → ℂ` analytic on `UnitDisk`, NNReal `R` with `0 < (R : ℝ) < 1`,
and `r ∈ (0, 1)`, the sequence
`fun k => (2π · r^(2k)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²` is summable.

Strategy: pick a per-`r` radius `R'(r) := ⟨(r+1)/2, _⟩` so that
`r < R'(r) < 1`. Then `cauchyPowerSeries f 0 R'(r)` has radius of
convergence ≥ `R'(r) > r`, so `‖(cps R'(r)) k‖ * r^k` is summable
(`FormalMultilinearSeries.summable_norm_mul_pow`). Squaring (since
the summand tends to 0, eventually `(·)² ≤ ·`) gives summability of
`‖(cps R'(r)).coeff k‖² * r^(2k)`. By (1), the coefficient norms agree
with those of the *canonical* `cps R`. Multiplying by the constant
`2π > 0` preserves summability. -/
private lemma summable_canonical_parseval_terms
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Summable (fun k : ℕ =>
      (2 * Real.pi * r ^ (2 * k))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
  -- Choose `R'(r) := ⟨(r+1)/2, _⟩` with `r < R'(r) < 1`.
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
  -- The cauchy power series at radius `R'` has radius of convergence ≥ R'.
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
  -- Radius of convergence is ≥ R'.
  have h_radius_ge : (R' : ℝ≥0∞) ≤ (cauchyPowerSeries f 0 R').radius :=
    h_fps'.r_le
  -- Cast `r : ℝ` to `r' : ℝ≥0` (using `r > 0`).
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
  -- Apply `summable_norm_mul_pow`.
  have h_summable_lin : Summable (fun n : ℕ =>
      ‖cauchyPowerSeries f 0 R' n‖ * (rNN : ℝ) ^ n) :=
    (cauchyPowerSeries f 0 R').summable_norm_mul_pow hrNN_lt
  -- Convert `‖p n‖` to `‖p.coeff n‖`. Also note `(rNN : ℝ) = r`.
  have hrNN_coe : ((rNN : ℝ≥0) : ℝ) = r := rfl
  have h_summable_lin' : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) := by
    convert h_summable_lin using 1
    funext n
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hrNN_coe]
  -- The summands are nonneg; tendsto 0 at `atTop`.
  have h_tendsto_zero : Tendsto (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) atTop (𝓝 0) :=
    h_summable_lin'.tendsto_atTop_zero
  -- Eventually, the summand is ≤ 1.
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
  -- Hence eventually `(‖coeff n‖ * r^n)² ≤ ‖coeff n‖ * r^n`, so the squared
  -- series is summable.
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
  -- Rewrite `(‖coeff‖ * r^n)² = ‖coeff‖² * r^(2n)`.
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
  -- Transfer the squared coefficient norms to those at the canonical `R` via (1).
  have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
    hf hR'_pos hR'_lt hR_pos hR_lt
  have h_summable_R : Summable (fun n : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2 * r ^ (2 * n)) := by
    convert h_summable_sq' using 1
    funext n
    rw [h_norm n]
  -- Multiply by `2π` and reorder.
  have h_summable_final : Summable (fun n : ℕ =>
      (2 * Real.pi * r ^ (2 * n))
        * ‖(cauchyPowerSeries f 0 R).coeff n‖ ^ 2) := by
    have h := h_summable_R.mul_left (2 * Real.pi)
    convert h using 1
    funext n
    ring
  exact h_summable_final

/-- Integrability of the radial integrand `r ↦ circleMeanSq f r * r` on
`Ioo 0 1`, derived from the polar integrability hypothesis via Fubini. -/
private lemma integrableOn_circleMeanSq_mul_radius
    {f : ℂ → ℂ}
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioo (0 : ℝ) 1) volume := by
  -- Convert `IntegrableOn (fun (r,θ) => ...) (Ioo 0 1 ×ˢ Ioo (-π) π)` to
  -- `Integrable (fun (r,θ) => ...) (vol.restrict (Ioo 0 1)).prod (vol.restrict (Ioo (-π) π))`.
  have hf_int : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hf_polar
  -- Apply `Integrable.integral_prod_left` to get integrability of the
  -- inner integral.
  have h_int_left := hf_int.integral_prod_left
  -- The inner integral is `∫ θ, r * ‖f‖² ∂(vol.restrict (Ioo (-π) π)) =
  -- circleMeanSq f r * r` for each `r`.
  rw [IntegrableOn]
  refine h_int_left.congr ?_
  refine Filter.Eventually.of_forall (fun r => ?_)
  -- Goal: ∫ θ ∂(vol.restrict (Ioo (-π) π)), r * ‖f(symm(r,θ))‖² = circleMeanSq f r * r
  unfold circleMeanSq
  change (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      = (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2) * r
  rw [integral_const_mul, mul_comm]

theorem bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    bergmanNormSq f
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
  -- Abbreviation for canonical coefficients.
  set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
  -- Step A: rewrite `bergmanNormSq f` via the radial polar form.
  rw [bergmanNormSq_radial_polar hf_polar]
  -- Step B: integrability of `r ↦ circleMeanSq f r * r` on `Ioo 0 1`.
  have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
      (Set.Ioo (0 : ℝ) 1) volume :=
    integrableOn_circleMeanSq_mul_radius hf_polar
  -- Step C: the integrand is nonneg on `Ioo 0 1`.
  have h_radial_nonneg : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ circleMeanSq f r * r := by
    intro r hr
    have hr_pos : 0 < r := hr.1
    have h_cm_nonneg : 0 ≤ circleMeanSq f r := by
      unfold circleMeanSq
      exact integral_nonneg (fun _ => sq_nonneg _)
    exact mul_nonneg h_cm_nonneg (le_of_lt hr_pos)
  -- Step D: per-r identity:
  -- `circleMeanSq f r * r = ∑' k, parsevalRadialTerm a k r` for `r ∈ Ioo 0 1`.
  have h_pointwise_eq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      circleMeanSq f r * r
        = ∑' k : ℕ, parsevalRadialTerm a k r := by
    intro r hr
    exact integrand_eq_tsum hf hR_pos hR_lt hr.1 hr.2
  -- Step E: summability of `fun k => parsevalRadialTerm a k r` for each
  -- `r ∈ Ioo 0 1`.
  have h_summable_r : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      Summable (fun k : ℕ => parsevalRadialTerm a k r) := by
    intro r hr
    -- `parsevalRadialTerm a k r = (2π · r^(2k)) ‖a k‖² * r`. Multiplying
    -- summable by constant preserves summability.
    have h_summ := summable_canonical_parseval_terms hf hR_pos hR_lt hr.1 hr.2
    have h := h_summ.mul_right r
    convert h using 1
    funext k
    unfold parsevalRadialTerm
    rw [show r ^ (2 * k + 1) = r ^ (2 * k) * r from pow_succ r (2 * k)]
    ring
  -- Step F: bound partial sums of `fun k => π/(k+1) ‖a k‖²` by `bergmanNormSq f`.
  -- Use `summable_of_sum_range_le`.
  have h_pi_summand_nonneg : ∀ k : ℕ,
      0 ≤ (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2 := by
    intro k
    have h_pi : 0 ≤ Real.pi := Real.pi_nonneg
    have h_inv : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg h_pi
      positivity
    exact mul_nonneg h_inv (by positivity)
  -- Bound for partial sums: ≤ `∫ r ∈ Ioo 0 1, circleMeanSq f r * r`.
  have h_total_eq : (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r)
      = bergmanNormSq f := (bergmanNormSq_radial_polar hf_polar).symm
  -- Partial sum bound:
  have h_partial_bound : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2)
        ≤ ∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r := by
    intro N
    -- Step F1: ∑ k ∈ range N, π/(k+1) ‖a k‖²
    -- = ∫ r ∈ Ioo 0 1, ∑ k ∈ range N, parsevalRadialTerm a k r
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2
        = ∫ r in Set.Ioo (0 : ℝ) 1,
            ∑ k ∈ Finset.range N, parsevalRadialTerm a k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => parsevalRadialTerm_integrable a k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (parsevalRadialTerm_integral a k).symm
    rw [h_finite_sum_eq]
    -- Step F2: pointwise on `Ioo 0 1`,
    -- ∑ k ∈ range N, parsevalRadialTerm a k r ≤ ∑' k, parsevalRadialTerm a k r
    --                                           = circleMeanSq f r * r
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · -- Integrability of the partial sum.
      exact integrable_finset_sum _
        (fun k _ => parsevalRadialTerm_integrable a k)
    · -- Pointwise inequality.
      have h_summ_r := h_summable_r r hr
      have h_partial_le : (∑ k ∈ Finset.range N, parsevalRadialTerm a k r)
          ≤ ∑' k, parsevalRadialTerm a k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => parsevalRadialTerm_nonneg a k (le_of_lt hr.1))
          h_summ_r
      rw [h_pointwise_eq r hr]
      exact h_partial_le
  -- Step G: deduce summability of `fun k => π/(k+1) ‖a k‖²`.
  have h_summable_final : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2) := by
    refine summable_of_sum_range_le (c := bergmanNormSq f) h_pi_summand_nonneg ?_
    intro N
    exact (h_partial_bound N).trans (le_of_eq h_total_eq)
  -- Step H: apply `integral_tsum_of_summable_integral_norm`.
  -- The hypothesis is `Summable fun k => ∫ r, ‖parsevalRadialTerm a k r‖`.
  -- For nonneg integrand on `Ioo 0 1`, this is summability of
  -- `fun k => π/(k+1) ‖a k‖²`.
  have h_summable_norm_int : Summable (fun k : ℕ =>
      ∫ r in Set.Ioo (0 : ℝ) 1, ‖parsevalRadialTerm a k r‖) := by
    have h_eq : ∀ k : ℕ,
        (∫ r in Set.Ioo (0 : ℝ) 1, ‖parsevalRadialTerm a k r‖)
          = (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2 := by
      intro k
      rw [show (∫ r in Set.Ioo (0 : ℝ) 1, ‖parsevalRadialTerm a k r‖)
          = ∫ r in Set.Ioo (0 : ℝ) 1, parsevalRadialTerm a k r from ?_]
      · exact parsevalRadialTerm_integral a k
      refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
      have h_nn := parsevalRadialTerm_nonneg a k (le_of_lt hr.1)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    refine (h_summable_final).congr (fun k => ?_)
    exact (h_eq k).symm
  -- Step I: the swap lemma.
  -- `Integrable (parsevalRadialTerm a k) (vol.restrict (Ioo 0 1))` =
  --   parsevalRadialTerm_integrable.
  have h_integrable_each : ∀ k : ℕ,
      Integrable (parsevalRadialTerm a k) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    fun k => parsevalRadialTerm_integrable a k
  -- Apply `MeasureTheory.integral_tsum_of_summable_integral_norm`.
  have h_swap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
    (F := parsevalRadialTerm a)
    h_integrable_each h_summable_norm_int
  -- `h_swap : ∑' k, ∫ r, parsevalRadialTerm a k r = ∫ r, ∑' k, parsevalRadialTerm a k r`.
  -- The set integral form: `∫ r in Ioo 0 1, ... = ∫ r ∂(vol.restrict (Ioo 0 1)), ...`.
  -- Step J: the RHS equals `∫ r in Ioo 0 1, circleMeanSq f r * r` via `h_pointwise_eq`.
  -- Bring everything together.
  have h_rhs_eq : (∫ r in Set.Ioo (0 : ℝ) 1, ∑' k : ℕ, parsevalRadialTerm a k r)
      = ∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    exact (h_pointwise_eq r hr).symm
  -- Now combine.
  -- LHS is ∑' k, ∫ r, parsevalRadialTerm a k r = ∑' k, π/(k+1) ‖a k‖²
  have h_lhs_eq : (∑' k : ℕ,
      ∫ r in Set.Ioo (0 : ℝ) 1, parsevalRadialTerm a k r)
      = ∑' k : ℕ, (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2 := by
    refine tsum_congr (fun k => ?_)
    exact parsevalRadialTerm_integral a k
  -- Chain: ∫ r in Ioo 0 1, circleMeanSq f r * r
  --       = ∫ r in Ioo 0 1, ∑' k, parsevalRadialTerm a k r   (by h_rhs_eq)
  --       = ∑' k, ∫ r in Ioo 0 1, parsevalRadialTerm a k r   (by h_swap)
  --       = ∑' k, π/(k+1) ‖a k‖²                              (by h_lhs_eq)
  rw [← h_rhs_eq, ← h_swap, h_lhs_eq]

/-- Termwise comparison consumer: domination of the canonical Cauchy
power-series coefficient norms transfers to domination of the Bergman A²
norm.

For two analytic functions `f, g : ℂ → ℂ` on the open unit disk with the
polar integrability hypothesis, if their canonical Cauchy-power-series
coefficient norms are pointwise dominated `‖a k‖ ≤ ‖b k‖`, then
`bergmanNormSq f ≤ bergmanNormSq g`. -/
theorem bergmanNormSq_termwise_mono
    {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    (hg : AnalyticOn ℂ g UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (hg_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    (h_coeff : ∀ k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖
          ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
    bergmanNormSq f ≤ bergmanNormSq g := by
  -- Rewrite both sides via (2).
  rw [bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hf hR_pos hR_lt hf_polar]
  rw [bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hg hR_pos hR_lt hg_polar]
  -- Termwise comparison: π/(k+1) ‖a k‖² ≤ π/(k+1) ‖b k‖².
  have h_term_le : ∀ k : ℕ,
      (Real.pi / ((k : ℝ) + 1)) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ (Real.pi / ((k : ℝ) + 1)) * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
    intro k
    have h_pi_div_nonneg : 0 ≤ Real.pi / ((k : ℝ) + 1) := by
      apply div_nonneg Real.pi_nonneg
      positivity
    have h_sq_le : ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h_coeff k) 2
    exact mul_le_mul_of_nonneg_left h_sq_le h_pi_div_nonneg
  -- Apply `tsum_le_tsum`. We need summability of both sides; since each side
  -- equals `bergmanNormSq` (a real), they are summable.
  -- Extract summability from the tsum identity: in `ℝ`, if a tsum equals
  -- a real number from a `HasSum`, it's summable.
  -- Alternative: redo summability via the proof-of-(2) summability fact.
  -- We rerun the summability bound here.
  -- Step: for each function, the per-term sum is summable (proved inside (2)).
  have h_summable_f : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
    -- Re-use the partial-sum bound: π/(k+1) ‖a k‖² ≥ 0 and partial sums
    -- bounded by `bergmanNormSq f`. Same argument as in (2)'s proof.
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
      intro k
      apply mul_nonneg
      · apply div_nonneg Real.pi_nonneg
        positivity
      · positivity
    -- Use the Bergman Parseval identity to extract summability via
    -- `Summable.of_nonneg_of_le` against the constant `bergmanNormSq f`.
    -- More direct: the tsum identity itself.
    have h_id := bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hf_polar
    -- We need summability. From the tsum identity `bergmanNormSq f = ∑' k, ...`,
    -- and each term ≥ 0, summability follows because the partial sums are
    -- bounded above by `bergmanNormSq f` (the tsum could equal 0 for
    -- non-summable but here the partial sums are ≤ tsum if summable... circular).
    -- The cleanest path: extract summability by replicating the partial-sum
    -- bound from (2)'s proof. Mirror the structure.
    refine summable_of_sum_range_le (c := bergmanNormSq f) h_nn ?_
    intro N
    -- Bound: ∑ k ∈ range N, π/(k+1) ‖a k‖² ≤ bergmanNormSq f.
    -- Use the same argument as in (2)'s proof body.
    -- We use the radial polar form and the per-r bound by `circleMeanSq`.
    have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
        (Set.Ioo (0 : ℝ) 1) volume :=
      integrableOn_circleMeanSq_mul_radius hf_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioo (0 : ℝ) 1,
            ∑ k ∈ Finset.range N,
              parsevalRadialTerm
                (fun k => (cauchyPowerSeries f 0 R).coeff k) k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => parsevalRadialTerm_integrable _ k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (parsevalRadialTerm_integral _ k).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r)
        = bergmanNormSq f := (bergmanNormSq_radial_polar hf_polar).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => parsevalRadialTerm_integrable _ k)
    · have h_summ_r : Summable (fun k : ℕ =>
          parsevalRadialTerm
            (fun k => (cauchyPowerSeries f 0 R).coeff k) k r) := by
        have h_summ := summable_canonical_parseval_terms hf hR_pos hR_lt hr.1 hr.2
        have h := h_summ.mul_right r
        convert h using 1
        funext k
        unfold parsevalRadialTerm
        rw [show r ^ (2 * k + 1) = r ^ (2 * k) * r from pow_succ r (2 * k)]
        ring
      have h_partial_le : (∑ k ∈ Finset.range N,
          parsevalRadialTerm
            (fun k => (cauchyPowerSeries f 0 R).coeff k) k r)
          ≤ ∑' k, parsevalRadialTerm
            (fun k => (cauchyPowerSeries f 0 R).coeff k) k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => parsevalRadialTerm_nonneg _ k (le_of_lt hr.1))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum hf hR_pos hR_lt hr.1 hr.2
      rw [h_pt_eq]
      exact h_partial_le
  have h_summable_g : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2) := by
    have h_nn : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
      intro k
      apply mul_nonneg
      · apply div_nonneg Real.pi_nonneg
        positivity
      · positivity
    refine summable_of_sum_range_le (c := bergmanNormSq g) h_nn ?_
    intro N
    have h_radial_int : IntegrableOn (fun r => circleMeanSq g r * r)
        (Set.Ioo (0 : ℝ) 1) volume :=
      integrableOn_circleMeanSq_mul_radius hg_polar
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1))
            * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2
        = ∫ r in Set.Ioo (0 : ℝ) 1,
            ∑ k ∈ Finset.range N,
              parsevalRadialTerm
                (fun k => (cauchyPowerSeries g 0 R).coeff k) k r := by
      rw [integral_finset_sum (Finset.range N)
            (fun k _ => parsevalRadialTerm_integrable _ k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (parsevalRadialTerm_integral _ k).symm
    rw [h_finite_sum_eq]
    have h_total_eq : (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq g r * r)
        = bergmanNormSq g := (bergmanNormSq_radial_polar hg_polar).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · exact integrable_finset_sum _
        (fun k _ => parsevalRadialTerm_integrable _ k)
    · have h_summ_r : Summable (fun k : ℕ =>
          parsevalRadialTerm
            (fun k => (cauchyPowerSeries g 0 R).coeff k) k r) := by
        have h_summ := summable_canonical_parseval_terms hg hR_pos hR_lt hr.1 hr.2
        have h := h_summ.mul_right r
        convert h using 1
        funext k
        unfold parsevalRadialTerm
        rw [show r ^ (2 * k + 1) = r ^ (2 * k) * r from pow_succ r (2 * k)]
        ring
      have h_partial_le : (∑ k ∈ Finset.range N,
          parsevalRadialTerm
            (fun k => (cauchyPowerSeries g 0 R).coeff k) k r)
          ≤ ∑' k, parsevalRadialTerm
            (fun k => (cauchyPowerSeries g 0 R).coeff k) k r :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => parsevalRadialTerm_nonneg _ k (le_of_lt hr.1))
          h_summ_r
      have h_pt_eq := integrand_eq_tsum hg hR_pos hR_lt hr.1 hr.2
      rw [h_pt_eq]
      exact h_partial_le
  exact h_summable_f.tsum_le_tsum h_term_le h_summable_g

end ProofRefinement.Korenblum
