import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval

/-!
# Hadamard three-circles theorem for `circleMeanSq`

This file is the **log-convexity / Hadamard three-circles** consumer of
sprint 010's canonical-witness Parseval identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`. It exposes
the multiplicative form of Hadamard's three-circles theorem for the A²
circle mean of an analytic function on the unit disk:

```
circleMeanSq f (√(r₁ · r₂))² ≤ circleMeanSq f r₁ · circleMeanSq f r₂
```

(equivalently, `log circleMeanSq f r` is convex in `log r` on `(0, 1)`,
phrased multiplicatively to avoid `-∞` for the zero function).

The proof is a direct **Cauchy–Schwarz on the Parseval `tsum`** of sprint
010's canonical-witness identity. Setting `R := ⟨(max r₁ r₂ + 1)/2, _⟩`
and `a_k := (cauchyPowerSeries f 0 R).coeff k`:

```
circleMeanSq f r = 2π · ∑' k, ‖a_k‖² · r^(2k)
```

Substituting `r = √(r₁ r₂)` so `r^(2k) = r₁^k · r₂^k`, the bound is

```
(2π · ∑' k, ‖a_k‖² · r₁^k · r₂^k)²
   ≤ (2π · ∑' k, ‖a_k‖² · r₁^(2k)) · (2π · ∑' k, ‖a_k‖² · r₂^(2k))
```

via Cauchy–Schwarz on `tsum`s with `u_k := ‖a_k‖ · r₁^k` and
`v_k := ‖a_k‖ · r₂^k`:
`(∑' u_k v_k)² ≤ (∑' u_k²) · (∑' v_k²)`.

Mathlib primitive: `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` with
`Real.HolderConjugate.two_two` to get the `p = q = 2` case
(Cauchy–Schwarz).
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## Per-`r` summability of `‖a_k‖² · r^(2k)`. -/

/-- Per-`r` summability of `‖(cauchyPowerSeries f 0 R).coeff k‖² · r^(2k)`
for `r ∈ [0, 1)`. The argument mirrors `summable_halfRadialTerm_at` from
`Proof.AnnulusBergmanParseval`: from `summable_norm_mul_pow` get linear
summability, then square-bound the eventually-small terms. -/
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

/-! ## Cauchy–Schwarz on the Parseval `tsum`. -/

/-- Cauchy–Schwarz on the Parseval `tsum`: with `u_k := ‖a_k‖ · r₁^k` and
`v_k := ‖a_k‖ · r₂^k`, `(∑' k, u_k * v_k)² ≤ (∑' k, u_k²) * (∑' k, v_k²)`.
This is the `p = q = 2` Hölder inequality on the counting measure, applied
through `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` with
`Real.HolderConjugate.two_two`. -/
private lemma cauchy_schwarz_coeff_radii
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 ≤ r₂) (hr₂' : r₂ < 1) :
    (∑' k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k) ^ 2
      ≤ (∑' k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k))
          * (∑' k : ℕ,
              ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) := by
  -- Set up notation.
  set u : ℕ → ℝ := fun k =>
    ‖(cauchyPowerSeries f 0 R).coeff k‖ * r₁ ^ k with hu_def
  set v : ℕ → ℝ := fun k =>
    ‖(cauchyPowerSeries f 0 R).coeff k‖ * r₂ ^ k with hv_def
  -- Nonnegativity.
  have hu_nonneg : ∀ k, 0 ≤ u k := fun k =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hr₁ k)
  have hv_nonneg : ∀ k, 0 ≤ v k := fun k =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hr₂ k)
  -- Match `u^2` and `v^2` to the Parseval shape.
  have h_u_sq_eq : ∀ k, u k ^ 2 =
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) := by
    intro k
    change (‖(cauchyPowerSeries f 0 R).coeff k‖ * r₁ ^ k) ^ 2 = _
    rw [mul_pow, ← pow_mul, mul_comm k 2]
  have h_v_sq_eq : ∀ k, v k ^ 2 =
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) := by
    intro k
    change (‖(cauchyPowerSeries f 0 R).coeff k‖ * r₂ ^ k) ^ 2 = _
    rw [mul_pow, ← pow_mul, mul_comm k 2]
  -- Match `u * v` to the geometric-mean Parseval shape.
  have h_uv_eq : ∀ k, u k * v k =
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k := by
    intro k
    change (‖(cauchyPowerSeries f 0 R).coeff k‖ * r₁ ^ k)
          * (‖(cauchyPowerSeries f 0 R).coeff k‖ * r₂ ^ k) = _
    rw [mul_pow]
    ring
  -- Summability of `u^2` and `v^2`.
  have h_u_sq_summable : Summable (fun k => u k ^ 2) := by
    have h := summable_coeff_sq_pow hf hR_pos hR_lt hr₁ hr₁'
    convert h using 1
    funext k
    exact h_u_sq_eq k
  have h_v_sq_summable : Summable (fun k => v k ^ 2) := by
    have h := summable_coeff_sq_pow hf hR_pos hR_lt hr₂ hr₂'
    convert h using 1
    funext k
    exact h_v_sq_eq k
  -- Convert `Summable (fun k => u k ^ 2)` to `Summable (fun k => u k ^ (2 : ℝ))`.
  have h_u_rpow_summable : Summable (fun k => u k ^ (2 : ℝ)) := by
    have h_eq : ∀ k : ℕ, u k ^ (2 : ℝ) = u k ^ 2 := fun k => Real.rpow_two _
    have heq_funs : (fun k => u k ^ (2 : ℝ)) = (fun k => u k ^ 2) := by
      funext k; exact h_eq k
    rw [heq_funs]; exact h_u_sq_summable
  have h_v_rpow_summable : Summable (fun k => v k ^ (2 : ℝ)) := by
    have h_eq : ∀ k : ℕ, v k ^ (2 : ℝ) = v k ^ 2 := fun k => Real.rpow_two _
    have heq_funs : (fun k => v k ^ (2 : ℝ)) = (fun k => v k ^ 2) := by
      funext k; exact h_eq k
    rw [heq_funs]; exact h_v_sq_summable
  -- Apply Mathlib's tsum-level Hölder with `p = q = 2`.
  have hpq : Real.HolderConjugate 2 2 := Real.HolderConjugate.two_two
  obtain ⟨_, h_holder⟩ :=
    Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hu_nonneg hv_nonneg
      h_u_rpow_summable h_v_rpow_summable
  -- `h_holder : ∑' u v ≤ (∑' u^(2:ℝ))^(1/2) * (∑' v^(2:ℝ))^(1/2)`.
  -- Convert `^ (2 : ℝ)` to `^ 2` in the tsums.
  have h_u_rpow_eq_sq : (∑' k, u k ^ (2 : ℝ)) = ∑' k, u k ^ 2 := by
    refine tsum_congr (fun k => ?_)
    exact Real.rpow_two _
  have h_v_rpow_eq_sq : (∑' k, v k ^ (2 : ℝ)) = ∑' k, v k ^ 2 := by
    refine tsum_congr (fun k => ?_)
    exact Real.rpow_two _
  rw [h_u_rpow_eq_sq, h_v_rpow_eq_sq] at h_holder
  -- Nonnegativity of the relevant tsums.
  have h_u2_tsum_nonneg : 0 ≤ ∑' k, u k ^ 2 := by
    refine tsum_nonneg ?_
    intro k; positivity
  have h_v2_tsum_nonneg : 0 ≤ ∑' k, v k ^ 2 := by
    refine tsum_nonneg ?_
    intro k; positivity
  have h_uv_tsum_nonneg : 0 ≤ ∑' k, u k * v k := by
    refine tsum_nonneg ?_
    intro k; exact mul_nonneg (hu_nonneg k) (hv_nonneg k)
  -- Square the Hölder inequality (both sides nonneg).
  have h_sq : (∑' k, u k * v k) ^ 2 ≤
      ((∑' k, u k ^ 2) ^ ((1 : ℝ) / 2)
        * (∑' k, v k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
    apply pow_le_pow_left₀ h_uv_tsum_nonneg h_holder
  -- Simplify `((u_sum)^(1/2) * (v_sum)^(1/2))^2 = u_sum * v_sum`.
  have h_simplify_u : ((∑' k, u k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = ∑' k, u k ^ 2 := by
    rw [show (((∑' k, u k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 : ℝ)
      = ((∑' k, u k ^ 2) ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) from by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul h_u2_tsum_nonneg]
    norm_num
  have h_simplify_v : ((∑' k, v k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = ∑' k, v k ^ 2 := by
    rw [show (((∑' k, v k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 : ℝ)
      = ((∑' k, v k ^ 2) ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) from by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul h_v2_tsum_nonneg]
    norm_num
  have h_simplify : ((∑' k, u k ^ 2) ^ ((1 : ℝ) / 2)
        * (∑' k, v k ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = (∑' k, u k ^ 2) * (∑' k, v k ^ 2) := by
    rw [mul_pow, h_simplify_u, h_simplify_v]
  rw [h_simplify] at h_sq
  -- Now rewrite the tsums in the conclusion to match the lemma statement.
  have h_uv_tsum_eq : (∑' k, u k * v k) = ∑' k,
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k := by
    refine tsum_congr (fun k => h_uv_eq k)
  have h_u2_tsum_eq : (∑' k, u k ^ 2) = ∑' k,
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) := by
    refine tsum_congr (fun k => h_u_sq_eq k)
  have h_v2_tsum_eq : (∑' k, v k ^ 2) = ∑' k,
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) := by
    refine tsum_congr (fun k => h_v_sq_eq k)
  rw [h_uv_tsum_eq, h_u2_tsum_eq, h_v2_tsum_eq] at h_sq
  exact h_sq

/-! ## Headline: geometric-mean form of Hadamard three-circles. -/

/-- **Hadamard three-circles theorem (geometric-mean / Cauchy–Schwarz form)
for `circleMeanSq`.**

For `f : ℂ → ℂ` analytic on the unit disk and `r₁, r₂ ∈ (0, 1)`:

```
circleMeanSq f (√(r₁ · r₂)) ^ 2 ≤ circleMeanSq f r₁ · circleMeanSq f r₂
```

Equivalently, `log circleMeanSq f r` is convex in `log r` on `(0, 1)` at the
geometric mean. The proof is Cauchy–Schwarz on the Parseval `tsum`
expansion of `circleMeanSq` provided by sprint 010's
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`. -/
theorem circleMeanSq_geometric_mean_le
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 < r₂) (hr₂' : r₂ < 1) :
    circleMeanSq f (Real.sqrt (r₁ * r₂)) ^ 2
      ≤ circleMeanSq f r₁ * circleMeanSq f r₂ := by
  -- Set up a common power-series radius.
  have hr₁_nn : 0 ≤ r₁ := le_of_lt hr₁
  have hr₂_nn : 0 ≤ r₂ := le_of_lt hr₂
  -- `√(r₁ r₂) ∈ [0, max r₁ r₂]`, so any `Rval > max r₁ r₂` works.
  set Rval : ℝ := (max r₁ r₂ + 1) / 2 with hRval_def
  have hmax_lt_one : max r₁ r₂ < 1 := max_lt hr₁' hr₂'
  have hmax_nonneg : 0 ≤ max r₁ r₂ := le_max_of_le_left hr₁_nn
  have hRval_pos : 0 < Rval := by
    rw [hRval_def]
    have : 0 < max r₁ r₂ + 1 := by linarith
    linarith
  have hRval_lt_one : Rval < 1 := by
    rw [hRval_def]; linarith
  have hr_max_lt_R : max r₁ r₂ < Rval := by
    rw [hRval_def]; linarith
  have hr₁_lt_R : r₁ < Rval := lt_of_le_of_lt (le_max_left _ _) hr_max_lt_R
  have hr₂_lt_R : r₂ < Rval := lt_of_le_of_lt (le_max_right _ _) hr_max_lt_R
  have hRval_nonneg : 0 ≤ Rval := le_of_lt hRval_pos
  set R : ℝ≥0 := ⟨Rval, hRval_nonneg⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := hRval_pos
  have hR_lt : (R : ℝ) < 1 := hRval_lt_one
  -- The geometric-mean radius `√(r₁ r₂) ∈ (0, max r₁ r₂] ⊂ (0, R)`.
  have h_prod_nonneg : 0 ≤ r₁ * r₂ := mul_nonneg hr₁_nn hr₂_nn
  have h_prod_pos : 0 < r₁ * r₂ := mul_pos hr₁ hr₂
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (r₁ * r₂) := Real.sqrt_nonneg _
  -- `√(r₁ r₂) ≤ √((max r₁ r₂)²) = max r₁ r₂` since `r₁ r₂ ≤ (max r₁ r₂)²`.
  have h_prod_le_max_sq : r₁ * r₂ ≤ (max r₁ r₂) ^ 2 := by
    have h₁ : r₁ ≤ max r₁ r₂ := le_max_left _ _
    have h₂ : r₂ ≤ max r₁ r₂ := le_max_right _ _
    have : r₁ * r₂ ≤ (max r₁ r₂) * (max r₁ r₂) :=
      mul_le_mul h₁ h₂ hr₂_nn hmax_nonneg
    rw [sq]; exact this
  have h_sqrt_le_max : Real.sqrt (r₁ * r₂) ≤ max r₁ r₂ := by
    have h := Real.sqrt_le_sqrt h_prod_le_max_sq
    rwa [Real.sqrt_sq hmax_nonneg] at h
  have h_sqrt_lt_R : Real.sqrt (r₁ * r₂) < Rval :=
    lt_of_le_of_lt h_sqrt_le_max hr_max_lt_R
  -- Apply the canonical-witness Parseval identity at the three radii `r₁`,
  -- `r₂`, `√(r₁ r₂)` with the same `R`.
  have h_eq_r₁ :
      circleMeanSq f r₁
        = ∑' k : ℕ,
            (2 * Real.pi * r₁ ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr₁_nn hr₁_lt_R
  have h_eq_r₂ :
      circleMeanSq f r₂
        = ∑' k : ℕ,
            (2 * Real.pi * r₂ ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr₂_nn hr₂_lt_R
  have h_eq_sqrt :
      circleMeanSq f (Real.sqrt (r₁ * r₂))
        = ∑' k : ℕ,
            (2 * Real.pi * (Real.sqrt (r₁ * r₂)) ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt h_sqrt_nonneg h_sqrt_lt_R
  -- Reshape the three tsums.
  -- For the geometric-mean radius: `(√(r₁ r₂))^(2k) = (r₁ r₂)^k`.
  have h_sqrt_pow_2k : ∀ k : ℕ, (Real.sqrt (r₁ * r₂)) ^ (2 * k) = (r₁ * r₂) ^ k := by
    intro k
    rw [pow_mul]
    rw [Real.sq_sqrt h_prod_nonneg]
  -- Pull out the `2π` from each tsum.
  have h_summable_r₁ : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt hr₁_nn hr₁'
  have h_summable_r₂ : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt hr₂_nn hr₂'
  -- Reshape `circleMeanSq f r₁ = (2π) * ∑' k, ‖a_k‖² * r₁^(2k)`.
  have h_circleMeanSq_r₁ :
      circleMeanSq f r₁ = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) := by
    rw [h_eq_r₁]
    rw [← h_summable_r₁.tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  have h_circleMeanSq_r₂ :
      circleMeanSq f r₂ = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) := by
    rw [h_eq_r₂]
    rw [← h_summable_r₂.tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  -- For the geometric-mean radius, use `summable_coeff_sq_pow` at
  -- `r := √(r₁ r₂)`. `r₁ r₂ ∈ [0, 1)` since `r₁, r₂ ∈ (0, 1)`.
  have h_prod_lt_one : r₁ * r₂ < 1 := by
    have : r₁ * r₂ < r₁ * 1 := by
      apply mul_lt_mul_of_pos_left hr₂' hr₁
    linarith
  have h_sqrt_lt_one : Real.sqrt (r₁ * r₂) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt h_prod_nonneg h_prod_lt_one
  have h_summable_sqrt : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        * (Real.sqrt (r₁ * r₂)) ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt h_sqrt_nonneg h_sqrt_lt_one
  -- Convert summability to the `(r₁ * r₂)^k` shape.
  have h_summable_prod : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k) := by
    convert h_summable_sqrt using 1
    funext k
    rw [h_sqrt_pow_2k k]
  have h_circleMeanSq_sqrt :
      circleMeanSq f (Real.sqrt (r₁ * r₂)) = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k := by
    rw [h_eq_sqrt]
    rw [← h_summable_prod.tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    rw [h_sqrt_pow_2k k]
    ring
  -- Now apply Cauchy–Schwarz on the Parseval tsums.
  have h_cs := cauchy_schwarz_coeff_radii hf hR_pos hR_lt hr₁_nn hr₁' hr₂_nn hr₂'
  -- Multiply both sides by `(2π)²` to get the conclusion.
  rw [h_circleMeanSq_sqrt, h_circleMeanSq_r₁, h_circleMeanSq_r₂]
  -- Goal: `((2π) * ∑'_sqrt) ^ 2 ≤ ((2π) * ∑'_r₁) * ((2π) * ∑'_r₂)`
  have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
  have h_lhs_eq : ((2 * Real.pi) * ∑' k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k) ^ 2
      = (2 * Real.pi) ^ 2 * (∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * (r₁ * r₂) ^ k) ^ 2 := by
    rw [mul_pow]
  have h_rhs_eq : ((2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k))
        * ((2 * Real.pi) * ∑' k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k))
      = (2 * Real.pi) ^ 2 *
          ((∑' k : ℕ,
              ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k))
            * (∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k))) := by
    ring
  rw [h_lhs_eq, h_rhs_eq]
  have h_2pi_sq_nonneg : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h_cs h_2pi_sq_nonneg

/-! ## General Hölder / log-convex form. -/

/-- Hölder inequality on the Parseval `tsum`: for any `a ∈ (0, 1)` with
Hölder-conjugate exponents `1/a, 1/(1-a)`,

`∑' k, ‖a_k‖² · r₁^(2ka) · r₂^(2k(1-a))
   ≤ (∑' k, ‖a_k‖² · r₁^(2k))^a · (∑' k, ‖a_k‖² · r₂^(2k))^(1-a)`. -/
private lemma holder_coeff_radii
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 < r₂) (hr₂' : r₂ < 1)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    (∑' k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
          * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k))
      ≤ (∑' k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
        * (∑' k : ℕ,
              ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a) := by
  have hr₁_nn : 0 ≤ r₁ := le_of_lt hr₁
  have hr₂_nn : 0 ≤ r₂ := le_of_lt hr₂
  have ha_nn : 0 ≤ a := le_of_lt ha₀
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_nn : 0 ≤ 1 - a := le_of_lt h1ma_pos
  -- Set up sequences for Hölder.
  -- `u_k = (‖a_k‖² · r₁^(2k))^a`, `v_k = (‖a_k‖² · r₂^(2k))^(1-a)`.
  -- Then with `p = 1/a, q = 1/(1-a)`, `u_k^p = ‖a_k‖² · r₁^(2k)` etc.
  set Akr₁ : ℕ → ℝ := fun k =>
    ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) with hAkr₁_def
  set Akr₂ : ℕ → ℝ := fun k =>
    ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) with hAkr₂_def
  have hAkr₁_nn : ∀ k, 0 ≤ Akr₁ k := by
    intro k; rw [hAkr₁_def]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr₁_nn _)
  have hAkr₂_nn : ∀ k, 0 ≤ Akr₂ k := by
    intro k; rw [hAkr₂_def]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr₂_nn _)
  set u : ℕ → ℝ := fun k => Akr₁ k ^ a with hu_def
  set v : ℕ → ℝ := fun k => Akr₂ k ^ (1 - a) with hv_def
  have hu_nn : ∀ k, 0 ≤ u k := fun k => Real.rpow_nonneg (hAkr₁_nn k) _
  have hv_nn : ∀ k, 0 ≤ v k := fun k => Real.rpow_nonneg (hAkr₂_nn k) _
  -- `Real.HolderConjugate (1/a) (1/(1-a))`.
  have hpq : Real.HolderConjugate (1 / a) (1 / (1 - a)) := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [show (1 / a) = a⁻¹ from one_div a]
      exact (one_lt_inv₀ ha₀).mpr ha₁
    · rw [show (1 / a) = a⁻¹ from one_div a, show (1 / (1 - a)) = (1 - a)⁻¹ from one_div _]
      rw [inv_inv, inv_inv]
      ring
  -- `u k ^ (1/a) = Akr₁ k`, `v k ^ (1/(1-a)) = Akr₂ k`.
  have ha_ne : a ≠ 0 := ne_of_gt ha₀
  have h1ma_ne : 1 - a ≠ 0 := ne_of_gt h1ma_pos
  have hu_rpow_eq : ∀ k, u k ^ (1 / a) = Akr₁ k := by
    intro k
    rw [hu_def]
    rw [← Real.rpow_mul (hAkr₁_nn k)]
    rw [mul_one_div, div_self ha_ne, Real.rpow_one]
  have hv_rpow_eq : ∀ k, v k ^ (1 / (1 - a)) = Akr₂ k := by
    intro k
    rw [hv_def]
    rw [← Real.rpow_mul (hAkr₂_nn k)]
    rw [mul_one_div, div_self h1ma_ne, Real.rpow_one]
  -- Summability of `u^(1/a)` and `v^(1/(1-a))`.
  have h_summable_Akr₁ : Summable Akr₁ := by
    rw [hAkr₁_def]
    exact summable_coeff_sq_pow hf hR_pos hR_lt hr₁_nn hr₁'
  have h_summable_Akr₂ : Summable Akr₂ := by
    rw [hAkr₂_def]
    exact summable_coeff_sq_pow hf hR_pos hR_lt hr₂_nn hr₂'
  have h_summable_u_rpow : Summable (fun k => u k ^ (1 / a)) := by
    have heq : (fun k => u k ^ (1 / a)) = Akr₁ := by
      funext k; exact hu_rpow_eq k
    rw [heq]; exact h_summable_Akr₁
  have h_summable_v_rpow : Summable (fun k => v k ^ (1 / (1 - a))) := by
    have heq : (fun k => v k ^ (1 / (1 - a))) = Akr₂ := by
      funext k; exact hv_rpow_eq k
    rw [heq]; exact h_summable_Akr₂
  -- Apply Mathlib's Hölder.
  obtain ⟨_, h_holder⟩ :=
    Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hu_nn hv_nn
      h_summable_u_rpow h_summable_v_rpow
  -- `h_holder : ∑' u v ≤ (∑' u^(1/a))^(1/(1/a)) * (∑' v^(1/(1-a)))^(1/(1/(1-a)))`.
  -- Simplify `1/(1/a) = a` and `1/(1/(1-a)) = 1 - a`.
  have h_inv_inv_a : 1 / (1 / a) = a := by
    rw [one_div, one_div, inv_inv]
  have h_inv_inv_1ma : 1 / (1 / (1 - a)) = 1 - a := by
    rw [one_div, one_div, inv_inv]
  rw [h_inv_inv_a, h_inv_inv_1ma] at h_holder
  -- Replace tsums of `u^(1/a)` and `v^(1/(1-a))` by tsums of `Akr₁` and `Akr₂`.
  have h_u_rpow_tsum : (∑' k, u k ^ (1 / a)) = ∑' k, Akr₁ k := by
    refine tsum_congr (fun k => hu_rpow_eq k)
  have h_v_rpow_tsum : (∑' k, v k ^ (1 / (1 - a))) = ∑' k, Akr₂ k := by
    refine tsum_congr (fun k => hv_rpow_eq k)
  rw [h_u_rpow_tsum, h_v_rpow_tsum] at h_holder
  -- Reshape `u k * v k` to match the conclusion's LHS:
  -- `u k * v k = (Akr₁ k)^a * (Akr₂ k)^(1-a)
  --   = (‖a_k‖²)^a · r₁^(2ka) · (‖a_k‖²)^(1-a) · r₂^(2k(1-a))
  --   = ‖a_k‖² · (r₁^a r₂^(1-a))^(2k).
  have h_uv_eq : ∀ k, u k * v k =
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k) := by
    intro k
    -- Unfold to: `(‖a_k‖² · r₁^(2k))^a * (‖a_k‖² · r₂^(2k))^(1-a)`.
    change (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
        * (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a)
      = ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
          * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k)
    rw [Real.mul_rpow (sq_nonneg _) (pow_nonneg hr₁_nn _),
        Real.mul_rpow (sq_nonneg _) (pow_nonneg hr₂_nn _)]
    -- Now: (‖a‖²)^a · (r₁^(2k))^a · ((‖a‖²)^(1-a) · (r₂^(2k))^(1-a))
    have h₁ : (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ a
        * (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ (1 - a)
          = ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
      rw [← Real.rpow_add_of_nonneg (sq_nonneg _) ha_nn h1ma_nn]
      simp [Real.rpow_one]
    have h₂ : (r₁ ^ (2 * k)) ^ a = r₁ ^ (((2 * k : ℕ) : ℝ) * a) := by
      rw [show ((r₁ ^ (2 * k)) : ℝ) = r₁ ^ ((2 * k : ℕ) : ℝ) from
        (Real.rpow_natCast r₁ (2 * k)).symm]
      rw [← Real.rpow_mul hr₁_nn]
    have h₃ : (r₂ ^ (2 * k)) ^ (1 - a) = r₂ ^ (((2 * k : ℕ) : ℝ) * (1 - a)) := by
      rw [show ((r₂ ^ (2 * k)) : ℝ) = r₂ ^ ((2 * k : ℕ) : ℝ) from
        (Real.rpow_natCast r₂ (2 * k)).symm]
      rw [← Real.rpow_mul hr₂_nn]
    rw [h₂, h₃]
    -- (r₁^a r₂^(1-a))^(2k) = r₁^(2ka) * r₂^(2k(1-a))
    have h_prod_pow : (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k)
        = r₁ ^ (((2 * k : ℕ) : ℝ) * a) * r₂ ^ (((2 * k : ℕ) : ℝ) * (1 - a)) := by
      rw [mul_pow]
      have e₁ : (r₁ ^ a) ^ (2 * k) = r₁ ^ (((2 * k : ℕ) : ℝ) * a) := by
        rw [show ((r₁ ^ a) ^ (2 * k) : ℝ) = (r₁ ^ a) ^ ((2 * k : ℕ) : ℝ) from
          (Real.rpow_natCast (r₁ ^ a) (2 * k)).symm]
        rw [← Real.rpow_mul hr₁_nn]
        ring_nf
      have e₂ : (r₂ ^ (1 - a)) ^ (2 * k) = r₂ ^ (((2 * k : ℕ) : ℝ) * (1 - a)) := by
        rw [show ((r₂ ^ (1 - a)) ^ (2 * k) : ℝ) = (r₂ ^ (1 - a)) ^ ((2 * k : ℕ) : ℝ) from
          (Real.rpow_natCast (r₂ ^ (1 - a)) (2 * k)).symm]
        rw [← Real.rpow_mul hr₂_nn]
        ring_nf
      rw [e₁, e₂]
    rw [h_prod_pow]
    -- Goal:
    -- (‖a‖²)^a · r₁^(2ka) · ((‖a‖²)^(1-a) · r₂^(2k(1-a)))
    --   = ‖a‖² · (r₁^(2ka) * r₂^(2k(1-a)))
    rw [show (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ a
            * r₁ ^ (((2 * k : ℕ) : ℝ) * a)
          * ((‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ (1 - a)
              * r₂ ^ (((2 * k : ℕ) : ℝ) * (1 - a)))
        = ((‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ a
              * (‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) ^ (1 - a))
          * (r₁ ^ (((2 * k : ℕ) : ℝ) * a)
              * r₂ ^ (((2 * k : ℕ) : ℝ) * (1 - a))) from by ring]
    rw [h₁]
  have h_uv_tsum_eq : (∑' k, u k * v k)
      = ∑' k, ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
          * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k) := by
    refine tsum_congr (fun k => h_uv_eq k)
  rw [h_uv_tsum_eq] at h_holder
  -- Substitute back the definitions of `Akr₁`, `Akr₂` in `h_holder`.
  rw [hAkr₁_def, hAkr₂_def] at h_holder
  exact h_holder

/-- **Hadamard three-circles theorem (general / Hölder / log-convex form)
for `circleMeanSq`.**

For `f : ℂ → ℂ` analytic on the unit disk, `r₁, r₂ ∈ (0, 1)`, and
`a ∈ [0, 1]`:

```
circleMeanSq f (r₁ ^ a * r₂ ^ (1 - a))
  ≤ circleMeanSq f r₁ ^ a * circleMeanSq f r₂ ^ (1 - a)
```

This is the multiplicative form of the convexity of `log circleMeanSq f r`
in `log r` on `(0, 1)`. The proof is Hölder's inequality on the Parseval
`tsum` expansion of `circleMeanSq` provided by sprint 010, with
endpoint cases `a = 0` and `a = 1` handled by direct evaluation. -/
theorem circleMeanSq_log_convex
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 < r₂) (hr₂' : r₂ < 1)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    circleMeanSq f (r₁ ^ a * r₂ ^ (1 - a))
      ≤ circleMeanSq f r₁ ^ a * circleMeanSq f r₂ ^ (1 - a) := by
  -- `circleMeanSq f r ≥ 0` for any `r` (it is an integral of `‖f‖²`).
  have h_cms_nonneg : ∀ r, 0 ≤ circleMeanSq f r := by
    intro r
    unfold circleMeanSq
    refine MeasureTheory.integral_nonneg ?_
    intro θ; positivity
  have hr₁_nn : 0 ≤ r₁ := le_of_lt hr₁
  have hr₂_nn : 0 ≤ r₂ := le_of_lt hr₂
  -- Endpoint cases `a = 0` and `a = 1`.
  rcases eq_or_lt_of_le ha₀ with ha₀_eq | ha₀_lt
  · -- a = 0
    rw [← ha₀_eq]
    rw [Real.rpow_zero, sub_zero, Real.rpow_one, one_mul, Real.rpow_zero, Real.rpow_one]
    simp
  rcases eq_or_lt_of_le ha₁ with ha₁_eq | ha₁_lt
  · -- a = 1
    rw [ha₁_eq]
    rw [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, Real.rpow_one, Real.rpow_zero, mul_one]
  -- Now `0 < a < 1`.
  have h1ma_pos : 0 < 1 - a := by linarith
  have h1ma_nn : 0 ≤ 1 - a := le_of_lt h1ma_pos
  -- Set up a common power-series radius.
  set Rval : ℝ := (max r₁ r₂ + 1) / 2 with hRval_def
  have hmax_lt_one : max r₁ r₂ < 1 := max_lt hr₁' hr₂'
  have hmax_nonneg : 0 ≤ max r₁ r₂ := le_max_of_le_left hr₁_nn
  have hRval_pos : 0 < Rval := by
    rw [hRval_def]
    have : 0 < max r₁ r₂ + 1 := by linarith
    linarith
  have hRval_lt_one : Rval < 1 := by
    rw [hRval_def]; linarith
  have hr_max_lt_R : max r₁ r₂ < Rval := by
    rw [hRval_def]; linarith
  have hr₁_lt_R : r₁ < Rval := lt_of_le_of_lt (le_max_left _ _) hr_max_lt_R
  have hr₂_lt_R : r₂ < Rval := lt_of_le_of_lt (le_max_right _ _) hr_max_lt_R
  have hRval_nonneg : 0 ≤ Rval := le_of_lt hRval_pos
  set R : ℝ≥0 := ⟨Rval, hRval_nonneg⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := hRval_pos
  have hR_lt : (R : ℝ) < 1 := hRval_lt_one
  -- Power-mean radius `r₁^a r₂^(1-a)`.
  have hr₁a_nn : 0 ≤ r₁ ^ a := Real.rpow_nonneg hr₁_nn _
  have hr₂1ma_nn : 0 ≤ r₂ ^ (1 - a) := Real.rpow_nonneg hr₂_nn _
  have hr_pow_nn : 0 ≤ r₁ ^ a * r₂ ^ (1 - a) := mul_nonneg hr₁a_nn hr₂1ma_nn
  -- Show `r₁^a r₂^(1-a) ≤ max r₁ r₂` (so it lies below R).
  -- For r ∈ (0,1) and a ∈ [0,1]: r^a is decreasing in a... no, it's
  -- decreasing for r ∈ (0,1). So r₁^a ≤ r₁^0 = 1 doesn't help directly.
  -- Use a simpler bound: `r₁^a · r₂^(1-a) ≤ max r₁ r₂` by taking max
  -- inside the rpows.
  -- `r₁^a ≤ (max r₁ r₂)^a` and `r₂^(1-a) ≤ (max r₁ r₂)^(1-a)`.
  have h_max_pos : 0 < max r₁ r₂ := lt_max_of_lt_left hr₁
  have hr₁_le_max : r₁ ≤ max r₁ r₂ := le_max_left _ _
  have hr₂_le_max : r₂ ≤ max r₁ r₂ := le_max_right _ _
  have hr₁a_le : r₁ ^ a ≤ (max r₁ r₂) ^ a :=
    Real.rpow_le_rpow hr₁_nn hr₁_le_max ha₀
  have hr₂1ma_le : r₂ ^ (1 - a) ≤ (max r₁ r₂) ^ (1 - a) :=
    Real.rpow_le_rpow hr₂_nn hr₂_le_max h1ma_nn
  have h_pow_max_eq : (max r₁ r₂) ^ a * (max r₁ r₂) ^ (1 - a) = max r₁ r₂ := by
    rw [← Real.rpow_add_of_nonneg hmax_nonneg ha₀ h1ma_nn]
    simp [Real.rpow_one]
  have h_pow_le_max : r₁ ^ a * r₂ ^ (1 - a) ≤ max r₁ r₂ := by
    have := mul_le_mul hr₁a_le hr₂1ma_le hr₂1ma_nn (Real.rpow_nonneg hmax_nonneg _)
    rw [h_pow_max_eq] at this
    exact this
  have h_pow_lt_R : r₁ ^ a * r₂ ^ (1 - a) < Rval :=
    lt_of_le_of_lt h_pow_le_max hr_max_lt_R
  -- Apply the canonical-witness Parseval at the three radii `r₁`, `r₂`,
  -- `r₁^a · r₂^(1-a)`.
  have h_eq_r₁ :
      circleMeanSq f r₁
        = ∑' k : ℕ,
            (2 * Real.pi * r₁ ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr₁_nn hr₁_lt_R
  have h_eq_r₂ :
      circleMeanSq f r₂
        = ∑' k : ℕ,
            (2 * Real.pi * r₂ ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr₂_nn hr₂_lt_R
  have h_eq_pow :
      circleMeanSq f (r₁ ^ a * r₂ ^ (1 - a))
        = ∑' k : ℕ,
            (2 * Real.pi * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr_pow_nn h_pow_lt_R
  -- Reshape: pull out 2π and rewrite to `‖a_k‖² * r^(2k)` shape.
  have h_summable_r₁ : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt hr₁_nn hr₁'
  have h_summable_r₂ : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt hr₂_nn hr₂'
  have h_pow_lt_one : r₁ ^ a * r₂ ^ (1 - a) < 1 := by
    have : r₁ ^ a * r₂ ^ (1 - a) ≤ max r₁ r₂ := h_pow_le_max
    linarith
  have h_summable_pow : Summable (fun k : ℕ =>
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k)) :=
    summable_coeff_sq_pow hf hR_pos hR_lt hr_pow_nn h_pow_lt_one
  have h_circleMeanSq_r₁ :
      circleMeanSq f r₁ = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) := by
    rw [h_eq_r₁]
    rw [← h_summable_r₁.tsum_mul_left]
    refine tsum_congr (fun k => ?_); ring
  have h_circleMeanSq_r₂ :
      circleMeanSq f r₂ = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) := by
    rw [h_eq_r₂]
    rw [← h_summable_r₂.tsum_mul_left]
    refine tsum_congr (fun k => ?_); ring
  have h_circleMeanSq_pow :
      circleMeanSq f (r₁ ^ a * r₂ ^ (1 - a)) = (2 * Real.pi) * ∑' k : ℕ,
          ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
            * (r₁ ^ a * r₂ ^ (1 - a)) ^ (2 * k) := by
    rw [h_eq_pow]
    rw [← h_summable_pow.tsum_mul_left]
    refine tsum_congr (fun k => ?_); ring
  -- Apply the Hölder lemma.
  have h_holder :=
    holder_coeff_radii hf hR_pos hR_lt hr₁ hr₁' hr₂ hr₂' ha₀_lt ha₁_lt
  -- Multiply both sides by 2π. We need: `2π · LHS ≤ (2π)^a · ... · (2π)^(1-a) · ...`
  -- which simplifies because `(2π)^a · (2π)^(1-a) = 2π`.
  rw [h_circleMeanSq_pow, h_circleMeanSq_r₁, h_circleMeanSq_r₂]
  -- Goal: `(2π) * ∑' ... ≤ ((2π) * ∑' r₁ stuff)^a * ((2π) * ∑' r₂ stuff)^(1-a)`
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  have h_2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt h_2pi_pos
  have h_sum_r₁_nn : 0 ≤ ∑' k : ℕ,
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k) := by
    refine tsum_nonneg (fun k => ?_)
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr₁_nn _)
  have h_sum_r₂_nn : 0 ≤ ∑' k : ℕ,
      ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k) := by
    refine tsum_nonneg (fun k => ?_)
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hr₂_nn _)
  -- Split (2π) · S = (2π)^a · (2π)^(1-a) · S^a^(1/a) · S^(1-a)^(1/(1-a)).
  -- Direct calc:
  have h_rhs_split :
      ((2 * Real.pi) * ∑' k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
        * ((2 * Real.pi) * ∑' k : ℕ,
              ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a)
      = (2 * Real.pi)
          * ((∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
            * (∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a)) := by
    rw [Real.mul_rpow h_2pi_nn h_sum_r₁_nn]
    rw [Real.mul_rpow h_2pi_nn h_sum_r₂_nn]
    have h_2pi_split : (2 * Real.pi) ^ a * (2 * Real.pi) ^ (1 - a) = 2 * Real.pi := by
      rw [← Real.rpow_add_of_nonneg h_2pi_nn ha₀ h1ma_nn]
      simp [Real.rpow_one]
    calc
      (2 * Real.pi) ^ a * (∑' k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
          * ((2 * Real.pi) ^ (1 - a) * (∑' k : ℕ,
              ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a))
        = ((2 * Real.pi) ^ a * (2 * Real.pi) ^ (1 - a))
            * ((∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
              * (∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a)) := by ring
      _ = (2 * Real.pi)
            * ((∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₁ ^ (2 * k)) ^ a
              * (∑' k : ℕ,
                ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r₂ ^ (2 * k)) ^ (1 - a)) := by
            rw [h_2pi_split]
  rw [h_rhs_split]
  -- Now goal: `(2π) * LHS_sum ≤ (2π) * RHS_holder`.
  exact mul_le_mul_of_nonneg_left h_holder h_2pi_nn

end ProofRefinement.Korenblum
