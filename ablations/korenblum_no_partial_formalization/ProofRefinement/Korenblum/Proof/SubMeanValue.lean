import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval
import ProofRefinement.Korenblum.Proof.PolarIntegrability
import ProofRefinement.Korenblum.Proof.CircleExpBridge

/-!
# Sprint 018: Bergman A² sub-mean-value inequality (area Cauchy / point evaluation)

This file pins the area-Cauchy / sub-mean-value inequality at the origin
for the Bergman A² norm:

* `normSq_zero_le_bergmanNormSq_div_pi` — for `f` analytic and A²-integrable
  on `UnitDisk`,
  `π · ‖f(0)‖² ≤ bergmanNormSq f`.

The proof reuses sprint 011's whole-disk Bergman Parseval identity
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`. The Bergman
norm is rewritten as a tsum
`∑' k, (π/(k+1)) * ‖a_k‖²` where `a_k := (cauchyPowerSeries f 0 R).coeff k`.
The `k = 0` summand is `π · ‖f 0‖²` (using `HasFPowerSeriesAt.coeff_zero`).
Since every summand is non-negative and the tsum is summable, a single
`Summable.le_tsum` extraction of the `k = 0` term yields the bound.

This is the missing analytic primitive that bridges *outer-region integral
domination* to *inner-region pointwise* / circle-mean information. See the
sprint contract for context.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-- Per-`r` summability of `(π/(k+1)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²`
on the strength of the polar integrability hypothesis. The argument
re-derives the same bound used inside `bergmanNormSq_termwise_mono` from
sprint 011: the partial sums are bounded above by `bergmanNormSq f` via
`bergmanNormSq_radial_polar` and per-`r` `circleMeanSq` domination, which by
non-negativity gives summability via `summable_of_sum_range_le`. -/
private lemma summable_pi_div_coeff_sq
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
  -- Apply the sprint 011 Bergman Parseval identity.
  have h_id := bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
    hf hR_pos hR_lt hf_polar
  -- The summand is non-negative.
  have h_nonneg : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1))
      * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
    intro k
    apply mul_nonneg
    · apply div_nonneg Real.pi_nonneg
      positivity
    · positivity
  -- The Bergman Parseval identity asserts the tsum equals `bergmanNormSq f`.
  -- We extract summability from this. The cleanest path is via
  -- `summable_iff_cauchySeq_finset` / `Summable.tsum_eq` argument, but
  -- the most direct: a tsum of a non-summable non-negative function is 0,
  -- so if the tsum equals the (non-negative) `bergmanNormSq f`, summability
  -- follows unless `bergmanNormSq f = 0`. To avoid the case split, we
  -- re-derive summability via `summable_of_sum_range_le` with the same
  -- `partial_sum ≤ bergmanNormSq` bound used inside sprint 011's identity
  -- proof.
  --
  -- Use `summable_of_sum_range_le` with bound `bergmanNormSq f`.
  refine summable_of_sum_range_le (c := bergmanNormSq f) h_nonneg ?_
  intro N
  -- We need: ∑ k ∈ range N, π/(k+1) ‖a k‖² ≤ bergmanNormSq f.
  -- Strategy: each partial sum is a tsum partial sum, the full tsum is
  -- nonnegative and equals `bergmanNormSq f`. Use `Finset.sum_le_tsum`
  -- on the (just-proved) summable family — but this is circular.
  --
  -- Alternative: the equality `bergmanNormSq f = ∑' k, ...` plus
  -- nonnegativity of summands tells us the partial sums are bounded by the
  -- tsum **iff the tsum is non-zero summable**. Without summability,
  -- `tsum` returns 0 in Mathlib's convention. So we case-split.
  by_cases h_summ : Summable (fun k : ℕ =>
      (Real.pi / ((k : ℝ) + 1))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2)
  · -- Summable case: partial sums ≤ tsum = bergmanNormSq f.
    have h_partial_le : ∑ k ∈ Finset.range N,
        (Real.pi / ((k : ℝ) + 1))
          * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
          ≤ ∑' k : ℕ, (Real.pi / ((k : ℝ) + 1))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
      Summable.sum_le_tsum (Finset.range N)
        (fun k _ => h_nonneg k) h_summ
    linarith [h_partial_le, h_id.le, h_id.ge]
  · -- Non-summable case: tsum is 0 by Mathlib convention.
    -- But bergmanNormSq f ≥ 0 trivially. Combined with `bergmanNormSq f
    -- = ∑' k, ... = 0`, we get bergmanNormSq f = 0.
    -- Then we need ∑ k ∈ range N, ... ≤ 0. Since each summand is ≥ 0,
    -- the partial sum is also ≥ 0. So we need the partial sum to be 0.
    -- But if each summand is ≥ 0 and the tsum (which by non-summability
    -- is 0) does not bound partial sums (in Mathlib's convention), we
    -- need a different argument.
    --
    -- Actually, we can derive a contradiction: a non-summable series of
    -- non-negative reals is unbounded above (its partial sums diverge),
    -- but `bergmanNormSq f` is finite — and the Bergman Parseval identity
    -- pins the integral form via the same partial-sum bound used in
    -- sprint 011. So we re-use that path.
    --
    -- Concretely, replicate the sprint 011 partial-sum argument here.
    -- (This is what sprint 011's `bergmanNormSq_termwise_mono` does.)
    set a : ℕ → ℂ := fun k => (cauchyPowerSeries f 0 R).coeff k with ha_def
    have h_radial_int : IntegrableOn (fun r => circleMeanSq f r * r)
        (Set.Ioo (0 : ℝ) 1) volume := by
      -- Restate the Bergman radial integrability — derived inside
      -- `bergmanNormSq_radial_polar`'s setup. We re-derive via the
      -- polar integrability and Fubini.
      have hf_int : Integrable
          (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
          ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
        rw [Measure.prod_restrict]
        exact hf_polar
      have h_int_left := hf_int.integral_prod_left
      rw [IntegrableOn]
      refine h_int_left.congr ?_
      refine Filter.Eventually.of_forall (fun r => ?_)
      change (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          = circleMeanSq f r * r
      unfold circleMeanSq
      rw [integral_const_mul, mul_comm]
    -- Replicate the `Summable.sum_le_tsum` step from sprint 011's proof
    -- via the *exact* same partial-sum bound used there. This is the
    -- argument inside sprint 011's `bergmanNormSq_termwise_mono`.
    -- Since we cannot reuse sprint 011's private helpers, we redo it here.
    -- The key is: ∑ k ∈ range N, π/(k+1) ‖a k‖²
    --     = ∫ r ∈ Ioo 0 1, ∑ k ∈ range N, parsevalRadialTerm a k r
    --     ≤ ∫ r ∈ Ioo 0 1, circleMeanSq f r * r  (= bergmanNormSq f).
    --
    -- But `parsevalRadialTerm` is private inside `BergmanParseval.lean`.
    -- We inline the computation: parsevalRadialTerm a k r =
    --   (2π · ‖a k‖²) * r^(2k+1).
    -- ∫ r ∈ Ioo 0 1, parsevalRadialTerm a k r = π/(k+1) * ‖a k‖².
    --
    -- To keep this short, we exploit the fact that each individual
    -- `(2π · ‖a k‖²) * r^(2k)` is bounded by `circleMeanSq f r` (the
    -- Cauchy L² estimate, exposed publicly as
    -- `cauchyPowerSeries_normSq_pow_le_circleMeanSq`). Sum over k from 0
    -- to N-1, multiply by r, integrate r from 0 to 1. This gives the
    -- partial-sum bound directly without reaching into sprint 011's
    -- private helpers.
    --
    -- More concretely:
    --   ∑ k ∈ range N, π/(k+1) ‖a k‖²
    --     = ∫ r ∈ Ioo 0 1, ∑ k ∈ range N, (2π · ‖a k‖²) r^(2k) * r dr
    --     ≤ ∫ r ∈ Ioo 0 1, circleMeanSq f r * r dr   (only when N ≤ 1
    --                                                   in this naive form;
    --                                                   we need a per-k
    --                                                   pointwise bound and
    --                                                   then sum, not sum
    --                                                   then bound).
    --
    -- Fortunately, sprint 010's pointwise tsum identity at `r ∈ (0, 1)`
    -- gives `circleMeanSq f r = ∑' k, (2π · r^(2k)) ‖(cps R').coeff k‖²`
    -- for any helper radius `R'(r)`, hence summable, with non-negative
    -- summands; the partial sum is ≤ the tsum = circleMeanSq f r. So
    -- per-r:
    --   ∑ k ∈ range N, (2π · r^(2k)) ‖a k‖² · r  ≤  circleMeanSq f r * r.
    -- Then integrate.
    --
    -- This is *exactly* the argument used inside sprint 011's identity
    -- proof, but applied per-summand. The `summable_canonical_parseval_terms`
    -- lemma gives summability of the per-r tsum.
    --
    -- For the present sprint, we appeal to the public sprint 017 lemma
    -- `cauchyPowerSeries_normSq_pow_le_circleMeanSq` which gives:
    --   (2π) * ‖a k‖² * r^(2k) ≤ circleMeanSq f r   for all k, r ∈ (0,1).
    -- Sum over k ∈ range N, multiply by r, integrate. The sum of the LHS
    -- over k ∈ range N is bounded by `N * circleMeanSq f r`, which is too
    -- weak.
    --
    -- A tighter route: bound the *partial-sum-of-(2π · r^(2k) ‖a k‖²)* by
    -- the *tsum*, which equals circleMeanSq f r (at any r ∈ (0,1)).
    -- The tsum identity is sprint 010's
    -- `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` at
    -- a per-r helper radius. We replicate the structure inline.
    have h_finite_sum_eq : ∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2
        = ∫ r in Set.Ioo (0 : ℝ) 1,
            ∑ k ∈ Finset.range N,
              (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) := by
      -- Each per-term integral: ∫ r ∈ Ioo 0 1, (2π ‖a k‖²) r^(2k+1) dr
      --                       = (2π ‖a k‖²) * (1/(2k+2))
      --                       = π / (k+1) * ‖a k‖².
      have h_per_term : ∀ k : ℕ,
          (∫ r in Set.Ioo (0 : ℝ) 1,
              (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1))
            = (Real.pi / ((k : ℝ) + 1)) * ‖a k‖ ^ 2 := by
        intro k
        rw [integral_const_mul]
        rw [← integral_Ioc_eq_integral_Ioo]
        rw [show (∫ r in Set.Ioc (0 : ℝ) 1, r ^ (2 * k + 1))
            = ∫ r in (0 : ℝ)..1, r ^ (2 * k + 1) from
              (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm]
        rw [integral_pow]
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
      have h_per_term_int : ∀ k : ℕ,
          IntegrableOn (fun r : ℝ =>
            (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1))
              (Set.Ioo (0 : ℝ) 1) volume := by
        intro k
        have hcont : Continuous fun r : ℝ =>
            (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) :=
          continuous_const.mul (continuous_pow _)
        exact (hcont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self
      rw [integral_finset_sum (Finset.range N) (fun k _ => h_per_term_int k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact (h_per_term k).symm
    rw [h_finite_sum_eq]
    -- Per-r pointwise bound: the partial sum is bounded by `circleMeanSq f r * r`.
    have h_total_eq : (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r)
        = bergmanNormSq f := (bergmanNormSq_radial_polar hf_polar).symm
    rw [← h_total_eq]
    refine setIntegral_mono_on ?_ h_radial_int measurableSet_Ioo (fun r hr => ?_)
    · -- Integrability of the partial sum.
      refine integrable_finset_sum _ (fun k _ => ?_)
      have hcont : Continuous fun r : ℝ =>
          (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1) :=
        continuous_const.mul (continuous_pow _)
      exact (hcont.integrableOn_Ioc).mono_set Set.Ioo_subset_Ioc_self
    · -- Pointwise inequality: ∑ k ∈ range N, (2π · ‖a k‖²) r^(2k+1)
      --                       ≤ circleMeanSq f r * r.
      -- The k-th summand is `(2π · ‖a k‖²) r^(2k) · r`. Sprint 017's
      -- public lemma gives `(2π) · ‖a k‖² · r^(2k) ≤ circleMeanSq f r`.
      -- Summing partial bounds is too weak; we need the sum-vs-tsum
      -- inequality.
      --
      -- Rewrite the partial sum as `r * ∑ k ∈ range N, (2π · ‖a k‖²) r^(2k)`.
      have hr_pos : 0 < r := hr.1
      have hr_lt : r < 1 := hr.2
      have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
      -- Per-r summability of `fun k => (2π · ‖a k‖²) r^(2k)` from sprint 017's
      -- private helper has been re-proved, but here we use a different approach:
      -- use sprint 010's per-r tsum identity at a helper radius `R'(r)`.
      -- That identity gives `circleMeanSq f r = ∑' k, (2π · r^(2k))
      -- ‖(cps R'(r)).coeff k‖²`. Bring partial sums in via
      -- `Finset.sum_le_tsum`.
      --
      -- Cleaner: appeal to sprint 010's per-r identity at *the user's* R via
      -- `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
      -- but that signature requires `r < R`. We'd need to pick the
      -- helper radius `(r+1)/2` and use radius-invariance of coefficient
      -- norms. Replicate the structure.
      set rval : ℝ := (r + 1) / 2 with hrval_def
      have hrval_pos : 0 < rval := by rw [hrval_def]; linarith
      have hrval_lt_one : rval < 1 := by rw [hrval_def]; linarith
      have hr_lt_rval : r < rval := by rw [hrval_def]; linarith
      have hrval_nonneg : 0 ≤ rval := le_of_lt hrval_pos
      set R' : ℝ≥0 := ⟨rval, hrval_nonneg⟩ with hR'_def
      have hR'_pos : (0 : ℝ) < (R' : ℝ) := hrval_pos
      have hR'_lt : (R' : ℝ) < 1 := hrval_lt_one
      have hr_lt_R' : r < (R' : ℝ) := hr_lt_rval
      -- Per-r tsum identity at R':
      have h_circle_eq :
          circleMeanSq f r
            = ∑' k : ℕ,
                (2 * Real.pi * r ^ (2 * k))
                  * ‖(cauchyPowerSeries f 0 R').coeff k‖ ^ 2 :=
        circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
          hf hR'_pos hR'_lt hr_nonneg hr_lt_R'
      -- Bridge from R' coefficients to R coefficients via radius-invariance.
      have h_norm := cauchyPowerSeries_coeff_norm_radius_invariant
        hf hR'_pos hR'_lt hR_pos hR_lt
      have h_circle_eq_R : circleMeanSq f r
          = ∑' k : ℕ,
              (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
        rw [h_circle_eq]
        refine tsum_congr (fun k => ?_)
        rw [show ‖(cauchyPowerSeries f 0 R').coeff k‖
            = ‖(cauchyPowerSeries f 0 R).coeff k‖ from h_norm k]
      -- Per-r summability of `fun k => (2π · r^(2k)) ‖a k‖²` from
      -- sprint 011's private helper, which is re-derivable here.
      -- Actually we can re-prove inline via the same machinery.
      have h_summ_R' : Summable (fun k : ℕ =>
          ‖(cauchyPowerSeries f 0 R').coeff k‖ ^ 2 * r ^ (2 * k)) := by
        -- Replicate `summable_coeff_sq_pow` from CauchyL2Estimate.lean
        -- using the fact that R' is the convergence radius.
        have h_subset' : Metric.closedBall (0 : ℂ) (R' : ℝ) ⊆ UnitDisk := by
          intro z hz
          rw [Metric.mem_closedBall, dist_zero_right] at hz
          change z ∈ Metric.ball (0 : ℂ) 1
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_le_of_lt hz hR'_lt
        have hf_diff' : DifferentiableOn ℂ f
            (Metric.closedBall (0 : ℂ) (R' : ℝ)) :=
          (hf.mono h_subset').differentiableOn
        have h_fps' : HasFPowerSeriesOnBall f
            (cauchyPowerSeries f 0 R') 0 (R' : ℝ≥0∞) :=
          hf_diff'.hasFPowerSeriesOnBall hR'_pos
        have h_radius_ge : (R' : ℝ≥0∞)
            ≤ (cauchyPowerSeries f 0 R').radius := h_fps'.r_le
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
          obtain ⟨N₀, hN⟩ := h_tendsto_zero 1 zero_lt_one
          refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
          have h := hN n hn
          rw [Real.dist_eq, sub_zero] at h
          have h_nn : 0 ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
            apply mul_nonneg
            · exact norm_nonneg _
            · exact pow_nonneg hr_nonneg n
          rw [abs_of_nonneg h_nn] at h
          linarith
        have h_sq_le : ∀ᶠ n in atTop,
            (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2
              ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
          filter_upwards [h_eventually_le_one] with n hn
          have h_nn : 0 ≤ ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n := by
            apply mul_nonneg
            · exact norm_nonneg _
            · exact pow_nonneg hr_nonneg n
          nlinarith
        have h_summable_sq : Summable (fun n : ℕ =>
            (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2) := by
          refine Summable.of_norm_bounded_eventually_nat (g := fun n =>
            ‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) h_summable_lin' ?_
          filter_upwards [h_sq_le] with n hn
          have h_nn : 0 ≤ (‖(cauchyPowerSeries f 0 R').coeff n‖ * r ^ n) ^ 2 := by
            positivity
          rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
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
        convert h_summable_sq using 1
        funext n
        rw [h_sq_eq n]
      -- Transfer to the user's R via radius-invariance.
      have h_summ_R : Summable (fun k : ℕ =>
          ‖a k‖ ^ 2 * r ^ (2 * k)) := by
        convert h_summ_R' using 1
        funext k
        congr 1
        rw [ha_def]
        rw [show ‖(cauchyPowerSeries f 0 R).coeff k‖
            = ‖(cauchyPowerSeries f 0 R').coeff k‖ from (h_norm k).symm]
      -- Multiply by `2π` and reorder summand factors.
      have h_summ_full : Summable (fun k : ℕ =>
          (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2) := by
        have h := h_summ_R.mul_left (2 * Real.pi)
        convert h using 1
        funext k; ring
      -- Per-summand non-negativity.
      have h_term_nn : ∀ k : ℕ, 0 ≤
          (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
        intro k
        have h_pi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
        have h_rpow : 0 ≤ r ^ (2 * k) := pow_nonneg hr_nonneg _
        exact mul_nonneg (mul_nonneg h_pi h_rpow) (by positivity)
      -- Partial sum vs tsum:
      have h_partial_le : ∑ k ∈ Finset.range N,
          (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
            ≤ ∑' k : ℕ,
                (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 :=
        Summable.sum_le_tsum (Finset.range N)
          (fun k _ => h_term_nn k) h_summ_full
      -- Now: the partial sum we need to bound is
      -- ∑ k ∈ range N, (2π · ‖a k‖²) * r^(2k+1)
      --     = ∑ k ∈ range N, (2π · r^(2k)) ‖a k‖² · r
      --     = r * (∑ k ∈ range N, (2π · r^(2k)) ‖a k‖²)
      --     ≤ r * (∑' k, (2π · r^(2k)) ‖a k‖²)
      --     = r * circleMeanSq f r       (via h_circle_eq_R, reversed)
      --     = circleMeanSq f r * r.
      have h_lhs_eq : ∑ k ∈ Finset.range N,
          (2 * Real.pi * ‖a k‖ ^ 2) * r ^ (2 * k + 1)
            = r * ∑ k ∈ Finset.range N,
                (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show r ^ (2 * k + 1) = r ^ (2 * k) * r from pow_succ r (2 * k)]
        ring
      rw [h_lhs_eq]
      have h_step1 :
          r * ∑ k ∈ Finset.range N,
              (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
            ≤ r * ∑' k : ℕ,
                (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left h_partial_le hr_nonneg
      have h_step2 :
          r * ∑' k : ℕ,
              (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
            = circleMeanSq f r * r := by
        rw [← h_circle_eq_R]
        ring
      linarith

/-! ## (1) Sub-mean-value inequality at the origin. -/

/-- **Sub-mean-value inequality at the origin.**

For `f : ℂ → ℂ` analytic on `UnitDisk` with the polar integrability
hypothesis, `π · ‖f(0)‖² ≤ bergmanNormSq f`.

The proof routes through sprint 011's whole-disk Bergman Parseval
identity `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
at the helper radius `R := 1/2`, and extracts the `k = 0` summand
`(π/(0+1)) · ‖a₀‖² = π · ‖f(0)‖²` via `Summable.le_tsum`.

The `a₀ = f 0` identification uses `HasFPowerSeriesAt.coeff_zero` together
with the fact that `(cauchyPowerSeries f 0 R).coeff k := (cauchyPowerSeries
f 0 R) k 1`. -/
theorem normSq_zero_le_bergmanNormSq_div_pi
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    Real.pi * ‖f 0‖ ^ 2 ≤ bergmanNormSq f := by
  -- Choose helper radius R = 1/2.
  set R : ℝ≥0 := ⟨1/2, by norm_num⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := by change (0 : ℝ) < 1/2; norm_num
  have hR_lt : (R : ℝ) < 1 := by change (1/2 : ℝ) < 1; norm_num
  -- Sprint 011's Bergman Parseval identity at R.
  have h_id := bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
    hf hR_pos hR_lt hf_polar
  -- Summability of the per-term Bergman Parseval expansion.
  have h_summ := summable_pi_div_coeff_sq hf hR_pos hR_lt hf_polar
  -- Per-summand non-negativity.
  have h_nonneg : ∀ k : ℕ, 0 ≤ (Real.pi / ((k : ℝ) + 1))
      * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
    intro k
    apply mul_nonneg
    · apply div_nonneg Real.pi_nonneg
      positivity
    · positivity
  -- Identify `(cauchyPowerSeries f 0 R).coeff 0 = f 0`.
  have h_coeff_zero : (cauchyPowerSeries f 0 R).coeff 0 = f 0 := by
    -- Build a HasFPowerSeriesAt at the origin.
    have h_subset : Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ UnitDisk := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      change z ∈ Metric.ball (0 : ℂ) 1
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hz hR_lt
    have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) :=
      (hf.mono h_subset).differentiableOn
    have h_fps : HasFPowerSeriesOnBall f
        (cauchyPowerSeries f 0 R) 0 (R : ℝ≥0∞) :=
      hf_diff.hasFPowerSeriesOnBall hR_pos
    have h_at : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 :=
      h_fps.hasFPowerSeriesAt
    -- `coeff 0 := p 0 1` (constant function 1 : Fin 0 → ℂ).
    -- And `HasFPowerSeriesAt.coeff_zero` gives `p 0 v = f 0` for any `v`.
    change (cauchyPowerSeries f 0 R) 0 (fun _ => (1 : ℂ)) = f 0
    exact h_at.coeff_zero (fun _ => 1)
  -- Apply Summable.le_tsum at index k = 0.
  have h_le_tsum :
      (Real.pi / ((0 : ℕ) + 1 : ℝ))
          * ‖(cauchyPowerSeries f 0 R).coeff 0‖ ^ 2
        ≤ ∑' k : ℕ,
            (Real.pi / ((k : ℝ) + 1))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
    h_summ.le_tsum 0 (fun k _ => h_nonneg k)
  -- Simplify (π/(0+1)) = π and rewrite using h_coeff_zero.
  have h_term0 :
      (Real.pi / ((0 : ℕ) + 1 : ℝ))
          * ‖(cauchyPowerSeries f 0 R).coeff 0‖ ^ 2
        = Real.pi * ‖f 0‖ ^ 2 := by
    rw [h_coeff_zero]
    push_cast
    ring
  rw [h_term0] at h_le_tsum
  rw [← h_id] at h_le_tsum
  exact h_le_tsum

end ProofRefinement.Korenblum
