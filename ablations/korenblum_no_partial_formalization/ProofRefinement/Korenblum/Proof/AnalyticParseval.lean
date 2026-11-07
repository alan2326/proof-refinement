import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct
import ProofRefinement.Korenblum.Proof.CirclePolynomialParseval

/-!
# Analytic Bergman-Parseval circle-mean identity

This file is the **analytic-level consumer** of `Proof.CirclePolynomialParseval`
(sprint 008). It lifts the polynomial Parseval identity

```
circleMeanSq (fun z => ∑ k ∈ Finset.range N, a k * z ^ k) r
  = ∑ k ∈ Finset.range N, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
```

to the **analytic / power-series** case. We expose:

* `circleMeanSq_hasFPowerSeriesOnBall` — for an analytic `f : ℂ → ℂ`
  represented by a formal power series `p` on `Metric.eball 0 R` and any
  radius `r ∈ [0, R)` (i.e. `0 ≤ r` and `ENNReal.ofReal r < R`):
  `circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖p.coeff k‖²`.

* `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` — for `AnalyticOn ℂ f UnitDisk`
  and any `r ∈ [0, 1)`, there exists `a : ℕ → ℂ` such that
  `circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖a k‖²`.

The proof of (1) applies sprint 008's `circleMeanSq_polynomial` to each
partial sum `p.partialSum N` of `p`, then passes to the limit using:

- `HasFPowerSeriesOnBall.tendstoUniformlyOn` for uniform convergence of
  partial sums on a strict subdisk;
- continuity of `f` on the compact `closedBall 0 r` (via
  `HasFPowerSeriesOnBall.continuousOn`) for a uniform sup-norm bound on `‖f‖`;
- the eventual proximity from uniform convergence to bound the partial-sum
  squared norms by a constant on `closedBall 0 r`;
- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` to
  commute the limit with the `setIntegral` over `Ioo (-π) π` (a finite-volume
  set);
- `hasSum_iff_tendsto_nat_of_nonneg` to convert the resulting `Tendsto` of
  finite partial sums of nonneg reals to a `tsum` identity.

The proof of (2) extracts `HasFPowerSeriesOnBall` data on a closed sub-ball
of the unit disk via Mathlib's `DifferentiableOn.hasFPowerSeriesOnBall`
(which produces the Cauchy power series of `f` at the origin), and reduces
to (1).
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## Tiny helpers. -/

/-- The polar-symm point at radius `r ≥ 0` lies in the closed ball of radius `r`. -/
private lemma polarCoord_symm_mem_closedBall {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Complex.norm_polarCoord_symm, abs_of_nonneg hr]

/-- The partial sum of a complex `FormalMultilinearSeries` at `z` is the
polynomial-form sum `∑ k ∈ Finset.range N, p.coeff k * z ^ k`. -/
private lemma partialSum_eq_finset_sum
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (z : ℂ) :
    p.partialSum N z = ∑ k ∈ Finset.range N, p.coeff k * z ^ k := by
  unfold FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  rw [smul_eq_mul, mul_comm]

/-! ## (1) Analytic Parseval on a power-series ball. -/

/-- Analytic Bergman-Parseval circle-mean identity.

For `f : ℂ → ℂ` represented by a formal power series `p` on the open ball
of (extended) radius `R` around `0`, and for any radius `r ∈ [0, R)`, the
`circleMeanSq` of `f` at radius `r` equals the `tsum` of the polynomial
Parseval terms. -/
theorem circleMeanSq_hasFPowerSeriesOnBall
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 R)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : ENNReal.ofReal r < R) :
    circleMeanSq f r
      = ∑' k : ℕ,
          (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2 := by
  -- Step A: pick `r' : ℝ≥0` with `ENNReal.ofReal r < (r' : ℝ≥0∞) < R`.
  obtain ⟨r', hr_lt_r', hr'_lt_R⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hr_lt
  -- Step B: convert `ENNReal.ofReal r < (r' : ℝ≥0∞)` to `r < (r' : ℝ)`.
  have hr_lt_r'_real : r < (r' : ℝ) := by
    have h := hr_lt_r'
    rw [show ((r' : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (r' : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mp h
  -- Step C: every polar-symm point at radius `r` lies in the metric closed ball
  -- of radius `r`, which is contained in `Metric.ball 0 r'` (as `r < r'`).
  have h_subset : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r' :=
    Metric.closedBall_subset_ball hr_lt_r'_real
  -- Step D: uniform convergence of `p.partialSum N` to `f` on `Metric.ball 0 r'`.
  have h_uniform : TendstoUniformlyOn (fun N y => p.partialSum N y)
      (fun y => f (0 + y)) atTop (Metric.ball (0 : ℂ) (r' : ℝ≥0)) :=
    hf.tendstoUniformlyOn hr'_lt_R
  -- Rewrite `f (0 + y) = f y` for the limit.
  have h_uniform' : TendstoUniformlyOn (fun N y => p.partialSum N y) f atTop
      (Metric.ball (0 : ℂ) (r' : ℝ≥0)) := by
    have h_eq : (fun y : ℂ => f (0 + y)) = f := by
      funext y; congr 1; ring
    rw [← h_eq]; exact h_uniform
  -- Step E: continuity of `f` on `Metric.eball 0 R` ⊇ `closedBall 0 r`.
  have hf_cont_on_eball : ContinuousOn f (Metric.eball (0 : ℂ) R) :=
    hf.continuousOn
  -- Show `closedBall 0 r ⊆ Metric.eball 0 R`.
  have h_closed_subset_eball : Metric.closedBall (0 : ℂ) r ⊆
      Metric.eball (0 : ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_eball, edist_zero_right]
    have h1 : (‖z‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [show (‖z‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from
        (ofReal_norm_eq_enorm z).symm]
      exact ENNReal.ofReal_le_ofReal hz
    exact lt_of_le_of_lt h1 hr_lt
  have hf_cont_on_closed : ContinuousOn f (Metric.closedBall (0 : ℂ) r) :=
    hf_cont_on_eball.mono h_closed_subset_eball
  -- Step F: the closed ball is compact, so `‖f‖` is bounded by some `M_f` on it.
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall (0 : ℂ) r
  obtain ⟨M_f, hM_f⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖f z‖ ≤ M := by
    rcases h_compact.bddAbove_image (hf_cont_on_closed.norm) with ⟨M, hM⟩
    refine ⟨M, fun z hz => ?_⟩
    exact hM (Set.mem_image_of_mem _ hz)
  -- Bound `M_f` by something nonneg.
  have hM_f_nonneg : 0 ≤ M_f := by
    -- The point `0` is in `closedBall 0 r` (since `r ≥ 0`).
    have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
      simp [Metric.mem_closedBall, hr_nonneg]
    exact le_trans (norm_nonneg _) (hM_f 0 h0_mem)
  -- Step G: from uniform convergence on `Metric.ball 0 r'`, eventually
  --   ‖p.partialSum N z - f z‖ < 1 for all z ∈ Metric.ball 0 r' and so
  -- ‖p.partialSum N z‖ ≤ ‖f z‖ + 1 ≤ M_f + 1 for z ∈ closedBall 0 r.
  -- We use `Metric.tendstoUniformlyOn_iff` to extract this eventual bound.
  have h_eventually_close : ∀ᶠ N in atTop,
      ∀ z ∈ Metric.ball (0 : ℂ) (r' : ℝ≥0), dist (f z) (p.partialSum N z) < 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at h_uniform'
    exact h_uniform' 1 zero_lt_one
  -- Convert this to a bound on `closedBall 0 r ⊆ ball 0 r'`.
  have h_eventually_bound : ∀ᶠ N in atTop,
      ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
        ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2 ≤ (M_f + 1) ^ 2 := by
    filter_upwards [h_eventually_close] with N hN θ _hθ
    have hz_mem : (Complex.polarCoord.symm (r, θ) : ℂ) ∈
        Metric.ball (0 : ℂ) (r' : ℝ≥0) :=
      h_subset (polarCoord_symm_mem_closedBall hr_nonneg θ)
    have h1 := hN _ hz_mem
    rw [dist_eq_norm] at h1
    -- h1 : ‖f z - p.partialSum N z‖ < 1.
    -- Note ‖f z - p.partialSum N z‖ = ‖p.partialSum N z - f z‖ by norm_sub_rev.
    rw [norm_sub_rev] at h1
    -- h1 : ‖p.partialSum N z - f z‖ < 1.
    have h2 : ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ≤ M_f + 1 := by
      have hsub := norm_sub_norm_le
        (p.partialSum N (Complex.polarCoord.symm (r, θ)))
        (f (Complex.polarCoord.symm (r, θ)))
      have h3 : ‖f (Complex.polarCoord.symm (r, θ))‖ ≤ M_f :=
        hM_f _ (polarCoord_symm_mem_closedBall hr_nonneg θ)
      linarith [le_of_lt h1, hsub]
    have h_norm_nonneg : 0 ≤ ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ :=
      norm_nonneg _
    have h_M_plus_one_nonneg : 0 ≤ M_f + 1 := by linarith
    nlinarith [sq_nonneg (M_f + 1 -
      ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖)]
  -- Step H: dominated convergence with constant bound `(M_f + 1)^2` on the
  -- finite-volume set `Ioo (-π) π`.
  have h_pointwise :
      ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
        Tendsto (fun N => ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          atTop (𝓝 (‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    intro θ _hθ
    have hz_mem : (Complex.polarCoord.symm (r, θ) : ℂ) ∈
        Metric.ball (0 : ℂ) (r' : ℝ≥0) :=
      h_subset (polarCoord_symm_mem_closedBall hr_nonneg θ)
    have h_pt :
        Tendsto (fun N => p.partialSum N (Complex.polarCoord.symm (r, θ)))
          atTop (𝓝 (f (Complex.polarCoord.symm (r, θ)))) := by
      have := (Metric.tendstoUniformlyOn_iff.mp h_uniform')
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [this ε hε] with N hN
      have h := hN _ hz_mem
      rw [dist_comm]
      exact h
    -- ‖·‖² is continuous, so ‖p_N(z)‖² → ‖f(z)‖².
    exact (continuous_norm.tendsto _).comp h_pt |>.pow 2
  -- Apply tendsto_integral_filter_of_dominated_convergence on the restricted
  -- volume measure on `Ioo (-π) π`.
  have h_meas_set : MeasurableSet (Set.Ioo (-Real.pi) Real.pi) := measurableSet_Ioo
  have h_finite_volume : (volume.restrict (Set.Ioo (-Real.pi) Real.pi))
      Set.univ < ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  -- Bound function: constant `(M_f + 1)^2`.
  have h_bound_integrable :
      Integrable (fun _ : ℝ => (M_f + 1) ^ 2)
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    refine integrable_const _
  -- Measurability of partial sums (each is continuous).
  have h_meas_partial : ∀ N,
      AEStronglyMeasurable
        (fun θ : ℝ =>
          ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    intro N
    have h_cont : Continuous fun θ : ℝ =>
        ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2 := by
      refine Continuous.pow ?_ 2
      refine continuous_norm.comp ?_
      refine (p.partialSum_continuous N).comp ?_
      -- Continuity of `θ ↦ polarCoord.symm (r, θ) : ℂ`.
      refine Continuous.congr (f := fun θ : ℝ =>
          (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ?_ ?_
      · exact continuous_const.mul
          (((Complex.continuous_ofReal).mul continuous_const).cexp)
      · intro θ
        exact (polarCoord_symm_eq_exp r θ).symm
    exact h_cont.aestronglyMeasurable
  -- The bound on the integrand, eventually in N.
  have h_bound_eventually :
      ∀ᶠ N in atTop,
        ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)),
          ‖‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2‖ ≤
            (M_f + 1) ^ 2 := by
    filter_upwards [h_eventually_bound] with N hN
    refine ae_restrict_of_forall_mem h_meas_set ?_
    intro θ hθ
    have h := hN θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h
  -- Pointwise tendsto a.e.
  have h_pointwise_ae :
      ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)),
        Tendsto (fun N => ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          atTop (𝓝 (‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    refine ae_restrict_of_forall_mem h_meas_set ?_
    exact h_pointwise
  -- Apply dominated convergence.
  have h_tendsto_int :
      Tendsto (fun N =>
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        atTop (𝓝 (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => (M_f + 1) ^ 2) ?_ h_bound_eventually
      h_bound_integrable h_pointwise_ae
    filter_upwards with N
    exact h_meas_partial N
  -- Step I: rewrite `‖partial_sum_N‖²` integral via `circleMeanSq` of the
  -- polynomial form, applying sprint 008's `circleMeanSq_polynomial`.
  have h_partial_eq : ∀ N,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∑ k ∈ Finset.range N, (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2 := by
    intro N
    -- Rewrite `partialSum N z = ∑ k ∈ range N, p.coeff k * z ^ k`.
    have h_eq : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ‖∑ k ∈ Finset.range N, p.coeff k *
                (Complex.polarCoord.symm (r, θ) : ℂ) ^ k‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [partialSum_eq_finset_sum]
    rw [h_eq]
    -- Now use `circleMeanSq_polynomial`.
    have h_cm : circleMeanSq (fun z => ∑ k ∈ Finset.range N, p.coeff k * z ^ k) r
        = ∑ k ∈ Finset.range N, (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2 :=
      circleMeanSq_polynomial (Finset.range N) p.coeff hr_nonneg
    -- Unfold `circleMeanSq` to match.
    unfold circleMeanSq at h_cm
    exact h_cm
  -- Step J: combine to get `Tendsto (∑ k ∈ range N, ...) atTop (𝓝 (circleMeanSq f r))`.
  have h_tendsto :
      Tendsto (fun N => ∑ k ∈ Finset.range N,
          (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2)
        atTop (𝓝 (circleMeanSq f r)) := by
    have h_rewrite : (fun N => ∑ k ∈ Finset.range N,
          (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2)
        = (fun N =>
            ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              ‖p.partialSum N (Complex.polarCoord.symm (r, θ))‖ ^ 2) := by
      funext N
      exact (h_partial_eq N).symm
    rw [h_rewrite]
    -- The RHS in h_tendsto_int matches `circleMeanSq f r` after unfolding.
    unfold circleMeanSq
    exact h_tendsto_int
  -- Step K: convert `Tendsto` to `tsum` via `hasSum_iff_tendsto_nat_of_nonneg`.
  have h_nonneg : ∀ k : ℕ,
      0 ≤ (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2 := by
    intro k
    have h_pi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
    have h_r : 0 ≤ r ^ (2 * k) := by positivity
    have h_norm : 0 ≤ ‖p.coeff k‖ ^ 2 := by positivity
    positivity
  have h_hasSum : HasSum (fun k =>
      (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2) (circleMeanSq f r) :=
    (hasSum_iff_tendsto_nat_of_nonneg h_nonneg _).mpr h_tendsto
  exact (h_hasSum.tsum_eq).symm

/-! ## (2) Disk-shape consumer. -/

/-- For any analytic `f` on the open unit disk and any `r ∈ [0, 1)`, the
`circleMeanSq` at `r` is the `tsum` of polynomial-Parseval terms for some
`a : ℕ → ℂ`. -/
theorem circleMeanSq_eq_tsum_of_analyticOn_unitDisk
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < 1) :
    ∃ a : ℕ → ℂ,
      circleMeanSq f r
        = ∑' k : ℕ, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
  -- Pick a radius `r' : ℝ` with `r < r' < 1`.
  set r' : ℝ := (r + 1) / 2 with hr'_def
  have hr_lt_r' : r < r' := by simp [hr'_def]; linarith
  have hr'_lt_one : r' < 1 := by simp [hr'_def]; linarith
  have hr'_nonneg : 0 ≤ r' := by linarith
  -- Cast to NNReal for `DifferentiableOn.hasFPowerSeriesOnBall`.
  set R : ℝ≥0 := ⟨r', hr'_nonneg⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := by
    change 0 < r'
    linarith
  -- `f` is differentiable on the closed ball `closedBall 0 R ⊆ ball 0 1 = UnitDisk`.
  have h_subset : Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ UnitDisk := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    change z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hr'_lt_one
  have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) := by
    have h_an : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) :=
      hf.mono h_subset
    exact h_an.differentiableOn
  -- Apply `DifferentiableOn.hasFPowerSeriesOnBall`. Its hypothesis is
  -- `R : ℝ≥0`, `hR : 0 < R` (real), and gives us a `HasFPowerSeriesOnBall`.
  have hR_pos_nn : (0 : ℝ) < (R : ℝ) := hR_pos
  have h_fps : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 (R : ℝ≥0∞) :=
    hf_diff.hasFPowerSeriesOnBall hR_pos_nn
  -- The radius bound: `ENNReal.ofReal r < (R : ℝ≥0∞)`.
  have h_radius_lt : ENNReal.ofReal r < (R : ℝ≥0∞) := by
    rw [show ((R : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mpr hr_lt_r'
  -- Use (1).
  refine ⟨fun k => (cauchyPowerSeries f 0 R).coeff k, ?_⟩
  exact circleMeanSq_hasFPowerSeriesOnBall h_fps hr_nonneg h_radius_lt

end ProofRefinement.Korenblum
