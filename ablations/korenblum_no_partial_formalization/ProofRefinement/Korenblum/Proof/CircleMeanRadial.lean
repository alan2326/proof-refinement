import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct
import ProofRefinement.Korenblum.Proof.CirclePolynomialParseval
import ProofRefinement.Korenblum.Proof.AnalyticParseval

/-!
# Radial monotonicity of `circleMeanSq` for analytic functions

This file is the **canonicalisation + radial-monotonicity** consumer of
`Proof.AnalyticParseval`. It exposes:

* `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` — the
  *canonical-witness* analytic Bergman-Parseval circle-mean identity. Strengthens
  sprint 009's existential
  `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` to fix the witness as
  Mathlib's `cauchyPowerSeries f 0 R` for a chosen NNReal radius `R`,
  with `0 ≤ r < (R : ℝ) < 1`.

* `circleMeanSq_termwise_mono` — the coefficient-level consumer. For two
  analytic `f, g : ℂ → ℂ` on `UnitDisk` and a common power-series radius
  `R : ℝ≥0` with `0 ≤ r < (R : ℝ) < 1`, if the coefficient norms of
  `cauchyPowerSeries f 0 R` are pointwise dominated by those of
  `cauchyPowerSeries g 0 R`, then `circleMeanSq f r ≤ circleMeanSq g r`.

* `circleMeanSq_radial_mono` — the headline radial-monotonicity statement:
  for `f` analytic on `UnitDisk` and `0 ≤ r₁ ≤ r₂ < 1`,
  `circleMeanSq f r₁ ≤ circleMeanSq f r₂`. The proof passes through the
  canonical-witness identity above with the common NNReal radius
  `R := ⟨(r₂ + 1) / 2, _⟩` and termwise comparison
  `(2π · r₁^(2k)) c ≤ (2π · r₂^(2k)) c` via `pow_le_pow_left₀` plus
  `mul_le_mul_of_nonneg_right`.
-/

open MeasureTheory Set Complex Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## (3) Canonical-witness analytic Parseval identity. -/

/-- Canonical-witness analytic Bergman-Parseval circle-mean identity.

For `f : ℂ → ℂ` analytic on `UnitDisk` and a chosen NNReal radius
`R : ℝ≥0` with `0 < (R : ℝ) < 1`, every `r ∈ [0, (R : ℝ))` satisfies
`circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²`.

The witness is Mathlib's `cauchyPowerSeries f 0 R`, a deterministic function
of `f` (and the chosen `R`). This is the strengthening of
`circleMeanSq_eq_tsum_of_analyticOn_unitDisk` that the radial-monotonicity
theorem `circleMeanSq_radial_mono` requires: it lets us apply the identity
at two different radii while reusing the same `cauchyPowerSeries` witness. -/
theorem circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < (R : ℝ)) :
    circleMeanSq f r
      = ∑' k : ℕ,
          (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
  -- Step 1: `closedBall 0 R ⊆ UnitDisk` (using `(R : ℝ) < 1`).
  have h_subset : Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ UnitDisk := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    change z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hR_lt
  -- Step 2: `f` is differentiable on the closed ball of radius `R`.
  have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) := by
    have h_an : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) :=
      hf.mono h_subset
    exact h_an.differentiableOn
  -- Step 3: `HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R`.
  have h_fps : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 (R : ℝ≥0∞) :=
    hf_diff.hasFPowerSeriesOnBall hR_pos
  -- Step 4: convert `r < (R : ℝ)` to `ENNReal.ofReal r < (R : ℝ≥0∞)`.
  have h_radius_lt : ENNReal.ofReal r < (R : ℝ≥0∞) := by
    rw [show ((R : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mpr hr_lt
  -- Step 5: apply the analytic Parseval identity from sprint 009 (1).
  exact circleMeanSq_hasFPowerSeriesOnBall h_fps hr_nonneg h_radius_lt

/-! ## Per-term nonnegativity. -/

/-- Each polynomial-Parseval term is nonnegative on a nonneg radius. -/
private lemma parseval_term_nonneg
    (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    0 ≤ (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2 := by
  have hpi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
  have hrk : 0 ≤ r ^ (2 * k) := by positivity
  have hak : 0 ≤ ‖a k‖ ^ 2 := by positivity
  have h1 : 0 ≤ 2 * Real.pi * r ^ (2 * k) := mul_nonneg hpi hrk
  exact mul_nonneg h1 hak

/-! ## Summability of the Parseval expansion. -/

/-- The polynomial-Parseval `tsum` for an analytic function under the
canonical-witness identity is summable. -/
private lemma summable_parseval_cauchy
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < (R : ℝ)) :
    Summable (fun k : ℕ =>
      (2 * Real.pi * r ^ (2 * k))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) := by
  -- We use the canonical-witness Parseval identity together with the
  -- nonnegativity of each term: a `tsum` of nonnegs converges to its `tsum`
  -- value, so summability follows from `summable_of_sum_range_le` once
  -- we know the partial sums are bounded above by `circleMeanSq f r`.
  -- Use `(hasSum_iff_tendsto_nat_of_nonneg).mpr` and the partial-sum
  -- monotone convergence: it is enough to show the partial sums are
  -- bounded.
  -- Simplest route: the Parseval identity states the `tsum` equals
  -- `circleMeanSq f r`, and since the terms are nonneg, summability follows
  -- from the fact that the tsum exists *and* equals a finite real.
  -- Use `Summable.of_nonneg_of_le` against a known summable bound? Easier:
  -- redo the `HasSum` from sprint 009 directly here.
  -- Reroute: pull out the `HasSum` packaged inside the analytic Parseval
  -- proof via the equality `circleMeanSq f r = tsum`.
  -- We re-derive the `HasSum` by the same argument as sprint 009.
  have h_subset : Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ UnitDisk := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    change z ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hR_lt
  have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) := by
    have h_an : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) (R : ℝ)) :=
      hf.mono h_subset
    exact h_an.differentiableOn
  -- Use the canonical-witness identity to rewrite `circleMeanSq f r` as the
  -- relevant `tsum`.
  have h_eq :=
    circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
      hf hR_pos hR_lt hr_nonneg hr_lt
  -- It suffices to exhibit a `HasSum`. From nonnegativity and the
  -- existence of the `tsum`, we get summability via `tsum_eq_zero` route?
  -- Cleaner: use `summable_of_sum_range_le` with bound `circleMeanSq f r`.
  -- First, convert the equality `circleMeanSq f r = ∑' …` into a
  -- HasSum statement: this requires summability, which is what we want!
  -- Workaround: the proof of `circleMeanSq_hasFPowerSeriesOnBall` in
  -- AnalyticParseval establishes a `HasSum (...) (circleMeanSq f r)`
  -- internally. We can re-derive that `HasSum` here by the same route.
  -- Step A: Set up the same machinery as in
  -- `circleMeanSq_hasFPowerSeriesOnBall`. We want the tendsto of partial
  -- sums to `circleMeanSq f r`, which together with nonnegativity gives a
  -- HasSum.
  -- Use the tsum result and the nonnegativity of terms to close summability.
  -- Note: `tsum_eq_zero_iff` and friends only work for *known* summability.
  -- Trick: nonneg + finite tsum ⇒ summable. In fact in `ℝ`, if the partial
  -- sums of a nonneg sequence are bounded, the sequence is summable. The
  -- Parseval identity tells us each finite truncation is bounded by the
  -- tsum which equals `circleMeanSq f r`.
  -- Use `summable_of_sum_le_of_nonneg_of_tendsto`-style reasoning. The
  -- cleanest Mathlib lemma is `summable_of_sum_range_le` which requires a
  -- bound on partial sums.
  -- We get the partial-sum bound from
  -- `circleMeanSq_polynomial`-style truncations; see the proof of
  -- `circleMeanSq_hasFPowerSeriesOnBall` for the same construction.
  -- For brevity here, redo the HasSum extraction in line with sprint 009.
  -- Pick `r' : ℝ≥0` with `ENNReal.ofReal r < (r' : ℝ≥0∞) < (R : ℝ≥0∞)`.
  have h_radius_lt : ENNReal.ofReal r < (R : ℝ≥0∞) := by
    rw [show ((R : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mpr hr_lt
  have h_fps : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 (R : ℝ≥0∞) :=
    hf_diff.hasFPowerSeriesOnBall hR_pos
  -- The canonical-witness identity says
  --   `circleMeanSq f r = tsum (fun k => …)`,
  -- and the proof internally constructs a `HasSum` with the same value.
  -- We bypass that and use the standard ℝ-summability result for a
  -- monotone bounded partial-sum sequence of nonnegatives. The easiest
  -- path is `summable_of_sum_range_le` with bound `circleMeanSq f r`.
  -- For that we need: ∀ N, ∑ k ∈ range N, … ≤ circleMeanSq f r.
  -- This follows from the polynomial-Parseval equality applied to the
  -- partial sum, plus the monotone-convergence reasoning embedded in
  -- `circleMeanSq_hasFPowerSeriesOnBall`.
  -- Skip ahead: we'll produce summability the easy way by using the fact
  -- that ℝ is a complete normed space and the `HasSum` extracted from
  -- `(hasSum_iff_tendsto_nat_of_nonneg).mpr` of a tendsto from below.
  -- We obtain the tendsto from the proof of
  -- `circleMeanSq_hasFPowerSeriesOnBall`. In fact we know
  --   `circleMeanSq f r = ∑' k, …` (from h_eq),
  -- and we know each term is nonneg (from `parseval_term_nonneg`).
  -- A nonneg `tsum` on `ℕ` is summable iff its value is finite (it is —
  -- `circleMeanSq f r` is a real). The Mathlib lemma for this is
  -- `summable_of_ne_top_of_Tendsto` or, more directly, the fact that the
  -- tsum is in ℝ implies summability in ℝ when the terms are nonneg.
  --
  -- Cleanest: `Summable` for nonneg real sequences is equivalent to the
  -- partial sums being bounded above. Use the `tsum`-equation to extract
  -- the bound.
  -- Reroute via `NNReal`: cast the nonneg ℝ-sequence to ℝ≥0, summability
  -- there is automatic if the tsum is finite, but the conversion is
  -- nontrivial.
  --
  -- Pragmatic route: Use `summable_of_sum_range_le`. We need the partial
  -- sums to be bounded by `circleMeanSq f r`.
  -- The bound argument: by induction on `N`, the partial sum
  -- `∑ k ∈ range N, (2π r^(2k)) ‖a k‖²` equals `circleMeanSq (p.partialSum N) r`
  -- (sprint 008's `circleMeanSq_polynomial`). Bounding it above by
  -- `circleMeanSq f r` requires something like a Bessel-style or
  -- monotone-convergence argument.
  --
  -- Easier: use `Summable` ↔ `HasSum (with the tsum value)` — that's not
  -- a one-liner, but Mathlib has `Summable.of_nonneg_of_le` against a
  -- known summable upper bound, which we don't have.
  --
  -- Final route: directly invoke `summable_of_sum_range_le`, where
  -- the bound is the partial-sum tendsto from the analytic Parseval
  -- proof. We re-derive that tendsto here using the same uniform-
  -- convergence + dominated-convergence machinery used internally in
  -- `circleMeanSq_hasFPowerSeriesOnBall`.
  -- Rather than rebuild that, we take a shortcut: the fact that
  -- `(hasSum_iff_tendsto_nat_of_nonneg).mpr h_tendsto` gives a `HasSum` is
  -- the *internal* end-state of `circleMeanSq_hasFPowerSeriesOnBall`'s
  -- proof. We do not get direct access to that `HasSum`, but we can rederive
  -- it step-by-step *here* — replicating the sprint 009 proof.
  --
  -- To avoid duplicating the entire proof, we use the following shortcut:
  -- we know `circleMeanSq f r = tsum (fun k => …)` (from h_eq) and each
  -- term is nonneg. In ℝ, *every* `tsum` is well-defined (it is `0` if
  -- not summable). Therefore, we cannot directly conclude summability from
  -- the equation alone.
  --
  -- BUT: we can use the partial-sum analytic Parseval applied to
  -- `p.partialSum N` and the fact that
  -- `circleMeanSq (p.partialSum N) r ≤ circleMeanSq f r` is *not* true
  -- in general either!
  --
  -- The correct route: redo the partial-sum tendsto argument here. Below
  -- we reproduce just enough of sprint 009's body to extract the
  -- `HasSum (fun k => …) (circleMeanSq f r)`, which immediately gives
  -- `Summable`.
  --
  -- This means re-running steps A–K of sprint 009's proof. We do that.
  --
  -- Pick `r' : ℝ≥0` with `ENNReal.ofReal r < r' < R` in `ℝ≥0∞`.
  obtain ⟨r', hr_lt_r', hr'_lt_R⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp h_radius_lt
  have hr_lt_r'_real : r < (r' : ℝ) := by
    have h := hr_lt_r'
    rw [show ((r' : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (r' : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mp h
  have h_subset' : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) r' :=
    Metric.closedBall_subset_ball hr_lt_r'_real
  have h_uniform : TendstoUniformlyOn
      (fun N y => (cauchyPowerSeries f 0 R).partialSum N y)
      (fun y => f (0 + y)) atTop (Metric.ball (0 : ℂ) (r' : ℝ≥0)) :=
    h_fps.tendstoUniformlyOn hr'_lt_R
  have h_uniform' : TendstoUniformlyOn
      (fun N y => (cauchyPowerSeries f 0 R).partialSum N y) f atTop
      (Metric.ball (0 : ℂ) (r' : ℝ≥0)) := by
    have h_eq2 : (fun y : ℂ => f (0 + y)) = f := by
      funext y; congr 1; ring
    convert h_uniform using 1
    exact h_eq2.symm
  have hf_cont_on_eball : ContinuousOn f (Metric.eball (0 : ℂ) (R : ℝ≥0∞)) :=
    h_fps.continuousOn
  have h_closed_subset_eball : Metric.closedBall (0 : ℂ) r ⊆
      Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_eball, edist_zero_right]
    have h1 : (‖z‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [show (‖z‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from
        (ofReal_norm_eq_enorm z).symm]
      exact ENNReal.ofReal_le_ofReal hz
    exact lt_of_le_of_lt h1 h_radius_lt
  have hf_cont_on_closed : ContinuousOn f (Metric.closedBall (0 : ℂ) r) :=
    hf_cont_on_eball.mono h_closed_subset_eball
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) r) :=
    isCompact_closedBall (0 : ℂ) r
  obtain ⟨M_f, hM_f⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) r, ‖f z‖ ≤ M := by
    rcases h_compact.bddAbove_image (hf_cont_on_closed.norm) with ⟨M, hM⟩
    refine ⟨M, fun z hz => ?_⟩
    exact hM (Set.mem_image_of_mem _ hz)
  have hM_f_nonneg : 0 ≤ M_f := by
    have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
      simp [Metric.mem_closedBall, hr_nonneg]
    exact le_trans (norm_nonneg _) (hM_f 0 h0_mem)
  -- Helper for membership in `closedBall 0 r` for a polar-symm point.
  have h_polar_mem : ∀ θ : ℝ,
      (Complex.polarCoord.symm (r, θ) : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
    intro θ
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Complex.norm_polarCoord_symm, abs_of_nonneg hr_nonneg]
  have h_eventually_close : ∀ᶠ N in atTop,
      ∀ z ∈ Metric.ball (0 : ℂ) (r' : ℝ≥0),
        dist (f z) ((cauchyPowerSeries f 0 R).partialSum N z) < 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at h_uniform'
    exact h_uniform' 1 zero_lt_one
  have h_eventually_bound : ∀ᶠ N in atTop,
      ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
        ‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2 ≤ (M_f + 1) ^ 2 := by
    filter_upwards [h_eventually_close] with N hN θ _hθ
    have hz_mem : (Complex.polarCoord.symm (r, θ) : ℂ) ∈
        Metric.ball (0 : ℂ) (r' : ℝ≥0) :=
      h_subset' (h_polar_mem θ)
    have h1 := hN _ hz_mem
    rw [dist_eq_norm] at h1
    rw [norm_sub_rev] at h1
    have h2 : ‖(cauchyPowerSeries f 0 R).partialSum N
        (Complex.polarCoord.symm (r, θ))‖ ≤ M_f + 1 := by
      have hsub := norm_sub_norm_le
        ((cauchyPowerSeries f 0 R).partialSum N
          (Complex.polarCoord.symm (r, θ)))
        (f (Complex.polarCoord.symm (r, θ)))
      have h3 : ‖f (Complex.polarCoord.symm (r, θ))‖ ≤ M_f :=
        hM_f _ (h_polar_mem θ)
      linarith [le_of_lt h1, hsub]
    have h_norm_nonneg : 0 ≤ ‖(cauchyPowerSeries f 0 R).partialSum N
        (Complex.polarCoord.symm (r, θ))‖ := norm_nonneg _
    have h_M_plus_one_nonneg : 0 ≤ M_f + 1 := by linarith
    nlinarith [sq_nonneg (M_f + 1 -
      ‖(cauchyPowerSeries f 0 R).partialSum N
        (Complex.polarCoord.symm (r, θ))‖)]
  have h_pointwise :
      ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
        Tendsto (fun N => ‖(cauchyPowerSeries f 0 R).partialSum N
            (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          atTop (𝓝 (‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    intro θ _hθ
    have hz_mem : (Complex.polarCoord.symm (r, θ) : ℂ) ∈
        Metric.ball (0 : ℂ) (r' : ℝ≥0) :=
      h_subset' (h_polar_mem θ)
    have h_pt :
        Tendsto (fun N => (cauchyPowerSeries f 0 R).partialSum N
            (Complex.polarCoord.symm (r, θ)))
          atTop (𝓝 (f (Complex.polarCoord.symm (r, θ)))) := by
      have := (Metric.tendstoUniformlyOn_iff.mp h_uniform')
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [this ε hε] with N hN
      have h := hN _ hz_mem
      rw [dist_comm]
      exact h
    exact (continuous_norm.tendsto _).comp h_pt |>.pow 2
  have h_meas_set : MeasurableSet (Set.Ioo (-Real.pi) Real.pi) := measurableSet_Ioo
  have h_bound_integrable :
      Integrable (fun _ : ℝ => (M_f + 1) ^ 2)
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    integrable_const _
  have h_meas_partial : ∀ N,
      AEStronglyMeasurable
        (fun θ : ℝ =>
          ‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    intro N
    have h_cont : Continuous fun θ : ℝ =>
        ‖(cauchyPowerSeries f 0 R).partialSum N
            (Complex.polarCoord.symm (r, θ))‖ ^ 2 := by
      refine Continuous.pow ?_ 2
      refine continuous_norm.comp ?_
      refine ((cauchyPowerSeries f 0 R).partialSum_continuous N).comp ?_
      refine Continuous.congr (f := fun θ : ℝ =>
          (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ?_ ?_
      · exact continuous_const.mul
          (((Complex.continuous_ofReal).mul continuous_const).cexp)
      · intro θ
        exact (polarCoord_symm_eq_exp r θ).symm
    exact h_cont.aestronglyMeasurable
  have h_bound_eventually :
      ∀ᶠ N in atTop,
        ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)),
          ‖‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2‖ ≤
            (M_f + 1) ^ 2 := by
    filter_upwards [h_eventually_bound] with N hN
    refine ae_restrict_of_forall_mem h_meas_set ?_
    intro θ hθ
    have h := hN θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h
  have h_pointwise_ae :
      ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)),
        Tendsto (fun N => ‖(cauchyPowerSeries f 0 R).partialSum N
            (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          atTop (𝓝 (‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    refine ae_restrict_of_forall_mem h_meas_set ?_
    exact h_pointwise
  have h_tendsto_int :
      Tendsto (fun N =>
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        atTop (𝓝 (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => (M_f + 1) ^ 2) ?_ h_bound_eventually
      h_bound_integrable h_pointwise_ae
    filter_upwards with N
    exact h_meas_partial N
  have h_partial_eq : ∀ N,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∑ k ∈ Finset.range N,
            (2 * Real.pi * r ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
    intro N
    have h_eq2 : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖(cauchyPowerSeries f 0 R).partialSum N
              (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ‖∑ k ∈ Finset.range N, (cauchyPowerSeries f 0 R).coeff k *
                (Complex.polarCoord.symm (r, θ) : ℂ) ^ k‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      have h_ps_eq : (cauchyPowerSeries f 0 R).partialSum N
            (Complex.polarCoord.symm (r, θ))
          = ∑ k ∈ Finset.range N, (cauchyPowerSeries f 0 R).coeff k *
              (Complex.polarCoord.symm (r, θ) : ℂ) ^ k := by
        unfold FormalMultilinearSeries.partialSum
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
        rw [smul_eq_mul, mul_comm]
      rw [h_ps_eq]
    rw [h_eq2]
    have h_cm : circleMeanSq
        (fun z => ∑ k ∈ Finset.range N,
          (cauchyPowerSeries f 0 R).coeff k * z ^ k) r
        = ∑ k ∈ Finset.range N,
            (2 * Real.pi * r ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 :=
      circleMeanSq_polynomial (Finset.range N)
        (fun k => (cauchyPowerSeries f 0 R).coeff k) hr_nonneg
    unfold circleMeanSq at h_cm
    exact h_cm
  have h_tendsto :
      Tendsto (fun N => ∑ k ∈ Finset.range N,
          (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2)
        atTop (𝓝 (circleMeanSq f r)) := by
    have h_rewrite : (fun N => ∑ k ∈ Finset.range N,
          (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2)
        = (fun N =>
            ∫ θ in Set.Ioo (-Real.pi) Real.pi,
              ‖(cauchyPowerSeries f 0 R).partialSum N
                  (Complex.polarCoord.symm (r, θ))‖ ^ 2) := by
      funext N
      exact (h_partial_eq N).symm
    rw [h_rewrite]
    unfold circleMeanSq
    exact h_tendsto_int
  have h_nonneg : ∀ k : ℕ, 0 ≤ (2 * Real.pi * r ^ (2 * k))
      * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := fun k =>
    parseval_term_nonneg (fun n => (cauchyPowerSeries f 0 R).coeff n) hr_nonneg k
  have h_hasSum : HasSum (fun k =>
      (2 * Real.pi * r ^ (2 * k))
        * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2) (circleMeanSq f r) :=
    (hasSum_iff_tendsto_nat_of_nonneg h_nonneg _).mpr h_tendsto
  exact h_hasSum.summable

/-! ## (2) Termwise comparison consumer. -/

/-- Termwise comparison consumer: domination of the canonical Cauchy
power-series coefficient norms transfers to domination of `circleMeanSq`. -/
theorem circleMeanSq_termwise_mono
    {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    (hg : AnalyticOn ℂ g UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < (R : ℝ))
    (h_coeff : ∀ k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖
          ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
    circleMeanSq f r ≤ circleMeanSq g r := by
  -- Rewrite both sides via the canonical-witness identity.
  rw [circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hf hR_pos hR_lt hr_nonneg hr_lt]
  rw [circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hg hR_pos hR_lt hr_nonneg hr_lt]
  -- Termwise comparison.
  have h_term_le : ∀ k : ℕ,
      (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
    intro k
    have hpi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
    have hrk : 0 ≤ r ^ (2 * k) := by positivity
    have hconst_nonneg : 0 ≤ 2 * Real.pi * r ^ (2 * k) := mul_nonneg hpi hrk
    have hsq_le : ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖ ^ 2 := by
      have hf_nonneg : 0 ≤ ‖(cauchyPowerSeries f 0 R).coeff k‖ := norm_nonneg _
      exact pow_le_pow_left₀ hf_nonneg (h_coeff k) 2
    exact mul_le_mul_of_nonneg_left hsq_le hconst_nonneg
  -- Apply `Summable.tsum_le_tsum`.
  exact (summable_parseval_cauchy hf hR_pos hR_lt hr_nonneg hr_lt).tsum_le_tsum
    h_term_le (summable_parseval_cauchy hg hR_pos hR_lt hr_nonneg hr_lt)

/-! ## (1) Radial monotonicity of `circleMeanSq`. -/

/-- Radial monotonicity: `r ↦ circleMeanSq f r` is non-decreasing on
`[0, 1)` for any analytic `f` on the open unit disk. -/
theorem circleMeanSq_radial_mono
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₁ r₂ : ℝ} (hr₁_nonneg : 0 ≤ r₁) (hr_le : r₁ ≤ r₂) (hr₂_lt : r₂ < 1) :
    circleMeanSq f r₁ ≤ circleMeanSq f r₂ := by
  -- Pick a common power-series radius `R := ⟨(r₂ + 1) / 2, _⟩` lying strictly
  -- between `r₂` and `1`.
  have hr₂_nonneg : 0 ≤ r₂ := le_trans hr₁_nonneg hr_le
  set Rval : ℝ := (r₂ + 1) / 2 with hRval_def
  have hRval_pos : 0 < Rval := by
    have : 0 < r₂ + 1 := by linarith
    have : 0 < (r₂ + 1) / 2 := by linarith
    exact this
  have hRval_lt_one : Rval < 1 := by
    rw [hRval_def]; linarith
  have hr₂_lt_R : r₂ < Rval := by
    rw [hRval_def]; linarith
  have hr₁_lt_R : r₁ < Rval := lt_of_le_of_lt hr_le hr₂_lt_R
  have hRval_nonneg : 0 ≤ Rval := le_of_lt hRval_pos
  set R : ℝ≥0 := ⟨Rval, hRval_nonneg⟩ with hR_def
  have hR_pos : (0 : ℝ) < (R : ℝ) := hRval_pos
  have hR_lt : (R : ℝ) < 1 := hRval_lt_one
  -- Apply the canonical-witness Parseval identity at both radii.
  rw [circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hf hR_pos hR_lt hr₁_nonneg (show r₁ < (R : ℝ) from hr₁_lt_R)]
  rw [circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        hf hR_pos hR_lt hr₂_nonneg (show r₂ < (R : ℝ) from hr₂_lt_R)]
  -- Termwise comparison: `r₁^(2k) ≤ r₂^(2k)`.
  have h_term_le : ∀ k : ℕ,
      (2 * Real.pi * r₁ ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
        ≤ (2 * Real.pi * r₂ ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
    intro k
    have hpi : 0 ≤ 2 * Real.pi := by linarith [Real.pi_nonneg]
    have hpow_le : r₁ ^ (2 * k) ≤ r₂ ^ (2 * k) :=
      pow_le_pow_left₀ hr₁_nonneg hr_le (2 * k)
    have hconst_le : 2 * Real.pi * r₁ ^ (2 * k)
        ≤ 2 * Real.pi * r₂ ^ (2 * k) :=
      mul_le_mul_of_nonneg_left hpow_le hpi
    have hcoeff_sq_nonneg : 0 ≤ ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 := by
      positivity
    exact mul_le_mul_of_nonneg_right hconst_le hcoeff_sq_nonneg
  -- Apply `Summable.tsum_le_tsum`.
  exact (summable_parseval_cauchy hf hR_pos hR_lt hr₁_nonneg
      (show r₁ < (R : ℝ) from hr₁_lt_R)).tsum_le_tsum
    h_term_le
    (summable_parseval_cauchy hf hR_pos hR_lt hr₂_nonneg
      (show r₂ < (R : ℝ) from hr₂_lt_R))

end ProofRefinement.Korenblum
