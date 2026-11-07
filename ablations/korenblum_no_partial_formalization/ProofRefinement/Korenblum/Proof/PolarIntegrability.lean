import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman

/-!
# Polar-pullback integrability bridge from `bergmanNormSq` integrability

This file derives the polar-pullback `IntegrableOn` hypothesis used by every
existing Bergman / radial scaffolding consumer
(`bergmanNormSq_polar`, `bergmanNormSq_radial_polar`,
`outerAnnulus_norm_sq_polar`, `innerDisk_norm_sq_polar`,
`validKorenblum_of_innerCircleMean_dom`,
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
`bergmanNormSq_termwise_mono`) directly from the contract's
`Integrable (fun z => ‖f z‖²) (volume.restrict UnitDisk)` hypothesis.

The route is the `lintegral` form of the polar substitution:
`Complex.lintegral_comp_polarCoord_symm`. Combined with monotonicity of
`lintegral` in the integration domain (`lintegral_mono_set`) and the
unit-disk-indicator vanishing for `r ≥ 1`, this bounds the polar-pullback
`lintegral` over `Ioo 0 1 ×ˢ Ioo (-π) π` by the unit-disk Bergman
`lintegral`, which is finite by `Integrable.hasFiniteIntegral`.

Two consumers are exposed:

* `polar_integrableOn_of_bergmanIntegrable` — the headline bridge for any
  `f` with global `AEStronglyMeasurable` measurability and Bergman A²
  integrability on the unit disk.
* `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` — the analytic-
  `f` specialisation, deriving polar-composition measurability from
  `AnalyticOn ℂ f UnitDisk` via `ContinuousOn.aestronglyMeasurable` on
  the polar rectangle.
-/

open MeasureTheory Set Complex
open scoped ENNReal

noncomputable section

namespace ProofRefinement.Korenblum

/-- The polar rectangle `(0,1) × (-π, π)`, in which `polarCoord.symm`
takes values in the open unit disk. -/
private def polarRect : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi

private theorem polarRect_subset_target :
    polarRect ⊆ Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  intro p hp
  exact ⟨Ioo_subset_Ioi_self hp.1, hp.2⟩

private theorem measurableSet_polarRect : MeasurableSet polarRect :=
  (measurableSet_Ioo).prod measurableSet_Ioo

/-- Continuity of `Complex.polarCoord.symm : ℝ × ℝ → ℂ`. -/
private theorem continuous_polarCoord_symm_complex :
    Continuous Complex.polarCoord.symm := by
  -- `Complex.polarCoord.symm p = p.1 * (cos p.2 + sin p.2 * I)`
  have heq : Complex.polarCoord.symm =
      fun p : ℝ × ℝ =>
        (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  rw [heq]
  fun_prop

/--
**Headline bridge.** For any `f : ℂ → ℂ` that is `Measurable` and whose
squared modulus is integrable on the open unit disk (the contract
hypothesis), the polar-pullback
`(r, θ) ↦ r · ‖f (polarCoord.symm (r,θ))‖²` is `IntegrableOn` the polar
rectangle `Ioo 0 1 ×ˢ Ioo (-π) π` with respect to `volume.prod volume`.

This is the gateway lemma every Bergman / radial scaffolding consumer
takes as an opaque hypothesis.

The proof:

1. `AEStronglyMeasurable` of the polar pullback is composition of
   `Continuous Complex.polarCoord.symm`, `‖·‖²`, and the multiplication
   by `p.1`, applied to the global measurability `hf_meas`.
2. `HasFiniteIntegral` is reduced to a finite `lintegral` via
   `Real.enorm_eq_ofReal` (since the integrand is nonneg on the
   rectangle).
3. The `lintegral` is bounded by:
     `∫⁻ p in polarRect, ENNReal.ofReal (r · ‖f(symm p)‖²)`
       ≤ `∫⁻ p in polarTarget, ENNReal.ofReal r · ENNReal.ofReal ‖f(symm p)‖²`
       (= same value, but with the indicator-of-UnitDisk picking out the
       same set, since for `r ≥ 1` the indicator vanishes)
       = `∫⁻ z, UnitDisk.indicator (ENNReal.ofReal ‖f z‖²) z`
       (via `Complex.lintegral_comp_polarCoord_symm`)
       = `∫⁻ z in UnitDisk, ENNReal.ofReal ‖f z‖²`
       < ∞ (by `Integrable.hasFiniteIntegral` of `hf_int`).
-/
theorem polar_integrableOn_of_bergmanIntegrable
    {f : ℂ → ℂ}
    (hf_meas : Measurable f)
    (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk)) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
  -- Notation.
  set rect : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi with hrect
  set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume with hμ
  have h_rect_meas : MeasurableSet rect := measurableSet_polarRect
  have h_rect_subset : rect ⊆ Complex.polarCoord.target :=
    polarRect_subset_target
  have hUD_meas : MeasurableSet UnitDisk :=
    Metric.isOpen_ball.measurableSet
  -- ----------------------------------------------------------------
  -- Step 1: AEStronglyMeasurable of the polar pullback (on the rect).
  -- ----------------------------------------------------------------
  have h_sym_cont : Continuous Complex.polarCoord.symm :=
    continuous_polarCoord_symm_complex
  have h_meas_polar : Measurable
      (fun p : ℝ × ℝ => f (Complex.polarCoord.symm p)) :=
    hf_meas.comp h_sym_cont.measurable
  have h_meas_intrand : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2) μ := by
    have h_norm_meas : Measurable
        (fun p : ℝ × ℝ => ‖f (Complex.polarCoord.symm p)‖) :=
      h_meas_polar.norm
    have h_norm_sq_meas : Measurable
        (fun p : ℝ × ℝ => ‖f (Complex.polarCoord.symm p)‖ ^ 2) :=
      h_norm_meas.pow_const 2
    have h_meas : Measurable
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2) :=
      measurable_fst.mul h_norm_sq_meas
    exact h_meas.aestronglyMeasurable
  -- ----------------------------------------------------------------
  -- Step 2: nonnegativity of the integrand on the rectangle.
  -- ----------------------------------------------------------------
  have h_nonneg : ∀ p ∈ rect,
      0 ≤ p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by
    intro p hp
    have h1 : 0 ≤ p.1 := le_of_lt hp.1.1
    have h2 : 0 ≤ ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by positivity
    exact mul_nonneg h1 h2
  -- ----------------------------------------------------------------
  -- Step 3: bound the polar lintegral by the unit-disk lintegral.
  -- We apply `Complex.lintegral_comp_polarCoord_symm` with
  -- `g z := UnitDisk.indicator (fun z => ENNReal.ofReal (‖f z‖²)) z`.
  -- ----------------------------------------------------------------
  set g : ℂ → ENNReal := fun z =>
    UnitDisk.indicator (fun w => ENNReal.ofReal (‖f w‖ ^ 2)) z with hg
  -- The polar substitution identity.
  have h_polar_sub :
      (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p))
        = ∫⁻ z, g z :=
    Complex.lintegral_comp_polarCoord_symm g
  -- The RHS is finite.
  have h_rhs_finite : (∫⁻ z, g z) < ∞ := by
    rw [show (∫⁻ z, g z) = ∫⁻ z in UnitDisk, ENNReal.ofReal (‖f z‖ ^ 2)
        from lintegral_indicator hUD_meas _]
    -- Convert the lintegral to a HasFiniteIntegral statement.
    have hfi : HasFiniteIntegral (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) := hf_int.hasFiniteIntegral
    -- `‖‖f z‖²‖ₑ = ENNReal.ofReal ‖f z‖²` by nonneg.
    have h_ae_nn :
        (fun _ : ℂ => (0 : ℝ)) ≤ᵐ[((volume : Measure ℂ).restrict UnitDisk)]
          fun z => ‖f z‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => by positivity
    rwa [hasFiniteIntegral_iff_ofReal h_ae_nn] at hfi
  -- On the rect, the indicator unfolds to the actual norm.
  have h_indicator_on_rect :
      EqOn (fun p : ℝ × ℝ =>
          ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p))
        (fun p => ENNReal.ofReal p.1 *
                    ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2))
        rect := by
    intro p hp
    have hr_pos : 0 < p.1 := hp.1.1
    have hr_lt : p.1 < 1 := hp.1.2
    have h_mem_UD : Complex.polarCoord.symm p ∈ UnitDisk :=
      (polarCoord_symm_mem_unitDisk_iff hr_pos).mpr hr_lt
    change ENNReal.ofReal p.1 *
            UnitDisk.indicator (fun w => ENNReal.ofReal (‖f w‖ ^ 2))
              (Complex.polarCoord.symm p)
        = ENNReal.ofReal p.1 *
            ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2)
    rw [Set.indicator_of_mem h_mem_UD]
  -- Convert `smul` to `*` in the polar substitution identity (they agree
  -- on `ℝ≥0∞` since `ENNReal.ofReal r • x = ENNReal.ofReal r * x`).
  have h_polar_mul :
      (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p))
        = ∫⁻ z, g z := by
    simp only [smul_eq_mul] at h_polar_sub
    exact h_polar_sub
  -- Bound the polar lintegral over the rectangle by the polar lintegral
  -- over the target.
  have h_lint_bound :
      (∫⁻ p in rect,
          ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
        ≤ ∫⁻ z, g z := by
    calc (∫⁻ p in rect,
            ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
        = ∫⁻ p in rect,
            ENNReal.ofReal p.1 *
              ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2) := by
            refine setLIntegral_congr_fun h_rect_meas ?_
            intro p hp
            have h1 : 0 ≤ p.1 := le_of_lt hp.1.1
            exact ENNReal.ofReal_mul h1
      _ = ∫⁻ p in rect,
            ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) := by
            refine setLIntegral_congr_fun h_rect_meas ?_
            intro p hp
            -- On the rectangle the indicator unfolds.
            exact (h_indicator_on_rect hp).symm
      _ ≤ ∫⁻ p in Complex.polarCoord.target,
            ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) :=
            lintegral_mono_set h_rect_subset
      _ = ∫⁻ z, g z := h_polar_mul
  -- ----------------------------------------------------------------
  -- Step 4: package as `IntegrableOn`.
  -- ----------------------------------------------------------------
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable on the restricted measure.
    exact h_meas_intrand.restrict
  · -- HasFiniteIntegral.
    rw [HasFiniteIntegral]
    -- `‖p.1 * ‖f(symm p)‖²‖ₑ ≤ ENNReal.ofReal (p.1 * ‖f(symm p)‖²)` ae on
    -- the rectangle, by nonnegativity, and the latter has finite integral.
    have h_finite_lint :
        (∫⁻ p in rect,
            ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
          < ∞ := lt_of_le_of_lt h_lint_bound h_rhs_finite
    have h_ae_eq :
        (fun p : ℝ × ℝ => ‖p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2‖ₑ)
          =ᵐ[μ.restrict rect] fun p =>
            ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2) := by
      refine (ae_restrict_iff' h_rect_meas).mpr ?_
      refine Filter.Eventually.of_forall fun p hp => ?_
      have h_nn : 0 ≤ p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 :=
        h_nonneg p hp
      exact Real.enorm_eq_ofReal h_nn
    calc (∫⁻ p, ‖p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2‖ₑ
              ∂(μ.restrict rect))
        = ∫⁻ p, ENNReal.ofReal
                  (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
              ∂(μ.restrict rect) := lintegral_congr_ae h_ae_eq
      _ < ∞ := h_finite_lint

/--
**Analytic-`f` specialisation.** For `f` analytic on the open unit disk
and Bergman A² integrable, the polar-pullback integrability follows
without an external measurability hypothesis: analyticity (continuity on
`UnitDisk`) plus continuity of `polarCoord.symm` on the rectangle
discharges the polar-composition measurability.

The proof goes by deriving `AEStronglyMeasurable` on the restricted
measure directly from `ContinuousOn (f ∘ polarCoord.symm)` on the
rectangle, then bounding `HasFiniteIntegral` by the same lintegral chain
as `polar_integrableOn_of_bergmanIntegrable`.
-/
theorem polar_integrableOn_of_analyticOn_of_bergmanIntegrable
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk)) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod volume) := by
  -- Notation.
  set rect : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  have h_rect_meas : MeasurableSet rect := measurableSet_polarRect
  have h_rect_subset : rect ⊆ Complex.polarCoord.target :=
    polarRect_subset_target
  have hUD_meas : MeasurableSet UnitDisk :=
    Metric.isOpen_ball.measurableSet
  -- The polar-composition `f ∘ polarCoord.symm` is continuous on the
  -- rectangle (analyticity gives continuity on `UnitDisk`, and
  -- `polarCoord.symm` maps the rectangle into `UnitDisk`).
  have h_sym_cont : Continuous Complex.polarCoord.symm :=
    continuous_polarCoord_symm_complex
  have h_f_cont_UD : ContinuousOn f UnitDisk := hf.continuousOn
  have h_comp_cont : ContinuousOn
      (fun p : ℝ × ℝ => f (Complex.polarCoord.symm p)) rect := by
    refine h_f_cont_UD.comp h_sym_cont.continuousOn ?_
    intro p hp
    have hr_pos : 0 < p.1 := hp.1.1
    have hr_lt : p.1 < 1 := hp.1.2
    exact (polarCoord_symm_mem_unitDisk_iff hr_pos).mpr hr_lt
  -- AEStronglyMeasurable of the polar composition on the restricted measure.
  have h_meas_polar : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f (Complex.polarCoord.symm p)) (μ.restrict rect) :=
    h_comp_cont.aestronglyMeasurable h_rect_meas
  have h_meas_intrand : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      (μ.restrict rect) := by
    have h_p1 : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1) (μ.restrict rect) :=
      continuous_fst.aestronglyMeasurable
    have h_norm_sq : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (μ.restrict rect) :=
      (h_meas_polar.norm).pow 2
    exact h_p1.mul h_norm_sq
  -- Now bound `HasFiniteIntegral` exactly as in the basic version.
  have h_nonneg : ∀ p ∈ rect,
      0 ≤ p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by
    intro p hp
    have h1 : 0 ≤ p.1 := le_of_lt hp.1.1
    have h2 : 0 ≤ ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by positivity
    exact mul_nonneg h1 h2
  -- Set up the same indicator function and reuse the polar substitution.
  set g : ℂ → ENNReal := fun z =>
    UnitDisk.indicator (fun w => ENNReal.ofReal (‖f w‖ ^ 2)) z with hg
  have h_polar_sub :
      (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • g (Complex.polarCoord.symm p))
        = ∫⁻ z, g z :=
    Complex.lintegral_comp_polarCoord_symm g
  have h_rhs_finite : (∫⁻ z, g z) < ∞ := by
    rw [show (∫⁻ z, g z) = ∫⁻ z in UnitDisk, ENNReal.ofReal (‖f z‖ ^ 2)
        from lintegral_indicator hUD_meas _]
    have hfi : HasFiniteIntegral (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) := hf_int.hasFiniteIntegral
    have h_ae_nn :
        (fun _ : ℂ => (0 : ℝ)) ≤ᵐ[((volume : Measure ℂ).restrict UnitDisk)]
          fun z => ‖f z‖ ^ 2 :=
      Filter.Eventually.of_forall fun _ => by positivity
    rwa [hasFiniteIntegral_iff_ofReal h_ae_nn] at hfi
  have h_indicator_on_rect :
      EqOn (fun p : ℝ × ℝ =>
          ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p))
        (fun p => ENNReal.ofReal p.1 *
                    ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2))
        rect := by
    intro p hp
    have hr_pos : 0 < p.1 := hp.1.1
    have hr_lt : p.1 < 1 := hp.1.2
    have h_mem_UD : Complex.polarCoord.symm p ∈ UnitDisk :=
      (polarCoord_symm_mem_unitDisk_iff hr_pos).mpr hr_lt
    change ENNReal.ofReal p.1 *
            UnitDisk.indicator (fun w => ENNReal.ofReal (‖f w‖ ^ 2))
              (Complex.polarCoord.symm p)
        = ENNReal.ofReal p.1 *
            ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2)
    rw [Set.indicator_of_mem h_mem_UD]
  have h_polar_mul :
      (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p))
        = ∫⁻ z, g z := by
    simp only [smul_eq_mul] at h_polar_sub
    exact h_polar_sub
  have h_lint_bound :
      (∫⁻ p in rect,
          ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
        ≤ ∫⁻ z, g z := by
    calc (∫⁻ p in rect,
            ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
        = ∫⁻ p in rect,
            ENNReal.ofReal p.1 *
              ENNReal.ofReal (‖f (Complex.polarCoord.symm p)‖ ^ 2) := by
            refine setLIntegral_congr_fun h_rect_meas ?_
            intro p hp
            have h1 : 0 ≤ p.1 := le_of_lt hp.1.1
            exact ENNReal.ofReal_mul h1
      _ = ∫⁻ p in rect,
            ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) := by
            refine setLIntegral_congr_fun h_rect_meas ?_
            intro p hp
            exact (h_indicator_on_rect hp).symm
      _ ≤ ∫⁻ p in Complex.polarCoord.target,
            ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p) :=
            lintegral_mono_set h_rect_subset
      _ = ∫⁻ z, g z := h_polar_mul
  refine ⟨h_meas_intrand, ?_⟩
  rw [HasFiniteIntegral]
  have h_finite_lint :
      (∫⁻ p in rect,
          ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2))
        < ∞ := lt_of_le_of_lt h_lint_bound h_rhs_finite
  have h_ae_eq :
      (fun p : ℝ × ℝ => ‖p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2‖ₑ)
        =ᵐ[μ.restrict rect] fun p =>
          ENNReal.ofReal (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2) := by
    refine (ae_restrict_iff' h_rect_meas).mpr ?_
    refine Filter.Eventually.of_forall fun p hp => ?_
    have h_nn : 0 ≤ p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 :=
      h_nonneg p hp
    exact Real.enorm_eq_ofReal h_nn
  calc (∫⁻ p, ‖p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2‖ₑ
            ∂(μ.restrict rect))
      = ∫⁻ p, ENNReal.ofReal
                (p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            ∂(μ.restrict rect) := lintegral_congr_ae h_ae_eq
    _ < ∞ := h_finite_lint

end ProofRefinement.Korenblum
