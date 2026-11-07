import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract

/-!
# Polar-coordinate decomposition of `bergmanNormSq`

This file derives the polar-coordinate decomposition of the Bergman A²
seminorm against Mathlib. It exposes:

* `polarCoord_symm_mem_unitDisk_iff` — the open unit disk membership
  criterion for points produced by `Complex.polarCoord.symm`.
* `polarTarget_inter_unitDisk_eq` — the intersection of the polar target
  with the polar preimage of the unit disk.
* `bergmanNormSq_polar` — the headline lemma: `bergmanNormSq f` rewrites
  as a repeated integral over `r ∈ Ioo 0 1` and `θ ∈ Ioo (-π) π` with the
  `r` Jacobian factor.

The decomposition is the natural bridge from `∫_𝔻 ‖f‖² dA` to
radial-against-circle integrals, which every honest improvement past the
Wang-2025 baseline requires.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

variable {f : ℂ → ℂ}

/-- For `r > 0`, the polar-symm point `r·(cos θ + sin θ·I)` lies in the open
unit disk iff `r < 1`. -/
theorem polarCoord_symm_mem_unitDisk_iff
    {r θ : ℝ} (hr : 0 < r) :
    Complex.polarCoord.symm (r, θ) ∈ UnitDisk ↔ r < 1 := by
  unfold UnitDisk
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm]
  exact (abs_of_pos hr).symm ▸ Iff.rfl

/-- The polar-coordinate decomposition of `bergmanNormSq`.

For any function `f : ℂ → ℂ` for which the polar pullback
`(r, θ) ↦ r · ‖f (polarCoord.symm (r,θ))‖²` is integrable on the polar
rectangle `(0,1) × (-π,π)`, the Bergman A² seminorm rewrites as the
iterated integral

  `∫ r ∈ (0,1), ∫ θ ∈ (-π,π), ‖f (polarCoord.symm (r,θ))‖² · r`.

The proof goes via `Complex.integral_comp_polarCoord_symm` (the polar
substitution) followed by Fubini (`MeasureTheory.setIntegral_prod`).
-/
theorem bergmanNormSq_polar
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    bergmanNormSq f =
      ∫ r in Ioo (0 : ℝ) 1,
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 * r := by
  have hUD_meas : MeasurableSet UnitDisk :=
    (Metric.isOpen_ball).measurableSet
  -- Step 1: rewrite `bergmanNormSq f` as an integral over all of ℂ via the
  -- indicator function.
  have step1 :
      bergmanNormSq f =
        ∫ z, (UnitDisk.indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) := by
    unfold bergmanNormSq
    exact (integral_indicator hUD_meas).symm
  -- Step 2: apply polar substitution. Reverse of
  -- `Complex.integral_comp_polarCoord_symm`.
  have step2 :
      (∫ z, (UnitDisk.indicator (fun z => ‖f z‖ ^ 2)) z
            ∂(volume : Measure ℂ))
        = ∫ p in Complex.polarCoord.target,
            p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm
      (fun z => UnitDisk.indicator (fun z => ‖f z‖ ^ 2) z)).symm
  -- Step 3: shrink the integration domain from `polarCoord.target =
  -- Ioi 0 ×ˢ Ioo (-π) π` to `Ioo 0 1 ×ˢ Ioo (-π) π`. Outside `Ioo 0 1` in
  -- the radial coordinate, `polarCoord.symm (r,θ)` lies on or outside the
  -- unit circle, so the indicator vanishes.
  have hT_meas : MeasurableSet (Complex.polarCoord.target) :=
    Complex.polarCoord.open_target.measurableSet
  have h_subset :
      Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi ⊆
        Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    intro p hp
    exact ⟨Ioo_subset_Ioi_self hp.1, hp.2⟩
  have h_diff_zero :
      ∀ p ∈ Complex.polarCoord.target \
              (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi),
        p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                (Complex.polarCoord.symm p) = 0 := by
    intro p hp
    obtain ⟨hp_target, hp_not⟩ := hp
    rw [Complex.polarCoord_target] at hp_target
    obtain ⟨hr_pos, hθ⟩ := hp_target
    -- Either `r ≥ 1` (then symm p ∉ UnitDisk so indicator = 0) or
    -- `θ ∉ Ioo (-π, π)` (impossible since `hθ : θ ∈ Ioo (-π) π`).
    -- In the second case the contradiction would already have been
    -- prevented by `hp_target`. So we must be in the case `¬ r < 1`.
    by_cases hr1 : p.1 < 1
    · -- Then p ∈ Ioo 0 1 ×ˢ Ioo (-π) π — contradicts `hp_not`.
      exact absurd ⟨⟨hr_pos, hr1⟩, hθ⟩ hp_not
    · push_neg at hr1
      have h_not_mem : Complex.polarCoord.symm p ∉ UnitDisk := by
        unfold UnitDisk
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos hr_pos]
        exact not_lt.mpr hr1
      rw [Set.indicator_of_notMem h_not_mem]
      simp
  have step3 :
      (∫ p in Complex.polarCoord.target,
          p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hT_meas h_subset
      h_diff_zero
  -- Step 4: on `Ioo 0 1 ×ˢ Ioo (-π) π`, the indicator unfolds to
  -- `‖f (polarCoord.symm p)‖ ^ 2` because `polarCoord.symm p ∈ UnitDisk`.
  have step4 :
      (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p))
        = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := by
    apply setIntegral_congr_fun
      ((measurableSet_Ioo).prod measurableSet_Ioo) ?_
    intro p hp
    obtain ⟨hr, _hθ⟩ := hp
    have h_mem : Complex.polarCoord.symm p ∈ UnitDisk :=
      (polarCoord_symm_mem_unitDisk_iff hr.1).mpr hr.2
    change p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                  (Complex.polarCoord.symm p)
        = p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2
    rw [Set.indicator_of_mem h_mem, smul_eq_mul]
  -- Step 5: Fubini.
  have step5 :
      (∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        = ∫ r in Ioo (0 : ℝ) 1,
            ∫ θ in Ioo (-Real.pi) Real.pi,
              (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 :=
    setIntegral_prod _ hf_polar
  -- Step 6: tidy the inner integrand.
  have step6 :
      (∫ r in Ioo (0 : ℝ) 1,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ r in Ioo (0 : ℝ) 1,
            ∫ θ in Ioo (-Real.pi) Real.pi,
              ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 * r := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun r => ?_
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    simp [mul_comm]
  -- Chain the steps.
  calc bergmanNormSq f
      = ∫ z, (UnitDisk.indicator (fun z => ‖f z‖ ^ 2)) z
              ∂(volume : Measure ℂ) := step1
    _ = ∫ p in Complex.polarCoord.target,
            p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step2
    _ = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 • (UnitDisk.indicator (fun z => ‖f z‖ ^ 2))
                    (Complex.polarCoord.symm p) := step3
    _ = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
            p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2 := step4
    _ = ∫ r in Ioo (0 : ℝ) 1,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            (r, θ).1 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 := step5
    _ = ∫ r in Ioo (0 : ℝ) 1,
          ∫ θ in Ioo (-Real.pi) Real.pi,
            ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 * r := step6

end ProofRefinement.Korenblum
