import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.PolarIntegrability

/-!
# Radial / circle integrability bridges from the polar-pullback `IntegrableOn`

This file derives the six remaining radial / per-θ integrability handles
needed by `validKorenblum_of_innerCircleMean_dom` (sprint 005) directly
from the polar-pullback `IntegrableOn` hypothesis (the output of
`Proof/PolarIntegrability.lean`, sprint 012). Together with the polar
bridge, this closes the last plumbing gap between the
`ValidKorenblumBound c` contract and the conditional Korenblum reduction.

The six derivations all route through Mathlib's Fubini-Tonelli /
product-measure machinery:

* `Measure.prod_restrict` — converts
  `IntegrableOn ... (s ×ˢ t) (volume.prod volume)` into
  `Integrable ... ((volume.restrict s).prod (volume.restrict t))`.
* `Integrable.integral_prod_left` — projects out the radial marginal,
  giving `IntegrableOn (fun r => ∫ θ in Ioo (-π) π, r * ‖f (symm (r,θ))‖²)
  (Ioo 0 1) volume`. The inner θ-integral evaluates to
  `r * circleMeanSq f r`.
* `IntegrableOn.mono_set` — restricts the radial marginal to `Ioc 0 c`
  and `Ioo c 1` via `Ioc 0 c ⊆ Ioo 0 1` and `Ioo c 1 ⊆ Ioo 0 1`.
* `Integrable.prod_right_ae` — gives the per-radius slice integrability
  in `∀ᵐ` form for the slice `θ ↦ r * ‖f (symm (r,θ))‖²`. For `r > 0` we
  divide through by `r` (using `integrable_fun_smul_iff`) to obtain the
  slice integrability of `θ ↦ ‖f (symm (r,θ))‖²`.

The per-radius circle integrability comes out in `∀ᵐ` form rather than
pointwise `∀ r ∈ Ioo c 1`. The cause is structural: `Integrable.prod_right_ae`
only commits to almost-every-r slice integrability. The clean conditional
Korenblum reduction in `Proof/CleanConditional.lean` consumes this via a
new `_ae`-variant of `validKorenblum_of_innerCircleMean_dom` derived
inline (a separate theorem; the existing pointwise reduction in
`Proof/RadialSplit.lean` stays as-is).
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

variable {f : ℂ → ℂ}

/-! ## Step 1: project out the radial marginal as `Integrable` over `Ioo 0 1`. -/

/-- The radial marginal of the polar-pullback integrability: the function
`r ↦ r * circleMeanSq f r` is integrable on `Ioo 0 1`. The inner θ-integral
of `r * ‖f (symm (r,θ))‖²` over `Ioo (-π) π` equals
`r * circleMeanSq f r`. -/
theorem radial_integrableOn_r_mul_circleMeanSq_Ioo_zero_one
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (fun r => r * circleMeanSq f r)
                 (Set.Ioo (0 : ℝ) 1) volume := by
  -- Convert `IntegrableOn ... (s ×ˢ t)` to `Integrable ... over restricted prod`.
  have h_prod : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hf_polar
  -- Apply `Integrable.integral_prod_left` to project out the radial marginal.
  have h_marginal : Integrable
      (fun r : ℝ => ∫ θ, r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2
                          ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    h_prod.integral_prod_left
  -- Rewrite the inner integral as `r * circleMeanSq f r`.
  have h_eq : (fun r : ℝ => ∫ θ, r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2
                          ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)))
            = fun r : ℝ => r * circleMeanSq f r := by
    funext r
    rw [integral_const_mul]
    rfl
  rw [h_eq] at h_marginal
  exact h_marginal

/-! ## Step 2: shrink the radial marginal to `Ioc 0 c` and `Ioo c 1`. -/

private theorem Ioc_subset_Ioo_zero_one {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Set.Ioc (0 : ℝ) c ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro r hr
  exact ⟨hr.1, lt_of_le_of_lt hr.2 hc1⟩

private theorem Ioo_subset_Ioo_zero_one {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Set.Ioo c 1 ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro r hr
  exact ⟨lt_trans hc hr.1, hr.2⟩

/-- Inner-half radial integrability on `Ioc 0 c`. -/
theorem radial_integrableOn_circleMeanSq_mul_r_Ioc
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntegrableOn (fun r => circleMeanSq f r * r)
                 (Set.Ioc 0 c) volume := by
  have h_full : IntegrableOn (fun r => r * circleMeanSq f r)
                              (Set.Ioo (0 : ℝ) 1) volume :=
    radial_integrableOn_r_mul_circleMeanSq_Ioo_zero_one hf_polar
  have h_shrunk : IntegrableOn (fun r => r * circleMeanSq f r)
                                (Set.Ioc 0 c) volume :=
    h_full.mono_set (Ioc_subset_Ioo_zero_one hc hc1)
  -- Swap the order: `r * circleMeanSq f r = circleMeanSq f r * r`.
  have h_eq : (fun r : ℝ => r * circleMeanSq f r) =
              (fun r : ℝ => circleMeanSq f r * r) := by
    funext r
    exact mul_comm _ _
  rw [h_eq] at h_shrunk
  exact h_shrunk

/-- Outer-half radial integrability on `Ioo c 1`. -/
theorem radial_integrableOn_circleMeanSq_mul_r_Ioo
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IntegrableOn (fun r => circleMeanSq f r * r)
                 (Set.Ioo c 1) volume := by
  have h_full : IntegrableOn (fun r => r * circleMeanSq f r)
                              (Set.Ioo (0 : ℝ) 1) volume :=
    radial_integrableOn_r_mul_circleMeanSq_Ioo_zero_one hf_polar
  have h_shrunk : IntegrableOn (fun r => r * circleMeanSq f r)
                                (Set.Ioo c 1) volume :=
    h_full.mono_set (Ioo_subset_Ioo_zero_one hc hc1)
  have h_eq : (fun r : ℝ => r * circleMeanSq f r) =
              (fun r : ℝ => circleMeanSq f r * r) := by
    funext r
    exact mul_comm _ _
  rw [h_eq] at h_shrunk
  exact h_shrunk

/-! ## Step 3: per-radius circle integrability in `∀ᵐ` form. -/

/-- For almost every radius `r ∈ Ioo c 1` (with respect to the restricted
volume measure), the per-θ slice
`θ ↦ ‖f (polarCoord.symm (r, θ))‖²` is integrable on `Ioo (-π) π`.

Routes through `Integrable.prod_right_ae`, then divides through by the
nonzero `r`-factor via `integrable_fun_smul_iff`. The `∀ᵐ` form is forced
because `Integrable.prod_right_ae` only commits to almost-every-r. -/
theorem circle_integrableOn_normSq_polar_Ioo_ae
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
      IntegrableOn (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
                   (Set.Ioo (-Real.pi) Real.pi) volume := by
  -- Convert `IntegrableOn ... (s ×ˢ t)` to `Integrable ... over restricted prod`.
  have h_prod : Integrable
      (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hf_polar
  -- Per-radius slice integrability for almost every `r ∈ Ioo 0 1`.
  have h_slice : ∀ᵐ r ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      Integrable (fun θ => r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
                 (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    h_prod.prod_right_ae
  -- Restrict the `∀ᵐ` from `Ioo 0 1` to `Ioo c 1`.
  have h_subset : Set.Ioo c 1 ⊆ Set.Ioo (0 : ℝ) 1 :=
    Ioo_subset_Ioo_zero_one hc hc1
  have h_slice' : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
      Integrable (fun θ => r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
                 (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    ae_restrict_of_ae_restrict_of_subset h_subset h_slice
  -- Combine with `r ∈ Ioo c 1 → r > 0`.
  have h_in_set : ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)), r ∈ Set.Ioo c 1 :=
    ae_restrict_mem measurableSet_Ioo
  -- Filter-upwards to extract the per-radius integrability.
  filter_upwards [h_slice', h_in_set] with r hr_int hr_mem
  have hr_pos : 0 < r := lt_trans hc hr_mem.1
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  -- `IntegrableOn (fun θ => ‖f (symm (r,θ))‖²) (Ioo (-π) π) volume` is by
  -- definition `Integrable ... (volume.restrict (Ioo (-π) π))`.
  -- We have `Integrable (fun θ => r * ‖f (symm (r,θ))‖²) (...)` and want
  -- to remove the `r * ` prefix using `integrable_fun_smul_iff`.
  have h_iff : Integrable
      (fun θ => r • ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) ↔
        Integrable
          (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
          (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    integrable_fun_smul_iff hr_ne _
  -- `r • x = r * x` for real `x`, so the `r * ` form coincides with `r • `.
  have h_rewrite :
      (fun θ => r * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = fun θ => r • ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 := by
    funext θ
    exact (smul_eq_mul (a := r) (b := _)).symm
  rw [h_rewrite] at hr_int
  exact h_iff.mp hr_int

end ProofRefinement.Korenblum
