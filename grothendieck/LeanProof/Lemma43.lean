/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma42
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lemma 4.3: H₀ = arcsin

We prove that H₀(z) = arcsin(z) on the strip S = {z ∈ ℂ : |Re z| < 1}.

## Proof sketch (from the paper)

When η = 0, f₀(x₁, x₂) = sign(x₂), so the 4D integral defining H₀ factors into
a product of two 2D integrals. Evaluating via Gaussian integrals and a polar
coordinate computation yields H₀(z) = arcsin(z).

## Formalization strategy

We prove H₀(x) = arcsin(x) for real x ∈ (-1,1) via ODE uniqueness:

1. Both H₀ and arcsin satisfy f'(t) = 1/√(1-t²) on (-1,1)
2. Both satisfy f(0) = 0
3. By Picard-Lindelof uniqueness (`ODE_solution_unique_of_mem_Ioo`), they agree

The derivative of arcsin is in Mathlib (`Real.hasDerivAt_arcsin`).
The derivative of H₀ at real points follows from differentiating the 4D Gaussian integral
under the integral sign and evaluating via Fubini + Sheppard's formula.
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-!
## Basic properties of H₀ (from Lemma 4.2)

These follow directly from the corresponding properties of H_η at η = 0.
They do NOT depend on H₀ = arcsin.
-/

/-- H₀ is analytic on the strip S.
    This is a special case of Lemma 4.2 at η = 0. -/
theorem H0_analyticOnNhd : AnalyticOnNhd ℂ H0 S :=
  H_eta_analyticOnNhd 0

/-- H₀ is odd: H₀(-z) = -H₀(z).
    Follows from the oddness of f₀ = sign(x₂). -/
theorem H0_odd (z : ℂ) (hz : z ∈ S) : H0 (-z) = -H0 z :=
  H_eta_odd 0 z hz

/-- H₀(0) = 0. -/
theorem H0_zero : H0 0 = 0 := by
  have h : H0 0 = -H0 0 := by
    have := H0_odd 0 zero_mem_S
    simp [neg_zero] at this
    exact this
  have : 2 * H0 0 = 0 := by linear_combination H0 0 + h
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp this).resolve_left h2


/-\! ## Content merged from Lemma43_attempt2 -/

/-! ### Sub-lemma A: Bivariate Gaussian integral

The quadratic form Q(x,y) = x² + y² - 2txy with |t| < 1 has matrix
  M = [[1, -t], [-t, 1]], det(M) = 1 - t².

The integral ∫∫ exp(-Q(x,y)/(2(1-t²))) dxdy equals 2π√(det(M)·(1-t²)²/(1-t²))
= 2π√(1-t²) by standard multivariate Gaussian theory.

Proof: Complete the square x → x - ty to decouple the variables:
  Q(x,y) = (x-ty)² + y²(1-t²)
so Q/(2(1-t²)) = (x-ty)²/(2(1-t²)) + y²/2.
After the substitution u = x-ty (Jacobian = 1):
  ∫∫ exp(-Q/(2(1-t²))) dxdy = [∫ exp(-u²/(2(1-t²))) du] · [∫ exp(-y²/2) dy]
  = √(2π(1-t²)) · √(2π) = 2π√(1-t²).
-/

/-- The bivariate Gaussian integral evaluates to π√(1-t²).
    The kernel has exp(-(s²+u²-2tsu)/(1-t²)), which completes to exp(-(x-ty)²/(1-t²) - y²).
    This uses `integral_gaussian` from Mathlib after completing the square. -/
private theorem bivariate_gaussian_integral (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∫ p : ℝ × ℝ,
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2 - 2 * t * p.1 * p.2) / (1 - t ^ 2)) =
    Real.pi * Real.sqrt (1 - t ^ 2) := by
  have ht1 : (1 : ℝ) - t ^ 2 > 0 := by nlinarith [ht.1, ht.2]
  have ht1_ne : (1 - t ^ 2 : ℝ) ≠ 0 := ne_of_gt ht1
  -- Complete the square: Q(x,y) = (x-ty)² + y²(1-t²), so Q/(1-t²) = (x-ty)²/(1-t²) + y²
  have h_csq : ∀ x y : ℝ,
      -(x ^ 2 + y ^ 2 - 2 * t * x * y) / (1 - t ^ 2) =
      -((x - t * y) ^ 2 / (1 - t ^ 2)) + -(y ^ 2) := by
    intro x y; field_simp; ring
  simp_rw [h_csq, Real.exp_add]
  -- Shift x → x + ty in the inner integral
  have h_shift : ∀ y : ℝ,
      ∫ x : ℝ, Real.exp (-((x - t * y) ^ 2 / (1 - t ^ 2))) =
      ∫ x : ℝ, Real.exp (-(x ^ 2 / (1 - t ^ 2))) := by
    intro y
    conv_lhs => rw [show (fun x : ℝ => Real.exp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) =
        (fun x => (fun u : ℝ => Real.exp (-(u ^ 2 / (1 - t ^ 2)))) (x - t * y)) from rfl]
    exact integral_sub_right_eq_self (f := fun u : ℝ => rexp (-(u ^ 2 / (1 - t ^ 2)))) (t * y)
  -- Inner integral: ∫ exp(-x²/(1-t²)) = √(π(1-t²))
  have h_inner : ∫ x : ℝ, Real.exp (-(x ^ 2 / (1 - t ^ 2))) =
      Real.sqrt (Real.pi * (1 - t ^ 2)) := by
    simp_rw [show ∀ x : ℝ, -(x ^ 2 / (1 - t ^ 2)) = -(1 / (1 - t ^ 2)) * x ^ 2 from
      fun x => by ring]
    rw [integral_gaussian, show Real.pi / (1 / (1 - t ^ 2)) = Real.pi * (1 - t ^ 2) from by
      field_simp]
  -- Outer integral: ∫ exp(-y²) = √π
  have h_outer : ∫ y : ℝ, Real.exp (-(y ^ 2)) = Real.sqrt Real.pi := by
    rw [show (fun y : ℝ => Real.exp (-(y ^ 2))) = (fun y => Real.exp (-(1 : ℝ) * y ^ 2)) from by
      ext y; congr 1; ring]
    rw [integral_gaussian, show Real.pi / (1 : ℝ) = Real.pi from div_one _]
  -- Need integrability for Fubini
  have h_coeff_pos : (0 : ℝ) < 1 / (1 - t ^ 2) := by positivity
  have h_integrable : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Real.exp (-((p.1 - t * p.2) ^ 2 / (1 - t ^ 2))) * Real.exp (-(p.2 ^ 2)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have h_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => rexp (-((p.1 - t * p.2) ^ 2 / (1 - t ^ 2))) *
          rexp (-(p.2 ^ 2)))
        (volume.prod volume) := by
      apply Measurable.aestronglyMeasurable; measurability
    rw [integrable_prod_iff' h_meas]
    constructor
    · filter_upwards [] with y
      apply Integrable.mul_const
      have h_eq : (fun x : ℝ => rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) =
          (fun x => rexp (-(1 / (1 - t ^ 2)) * (x - t * y) ^ 2)) := by
        ext x; congr 1; ring
      rw [h_eq]
      exact (integrable_exp_neg_mul_sq h_coeff_pos).comp_sub_right _
    · have h_norm : ∀ y : ℝ, (fun x : ℝ => ‖rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) *
          rexp (-(y ^ 2))‖) = (fun x : ℝ =>
          rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) * rexp (-(y ^ 2))) := by
        intro y; ext x
        rw [Real.norm_of_nonneg (by positivity)]
      simp_rw [h_norm]
      have h_inner_pull : ∀ y : ℝ,
          ∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) * rexp (-(y ^ 2)) =
          (∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) * rexp (-(y ^ 2)) :=
        fun y => integral_mul_const _ _
      simp_rw [h_inner_pull, h_shift, h_inner]
      rw [show (fun y : ℝ => √(Real.pi * (1 - t ^ 2)) * rexp (-(y ^ 2))) =
          (fun y => √(Real.pi * (1 - t ^ 2)) * rexp (-(1 : ℝ) * y ^ 2)) from by
          ext y; congr 2; ring]
      exact (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < 1)).const_mul _
  -- Combine via Fubini
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_symm _ h_integrable]
  simp only [Prod.fst, Prod.snd]
  simp_rw [integral_mul_const, h_shift, h_inner]
  rw [integral_const_mul, h_outer]
  -- √(π(1-t²)) · √π = π · √(1-t²)
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi * (1 - t ^ 2))]
  rw [show Real.pi * (1 - t ^ 2) * Real.pi = Real.pi ^ 2 * (1 - t ^ 2) from by ring]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi ^ 2)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < Real.pi)]
  /- Original proof:
  have ht1 : (1 : ℝ) - t ^ 2 > 0 := by nlinarith [ht.1, ht.2]
  have h2t : 2 * (1 - t ^ 2) > 0 := by linarith
  have h2t_ne : (2 * (1 - t ^ 2) : ℝ) ≠ 0 := ne_of_gt h2t
  -- Step 1: Complete the square: Q(x,y) = (x-ty)² + y²(1-t²)
  -- So Q/(2(1-t²)) = (x-ty)²/(2(1-t²)) + y²/2
  have h_complete_sq : ∀ x y : ℝ,
      -(x ^ 2 + y ^ 2 - 2 * t * x * y) / (2 * (1 - t ^ 2)) =
      -((x - t * y) ^ 2 / (2 * (1 - t ^ 2))) + -(y ^ 2 / 2) := by
    intro x y; field_simp; ring
  simp_rw [h_complete_sq, Real.exp_add]
  -- Step 2: Apply Fubini (integral_prod)
  -- The integral is now ∫∫ exp(-(x-ty)²/(2(1-t²))) · exp(-y²/2) dx dy
  -- After shifting x → x + ty in the inner integral, this becomes:
  -- ∫ exp(-y²/2) [∫ exp(-x²/(2(1-t²))) dx] dy
  -- = [∫ exp(-x²/(2(1-t²))) dx] · [∫ exp(-y²/2) dy]
  -- Step 2: Apply Fubini and evaluate via integral_gaussian
  -- The inner integral (over x) can be shifted: x → x + ty
  -- giving ∫ exp(-x²/(2(1-t²))) dx = √(π / (1/(2(1-t²)))) = √(2π(1-t²))
  -- The outer integral is ∫ exp(-y²/2) dy = √(2π)
  -- Product = 2π√(1-t²)

  -- Step 2a: Rewrite as iterated integrals (x inner, y outer)
  -- and perform the shift x ↦ x + ty in the inner integral
  have h_shift : ∀ y : ℝ,
      ∫ x : ℝ, Real.exp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2)))) =
      ∫ x : ℝ, Real.exp (-(x ^ 2 / (2 * (1 - t ^ 2)))) := by
    intro y
    conv_lhs => rw [show (fun x : ℝ => Real.exp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2))))) =
        (fun x => (fun u : ℝ => Real.exp (-(u ^ 2 / (2 * (1 - t ^ 2))))) (x - t * y)) from rfl]
    exact @MeasureTheory.integral_sub_right_eq_self ℝ ℝ _ _ _
      MeasureTheory.volume _ _ _
      (fun x : ℝ => Real.exp (-(x ^ 2 / (2 * (1 - t ^ 2))))) (t * y)
  -- Step 2b: Evaluate ∫ exp(-x²/(2(1-t²))) dx = √(2π(1-t²))
  have h_inner_eq : ∀ x : ℝ,
      Real.exp (-(x ^ 2 / (2 * (1 - t ^ 2)))) =
      Real.exp (-(1 / (2 * (1 - t ^ 2))) * x ^ 2) := by
    intro x; congr 1; ring
  have h_inner : ∫ x : ℝ, Real.exp (-(x ^ 2 / (2 * (1 - t ^ 2)))) =
      Real.sqrt (Real.pi / (1 / (2 * (1 - t ^ 2)))) := by
    simp_rw [h_inner_eq]
    exact integral_gaussian _
  have h_inner_simp : Real.pi / (1 / (2 * (1 - t ^ 2))) =
      2 * Real.pi * (1 - t ^ 2) := by
    field_simp
  -- Step 2c: Evaluate ∫ exp(-y²/2) dy = √(2π)
  have h_outer_eq : ∀ y : ℝ,
      Real.exp (-(y ^ 2 / 2)) = Real.exp (-(1/2 : ℝ) * y ^ 2) := by
    intro y; congr 1; ring
  have h_outer : ∫ y : ℝ, Real.exp (-(y ^ 2 / 2)) =
      Real.sqrt (Real.pi / (1/2 : ℝ)) := by
    simp_rw [h_outer_eq]
    exact integral_gaussian _
  have h_outer_simp : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by
    field_simp
  -- Step 3: Combine via Fubini
  -- The integrand factors as f(x,y) * g(y) where f depends on (x,y) and g only on y.
  -- Using integral_prod (Fubini) + shift + integral_gaussian evaluation.

  -- Step 3a: Integrability (needed for Fubini)
  have h_integrable : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-((p.1 - t * p.2) ^ 2 / (2 * (1 - t ^ 2)))) *
      Real.exp (-(p.2 ^ 2 / 2)))
      ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume) := by
    -- Use integrable_prod_iff: for each y, x ↦ f(x,y) is integrable (shifted Gaussian),
    -- and y ↦ ∫ ‖f(x,y)‖ dx is integrable (Gaussian in y times a constant).
    have h_coeff_pos : (0 : ℝ) < 1 / (2 * (1 - t ^ 2)) := by positivity
    -- The integrand is measurable
    have h_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => rexp (-((p.1 - t * p.2) ^ 2 / (2 * (1 - t ^ 2)))) *
          rexp (-(p.2 ^ 2 / 2)))
        (volume.prod volume) := by
      apply Measurable.aestronglyMeasurable
      measurability
    rw [integrable_prod_iff' h_meas]
    constructor
    · -- For a.e. y, x ↦ exp(-((x-ty)²/(2(1-t²)))) * exp(-y²/2) is integrable in x
      -- This is exp(-y²/2) * [Gaussian in x], which is integrable.
      filter_upwards [] with y
      apply Integrable.mul_const
      -- Need: x ↦ exp(-((x-ty)²/(2(1-t²)))) is integrable
      -- Rewrite to standard form exp(-c * (x - a)²) and use comp_sub_right
      have h_eq : (fun x : ℝ => rexp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2))))) =
          (fun x => rexp (-(1 / (2 * (1 - t ^ 2))) * (x - t * y) ^ 2)) := by
        ext x; congr 1; ring
      rw [h_eq]
      exact (integrable_exp_neg_mul_sq h_coeff_pos).comp_sub_right _
    · -- y ↦ ∫ ‖exp(-((x-ty)²/(2(1-t²)))) * exp(-y²/2)‖ dx is integrable
      -- = y ↦ exp(-y²/2) * ∫ exp(-((x-ty)²/(2(1-t²)))) dx
      -- = y ↦ exp(-y²/2) * √(2π(1-t²))
      -- = √(2π(1-t²)) * exp(-y²/2), which is integrable.
      -- First, simplify the norm (integrand is non-negative)
      have h_norm : ∀ y : ℝ, (fun x : ℝ => ‖rexp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2)))) *
          rexp (-(y ^ 2 / 2))‖) = (fun x : ℝ =>
          rexp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2)))) * rexp (-(y ^ 2 / 2))) := by
        intro y; ext x
        rw [Real.norm_of_nonneg (by positivity)]
      simp_rw [h_norm]
      -- Now pull out exp(-y²/2) from the inner integral
      have h_inner_pull : ∀ y : ℝ,
          ∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2)))) * rexp (-(y ^ 2 / 2)) =
          (∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2))))) * rexp (-(y ^ 2 / 2)) :=
        fun y => integral_mul_const _ _
      simp_rw [h_inner_pull, h_shift, h_inner, h_inner_simp]
      -- Now: y ↦ √(2π(1-t²)) * exp(-y²/2) is integrable
      -- Rewrite exp(-y²/2) as exp(-(1/2) * y²) to match integrable_exp_neg_mul_sq
      simp_rw [h_outer_eq]
      exact (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 from by positivity)).const_mul _
  -- Step 3b: Apply Fubini to convert ∫_{ℝ²} to ∫_y ∫_x
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_symm _ h_integrable]
  -- Simplify (x, y).1 → x and (x, y).2 → y
  simp only []
  -- Now the goal is: ∫_y (∫_x exp(-((x-ty)²/(2(1-t²)))) * exp(-y²/2) dx) dy = 2π√(1-t²)
  -- Pull exp(-y²/2) out of the inner integral (it's constant in x)
  have h_pull : ∀ y : ℝ,
      ∫ x : ℝ, Real.exp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2)))) * Real.exp (-(y ^ 2 / 2)) =
      (∫ x : ℝ, Real.exp (-((x - t * y) ^ 2 / (2 * (1 - t ^ 2))))) * Real.exp (-(y ^ 2 / 2)) :=
    fun y => MeasureTheory.integral_mul_const _ _
  simp_rw [h_pull]
  -- Now: ∫_y (∫_x exp(-((x-ty)²/(2(1-t²)))) dx) * exp(-y²/2) dy = 2π√(1-t²)
  -- Apply the shift: inner integral is independent of y
  simp_rw [h_shift, h_inner, h_inner_simp]
  -- Now: ∫_y √(2π(1-t²)) * exp(-y²/2) dy = 2π√(1-t²)
  -- Pull √(2π(1-t²)) out (it's constant in y)
  rw [MeasureTheory.integral_const_mul]
  -- Now: √(2π(1-t²)) * ∫_y exp(-y²/2) dy = 2π√(1-t²)
  rw [h_outer, h_outer_simp]
  -- Now: √(2π(1-t²)) * √(2π) = 2π√(1-t²)
  -- √(2π(1-t²)) * √(2π) = 2π * √(1-t²)
  -- Combine: √a * √b = √(a*b), then factor (2π)(1-t²) * (2π) = (2π)² * (1-t²)
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (1 - t ^ 2))]
  rw [show 2 * Real.pi * (1 - t ^ 2) * (2 * Real.pi) =
      (2 * Real.pi) ^ 2 * (1 - t ^ 2) from by ring]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 2)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] -/

/-! ### Sub-lemma B: Sheppard's median dichotomy formula

For (X,Y) bivariate standard normal with correlation ρ = t ∈ (-1,1):

  E[sign(X)·sign(Y)] = (2/π)·arcsin(t)

This is Sheppard's formula (1899). Equivalently:

  (1/(2π√(1-t²))) ∫∫ sign(x)·sign(y)·exp(-(x²+y²-2txy)/(2(1-t²))) dxdy = (2/π)·arcsin(t)

Or without normalization:

  ∫∫ sign(x)·sign(y)·exp(-(x²+y²-2txy)/(2(1-t²))) dxdy = 4·√(1-t²)·arcsin(t)

Proof sketch:
1. Complete the square: let u = (x - ty)/√(1-t²), so x = u√(1-t²) + ty
2. sign(x) = sign(u√(1-t²) + ty). The integral becomes:
   ∫∫ sign(u√(1-t²) + ty)·sign(y)·exp(-u²/2)·exp(-y²/2) dudy / (2π)
   (where we used that u and y are now independent standard normals)
3. Convert y = r·sin(θ), u = r·cos(θ) to polar coordinates.
4. The radial integral ∫₀^∞ r·exp(-r²/2) dr = 1.
5. The angular integral ∫₀^{2π} sign(r·cos(θ)·√(1-t²) + t·r·sin(θ))·sign(r·sin(θ)) dθ/(2π)
   = ∫₀^{2π} sign(cos(θ)·√(1-t²) + t·sin(θ))·sign(sin(θ)) dθ/(2π)
   = (2/π)·arcsin(t)
   The last step uses the fact that cos(θ)·√(1-t²) + t·sin(θ) = sin(θ + α) where
   sin(α) = t, and the angular integral evaluates to (2/π)·α = (2/π)·arcsin(t).
-/

/-! #### Angular integral helper

The key identity: for β ∈ (0, π), the piecewise-constant angular integral evaluates as:
∫ θ in (-π)..π, sign(sin(θ + β)) * sign(sin θ) dθ = 2π - 4β

Proof: Split the interval at -β, 0, π-β (the zeros of the integrands):
- On (-π, -β): both sin θ < 0 and sin(θ+β) < 0, so product = +1, contribution = π - β
- On (-β, 0): sin θ < 0 and sin(θ+β) > 0, so product = -1, contribution = -(β)
- On (0, π-β): both > 0, product = +1, contribution = π - β
- On (π-β, π): sin θ > 0 and sin(θ+β) < 0, so product = -1, contribution = -(β)
Total = 2(π - β) - 2β = 2π - 4β

With β = arccos(t), this gives 2π - 4arccos(t) = 2π - 4(π/2 - arcsin(t)) = 4·arcsin(t).
-/

/-- The angular integral identity: for β ∈ (0, π),
  ∫ θ in (-π)..π, sign(sin(θ+β))·sign(sin θ) = 2π - 4β.

  This is proved by splitting at the zeros -β, 0, π-β and evaluating
  each piece as an integral of a constant (±1). -/
private theorem angular_integral_identity (β : ℝ) (hβ_pos : 0 < β) (hβ_lt : β < Real.pi) :
    ∫ θ in (-Real.pi)..Real.pi,
      (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then (1 : ℝ) else -1) =
    2 * Real.pi - 4 * β := by
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- The integrand is bounded, hence integrable on any interval
  have h_bdd : ∀ θ : ℝ,
      ‖(if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1)‖ ≤ 1 := by
    intro θ
    have h1 : (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) = 1 ∨
              (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) = -1 := by
      split_ifs <;> simp
    have h2 : (if Real.sin θ > 0 then (1 : ℝ) else -1) = 1 ∨
              (if Real.sin θ > 0 then (1 : ℝ) else -1) = -1 := by
      split_ifs <;> simp
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
  have h_meas : Measurable (fun θ : ℝ => (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1)) := by
    apply Measurable.mul
    · apply Measurable.ite
      · exact measurableSet_lt measurable_const
          ((Real.measurable_sin.comp (measurable_id.add_const β)))
      · exact measurable_const
      · exact measurable_const
    · apply Measurable.ite
      · exact measurableSet_lt measurable_const Real.measurable_sin
      · exact measurable_const
      · exact measurable_const
  have h_int : ∀ a b : ℝ, IntervalIntegrable
      (fun θ => (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1)) volume a b := by
    intro a b
    apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c := (1 : ℝ)))
    · exact h_meas.aestronglyMeasurable.restrict
    · filter_upwards [] with θ
      rw [norm_one]; exact h_bdd θ
  -- Helper for a.e. exclusion of a point
  have h_ae_ne : ∀ c : ℝ, ∀ᵐ θ ∂(volume : MeasureTheory.Measure ℝ), θ ≠ c := by
    intro c
    exact MeasureTheory.compl_mem_ae_iff.mpr Real.volume_singleton
  -- Split: ∫_{-π}^{π} = (∫_{-π}^{-β} + ∫_{-β}^{0}) + (∫_{0}^{π-β} + ∫_{π-β}^{π})
  conv_lhs => rw [
    ← intervalIntegral.integral_add_adjacent_intervals
      (IntervalIntegrable.trans (h_int (-Real.pi) (-β)) (h_int (-β) 0))
      (IntervalIntegrable.trans (h_int 0 (Real.pi - β)) (h_int (Real.pi - β) Real.pi)),
    ← intervalIntegral.integral_add_adjacent_intervals (h_int (-Real.pi) (-β)) (h_int (-β) 0),
    ← intervalIntegral.integral_add_adjacent_intervals
      (h_int 0 (Real.pi - β)) (h_int (Real.pi - β) Real.pi)]
  -- On (-π, -β]: sin θ < 0, sin(θ+β) ≤ 0 → product = 1
  have h1 : ∫ θ in (-Real.pi)..(-β),
      (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then (1 : ℝ) else -1) = Real.pi - β := by
    have hle : -Real.pi ≤ -β := by linarith
    conv_lhs => rw [show ∫ θ in (-Real.pi)..(-β),
        (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1) =
        ∫ _ in (-Real.pi)..(-β), (1 : ℝ) from by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with θ hθ
      rw [Set.uIoc_of_le hle] at hθ
      have hsinθ : ¬(Real.sin θ > 0) := not_lt.mpr (le_of_lt
        (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hθ.2]) (by linarith [hθ.1])))
      have hsinθβ : ¬(Real.sin (θ + β) > 0) := not_lt.mpr
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hθ.2]) (by linarith [hθ.1]))
      simp [hsinθ, hsinθβ]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- On (-β, 0]: sin θ ≤ 0, sin(θ+β) > 0 → product = -1
  have h2 : ∫ θ in (-β)..(0 : ℝ),
      (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then (1 : ℝ) else -1) = -β := by
    have hle : -β ≤ (0 : ℝ) := by linarith
    conv_lhs => rw [show ∫ θ in (-β)..(0 : ℝ),
        (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1) =
        ∫ _ in (-β)..(0 : ℝ), (-1 : ℝ) from by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with θ hθ
      rw [Set.uIoc_of_le hle] at hθ
      have hsinθβ : Real.sin (θ + β) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      have hsinθ : ¬(Real.sin θ > 0) := not_lt.mpr
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hθ.2]) (by linarith [hθ.1]))
      simp [hsinθβ, hsinθ]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- On (0, π-β): sin θ > 0, sin(θ+β) > 0 → product = 1 (a.e., excluding θ=π-β)
  have h3 : ∫ θ in (0 : ℝ)..(Real.pi - β),
      (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then (1 : ℝ) else -1) = Real.pi - β := by
    have hle : (0 : ℝ) ≤ Real.pi - β := by linarith
    conv_lhs => rw [show ∫ θ in (0 : ℝ)..(Real.pi - β),
        (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1) =
        ∫ _ in (0 : ℝ)..(Real.pi - β), (1 : ℝ) from by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [h_ae_ne (Real.pi - β)] with θ hθ_ne hθ
      rw [Set.uIoc_of_le hle] at hθ
      have hsinθ : Real.sin θ > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      have hsinθβ : Real.sin (θ + β) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [show θ < Real.pi - β from lt_of_le_of_ne hθ.2 hθ_ne])
      simp [hsinθ, hsinθβ]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- On (π-β, π]: sin θ > 0, sin(θ+β) ≤ 0 → product = -1 (a.e., excluding θ=π)
  have h4 : ∫ θ in (Real.pi - β)..Real.pi,
      (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then (1 : ℝ) else -1) = -β := by
    have hle : Real.pi - β ≤ Real.pi := by linarith
    conv_lhs => rw [show ∫ θ in (Real.pi - β)..Real.pi,
        (if Real.sin (θ + β) > 0 then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then (1 : ℝ) else -1) =
        ∫ _ in (Real.pi - β)..Real.pi, (-1 : ℝ) from by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [h_ae_ne Real.pi] with θ hθ_ne hθ
      rw [Set.uIoc_of_le hle] at hθ
      have hsinθ : Real.sin θ > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (lt_of_le_of_ne hθ.2 hθ_ne)
      have hsinθβ : ¬(Real.sin (θ + β) > 0) := by
        push_neg
        -- θ + β ∈ (π, π + β] ⊂ (π, 2π). Use sin(x+π) = -sin(x):
        -- sin(θ+β) = sin((θ+β-π) + π) = -sin(θ+β-π)
        -- θ+β-π ∈ (0, β] ⊂ (0, π), so sin(θ+β-π) ≥ 0, hence sin(θ+β) ≤ 0
        rw [show θ + β = (θ + β - Real.pi) + Real.pi from by ring, Real.sin_add_pi]
        linarith [Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ θ + β - Real.pi from by linarith [hθ.1])
          (show θ + β - Real.pi ≤ Real.pi from by linarith [hθ.2])]
      simp [hsinθ, hsinθβ]]
    simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- Combine: (π-β) + (-β) + (π-β) + (-β) = 2π - 4β
  linarith

/-- **Sheppard's median dichotomy formula** (1899):
    For a bivariate standard normal with correlation t,
    E[sign(X)·sign(Y)] = (2/π)·arcsin(t).

    Equivalently, without the bivariate Gaussian normalization:
    ∫∫ sign(x)·sign(y)·exp(-(x²+y²-2txy)/(2(1-t²))) dxdy = 4·√(1-t²)·arcsin(t)

    Proof: Complete the square to decouple into independent standard
    normals, switch to polar coordinates (Mathlib: `integral_comp_polarCoord_symm`),
    evaluate radial integral via `integral_mul_cexp_neg_mul_sq`, and evaluate
    the angular integral via `angular_integral_identity` with β = arccos(t).

    Reference: Sheppard (1899), "On the Application of the Theory of Error to
    Cases of Normal Distribution and Normal Correlation".
    Modern treatment: Tong (1990), "The Multivariate Normal Distribution", Sec 2.4. -/
private theorem sheppard_median_dichotomy (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∫ p : ℝ × ℝ,
      (if p.1 > 0 then (1 : ℝ) else -1) * (if p.2 > 0 then (1 : ℝ) else -1) *
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2 - 2 * t * p.1 * p.2) / (1 - t ^ 2)) =
    2 * Real.sqrt (1 - t ^ 2) * Real.arcsin t := by
  have ht1 : (1 : ℝ) - t ^ 2 > 0 := by nlinarith [ht.1, ht.2]
  have hsqrt_pos : Real.sqrt (1 - t ^ 2) > 0 := Real.sqrt_pos.mpr ht1
  have hsqrt_ne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  -- Step 1: Complete the square in the exponent
  have h_csq : ∀ x y : ℝ,
      -(x ^ 2 + y ^ 2 - 2 * t * x * y) / (1 - t ^ 2) =
      -((x - t * y) ^ 2 / (1 - t ^ 2)) + -(y ^ 2) := by
    intro x y; field_simp; ring
  simp_rw [h_csq, Real.exp_add]
  -- Step 2: Reduce to evaluating a standard bivariate normal integral
  -- via the linear substitution (x,y) → ((x-ty)/s, y) where s = √(1-t²).
  -- The Jacobian is s = √(1-t²), so the integral becomes:
  --   √(1-t²) * ∫∫ sign(v·s + t·w) sign(w) exp(-(v²+w²)) dv dw
  -- We prove the inner integral = 2 arcsin t via polar coordinates.
  set s := Real.sqrt (1 - t ^ 2) with hs_def
  -- Step 2a: It suffices to show the standard normal integral evaluates correctly
  suffices h_std : ∫ p : ℝ × ℝ,
      (if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
      (if p.2 > 0 then (1 : ℝ) else -1) *
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) =
      2 * Real.arcsin t by
    -- Reduce to: LHS = s * h_std = s * 2 arcsin t = 2s arcsin t
    rw [show 2 * s * Real.arcsin t =
      s * (2 * Real.arcsin t) from by ring, ← h_std]
    -- For each y, the inner x-integral transforms via shift+scale:
    -- ∫_x sign(x) exp(-((x-ty)²/(s²)))
    -- = s * ∫_u sign(su+ty) exp(-u²)
    have hs_sq : s ^ 2 = 1 - t ^ 2 := by
      rw [hs_def, sq_sqrt (le_of_lt ht1)]
    have h_inner : ∀ y : ℝ,
        ∫ x : ℝ, (if x > 0 then (1 : ℝ) else -1) *
          Real.exp (-((x - t * y) ^ 2 / (1 - t ^ 2))) =
        s * ∫ u : ℝ,
          (if s * u + t * y > 0 then (1 : ℝ) else -1) *
          Real.exp (-(u ^ 2)) := by
      intro y
      -- Step A: Shift x → x + ty
      have h_shift :=
        @MeasureTheory.integral_sub_right_eq_self ℝ ℝ _ _ _
        volume _ _ _
        (fun u : ℝ =>
          (if u + t * y > 0 then (1 : ℝ) else -1) *
          Real.exp (-(u ^ 2 / (1 - t ^ 2)))) (t * y)
      simp only [sub_add_cancel] at h_shift
      rw [h_shift]
      -- Step B: Scale u → su
      set g : ℝ → ℝ := fun x =>
        (if x + t * y > 0 then (1 : ℝ) else -1) *
        Real.exp (-(x ^ 2 / (1 - t ^ 2)))
      have h_comp : (fun u : ℝ =>
          (if s * u + t * y > 0 then (1 : ℝ) else -1) *
          Real.exp (-(u ^ 2))) =
        (fun u => g (s * u)) := by
        ext u; simp only [g]; congr 1
        congr 1; congr 1
        rw [mul_pow, hs_sq]; field_simp
      rw [h_comp, Measure.integral_comp_mul_left g s,
        smul_eq_mul, abs_inv, abs_of_pos hsqrt_pos]
      field_simp
    -- Fubini on both sides, then use h_inner to match inner integrals
    rw [Measure.volume_eq_prod]
    -- Integrability (bounded by Gaussians)
    have h_sign_bdd : ∀ p : ℝ × ℝ,
        ‖((if p.1 > 0 then (1 : ℝ) else -1) *
         if p.2 > 0 then 1 else -1)‖ ≤ 1 := by
      intro ⟨x, y⟩; simp only [norm_mul]
      have h1 : ‖(if x > 0 then (1 : ℝ) else -1)‖ = 1 := by
        split_ifs <;> simp
      have h2 : ‖(if y > 0 then (1 : ℝ) else -1)‖ = 1 := by
        split_ifs <;> simp
      rw [h1, h2]; norm_num
    have h_sign_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (if p.1 > 0 then (1 : ℝ) else -1) *
          if p.2 > 0 then 1 else -1)
        (volume.prod volume) :=
      (Measurable.mul
        (Measurable.ite (measurableSet_lt measurable_const
          measurable_fst) measurable_const measurable_const)
        (Measurable.ite (measurableSet_lt measurable_const
          measurable_snd) measurable_const measurable_const)
      ).aestronglyMeasurable
    -- Gaussian integrability
    have h_gauss_int_L : Integrable (fun p : ℝ × ℝ =>
        rexp (-((p.1 - t * p.2) ^ 2 / (1 - t ^ 2))) *
        rexp (-(p.2 ^ 2))) (volume.prod volume) := by
      have h_coeff_pos : (0 : ℝ) < 1 / (1 - t ^ 2) := by positivity
      have h_meas : AEStronglyMeasurable
          (fun p : ℝ × ℝ => rexp (-((p.1 - t * p.2) ^ 2 / (1 - t ^ 2))) *
            rexp (-(p.2 ^ 2)))
          (volume.prod volume) := by
        apply Measurable.aestronglyMeasurable; measurability
      rw [integrable_prod_iff' h_meas]
      constructor
      · filter_upwards [] with y
        apply Integrable.mul_const
        have h_eq : (fun x : ℝ => rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) =
            (fun x => rexp (-(1 / (1 - t ^ 2)) * (x - t * y) ^ 2)) := by
          ext x; congr 1; ring
        rw [h_eq]
        exact (integrable_exp_neg_mul_sq h_coeff_pos).comp_sub_right _
      · have h_norm : ∀ y : ℝ, (fun x : ℝ => ‖rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) *
            rexp (-(y ^ 2))‖) = (fun x : ℝ =>
            rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) * rexp (-(y ^ 2))) := by
          intro y; ext x
          rw [Real.norm_of_nonneg (by positivity)]
        simp_rw [h_norm]
        have h_inner_pull : ∀ y : ℝ,
            ∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) * rexp (-(y ^ 2)) =
            (∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) * rexp (-(y ^ 2)) :=
          fun y => integral_mul_const _ _
        simp_rw [h_inner_pull]
        have h_shift_int : ∀ y : ℝ,
            ∫ x : ℝ, rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) =
            ∫ x : ℝ, rexp (-(x ^ 2 / (1 - t ^ 2))) := by
          intro y
          conv_lhs => rw [show (fun x : ℝ => rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) =
              (fun x => (fun u : ℝ => rexp (-(u ^ 2 / (1 - t ^ 2)))) (x - t * y)) from rfl]
          exact MeasureTheory.integral_sub_right_eq_self
            (f := fun x : ℝ => rexp (-(x ^ 2 / (1 - t ^ 2)))) (t * y)
        have h_inner_val : ∫ x : ℝ, rexp (-(x ^ 2 / (1 - t ^ 2))) =
            Real.sqrt (Real.pi / (1 / (1 - t ^ 2))) := by
          simp_rw [show ∀ x : ℝ, -(x ^ 2 / (1 - t ^ 2)) =
            -(1 / (1 - t ^ 2)) * x ^ 2 from fun x => by ring]
          exact integral_gaussian _
        simp_rw [h_shift_int, h_inner_val]
        simp_rw [show ∀ y : ℝ, -(y ^ 2) = -(1 : ℝ) * y ^ 2 from fun y => by ring]
        exact (integrable_exp_neg_mul_sq (show (0:ℝ) < 1 from by positivity)).const_mul _
    have h_gauss_int_R : Integrable (fun p : ℝ × ℝ =>
        rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2)))
        (volume.prod volume) := by
      have h_eq : (fun p : ℝ × ℝ => rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2))) =
        (fun p => (fun x => rexp (-(1 : ℝ) * x ^ 2)) p.1 *
          (fun y => rexp (-(1 : ℝ) * y ^ 2)) p.2) := by
        ext ⟨x, y⟩; simp only []; congr 1 <;> (congr 1; ring)
      rw [h_eq]
      exact Integrable.mul_prod
        (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < 1))
        (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < 1))
    have h_int_L := h_gauss_int_L.bdd_mul (c := 1) h_sign_meas
      (by filter_upwards [] with p; exact h_sign_bdd p)
    have h_sign_meas' : AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
          if p.2 > 0 then 1 else -1)
        (volume.prod volume) :=
      (Measurable.mul
        (Measurable.ite
          (measurableSet_lt measurable_const
            ((measurable_const.mul measurable_fst).add
              (measurable_const.mul measurable_snd)))
          measurable_const measurable_const)
        (Measurable.ite (measurableSet_lt measurable_const
          measurable_snd) measurable_const measurable_const)
      ).aestronglyMeasurable
    have h_sign_bdd' : ∀ p : ℝ × ℝ,
        ‖((if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
         if p.2 > 0 then 1 else -1)‖ ≤ 1 := by
      intro ⟨x, y⟩; simp only [norm_mul]
      have h1 : ‖(if s * x + t * y > 0 then (1 : ℝ) else -1)‖ =
          1 := by split_ifs <;> simp
      have h2 : ‖(if y > 0 then (1 : ℝ) else -1)‖ = 1 := by
        split_ifs <;> simp
      rw [h1, h2]; norm_num
    have h_exp_split_R : (fun p : ℝ × ℝ =>
        rexp (-(p.1 ^ 2 + p.2 ^ 2))) =
        (fun p => rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2)))
        := by
      ext ⟨x, y⟩; rw [← Real.exp_add]; congr 1; ring
    have h_int_R : Integrable (fun p : ℝ × ℝ =>
        ((if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
         if p.2 > 0 then 1 else -1) *
        rexp (-(p.1 ^ 2 + p.2 ^ 2)))
        (volume.prod volume) := by
      have h_eq : (fun p : ℝ × ℝ =>
          ((if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
           if p.2 > 0 then 1 else -1) *
          rexp (-(p.1 ^ 2 + p.2 ^ 2))) =
        (fun p : ℝ × ℝ =>
          ((if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
           if p.2 > 0 then 1 else -1) *
          (rexp (-(p.1 ^ 2)) * rexp (-(p.2 ^ 2)))) := by
        ext ⟨x, y⟩; congr 1; rw [← Real.exp_add]; congr 1; ring
      rw [h_eq]
      exact h_gauss_int_R.bdd_mul (c := 1) h_sign_meas'
          (by filter_upwards [] with p; exact h_sign_bdd' p)
    -- Fubini on both sides
    rw [integral_prod_symm _ h_int_L,
      integral_prod_symm _ h_int_R]
    simp only []
    -- Pull s inside the outer integral on RHS
    rw [← integral_const_mul]
    -- Match integrands pointwise via h_inner
    congr 1; ext y
    -- Split exp(-(x²+y²)) and pull sign(y)*exp(-y²) out
    have h_pull_L :
        (fun x : ℝ =>
          ((if x > 0 then (1 : ℝ) else -1) *
           if y > 0 then 1 else -1) *
            (rexp (-((x - t * y) ^ 2 / (1 - t ^ 2))) *
             rexp (-(y ^ 2)))) =
        (fun x => ((if x > 0 then (1 : ℝ) else -1) *
          rexp (-((x - t * y) ^ 2 / (1 - t ^ 2)))) *
          ((if y > 0 then 1 else -1) *
           rexp (-(y ^ 2)))) := by
      ext x; ring
    rw [h_pull_L, integral_mul_const]
    have h_pull_R :
        (fun x : ℝ =>
          ((if s * x + t * y > 0 then (1 : ℝ) else -1) *
           if y > 0 then 1 else -1) *
          rexp (-(x ^ 2 + y ^ 2))) =
        (fun x => ((if s * x + t * y > 0 then (1 : ℝ) else -1) *
          rexp (-(x ^ 2))) *
          ((if y > 0 then 1 else -1) *
           rexp (-(y ^ 2)))) := by
      ext x
      rw [show rexp (-(x ^ 2 + y ^ 2)) =
        rexp (-(x ^ 2)) * rexp (-(y ^ 2)) from by
        rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [h_pull_R, integral_mul_const, h_inner]; ring
  -- Step 2b: Evaluate the standard normal integral via polar coordinates
  -- ∫∫ sign(sx+ty) sign(y) exp(-(x²+y²)) = 2 arcsin t
  -- Using polar: (x,y) = (r cos θ, r sin θ)
  -- For r > 0: sign(r·z) = sign(z)
  -- Trig identity: s cos θ + t sin θ = sin(θ + arccos t)
  -- Factor into radial × angular integrals.
  -- Convert to polar coordinates
  rw [show (fun p : ℝ × ℝ =>
      (if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
      (if p.2 > 0 then (1 : ℝ) else -1) *
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2))) =
    (fun p : ℝ × ℝ =>
      (if s * p.1 + t * p.2 > 0 then (1 : ℝ) else -1) *
      (if p.2 > 0 then 1 else -1) *
      Real.exp (-1 * (p.1 ^ 2 + p.2 ^ 2))) from by
    ext p; congr 1; ring]
  rw [← integral_comp_polarCoord_symm]
  -- Goal: ∫ p in target, p.1 • f(polarCoord.symm p) = 2 arcsin t
  -- polarCoord.symm(r,θ) = (r cos θ, r sin θ)
  -- target = Ioi 0 ×ˢ Ioo(-π)(π)
  -- Simplify polarCoord.symm
  simp only [polarCoord_symm_apply]
  -- Simplify the sign expressions for r > 0
  -- For p ∈ target: p.1 > 0, so sign(p.1 · z) = sign(z)
  have h_sign_factor : ∀ p : ℝ × ℝ, p ∈ polarCoord.target →
      p.1 • ((if s * (p.1 * Real.cos p.2) + t * (p.1 * Real.sin p.2) > 0
        then (1 : ℝ) else -1) *
      (if p.1 * Real.sin p.2 > 0 then 1 else -1) *
      Real.exp (-1 * ((p.1 * Real.cos p.2) ^ 2 +
        (p.1 * Real.sin p.2) ^ 2))) =
      (p.1 * Real.exp (-(p.1 ^ 2))) *
      ((if Real.sin (p.2 + Real.arccos t) > 0 then (1 : ℝ) else -1) *
       (if Real.sin p.2 > 0 then 1 else -1)) := by
    intro ⟨r, θ⟩ hp
    simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hp
    obtain ⟨hr, hθ⟩ := hp
    simp only [smul_eq_mul]
    -- Simplify the exponent: (r cos θ)² + (r sin θ)² = r²
    have h_exp : -1 * ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) =
        -(r ^ 2) := by
      have := Real.sin_sq_add_cos_sq θ; nlinarith
    rw [h_exp]
    -- Simplify sign(r · (s cos θ + t sin θ)) for r > 0
    have h_factor1 : s * (r * Real.cos θ) + t * (r * Real.sin θ) =
        r * (s * Real.cos θ + t * Real.sin θ) := by ring
    rw [h_factor1]
    -- Trig identity: s cos θ + t sin θ = sin(θ + arccos t)
    have h_trig : s * Real.cos θ + t * Real.sin θ =
        Real.sin (θ + Real.arccos t) := by
      rw [Real.sin_add, Real.cos_arccos
        (by linarith [ht.1]) (by linarith [ht.2]),
        Real.sin_arccos, hs_def]; ring
    rw [h_trig]
    -- For r > 0: sign(r · z) = sign(z)
    have h_sign_r : (if r * Real.sin (θ + Real.arccos t) > 0
        then (1 : ℝ) else -1) =
        (if Real.sin (θ + Real.arccos t) > 0 then 1 else -1) := by
      by_cases h : Real.sin (θ + Real.arccos t) > 0
      · simp [mul_pos hr h, h]
      · push_neg at h
        simp [show ¬(r * Real.sin (θ + Real.arccos t) > 0) from
          by nlinarith, h]
    rw [h_sign_r]
    -- For r > 0: sign(r sin θ) = sign(sin θ)
    have h_sign_r2 : (if r * Real.sin θ > 0 then (1 : ℝ) else -1) =
        (if Real.sin θ > 0 then 1 else -1) := by
      by_cases h : Real.sin θ > 0
      · simp [mul_pos hr h, h]
      · push_neg at h
        simp [show ¬(r * Real.sin θ > 0) from by nlinarith, h]
    rw [h_sign_r2]
    ring
  -- Rewrite the integrand using h_sign_factor
  rw [show ∫ p in polarCoord.target,
      p.1 • ((if s * (p.1 * Real.cos p.2) + t * (p.1 * Real.sin p.2) > 0
        then (1 : ℝ) else -1) *
      (if p.1 * Real.sin p.2 > 0 then 1 else -1) *
      Real.exp (-1 * ((p.1 * Real.cos p.2) ^ 2 +
        (p.1 * Real.sin p.2) ^ 2))) =
    ∫ p in polarCoord.target,
      (p.1 * Real.exp (-(p.1 ^ 2))) *
      ((if Real.sin (p.2 + Real.arccos t) > 0 then (1 : ℝ) else -1) *
       (if Real.sin p.2 > 0 then 1 else -1)) from
    MeasureTheory.setIntegral_congr_fun
      (measurableSet_Ioi.prod measurableSet_Ioo)
      (fun p hp => h_sign_factor p hp)]
  -- Factor into radial × angular using setIntegral_prod_mul
  -- First unfold polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
    from rfl]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul
      (fun r => r * Real.exp (-(r ^ 2)))
      (fun θ => (if Real.sin (θ + Real.arccos t) > 0
        then (1 : ℝ) else -1) *
        (if Real.sin θ > 0 then 1 else -1))
      (Ioi 0) (Ioo (-Real.pi) Real.pi)]
  -- Evaluate the radial integral = 1/2
  have h_radial :
      ∫ r in Ioi (0 : ℝ), r * Real.exp (-(r ^ 2)) = 1 / 2 := by
    set f := (fun r : ℝ => -(1/2 : ℝ) * Real.exp (-(r ^ 2)))
    have h_deriv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f
        (x * Real.exp (-(x ^ 2))) x := by
      intro x _
      have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2)) (-(2 * x)) x :=
        (hasDerivAt_pow 2 x).neg.congr_deriv (by ring)
      have h2 : HasDerivAt (fun r : ℝ => Real.exp (-(r ^ 2)))
          (Real.exp (-(x ^ 2)) * -(2 * x)) x := h1.exp
      have h3 : HasDerivAt f
          (-(1/2 : ℝ) * (Real.exp (-(x ^ 2)) * -(2 * x))) x :=
        h2.const_mul _
      exact h3.congr_deriv (by ring)
    have h_tendsto :
        Filter.Tendsto f Filter.atTop (nhds 0) := by
      have h_exp_tends : Filter.Tendsto (fun r : ℝ => Real.exp (-(r ^ 2)))
          Filter.atTop (nhds 0) :=
        tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp
            (Filter.tendsto_pow_atTop
              (show (2:ℕ) ≠ 0 from by norm_num)))
      change Filter.Tendsto (fun r => -(1/2 : ℝ) * Real.exp (-(r ^ 2)))
          Filter.atTop (nhds 0)
      rw [show (0 : ℝ) = -(1/2 : ℝ) * 0 from by ring]
      exact h_exp_tends.const_mul _
    have h_nonneg : ∀ x ∈ Ioi (0 : ℝ),
        0 ≤ x * Real.exp (-(x ^ 2)) :=
      fun x hx => mul_nonneg (le_of_lt hx) (exp_nonneg _)
    have h_cont : ContinuousWithinAt f (Ici 0) 0 := by
      apply ContinuousAt.continuousWithinAt; fun_prop
    have h_deriv_Ioi : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
        (x * Real.exp (-(x ^ 2))) x :=
      fun x hx => h_deriv x (Ioi_subset_Ici_self hx)
    have h_intble := integrableOn_Ioi_deriv_of_nonneg h_cont
      h_deriv_Ioi h_nonneg h_tendsto
    rw [integral_Ioi_of_hasDerivAt_of_tendsto'
      h_deriv h_intble h_tendsto]
    -- Goal: 0 - f 0 = 1/2, i.e., 0 - (-(1/2)*exp(0)) = 1/2
    simp [f, Real.exp_zero]
  -- Evaluate the angular integral
  have h_angular : ∫ θ in Ioo (-Real.pi) Real.pi,
      (if Real.sin (θ + Real.arccos t) > 0 then (1 : ℝ) else -1) *
      (if Real.sin θ > 0 then 1 else -1) =
      4 * Real.arcsin t := by
    -- Convert Ioo to Ioc (differ by measure-0 endpoint)
    rw [← integral_Ioc_eq_integral_Ioo]
    -- Convert Ioc integral to interval integral
    rw [← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    -- Apply angular_integral_identity with β = arccos t
    have hβ_pos : 0 < Real.arccos t :=
      Real.arccos_pos.mpr (by linarith [ht.2])
    have hβ_lt : Real.arccos t < Real.pi :=
      Real.arccos_lt_pi.mpr (by linarith [ht.1])
    rw [angular_integral_identity (Real.arccos t) hβ_pos hβ_lt]
    -- 2π - 4 arccos t = 4 arcsin t
    have := Real.arccos_eq_pi_div_two_sub_arcsin t
    linarith
  -- Combine: 1/2 * (4 arcsin t) = 2 arcsin t
  rw [h_radial, h_angular]; ring

/-! ### Sub-lemma C: Kernel factoring

At real z = t, the kernel exponent is:
  K(x₁,x₂,y₁,y₂,t) = -((x₁²+x₂²) + (y₁²+y₂²) - 2t(x₁y₁+x₂y₂)) / (2(1-t²))
                      = K₁(x₁,y₁,t) + K₂(x₂,y₂,t)
where K_i(s,u,t) = -(s²+u²-2tsu) / (2(1-t²)).

This is because the cross terms x₁y₁ and x₂y₂ are independent.
So exp(K) = exp(K₁)·exp(K₂), and the integrand factors.
-/

/-- The kernel exponent at real t splits as a sum of two independent 2D quadratic forms.
    K(x₁,x₂,y₁,y₂,t) = K₁(x₁,y₁,t) + K₂(x₂,y₂,t) where
    Kᵢ(s,u,t) = -(s²+u²-2tsu) / (1-t²). -/
private theorem kernel_exponent_factors_at_real (x₁ x₂ y₁ y₂ t : ℝ)
    (_ht : (1 : ℝ) - t ^ 2 ≠ 0) :
    kernel_exponent x₁ x₂ y₁ y₂ (↑t : ℂ) =
    (((-(x₁ ^ 2 + y₁ ^ 2 - 2 * t * x₁ * y₁) / (1 - t ^ 2) : ℝ) : ℂ) +
    ((-(x₂ ^ 2 + y₂ ^ 2 - 2 * t * x₂ * y₂) / (1 - t ^ 2) : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_add]
  unfold kernel_exponent
  push_cast
  field_simp
  ring

/-! ### Sub-lemma C: Kernel factoring and 4D integral Fubini decomposition

The 4D integral defining H₀(t) factors into a product of two 2D integrals
after applying Fubini. The key steps are:

1. f_eta 0 depends only on the second component (sign function)
2. The kernel exponent splits as K₁(x₁,y₁,t) + K₂(x₂,y₂,t)
3. The integrand therefore factors as [exp(K₁)] * [sign(x₂)·sign(y₂)·exp(K₂)]
4. By Fubini (with measure rearrangement), the 4D integral is a product

This decomposition requires rearranging the product measure
((ℝ×ℝ)×(ℝ×ℝ), indexed as (x₁,x₂,y₁,y₂)) to ((ℝ×ℝ)×(ℝ×ℝ), indexed as (x₁,y₁,x₂,y₂)),
then applying `integral_prod_mul` to factor the integral into two 2D integrals.
-/

/-- The 4D integral defining H₀(↑t) can be expressed in terms of the
    bivariate Gaussian integral and Sheppard's formula.

    This lemma handles the Fubini decomposition: the integrand factors
    since f_eta 0 depends only on x₂,y₂ and the kernel exponent splits
    as K₁(x₁,y₁) + K₂(x₂,y₂). After rearranging the product measure
    and applying integral_prod_mul, the 4D integral equals
    (1/(2π(1-t²))) * [∫∫ exp(K₁)] * [∫∫ sign(x₂)sign(y₂)exp(K₂)]. -/
private theorem H0_integral_factors (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      ↑(f_eta 0 p.1 * f_eta 0 p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 (↑t : ℂ)) /
      (2 * ↑Real.pi * (1 - (↑t : ℂ) ^ 2)) =
    (↑(∫ q : ℝ × ℝ,
      Real.exp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2))) : ℂ) *
    (↑(∫ q : ℝ × ℝ,
      (if q.1 > 0 then (1 : ℝ) else -1) * (if q.2 > 0 then (1 : ℝ) else -1) *
      Real.exp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2))) : ℂ) /
    (2 * ↑Real.pi * (1 - (↑t : ℂ) ^ 2)) := by
  have ht1 : (1 : ℝ) - t ^ 2 > 0 := by nlinarith [ht.1, ht.2]
  have ht1_ne : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt ht1
  have h_div_ne : (2 : ℂ) * ↑Real.pi * (1 - (↑t : ℂ) ^ 2) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero _) _
    · exact_mod_cast Real.pi_ne_zero
    · rw [show (1 : ℂ) - (↑t : ℂ) ^ 2 = ↑((1 : ℝ) - t ^ 2) from by push_cast; ring]
      exact_mod_cast ht1_ne
  -- It suffices to prove the numerators are equal (the divisors are identical)
  suffices h : ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      ↑(f_eta 0 p.1 * f_eta 0 p.2) * Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 ↑t) =
    ↑(∫ q : ℝ × ℝ, Real.exp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2))) *
    ↑(∫ q : ℝ × ℝ,
      (if q.1 > 0 then (1 : ℝ) else -1) * (if q.2 > 0 then (1 : ℝ) else -1) *
      Real.exp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2))) by
    simp_rw [MeasureTheory.integral_div]
    exact congrArg (· / _) h
  -- Step 1: Replace f_eta 0 with sign function and factor kernel
  simp only [f_eta_zero]
  simp_rw [kernel_exponent_factors_at_real _ _ _ _ _ ht1_ne, Complex.exp_add]
  -- Now the integrand is:
  --   ↑(sign(p.1.2) * sign(p.2.2)) * ↑(rexp(K₁(p.1.1,p.2.1))) * ↑(rexp(K₂(p.1.2,p.2.2)))
  -- which factors as a function of (p.1.1, p.2.1) times a function of (p.1.2, p.2.2).
  -- This is the factoring step that requires rearranging the product space
  -- ((x₁,x₂),(y₁,y₂)) ↔ ((x₁,y₁),(x₂,y₂)) and then applying integral_prod_mul.
  --
  -- The rearrangement σ : ((a,b),(c,d)) ↦ ((a,c),(b,d)) is built from
  -- prodAssoc, prodComm, prodCongr and is measure-preserving.
  -- After applying σ, the integrand factors as f(q.1) * g(q.2) over
  -- (ℝ × ℝ) × (ℝ × ℝ), and integral_prod_mul gives the product.
  --
  -- Formalizing the rearrangement, the complex↔real coercions, and the
  -- integrability conditions requires ~200 lines of technical Lean code.
  -- The mathematical content is routine (Fubini for factored integrands).
  -- Convert cexp ↑r to ↑(rexp r), then ↑a * ↑b to ↑(a * b)
  simp_rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
  -- Convert ∫ p, ↑(f p) to ↑(∫ p, f p) via integral_complex_ofReal
  rw [integral_complex_ofReal]
  -- Both sides are ↑(real_expression); strip the cast
  congr 1
  -- Define the measure-preserving rearrangement σ : ((a,b),(c,d)) ↦ ((a,c),(b,d))
  let σ : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm.trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))
          (MeasurableEquiv.refl ℝ)).trans <|
        (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)))).trans <|
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm
  have hσ : ∀ a b c d : ℝ, σ ((a, b), (c, d)) = ((a, c), (b, d)) := by
    intro a b c d
    simp [σ, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr,
          MeasurableEquiv.prodComm]
  have hσ_vol : MeasurePreserving σ volume volume := by
    change MeasurePreserving
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl ℝ).prodCongr
          (MeasurableEquiv.prodAssoc.symm.trans
            ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)).trans
              MeasurableEquiv.prodAssoc))).trans
          MeasurableEquiv.prodAssoc.symm))
      volume volume
    apply MeasurePreserving.trans volume_preserving_prodAssoc
    apply MeasurePreserving.trans _ volume_preserving_prodAssoc.symm
    exact (MeasurePreserving.id volume).prod
      (MeasurePreserving.trans volume_preserving_prodAssoc.symm
        (MeasurePreserving.trans
          ((Measure.measurePreserving_swap (α := ℝ) (β := ℝ)).prod
            (MeasurePreserving.id volume))
          volume_preserving_prodAssoc))
  -- Rearrange the 4D integral via σ
  rw [← hσ_vol.integral_comp σ.measurableEmbedding]
  -- After σ, simplify (σ x).i.j to concrete coordinates
  -- σ ((a,b),(c,d)) = ((a,c),(b,d)), so the integrand becomes
  --   sign(c)·sign(d)·exp(K(a,b))·exp(K(c,d)) = exp(K(a,b))·(sign(c)·sign(d)·exp(K(c,d)))
  -- which factors as f(x.1) * g(x.2) over (ℝ × ℝ) × (ℝ × ℝ)
  have h_integrand : ∀ x : (ℝ × ℝ) × (ℝ × ℝ),
      ((if (σ x).1.2 > 0 then (1:ℝ) else -1) * if (σ x).2.2 > 0 then (1:ℝ) else -1) *
        (rexp (-((σ x).1.1 ^ 2 + (σ x).2.1 ^ 2 - 2 * t * (σ x).1.1 * (σ x).2.1) /
          (1 - t ^ 2)) *
          rexp (-((σ x).1.2 ^ 2 + (σ x).2.2 ^ 2 - 2 * t * (σ x).1.2 * (σ x).2.2) /
          (1 - t ^ 2))) =
      rexp (-(x.1.1 ^ 2 + x.1.2 ^ 2 - 2 * t * x.1.1 * x.1.2) / (1 - t ^ 2)) *
        (((if x.2.1 > 0 then (1:ℝ) else -1) * if x.2.2 > 0 then (1:ℝ) else -1) *
          rexp (-(x.2.1 ^ 2 + x.2.2 ^ 2 - 2 * t * x.2.1 * x.2.2) / (1 - t ^ 2))) := by
    intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [hσ]; ring
  simp_rw [h_integrand]
  -- Apply Fubini: ∫ f(x.1) * g(x.2) = (∫ f) * (∫ g)
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun q : ℝ × ℝ => rexp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2)))
    (fun q : ℝ × ℝ => ((if q.1 > 0 then (1:ℝ) else -1) * if q.2 > 0 then (1:ℝ) else -1) *
      rexp (-(q.1 ^ 2 + q.2 ^ 2 - 2 * t * q.1 * q.2) / (1 - t ^ 2)))

/-- **Direct computation**: H₀(↑t) = ↑(arcsin t) for real t ∈ (-1,1).

    Proof: Expand H₀ using the integral definition, factor the 4D integral
    via `H0_integral_factors`, evaluate via `bivariate_gaussian_integral`
    and `sheppard_median_dichotomy`, and simplify algebraically.

    H₀(t) = (1/4) · (1/(2π(1-t²))) · 2π√(1-t²) · 4√(1-t²)·arcsin(t)
           = 1 · arcsin(t) = arcsin(t) -/
private theorem H0_eq_arcsin_direct (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    H0 (↑t : ℂ) = ↑(Real.arcsin t) := by
  have ht1 : (1 : ℝ) - t ^ 2 > 0 := by nlinarith [ht.1, ht.2]
  have ht1_ne : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt ht1
  -- Step 1: Unfold H0 = H_eta 0 and apply f_eta_zero, kernel factoring
  unfold H0 H_eta
  -- Step 2: Apply the Fubini factoring lemma
  rw [H0_integral_factors t ht]
  -- Step 3: Evaluate the two 2D integrals
  rw [bivariate_gaussian_integral t ht]
  rw [sheppard_median_dichotomy t ht]
  -- Step 4: Algebraic simplification
  -- Goal: ((↑(π√(1-t²))) * ↑(2√(1-t²)·arcsin(t))) / (2π(1-t²)) = ↑(arcsin t)
  push_cast
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hsqrt_pos : Real.sqrt (1 - t ^ 2) > 0 := Real.sqrt_pos.mpr ht1
  have hsqrt_ne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt ht1.le
  -- ↑(√(1-t²)) ^ 2 = ↑(1 - t²) as complex
  have hsqrt_sq_complex : (↑(Real.sqrt (1 - t ^ 2)) : ℂ) ^ 2 = ↑((1 : ℝ) - t ^ 2) := by
    rw [← Complex.ofReal_pow]
    exact congrArg Complex.ofReal hsqrt_sq
  -- (1 - ↑t²) as complex is nonzero
  have h1t2_ne : (1 : ℂ) - (↑t : ℂ) ^ 2 ≠ 0 := by
    rw [show (1 : ℂ) - (↑t : ℂ) ^ 2 = ↑((1 : ℝ) - t ^ 2) from by push_cast; ring]
    exact_mod_cast ht1_ne
  field_simp
  ring_nf
  rw [hsqrt_sq_complex]
  push_cast
  have h1t2_ne' : (1 : ℂ) - ↑(t ^ 2) ≠ 0 := by
    rw [show (1 : ℂ) - ↑(t ^ 2) = ↑((1 : ℝ) - t ^ 2) from by push_cast; ring]
    exact_mod_cast ht1_ne
  field_simp

/-! ## Main theorem: H₀ = arcsin (from attempt2) -/

/-- H₀(↑x) = ↑(arcsin x) for real x with |x| < 1.

    This is proved by direct evaluation of the 4D Gaussian integral defining H₀.
    The integral factors by Fubini into a bivariate Gaussian times Sheppard's
    sign-correlation integral. -/
theorem sheppard_H0_eq_arcsin_v2 (x : ℝ) (hx : |x| < 1) :
    H0 (↑x) = ↑(Real.arcsin x) := by
  have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo]; constructor <;> linarith [neg_abs_le x, le_abs_self x]
  exact H0_eq_arcsin_direct x hx_mem

/-! ## Derive the derivative from H₀ = arcsin (from attempt2) -/

/-- The derivative of H₀ restricted to real inputs equals 1/√(1-t²).
    This follows from sheppard_H0_eq_arcsin_v2 via EventuallyEq. -/
theorem H0_deriv_real_eq_inv_sqrt_v2 (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => H0 (↑s : ℂ))
      (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t := by
  -- Step 1: H₀(↑s) = ↑(arcsin s) near t, by sheppard_H0_eq_arcsin_v2
  have h_eq : (fun s : ℝ => H0 (↑s : ℂ)) =ᶠ[nhds t]
      (fun s : ℝ => (↑(Real.arcsin s) : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (-1 : ℝ) 1, Ioo_mem_nhds ht.1 ht.2, ?_⟩
    intro x hx
    exact sheppard_H0_eq_arcsin_v2 x
      (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  -- Step 2: arcsin has the right derivative (from Mathlib)
  have h_arcsin : HasDerivAt (fun s : ℝ => (↑(Real.arcsin s) : ℂ))
      (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t :=
    (Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)).ofReal_comp
  -- Step 3: Transfer via EventuallyEq
  exact h_eq.hasDerivAt_iff.mpr h_arcsin

/-!
## H₀ = arcsin via ODE uniqueness

### Proof outline

The proof that H₀(x) = arcsin(x) for real x with |x| < 1 is established via
ODE uniqueness. The key computational input is the derivative of H₀ at real points.

**Step 1** (f₀ = sign): When η = 0, f₀(x₁,x₂) = sign(x₂), so the product
  f₀(x)·f₀(y) = sign(x₂)·sign(y₂) depends only on x₂, y₂.

**Step 2** (Factor the 4D integral): With z = x real, the kernel exponent is real
  and symmetric. The substitution u₁ = (x₁+y₁)/√2, v₁ = (x₁-y₁)/√2 diagonalizes
  the x₁,y₁ quadratic form; the u₁,v₁ Gaussian integrals evaluate to standard
  factors via `integral_gaussian` from Mathlib.

**Step 3** (Sheppard's formula): The remaining 2D integral over (x₂, y₂) with
  the sign function and a bivariate Gaussian kernel evaluates to arcsin(x):
    (1/(2π(1-x²))) ∫∫ sign(s)·sign(t)·exp(-(s²+t²-2x·s·t)/(2(1-x²))) ds dt
      = (2/π)·arcsin(x)
  This is Sheppard's median dichotomy formula (1899), provable by completing
  the square and using polar coordinates. Together with the normalization
  prefactor 1/(2π), this gives H₀(x) = arcsin(x).

**Step 4** (ODE characterization): Differentiating H₀(x) via the same factoring
  shows H₀'(x) = 1/√(1-x²). Since arcsin'(x) = 1/√(1-x²) and both vanish at 0,
  ODE uniqueness (Picard-Lindelof/Gronwall) gives H₀ = arcsin on (-1,1).
-/

/-- The derivative of H₀ restricted to real inputs equals 1/√(1-t²).

    This is the key computational input for Sheppard's formula. It requires
    differentiating the 4D Gaussian integral defining H₀ under the integral sign,
    factoring the (x₁,y₁) variables via diagonalization, and evaluating the
    remaining (x₂,y₂) integral via Sheppard's median dichotomy formula.

    The computation involves:
    1. Leibniz integral rule (differentiation under the integral sign)
    2. Fubini's theorem to factor the 4D integral
    3. Gaussian integral evaluation for the (x₁,y₁) variables
    4. Sheppard's formula for the (x₂,y₂) bivariate sign-Gaussian integral
    These are deep measure-theoretic computations (~200 lines). -/
private theorem H0_deriv_real_eq_inv_sqrt (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => H0 (↑s : ℂ))
      (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t :=
  H0_deriv_real_eq_inv_sqrt_v2 t ht

/-- **Sheppard's median dichotomy formula** (1899): H₀(↑x) = ↑(arcsin x) for real x
    with |x| < 1.

    At η = 0, f₀(x₁,x₂) = sign(x₂), so the 4D Gaussian integral defining H₀ factors:
    1. The (x₁,y₁) quadratic form diagonalizes via u = (x₁+y₁)/√2, v = (x₁-y₁)/√2,
       yielding standard Gaussian normalization 2π√(1-t²) (via `integral_cexp_quadratic`).
    2. The (x₂,y₂) part computes E[sign(X₂)·sign(Y₂)] for bivariate Gaussians with
       correlation t. By Sheppard's formula (polar coordinate computation),
       this expectation equals (2/π)·arcsin(t).
    3. Combined with the outer factor 1/4 and the normalization from step 1,
       the full integral evaluates to arcsin(t).

    The proof uses ODE uniqueness (Picard-Lindelöf): both H₀ and arcsin satisfy
    f'(t) = 1/√(1-t²) on (-1,1) with f(0) = 0, and the vector field is independent
    of y (hence trivially Lipschitz with K=0), so they must agree. -/
private theorem sheppard_H0_eq_arcsin (x : ℝ) (hx : |x| < 1) :
    H0 (↑x) = ↑(Real.arcsin x) := by
  -- Step 1: x ∈ Ioo (-1) 1
  have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo]; constructor <;> linarith [neg_abs_le x, le_abs_self x]
  -- Step 2: t ↦ ↑(arcsin t) has derivative ↑(1/√(1-t²)) (from Mathlib)
  have arcsin_deriv : ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (↑(Real.arcsin s) : ℂ))
        (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t := by
    intro t ht
    exact (Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)).ofReal_comp
  -- Step 3: Both agree at 0
  have h_at_zero :
      (fun s : ℝ => H0 (↑s : ℂ)) 0 =
      (fun s : ℝ => (↑(Real.arcsin s) : ℂ)) 0 := by
    simp [H0_zero, Real.arcsin_zero]
  -- Step 4: Apply ODE uniqueness (Picard-Lindelöf/Gronwall)
  -- The vector field v(t, y) = ↑(1/√(1-t²)) is independent of y,
  -- hence trivially Lipschitz with constant K = 0.
  have h_eq := ODE_solution_unique_of_mem_Ioo
    (v := fun t (_ : ℂ) => (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ))
    (s := fun _ => Set.univ) (K := 0)
    (fun t _ x _ y _ => by simp)
    (⟨neg_lt_zero.mpr one_pos, one_pos⟩ : (0 : ℝ) ∈ Set.Ioo (-1) 1)
    (fun t ht => ⟨H0_deriv_real_eq_inv_sqrt t ht, trivial⟩)
    (fun t ht => ⟨arcsin_deriv t ht, trivial⟩)
    h_at_zero
  exact h_eq hx_mem


/-- The derivative of H₀ at a real point x with |x| < 1 is 1/√(1-x²).

    **Proof strategy**: Rather than differentiating the 4D Gaussian integral directly,
    we use `sheppard_H0_eq_arcsin` (which evaluates the integral as arcsin) together
    with the analyticity of H₀ on S (Lemma 4.2).

    1. H₀ is analytic on S → differentiable at ↑t → `HasDerivAt H0 (deriv H0 ↑t) ↑t`
    2. By `HasDerivAt.comp_ofReal`, the real function x ↦ H₀(↑x) has derivative
       `deriv H0 ↑t` at t.
    3. By `sheppard_H0_eq_arcsin`, x ↦ H₀(↑x) agrees with x ↦ ↑(arcsin x) on (-1,1).
    4. By `Real.hasDerivAt_arcsin` (Mathlib), x ↦ ↑(arcsin x) has derivative
       ↑(1/√(1-t²)) at t.
    5. Since the functions agree near t, `Filter.EventuallyEq.hasDerivAt_iff` transfers
       the `HasDerivAt`, and uniqueness of derivatives gives `deriv H0 ↑t = ↑(1/√(1-t²))`. -/
theorem H0_hasDerivAt_real (t : ℝ) (ht : |t| < 1) :
    HasDerivAt H0 (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) (↑t : ℂ) := by
  -- Step 1: H₀ is analytic on S, hence differentiable at ↑t ∈ S
  have ht_mem : (↑t : ℂ) ∈ S := by
    change |Complex.re ↑t| < 1; rwa [Complex.ofReal_re]
  have h_diff : DifferentiableAt ℂ H0 (↑t : ℂ) :=
    (H_eta_analyticOnNhd 0).differentiableOn.differentiableAt (S_isOpen.mem_nhds ht_mem)
  have h_hda := h_diff.hasDerivAt
  -- Step 2: The real function x ↦ H₀(↑x) has derivative deriv H₀ ↑t at t
  have h_real_H0 : HasDerivAt (fun x : ℝ => H0 (↑x : ℂ)) (deriv H0 (↑t : ℂ)) t :=
    h_hda.comp_ofReal
  -- Step 3: H₀(↑x) = ↑(arcsin x) on (-1, 1), so the functions agree near t
  have h_eq : (fun x : ℝ => H0 (↑x : ℂ)) =ᶠ[nhds t]
      (fun x : ℝ => (↑(Real.arcsin x) : ℂ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Ioo (-1) 1,
      Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t]),
      fun x hx => sheppard_H0_eq_arcsin x
        (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)⟩
  -- Step 4: Transfer the derivative via the eventual equality
  have h_arcsin_deriv : HasDerivAt (fun x : ℝ => (↑(Real.arcsin x) : ℂ))
      (deriv H0 (↑t : ℂ)) t :=
    h_eq.hasDerivAt_iff.mp h_real_H0
  -- Step 5: Mathlib gives the derivative of arcsin
  have h_arcsin_std : HasDerivAt (fun x : ℝ => (↑(Real.arcsin x) : ℂ))
      (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t :=
    (Real.hasDerivAt_arcsin (by linarith [neg_abs_le t] : t ≠ -1)
      (by linarith [le_abs_self t] : t ≠ 1)).ofReal_comp
  -- Uniqueness of derivatives: deriv H₀ ↑t = ↑(1/√(1-t²))
  rwa [← h_arcsin_deriv.unique h_arcsin_std]

/-- H₀ agrees with arcsin on real inputs in (-1, 1).

    This is the foundational identity for the Grothendieck inequality proof.
    The proof uses ODE uniqueness (Picard-Lindelof): both H₀ and arcsin satisfy
      f'(t) = 1/√(1-t²) on (-1,1) with f(0) = 0,
    so they must agree. The vector field v(t,y) = 1/√(1-t²) is independent of y,
    hence trivially Lipschitz (K=0), making the uniqueness theorem applicable.

    All downstream results (sin_H0_eq, H0_sin_eq, H0_deriv, etc.) follow from
    this theorem via the identity theorem and chain rule. -/
theorem H0_eq_arcsin_real (x : ℝ) (hx : |x| < 1) :
    H0 (↑x) = ↑(Real.arcsin x) := by
  -- Both t ↦ H₀(↑t) and t ↦ ↑(arcsin t) satisfy the ODE
  --   f'(t) = ↑(1/√(1-t²)) on (-1,1) with f(0) = 0.
  -- By Picard-Lindelof uniqueness (ODE_solution_unique_of_mem_Ioo), they agree.
  have hx_mem : x ∈ Ioo (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo]; constructor <;> linarith [neg_abs_le x, le_abs_self x]
  -- Step 1: t ↦ H₀(↑t) has derivative ↑(1/√(1-t²)) via chain rule
  have h_H0_deriv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => H0 (↑s : ℂ))
        (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t := by
    intro t ht
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- ofReal has derivative 1
    have h_ofReal : HasDerivAt (fun s : ℝ => (↑s : ℂ)) 1 t := by
      have h := Complex.ofRealCLM.hasDerivAt (x := t)
      have h2 : Complex.ofRealCLM (1 : ℝ) = (1 : ℂ) := by
        simp [Complex.ofRealCLM, Complex.ofReal_one]
      rw [h2] at h; exact h
    -- Chain rule: (H₀ ∘ ofReal)'(t) = H₀'(↑t) · 1 = H₀'(↑t)
    have h_comp := (H0_hasDerivAt_real t ht_abs).comp t h_ofReal
    simp only [Function.comp_def] at h_comp
    convert h_comp using 1
    push_cast; ring
  -- Step 2: t ↦ ↑(arcsin t) has the same derivative (from Mathlib)
  have h_arcsin_deriv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (↑(Real.arcsin s) : ℂ))
        (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ) t := by
    intro t ht
    exact (Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)).ofReal_comp
  -- Step 3: Both agree at 0
  have h_at_zero :
      (fun s : ℝ => H0 (↑s : ℂ)) 0 =
      (fun s : ℝ => (↑(Real.arcsin s) : ℂ)) 0 := by
    simp [H0_zero, Real.arcsin_zero]
  -- Step 4: Apply ODE uniqueness (Gronwall/Picard-Lindelof)
  -- v(t, y) = ↑(1/√(1-t²)) is independent of y, so Lipschitz with K = 0
  have h_eq := ODE_solution_unique_of_mem_Ioo
    (v := fun t (_ : ℂ) => (↑(1 / Real.sqrt (1 - t ^ 2)) : ℂ))
    (s := fun _ => Set.univ) (K := 0)
    (fun t _ x _ y _ => by simp)
    (⟨neg_lt_zero.mpr one_pos, one_pos⟩ : (0 : ℝ) ∈ Ioo (-1) 1)
    (fun t ht => ⟨h_H0_deriv t ht, trivial⟩)
    (fun t ht => ⟨h_arcsin_deriv t ht, trivial⟩)
    h_at_zero
  exact h_eq hx_mem

/-!
## Derived properties

These follow from the core properties above via the identity theorem and chain rule.
-/

-- S is convex (needed for the identity theorem)
theorem S_convex : Convex ℝ S := by
  intro x hx y hy a b ha hb hab
  simp only [S, mem_setOf_eq] at *
  show |((a : ℂ) • x + (b : ℂ) • y).re| < 1
  have hre : ((a : ℂ) • x + (b : ℂ) • y).re = a * x.re + b * y.re := by
    simp [Complex.add_re]
  rw [hre]
  have h1 : |a * x.re + b * y.re| ≤ a * |x.re| + b * |y.re| := by
    calc |a * x.re + b * y.re|
        ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
      _ = a * |x.re| + b * |y.re| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 : a * |x.re| + b * |y.re| < 1 := by
    have hax : a * |x.re| ≤ a * 1 := mul_le_mul_of_nonneg_left hx.le ha
    have hby : b * |y.re| ≤ b * 1 := mul_le_mul_of_nonneg_left hy.le hb
    by_cases ha0 : a = 0
    · subst ha0; simp at hab ⊢; rw [hab]; simpa using hy
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have : a * |x.re| < a * 1 := mul_lt_mul_of_pos_left hx ha'
      linarith
  linarith

theorem S_isPreconnected : IsPreconnected S := S_convex.isPreconnected

/-- sin(H₀(z)) = z for z ∈ S.
    This is the key identity that makes H₀ the inverse of sin on S. -/
theorem sin_H0_eq (z : ℂ) (hz : z ∈ S) : Complex.sin (H0 z) = z := by
  -- Use the identity theorem: sin ∘ H₀ - id is analytic on S and vanishes on (-1,1)
  -- Step 1: Analyticity of sin ∘ H₀
  have h_sin_analytic : AnalyticOnNhd ℂ Complex.sin Set.univ :=
    fun z _ => Complex.differentiable_sin.analyticAt z
  have h_comp_analytic : AnalyticOnNhd ℂ (fun z => Complex.sin (H0 z)) S := by
    apply AnalyticOnNhd.comp h_sin_analytic H0_analyticOnNhd
    exact fun _ _ => Set.mem_univ _
  -- The function g(z) = sin(H₀(z)) - z is analytic on S
  have h_g_analytic : AnalyticOnNhd ℂ (fun z => Complex.sin (H0 z) - z) S :=
    h_comp_analytic.sub (analyticOnNhd_id.mono (fun _ _ => trivial))
  -- Step 2: g vanishes frequently near 0
  -- We show g(x) = 0 for real x ∈ (-1,1) using H0_eq_arcsin_real and sin_arcsin
  have h_zero_on_real : ∀ (x : ℝ), |x| < 1 →
      Complex.sin (H0 (↑x)) - (↑x : ℂ) = 0 := by
    intro x hx
    rw [H0_eq_arcsin_real x hx]
    have hx1 : -1 ≤ x := by linarith [neg_abs_le x]
    have hx2 : x ≤ 1 := by linarith [le_abs_self x]
    rw [sub_eq_zero]
    rw [← Complex.ofReal_sin]
    congr 1
    exact Real.sin_arcsin hx1 hx2
  -- There are points accumulating to 0 in S \ {0} where g vanishes
  have h_closure : (0 : ℂ) ∈
      closure ({z | Complex.sin (H0 z) - z = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set x : ℝ := min (ε / 2) (1 / 2) with hx_def
    have hx_pos : 0 < x := lt_min (by linarith) (by norm_num)
    have hx_lt_eps : (x : ℝ) < ε := by
      calc x ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    have hx_lt_one : |x| < 1 := by
      rw [abs_of_pos hx_pos]
      calc x ≤ 1 / 2 := min_le_right _ _
        _ < 1 := by norm_num
    refine ⟨(↑x : ℂ), ?_, ?_⟩
    · constructor
      · exact h_zero_on_real x hx_lt_one
      · simp [Complex.ext_iff]
        exact ne_of_gt hx_pos
    · simp [Complex.dist_eq, Complex.norm_real, abs_of_pos hx_pos]
      exact hx_lt_eps
  have h_freq : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      (fun z => Complex.sin (H0 z) - z) z = 0 :=
    mem_closure_ne_iff_frequently_within.mp h_closure
  -- Step 3: Apply identity theorem
  have h_eq := h_g_analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    S_isPreconnected zero_mem_S h_freq
  have := h_eq hz
  simp [Pi.zero_apply] at this
  exact sub_eq_zero.mp this

/-- The domain where H₀ ∘ sin is defined: strip |Re z| < π/2 intersected
    with sin⁻¹(S) -/
private def D : Set ℂ :=
  {z : ℂ | |z.re| < Real.pi / 2} ∩ Complex.sin ⁻¹' S

private theorem D_isOpen : IsOpen D := by
  apply IsOpen.inter
  · have : {z : ℂ | |z.re| < Real.pi / 2} =
        {z : ℂ | z.re < Real.pi / 2} ∩
        {z : ℂ | -(Real.pi / 2) < z.re} := by
      ext z; simp [abs_lt, and_comm]
    rw [this]
    exact IsOpen.inter
      (isOpen_lt (continuous_re) continuous_const)
      (isOpen_lt continuous_const continuous_re)
  · exact S_isOpen.preimage Complex.continuous_sin

private theorem zero_mem_D : (0 : ℂ) ∈ D := by
  refine ⟨?_, ?_⟩
  · simp [abs_of_pos (div_pos Real.pi_pos two_pos), Real.pi_pos]
  · simp [S, Complex.sin_zero]

private theorem D_isPreconnected : IsPreconnected D := by
  -- Key helper: Re(sin z) = sin(Re z) * cosh(Im z)
  have sin_re_eq : ∀ (z : ℂ),
      (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    intro z
    have h1 : z = ↑z.re + ↑z.im * I := (Complex.re_add_im z).symm
    calc (Complex.sin z).re
        = (Complex.sin (↑z.re + ↑z.im * I)).re := by rw [← h1]
      _ = Real.sin z.re * Real.cosh z.im := by
          rw [Complex.sin_add_mul_I]
          simp [Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
                Complex.cos_ofReal_im, Complex.sinh_ofReal_im]
  suffices h : StarConvex ℝ (0 : ℂ) D by
    exact (IsPathConnected.isConnected
      (h.isPathConnected zero_mem_D)).isPreconnected
  intro y hy a b ha hb hab
  simp only [smul_zero, zero_add]
  simp only [D, mem_inter_iff, mem_setOf_eq, mem_preimage] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hb1 : b ≤ 1 := by linarith
  have hby_re : (b • y).re = b * y.re := by simp
  have hby_im : (b • y).im = b * y.im := by simp
  refine ⟨?_, ?_⟩
  -- Part 1: |(b • y).re| < π / 2
  case refine_1 =>
    rw [hby_re, abs_mul, abs_of_nonneg hb]
    calc b * |y.re|
        ≤ 1 * |y.re| :=
          mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ = |y.re| := one_mul _
      _ < π / 2 := hy1
  -- Part 2: Complex.sin (b • y) ∈ S
  case refine_2 =>
    simp only [S, mem_setOf_eq] at hy2 ⊢
    rw [sin_re_eq, hby_re, hby_im]
    rw [sin_re_eq] at hy2
    rw [abs_mul, abs_of_nonneg (Real.cosh_pos _).le]
    rw [abs_mul, abs_of_nonneg (Real.cosh_pos _).le] at hy2
    -- cosh bound: cosh(b * y.im) ≤ cosh(y.im)
    have hcosh_le : Real.cosh (b * y.im) ≤ Real.cosh y.im :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_mul, abs_of_nonneg hb]
        exact mul_le_of_le_one_left (abs_nonneg _) hb1)
    -- sin bound: |sin(b * y.re)| ≤ |sin(y.re)|
    have hsin_le : |Real.sin (b * y.re)| ≤ |Real.sin y.re| := by
      rcases le_or_gt 0 y.re with hyre | hyre
      · -- y.re ≥ 0
        have h1 : 0 ≤ b * y.re := mul_nonneg hb hyre
        have h2 : b * y.re ≤ y.re := by nlinarith
        rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h1
              (by linarith [le_abs_self y.re]))]
        rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hyre
              (by linarith [le_abs_self y.re]))]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [pi_pos])
          (by linarith [le_abs_self y.re]) h2
      · -- y.re < 0
        have h1 : b * y.re ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hb hyre.le
        have h2 : y.re ≤ b * y.re := by nlinarith
        rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h1
              (by linarith [neg_abs_le y.re]))]
        rw [abs_of_nonpos
              (Real.sin_nonpos_of_nonpos_of_neg_pi_le hyre.le
              (by linarith [neg_abs_le y.re]))]
        linarith [Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [neg_abs_le y.re])
          (by linarith [pi_pos] : b * y.re ≤ π / 2) h2]
    -- Combine the bounds
    calc |Real.sin (b * y.re)| * Real.cosh (b * y.im)
        ≤ |Real.sin y.re| * Real.cosh (b * y.im) :=
          mul_le_mul_of_nonneg_right hsin_le (Real.cosh_pos _).le
      _ ≤ |Real.sin y.re| * Real.cosh y.im :=
          mul_le_mul_of_nonneg_left hcosh_le (abs_nonneg _)
      _ < 1 := hy2

/-- H₀(sin(z)) = z for z in the appropriate preimage of S under sin. -/
theorem H0_sin_eq (z : ℂ) (hz : |z.re| < Real.pi / 2)
    (hz' : Complex.sin z ∈ S) : H0 (Complex.sin z) = z := by
  have hz_in_D : z ∈ D := by
    refine ⟨?_, hz'⟩
    simp [abs_lt] at hz ⊢; exact ⟨by linarith, by linarith⟩
  -- H₀ ∘ sin is analytic on D
  have h_comp : AnalyticOnNhd ℂ (fun z => H0 (Complex.sin z)) D := by
    have h_sin : AnalyticOnNhd ℂ Complex.sin Set.univ :=
      fun z _ => Complex.differentiable_sin.analyticAt z
    have h_sin_D : AnalyticOnNhd ℂ Complex.sin D :=
      h_sin.mono (fun _ _ => Set.mem_univ _)
    apply AnalyticOnNhd.comp H0_analyticOnNhd h_sin_D
    exact fun z hz => hz.2
  -- g = H₀ ∘ sin - id is analytic on D
  have h_g : AnalyticOnNhd ℂ (fun z => H0 (Complex.sin z) - z) D :=
    h_comp.sub ((analyticOnNhd_id).mono (fun _ _ => trivial))
  -- g vanishes on real x ∈ (-π/2, π/2)
  have h_zero_real : ∀ (x : ℝ), |x| < Real.pi / 2 →
      H0 (Complex.sin (↑x)) - (↑x : ℂ) = 0 := by
    intro x hx
    have hsin_bound : |Real.sin x| < 1 := by
      have hx' : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.mem_Ioo]
        constructor <;> linarith [neg_abs_le x, le_abs_self x]
      have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hx'
      rw [abs_lt]
      constructor
      · by_contra h; push_neg at h
        have h1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (Real.cos x),
                   sq_nonneg (Real.sin x + 1)]
      · by_contra h; push_neg at h
        have h1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (Real.cos x),
                   sq_nonneg (Real.sin x - 1)]
    rw [← Complex.ofReal_sin,
        H0_eq_arcsin_real (Real.sin x) hsin_bound]
    simp [sub_eq_zero]
    have hx1 : -(Real.pi / 2) ≤ x := by linarith [neg_abs_le x]
    have hx2 : x ≤ Real.pi / 2 := by linarith [le_abs_self x]
    exact_mod_cast Real.arcsin_sin hx1 hx2
  -- 0 is an accumulation point of zeros
  have h_closure : (0 : ℂ) ∈
      closure ({z | H0 (Complex.sin z) - z = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set x : ℝ := min (ε / 2) (1 / 2)
    have hx_pos : 0 < x := lt_min (by linarith) (by norm_num)
    have hx_lt_pi2 : |x| < Real.pi / 2 := by
      rw [abs_of_pos hx_pos]
      calc x ≤ 1 / 2 := min_le_right _ _
        _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
    refine ⟨(↑x : ℂ), ?_, ?_⟩
    · exact ⟨h_zero_real x hx_lt_pi2,
        by simp [Complex.ext_iff]; exact ne_of_gt hx_pos⟩
    · simp [Complex.dist_eq, Complex.norm_real,
            abs_of_pos hx_pos]
      calc x ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
  have h_freq : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      (fun z => H0 (Complex.sin z) - z) z = 0 :=
    mem_closure_ne_iff_frequently_within.mp h_closure
  -- Apply identity theorem
  have h_eq := h_g.eqOn_zero_of_preconnected_of_frequently_eq_zero
    D_isPreconnected zero_mem_D h_freq
  have := h_eq hz_in_D
  simp at this
  exact sub_eq_zero.mp this

/-- H₀'(z) = 1/√(1-z²) on S, i.e., H₀ has the same derivative as arcsin.
    This follows from differentiating sin(H₀(z)) = z via the chain rule. -/
theorem H0_deriv (z : ℂ) (hz : z ∈ S) :
    HasDerivAt H0 (1 / (1 - z ^ 2) ^ (1/2 : ℂ)) z := by
  -- Step 1: H₀ is differentiable at z (from analyticity on S)
  have h_diff_H0 : DifferentiableAt ℂ H0 z :=
    H0_analyticOnNhd.differentiableOn.differentiableAt
      (S_isOpen.mem_nhds hz)
  -- Step 2: sin ∘ H₀ = id on S
  have h_evt : (Complex.sin ∘ H0) =ᶠ[nhds z] id :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨S, S_isOpen.mem_nhds hz, fun w hw => sin_H0_eq w hw⟩
  -- Step 3: Differentiate sin(H₀(z)) = z
  have h1 : deriv (Complex.sin ∘ H0) z = 1 := by
    rw [h_evt.deriv_eq, deriv_id']
  have h2 : deriv (Complex.sin ∘ H0) z =
      Complex.cos (H0 z) * deriv H0 z :=
    ((Complex.hasDerivAt_sin (H0 z)).comp z
      h_diff_H0.hasDerivAt).deriv
  have h_cos_mul : Complex.cos (H0 z) * deriv H0 z = 1 := by
    rw [← h2, h1]
  have h_cos_ne : Complex.cos (H0 z) ≠ 0 :=
    left_ne_zero_of_mul_eq_one h_cos_mul
  have h_sin_eq : Complex.sin (H0 z) = z := sin_H0_eq z hz
  have h_cos_sq : Complex.cos (H0 z) ^ 2 = 1 - z ^ 2 := by
    have := Complex.cos_sq' (H0 z)
    rw [h_sin_eq] at this; exact this
  -- Step 4: suffices to show deriv value
  suffices h : deriv H0 z = 1 / (1 - z ^ 2) ^ (1 / 2 : ℂ) by
    rw [← h]; exact h_diff_H0.hasDerivAt
  -- Step 5: H₀'(z) = 1/cos(H₀(z))
  have h_deriv_val : deriv H0 z = 1 / Complex.cos (H0 z) := by
    rw [one_div]
    exact eq_inv_of_mul_eq_one_left
      (by rw [mul_comm]; exact h_cos_mul)
  rw [h_deriv_val]
  congr 1
  -- Step 6: cos(H₀(z)) = (1-z²)^(1/2)
  have h_half : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [h_half, ← h_cos_sq]
  -- Step 7: Show 0 < Re(cos(H₀(z))) via IVT argument
  have re_one_sub_sq (w : ℂ) (hw : w ∈ S) :
      0 < (1 - w ^ 2).re := by
    have hw_mem : |w.re| < 1 := hw
    have : (1 - w ^ 2).re =
        1 - w.re * w.re + w.im * w.im := by
      simp [Complex.sub_re, Complex.one_re,
            Complex.mul_re, Complex.add_re,
            Complex.ofReal_re, Complex.ofReal_im, sq]
      ring
    rw [this]
    have ⟨_, _⟩ := abs_lt.mp hw_mem
    nlinarith [mul_self_nonneg w.im]
  -- Re(cos(H₀(w))) ≠ 0 for all w ∈ S
  have h_re_ne_zero_all :
      ∀ w ∈ S, (Complex.cos (H0 w)).re ≠ 0 := by
    intro w hw
    have h_dw : DifferentiableAt ℂ H0 w :=
      H0_analyticOnNhd.differentiableOn.differentiableAt
        (S_isOpen.mem_nhds hw)
    have h_evtw : (Complex.sin ∘ H0) =ᶠ[nhds w] id :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨S, S_isOpen.mem_nhds hw,
         fun u hu => sin_H0_eq u hu⟩
    have h1w : deriv (Complex.sin ∘ H0) w = 1 := by
      rw [h_evtw.deriv_eq, deriv_id']
    have h2w := ((Complex.hasDerivAt_sin (H0 w)).comp w
      h_dw.hasDerivAt).deriv
    have h_cmw : Complex.cos (H0 w) * deriv H0 w = 1 := by
      rw [← h2w, h1w]
    have h_sw : Complex.sin (H0 w) = w := sin_H0_eq w hw
    have h_csw : Complex.cos (H0 w) ^ 2 = 1 - w ^ 2 := by
      have := Complex.cos_sq' (H0 w)
      rw [h_sw] at this; exact this
    intro h_eq
    have h_csw_re : (Complex.cos (H0 w) ^ 2).re =
        (Complex.cos (H0 w)).re * (Complex.cos (H0 w)).re -
        (Complex.cos (H0 w)).im *
          (Complex.cos (H0 w)).im := by
      simp [Complex.mul_re, sq]
    rw [h_csw] at h_csw_re
    rw [h_eq] at h_csw_re
    simp only [zero_mul, zero_sub] at h_csw_re
    have := re_one_sub_sq w hw
    linarith [mul_self_nonneg (Complex.cos (H0 w)).im]
  -- Continuity of Re ∘ cos ∘ H₀ on S
  have h_cont :
      ContinuousOn (fun w => (Complex.cos (H0 w)).re) S := by
    apply ContinuousOn.comp (f := Complex.cos ∘ H0)
      Complex.continuous_re.continuousOn
    · exact (Complex.differentiable_cos.comp_differentiableOn
        (H0_analyticOnNhd.differentiableOn)).continuousOn
    · exact fun _ _ => Set.mem_univ _
  -- Value at 0: Re(cos(H₀(0))) = 1 > 0
  have h_val_zero : (Complex.cos (H0 0)).re = 1 := by
    rw [H0_zero, Complex.cos_zero]; simp
  have h_re_pos : 0 < (Complex.cos (H0 z)).re := by
    by_contra h_not_pos
    push_neg at h_not_pos
    have h_ne : (Complex.cos (H0 z)).re ≠ 0 :=
      h_re_ne_zero_all z hz
    have h_lt : (Complex.cos (H0 z)).re < 0 :=
      lt_of_le_of_ne h_not_pos h_ne
    have h_ivt :=
      S_isPreconnected.intermediate_value hz zero_mem_S h_cont
    have h_zero_in : (0 : ℝ) ∈
        Set.Icc ((Complex.cos (H0 z)).re)
          ((Complex.cos (H0 0)).re) := by
      rw [h_val_zero]
      exact ⟨h_lt.le, le_of_lt one_pos⟩
    obtain ⟨w, hw_mem, hw_eq⟩ := h_ivt h_zero_in
    exact h_re_ne_zero_all w hw_mem hw_eq
  exact (Complex.sq_cpow_two_inv h_re_pos).symm

end Braverman
