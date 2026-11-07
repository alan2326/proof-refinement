/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import LeanProof.Theorem44Support

/-!
# Theorem 4.4 Endpoint computations: pure u₁ derivatives

Paper equations (51), (52), (57): the ∂F44/∂u₁, (∂²F44/∂u₁²)(0,0),
and (∂⁴F44/∂u₁⁴)(0,0) endpoint values.

## Strategy (from the plan)
1. Prove the first-derivative formula d_u1_F44_formula (paper eq. 51)
   — this is the moving-boundary FTC step
2. Differentiate once more for d20_F44_at_zero (paper eq. 52)
3. Differentiate three more times for d40_F44_at_zero (paper eq. 57)

## What NOT to do
- Do not differentiate the whole 4D integral four times from scratch
- Start from d_u1_F44_formula and build up
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## D1a. First derivative formula (paper equation 51) -/

/-- ∂F44/∂u₁ at (u₁, u₂): the Leibniz/FTC formula for differentiating
    the lower boundary x₂ = u₁·h₅(x₁) of the inner integral.
    Note: F44 uses the exp(-S/4)·sin(D/2) kernel (matching H_eta normalization). -/
theorem d_u1_F44_formula (u₁ u₂ : ℝ) :
    deriv (fun t => F44 t u₂) u₁ =
      -(∫ x₁ : ℝ, ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (u₂ * h5 y₁),
        Real.exp (-(x₁ ^ 2 + (u₁ * h5 x₁) ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
        h5 x₁ * Real.sin (x₁ * y₁ + u₁ * h5 x₁ * y₂)) := by
  sorry

/-! ## D1b. d20_F44(0,0) -/

/-- (∂²F44/∂u₁²)(0,0).
    Differentiate d_u1_F44_formula once more in u₁, evaluate at (0,0).
    TODO: recompute numerical value for exp(-S/4)·sin(D/2) kernel. -/
theorem d20_F44_at_zero :
    d20_F44 0 0 = sorry := by
  sorry

/-! ## D1c. d40_F44(0,0) -/

/-- (∂⁴F44/∂u₁⁴)(0,0).
    Differentiate d_u1_F44_formula three more times in u₁, evaluate at (0,0).
    TODO: recompute numerical value for exp(-S/4)·sin(D/2) kernel. -/
theorem d40_F44_at_zero :
    d40_F44 0 0 = sorry := by
  sorry

end Braverman
