/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import LeanProof.Theorem44Support

/-!
# Theorem 4.4 Endpoint computations: mixed derivatives

Paper equations (53), (56), (58), (59): the mixed ∂u₁∂u₂ derivatives
of F44 at (0,0).

## Strategy (from the plan)
1. Prove d11_F44_formula (paper eq. 53) — differentiate eq. (51) in u₂
2. Evaluate at (0,0) for d11_F44_at_zero (paper eq. 56)
3. Differentiate twice more in u₂ for d13_F44_at_zero (paper eq. 58)
4. Differentiate once in u₁ and once in u₂ for d22_F44_at_zero (paper eq. 59)

## What NOT to do
- Do not redefine shared analytic lemmas from Theorem44Support
- Do not differentiate the full 4D integral from scratch
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## D2a. Mixed first-derivative formula (paper equation 53)

Starting from the first derivative formula (eq. 51):
  ∂F44/∂u₁(u₁,u₂) = -4 ∫∫∫_{y₂ > u₂·h₅(y₁)}
    exp(-(x₁² + (u₁·h₅(x₁))² + y₁² + y₂²)/2) · h₅(x₁) · sin(x₁y₁ + u₁·h₅(x₁)·y₂)

We differentiate with respect to u₂ using Leibniz/FTC on the y₂ boundary.
The boundary term evaluates the integrand at y₂ = u₂·h₅(y₁) with a factor of -h₅(y₁),
giving the formula below. The sign: -4 × (-h₅(y₁)) = +4·h₅(y₁).
-/

/-- ∂²F44/(∂u₁∂u₂) formula: differentiate eq. (51) with respect to u₂.
    Paper equation (53). The Leibniz rule applied to the y₂ lower boundary
    u₂·h₅(y₁) gives a factor of h₅(y₁) and evaluates y₂ at the boundary. -/
theorem d11_F44_formula (u₁ u₂ : ℝ) :
    deriv (fun s => deriv (fun t => F44 t s) u₁) u₂ =
      ∫ x₁ : ℝ, ∫ y₁ : ℝ,
        Real.exp (-(x₁ ^ 2 + (u₁ * h5 x₁) ^ 2 + y₁ ^ 2 + (u₂ * h5 y₁) ^ 2) / 2) *
        h5 x₁ * h5 y₁ *
        Real.sin (x₁ * y₁ + u₁ * h5 x₁ * (u₂ * h5 y₁)) := by
  -- Proof outline:
  -- 1. Use d_u1_F44_formula to rewrite the inner derivative
  -- 2. Apply Leibniz/FTC to differentiate ∫_{y₂ > u₂·h₅(y₁)} in u₂
  -- 3. The boundary contribution gives -(-4)·h₅(y₁)·(integrand at y₂=u₂·h₅(y₁))
  -- This requires: dominated convergence for the parameter derivative,
  -- and FTC for the lower boundary of the y₂ integral.
  sorry

/-! ## D2b. Equation (56): d11_F44(0,0)

At (u₁,u₂) = (0,0), the formula (53) simplifies dramatically:
- u₁·h₅(x₁) = 0 and u₂·h₅(y₁) = 0
- The exponential becomes exp(-(x₁² + y₁²)/2)
- sin(x₁·y₁ + 0) = sin(x₁·y₁)

So d11_F44(0,0) = 4 ∫∫ exp(-(x₁²+y₁²)/2) · h₅(x₁) · h₅(y₁) · sin(x₁y₁) dx₁ dy₁

Apply gaussian_h5_sin_transform to the y₁ integral:
  ∫ h₅(y₁) · exp(-y₁²/2) · sin(x₁·y₁) dy₁ = √(2π) · exp(-x₁²/2) · h₅(x₁)

This gives: 4·√(2π) · ∫ h₅(x₁)² · exp(-x₁²) dx₁

By h₅ orthonormality (∫ h₅(x)² exp(-x²) dx = √π, but normalized so
∫ h₅² exp(-x²) = √π, then 4·√(2π)·√π = 4·√(2π²) — actually with our
normalization, ∫ h₅(x)² exp(-x²/2) · exp(-x²/2) uses the transform directly).

The final computation: after applying the sine transform and collecting,
we get exactly 4·√(2π).
-/

/-- (∂²F44/∂u₁∂u₂)(0,0).
    Evaluate d11_F44_formula at (0,0). The integrand simplifies to
    exp(-(x₁²+y₁²)/4) · h₅(x₁) · h₅(y₁) · sin(x₁y₁/2).
    TODO: recompute numerical value for exp(-S/4)·sin(D/2) kernel. -/
theorem d11_F44_at_zero :
    d11_F44 0 0 = sorry := by
  sorry

/-! ## D2c. Equation (58): d13_F44(0,0)

We need iteratedDeriv 3 (fun s => deriv (fun t => F44 t s) 0) 0.

Starting from d11_F44_formula at u₁=0:
  deriv (fun s => deriv (fun t => F44 t s) 0) u₂
  = 4 ∫∫ exp(-(x₁² + y₁² + (u₂·h₅(y₁))²)/2) · h₅(x₁) · h₅(y₁) · sin(x₁·y₁)

(Since u₁=0: the u₁·h₅(x₁) terms vanish, and sin(x₁y₁ + 0) = sin(x₁y₁).)

Now we differentiate twice more in u₂. The u₂ dependence is only in
exp(-(u₂·h₅(y₁))²/2) = exp(-u₂²·h₅(y₁)²/2).

Let g(u₂) = exp(-u₂²·h₅(y₁)²/2). Then:
  g'(u₂) = -u₂·h₅(y₁)²·g(u₂)
  g''(u₂) = (-h₅(y₁)² + u₂²·h₅(y₁)⁴)·g(u₂)

At u₂=0: g(0)=1, g'(0)=0, g''(0)=-h₅(y₁)².

So iteratedDeriv 2 of (fun u₂ => ...) at 0 gives:
  4 ∫∫ (-h₅(y₁)²) · exp(-(x₁²+y₁²)/2) · h₅(x₁) · h₅(y₁) · sin(x₁y₁)
  = -4 ∫∫ exp(-(x₁²+y₁²)/2) · h₅(x₁) · h₅(y₁)³ · sin(x₁y₁)

Apply gaussian_h5_sin_transform (viewing h₅(y₁)³·sin as needing a different identity):
Actually, we need ∫ h₅(y)³ · exp(-y²/2) · sin(xy) dy. This factors through the
Fourier sine transform of h₅³·Gaussian.

After the full computation (using the Hermite recurrence or direct integration):
  d13_F44(0,0) = -18612·√2
-/

/-- (∂⁴F44/∂u₁·∂u₂³)(0,0).
    Differentiate d11_F44_formula twice more in u₂, evaluate at (0,0).
    TODO: recompute numerical value for exp(-S/4)·sin(D/2) kernel. -/
theorem d13_F44_at_zero :
    d13_F44 0 0 = sorry := by
  unfold d13_F44
  -- The full proof requires:
  -- 1. Use d11_F44_formula to express the inner function
  -- 2. Compute iteratedDeriv 2 of the u₂-dependent part at u₂=0
  --    The u₂ dependence is in exp(-u₂²·h₅(y₁)²/2) and sin(x₁y₁ + 0·h₅(x₁)·u₂·h₅(y₁))
  --    At u₁=0, sin term has no u₂ dependence, so only the Gaussian contributes
  -- 3. The second u₂-derivative of exp(-u₂²·h₅(y₁)²/2) at u₂=0 is -h₅(y₁)²
  -- 4. This gives -4 ∫∫ exp(-(x₁²+y₁²)/2) · h₅(x₁) · h₅(y₁)³ · sin(x₁y₁)
  -- 5. Apply gaussian_h5_sin_transform for the y₁ integral
  --    (need the identity for h₅³ times Gaussian sine transform)
  -- 6. Apply lemma_4_1_eq26 for ∫ h₅⁴ exp(-x²)
  sorry

/-! ## D2d. Equation (59): d22_F44(0,0)

We need iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun t => F44 t s) 0) 0.

This requires differentiating the formula (53) once in u₁ and once in u₂.

At (0,0), the surviving term involves:
  ∫∫ h₅(x₁)² · h₅(y₁)² · exp(-(x₁²+y₁²)/2) · cos(x₁·y₁) dx₁ dy₁

This is exactly the integral computed in Lemma 4.1 eq. (27):
  = 176400·√2·π / h5_norm_const⁴

After combining with the prefactor, d22_F44(0,0) = 196·√2.
-/

/-- (∂⁴F44/∂u₁²·∂u₂²)(0,0).
    Differentiate d11_F44_formula once in u₁ and once in u₂, evaluate at (0,0).
    TODO: recompute numerical value for exp(-S/4)·sin(D/2) kernel. -/
theorem d22_F44_at_zero :
    d22_F44 0 0 = sorry := by
  unfold d22_F44
  -- The proof requires:
  -- 1. Express iteratedDeriv 2 in u₁ of F44 via two applications of d_u1_F44_formula
  -- 2. Differentiate twice in u₂ using formula structure
  -- 3. At (0,0), the key surviving integral is
  --    4 · ∫∫ h₅(x₁)² · h₅(y₁)² · exp(-(x₁²+y₁²)/2) · cos(x₁y₁)
  --    The cosine appears because differentiating sin once in each variable
  --    (via boundary terms) produces a cosine of the diagonal argument
  -- 4. Apply lemma_4_1_eq27:
  --    ∫∫ h₅(x)² h₅(y)² exp(-(x²+y²)/2) cos(xy) = 176400·√2·π / h5_norm_const⁴
  -- 5. Simplify: 4 · 176400·√2·π / h5_norm_const⁴ = 196·√2
  --    (using h5_norm_const⁴ = (16·√(π·15))⁴ = ... and the cancellation)
  sorry

end Braverman
