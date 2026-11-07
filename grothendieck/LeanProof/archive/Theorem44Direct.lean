/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import LeanProof.Theorem44Regularity

/-!
# Theorem 4.4 — Direct derivative computation

Alternative to the paper's F(u₁,u₂) approach. Instead of introducing F and
differentiating moving limits, we:

1. Work directly with the fixed-domain 4D integral Φ(η) = ∫ sign(x₂)·sign(y₂)·K_η
2. Use D = h₅(x₁)∂_{x₂} + h₅(y₁)∂_{y₂} so that ∂_η^n K_η = D^n K_η
3. Apply the sign-IBP lemma: ∫ sign(t)·g'(t) dt = -2·g(0)
4. Reduce to 2D Gaussian/Hermite integrals

This bypasses the chain rule through F44(η,η) and all moving-limit FTC.

## Key lemma: sign-IBP

For g with sufficient decay:
  ∫ sign(t) · g^(m)(t) dt = -2 · g^(m-1)(0)

Proof: split at 0, integrate by parts on each half, boundary terms cancel
at ±∞ by decay, inner boundary gives -2·g^(m-1)(0).

## Structure

- `SignIBP.lean`: The reusable sign-IBP lemma
- This file: D operator, D^k K₀ computation, derivative assembly
-/

open Complex Set Real MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Braverman

/-! ## The sign-IBP lemma -/

/-- Integration by parts against sign: ∫ sign(t) · g'(t) dt = -2 · g(0),
    for g with sufficient decay. This replaces all moving-limit FTC. -/
theorem sign_ibp_deriv (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hdecay : Tendsto g atTop (nhds 0) ∧ Tendsto g atBot (nhds 0))
    (hint : Integrable (deriv g) volume) :
    ∫ t, (if 0 < t then (1 : ℝ) else -1) * deriv g t = -2 * g 0 := by
  sorry

/-! ## The D operator on the kernel -/

-- The differential operator D = h₅(x₁)·∂_{x₂} + h₅(y₁)·∂_{y₂}
-- applied to the Gaussian-sine kernel K.
-- Since K_η is just K₀ shifted by η in x₂ and y₂,
-- ∂_η K_η = D K_η.

-- For k ≤ 4, D^k K₀ is an explicit polynomial × Gaussian × trig.
-- The binomial expansion D^4 = Σ C(4,a) h₅(x₁)^a h₅(y₁)^b ∂_{x₂}^a ∂_{y₂}^b
-- with the sign-IBP lemma collapses the 4D integral to 2D boundary evaluations.

/-! ## Second derivative: Φ''(0) = 0 -/

-- D² = h₅(x₁)²·∂²_{x₂} + 2·h₅(x₁)·h₅(y₁)·∂_{x₂}∂_{y₂} + h₅(y₁)²·∂²_{y₂}
--
-- After sign-IBP in x₂ (or y₂):
-- ∫ sign(x₂)·∂²_{x₂} K₀ dx₂ = -2·(∂_{x₂} K₀)|_{x₂=0}
-- etc.
-- The resulting 2D integrals cancel by the Hermite identity (paper eq 55).

/-! ## Fourth derivative: Φ''''(0) = 38400·√2 -/

-- D⁴ = Σ_{a+b=4} C(4,a) h₅(x₁)^a h₅(y₁)^b ∂^a_{x₂} ∂^b_{y₂}
-- Coefficients: (1, 4, 6, 4, 1), by x↔y symmetry collapses to (2, 8, 6)
-- After sign-IBP: three types of 2D integrals
-- 2·(paper 57) + 8·(paper 58) + 6·(paper 59) = 38400·√2

end Braverman
