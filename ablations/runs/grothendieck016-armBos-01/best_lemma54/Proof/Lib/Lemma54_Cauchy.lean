/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem51
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy Coefficient Bounds — generic building blocks

Generic Cauchy-estimate helpers used by the paper-faithful Lemma 5.4
proof. The application of these helpers to the specific `F_inv` of the
paper (analytic on `disk r₁`) lives in `Lemma54_Paper_Cauchy.lean`.

## Main results

- `cauchy_taylor_coeff_bound`: if `‖f‖ ≤ M` on `sphere(0,R)` and `f` is
  analytic on `ball(0,R)`, then `‖taylor_coeff f k‖ ≤ M / Rᵏ`.
- `cauchy_taylor_coeff_bound'`: variant for `f` differentiable on the
  closed ball.
- `cauchy_taylor_coeff_bound_closedBall`: variant with bound on the
  whole closed ball.
-/

open Complex Set Metric Real

noncomputable section

namespace Braverman

/-! ### Cauchy coefficient bound -/

/-- **General Cauchy coefficient bound.** If `f` is analytic on
`ball(0,R)` with continuous extension to `closedBall(0,R)`, and
`‖f(z)‖ ≤ M` for `z ∈ sphere(0,R)`, then the `k`-th Taylor coefficient
satisfies `‖aₖ‖ ≤ M / Rᵏ`.

This follows from Cauchy's estimate
`‖iteratedDeriv k f 0‖ ≤ k! · M / Rᵏ` and
`taylor_coeff f k = iteratedDeriv k f 0 / k!`. -/
theorem cauchy_taylor_coeff_bound {f : ℂ → ℂ} {R M : ℝ} {k : ℕ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball (0 : ℂ) R))
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ‖taylor_coeff f k‖ ≤ M / R ^ k := by
  unfold taylor_coeff
  rw [norm_div, Complex.norm_natCast]
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR hf hM
  have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr k.factorial_pos
  rw [div_le_div_iff₀ hk_pos (pow_pos hR k)]
  have h := mul_le_mul_of_nonneg_right hcauchy (le_of_lt (pow_pos hR k))
  rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hR k))] at h
  linarith

/-- Variant: Cauchy coefficient bound for functions differentiable on
`closedBall(0,R)`. Covers analytic functions. -/
theorem cauchy_taylor_coeff_bound' {f : ℂ → ℂ} {R M : ℝ} {k : ℕ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R))
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ‖taylor_coeff f k‖ ≤ M / R ^ k :=
  cauchy_taylor_coeff_bound hR (hf.diffContOnCl_ball Subset.rfl) hM

/-- Variant: bound on the closed ball implies bound on the sphere. -/
theorem cauchy_taylor_coeff_bound_closedBall {f : ℂ → ℂ} {R M : ℝ} {k : ℕ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R))
    (hM : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ M) :
    ‖taylor_coeff f k‖ ≤ M / R ^ k :=
  cauchy_taylor_coeff_bound' hR hf (fun z hz => hM z (sphere_subset_closedBall hz))

end Braverman
