/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Defs.HermitePoly
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Lemma 4.1: Hermite integral computations

We prove the two key integral identities from Lemma 4.1 of the paper:

1. (equation 26): `∫ exp(-x²) · h₅(x)⁴ dx = 4653√π`
2. (equation 27): `∫∫ exp(-(x²+y²)/2) · h₅(x)² · h₅(y)² · cos(xy) dx dy = 49√2`

These are the computational backbone needed for Theorem 4.4.

## Strategy for (26)

We use "Approach B" (Lean-friendly):
1. Expand h₅⁴ via the unnormalized polynomial (degree 20)
2. Reduce to Gaussian moment integrals I(n) = ∫ x^(2n) exp(-x²) dx
3. Use the recursion I(n+1) = (2n+1)/2 · I(n) with I(0) = √π
-/

open Real MeasureTheory Set

noncomputable section

namespace Braverman

/-! ### Gaussian moment integrals -/

/-- The Gaussian moment integral I(n) = ∫ x^(2n) · exp(-x²) dx. -/
def gaussianMoment (n : ℕ) : ℝ := ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)

/-- I(0) = √π. This is the standard Gaussian integral. -/
theorem gaussianMoment_zero : gaussianMoment 0 = Real.sqrt Real.pi := by
  simp only [gaussianMoment, Nat.zero_eq, mul_zero, pow_zero, one_mul]
  have h := integral_gaussian (1 : ℝ)
  simp at h
  exact h

/-- The recursion I(n+1) = (2n+1)/2 · I(n), proved by integration by parts. -/
theorem gaussianMoment_succ (n : ℕ) :
    gaussianMoment (n + 1) = (2 * n + 1) / 2 * gaussianMoment n := by
  unfold gaussianMoment
  -- Helper: x^k * exp(-x²) is integrable for any k
  have pow_int : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (k : ℕ) * Real.exp (-x ^ 2)) := by
    intro k
    have hk : -1 < (↑k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1) hk
    simp only [one_mul] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast]
  -- Derivative of x^(2n+1)
  have hu : ∀ x : ℝ, HasDerivAt (fun x => x ^ (2 * n + 1))
      ((↑(2 * n + 1) : ℝ) * x ^ (2 * n)) x := by
    intro x; have := hasDerivAt_pow (2 * n + 1) x
    simp only [Nat.cast_succ] at this; convert this using 1; push_cast; ring
  -- Derivative of -(1/2) * exp(-x²): equals x * exp(-x²)
  have hv : ∀ x : ℝ, HasDerivAt (fun x => -(1/2 : ℝ) * Real.exp (-x ^ 2))
      (x * Real.exp (-x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x => x ^ 2) (2 * x) x := by
      have := hasDerivAt_pow 2 x; simpa using this
    have h2 : HasDerivAt (fun x => -x ^ 2) (-(2 * x)) x := h1.neg
    have h3 : HasDerivAt (fun x => Real.exp (-x ^ 2)) (Real.exp (-x ^ 2) * -(2 * x)) x :=
      h2.exp
    have h4 := h3.const_mul (-(1/2 : ℝ))
    convert h4 using 1; ring
  -- Integrability: u * v' = x^(2n+2) * exp(-x²)
  have huv' : Integrable (fun x : ℝ => x ^ (2 * n + 1) * (x * rexp (-x ^ 2))) := by
    have : (fun x : ℝ => x ^ (2 * n + 1) * (x * rexp (-x ^ 2))) =
        fun x => x ^ (2 * n + 2) * rexp (-x ^ 2) := by ext x; ring
    rw [this]; exact pow_int _
  -- Integrability: u' * v
  have hu'v : Integrable (fun x : ℝ =>
      ↑(2 * n + 1) * x ^ (2 * n) * (-(1 / 2) * rexp (-x ^ 2))) := by
    have : (fun x : ℝ => ↑(2 * n + 1) * x ^ (2 * n) * (-(1 / 2) * rexp (-x ^ 2))) =
        fun x => -(↑(2 * n + 1) / 2) * (x ^ (2 * n) * rexp (-x ^ 2)) := by ext x; ring
    rw [this]; exact (pow_int _).const_mul _
  -- Integrability: u * v
  have huv : Integrable (fun x : ℝ =>
      x ^ (2 * n + 1) * (-(1 / 2) * rexp (-x ^ 2))) := by
    have : (fun x : ℝ => x ^ (2 * n + 1) * (-(1 / 2) * rexp (-x ^ 2))) =
        fun x => -(1 / 2 : ℝ) * (x ^ (2 * n + 1) * rexp (-x ^ 2)) := by ext x; ring
    rw [this]; exact (pow_int _).const_mul _
  -- Integration by parts: ∫ u v' = -∫ u' v (boundary terms vanish)
  have ibp : ∫ x : ℝ, x ^ (2 * n + 1) * (x * rexp (-x ^ 2)) =
      -∫ x : ℝ, ↑(2 * n + 1) * x ^ (2 * n) * (-(1 / 2) * rexp (-x ^ 2)) :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
  -- Rewrite LHS to match IBP
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  have lhs_eq : ∫ x : ℝ, x ^ (2 * n + 2) * rexp (-x ^ 2) =
      ∫ x : ℝ, x ^ (2 * n + 1) * (x * rexp (-x ^ 2)) := by
    congr 1; ext x; ring
  rw [lhs_eq, ibp]
  -- Simplify -(∫ -(c * f)) = c * ∫ f
  have rhs_eq : ∀ x : ℝ, ↑(2 * n + 1) * x ^ (2 * n) * (-(1 / 2) * rexp (-x ^ 2)) =
      -((2 * ↑n + 1) / 2 * (x ^ (2 * n) * rexp (-x ^ 2))) := by
    intro x; push_cast; ring
  simp_rw [rhs_eq, integral_neg, neg_neg]
  rw [show (fun x : ℝ => (2 * ↑n + 1) / 2 * (x ^ (2 * n) * rexp (-x ^ 2))) =
    fun x => ((2 * ↑n + 1) / 2 : ℝ) • (x ^ (2 * n) * rexp (-x ^ 2)) from
    funext (fun x => (smul_eq_mul _ _).symm), MeasureTheory.integral_smul]
  simp [smul_eq_mul]

/-- Explicit values of I(n) for small n. -/
theorem gaussianMoment_one : gaussianMoment 1 = Real.sqrt Real.pi / 2 := by
  rw [gaussianMoment_succ, gaussianMoment_zero]; ring

theorem gaussianMoment_two : gaussianMoment 2 = 3 / 4 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_one]; ring

theorem gaussianMoment_three : gaussianMoment 3 = 15 / 8 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_two]; ring

theorem gaussianMoment_four : gaussianMoment 4 = 105 / 16 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_three]; ring

theorem gaussianMoment_five : gaussianMoment 5 = 945 / 32 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_four]; ring

theorem gaussianMoment_six : gaussianMoment 6 = 10395 / 64 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_five]; ring

theorem gaussianMoment_seven : gaussianMoment 7 = 135135 / 128 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_six]; ring

theorem gaussianMoment_eight : gaussianMoment 8 = 2027025 / 256 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_seven]; ring

theorem gaussianMoment_nine : gaussianMoment 9 = 34459425 / 512 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_eight]; ring

theorem gaussianMoment_ten : gaussianMoment 10 = 654729075 / 1024 * Real.sqrt Real.pi := by
  rw [gaussianMoment_succ, gaussianMoment_nine]; ring

/-! ### The normalization constant -/

/-- The normalization constant is positive. -/
theorem h5_norm_const_pos : 0 < h5_norm_const := by
  unfold h5_norm_const
  positivity

/-! ### Lemma 4.1, equation (26) -/

/-- The unnormalized integral ∫ h₅_unnorm(x)⁴ · exp(-x²) dx.
    This reduces to a linear combination of Gaussian moments. -/
-- Helper: x^k * exp(-x²) is integrable for any k
private theorem integrable_pow_mul_exp (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) := by
  have hk : -1 < (↑k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1) hk
  simp only [one_mul] at this
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.rpow_natCast]

-- Helper: c * x^k * exp(-x²) is integrable
theorem integrable_const_mul_pow_mul_exp (c : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => c * x ^ k * Real.exp (-x ^ 2)) := by
  have : (fun x : ℝ => c * x ^ k * Real.exp (-x ^ 2)) =
      fun x => c * (x ^ k * Real.exp (-x ^ 2)) := by ext x; ring
  rw [this]; exact (integrable_pow_mul_exp k).const_mul c

theorem integral_const_mul_pow_mul_exp_eq (c : ℝ) (n : ℕ) :
    ∫ x : ℝ, c * x ^ (2 * n) * Real.exp (-x ^ 2) = c * gaussianMoment n := by
  unfold gaussianMoment
  rw [show (fun x : ℝ => c * x ^ (2 * n) * Real.exp (-x ^ 2)) =
      fun x => c * (x ^ (2 * n) * Real.exp (-x ^ 2)) from funext (fun x => by ring)]
  rw [integral_const_mul]

theorem integral_h5_unnorm_pow_four :
    ∫ x : ℝ, h5_unnorm x ^ 4 * Real.exp (-x ^ 2) =
    16750800 * Real.sqrt Real.pi := by
  -- Define abbreviation for monomial integrand
  let f : ℝ → ℕ → ℝ → ℝ := fun c k x => c * x ^ k * Real.exp (-x ^ 2)
  have intf : ∀ c k, Integrable (f c k) := fun c k =>
    integrable_const_mul_pow_mul_exp c k
  -- Rewrite integrand as right-associated sum of functions
  have heq : (fun x => h5_unnorm x ^ 4 * Real.exp (-x ^ 2)) =
      (f 256 20 + (f (-5120) 18 + (f 42240 16 + (f (-185600) 14 +
      (f 469600 12 + (f (-696000) 10 + (f 594000 8 + (f (-270000) 6 +
      f 50625 4)))))))) := by
    ext x; simp only [f, Pi.add_apply, h5_unnorm]; ring
  -- Rewrite the integral
  calc ∫ x : ℝ, h5_unnorm x ^ 4 * Real.exp (-x ^ 2)
      = ∫ x, (f 256 20 + (f (-5120) 18 + (f 42240 16 + (f (-185600) 14 +
        (f 469600 12 + (f (-696000) 10 + (f 594000 8 + (f (-270000) 6 +
        f 50625 4)))))))) x := by
          congr 1
    _ = (∫ x, f 256 20 x) + ∫ x, (f (-5120) 18 + (f 42240 16 + (f (-185600) 14 +
        (f 469600 12 + (f (-696000) 10 + (f 594000 8 + (f (-270000) 6 +
        f 50625 4))))))) x :=
          integral_add' (intf 256 20) ((intf (-5120) 18).add ((intf 42240 16).add
            ((intf (-185600) 14).add ((intf 469600 12).add ((intf (-696000) 10).add
            ((intf 594000 8).add ((intf (-270000) 6).add (intf 50625 4))))))))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ∫ x, (f 42240 16 + (f (-185600) 14 +
        (f 469600 12 + (f (-696000) 10 + (f 594000 8 + (f (-270000) 6 +
        f 50625 4)))))) x) := by
          congr 1; exact integral_add' (intf (-5120) 18) ((intf 42240 16).add
            ((intf (-185600) 14).add ((intf 469600 12).add ((intf (-696000) 10).add
            ((intf 594000 8).add ((intf (-270000) 6).add (intf 50625 4)))))))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ∫ x, (f (-185600) 14 + (f 469600 12 + (f (-696000) 10 + (f 594000 8 +
        (f (-270000) 6 + f 50625 4))))) x)) := by
          congr 2; exact integral_add' (intf 42240 16) ((intf (-185600) 14).add
            ((intf 469600 12).add ((intf (-696000) 10).add ((intf 594000 8).add
            ((intf (-270000) 6).add (intf 50625 4))))))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ((∫ x, f (-185600) 14 x) + ∫ x, (f 469600 12 + (f (-696000) 10 +
        (f 594000 8 + (f (-270000) 6 + f 50625 4)))) x))) := by
          congr 3; exact integral_add' (intf (-185600) 14) ((intf 469600 12).add
            ((intf (-696000) 10).add ((intf 594000 8).add ((intf (-270000) 6).add
            (intf 50625 4)))))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ((∫ x, f (-185600) 14 x) + ((∫ x, f 469600 12 x) + ∫ x, (f (-696000) 10 +
        (f 594000 8 + (f (-270000) 6 + f 50625 4))) x)))) := by
          congr 4; exact integral_add' (intf 469600 12) ((intf (-696000) 10).add
            ((intf 594000 8).add ((intf (-270000) 6).add (intf 50625 4))))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ((∫ x, f (-185600) 14 x) + ((∫ x, f 469600 12 x) + ((∫ x, f (-696000) 10 x) +
        ∫ x, (f 594000 8 + (f (-270000) 6 + f 50625 4)) x))))) := by
          congr 5; exact integral_add' (intf (-696000) 10) ((intf 594000 8).add
            ((intf (-270000) 6).add (intf 50625 4)))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ((∫ x, f (-185600) 14 x) + ((∫ x, f 469600 12 x) + ((∫ x, f (-696000) 10 x) +
        ((∫ x, f 594000 8 x) + ∫ x, (f (-270000) 6 + f 50625 4) x)))))) := by
          congr 6; exact integral_add' (intf 594000 8) ((intf (-270000) 6).add (intf 50625 4))
    _ = (∫ x, f 256 20 x) + ((∫ x, f (-5120) 18 x) + ((∫ x, f 42240 16 x) +
        ((∫ x, f (-185600) 14 x) + ((∫ x, f 469600 12 x) + ((∫ x, f (-696000) 10 x) +
        ((∫ x, f 594000 8 x) + ((∫ x, f (-270000) 6 x) + ∫ x, f 50625 4 x))))))) := by
          congr 7; exact integral_add' (intf (-270000) 6) (intf 50625 4)
    _ = 16750800 * Real.sqrt Real.pi := by
        -- Each ∫ f c k x is c * gaussianMoment(k/2)
        -- f c k x = c * x ^ k * exp(-x^2) and k is even
        simp only [f]
        rw [integral_const_mul_pow_mul_exp_eq 256 10,
            integral_const_mul_pow_mul_exp_eq (-5120) 9,
            integral_const_mul_pow_mul_exp_eq 42240 8,
            integral_const_mul_pow_mul_exp_eq (-185600) 7,
            integral_const_mul_pow_mul_exp_eq 469600 6,
            integral_const_mul_pow_mul_exp_eq (-696000) 5,
            integral_const_mul_pow_mul_exp_eq 594000 4,
            integral_const_mul_pow_mul_exp_eq (-270000) 3,
            integral_const_mul_pow_mul_exp_eq 50625 2]
        rw [gaussianMoment_ten, gaussianMoment_nine, gaussianMoment_eight,
            gaussianMoment_seven, gaussianMoment_six, gaussianMoment_five,
            gaussianMoment_four, gaussianMoment_three, gaussianMoment_two]
        ring

/-- **Lemma 4.1, equation (26)** in terms of our normalized h₅. -/
theorem lemma_4_1_eq26 :
    ∫ x : ℝ, h5 x ^ 4 * Real.exp (-x ^ 2) =
    16750800 * Real.sqrt Real.pi / h5_norm_const ^ 4 := by
  have heq : (fun x => h5 x ^ 4 * rexp (-x ^ 2)) =
      fun x => (1 / h5_norm_const ^ 4) * (h5_unnorm x ^ 4 * rexp (-x ^ 2)) := by
    ext x; simp [h5, div_pow]; ring
  rw [heq, MeasureTheory.integral_const_mul, integral_h5_unnorm_pow_four]
  ring

/-! ### Lemma 4.1, equation (27) -/

/-! #### Gaussian cosine moments

We compute `C(n, y) = ∫ x^n · exp(-x²/2) · cos(xy) dx` for even `n` up to 10,
using integration by parts to establish the recursion:
  C(n+1, y) = n · C(n-1, y) - y · S(n, y)
  S(n+1, y) = n · S(n-1, y) + y · C(n, y)
where `S(n, y) = ∫ x^n · exp(-x²/2) · sin(xy) dx`.

The base case `C(0, y) = √(2π) · exp(-y²/2)` follows from the Fourier
transform of the Gaussian (via `integral_cexp_quadratic`).

The key integration-by-parts identity uses `d/dx[exp(-x²/2)] = -x · exp(-x²/2)`:
from ∫ u · v' = -∫ u' · v with u = x^n · cos(xy), v = -exp(-x²/2). -/

/-- `∫ x^k * exp(-(1/2)*x²)` is integrable for any k. -/
private theorem integrable_pow_mul_exp_half (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * rexp (-(1/2) * x ^ 2)) := by
  have hk : -1 < (↑k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2) hk
  exact this.congr (Filter.Eventually.of_forall fun x => by simp [Real.rpow_natCast])

/-- Base case: `∫ exp(-x²/2) · cos(xy) = √(2π) · exp(-y²/2)`.
    This is the Fourier transform of the standard Gaussian. -/
private theorem gaussian_cos_moment_zero (y : ℝ) :
    ∫ x : ℝ, rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) := by
  -- Key: cos(xy) = Re(cexp(I*xy)), so the integral is Re of a complex Gaussian
  -- Define the complex integrand f(x) = cexp((-1/2)*x² + I*y*x)
  set f : ℝ → ℂ := fun x => Complex.exp ((-1/2 : ℂ) * (x : ℂ) ^ 2 +
    Complex.I * (y : ℂ) * (x : ℂ)) with hf_def
  -- f is integrable (from integrable_cexp_quadratic')
  have hint : Integrable f := by
    have h := integrable_cexp_quadratic' (show ((-1/2 : ℂ)).re < 0 from by norm_num)
      (Complex.I * (y : ℂ)) 0
    simp only [add_zero] at h; exact h
  -- Step 1: Our integrand = Re(f(x))
  have hre : ∀ x : ℝ, rexp (-x ^ 2 / 2) * cos (x * y) = (f x).re := by
    intro x
    simp only [f]
    -- Rewrite the complex argument as ↑a + ↑b * I
    have harg : (-1/2 : ℂ) * (x : ℂ) ^ 2 + Complex.I * (y : ℂ) * (x : ℂ) =
        ↑(-x^2/2 : ℝ) + ↑(x * y : ℝ) * Complex.I := by
      rw [← Complex.ofReal_pow]; push_cast; ring
    rw [harg, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    -- Goal: rexp * cos = (↑(rexp) * (↑(cos) + ↑(sin) * I)).re
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  simp_rw [hre]
  -- Step 2: ∫ Re(f) = Re(∫ f)
  rw [show (fun x : ℝ => (f x).re) = (fun x : ℝ => RCLike.re (f x)) from rfl,
      integral_re hint]
  -- Step 3: Compute ∫ f using integral_cexp_quadratic
  have hcalc := integral_cexp_quadratic (show ((-1/2 : ℂ)).re < 0 from by norm_num)
      (Complex.I * (y : ℂ)) 0
  simp only [add_zero, zero_sub] at hcalc
  rw [show (∫ x : ℝ, f x) = ∫ x : ℝ,
      Complex.exp ((-1/2 : ℂ) * ↑x ^ 2 + Complex.I * ↑y * ↑x) from rfl,
    hcalc]
  -- Step 4: Simplify the complex expression and take Re
  -- Simplify arithmetic: -(-1/2) = 1/2, π/(1/2) = 2π
  -- (I*y)² = -y², 4*(-1/2) = -2, -(-y²/(-2)) = -y²/2
  have hsimp1 : (↑Real.pi / -(-1/2 : ℂ)) = ↑(2 * Real.pi) := by
    push_cast; ring
  have hsimp2 : -((Complex.I * ↑y) ^ 2 / (4 * (-1/2 : ℂ))) = ↑(-y^2/2 : ℝ) := by
    have : (Complex.I * (↑y : ℂ)) ^ 2 = -(↑y : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [this]; push_cast; ring
  rw [hsimp1, hsimp2, ← Complex.ofReal_exp]
  -- Now: Re(↑(2π)^(1/2 : ℂ) * ↑(exp(-y²/2)))
  -- Need: ↑(2π)^(1/2 : ℂ) = ↑(sqrt(2π))
  have h2pi_pos : (0 : ℝ) ≤ 2 * Real.pi := (mul_pos two_pos Real.pi_pos).le
  have hpow : (↑(2 * Real.pi) : ℂ) ^ (1/2 : ℂ) = ↑(Real.sqrt (2 * Real.pi)) := by
    rw [Real.sqrt_eq_rpow, show (1/2 : ℂ) = ↑(1/2 : ℝ) from by push_cast; ring,
        ← Complex.ofReal_cpow h2pi_pos]
  rw [hpow, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-! #### Integration by parts machinery for Gaussian cosine/sine moments -/

private theorem integrable_pow_mul_exp_half_cos (k : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => x ^ k * rexp (-(1/2) * x ^ 2) * cos (x * y)) :=
  (integrable_pow_mul_exp_half k).norm.mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs]; rw [abs_mul]; exact
      mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))

theorem integrable_pow_mul_exp_half_sin (k : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ => x ^ k * rexp (-(1/2) * x ^ 2) * sin (x * y)) :=
  (integrable_pow_mul_exp_half k).norm.mono' (by fun_prop)
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs]; rw [abs_mul]; exact
      mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))

private theorem hasDerivAt_neg_exp_half (x : ℝ) :
    HasDerivAt (fun x => -rexp (-(1/2) * x ^ 2))
      (x * rexp (-(1/2) * x ^ 2)) x := by
  convert ((hasDerivAt_pow 2 x).const_mul (-(1/2 : ℝ))).exp.neg using 1; simp; ring

/-- IBP cosine recursion: `C(n+1) = n·C(n-1) - y·S(n)`. -/
private theorem ibp_cos_step (n : ℕ) (_hn : 1 ≤ n) (y : ℝ) :
    ∫ x : ℝ, x ^ (n + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y) =
    ↑n * (∫ x : ℝ, x ^ (n - 1) * rexp (-(1/2) * x ^ 2) * cos (x * y)) -
    y * (∫ x : ℝ, x ^ n * rexp (-(1/2) * x ^ 2) * sin (x * y)) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t => t ^ n * cos (t * y))
      (↑n * x ^ (n - 1) * cos (x * y) - y * x ^ n * sin (x * y)) x := by
    intro x
    convert (hasDerivAt_pow n x).mul ((hasDerivAt_mul_const y (x := x)).cos) using 1; ring
  have huv' : Integrable (fun x => x ^ n * cos (x * y) * (x * rexp (-(1/2) * x ^ 2))) :=
    (integrable_pow_mul_exp_half_cos (n+1) y).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have hu'v : Integrable (fun x =>
      (↑n * x ^ (n-1) * cos (x * y) - y * x ^ n * sin (x * y)) *
      (-rexp (-(1/2) * x ^ 2))) :=
    (((integrable_pow_mul_exp_half_cos (n-1) y).const_mul (-↑n)).add
      ((integrable_pow_mul_exp_half_sin n y).const_mul y)).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have huv : Integrable (fun x => x ^ n * cos (x * y) * (-rexp (-(1/2) * x ^ 2))) :=
    ((integrable_pow_mul_exp_half_cos n y).neg).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.neg_apply]; ring)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hasDerivAt_neg_exp_half
    huv' hu'v huv
  rw [show (fun x => x ^ (n + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y)) =
      fun x => x ^ n * cos (x * y) * (x * rexp (-(1/2) * x ^ 2)) from funext fun x => by ring,
    ibp,
    show (fun x => (↑n * x ^ (n-1) * cos (x * y) - y * x ^ n * sin (x * y)) *
      (-rexp (-(1/2) * x ^ 2))) =
      fun x => ((-↑n) * (x ^ (n-1) * rexp (-(1/2) * x ^ 2) * cos (x * y)) +
        y * (x ^ n * rexp (-(1/2) * x ^ 2) * sin (x * y))) from funext fun x => by ring]
  rw [integral_add
    (((integrable_pow_mul_exp_half_cos (n-1) y).const_mul (-↑n)).congr
      (Filter.Eventually.of_forall fun x => by ring))
    (((integrable_pow_mul_exp_half_sin n y).const_mul y).congr
      (Filter.Eventually.of_forall fun x => by ring))]
  conv_lhs =>
    rw [show (fun x => -↑n * (x ^ (n - 1) * rexp (-(1 / 2) * x ^ 2) * cos (x * y))) =
        fun x => (-↑n : ℝ) * (x ^ (n - 1) * rexp (-(1 / 2) * x ^ 2) * cos (x * y)) from rfl]
    rw [integral_const_mul ((-↑n : ℝ)), integral_const_mul y]
  linarith

/-- IBP sine recursion: `S(n+1) = n·S(n-1) + y·C(n)`. -/
private theorem ibp_sin_step (n : ℕ) (_hn : 1 ≤ n) (y : ℝ) :
    ∫ x : ℝ, x ^ (n + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y) =
    ↑n * (∫ x : ℝ, x ^ (n - 1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) +
    y * (∫ x : ℝ, x ^ n * rexp (-(1/2) * x ^ 2) * cos (x * y)) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t => t ^ n * sin (t * y))
      (↑n * x ^ (n - 1) * sin (x * y) + y * x ^ n * cos (x * y)) x := by
    intro x
    convert (hasDerivAt_pow n x).mul ((hasDerivAt_mul_const y (x := x)).sin) using 1; ring
  have huv' : Integrable (fun x => x ^ n * sin (x * y) * (x * rexp (-(1/2) * x ^ 2))) :=
    (integrable_pow_mul_exp_half_sin (n+1) y).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have hu'v : Integrable (fun x =>
      (↑n * x ^ (n-1) * sin (x * y) + y * x ^ n * cos (x * y)) *
      (-rexp (-(1/2) * x ^ 2))) :=
    (((integrable_pow_mul_exp_half_sin (n-1) y).const_mul (-↑n)).add
      ((integrable_pow_mul_exp_half_cos n y).const_mul (-y))).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply]; ring)
  have huv : Integrable (fun x => x ^ n * sin (x * y) * (-rexp (-(1/2) * x ^ 2))) :=
    ((integrable_pow_mul_exp_half_sin n y).neg).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.neg_apply]; ring)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hasDerivAt_neg_exp_half
    huv' hu'v huv
  rw [show (fun x => x ^ (n + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) =
      fun x => x ^ n * sin (x * y) * (x * rexp (-(1/2) * x ^ 2)) from funext fun x => by ring,
    ibp,
    show (fun x => (↑n * x ^ (n-1) * sin (x * y) + y * x ^ n * cos (x * y)) *
      (-rexp (-(1/2) * x ^ 2))) =
      fun x => ((-↑n) * (x ^ (n-1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) +
        (-y) * (x ^ n * rexp (-(1/2) * x ^ 2) * cos (x * y))) from funext fun x => by ring]
  rw [integral_add
    (((integrable_pow_mul_exp_half_sin (n-1) y).const_mul (-↑n)).congr
      (Filter.Eventually.of_forall fun x => by ring))
    (((integrable_pow_mul_exp_half_cos n y).const_mul (-y)).congr
      (Filter.Eventually.of_forall fun x => by ring))]
  conv_lhs =>
    rw [show (fun x => -↑n * (x ^ (n - 1) * rexp (-(1 / 2) * x ^ 2) * sin (x * y))) =
        fun x => (-↑n : ℝ) * (x ^ (n - 1) * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) from rfl]
    rw [integral_const_mul ((-↑n : ℝ)),
        show (fun x => -y * (x ^ n * rexp (-(1 / 2) * x ^ 2) * cos (x * y))) =
          fun x => (-y : ℝ) * (x ^ n * rexp (-(1 / 2) * x ^ 2) * cos (x * y)) from rfl,
        integral_const_mul ((-y : ℝ))]
  linarith

/-- Base case for sine moments: `S(1) = y·C(0)`. -/
theorem sin_moment_one (y : ℝ) :
    ∫ x : ℝ, x * rexp (-(1/2) * x ^ 2) * sin (x * y) =
    y * (∫ x : ℝ, rexp (-(1/2) * x ^ 2) * cos (x * y)) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun t => sin (t * y)) (y * cos (x * y)) x := by
    intro x; convert (hasDerivAt_mul_const y (x := x)).sin using 1; ring
  have huv' : Integrable (fun x => sin (x * y) * (x * rexp (-(1/2) * x ^ 2))) :=
    (integrable_pow_mul_exp_half_sin 1 y).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have hu'v : Integrable (fun x => y * cos (x * y) * (-rexp (-(1/2) * x ^ 2))) :=
    ((integrable_pow_mul_exp_half_cos 0 y).const_mul (-y)).congr
      (Filter.Eventually.of_forall fun x => by simp; ring)
  have huv : Integrable (fun x => sin (x * y) * (-rexp (-(1/2) * x ^ 2))) :=
    ((integrable_pow_mul_exp_half_sin 0 y).neg).congr
      (Filter.Eventually.of_forall fun x => by simp; ring)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hasDerivAt_neg_exp_half
    huv' hu'v huv
  rw [show (fun x => x * rexp (-(1/2) * x ^ 2) * sin (x * y)) =
      (fun x => sin (x * y) * (x * rexp (-(1/2) * x ^ 2))) from funext fun x => by ring,
    ibp,
    show (fun x => y * cos (x * y) * (-rexp (-(1/2) * x ^ 2))) =
      (fun x => (-y) * (rexp (-(1/2) * x ^ 2) * cos (x * y))) from funext fun x => by ring,
    integral_const_mul]; linarith

/-- Conversion between `-x²/2` and `-(1/2)*x²` forms in exp. -/
private theorem exp_half_eq (x : ℝ) : rexp (-x ^ 2 / 2) = rexp (-(1/2) * x ^ 2) := by
  congr 1; ring

/-- `gaussian_cos_moment_zero` restated in the `-(1/2)*x²` form used by IBP. -/
theorem gaussian_cos_moment_zero' (y : ℝ) :
    ∫ x : ℝ, rexp (-(1/2) * x ^ 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) := by
  have h := gaussian_cos_moment_zero y
  simp_rw [exp_half_eq] at h; exact h

/-! #### Gaussian cosine moments via IBP chain

We chain through `C(0) → S(1) → C(2) → S(3) → C(4) → S(5) → C(6) → S(7) → C(8) → S(9) → C(10)`,
where `C(n) = ∫ x^n exp(-x²/2) cos(xy)` and `S(n) = ∫ x^n exp(-x²/2) sin(xy)`. -/

private theorem gaussian_cos_moment_two (y : ℝ) :
    ∫ x : ℝ, x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) * (1 - y ^ 2) := by
  simp_rw [exp_half_eq]
  -- C(2) = ibp_cos_step 1: C(2) = 1*C(0) - y*S(1)
  rw [show (2 : ℕ) = 1 + 1 from rfl, ibp_cos_step 1 le_rfl y]
  simp only [Nat.cast_one, show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul, pow_one,
    show (1 : ℕ) + 1 = 2 from rfl]
  rw [sin_moment_one, gaussian_cos_moment_zero']
  ring

private theorem gaussian_cos_moment_two' (y : ℝ) :
    ∫ x : ℝ, x ^ 2 * rexp (-(1/2) * x ^ 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) * (1 - y ^ 2) := by
  have h := gaussian_cos_moment_two y; simp_rw [exp_half_eq] at h; exact h

private theorem gaussian_cos_moment_four (y : ℝ) :
    ∫ x : ℝ, x ^ 4 * rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) * (y ^ 4 - 6 * y ^ 2 + 3) := by
  simp_rw [exp_half_eq]
  -- C(4) = 3*C(2) - y*S(3)
  change ∫ x : ℝ, x ^ (3 + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y) = _
  rw [ibp_cos_step 3 (by norm_num) y]
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show (3 : ℕ) = 2 + 1 from rfl,
    Nat.cast_ofNat]
  -- expand S(3) via IBP
  rw [ibp_sin_step 2 (by norm_num) y]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.cast_ofNat, pow_one]
  rw [sin_moment_one, gaussian_cos_moment_zero', gaussian_cos_moment_two']
  ring

private theorem gaussian_cos_moment_four' (y : ℝ) :
    ∫ x : ℝ, x ^ 4 * rexp (-(1/2) * x ^ 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) * (y ^ 4 - 6 * y ^ 2 + 3) := by
  have h := gaussian_cos_moment_four y; simp_rw [exp_half_eq] at h; exact h

/-- Sine moment helper: `S(3) = 2*S(1) + y*C(2)`, fully evaluated. -/
theorem sin_moment_three (y : ℝ) :
    ∫ x : ℝ, x ^ 3 * rexp (-(1/2) * x ^ 2) * sin (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) * (3 * y - y ^ 3) := by
  change ∫ x : ℝ, x ^ (2 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y) = _
  rw [ibp_sin_step 2 (by norm_num) y]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.cast_ofNat, pow_one]
  rw [sin_moment_one, gaussian_cos_moment_zero', gaussian_cos_moment_two']
  ring

private theorem gaussian_cos_moment_six (y : ℝ) :
    ∫ x : ℝ, x ^ 6 * rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) *
      (-y ^ 6 + 15 * y ^ 4 - 45 * y ^ 2 + 15) := by
  simp_rw [exp_half_eq]
  -- C(6) = 5*C(4) - y*S(5)
  change ∫ x : ℝ, x ^ (5 + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y) = _
  rw [ibp_cos_step 5 (by norm_num) y]
  simp only [show (5 : ℕ) - 1 = 4 from rfl, Nat.cast_ofNat]
  -- S(5) = 4*S(3) + y*C(4)
  change 5 * (∫ x : ℝ, x ^ 4 * rexp (-(1/2) * x ^ 2) * cos (x * y)) -
    y * (∫ x : ℝ, x ^ (4 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) = _
  rw [ibp_sin_step 4 (by norm_num) y]
  simp only [show (4 : ℕ) - 1 = 3 from rfl, Nat.cast_ofNat]
  rw [sin_moment_three, gaussian_cos_moment_four']
  ring

private theorem gaussian_cos_moment_six' (y : ℝ) :
    ∫ x : ℝ, x ^ 6 * rexp (-(1/2) * x ^ 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) *
      (-y ^ 6 + 15 * y ^ 4 - 45 * y ^ 2 + 15) := by
  have h := gaussian_cos_moment_six y; simp_rw [exp_half_eq] at h; exact h

/-- Sine moment helper: `S(5)`, fully evaluated. -/
theorem sin_moment_five (y : ℝ) :
    ∫ x : ℝ, x ^ 5 * rexp (-(1/2) * x ^ 2) * sin (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) *
      (y ^ 5 - 10 * y ^ 3 + 15 * y) := by
  change ∫ x : ℝ, x ^ (4 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y) = _
  rw [ibp_sin_step 4 (by norm_num) y]
  simp only [show (4 : ℕ) - 1 = 3 from rfl, Nat.cast_ofNat]
  rw [sin_moment_three, gaussian_cos_moment_four']
  ring

private theorem gaussian_cos_moment_eight (y : ℝ) :
    ∫ x : ℝ, x ^ 8 * rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) *
      (y ^ 8 - 28 * y ^ 6 + 210 * y ^ 4 - 420 * y ^ 2 + 105) := by
  simp_rw [exp_half_eq]
  -- C(8) = 7*C(6) - y*S(7)
  change ∫ x : ℝ, x ^ (7 + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y) = _
  rw [ibp_cos_step 7 (by norm_num) y]
  simp only [show (7 : ℕ) - 1 = 6 from rfl, Nat.cast_ofNat]
  -- S(7) = 6*S(5) + y*C(6)
  change 7 * (∫ x : ℝ, x ^ 6 * rexp (-(1/2) * x ^ 2) * cos (x * y)) -
    y * (∫ x : ℝ, x ^ (6 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) = _
  rw [ibp_sin_step 6 (by norm_num) y]
  simp only [show (6 : ℕ) - 1 = 5 from rfl, Nat.cast_ofNat]
  rw [sin_moment_five, gaussian_cos_moment_six']
  ring

private theorem gaussian_cos_moment_eight' (y : ℝ) :
    ∫ x : ℝ, x ^ 8 * rexp (-(1/2) * x ^ 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) *
      (y ^ 8 - 28 * y ^ 6 + 210 * y ^ 4 - 420 * y ^ 2 + 105) := by
  have h := gaussian_cos_moment_eight y; simp_rw [exp_half_eq] at h; exact h

/-- Sine moment helper: `S(7)`, fully evaluated. -/
private theorem sin_moment_seven (y : ℝ) :
    ∫ x : ℝ, x ^ 7 * rexp (-(1/2) * x ^ 2) * sin (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-(1/2) * y ^ 2) *
      (-y ^ 7 + 21 * y ^ 5 - 105 * y ^ 3 + 105 * y) := by
  change ∫ x : ℝ, x ^ (6 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y) = _
  rw [ibp_sin_step 6 (by norm_num) y]
  simp only [show (6 : ℕ) - 1 = 5 from rfl, Nat.cast_ofNat]
  rw [sin_moment_five, gaussian_cos_moment_six']
  ring

private theorem gaussian_cos_moment_ten (y : ℝ) :
    ∫ x : ℝ, x ^ 10 * rexp (-x ^ 2 / 2) * cos (x * y) =
    Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) *
      (-y ^ 10 + 45 * y ^ 8 - 630 * y ^ 6 + 3150 * y ^ 4 -
        4725 * y ^ 2 + 945) := by
  simp_rw [exp_half_eq]
  -- C(10) = 9*C(8) - y*S(9)
  change ∫ x : ℝ, x ^ (9 + 1) * rexp (-(1/2) * x ^ 2) * cos (x * y) = _
  rw [ibp_cos_step 9 (by norm_num) y]
  simp only [show (9 : ℕ) - 1 = 8 from rfl, Nat.cast_ofNat]
  -- S(9) = 8*S(7) + y*C(8)
  change 9 * (∫ x : ℝ, x ^ 8 * rexp (-(1/2) * x ^ 2) * cos (x * y)) -
    y * (∫ x : ℝ, x ^ (8 + 1) * rexp (-(1/2) * x ^ 2) * sin (x * y)) = _
  rw [ibp_sin_step 8 (by norm_num) y]
  simp only [show (8 : ℕ) - 1 = 7 from rfl, Nat.cast_ofNat]
  rw [sin_moment_seven, gaussian_cos_moment_eight']
  ring

/-- The inner integral identity for Lemma 4.1, equation (27).

    This combines the individual Gaussian cosine moments with the expansion
    h5_unnorm(x)² = 16x¹⁰ - 160x⁸ + 520x⁶ - 600x⁴ + 225x², using linearity
    of the integral to express the result as a linear combination of the
    moment formulas above. The polynomial identity

      16(-y¹⁰+45y⁸-630y⁶+3150y⁴-4725y²+945)
    + (-160)(y⁸-28y⁶+210y⁴-420y²+105)
    + 520(-y⁶+15y⁴-45y²+15)
    + (-600)(y⁴-6y²+3) + 225(1-y²)
    = -16y¹⁰ + 560y⁸ - 6120y⁶ + 24000y⁴ - 28425y² + 4545

    is verified by `ring`. -/
private theorem inner_integral_h5_unnorm_sq_cos (y : ℝ) :
    ∫ x : ℝ, h5_unnorm x ^ 2 * Real.exp (-x ^ 2 / 2) *
      Real.cos (x * y) =
    Real.sqrt (2 * Real.pi) * Real.exp (- y ^ 2 / 2) *
      (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
       24000 * y ^ 4 - 28425 * y ^ 2 + 4545) := by
  -- Expand h5_unnorm² and split into monomial integrals
  have exp_rw : ∀ x : ℝ, rexp (-x ^ 2 / 2) = rexp (-(1/2) * x ^ 2) := by
    intro x; congr 1; ring
  -- Integrability helpers
  have pow_cos_int : ∀ k : ℕ, ∀ c : ℝ,
      Integrable (fun x : ℝ => c * x ^ k * rexp (-x ^ 2 / 2) * cos (x * y)) := by
    intro k c
    have hg := integrable_pow_mul_exp_half k
    -- |c * x^k * exp(-x²/2) * cos(xy)| ≤ |c| * |x^k * exp(-(1/2)*x²)|
    have hint1 : Integrable (fun x : ℝ => x ^ k * rexp (-x ^ 2 / 2) * cos (x * y)) := by
      apply hg.norm.mono' (by fun_prop : AEStronglyMeasurable _ _)
      apply Filter.Eventually.of_forall; intro x
      rw [exp_rw x]
      simp only [Real.norm_eq_abs]
      calc |x ^ k * rexp (-(1/2) * x ^ 2) * cos (x * y)|
          = |x ^ k * rexp (-(1/2) * x ^ 2)| * |cos (x * y)| := abs_mul _ _
        _ ≤ |x ^ k * rexp (-(1/2) * x ^ 2)| * 1 :=
            mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
        _ = |x ^ k * rexp (-(1/2) * x ^ 2)| := mul_one _
    exact (hint1.const_mul c).congr (Filter.Eventually.of_forall fun x => by ring)
  -- Expand h5_unnorm² into monomials
  have heq : (fun x : ℝ => h5_unnorm x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y)) =
      fun x => ((16 * x ^ 10 * rexp (-x ^ 2 / 2) * cos (x * y) +
        (-160) * x ^ 8 * rexp (-x ^ 2 / 2) * cos (x * y)) +
        (520 * x ^ 6 * rexp (-x ^ 2 / 2) * cos (x * y) +
        (-600) * x ^ 4 * rexp (-x ^ 2 / 2) * cos (x * y))) +
        225 * x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y) := by
    ext x; simp [h5_unnorm]; ring
  rw [heq]
  -- Split the sum integral into individual integrals using integral_add'
  have i10 := pow_cos_int 10 16
  have i8 := pow_cos_int 8 (-160)
  have i6 := pow_cos_int 6 520
  have i4 := pow_cos_int 4 (-600)
  have i2 := pow_cos_int 2 225
  conv_lhs =>
    rw [show (fun x => (16 * x ^ 10 * rexp (-x ^ 2 / 2) * cos (x * y) +
        (-160) * x ^ 8 * rexp (-x ^ 2 / 2) * cos (x * y) +
        (520 * x ^ 6 * rexp (-x ^ 2 / 2) * cos (x * y) +
        (-600) * x ^ 4 * rexp (-x ^ 2 / 2) * cos (x * y))) +
        225 * x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y)) =
      ((fun x => 16 * x ^ 10 * rexp (-x ^ 2 / 2) * cos (x * y)) +
       (fun x => (-160) * x ^ 8 * rexp (-x ^ 2 / 2) * cos (x * y)) +
       ((fun x => 520 * x ^ 6 * rexp (-x ^ 2 / 2) * cos (x * y)) +
        (fun x => (-600) * x ^ 4 * rexp (-x ^ 2 / 2) * cos (x * y)))) +
      (fun x => 225 * x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y)) from rfl]
  rw [integral_add' ((i10.add i8).add (i6.add i4)) i2,
      integral_add' (i10.add i8) (i6.add i4),
      integral_add' i10 i8, integral_add' i6 i4]
  -- Factor out constants from each integral
  simp only [show ∀ (c : ℝ) (k : ℕ), (fun x : ℝ => c * x ^ k * rexp (-x ^ 2 / 2) * cos (x * y)) =
      fun x => c * (x ^ k * rexp (-x ^ 2 / 2) * cos (x * y)) from
    fun c k => funext (fun x => by ring)]
  simp only [integral_const_mul]
  -- Substitute the individual moment formulas
  rw [gaussian_cos_moment_ten, gaussian_cos_moment_eight,
      gaussian_cos_moment_six, gaussian_cos_moment_four,
      gaussian_cos_moment_two]
  ring

/-- The product h5_unnorm(y)² · P(y) as a polynomial in y,
    where P is the polynomial from the inner integral. The product
    reduces to a degree-20 polynomial with the following coefficients. -/
private theorem integral_product_poly :
    ∫ y : ℝ, (h5_unnorm y ^ 2 *
      (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
       24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) *
      Real.exp (-y ^ 2) = 176400 * Real.sqrt Real.pi := by
  let f : ℝ → ℕ → ℝ → ℝ := fun c k x => c * x ^ k * Real.exp (-x ^ 2)
  have intf : ∀ c k, Integrable (f c k) := fun c k =>
    integrable_const_mul_pow_mul_exp c k
  -- Expand the integrand into monomials
  have heq : (fun y => (h5_unnorm y ^ 2 *
      (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
       24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) *
      Real.exp (-y ^ 2)) =
    (f 1022625 2 + (f (-9122625) 4 + (f 24818400 6 +
      (f (-31285200) 8 + (f 20898720 10 + (f (-7816800) 12 +
      (f 1664000 14 + (f (-195840) 16 + (f 11520 18 +
      f (-256) 20))))))))) := by
    ext y; simp only [f, Pi.add_apply, h5_unnorm]; ring
  calc ∫ y, (h5_unnorm y ^ 2 *
      (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
       24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) *
      Real.exp (-y ^ 2)
      = ∫ y, (f 1022625 2 + (f (-9122625) 4 + (f 24818400 6 +
        (f (-31285200) 8 + (f 20898720 10 + (f (-7816800) 12 +
        (f 1664000 14 + (f (-195840) 16 + (f 11520 18 +
        f (-256) 20))))))))) y := by congr 1
    _ = (∫ y, f 1022625 2 y) + ∫ y, (f (-9122625) 4 +
        (f 24818400 6 + (f (-31285200) 8 + (f 20898720 10 +
        (f (-7816800) 12 + (f 1664000 14 + (f (-195840) 16 +
        (f 11520 18 + f (-256) 20)))))))) y :=
        integral_add' (intf 1022625 2) ((intf (-9122625) 4).add
          ((intf 24818400 6).add ((intf (-31285200) 8).add
          ((intf 20898720 10).add ((intf (-7816800) 12).add
          ((intf 1664000 14).add ((intf (-195840) 16).add
          ((intf 11520 18).add (intf (-256) 20)))))))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ∫ y, (f 24818400 6 + (f (-31285200) 8 + (f 20898720 10 +
        (f (-7816800) 12 + (f 1664000 14 + (f (-195840) 16 +
        (f 11520 18 + f (-256) 20))))))) y) := by
        congr 1; exact integral_add' (intf (-9122625) 4)
          ((intf 24818400 6).add ((intf (-31285200) 8).add
          ((intf 20898720 10).add ((intf (-7816800) 12).add
          ((intf 1664000 14).add ((intf (-195840) 16).add
          ((intf 11520 18).add (intf (-256) 20))))))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ∫ y, (f (-31285200) 8 +
        (f 20898720 10 + (f (-7816800) 12 + (f 1664000 14 +
        (f (-195840) 16 + (f 11520 18 +
        f (-256) 20)))))) y)) := by
        congr 2; exact integral_add' (intf 24818400 6)
          ((intf (-31285200) 8).add ((intf 20898720 10).add
          ((intf (-7816800) 12).add ((intf 1664000 14).add
          ((intf (-195840) 16).add ((intf 11520 18).add
          (intf (-256) 20)))))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ∫ y, (f 20898720 10 + (f (-7816800) 12 +
        (f 1664000 14 + (f (-195840) 16 + (f 11520 18 +
        f (-256) 20))))) y))) := by
        congr 3; exact integral_add' (intf (-31285200) 8)
          ((intf 20898720 10).add ((intf (-7816800) 12).add
          ((intf 1664000 14).add ((intf (-195840) 16).add
          ((intf 11520 18).add (intf (-256) 20))))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ((∫ y, f 20898720 10 y) + ∫ y, (f (-7816800) 12 +
        (f 1664000 14 + (f (-195840) 16 + (f 11520 18 +
        f (-256) 20)))) y)))) := by
        congr 4; exact integral_add' (intf 20898720 10)
          ((intf (-7816800) 12).add ((intf 1664000 14).add
          ((intf (-195840) 16).add ((intf 11520 18).add
          (intf (-256) 20)))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ((∫ y, f 20898720 10 y) + ((∫ y, f (-7816800) 12 y) +
        ∫ y, (f 1664000 14 + (f (-195840) 16 + (f 11520 18 +
        f (-256) 20))) y))))) := by
        congr 5; exact integral_add' (intf (-7816800) 12)
          ((intf 1664000 14).add ((intf (-195840) 16).add
          ((intf 11520 18).add (intf (-256) 20))))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ((∫ y, f 20898720 10 y) + ((∫ y, f (-7816800) 12 y) +
        ((∫ y, f 1664000 14 y) + ∫ y, (f (-195840) 16 +
        (f 11520 18 + f (-256) 20)) y)))))) := by
        congr 6; exact integral_add' (intf 1664000 14)
          ((intf (-195840) 16).add ((intf 11520 18).add
          (intf (-256) 20)))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ((∫ y, f 20898720 10 y) + ((∫ y, f (-7816800) 12 y) +
        ((∫ y, f 1664000 14 y) + ((∫ y, f (-195840) 16 y) +
        ∫ y, (f 11520 18 + f (-256) 20) y))))))) := by
        congr 7; exact integral_add' (intf (-195840) 16)
          ((intf 11520 18).add (intf (-256) 20))
    _ = (∫ y, f 1022625 2 y) + ((∫ y, f (-9122625) 4 y) +
        ((∫ y, f 24818400 6 y) + ((∫ y, f (-31285200) 8 y) +
        ((∫ y, f 20898720 10 y) + ((∫ y, f (-7816800) 12 y) +
        ((∫ y, f 1664000 14 y) + ((∫ y, f (-195840) 16 y) +
        ((∫ y, f 11520 18 y) +
        ∫ y, f (-256) 20 y)))))))) := by
        congr 8; exact integral_add' (intf 11520 18)
          (intf (-256) 20)
    _ = 176400 * Real.sqrt Real.pi := by
        simp only [f]
        rw [integral_const_mul_pow_mul_exp_eq 1022625 1,
            integral_const_mul_pow_mul_exp_eq (-9122625) 2,
            integral_const_mul_pow_mul_exp_eq 24818400 3,
            integral_const_mul_pow_mul_exp_eq (-31285200) 4,
            integral_const_mul_pow_mul_exp_eq 20898720 5,
            integral_const_mul_pow_mul_exp_eq (-7816800) 6,
            integral_const_mul_pow_mul_exp_eq 1664000 7,
            integral_const_mul_pow_mul_exp_eq (-195840) 8,
            integral_const_mul_pow_mul_exp_eq 11520 9,
            integral_const_mul_pow_mul_exp_eq (-256) 10]
        rw [gaussianMoment_one, gaussianMoment_two,
            gaussianMoment_three, gaussianMoment_four,
            gaussianMoment_five, gaussianMoment_six,
            gaussianMoment_seven, gaussianMoment_eight,
            gaussianMoment_nine, gaussianMoment_ten]
        ring

/-- The unnormalized double integral:
    ∫∫ h5_unnorm(x)² h5_unnorm(y)² exp(-(x²+y²)/2) cos(xy) dx dy
    = 176400 √2 π.

    Proof strategy: apply Fubini, compute the inner x-integral using
    the contour-shift formula (inner_integral_h5_unnorm_sq_cos),
    then compute the resulting y-integral using Gaussian moments
    (integral_product_poly). -/
private theorem integral_h5_unnorm_sq_double :
    ∫ (a : ℝ × ℝ),
      h5_unnorm a.1 ^ 2 * h5_unnorm a.2 ^ 2 *
      rexp (-(a.1 ^ 2 + a.2 ^ 2) / 2) * cos (a.1 * a.2) =
    176400 * Real.sqrt 2 * Real.pi := by
  -- Step 1: Apply Fubini to convert to iterated integral
  have hfub : ∫ (a : ℝ × ℝ),
      h5_unnorm a.1 ^ 2 * h5_unnorm a.2 ^ 2 *
      rexp (-(a.1 ^ 2 + a.2 ^ 2) / 2) * cos (a.1 * a.2) =
      ∫ y, ∫ x, h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
      rexp (-(x ^ 2 + y ^ 2) / 2) * cos (x * y) := by
    -- Apply Fubini's theorem (symmetric version)
    have hint : Integrable (fun a : ℝ × ℝ =>
        h5_unnorm a.1 ^ 2 * h5_unnorm a.2 ^ 2 *
        rexp (-(a.1 ^ 2 + a.2 ^ 2) / 2) * cos (a.1 * a.2)) volume := by
      rw [Measure.volume_eq_prod]
      -- x^k * exp(-x²/2) is integrable for any k
      have pow_int_half : ∀ k : ℕ, Integrable (fun x : ℝ =>
          x ^ (k : ℕ) * rexp (-(1/2) * x ^ 2)) := by
        intro k
        have hk : -1 < (↑k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
        have := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2) hk
        exact this.congr (Filter.Eventually.of_forall fun x => by simp [Real.rpow_natCast])
      -- Rewrite exp(-x²/2) = exp(-(1/2)*x²)
      have exp_rw : ∀ x : ℝ, rexp (-x ^ 2 / 2) = rexp (-(1/2) * x ^ 2) := by
        intro x; congr 1; ring
      -- g(t) = h5_unnorm(t)^2 * exp(-t^2/2) is integrable
      have hg : Integrable (fun t : ℝ => h5_unnorm t ^ 2 * rexp (-t ^ 2 / 2)) := by
        have heq : (fun t : ℝ => h5_unnorm t ^ 2 * rexp (-t ^ 2 / 2)) =
            fun t => (16 * t ^ 10 - 160 * t ^ 8 + 520 * t ^ 6 -
              600 * t ^ 4 + 225 * t ^ 2) * rexp (-(1/2) * t ^ 2) := by
          ext t; simp [h5_unnorm, exp_rw]; ring
        rw [heq]
        have mk_int : ∀ (c : ℝ) (k : ℕ), Integrable (fun x : ℝ =>
            c * x ^ k * rexp (-(1/2) * x ^ 2)) :=
          fun c k => ((pow_int_half k).const_mul c).congr
            (Filter.Eventually.of_forall fun x => by ring)
        have sum_eq : (fun t : ℝ => (16 * t ^ 10 - 160 * t ^ 8 + 520 * t ^ 6 -
              600 * t ^ 4 + 225 * t ^ 2) * rexp (-(1/2) * t ^ 2)) =
            fun t => (16 * t ^ 10 * rexp (-(1/2) * t ^ 2) +
              (-160) * t ^ 8 * rexp (-(1/2) * t ^ 2)) +
              (520 * t ^ 6 * rexp (-(1/2) * t ^ 2) +
              (-600) * t ^ 4 * rexp (-(1/2) * t ^ 2)) +
              225 * t ^ 2 * rexp (-(1/2) * t ^ 2) := by
          ext t; ring
        rw [sum_eq]
        exact (((mk_int 16 10).add (mk_int (-160) 8)).add
          ((mk_int 520 6).add (mk_int (-600) 4))).add (mk_int 225 2)
      -- Bound: |f(x,y)| ≤ g(x) * g(y) since |cos| ≤ 1
      have hbound : Integrable (fun a : ℝ × ℝ =>
          (h5_unnorm a.1 ^ 2 * rexp (-a.1 ^ 2 / 2)) *
          (h5_unnorm a.2 ^ 2 * rexp (-a.2 ^ 2 / 2)))
          (volume.prod volume) :=
        hg.mul_prod hg
      have hcont : Continuous h5_unnorm := by unfold h5_unnorm; fun_prop
      have hasm : AEStronglyMeasurable (fun a : ℝ × ℝ =>
          h5_unnorm a.1 ^ 2 * h5_unnorm a.2 ^ 2 *
          rexp (-(a.1 ^ 2 + a.2 ^ 2) / 2) * cos (a.1 * a.2))
          (volume.prod volume) := by
        apply AEStronglyMeasurable.mul
        · apply AEStronglyMeasurable.mul
          · apply AEStronglyMeasurable.mul
            · exact ((hcont.comp continuous_fst).pow 2).aestronglyMeasurable
            · exact ((hcont.comp continuous_snd).pow 2).aestronglyMeasurable
          · have : Continuous (fun a : ℝ × ℝ => rexp (-(a.1 ^ 2 + a.2 ^ 2) / 2)) := by
              apply Real.continuous_exp.comp
              apply Continuous.div_const
              apply Continuous.neg
              exact (continuous_fst.pow 2).add (continuous_snd.pow 2)
            exact this.aestronglyMeasurable
        · exact (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable
      exact hbound.mono' hasm
        (Filter.Eventually.of_forall fun ⟨x, y⟩ => by
          simp only
          rw [Real.norm_eq_abs]
          have hexp : rexp (-(x ^ 2 + y ^ 2) / 2) = rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp]
          have hsq_x : 0 ≤ h5_unnorm x ^ 2 := sq_nonneg _
          have hsq_y : 0 ≤ h5_unnorm y ^ 2 := sq_nonneg _
          have hexp_x : 0 ≤ rexp (-x ^ 2 / 2) := (Real.exp_pos _).le
          have hexp_y : 0 ≤ rexp (-y ^ 2 / 2) := (Real.exp_pos _).le
          have hprod_nn : 0 ≤ h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
              (rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2)) :=
            mul_nonneg (mul_nonneg hsq_x hsq_y) (mul_nonneg hexp_x hexp_y)
          calc |h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
                (rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2)) * cos (x * y)|
              = |h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
                (rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2))| * |cos (x * y)| :=
                abs_mul _ _
            _ ≤ |h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
                (rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2))| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = h5_unnorm x ^ 2 * rexp (-x ^ 2 / 2) *
                (h5_unnorm y ^ 2 * rexp (-y ^ 2 / 2)) := by
                rw [mul_one, abs_of_nonneg hprod_nn]; ring)
    rw [Measure.volume_eq_prod]
    exact integral_prod_symm _ hint
  rw [hfub]
  -- Step 2: Factor out y-dependent terms from inner integral
  have hfactor : ∀ y : ℝ, (∫ x, h5_unnorm x ^ 2 *
      h5_unnorm y ^ 2 * rexp (-(x ^ 2 + y ^ 2) / 2) *
      cos (x * y)) = h5_unnorm y ^ 2 * rexp (-y ^ 2 / 2) *
      (∫ x, h5_unnorm x ^ 2 * rexp (-x ^ 2 / 2) *
      cos (x * y)) := by
    intro y
    have : (fun x => h5_unnorm x ^ 2 * h5_unnorm y ^ 2 *
        rexp (-(x ^ 2 + y ^ 2) / 2) * cos (x * y)) =
      fun x => h5_unnorm y ^ 2 * rexp (-y ^ 2 / 2) *
        (h5_unnorm x ^ 2 * rexp (-x ^ 2 / 2) * cos (x * y)) := by
      ext x
      have hexp : rexp (-(x ^ 2 + y ^ 2) / 2) =
          rexp (-x ^ 2 / 2) * rexp (-y ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]; ring
    rw [this, integral_const_mul]
  simp_rw [hfactor]
  -- Step 3: Substitute the inner integral result
  simp_rw [inner_integral_h5_unnorm_sq_cos]
  -- Step 4: Simplify to get the product polynomial integral
  -- Rewrite to pull out sqrt(2*pi) and combine exp factors
  have hsimpl : (fun y => h5_unnorm y ^ 2 * rexp (-y ^ 2 / 2) *
      (Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) *
        (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
         24000 * y ^ 4 - 28425 * y ^ 2 + 4545))) =
      fun y => Real.sqrt (2 * Real.pi) *
      ((h5_unnorm y ^ 2 *
        (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
         24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) *
        rexp (-y ^ 2)) := by
    ext y
    have hexp2 : rexp (-y ^ 2 / 2) * rexp (-y ^ 2 / 2) =
        rexp (-y ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have : h5_unnorm y ^ 2 * rexp (-y ^ 2 / 2) *
      (Real.sqrt (2 * Real.pi) * rexp (-y ^ 2 / 2) *
        (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
         24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) =
      Real.sqrt (2 * Real.pi) *
      ((h5_unnorm y ^ 2 *
        (-16 * y ^ 10 + 560 * y ^ 8 - 6120 * y ^ 6 +
         24000 * y ^ 4 - 28425 * y ^ 2 + 4545)) *
        (rexp (-y ^ 2 / 2) * rexp (-y ^ 2 / 2))) := by ring
    rw [this, hexp2]
  rw [hsimpl, integral_const_mul, integral_product_poly]
  -- Now: sqrt(2*pi) * (176400 * sqrt(pi)) = 176400 * sqrt(2) * pi
  rw [Real.sqrt_mul (le_of_lt two_pos)]
  have hsqpi : Real.sqrt π ^ 2 = π := Real.sq_sqrt (le_of_lt Real.pi_pos)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- **Lemma 4.1, equation (27)** (normalized version):
    ∫∫ h₅(x)² h₅(y)² exp(-(x²+y²)/2) cos(xy) dx dy,
    expressed in terms of the normalization constant. -/
theorem lemma_4_1_eq27 :
    ∫ p : ℝ × ℝ, h5 p.1 ^ 2 * h5 p.2 ^ 2 *
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * Real.cos (p.1 * p.2) =
    176400 * Real.sqrt 2 * Real.pi / h5_norm_const ^ 4 := by
  have heq : (fun p : ℝ × ℝ =>
      h5 p.1 ^ 2 * h5 p.2 ^ 2 *
      rexp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * cos (p.1 * p.2)) =
      fun p => (1 / h5_norm_const ^ 4) *
      (h5_unnorm p.1 ^ 2 * h5_unnorm p.2 ^ 2 *
      rexp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * cos (p.1 * p.2)) := by
    ext ⟨x, y⟩; simp [h5, div_pow]; ring
  rw [heq, MeasureTheory.integral_const_mul,
      integral_h5_unnorm_sq_double]
  ring

/-! ## Content merged from Lemma41_attempt2 -/

/-- Unnormalized `h5` Fourier/sine identity (Braverman equation 55, unnormalized).
    ∫ h5_unnorm(x) · exp(-x²/2) · sin(xy) dx = √(2π) · exp(-y²/2) · h5_unnorm(y) -/
theorem h5_unnorm_fourier_sin (y : ℝ) :
    ∫ x : ℝ, h5_unnorm x * Real.exp (-x ^ 2 / 2) * Real.sin (x * y)
      = Real.sqrt (2 * Real.pi) * Real.exp (-y ^ 2 / 2) * h5_unnorm y := by
  -- Rewrite exp form
  have exp_rw : ∀ x : ℝ, rexp (-x ^ 2 / 2) = rexp (-(1/2) * x ^ 2) := by
    intro x; congr 1; ring
  simp_rw [exp_rw]
  have i5 :
      Integrable (fun x : ℝ =>
        4 * x ^ 5 * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) :=
    ((integrable_pow_mul_exp_half_sin 5 y).const_mul 4).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have i3 :
      Integrable (fun x : ℝ =>
        (-20) * x ^ 3 * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) :=
    ((integrable_pow_mul_exp_half_sin 3 y).const_mul (-20)).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have i1 :
      Integrable (fun x : ℝ =>
        15 * x * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) :=
    ((integrable_pow_mul_exp_half_sin 1 y).const_mul 15).congr
      (Filter.Eventually.of_forall fun x => by ring)
  have heq :
      (fun x : ℝ => h5_unnorm x * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) =
        (fun x => 4 * x ^ 5 * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) +
        (fun x => (-20) * x ^ 3 * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) +
        (fun x => 15 * x * Real.exp (-(1/2) * x ^ 2) * Real.sin (x * y)) := by
    funext x
    simp [h5_unnorm]
    ring
  rw [heq]
  rw [integral_add' (i5.add i3) i1]
  rw [integral_add' i5 i3]
  -- Now substitute the moment formulas
  -- sin_moment_five: ∫ x^5 exp(-(1/2)x²) sin(xy) = √(2π) exp(-(1/2)y²) (y^5 - 10y³ + 15y)
  -- sin_moment_three: ∫ x^3 exp(-(1/2)x²) sin(xy) = √(2π) exp(-(1/2)y²) (3y - y³)
  -- sin_moment_one: ∫ x exp(-(1/2)x²) sin(xy) = y * ∫ exp(-(1/2)x²) cos(xy)
  --                                              = y * √(2π) exp(-(1/2)y²)
  -- Factor out constants from each integral
  rw [show (fun x => 4 * x ^ 5 * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) =
      fun x => 4 * (x ^ 5 * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) from
    funext fun x => by ring,
    show (fun x => (-20) * x ^ 3 * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) =
      fun x => (-20) * (x ^ 3 * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) from
    funext fun x => by ring,
    show (fun x => 15 * x * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) =
      fun x => 15 * (x * rexp (-(1 / 2) * x ^ 2) * sin (x * y)) from
    funext fun x => by ring]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [sin_moment_five, sin_moment_three, sin_moment_one, gaussian_cos_moment_zero']
  simp [h5_unnorm]
  ring

/-- Braverman equation (55), normalized version:
    ∫ h5(x) · exp(-x²/2) · sin(xy) dx = √(2π) · exp(-y²/2) · h5(y) -/
theorem lemma_4_4_eq55 (y : ℝ) :
    ∫ x : ℝ, h5 x * Real.exp (-x ^ 2 / 2) * Real.sin (x * y)
      = Real.sqrt (2 * Real.pi) * Real.exp (-y ^ 2 / 2) * h5 y := by
  have exp_rw : ∀ x : ℝ, rexp (-x ^ 2 / 2) = rexp (-(1/2) * x ^ 2) := by
    intro x; congr 1; ring
  have heq :
      (fun x : ℝ => h5 x * Real.exp (-x ^ 2 / 2) * Real.sin (x * y)) =
      (fun x : ℝ =>
        (1 / h5_norm_const) *
          (h5_unnorm x * Real.exp (-x ^ 2 / 2) * Real.sin (x * y))) := by
    funext x
    simp [h5]
    ring
  rw [heq, MeasureTheory.integral_const_mul, h5_unnorm_fourier_sin]
  simp [h5]
  ring

end Braverman
