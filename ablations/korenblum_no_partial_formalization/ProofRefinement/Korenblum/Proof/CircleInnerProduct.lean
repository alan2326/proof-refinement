import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleExpBridge

/-!
# `Complex.exp(ikθ)` orthogonality and the monomial circle-mean inner pairing

This file is the **off-diagonal** companion to `CircleExpBridge`. Together
with the diagonal seeds (`circleMeanSq_monomial`, `circleMeanSq_const`,
`circleMeanSq_smul` from `CircleExpBridge`), it gives the workspace the
full monomial circle-mean orthogonality needed to assemble the polynomial
Bergman-Parseval identity.

We expose:

* `integral_exp_int_mul_theta_zero` — for `k : ℤ`, `k ≠ 0`,
  `∫ θ in Ioo (-π) π, exp((k : ℂ) * θ * I) = 0`. Proved by reducing the
  `Ioo` set integral to an interval integral, applying
  `integral_exp_mul_complex` with `c = (k : ℂ) * I ≠ 0`, and using
  `exp_int_mul_two_pi_mul_I` to collapse `exp(kIπ) - exp(-kIπ) = 0`.
* `integral_exp_int_mul_theta_eq_two_pi` — the `k = 0` case, giving
  `(2 * Real.pi : ℂ)`.
* `circleMeanInner f g r` — the `ℂ`-valued circle inner product, with the
  conjugate convention `∫ θ, conj(f(...)) · g(...)` (conjugate-linear in
  `f`, linear in `g`).
* `circleMeanInner_monomial_diff` — the headline orthogonality:
  `circleMeanInner (z^m) (z^n) r = 0` for `m ≠ n`.
* `circleMeanInner_monomial_same` — the diagonal:
  `circleMeanInner (z^n) (z^n) r = (2π · r^(2n) : ℂ)`.
* `circleMeanSq_eq_re_circleMeanInner_self` — the bridge to the existing
  `ℝ`-valued `circleMeanSq`:  `circleMeanSq f r = (circleMeanInner f f r).re`.
-/

open MeasureTheory Set Complex intervalIntegral

noncomputable section

namespace ProofRefinement.Korenblum

/-! ## (1) and (2) — circle exp integrals over `Ioo (-π) π`. -/

/-- For nonzero integer `k`, the circle integral of `exp(ikθ)` vanishes. -/
theorem integral_exp_int_mul_theta_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) = 0 := by
  -- Step 1: bridge `Ioo (-π) π` to `Ioc (-π) π` (the volume of the difference is 0).
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_nonneg]
  -- Set up the desired identity: rewrite the integrand as `exp(c * θ)` with `c = kI`.
  set c : ℂ := (k : ℂ) * Complex.I with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def]
    exact mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  -- Pointwise rewrite `(k : ℂ) * (θ : ℂ) * I = c * θ`.
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            Complex.exp (c * (θ : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    congr 1
    rw [hc_def]; ring
  rw [hpt]
  -- Step 2: bridge `Ioo` to interval integral via `Ioc → Ioo` and `integral_of_le`.
  have hbridge :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi, Complex.exp (c * (θ : ℂ)))
        = ∫ θ in -Real.pi..Real.pi, Complex.exp (c * (θ : ℂ)) := by
    rw [intervalIntegral.integral_of_le hπ, integral_Ioc_eq_integral_Ioo]
  rw [hbridge]
  -- Step 3: apply `integral_exp_mul_complex` to evaluate the antiderivative.
  rw [integral_exp_mul_complex hc_ne]
  -- Goal: (exp(c * π) - exp(c * (-π))) / c = 0.
  -- We show `exp(c * π) = exp(c * (-π))`, i.e. `exp(2kIπ) = 1`.
  rw [show ((-Real.pi : ℝ) : ℂ) = -((Real.pi : ℝ) : ℂ) by push_cast; ring]
  have hkey : Complex.exp (c * (Real.pi : ℂ))
      = Complex.exp (c * (-(Real.pi : ℂ))) := by
    have hexp2k : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k
    have hsum : c * (Real.pi : ℂ) - c * (-(Real.pi : ℂ))
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hc_def]; ring
    have :
        Complex.exp (c * (Real.pi : ℂ))
          = Complex.exp (c * (-(Real.pi : ℂ)))
              * Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      linear_combination hsum
    rw [this, hexp2k, mul_one]
  rw [hkey, sub_self, zero_div]

/-- Companion `k = 0` case: the integrand is identically `1`, integral is `2π`. -/
theorem integral_exp_int_mul_theta_eq_two_pi :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        Complex.exp ((0 : ℂ) * (θ : ℂ) * Complex.I))
      = (2 * Real.pi : ℂ) := by
  -- Pointwise: `0 * θ * I = 0`, `exp 0 = 1`.
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          Complex.exp ((0 : ℂ) * (θ : ℂ) * Complex.I))
        = ∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    simp [Complex.exp_zero]
  rw [hpt]
  -- Then `setIntegral_const` and `Real.volume_real_Ioo_of_le`.
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
  -- Goal: (π - -π) • (1 : ℂ) = (2 * π : ℂ).
  rw [Complex.real_smul]
  push_cast
  ring

/-! ## (3) The `ℂ`-valued circle inner product. -/

/-- Circle inner product on `(ℂ → ℂ)`-valued functions at radius `r`. The
convention is **conjugate-linear in `f`, linear in `g`**:
`circleMeanInner f g r = ∫ θ, conj(f(re^{iθ})) · g(re^{iθ})`. -/
noncomputable def circleMeanInner (f g : ℂ → ℂ) (r : ℝ) : ℂ :=
  ∫ θ in Set.Ioo (-Real.pi) Real.pi,
    (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
      * g (Complex.polarCoord.symm (r, θ))

/-! ## (4) Off-diagonal monomial orthogonality. -/

/-- Monomial cross-pairing vanishes off-diagonal. -/
theorem circleMeanInner_monomial_diff
    (m n : ℕ) (hmn : m ≠ n) (r : ℝ) :
    circleMeanInner (fun z => z ^ m) (fun z => z ^ n) r = 0 := by
  unfold circleMeanInner
  -- Step 1: rewrite the integrand as a constant `(r^m * r^n : ℂ)` times
  -- `exp((n - m : ℤ) * θ * I)`.
  set k : ℤ := (n : ℤ) - (m : ℤ) with hk_def
  have hk_ne : k ≠ 0 := by
    rw [hk_def]
    intro h
    apply hmn
    have : (n : ℤ) = (m : ℤ) := by linarith
    exact_mod_cast this.symm
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ m)
            * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n)
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((r : ℂ) ^ m * (r : ℂ) ^ n)
              * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    -- polarCoord.symm (r,θ) = r * exp(θI)
    rw [polarCoord_symm_eq_exp]
    -- Goal: conj((r * exp(θI))^m) * (r * exp(θI))^n
    --       = (r^m * r^n) * exp(k * θ * I)
    -- where k = n - m.
    rw [mul_pow, mul_pow]
    rw [map_mul]
    rw [map_pow, map_pow]
    rw [Complex.conj_ofReal]
    -- conj(exp(θI)) = exp(-θI)
    have hconj : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        = Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_ofReal]
    rw [hconj]
    -- Now: (r^m * exp(-θI)^m) * (r^n * exp(θI)^n) = (r^m * r^n) * exp(k * θ * I)
    -- Reorder: (r^m * r^n) * (exp(-θI)^m * exp(θI)^n)
    -- and combine exponentials.
    -- First, note exp(X)^m = exp(m * X), exp(Y)^n = exp(n * Y).
    rw [show (Complex.exp (-((θ : ℂ) * Complex.I))) ^ m
            = Complex.exp ((m : ℂ) * (-((θ : ℂ) * Complex.I))) from
            (Complex.exp_nat_mul (-((θ : ℂ) * Complex.I)) m).symm]
    rw [show (Complex.exp ((θ : ℂ) * Complex.I)) ^ n
            = Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)) from
            (Complex.exp_nat_mul ((θ : ℂ) * Complex.I) n).symm]
    -- Now goal is:
    --  r^m * exp(m * -(θI)) * (r^n * exp(n * θI)) = r^m * r^n * exp(k * θ * I)
    -- Reorder LHS to (r^m * r^n) * (exp(m*-θI) * exp(n*θI)).
    rw [show ((r : ℂ) ^ m * Complex.exp ((m : ℂ) * (-((θ : ℂ) * Complex.I))))
            * ((r : ℂ) ^ n * Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I)))
            = ((r : ℂ) ^ m * (r : ℂ) ^ n)
              * (Complex.exp ((m : ℂ) * (-((θ : ℂ) * Complex.I)))
                  * Complex.exp ((n : ℂ) * ((θ : ℂ) * Complex.I))) from by ring]
    rw [← Complex.exp_add]
    -- Now goal: (r^m * r^n) * exp(m*(-θI) + n*(θI)) = (r^m * r^n) * exp(k*θ*I)
    congr 1
    -- m*(-θI) + n*(θI) = (n-m)*θ*I = k*θ*I
    simp only [hk_def]
    push_cast
    ring
  rw [hpt]
  -- Step 2: pull the constant outside the integral.
  rw [MeasureTheory.integral_const_mul]
  -- Step 3: integral is zero by (1).
  rw [integral_exp_int_mul_theta_zero hk_ne, mul_zero]

/-! ## (5) Diagonal monomial pairing. -/

/-- Diagonal monomial pairing: `‖z^n‖²` integrates over the circle to
`2π · r^(2n)`. -/
theorem circleMeanInner_monomial_same (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    circleMeanInner (fun z => z ^ n) (fun z => z ^ n) r
      = ((2 * Real.pi * r ^ (2 * n) : ℝ) : ℂ) := by
  unfold circleMeanInner
  -- The integrand simplifies pointwise to the constant `r^(2n) : ℂ`.
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) ((Complex.polarCoord.symm (r, θ) : ℂ) ^ n)
            * (Complex.polarCoord.symm (r, θ) : ℂ) ^ n)
        = ∫ _ in Set.Ioo (-Real.pi) Real.pi, ((r ^ (2 * n) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
    rw [norm_pow, Complex.norm_polarCoord_symm, abs_of_nonneg hr]
    -- Goal: ((r^n)^2 : ℝ → ℂ) = (r^(2n) : ℂ)
    push_cast
    ring
  rw [hpt]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
  -- Goal: (π - -π) • ((r^(2n) : ℝ) : ℂ) = (2π * r^(2n) : ℂ)
  rw [Complex.real_smul]
  push_cast
  ring

/-! ## (6) Bridge to the real-valued `circleMeanSq`. -/

/-- The existing `ℝ`-valued circle mean is the real part of the diagonal
of the new `ℂ`-valued inner product. -/
theorem circleMeanSq_eq_re_circleMeanInner_self (f : ℂ → ℂ) (r : ℝ) :
    circleMeanSq f r = (circleMeanInner f f r).re := by
  unfold circleMeanSq circleMeanInner
  -- Pointwise, `conj(f(...)) * f(...) = (‖f(...)‖² : ℝ → ℂ)`. The integral of the latter
  -- is the (ℝ → ℂ) coercion of the original ℝ-valued circleMeanSq integrand. Then
  -- `.re ((∫ ‖f‖² : ℂ)) = ∫ ‖f‖² : ℝ`.
  have hpt :
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
            * f (Complex.polarCoord.symm (r, θ)))
        = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
            ((‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_eq_norm_sq]
  rw [hpt]
  -- Now the RHS is `(∫ θ, (‖f(...)‖² : ℂ)).re`. Use `integral_complex_ofReal` to
  -- pull the ℝ → ℂ coercion outside the integral.
  rw [integral_complex_ofReal]
  -- Goal: ∫ θ, ‖f(...)‖² = (((∫ θ, ‖f(...)‖² : ℝ) : ℂ)).re
  rw [Complex.ofReal_re]

end ProofRefinement.Korenblum
