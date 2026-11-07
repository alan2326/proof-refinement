import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.RadialBergman

/-!
# Bridge from `Complex.polarCoord.symm` to `Complex.exp` and monomial circle means

This file builds the first stone in the Bergman-Parseval / monomial-decomposition
direction. We expose:

* `polarCoord_symm_eq_exp` — the pointwise identity
  `(Complex.polarCoord.symm (r, θ) : ℂ) = (r : ℂ) * Complex.exp (θ * Complex.I)`
  for any reals `r`, `θ` (no positivity hypothesis required).
* `norm_polarCoord_symm_pow` — for `r ≥ 0` and `n : ℕ`,
  `‖(Complex.polarCoord.symm (r, θ) : ℂ) ^ n‖ ^ 2 = r ^ (2 * n)`.
* `circleMeanSq_monomial` — for `r ≥ 0` and `n : ℕ`,
  `circleMeanSq (fun z => z ^ n) r = 2 * Real.pi * r ^ (2 * n)`.
* `circleMeanSq_const` — for `c : ℂ`, `r : ℝ`,
  `circleMeanSq (fun _ => c) r = 2 * Real.pi * ‖c‖ ^ 2`.
* `circleMeanSq_smul` — for `c : ℂ`, `f : ℂ → ℂ`, `r : ℝ`,
  `circleMeanSq (fun z => c * f z) r = ‖c‖ ^ 2 * circleMeanSq f r`.

Together (1)–(5) form the seed monomial-orthogonality / scaling block on top
of which the polynomial Parseval identity for `circleMeanSq` is built.
-/

open MeasureTheory Set Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- Bridge identity: the polar-symm point `r·(cos θ + sin θ·I)` equals
`r · exp(θ · I)` as complex numbers, for any reals `r`, `θ`. -/
theorem polarCoord_symm_eq_exp (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ) : ℂ)
      = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, Complex.ofReal_cos,
      Complex.ofReal_sin]

/-- Squared norm of the `n`-th power of the polar-symm point.
For `r ≥ 0` we have `‖(polarCoord.symm (r,θ))^n‖² = r^(2n)`. -/
theorem norm_polarCoord_symm_pow {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (n : ℕ) :
    ‖(Complex.polarCoord.symm (r, θ) : ℂ) ^ n‖ ^ 2 = r ^ (2 * n) := by
  rw [norm_pow]
  rw [Complex.norm_polarCoord_symm]
  -- Goal: |r| ^ n ^ 2 = r ^ (2 * n)
  rw [abs_of_nonneg hr]
  -- Goal: r ^ n ^ 2 = r ^ (2 * n)
  rw [← pow_mul]
  ring_nf

/-- Squared-norm circle mean of the monomial `z^n` at radius `r ≥ 0`. -/
theorem circleMeanSq_monomial {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    circleMeanSq (fun z => z ^ n) r = 2 * Real.pi * r ^ (2 * n) := by
  unfold circleMeanSq
  -- Step 1: rewrite the integrand pointwise as the constant `r^(2n)`.
  have hrewrite :
      (∫ θ in Ioo (-Real.pi) Real.pi,
          ‖(Complex.polarCoord.symm (r, θ) : ℂ) ^ n‖ ^ 2)
        = ∫ _ in Ioo (-Real.pi) Real.pi, (r ^ (2 * n) : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    exact norm_polarCoord_symm_pow hr θ n
  rw [hrewrite]
  -- Step 2: integral of a constant on Ioo (-π) π equals (2π) * constant.
  rw [setIntegral_const]
  -- Goal: (volume.real (Ioo (-π) π)) • r^(2n) = 2 * π * r^(2n)
  rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
  -- Goal: (π - -π) • r^(2n) = 2 * π * r^(2n)
  simp only [smul_eq_mul]
  ring

/-- Squared-norm circle mean of a constant function `(fun _ => c)` at radius `r`. -/
theorem circleMeanSq_const (c : ℂ) (r : ℝ) :
    circleMeanSq (fun _ => c) r = 2 * Real.pi * ‖c‖ ^ 2 := by
  unfold circleMeanSq
  -- Integrand is the constant `‖c‖^2`.
  rw [setIntegral_const]
  rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
  simp only [smul_eq_mul]
  ring

/-- Multiplicative-scalar identity for `circleMeanSq`:
`circleMeanSq (z ↦ c · f z) r = ‖c‖² · circleMeanSq f r`. -/
theorem circleMeanSq_smul (c : ℂ) (f : ℂ → ℂ) (r : ℝ) :
    circleMeanSq (fun z => c * f z) r
      = ‖c‖ ^ 2 * circleMeanSq f r := by
  unfold circleMeanSq
  -- Step 1: rewrite the integrand pointwise: ‖c * f(...)‖² = ‖c‖² * ‖f(...)‖².
  have hrewrite :
      (∫ θ in Ioo (-Real.pi) Real.pi,
          ‖c * f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        = ∫ θ in Ioo (-Real.pi) Real.pi,
            ‖c‖ ^ 2 * ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [norm_mul, mul_pow]
  rw [hrewrite]
  -- Step 2: pull `‖c‖²` out of the integral.
  rw [integral_const_mul]

end ProofRefinement.Korenblum
