import Mathlib
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.MobiusDisk

/-!
# Möbius unit-disk automorphism: derivative + Jacobian-modulus identity

This file pins three theorems on top of `Proof/MobiusDisk.lean`'s algebraic /
analytic primitives:

* `hasDerivAt_mobiusDisk` — pointwise derivative formula
  `(mobiusDisk a)'(z) = -(1 - conj(a) * a) / (1 - conj(a) z)^2`,
* `norm_sq_deriv_mobiusDisk` — modulus identity (positive real Jacobian factor)
  `‖(mobiusDisk a)'(z)‖² = (1 - ‖a‖²)² / ‖1 - conj(a) z‖^4`,
* `deriv_mobiusDisk` — the same as (1) packaged for `deriv`.

The proofs are self-contained against Mathlib (`HasDerivAt.div`,
`HasDerivAt.const_sub`, `HasDerivAt.const_mul`, `Complex.mul_conj`,
`norm_div`, `norm_pow`, ...) plus `Proof.MobiusDisk`'s
`mobiusDisk_denom_ne_zero`.
-/

open Complex

noncomputable section

namespace ProofRefinement.Korenblum

/-- Membership bridge between `UnitDisk` and `‖z‖ < 1`, repeated locally. -/
private theorem mem_unitDisk_iff_norm_lt_one' {z : ℂ} :
    z ∈ UnitDisk ↔ ‖z‖ < 1 := by
  unfold UnitDisk
  rw [Metric.mem_ball, dist_zero_right]

/-- **(1) Pointwise derivative formula.**

For `a ∈ UnitDisk` (so `‖a‖ < 1`) and any `z` with `‖z‖ < 1`,

`(mobiusDisk a)'(z) = -(1 - conj(a) * a) / (1 - conj(a) z)^2`.

This is the exact analytic derivative — the "complex Jacobian" of `φ_a`. The
proof composes the standard quotient rule (`HasDerivAt.div`) on top of two
linear primitives (numerator `a - z` with derivative `-1`, denominator
`1 - conj(a) z` with derivative `-conj(a)`), then simplifies the quotient-rule
output via `convert`+`ring`. -/
theorem hasDerivAt_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    HasDerivAt (mobiusDisk a)
      (-(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2) z := by
  -- Numerator: HasDerivAt (fun w => a - w) (-1) z.
  have h_num : HasDerivAt (fun w : ℂ => a - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub a
  -- Denominator: HasDerivAt (fun w => 1 - conj(a) * w) (-(conj(a))) z.
  have h_mul : HasDerivAt (fun w : ℂ => (starRingEnd ℂ) a * w)
      ((starRingEnd ℂ) a) z := by
    simpa using (hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)
  have h_den : HasDerivAt (fun w : ℂ => 1 - (starRingEnd ℂ) a * w)
      (-(starRingEnd ℂ) a) z := by
    simpa using h_mul.const_sub 1
  -- Denominator non-vanishing.
  have hz_le : ‖z‖ ≤ 1 := le_of_lt hz
  have hD_ne : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    mobiusDisk_denom_ne_zero ha hz_le
  -- Quotient rule.
  have h_div :
      HasDerivAt (fun w : ℂ => (a - w) / (1 - (starRingEnd ℂ) a * w))
        (((-1 : ℂ) * (1 - (starRingEnd ℂ) a * z)
            - (a - z) * (-(starRingEnd ℂ) a))
          / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
    exact h_num.div h_den hD_ne
  -- The function `mobiusDisk a` is definitionally `(a - ·) / (1 - conj(a) · ·)`.
  -- And the derivative simplifies algebraically.
  have h_eq :
      ((-1 : ℂ) * (1 - (starRingEnd ℂ) a * z)
          - (a - z) * (-(starRingEnd ℂ) a))
        / (1 - (starRingEnd ℂ) a * z) ^ 2
      = -(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2 := by
    have hD_sq_ne : (1 - (starRingEnd ℂ) a * z) ^ 2 ≠ 0 := pow_ne_zero 2 hD_ne
    field_simp
    ring
  rw [h_eq] at h_div
  -- mobiusDisk a w = (a - w) / (1 - conj(a) * w) by definition.
  exact h_div

/-- **(2) Modulus identity (the real Jacobian factor).**

For `a ∈ UnitDisk` (so `‖a‖ < 1`) and any `z` with `‖z‖ < 1`,

`‖-(1 - conj(a) * a) / (1 - conj(a) z)^2‖² = (1 - ‖a‖²)² / ‖1 - conj(a) z‖^4`.

This is the explicit positive real Jacobian factor that appears in any
Bergman A² change-of-variables on the disk under `φ_a`. -/
theorem norm_sq_deriv_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    ‖-(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2‖ ^ 2
      = (1 - ‖a‖ ^ 2) ^ 2 / ‖1 - (starRingEnd ℂ) a * z‖ ^ 4 := by
  -- Membership translation.
  have ha_lt : ‖a‖ < 1 := mem_unitDisk_iff_norm_lt_one'.mp ha
  have hz_le : ‖z‖ ≤ 1 := le_of_lt hz
  have hD_ne : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
    mobiusDisk_denom_ne_zero ha hz_le
  -- Norm of denominator is positive.
  have hD_norm_pos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := norm_pos_iff.mpr hD_ne
  -- conj(a) * a = ‖a‖² as a complex number (real part of a ↦ ‖a‖² scalar).
  -- Mathlib: `Complex.mul_conj a : a * (conj a) = ↑(normSq a)`. We use that
  -- `conj a * a = ↑(normSq a)` by commutativity.
  have h_conj_mul : (starRingEnd ℂ) a * a = (Complex.normSq a : ℂ) := by
    rw [mul_comm]
    exact Complex.mul_conj a
  -- 1 - conj(a) * a = (1 - ‖a‖²) as a real-cast complex number.
  have h_one_sub : (1 : ℂ) - (starRingEnd ℂ) a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [h_conj_mul]
    have h_normSq : Complex.normSq a = ‖a‖ ^ 2 := (Complex.sq_norm a).symm
    rw [h_normSq]
    push_cast
    ring
  -- Norm of -(1 - conj(a) * a) = norm of (1 - ‖a‖²) as real.
  have h_pos_real : (0 : ℝ) ≤ 1 - ‖a‖ ^ 2 := by
    have h_a_sq_lt : ‖a‖ ^ 2 < 1 := by
      have : ‖a‖ ^ 2 < 1 ^ 2 := by
        apply sq_lt_sq' <;> [linarith [norm_nonneg a]; exact ha_lt]
      simpa using this
    linarith
  have h_norm_num :
      ‖-(1 - (starRingEnd ℂ) a * a)‖ = 1 - ‖a‖ ^ 2 := by
    rw [norm_neg, h_one_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg h_pos_real]
  -- ‖num/denom^2‖² = (‖num‖ / ‖denom^2‖)² = ‖num‖² / ‖denom^2‖²
  --              = ‖num‖² / (‖denom‖²)² = ‖num‖² / ‖denom‖⁴.
  rw [norm_div, norm_pow, div_pow]
  -- Now: ‖-(1 - conj(a)*a)‖² / (‖1 - conj(a) z‖²)² = (1 - ‖a‖²)² / ‖1-conj(a) z‖⁴.
  rw [h_norm_num]
  -- (‖1 - conj(a) z‖²)² = ‖1 - conj(a) z‖⁴.
  have h_denom_sq : (‖1 - (starRingEnd ℂ) a * z‖ ^ 2) ^ 2
      = ‖1 - (starRingEnd ℂ) a * z‖ ^ 4 := by ring
  rw [h_denom_sq]

/-- **(3) `deriv` form of (1).**

`deriv (mobiusDisk a) z = -(1 - conj(a) * a) / (1 - conj(a) z)^2`. Direct
corollary of (1) via `HasDerivAt.deriv`. -/
theorem deriv_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    deriv (mobiusDisk a) z
      = -(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2 :=
  (hasDerivAt_mobiusDisk ha hz).deriv

end ProofRefinement.Korenblum
