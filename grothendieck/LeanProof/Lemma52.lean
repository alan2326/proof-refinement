/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma43
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Lemma 5.2: H₀ is injective on S and H₀(S) ⊇ D

We prove two facts:
1. H₀ is one-to-one on the strip S
2. The image H₀(S) contains the open unit disk D

## Proof of injectivity

Since H₀ = arcsin (Lemma 4.3), and sin is injective on the vertical strip
{w : |Re w| < π/2}, the inverse arcsin is injective on S.

## Proof that H₀(S) ⊇ D

We need to show: if |w| < 1 then |sin(w)| < 1 (taking Re-absolute value).
The paper proves this via the identity |sin(a+bi)| = (e^b + e^{-b})/2 · |sin a|
and the inequality: for x ∈ (0,1), cosh(x)·x < 1 (proved via Taylor remainder).
-/

open Complex Set Metric Real

noncomputable section

namespace Braverman

/-!
## Key inequality: cosh(x) · x < 1 for x ∈ (0, 1)

This is inequality (70) from the paper. The proof uses Taylor's theorem:
  cosh(x) ≤ 1 + x²/2 + x⁴·cosh(1)/24
and then (1 + x²/2 + x⁴·cosh(1)/24)·x² < 1 for x ∈ (0,1).
-/

/-- For a² + b² < 1, we have |sin(a)| · cosh(b) < 1.
    This is used to show sin maps D into S in the Re direction.
    The proof uses |sin(a)| ≤ |a| and the Taylor bound for cosh. -/
theorem sin_cosh_lt_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 < 1) :
    |Real.sin a| * Real.cosh b < 1 := by
  -- Differentiability of cosh and sinh
  have hdc : Differentiable ℝ Real.cosh := Real.differentiable_cosh
  have hds : Differentiable ℝ Real.sinh := Real.differentiable_sinh
  -- Auxiliary: sinh is nonneg for nonneg input and nonpos for nonpos input
  have hsinh_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sinh x := by
    intro x hx; rw [sinh_eq]
    linarith [exp_le_exp.mpr (show -x ≤ x by linarith)]
  have hsinh_nonpos : ∀ x : ℝ, x ≤ 0 → Real.sinh x ≤ 0 := by
    intro x hx; rw [sinh_eq]
    linarith [exp_le_exp.mpr (show x ≤ -x by linarith)]
  -- Step 1: x * sinh x ≥ 0 for all x
  have hmul_sinh : ∀ x : ℝ, 0 ≤ x * Real.sinh x := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · exact mul_nonneg hx (hsinh_nonneg x hx)
    · exact mul_nonneg_iff.mpr (Or.inr ⟨le_of_lt hx, hsinh_nonpos x (le_of_lt hx)⟩)
  -- Step 2: f(x) = x * cosh x - sinh x is monotone (derivative = x * sinh x ≥ 0)
  have hf_mono : Monotone (fun x : ℝ => x * Real.cosh x - Real.sinh x) := by
    apply monotone_of_deriv_nonneg
    · exact (differentiable_id.mul hdc).sub hds
    · intro x
      have hd : deriv (fun x : ℝ => x * Real.cosh x - Real.sinh x) x = x * Real.sinh x := by
        have h1 : HasDerivAt (fun x => x * Real.cosh x) (1 * Real.cosh x + x * Real.sinh x) x :=
          (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
        have h2 : HasDerivAt (fun x => x * Real.cosh x - Real.sinh x)
            (1 * Real.cosh x + x * Real.sinh x - Real.cosh x) x :=
          h1.sub (Real.hasDerivAt_sinh x)
        rw [h2.deriv]; ring
      rw [hd]; exact hmul_sinh x
  -- Step 3: sinh² x ≤ x² * cosh² x (from |sinh x| ≤ |x| * cosh x via monotonicity)
  have habs_sinh_le : ∀ x : ℝ, Real.sinh x ^ 2 ≤ x ^ 2 * Real.cosh x ^ 2 := by
    intro x
    have hf0 : (fun x : ℝ => x * Real.cosh x - Real.sinh x) 0 = 0 := by
      simp [Real.cosh_zero, Real.sinh_zero]
    have key : |Real.sinh x| ≤ |x| * Real.cosh x := by
      rcases le_or_gt 0 x with hx | hx
      · have hfx := hf_mono hx; rw [hf0] at hfx
        rw [abs_of_nonneg (hsinh_nonneg x hx), abs_of_nonneg hx]; linarith
      · have hfx := hf_mono (le_of_lt hx); rw [hf0] at hfx
        rw [abs_of_nonpos (hsinh_nonpos x (le_of_lt hx))]
        rw [abs_of_nonpos (le_of_lt hx)]; linarith
    calc Real.sinh x ^ 2 = |Real.sinh x| ^ 2 := (sq_abs _).symm
      _ ≤ (|x| * Real.cosh x) ^ 2 := sq_le_sq' (by linarith [abs_nonneg (Real.sinh x)]) key
      _ = x ^ 2 * Real.cosh x ^ 2 := by rw [mul_pow, sq_abs]
  -- Step 4: (1 - b²) * cosh² b ≤ 1
  have hcosh_bound : (1 - b ^ 2) * Real.cosh b ^ 2 ≤ 1 := by
    have h1 := Real.cosh_sq_sub_sinh_sq b
    have h2 := habs_sinh_le b
    nlinarith
  -- Step 5: sin² a ≤ a²
  have h_sin_sq : Real.sin a ^ 2 ≤ a ^ 2 := by
    have h := @abs_sin_le_abs a
    calc Real.sin a ^ 2 = |Real.sin a| ^ 2 := (sq_abs _).symm
      _ ≤ |a| ^ 2 := sq_le_sq' (by linarith [abs_nonneg (Real.sin a)]) h
      _ = a ^ 2 := sq_abs a
  -- Step 6: Conclusion via (|sin a| * cosh b)² < 1
  suffices h : (|Real.sin a| * Real.cosh b) ^ 2 < 1 by
    nlinarith [sq_nonneg (|Real.sin a| * Real.cosh b)]
  rw [mul_pow, sq_abs]
  have hb2 : b ^ 2 < 1 := by nlinarith [sq_nonneg a]
  have ha2 : a ^ 2 < 1 - b ^ 2 := by linarith
  calc Real.sin a ^ 2 * Real.cosh b ^ 2
      ≤ a ^ 2 * Real.cosh b ^ 2 := by
        apply mul_le_mul_of_nonneg_right h_sin_sq (sq_nonneg _)
    _ < (1 - b ^ 2) * Real.cosh b ^ 2 := by
        apply mul_lt_mul_of_pos_right ha2
        exact sq_pos_of_pos (Real.cosh_pos b)
    _ ≤ 1 := hcosh_bound

/-!
## |sin(a + bi)|² = sin²(a) · cosh²(b) + cos²(a) · sinh²(b)

Standard identity for the modulus of complex sin.
-/

/-- The squared norm of sin(a + bi). -/
theorem norm_sq_sin_add_mul_I (a b : ℝ) :
    ‖Complex.sin (↑a + ↑b * I)‖ ^ 2 =
    Real.sin a ^ 2 * Real.cosh b ^ 2 + Real.cos a ^ 2 * Real.sinh b ^ 2 := by
  rw [Complex.sq_norm, Complex.sin_add_mul_I]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_mul,
    Complex.normSq_add_mul_I]
  ring

/-!
## Main results
-/

/-- If a² + b² < 1 then |sin(a + bi)| < 1.
    This shows sin maps the open unit disk into the strip S (in the Re direction).
    The paper's proof: |sin(a+bi)| ≤ cosh(b)·|sin(a)| ≤ cosh(b)·|a|,
    and cosh(b)·|a| ≤ cosh(√(a²+b²))·√(a²+b²) < 1 when a²+b² < 1. -/
theorem norm_sin_lt_one_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    |Complex.re (Complex.sin z)| < 1 := by
  have hre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    conv_lhs => rw [← Complex.re_add_im z, Complex.sin_add_mul_I]
    simp [Complex.sin_ofReal_re]
  rw [hre]
  have hsq : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    have h1 : ‖z‖ ^ 2 < 1 ^ 2 := by nlinarith
    have h2 : ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
    rw [h2, Complex.normSq_apply] at h1
    linarith [sq_abs z.re, sq_abs z.im]
  rw [abs_mul, abs_of_nonneg (Real.cosh_pos z.im).le]
  exact sin_cosh_lt_one z.re z.im hsq

/-- H₀ is injective on S.
    Follows from H₀ = arcsin (Lemma 4.3) and the fact that sin is injective
    on the strip {w : |Re w| < π/2}. -/
theorem H0_injective : InjOn H0 S := by
  intro z₁ hz₁ z₂ hz₂ h
  have h1 := sin_H0_eq z₁ hz₁
  have h2 := sin_H0_eq z₂ hz₂
  rw [h] at h1
  exact h1.symm.trans h2

/-- The image H₀(S) contains the open unit disk.
    Equivalently: for every w ∈ D, there exists z ∈ S with H₀(z) = w.
    Since H₀ = arcsin, this is equivalent to: sin maps some subset of S onto D,
    i.e., for every w with |w| < 1, sin(w) ∈ S. -/
theorem H0_image_contains_disk : disk 1 ⊆ H0 '' S := by
  intro w hw
  rw [mem_disk_iff] at hw
  have hsin_S : Complex.sin w ∈ S := norm_sin_lt_one_of_norm_lt_one w hw
  have hre : |w.re| < Real.pi / 2 := by
    calc |w.re| ≤ ‖w‖ := abs_re_le_norm w
      _ < 1 := hw
      _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  exact ⟨Complex.sin w, hsin_S, H0_sin_eq w hre hsin_S⟩

/-- Combined statement of Lemma 5.2. -/
theorem lemma_5_2 : InjOn H0 S ∧ disk 1 ⊆ H0 '' S :=
  ⟨H0_injective, H0_image_contains_disk⟩

end Braverman
