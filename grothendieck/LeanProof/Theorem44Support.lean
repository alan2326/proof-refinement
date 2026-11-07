/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import LeanProof.Lemma41
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Theorem 4.4 Support lemmas

Small analytic lemmas used by the endpoint computations:
- Gaussian cosine transform (paper eq. 38)
- Gaussian Hermite sine transform (paper eq. 55)
- Half-line Gaussian moments for eq. 57
- Base value Φ(0) = 4π·log(1+√2)
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## B1. Gaussian cosine transform (paper equation 38) -/

/-- `∫ exp(-y²/2) · cos(xy) dy = √(2π) · exp(-x²/2)`.
    This is the Fourier transform of the standard Gaussian. -/
theorem gaussian_cos_transform (x : ℝ) :
    ∫ y : ℝ, Real.exp (-(y ^ 2) / 2) * Real.cos (x * y)
      = Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2) := by
  simp_rw [show ∀ y : ℝ, -(y ^ 2) / 2 = -(1 / 2) * y ^ 2 from fun y => by ring,
    show ∀ y : ℝ, Real.cos (x * y) = Real.cos (y * x) from fun y => by rw [mul_comm]]
  exact gaussian_cos_moment_zero' x

/-! ## B2. Gaussian Hermite sine transform (paper equation 55) -/

/-- `∫ h₅(y) · exp(-y²/2) · sin(xy) dy = √(2π) · exp(-x²/2) · h₅(x)`.
    This is the key Hermite-Fourier identity. Already proved as `lemma_4_4_eq55`. -/
theorem gaussian_h5_sin_transform (x : ℝ) :
    ∫ y : ℝ, h5 y * Real.exp (-(y ^ 2) / 2) * Real.sin (x * y)
      = Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2) * h5 x := by
  have h := lemma_4_4_eq55 x
  simp_rw [mul_comm _ x] at h
  exact h

/-! ## B3. Half-line Gaussian moments used in equation (57) -/

/-- `∫_{y>0} exp(-y²/2) · y dy = 1`. -/
theorem gaussian_Ioi_y :
    ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(y ^ 2) / 2) * y = 1 := by
  have h_exp_rw : ∀ y : ℝ, Real.exp (-(y ^ 2) / 2) = Real.exp (-(y ^ 2 / 2)) := by
    intro y; congr 1; ring
  simp_rw [h_exp_rw]
  set f := fun y : ℝ => -Real.exp (-(y ^ 2 / 2))
  have h_deriv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x :=
      ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by ring) |>.neg
    simpa [f, mul_comm] using (h1.exp.neg.congr_deriv (by ring))
  have h_tendsto : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = -0 by simp]
    exact
      ((Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.atTop_div_const
            (show (0 : ℝ) < 2 by norm_num)
            (Filter.tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num))))).neg)
  have h_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(x ^ 2 / 2)) * x := by
    intro x hx
    exact mul_nonneg (Real.exp_nonneg _) (le_of_lt (Set.mem_Ioi.mp hx))
  have h_cont : ContinuousWithinAt f (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt; fun_prop
  have h_deriv_Ioi : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * x) x := by
    intro x hx; exact h_deriv x (Ioi_subset_Ici_self hx)
  have h_intble :=
    integrableOn_Ioi_deriv_of_nonneg h_cont h_deriv_Ioi h_nonneg h_tendsto
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv h_intble h_tendsto]
  simp [f, Real.exp_zero]

/-- `∫_{y>0} exp(-y²/2) · y³ dy = 2`. -/
theorem gaussian_Ioi_y3 :
    ∫ y in Set.Ioi (0 : ℝ), Real.exp (-(y ^ 2) / 2) * y ^ 3 = 2 := by
  have h_exp_rw : ∀ y : ℝ, Real.exp (-(y ^ 2) / 2) = Real.exp (-(y ^ 2 / 2)) := by
    intro y; congr 1; ring
  simp_rw [h_exp_rw]
  set f := fun y : ℝ => -((y ^ 2 + 2) * Real.exp (-(y ^ 2 / 2)))
  have h_deriv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * x ^ 3) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 2) (2 * x) x := by
      simpa using hpow.add_const (2 : ℝ)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
        (Real.exp (-(x ^ 2 / 2)) * (-x)) x := by
      exact ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by ring) |>.neg |>.exp
    have hprod : HasDerivAt
        (fun y : ℝ => (y ^ 2 + 2) * Real.exp (-(y ^ 2 / 2)))
        (-(Real.exp (-(x ^ 2 / 2)) * x ^ 3)) x := by
      exact (h1.mul h2).congr_deriv (by ring)
    simpa [f] using hprod.neg
  have hsqdiv :
      Filter.Tendsto (fun x : ℝ => x ^ 2 / 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (show (0 : ℝ) < 2 by norm_num)
      (Filter.tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num))
  have h_exp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hsqdiv)
  have h_uexp :
      Filter.Tendsto (fun x : ℝ => (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    simpa [pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsqdiv
  have h_sqexp :
      Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    rw [show (fun x : ℝ => x ^ 2 * rexp (-(x ^ 2 / 2))) =
      (fun x => 2 * (x ^ 2 / 2 * rexp (-(x ^ 2 / 2)))) from by ext x; ring,
      show (0 : ℝ) = 2 * 0 from by norm_num]
    exact (tendsto_const_nhds (x := (2 : ℝ))).mul h_uexp
  have h_twoexp :
      Filter.Tendsto (fun x : ℝ => 2 * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul h_exp
  have h_sum :
      Filter.Tendsto (fun x : ℝ => (x ^ 2 + 2) * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    rw [show (fun x : ℝ => (x ^ 2 + 2) * rexp (-(x ^ 2 / 2))) =
      (fun x => x ^ 2 * rexp (-(x ^ 2 / 2)) + 2 * rexp (-(x ^ 2 / 2))) from by ext x; ring,
      show (0 : ℝ) = 0 + 0 from by norm_num]
    exact h_sqexp.add h_twoexp
  have h_tendsto : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = -0 by simp]; simpa [f] using h_sum.neg
  have h_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(x ^ 2 / 2)) * x ^ 3 := by
    intro x hx; exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg (le_of_lt (Set.mem_Ioi.mp hx)) 3)
  have h_cont : ContinuousWithinAt f (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt; fun_prop
  have h_deriv_Ioi : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * x ^ 3) x := by
    intro x hx; exact h_deriv x (Ioi_subset_Ici_self hx)
  have h_intble :=
    integrableOn_Ioi_deriv_of_nonneg h_cont h_deriv_Ioi h_nonneg h_tendsto
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv h_intble h_tendsto]
  simp [f, Real.exp_zero]

/-- `∫_{y>0} exp(-y²/2) · (y + y³/3) dy = 5/3`. -/
theorem gaussian_Ioi_y_plus_y3_div3 :
    ∫ y in Set.Ioi (0 : ℝ),
      Real.exp (-(y ^ 2) / 2) * (y + y ^ 3 / 3) = 5 / 3 := by
  have h_exp_rw : ∀ y : ℝ, Real.exp (-(y ^ 2) / 2) = Real.exp (-(y ^ 2 / 2)) := by
    intro y; congr 1; ring
  simp_rw [h_exp_rw]
  set f := fun y : ℝ => -((y ^ 2 / 3 + 5 / 3) * Real.exp (-(y ^ 2 / 2)))
  have h_deriv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * (x + x ^ 3 / 3)) x := by
    intro x _
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2 / 3) ((2 * x) / 3) x := by
      simpa using (hasDerivAt_pow 2 x).div_const (3 : ℝ)
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 3 + 5 / 3) ((2 * x) / 3) x := by
      simpa using hpow.add_const ((5 : ℝ) / 3)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
        (Real.exp (-(x ^ 2 / 2)) * (-x)) x :=
      ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by ring) |>.neg |>.exp
    have hprod : HasDerivAt
        (fun y : ℝ => (y ^ 2 / 3 + 5 / 3) * Real.exp (-(y ^ 2 / 2)))
        (-(Real.exp (-(x ^ 2 / 2)) * (x + x ^ 3 / 3))) x := by
      exact (h1.mul h2).congr_deriv (by ring)
    simpa [f] using hprod.neg
  have hsqdiv :
      Filter.Tendsto (fun x : ℝ => x ^ 2 / 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (show (0 : ℝ) < 2 by norm_num)
      (Filter.tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num))
  have h_exp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hsqdiv)
  have h_uexp :
      Filter.Tendsto (fun x : ℝ => (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    simpa [pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsqdiv
  have h_x2exp :
      Filter.Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    rw [show (fun x : ℝ => x ^ 2 * rexp (-(x ^ 2 / 2))) =
      (fun x => 2 * (x ^ 2 / 2 * rexp (-(x ^ 2 / 2)))) from by ext x; ring,
      show (0 : ℝ) = 2 * 0 from by norm_num]
    exact (tendsto_const_nhds (x := (2 : ℝ))).mul h_uexp
  have h_polyexp :
      Filter.Tendsto (fun x : ℝ => x ^ 2 / 3 * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    rw [show (fun x : ℝ => x ^ 2 / 3 * rexp (-(x ^ 2 / 2))) =
      (fun x => 1 / 3 * (x ^ 2 * rexp (-(x ^ 2 / 2)))) from by ext x; ring,
      show (0 : ℝ) = 1 / 3 * 0 from by norm_num]
    exact (tendsto_const_nhds (x := (1 / 3 : ℝ))).mul h_x2exp
  have h_constexp :
      Filter.Tendsto (fun x : ℝ => (5 / 3 : ℝ) * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (5 / 3 : ℝ))).mul h_exp
  have h_sum :
      Filter.Tendsto
        (fun x : ℝ => (x ^ 2 / 3 + 5 / 3) * Real.exp (-(x ^ 2 / 2)))
        Filter.atTop (nhds 0) := by
    rw [show (fun x : ℝ => (x ^ 2 / 3 + 5 / 3) * rexp (-(x ^ 2 / 2))) =
      (fun x => x ^ 2 / 3 * rexp (-(x ^ 2 / 2)) + 5 / 3 * rexp (-(x ^ 2 / 2))) from
        by ext x; ring,
      show (0 : ℝ) = 0 + 0 from by norm_num]
    exact h_polyexp.add h_constexp
  have h_tendsto : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = -0 by simp]; simpa [f] using h_sum.neg
  have h_nonneg : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ Real.exp (-(x ^ 2 / 2)) * (x + x ^ 3 / 3) := by
    intro x hx
    have hx0 := le_of_lt (Set.mem_Ioi.mp hx)
    exact mul_nonneg (Real.exp_nonneg _) (by positivity)
  have h_cont : ContinuousWithinAt f (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt; fun_prop
  have h_deriv_Ioi : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
      (Real.exp (-(x ^ 2 / 2)) * (x + x ^ 3 / 3)) x := by
    intro x hx; exact h_deriv x (Ioi_subset_Ici_self hx)
  have h_intble :=
    integrableOn_Ioi_deriv_of_nonneg h_cont h_deriv_Ioi h_nonneg h_tendsto
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv h_intble h_tendsto]
  simp [f, Real.exp_zero]

/-! ## B4. Base value at zero -/

/-- `Φ(0) = 4π · log(1+√2)`. From Lemma 4.3 and arcsin(i) = i·log(1+√2). -/
theorem Phi_zero : Phi 0 = 4 * Real.pi * Real.log (1 + Real.sqrt 2) := by
  unfold Phi
  congr 1
  exact varphi_zero

end Braverman
