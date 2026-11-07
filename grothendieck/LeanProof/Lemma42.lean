/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Defs.Kernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Liouville

/-!
# Lemma 4.2: Analyticity and bound for H_η on the strip

We prove that H_η is analytic on the strip S = {z ∈ ℂ : |Re z| < 1} and
establish the explicit bound (43) from the paper.

## Proof sketch

The integrand of H_η (eq 41) is:
- Holomorphic in z for each fixed (x, y) ∈ ℝ² × ℝ²
- Dominated by an integrable Gaussian bound uniform on compact subsets of S

By differentiating under the integral (Leibniz rule with dominated convergence),
H_η is holomorphic, hence analytic, on S.

The bound (43) comes from bounding |f_η| ≤ 1, taking absolute values inside
the integral, and evaluating the resulting Gaussian integral in closed form
via the change of variables u = x + y, v = x - y.
-/

open Complex Set MeasureTheory Filter Topology Metric

noncomputable section

namespace Braverman

/-! ### Auxiliary lemmas for kernel_exponent -/

/-- The kernel exponent with z negated and y negated equals the original kernel exponent.
    This is because negating z flips the sign of the cross term 2z⟨x,y⟩, and
    negating y also flips the sign of ⟨x,y⟩, so the two sign flips cancel.
    The denominator 1-z² = 1-(-z)² is unchanged. -/
lemma kernel_exponent_neg_z_neg_y (x₁ x₂ y₁ y₂ : ℝ) (z : ℂ) :
    kernel_exponent x₁ x₂ (-y₁) (-y₂) (-z) = kernel_exponent x₁ x₂ y₁ y₂ z := by
  simp only [kernel_exponent]
  congr 1
  push_cast
  ring

/-- f_eta at the negated point: f_η(-x₁,-x₂) = -f_η(x₁,x₂) when x₂ ≠ η·h₅(x₁). -/
lemma f_eta_neg_of_ne (η : ℝ) (x₁ x₂ : ℝ) (hne : x₂ ≠ η * h5 x₁) :
    f_eta η (-x₁, -x₂) = -(f_eta η (x₁, x₂)) := by
  unfold f_eta
  simp only [h5_odd, mul_neg]
  by_cases h : x₂ > η * h5 x₁
  · have h1 : ¬(-x₂ > -(η * h5 x₁)) := by linarith
    simp [h, h1]
  · have hlt : x₂ < η * h5 x₁ := lt_of_le_of_ne (le_of_not_gt h) hne
    have h1 : -x₂ > -(η * h5 x₁) := by linarith
    simp [h, h1]

/-! ### Analyticity -/

/-- The H_eta integrand is integrable for z in the strip.
    This is a key technical ingredient: the Gaussian factor ensures L¹ integrability. -/
-- The kernel exponent is measurable as a function of p for fixed z
private lemma kernel_exponent_measurable_p (z : ℂ) :
    Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) := by
  unfold kernel_exponent
  apply Measurable.neg
  apply Measurable.div_const
  apply Measurable.sub
  · apply Measurable.add
    · exact measurable_ofReal.comp
        ((measurable_fst.fst.pow_const 2).add (measurable_fst.snd.pow_const 2))
    · exact measurable_ofReal.comp
        ((measurable_snd.fst.pow_const 2).add (measurable_snd.snd.pow_const 2))
  · apply Measurable.const_mul
    exact measurable_ofReal.comp
      ((measurable_fst.fst.mul measurable_snd.fst).add
       (measurable_fst.snd.mul measurable_snd.snd))

-- The H_eta integrand is measurable
private lemma H_eta_integrand_aestronglyMeasurable (η : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))) MeasureTheory.volume :=
  (((measurable_ofReal.comp
      (((f_eta_measurable η).comp measurable_fst).mul
       ((f_eta_measurable η).comp measurable_snd))).mul
    ((kernel_exponent_measurable_p z).cexp)).div_const _).aestronglyMeasurable

/-- The explicit Gaussian bound constant for a given z ∈ S.
    This is `(1-|Re z|)²/(4·D2(z))` where `D2 = (1-Re(z)²+Im(z)²)² + (2·Re(z)·Im(z))²`. -/
private noncomputable def kernel_bound_const (z : ℂ) : ℝ :=
  (1 - |z.re|) ^ 2 / (2 * ((1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2))

/-- The explicit bound with kernel_bound_const: this is the core lemma. -/
private lemma kernel_exponent_re_bound_with_const (z : ℂ) (hz : z ∈ S) :
    0 < kernel_bound_const z ∧ ∀ x₁ x₂ y₁ y₂ : ℝ,
      (kernel_exponent x₁ x₂ y₁ y₂ z).re ≤
        -(kernel_bound_const z) * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) := by
  -- Write z = a + bi. kernel_bound_const z = (1-|a|)²/(4·D2).
  set a := z.re
  set b := z.im
  rw [mem_S_iff] at hz
  -- The key bound constant
  set D2 := (1 - a ^ 2 + b ^ 2) ^ 2 + (2 * a * b) ^ 2
  -- kernel_bound_const z unfolds to (1-|a|)²/(4*D2) definitionally
  change 0 < (1 - |a|) ^ 2 / (2 * D2) ∧ _
  have hD2_pos : 0 < D2 := by
    have ha_lt : a ^ 2 < 1 := by
      have h1 := sq_abs a
      have h2 : |a| * |a| < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) hz (le_of_lt hz)
      linarith [sq (|a|)]
    nlinarith [sq_nonneg (1 - a ^ 2 + b ^ 2), sq_nonneg (2 * a * b), sq_nonneg b]
  have h1_sub_abs_a : 0 < 1 - |a| := by linarith [abs_nonneg a]
  refine ⟨div_pos (sq_pos_of_pos h1_sub_abs_a) (by linarith), ?_⟩
  intro x₁ x₂ y₁ y₂
  set s := x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2
  set t := x₁ * y₁ + x₂ * y₂
  -- AM-GM bound: 2|t| ≤ s
  have ht_bound : 2 * |t| ≤ s := by
    have h1 : 0 ≤ (x₁ - y₁) ^ 2 + (x₂ - y₂) ^ 2 := by positivity
    have h2 : 0 ≤ (x₁ + y₁) ^ 2 + (x₂ + y₂) ^ 2 := by positivity
    have h_abs_2t : (2 : ℝ) * |t| = |2 * t| := by
      rw [abs_mul]; norm_num
    rw [h_abs_2t, abs_le]
    constructor <;> nlinarith
  -- The kernel exponent's real part can be computed as:
  --   Re(-(N/D)) = -(Re(N)·Re(D) + Im(N)·Im(D)) / normSq(D)
  -- where N = s - 2z·t, D = 2(1-z²)
  -- After expansion with z = a + bi:
  --   Re(N) = s - 2at, Im(N) = -2bt
  --   Re(D) = 2(1-a²+b²), Im(D) = -4ab
  --   (since Re(D)= 2-2Re(z²) = 2(1-a²+b²) and Im(D) = -2·Im(z²) = -4ab)
  --   Actually: D = 2(1-z²) = 2 - 2z², and z² = a²-b² + 2abi
  --   so D = 2(1-a²+b²) - 4abi, Re(D) = 2(1-a²+b²), Im(D) = -4ab
  --   Numerator N = (s-2at) - 2bti (as ℂ)
  --   Re(N·conj(D)) = Re(N)·Re(D) + Im(N)·Im(D) -- but div_re uses normSq in denominator
  --   = (s-2at)·2(1-a²+b²) + (-2bt)·(-4ab)
  --   = 2(s-2at)(1-a²+b²) + 8ab²t
  --   = 2s(1-a²+b²) - 4at(1-a²+b²) + 8ab²t
  --   = 2s(1-a²+b²) - 4at(1-a²+b²-2b²)
  --   = 2s(1-a²+b²) - 4at(1-a²-b²)
  -- So Re(-(N/D)) = -(2s(1-a²+b²) - 4at(1-a²-b²)) / normSq(D)
  -- = -(2s(1-a²+b²) - 4at(1-a²-b²)) / (4·D2)
  -- We need this ≤ -(1-|a|)/(2·D2) · s
  -- i.e., -(2s(1-a²+b²) - 4at(1-a²-b²)) / (4·D2) ≤ -(1-|a|)·s/(2·D2)
  -- Multiply both sides by 4·D2 > 0 and flip:
  --   (1-|a|)·s · 2 ≤ 2s(1-a²+b²) - 4at(1-a²-b²)
  -- i.e., 2(1-|a|)s ≤ 2s(1-a²+b²) - 4at(1-a²-b²)
  -- Since 1-a² = (1-|a|)(1+|a|), 1-a²+b² ≥ 1-a² ≥ (1-|a|), and
  -- |4at(1-a²-b²)| ≤ 4·|a|·|t|·|1-a²-b²|
  -- We can bound: 2s(1-a²+b²) ≥ 2s(1-|a|) and 4at(1-a²-b²) can go either way.
  -- Actually, we need:
  --   2s(1-a²+b²) - 4at(1-a²-b²) ≥ 2(1-|a|)s
  -- iff 2s((1-a²+b²) - (1-|a|)) ≥ 4at(1-a²-b²)
  -- iff 2s(|a|-a²+b²+|a|·something) ≥ ... This gets messy.
  -- Let's just verify computationally via simp/push_cast/ring_nf and nlinarith.
  -- The algebraic computation requires expanding the complex division's real part.
  -- kernel_exponent = -(N/D) where N = s - 2z·t (as complex) and D = 2(1-z²).
  -- Re(-(N/D)) = -(Re(N)·Re(D) + Im(N)·Im(D)) / normSq(D)
  -- where normSq(D) = 4·D2 > 0.
  -- After expansion: Re(N)·Re(D) + Im(N)·Im(D) = 2s(1-a²+b²) - 4at(1-a²-b²)
  -- We need: -this/(4·D2) ≤ -(1-|a|)/(2·D2) · s
  -- i.e., this/(4·D2) ≥ (1-|a|)/(2·D2) · s
  -- i.e., this ≥ 2(1-|a|)·s  (multiply by 4·D2 > 0)
  -- i.e., 2s(1-a²+b²) - 4at(1-a²-b²) ≥ 2(1-|a|)·s
  -- Using |t| ≤ s/2 and 1-a² = (1-|a|)(1+|a|):
  --   2s(1-a²+b²) ≥ 2s(1-|a|) + 2sb² + 2s|a|(1-|a|)  (since 1-a² ≥ (1-|a|)(1+|a|) = 1-a²)
  --   Wait, 1-a²+b² = (1-|a|)(1+|a|)+b² ≥ (1-|a|), so 2s(1-a²+b²) ≥ 2(1-|a|)s already.
  --   The cross term -4at(1-a²-b²): we bound |4at(1-a²-b²)| ≤ 4|a|·(s/2)·|1-a²-b²| = 2|a|s|1-a²-b²|
  --   But (1-a²+b²) ≥ |1-a²-b²| since (1-a²+b²)²-(1-a²-b²)² = 4b²(1-a²) ≥ 0
  --   So 2s(1-a²+b²) - 4at(1-a²-b²) ≥ 2s(1-a²+b²) - 2|a|s(1-a²+b²)
  --     = 2s(1-|a|)(1-a²+b²) ≥ 2s(1-|a|)
  -- This proves the bound. The formal version needs expanding complex arithmetic.
  -- We prove the bound by converting to a purely real inequality.
  -- The full algebraic computation is involved but systematic.
  -- Step 1: Reduce to an inequality about Re(N/D) for explicit N, D.
  -- Step 2: Use div_re to expand into a fraction with normSq in denominator.
  -- Step 3: Clear the denominator (positive) and use nlinarith with AM-GM.
  -- Since the algebraic manipulation is very long, we combine all steps:
  suffices h : (kernel_exponent x₁ x₂ y₁ y₂ z).re ≤
      -((1 - |a|) ^ 2 / (2 * D2)) * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) from h
  -- Expand kernel_exponent
  unfold kernel_exponent
  -- Re(-w) = -Re(w)
  simp only [neg_re]
  -- Now need: -(N/D).re ≤ -(1-|a|)/(2·D2) · s
  -- Equivalently: (N/D).re ≥ (1-|a|)/(2·D2) · s
  -- Use div_re: (N/D).re = N.re*D.re/normSq(D) + N.im*D.im/normSq(D)
  rw [Complex.div_re]
  -- Now have a fraction. The normSq in the denominator needs to be shown positive.
  -- normSq(D) = normSq(2*(1-z²)) = 4*normSq(1-z²) = 4*D2
  -- The detailed computation of N.re, N.im, D.re, D.im and normSq(D) in terms of
  -- a, b, x₁, x₂, y₁, y₂ followed by nlinarith is the core work.
  -- Expand all complex .re, .im, normSq to real arithmetic
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  have hzsq_re : (z ^ 2).re = a ^ 2 - b ^ 2 := by
    simp [sq, Complex.mul_re]; ring
  have hzsq_im : (z ^ 2).im = 2 * a * b := by
    simp [sq, Complex.mul_im]; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.normSq_apply,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, zero_sub,
    h2re, h2im, hzsq_re, hzsq_im]
  -- z.re = a, z.im = b by definition
  -- The two fractions share a common denominator. Combine them.
  -- The denominator is normSq(1-z²) = D2.
  have hD := show (1 - (a ^ 2 - b ^ 2)) * (1 - (a ^ 2 - b ^ 2)) +
      -(2 * a * b) * -(2 * a * b) = D2 by ring
  rw [show z.re = a from rfl, show z.im = b from rfl, hD]
  -- Now combine the two fractions with common denominator D2
  rw [div_add_div_same]
  -- Both sides involve division by D2 > 0. We multiply both sides by 2*D2 > 0.
  have h2D2 : (0 : ℝ) < 2 * D2 := by linarith
  -- Suffices to prove the inequality after clearing positive denominators.
  -- LHS * (4*D2) = -(numerator), RHS * (4*D2) = -2(1-|a|)s
  -- So we need: numerator ≥ 2(1-|a|)s.
  -- Use the key steps from the sketch above.
  have ha_sq_lt : a ^ 2 < 1 := by
    have h1 := sq_abs a; have h2 : |a| * |a| < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) hz (le_of_lt hz)
    linarith [sq (|a|)]
  -- Main inequality: clear denominators and reduce to polynomial
  suffices h_main : (1 - |a|) ^ 2 * s ≤
      (s - 2 * a * t) * (2 * (1 - a ^ 2 + b ^ 2)) + 4 * a * b * (2 * b * t) by
    have h_rhs : -((1 - |a|) ^ 2 / (2 * D2)) * s =
        -((1 - |a|) ^ 2 * s / (2 * D2)) := by ring
    rw [h_rhs]
    apply neg_le_neg
    -- Goal: (1-|a|)²·s / (2·D2) ≤ numerator / D2
    -- Rewrite LHS: (1-|a|)²·s / (2·D2) = ((1-|a|)²·s/2) / D2
    rw [show (1 - |a|) ^ 2 * s / (2 * D2) = ((1 - |a|) ^ 2 * s / 2) / D2 from by ring]
    apply div_le_div_of_nonneg_right _ hD2_pos.le
    -- Need: (1-|a|)²·s/2 ≤ numerator (which is (s-2at)(1-a²+b²) + 4ab²t)
    linarith [h_main]
  -- Expand: (s - 2at)·2(1-a²+b²) + 8ab²t
  --       = 2(1-a²+b²)s - 4at(1-a²+b²) + 8ab²t
  --       = 2(1-a²+b²)s - 4at(1-a²+b² - 2b²)
  --       = 2(1-a²+b²)s - 4at(1-a²-b²)
  -- Need: (1-|a|)²s ≤ 2(1-a²+b²)s - 4at(1-a²-b²)
  -- Proof sketch: LHS ≤ 2(1-|a|)(1-a²+b²)s ≤ RHS.
  -- Case split on sign of a to eliminate |a|
  have ht_abs : |t| ≤ s / 2 := by linarith
  have ht_pos : t ≤ s / 2 := le_of_abs_le ht_abs
  have ht_neg : -(s / 2) ≤ t := neg_le_of_abs_le ht_abs
  have hs_nn : 0 ≤ s := by positivity
  -- From |a| < 1 we get -1 < a < 1
  have ha_lt_one : a < 1 := by
    rcases abs_lt.mp hz with ⟨_, h⟩; exact h
  have ha_gt_neg_one : -1 < a := by
    rcases abs_lt.mp hz with ⟨h, _⟩; linarith
  rcases le_or_gt 0 a with ha_nn | ha_neg
  · rw [abs_of_nonneg ha_nn]
    -- RHS - LHS = (1-a)·((1+3a)s - 4at(1+a)) + 2b²(s+2at) ≥ 0
    suffices 0 ≤ (s - 2 * a * t) * (2 * (1 - a ^ 2 + b ^ 2)) +
        4 * a * b * (2 * b * t) - (1 - a) ^ 2 * s by linarith
    have h_factor : (s - 2 * a * t) * (2 * (1 - a ^ 2 + b ^ 2)) +
        4 * a * b * (2 * b * t) - (1 - a) ^ 2 * s =
        (1 - a) * ((1 + 3 * a) * s - 4 * a * t * (1 + a)) +
        2 * b ^ 2 * (s + 2 * a * t) := by ring
    rw [h_factor]
    apply add_nonneg
    · -- First term: (1-a) * ((1+3a)s - 4at(1+a)) ≥ 0
      -- (1-a) ≥ 0 since a < 1. Inner: (1+3a)s ≥ 4a|t|(1+a) ≥ |4at(1+a)|.
      apply mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a)
      -- Factor inner as: (1-a)(1+2a)·s + 4a(1+a)·(s/2 - t) + 4a(1+a)·(s/2 + t) - 4a(1+a)s ... no
      -- Simpler: inner ≥ (1+3a)s - 4a(s/2)(1+a) = s(1+3a-2a-2a²) = s(1-a)(1+2a) ≥ 0
      -- and inner ≥ (1+3a)s + 4a(s/2)(1+a) = s(1+3a+2a+2a²) = s(1+5a+2a²) ... not needed.
      -- Just show (1+3a)s - 4at(1+a) ≥ s(1-a)(1+2a) ≥ 0 when t ≤ s/2,
      -- and (1+3a)s - 4at(1+a) ≥ ... when t ≥ -s/2. Both cases: use |4at(1+a)| ≤ 2as(1+a).
      have h_inner_factored : (1 + 3 * a) * s - 4 * a * t * (1 + a) =
          (1 - a) * (1 + 2 * a) * s + 4 * a * (1 + a) * (s / 2 - t) := by ring
      rw [h_inner_factored]
      apply add_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) (by nlinarith : (0 : ℝ) ≤ 1 + 2 * a)
        · exact hs_nn
      · apply mul_nonneg
        · nlinarith
        · linarith
    · -- Second term: 2b²(s+2at) ≥ 0
      apply mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * b ^ 2)
      -- s + 2at ≥ 0 follows from: s+2at = (1+2a)(s/2+t) + (1-2a)(s/2-t)... no simpler:
      -- s + 2at ≥ s - 2a(s/2) = s(1-a) ≥ 0 when t ≤ s/2 and a ≥ 0
      -- Actually s+2at ≥ s - 2|a||t| ≥ s - 2·1·(s/2) = 0 ... but we don't have |a| ≤ 1 in scope
      -- Simplest: factor as s/2+t + a(s/2+t) + (1-a)(s/2-t)... no.
      -- Just use: s+2at = s(1+2a) - 2a(s-2t) ... hmm.
      -- Actually s + 2at ≥ 0 iff t ≥ -s/(2a) when a > 0, which is ≥ -s/2 ≥ ... always true
      -- When a = 0: s + 0 = s ≥ 0.
      -- For a > 0: s + 2at ≥ s - 2a(s/2) = s(1-a) ≥ 0
      -- using t ≥ -s/2.
      nlinarith
  · rw [abs_of_neg ha_neg]
    -- RHS - LHS = (1+a)·((1-3a)s - 4at(1-a)) + 2b²(s+2at)
    suffices 0 ≤ (s - 2 * a * t) * (2 * (1 - a ^ 2 + b ^ 2)) +
        4 * a * b * (2 * b * t) - (1 - -a) ^ 2 * s by linarith
    have h_factor : (s - 2 * a * t) * (2 * (1 - a ^ 2 + b ^ 2)) +
        4 * a * b * (2 * b * t) - (1 - -a) ^ 2 * s =
        (1 + a) * ((1 - 3 * a) * s - 4 * a * t * (1 - a)) +
        2 * b ^ 2 * (s + 2 * a * t) := by ring
    rw [h_factor]
    apply add_nonneg
    · apply mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a)
      -- Inner = (1-3a)s - 4at(1-a). For a < 0, -a > 0, so 1-3a > 1 and 1-a > 1.
      -- Factor: = (1+a)(1-2a)s + 4(-a)(1-a)(s/2 + t)
      have h_inner_factored : (1 - 3 * a) * s - 4 * a * t * (1 - a) =
          (1 + a) * (1 - 2 * a) * s + 4 * (-a) * (1 - a) * (s / 2 + t) := by ring
      rw [h_inner_factored]
      apply add_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (by nlinarith : (0 : ℝ) ≤ 1 - 2 * a)
        · exact hs_nn
      · apply mul_nonneg
        · nlinarith
        · linarith
    · apply mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * b ^ 2)
      -- s + 2at ≥ s(1+a) ≥ 0
      have h1 : s + 2 * a * t ≥ s * (1 + a) := by
        have : 2 * a * t ≥ a * s := by
          have : 2 * a * t ≥ 2 * a * (s / 2) :=
            mul_le_mul_of_nonpos_left ht_pos (by linarith : 2 * a ≤ 0)
          linarith
        linarith
      have h2 : s * (1 + a) ≥ 0 := mul_nonneg hs_nn (by linarith)
      linarith

/-- Existential version of the bound, for convenience. -/
lemma kernel_exponent_re_bound (z : ℂ) (hz : z ∈ S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x₁ x₂ y₁ y₂ : ℝ,
      (kernel_exponent x₁ x₂ y₁ y₂ z).re ≤
        -c * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) :=
  ⟨kernel_bound_const z, (kernel_exponent_re_bound_with_const z hz).1,
   (kernel_exponent_re_bound_with_const z hz).2⟩

/-- A 2D Gaussian is integrable over ℝ × ℝ.
    This follows from the 1D result via Fubini/product integrability. -/
private lemma integrable_gaussian_2d (c : ℝ) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2))) volume := by
  have hfact : ∀ p : ℝ × ℝ, Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2)) =
      Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
    intro p
    rw [show -c * (p.1 ^ 2 + p.2 ^ 2) = -c * p.1 ^ 2 + -c * p.2 ^ 2 by ring]
    exact Real.exp_add _ _
  simp_rw [hfact]
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
  exact Integrable.mul_prod (integrable_exp_neg_mul_sq hc) (integrable_exp_neg_mul_sq hc)

/-- A 4D Gaussian is integrable over (ℝ×ℝ) × (ℝ×ℝ).
    This follows from the 2D result via Fubini/product integrability. -/
lemma integrable_gaussian_4d (c : ℝ) (hc : 0 < c) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (-c * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2))) volume := by
  have hfact : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-c * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) =
      Real.exp (-c * (p.1.1 ^ 2 + p.1.2 ^ 2)) *
        Real.exp (-c * (p.2.1 ^ 2 + p.2.2 ^ 2)) := by
    intro p
    rw [show -c * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) =
        -c * (p.1.1 ^ 2 + p.1.2 ^ 2) + -c * (p.2.1 ^ 2 + p.2.2 ^ 2) by ring]
    exact Real.exp_add _ _
  simp_rw [hfact]
  rw [show (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) = volume.prod volume from rfl]
  exact Integrable.mul_prod (integrable_gaussian_2d c hc) (integrable_gaussian_2d c hc)

/-- The cexp(kernel_exponent) is integrable for z in the strip.
    The kernel_exponent is a negative-definite quadratic form for |Re z| < 1,
    so the integral is a convergent 4D Gaussian. -/
theorem cexp_kernel_integrable (z : ℂ) (hz : z ∈ S) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)) volume := by
  -- Step 1: Extract the Gaussian bound constant from kernel_exponent_re_bound
  obtain ⟨c, hc, hre⟩ := kernel_exponent_re_bound z hz
  -- Step 2: Bound ‖cexp(kernel_exponent)‖ ≤ exp(-c * quadratic)
  apply Integrable.mono' (integrable_gaussian_4d c hc)
  · exact ((kernel_exponent_measurable_p z).cexp).aestronglyMeasurable
  · filter_upwards with p
    rw [Complex.norm_exp]
    exact Real.exp_le_exp_of_le (hre p.1.1 p.1.2 p.2.1 p.2.2)

theorem H_eta_integrand_integrable (η : ℝ) (z : ℂ) (hz : z ∈ S) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))) MeasureTheory.volume := by
  -- Factor out the constant denominator: integrand = (f · cexp K) / const
  apply Integrable.div_const
  -- Now show: f_eta(p.1) * f_eta(p.2) * cexp(kernel_exponent) is integrable
  -- Since |f_eta| = 1 everywhere, bound the norm by ‖cexp(kernel_exponent)‖
  apply Integrable.mono' (g := fun p =>
      ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖)
  · exact (cexp_kernel_integrable z hz).norm
  · exact (measurable_ofReal.comp
      (((f_eta_measurable η).comp measurable_fst).mul
       ((f_eta_measurable η).comp measurable_snd))).aestronglyMeasurable.mul
      ((kernel_exponent_measurable_p z).cexp).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul]
    calc ‖(↑(f_eta η p.1 * f_eta η p.2) : ℂ)‖ *
          ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖
        ≤ 1 * ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Complex.norm_real]
          simp only [Real.norm_eq_abs, abs_mul, f_eta_bounded, mul_one, le_refl]
      _ = ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖ := one_mul _

-- Helper: 1 - z² ≠ 0 on the strip S
lemma one_sub_sq_ne_zero_on_S (z : ℂ) (hz : z ∈ S) : 1 - z ^ 2 ≠ 0 := by
  rw [mem_S_iff] at hz
  -- Factor 1 - z² = (1-z)(1+z)
  rw [show (1 : ℂ) - z ^ 2 = (1 - z) * (1 + z) by ring]
  intro h
  rcases mul_eq_zero.mp h with h1 | h1
  · -- 1 - z = 0 means z = 1
    have heq : z = 1 := (sub_eq_zero.mp h1).symm
    rw [heq] at hz; simp at hz
  · -- 1 + z = 0 means z = -1
    have heq : z = -1 := (neg_eq_of_add_eq_zero_right h1).symm
    rw [heq] at hz; simp at hz

-- Helper: 2π(1-z²) ≠ 0 on the strip S
lemma denom_ne_zero_on_S (z : ℂ) (hz : z ∈ S) :
    2 * ↑Real.pi * (1 - z ^ 2) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  · exact one_sub_sq_ne_zero_on_S z hz

/-- The H_eta integrand is differentiable in z for each fixed p.
    The integrand z ↦ f_η(p) · exp(K(p,z)) / (2π(1-z²)) is a composition
    of analytic functions in z. -/
-- kernel_exponent is differentiable in z on S
lemma kernel_exponent_differentiableOn (x₁ x₂ y₁ y₂ : ℝ) :
    DifferentiableOn ℂ (fun z => kernel_exponent x₁ x₂ y₁ y₂ z) S := by
  unfold kernel_exponent
  apply DifferentiableOn.neg
  apply DifferentiableOn.div
  · apply DifferentiableOn.sub
    · apply DifferentiableOn.add
      · exact differentiableOn_const _
      · exact differentiableOn_const _
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · exact differentiableOn_const _
        · exact differentiableOn_id
      · exact differentiableOn_const _
  · exact (differentiableOn_const _).sub (differentiableOn_id.pow _)
  · intro z hz
    exact one_sub_sq_ne_zero_on_S z hz

theorem H_eta_integrand_differentiable (η : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    DifferentiableOn ℂ (fun z =>
      ↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))) S := by
  apply DifferentiableOn.div
  · apply DifferentiableOn.mul
    · exact differentiableOn_const _
    · exact (kernel_exponent_differentiableOn p.1.1 p.1.2 p.2.1 p.2.2).cexp
  · exact ((differentiableOn_const _).mul
      ((differentiableOn_const _).sub (differentiableOn_id.pow _)))
  · intro z hz
    exact denom_ne_zero_on_S z hz

set_option maxHeartbeats 400000 in
/-- Dominated convergence bound: for any compact K ⊆ S, the H_eta integrand is
    bounded by an integrable function uniformly on K. -/
theorem H_eta_integrand_dominated (η : ℝ) (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ bound : (ℝ × ℝ) × (ℝ × ℝ) → ℝ,
      Integrable bound MeasureTheory.volume ∧
      ∀ z ∈ K, ∀ p, ‖(↑(f_eta η p.1 * f_eta η p.2) *
        Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
        (2 * ↑Real.pi * (1 - z ^ 2)) : ℂ)‖ ≤ bound p := by
  -- Step 1: Since K is compact and z ↦ ‖2π(1-z²)‖⁻¹ is continuous on K ⊆ S, get M.
  -- Since K compact ⊆ S open, z ↦ ‖integrand‖ ≤ M · exp(-c·quadratic) for uniform c, M.
  -- Use the triangle inequality: ‖f·cexp(K)/D‖ ≤ exp(Re K) / ‖D‖
  -- For each z ∈ K ⊆ S, kernel_exponent_re_bound gives c(z) > 0 with
  --   Re(kernel_exponent) ≤ -c(z) · (x₁²+x₂²+y₁²+y₂²)
  -- We need a uniform c > 0 and M < ∞ over K.
  -- Step 1: Get uniform Gaussian constant from compactness.
  -- The map z ↦ (1-|z.re|)²/(4·D2(z)) is continuous and positive on K.
  -- By compactness it has a positive minimum c_min.
  -- Step 2: Get uniform denominator bound from compactness.
  -- The map z ↦ ‖2π(1-z²)‖ is continuous and positive on S.
  -- By compactness of K, it has a positive minimum, giving M = 1/min.
  -- For the formal proof, we observe that it suffices to provide *any*
  -- integrable bound. We use norm_integral_le and the pointwise bound.
  -- Since the full compactness argument is substantial, we construct the
  -- bound via the continuous dependence on z over compact K.
  -- Use the fact that continuous functions on compact sets are bounded.
  have hS_open := S_isOpen
  -- The denominator function is continuous on ℂ
  have h_denom_cont : Continuous (fun z : ℂ => 2 * ↑Real.pi * (1 - z ^ 2)) :=
    continuous_const.mul (continuous_const.sub (continuous_id.pow 2))
  -- The denominator is nonzero on S
  -- Its norm is continuous and positive on K, hence bounded below
  have h_norm_denom_cont : Continuous (fun z : ℂ => ‖2 * ↑Real.pi * (1 - z ^ 2)‖) :=
    continuous_norm.comp h_denom_cont
  -- Get M = sup of 1/‖denom‖ on K
  -- Equivalently, get the minimum of ‖denom‖ on K
  -- Since ‖denom‖ is continuous on K (compact), it attains its minimum.
  -- The minimum is positive since denom ≠ 0 on K ⊆ S.
  have h_denom_pos : ∀ z ∈ K, 0 < ‖2 * ↑Real.pi * (1 - z ^ 2)‖ := by
    intro z hz
    rw [norm_pos_iff]
    exact denom_ne_zero_on_S z (hKS hz)
  -- Get the Gaussian constant. For each z ∈ K ⊆ S, kernel_exponent_re_bound gives c(z).
  -- The function c(z) = (1-|z.re|)²/(4·D2(z)) is continuous and positive on K.
  -- For simplicity, since K ⊆ S is compact in the open strip,
  -- there exists r < 1 with |z.re| ≤ r for all z ∈ K.
  -- Then c(z) ≥ (1-r)²/(4·max_K D2) > 0.
  -- But formalizing this requires showing D2 is bounded on K.
  -- A simpler approach: for any compact K ⊆ S, kernel_exponent_re_bound
  -- gives a bound for each z. We just need to show the infimum is positive.
  -- Let's use the fact that z ↦ c(z) is continuous and positive on K.
  -- Actually, the cleanest approach is to just produce *any* integrable
  -- dominator. For each z ∈ K, we have ‖integrand(z,p)‖ ≤ g_z(p) where
  -- g_z is integrable. We need a single g that works for all z ∈ K.
  -- The simplest: bound each factor separately using compactness.
  -- Factor 1: ‖cexp(kernel_exponent)‖ = exp(Re(kernel_exponent))
  -- Factor 2: ‖(f·...)‖ ≤ 1 (from f_eta_bounded)
  -- Factor 3: ‖1/denom‖ = 1/‖denom‖ ≤ M (bounded on compact K)
  -- So ‖integrand‖ ≤ M · exp(-c·quadratic)
  -- and M · exp(-c·quadratic) is integrable since exp(-c·quadratic) is.
  -- Handle the empty case: if K is empty, everything is vacuously true
  by_cases hK_ne : K.Nonempty
  swap
  · exact ⟨0, integrable_zero _ _ _, fun z hz => absurd ⟨z, hz⟩ hK_ne⟩
  -- Step A: bound 1/‖denom‖ on K
  obtain ⟨z_min, hz_min_mem, hz_min_le⟩ :=
    hK.exists_isMinOn hK_ne h_norm_denom_cont.continuousOn
  set M_denom := ‖2 * ↑Real.pi * (1 - z_min ^ 2)‖ with hM_denom_def
  have hM_pos : 0 < M_denom := h_denom_pos z_min hz_min_mem
  -- For all z ∈ K, ‖denom(z)‖ ≥ M_denom > 0
  have h_denom_lb : ∀ z ∈ K, M_denom ≤ ‖2 * ↑Real.pi * (1 - z ^ 2)‖ := by
    intro z hz
    exact hz_min_le hz
  -- Step B: bound exp(Re(kernel_exponent)) uniformly on K
  -- We need a single c > 0 that works for all z ∈ K.
  -- The function c(z) from kernel_exponent_re_bound is continuous on K ⊆ S.
  -- By compactness of K, the continuous function z ↦ c(z) has a positive minimum.
  -- Rather than formalizing the explicit formula for c(z), we use the
  -- continuous extension: the map z ↦ (1-|z.re|)² is continuous and positive on K ⊆ S,
  -- so it has a positive minimum on K.
  -- For the denominator D2, it's continuous and positive on K.
  -- This gives c_min > 0 with Re(kernel_exponent) ≤ -c_min·quadratic for all z ∈ K.
  -- Rather than formalizing this continuity argument, we can use a simpler approach:
  -- Since K ⊆ S is compact, there exists r with 0 ≤ r < 1 and |z.re| ≤ r for all z ∈ K.
  -- Then use r to build a uniform constant.
  -- Compact K has bounded image under the continuous map |·.re|
  have h_re_cont : Continuous (fun z : ℂ => |z.re|) := continuous_abs.comp Complex.continuous_re
  obtain ⟨z_max, hz_max_mem, hz_max_ge⟩ :=
    hK.exists_isMaxOn hK_ne h_re_cont.continuousOn
  set r := |z_max.re| with hr_def
  have hr_lt_one : r < 1 := by
    have := hKS hz_max_mem
    rw [mem_S_iff] at this
    exact this
  have hr_nn : 0 ≤ r := abs_nonneg _
  -- For all z ∈ K, |z.re| ≤ r < 1
  have h_re_bound : ∀ z ∈ K, |z.re| ≤ r := fun z hz => hz_max_ge hz
  -- Also bound |z.im| on K: K compact ⟹ bounded ⟹ |z.im| ≤ R for some R
  have h_im_cont : Continuous (fun z : ℂ => |z.im|) := continuous_abs.comp Complex.continuous_im
  obtain ⟨z_im_max, hz_im_max_mem, hz_im_max_ge⟩ :=
    hK.exists_isMaxOn hK_ne h_im_cont.continuousOn
  set R := |z_im_max.im| with hR_def
  -- Now build uniform c: for z ∈ K, kernel_exponent_re_bound gives c(z) which depends on z.
  -- We need to show c(z) ≥ c_min > 0 for all z ∈ K.
  -- c(z) = (1-|a|)²/(4·D2) where D2 = (1-a²+b²)² + (2ab)²
  -- For |a| ≤ r and |b| ≤ R:
  -- (1-|a|)² ≥ (1-r)² > 0
  -- D2 = (1-a²+b²)² + (2ab)² ≤ (1+R²)² + (2R)² = (1+R²)² + 4R² [crude bound, since a²≤1, b²≤R²]
  -- Actually D2 ≤ (1-a²+b²)² + 4a²b² ≤ (1+b²)² + 4b² ≤ (1+R²)² + 4R²
  -- So c(z) ≥ (1-r)²/(4·((1+R²)²+4R²)) := c_min
  -- This c_min > 0 works uniformly.
  -- For simplicity, let's just use the fact that kernel_exponent_re_bound works for each z
  -- and extract the bound via the r, R parameters.
  -- Actually the simplest formal approach: use kernel_exponent_re_bound for each z ∈ K,
  -- then show the resulting c(z) is bounded below.
  -- For each z ∈ K, the bound constant is (1-|z.re|)²/(4*D2(z)).
  -- We bound (1-|z.re|)² ≥ (1-r)² and D2(z) ≤ D2_max.
  -- D2(z) = (1-z.re²+z.im²)² + (2·z.re·z.im)²
  -- Upper bound D2: since |z.re| ≤ r < 1 and |z.im| ≤ R:
  --   1-z.re²+z.im² ≤ 1+R² and 2|z.re·z.im| ≤ 2R
  --   D2 ≤ (1+R²)² + 4R²
  set D2_max := (1 + R ^ 2) ^ 2 + 4 * R ^ 2
  set c_unif := (1 - r) ^ 2 / (2 * D2_max)
  -- Show D2_max > 0
  have hD2_max_pos : 0 < D2_max := by positivity
  -- Show c_unif > 0
  have hc_unif_pos : 0 < c_unif := div_pos (sq_pos_of_pos (by linarith)) (by linarith)
  -- Show c_unif ≤ kernel_bound_const z for all z ∈ K
  have h_im_bound : ∀ z ∈ K, |z.im| ≤ R := fun z hz => hz_im_max_ge hz
  have h_cunif_le : ∀ z ∈ K, c_unif ≤ kernel_bound_const z := by
    intro z hz
    unfold kernel_bound_const
    set a := z.re; set b := z.im
    set D2z := (1 - a ^ 2 + b ^ 2) ^ 2 + (2 * a * b) ^ 2
    -- (1-r)² ≤ (1-|a|)² because |a| ≤ r
    have h_num : (1 - r) ^ 2 ≤ (1 - |a|) ^ 2 := by
      apply sq_le_sq' <;> linarith [h_re_bound z hz, abs_nonneg a]
    -- D2z ≤ D2_max
    have ha_abs_lt : |a| < 1 := lt_of_le_of_lt (h_re_bound z hz) hr_lt_one
    have ha_sq : a ^ 2 ≤ 1 := by
      have := sq_abs a; have := mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a) ha_abs_lt
        (le_of_lt ha_abs_lt)
      nlinarith
    have hb_abs : |b| ≤ R := h_im_bound z hz
    have hb_sq : b ^ 2 ≤ R ^ 2 := by
      have hR_nn : 0 ≤ R := abs_nonneg _
      nlinarith [sq_abs b, sq_abs R, mul_le_mul hb_abs hb_abs (abs_nonneg _) hR_nn]
    have h_D2z_le : D2z ≤ D2_max := by
      have h1 : 1 - a ^ 2 + b ^ 2 ≤ 1 + R ^ 2 := by nlinarith [sq_nonneg a]
      have h1nn : 0 ≤ 1 - a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b]
      have h1nn' : 0 ≤ 1 + R ^ 2 := by positivity
      have h3 : (1 - a ^ 2 + b ^ 2) ^ 2 ≤ (1 + R ^ 2) ^ 2 := by
        exact sq_le_sq' (by linarith) h1
      have h4 : (2 * a * b) ^ 2 ≤ 4 * R ^ 2 := by
        have hab_abs : |a * b| ≤ R := by
          calc |a * b| = |a| * |b| := abs_mul a b
            _ ≤ 1 * R := mul_le_mul (le_of_lt ha_abs_lt) hb_abs (abs_nonneg _) (by linarith)
            _ = R := one_mul R
        have hab_sq : (a * b) ^ 2 ≤ R ^ 2 := by
          have h_ab_nn : 0 ≤ |a * b| := abs_nonneg _
          have hR_nn : 0 ≤ R := abs_nonneg _
          have := mul_le_mul hab_abs hab_abs h_ab_nn hR_nn
          nlinarith [sq_abs (a * b), sq_abs R]
        nlinarith
      linarith
    have hD2z_pos : 0 < D2z := by
      have ha2_lt : a ^ 2 < 1 := by
        have := sq_abs a
        have := mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg a) ha_abs_lt (le_of_lt ha_abs_lt)
        nlinarith
      nlinarith [sq_nonneg (1 - a ^ 2 + b ^ 2), sq_nonneg (2 * a * b), sq_nonneg b]
    calc c_unif = (1 - r) ^ 2 / (2 * D2_max) := rfl
      _ ≤ (1 - r) ^ 2 / (2 * D2z) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity : (0 : ℝ) < 2 * D2z)
            (by linarith : 2 * D2z ≤ 2 * D2_max)
      _ ≤ (1 - |a|) ^ 2 / (2 * D2z) :=
          div_le_div_of_nonneg_right h_num (by linarith)
  -- Uniform kernel bound for all z ∈ K
  have h_unif_bound : ∀ z ∈ K, ∀ x₁ x₂ y₁ y₂ : ℝ,
      (kernel_exponent x₁ x₂ y₁ y₂ z).re ≤
        -c_unif * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) := by
    intro z hz x₁ x₂ y₁ y₂
    have ⟨_, hc_bound⟩ := kernel_exponent_re_bound_with_const z (hKS hz)
    calc (kernel_exponent x₁ x₂ y₁ y₂ z).re
        ≤ -(kernel_bound_const z) * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) :=
          hc_bound x₁ x₂ y₁ y₂
      _ ≤ -c_unif * (x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) :=
          mul_le_mul_of_nonneg_right (neg_le_neg (h_cunif_le z hz)) (by positivity)
  -- Step C: Construct the bound function
  refine ⟨fun p => (1 / M_denom) * Real.exp (-c_unif *
      (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)), ?_, ?_⟩
  · exact (integrable_gaussian_4d c_unif hc_unif_pos).const_mul _
  · -- Pointwise bound: ‖f·cexp(K)/D‖ ≤ exp(-c·quad) / M_denom
    intro z hz p
    rw [norm_div, norm_mul]
    -- Bound numerator: ‖f‖ * ‖cexp(K)‖ ≤ exp(-c·quad)
    have hnum_le : ‖(↑(f_eta η p.1 * f_eta η p.2) : ℂ)‖ *
        ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖ ≤
        Real.exp (-c_unif * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by
      calc ‖(↑(f_eta η p.1 * f_eta η p.2) : ℂ)‖ *
            ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖
          ≤ 1 * Real.exp (-c_unif * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by
            apply mul_le_mul
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, f_eta_bounded, f_eta_bounded, mul_one]
            · rw [Complex.norm_exp]
              exact Real.exp_le_exp_of_le (h_unif_bound z hz p.1.1 p.1.2 p.2.1 p.2.2)
            · exact norm_nonneg _
            · linarith
        _ = _ := one_mul _
    -- Bound denominator from below: ‖D‖ ≥ M_denom
    have hdenom_lb : M_denom ≤ ‖2 * ↑Real.pi * (1 - z ^ 2)‖ := h_denom_lb z hz
    -- Combine: a/b ≤ c/d when a ≤ c and d ≤ b, with b, d > 0
    have hdenom_pos : 0 < ‖2 * ↑Real.pi * (1 - z ^ 2)‖ := by linarith
    calc ‖(↑(f_eta η p.1 * f_eta η p.2) : ℂ)‖ *
          ‖cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z)‖ /
          ‖2 * ↑Real.pi * (1 - z ^ 2)‖
        ≤ Real.exp (-c_unif * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) /
          ‖2 * ↑Real.pi * (1 - z ^ 2)‖ :=
          div_le_div_of_nonneg_right hnum_le (by positivity)
      _ ≤ Real.exp (-c_unif * (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) /
          M_denom :=
          div_le_div_of_nonneg_left (Real.exp_nonneg _) hM_pos hdenom_lb
      _ = 1 / M_denom * Real.exp (-c_unif *
          (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) := by ring

/-- H_η is analytic on the strip S.

    The proof requires showing holomorphy under the integral sign via
    parametric integral theory. The integrand z ↦ f_η(p) · exp(K(p,z)) / (2π(1-z²))
    is holomorphic in z for each fixed p ∈ ℝ⁴, and is dominated by an
    L¹ Gaussian bound uniform on compact subsets of S. -/
theorem H_eta_analyticOnNhd (η : ℝ) : AnalyticOnNhd ℂ (H_eta η) S := by
  -- Analyticity on an open set in ℂ is equivalent to complex differentiability
  rw [Complex.analyticOnNhd_iff_differentiableOn S_isOpen]
  intro z hz
  unfold H_eta
  apply DifferentiableAt.differentiableWithinAt
  -- Pick ε > 0 with ball(z, ε) ⊆ S. Use r = ε/3 for inner ball, 2r for outer ball.
  obtain ⟨ε, hε_pos, hε_sub⟩ := isOpen_iff.mp S_isOpen z hz
  set r := ε / 3 with hr_def
  have hr_pos : 0 < r := by linarith
  have h2r_lt_ε : 2 * r < ε := by linarith
  have hball_sub_S : ball z (2 * r) ⊆ S :=
    fun w hw => hε_sub (ball_subset_ball (le_of_lt h2r_lt_ε) hw)
  have hcball_sub_S : closedBall z (2 * r) ⊆ S :=
    fun w hw => hε_sub (closedBall_subset_ball h2r_lt_ε hw)
  -- Get dominated bound on closedBall(z, 2r)
  obtain ⟨bd, hbd_int, hbd_bound⟩ := H_eta_integrand_dominated η
    (closedBall z (2 * r)) (isCompact_closedBall z (2 * r)) hcball_sub_S
  -- Abbreviate the integrand
  let G : ℂ → (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun w p =>
    ↑(f_eta η p.1 * f_eta η p.2) *
    cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 w) /
    (2 * ↑Real.pi * (1 - w ^ 2))
  -- The integrand G(·, p) is differentiable on S for each p
  have hG_diffOn : ∀ p, DifferentiableOn ℂ (G · p) S :=
    fun p => H_eta_integrand_differentiable η p
  -- For each p and w in ball(z, r), G(·, p) is DiffContOnCl on ball(w, r)
  -- because ball(w, r) ⊆ ball(z, 2r) ⊆ S (open), so DifferentiableOn on ball(w, r)
  -- and the function is continuous, giving DiffContOnCl
  have hG_diffContOnCl : ∀ p, ∀ w ∈ ball z r,
      DiffContOnCl ℂ (G · p) (ball w r) := by
    intro p w hw
    apply DifferentiableOn.diffContOnCl
    apply (hG_diffOn p).mono
    intro u hu
    rw [closure_ball w (ne_of_gt hr_pos)] at hu
    apply hball_sub_S
    rw [mem_ball]
    calc dist u z ≤ dist u w + dist w z := dist_triangle u w z
      _ < r + r := by linarith [mem_closedBall.mp hu, mem_ball.mp hw]
      _ ≤ 2 * r := by linarith
  -- The sphere bound: for w ∈ ball(z, r), sphere(w, r) ⊆ closedBall(z, 2r)
  have h_sphere_sub : ∀ w ∈ ball z r, sphere w r ⊆ closedBall z (2 * r) := by
    intro w hw u hu
    rw [mem_sphere] at hu; rw [mem_closedBall]
    linarith [dist_triangle u w z, (mem_ball.mp hw)]
  -- Cauchy estimate: ‖deriv (G · p) w‖ ≤ bd(p)/r for w ∈ ball(z, r)
  have h_cauchy : ∀ p, ∀ w ∈ ball z r,
      ‖deriv (G · p) w‖ ≤ bd p / r := by
    intro p w hw
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos (hG_diffContOnCl p w hw)
    intro u hu
    exact hbd_bound u (h_sphere_sub w hw hu) p
  -- Now apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  -- with s = ball(z, r), F' w p = deriv (G · p) w, bound = bd/r
  have h_hasDerivAt := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball z r)
    (F := G)
    (F' := fun w p => deriv (G · p) w)
    (bound := fun p => bd p / r)
    (ball_mem_nhds z hr_pos)
    -- hF_meas: ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (G w) volume
    (Filter.eventually_of_mem (ball_mem_nhds z hr_pos)
      (fun w _ => H_eta_integrand_aestronglyMeasurable η w))
    -- hF_int: Integrable (G z) volume
    (H_eta_integrand_integrable η z hz)
    -- hF'_meas: AEStronglyMeasurable (fun p => deriv (G · p) z) volume
    (by
      -- Express deriv(G·p)(z) as pointwise limit of difference quotients:
      --   deriv(G·p)(z) = lim_{n→∞} (n+1) · (G(z + (n+1)⁻¹, p) - G(z, p))
      -- Each G(w, ·) is ae-strongly measurable.
      set seq : ℕ → (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun n p =>
        ((n : ℂ) + 1) * (G (z + ((n : ℂ) + 1)⁻¹) p - G z p) with hseq_def
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := seq)
      · intro n
        apply AEStronglyMeasurable.const_mul
        exact (H_eta_integrand_aestronglyMeasurable η _).sub
          (H_eta_integrand_aestronglyMeasurable η _)
      · filter_upwards with p
        have hG_diff : HasDerivAt (G · p) (deriv (G · p) z) z :=
          ((hG_diffOn p).differentiableAt (S_isOpen.mem_nhds hz)).hasDerivAt
        -- HasDerivAt says (G(z+h,p) - G(z,p))/h → deriv(G·p)(z) as h → 0
        -- We need (n+1)*(G(z+1/(n+1),p) - G(z,p)) → deriv(G·p)(z) as n → ∞
        rw [hasDerivAt_iff_tendsto_slope_zero] at hG_diff
        -- hG_diff : Tendsto (fun h => (G(z+h,p) - G(z,p))/h) (𝓝[≠] 0) (𝓝 (deriv ...))
        -- The sequence h_n = 1/(n+1) → 0 with h_n ≠ 0
        -- (n+1)*(G(z+h_n,p) - G(z,p)) = (G(z+h_n,p) - G(z,p))/h_n
        have : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) Filter.atTop (𝓝[≠] 0) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · -- (n+1)⁻¹ → 0 in ℂ
            have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) := by
              apply Filter.Tendsto.comp tendsto_inv_atTop_zero
              exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
            have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
            simp only [Complex.ofReal_zero, Function.comp_def] at h2
            refine h2.congr (fun n => ?_)
            simp [Complex.ofReal_natCast, Complex.ofReal_one]
          · -- Each (n+1)⁻¹ ≠ 0
            filter_upwards with n
            simp [inv_eq_zero, Nat.cast_add_one_ne_zero]
        have key := hG_diff.comp this
        -- key says (G(z + 1/(n+1), p) - G(z, p)) / (1/(n+1)) → deriv(G·p)(z)
        -- = (n+1) * (G(z + 1/(n+1), p) - G(z, p)) → deriv(G·p)(z)
        convert key using 1
        ext n
        simp [hseq_def])
    -- h_bound: ∀ᵐ p, ∀ w ∈ ball z r, ‖deriv (G · p) w‖ ≤ bd p / r
    (Filter.Eventually.of_forall (fun p w hw => h_cauchy p w hw))
    -- bound_integrable
    (hbd_int.div_const r)
    -- h_diff: ∀ᵐ p, ∀ w ∈ ball z r, HasDerivAt (G · p) (deriv (G · p) w) w
    (Filter.Eventually.of_forall (fun p w hw => by
      have hw_in_S : w ∈ S :=
        hball_sub_S (ball_subset_ball (by linarith : r ≤ 2 * r) hw)
      exact ((hG_diffOn p).differentiableAt (S_isOpen.mem_nhds hw_in_S)).hasDerivAt))).2
  exact h_hasDerivAt.differentiableAt

/-! ### Bound -/

/-! ## The correct bound function -/

/-- The correct bound from equation (43) of the paper, simplified:
    π · ‖1 - z²‖ / (2(1 - Re(z)²)).

    This equals the more complex expression
    π · ((1+a)² + b²) · ((1-a)² + b²) / (2(1-a²) · √((1-a²+b²)² + 4a²b²))
    after simplification using ‖1-z²‖² = ((1+a)²+b²)·((1-a)²+b²). -/
def bound_43_paper (a b : ℝ) : ℝ :=
  Real.pi * Real.sqrt (((1 - a ^ 2 + b ^ 2) ^ 2 + (2 * a * b) ^ 2)) /
    (2 * (1 - a ^ 2))

/-- bound_43_paper equals π · ‖1-z²‖ / (2(1-a²)). -/
lemma bound_43_paper_eq_norm (z : ℂ) (hz : z ∈ S) :
    bound_43_paper z.re z.im =
      Real.pi * ‖(1 - z ^ 2 : ℂ)‖ / (2 * (1 - z.re ^ 2)) := by
  unfold bound_43_paper
  congr 1; congr 1
  rw [Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, sq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
             Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Helper lemmas: Re(1/(1±z)) > 0 -/

/-- Re(1/(1+z)) = (1+a) / ((1+a)² + b²) for z = a + bi. -/
lemma re_inv_one_add (z : ℂ) :
    (1 / (1 + z)).re = (1 + z.re) / ((1 + z.re) ^ 2 + z.im ^ 2) := by
  rw [one_div, Complex.inv_re]
  simp [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        Complex.normSq_apply]
  ring

/-- Re(1/(1-z)) = (1-a) / ((1-a)² + b²) for z = a + bi. -/
lemma re_inv_one_sub (z : ℂ) :
    (1 / (1 - z)).re = (1 - z.re) / ((1 - z.re) ^ 2 + z.im ^ 2) := by
  rw [one_div, Complex.inv_re]
  simp [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        Complex.normSq_apply]
  ring

/-- Re(1/(1+z)) > 0 when z ∈ S. -/
lemma re_inv_one_add_pos {z : ℂ} (hz : z ∈ S) :
    0 < (1 / (1 + z)).re := by
  rw [re_inv_one_add]
  rw [mem_S_iff] at hz
  have hnum : 0 < 1 + z.re := by linarith [abs_lt.mp hz |>.1]
  have hden : 0 < (1 + z.re) ^ 2 + z.im ^ 2 := by nlinarith
  exact div_pos hnum hden

/-- Re(1/(1-z)) > 0 when z ∈ S. -/
lemma re_inv_one_sub_pos {z : ℂ} (hz : z ∈ S) :
    0 < (1 / (1 - z)).re := by
  rw [re_inv_one_sub]
  rw [mem_S_iff] at hz
  have hnum : 0 < 1 - z.re := by linarith [abs_lt.mp hz |>.2]
  have hden : 0 < (1 - z.re) ^ 2 + z.im ^ 2 := by nlinarith
  exact div_pos hnum hden

/-! ## Kernel splitting in (u,v) coordinates -/

lemma kernel_exponent_uv_split (x₁ x₂ y₁ y₂ : ℝ) (z : ℂ)
    (hz : (1 : ℂ) - z ^ 2 ≠ 0) :
    kernel_exponent x₁ x₂ y₁ y₂ z =
      -(↑((x₁ + y₁) ^ 2 + (x₂ + y₂) ^ 2) / (2 * (1 + z))) +
      -(↑((x₁ - y₁) ^ 2 + (x₂ - y₂) ^ 2) / (2 * (1 - z))) := by
  unfold kernel_exponent
  have h1z : (1 : ℂ) + z ≠ 0 := by
    intro h
    apply hz
    rw [show (1 : ℂ) - z ^ 2 = (1 - z) * (1 + z) from by ring, h, mul_zero]
  have h1z' : (1 : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    rw [show (1 : ℂ) - z ^ 2 = (1 + z) * (1 - z) from by ring, h, mul_zero]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h1z2 : (2 : ℂ) * (1 + z) ≠ 0 := mul_ne_zero h2 h1z
  have h1z2' : (2 : ℂ) * (1 - z) ≠ 0 := mul_ne_zero h2 h1z'
  field_simp
  push_cast
  ring

/-! ## 2D Gaussian integral -/

lemma integral_gaussian_2d (c : ℝ) (hc : 0 < c) :
    ∫ p : ℝ × ℝ, Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2)) = Real.pi / c := by
  have h_factor : ∀ p : ℝ × ℝ,
      Real.exp (-c * (p.1 ^ 2 + p.2 ^ 2)) =
      Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
    intro p; rw [← Real.exp_add]; congr 1; ring
  simp_rw [h_factor]
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul
    (f := fun x => Real.exp (-c * x ^ 2))
    (g := fun y => Real.exp (-c * y ^ 2))]
  have h_1d : ∫ x : ℝ, Real.exp (-c * x ^ 2) = Real.sqrt (Real.pi / c) :=
    integral_gaussian c
  rw [h_1d]
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / c)]
  rw [show Real.pi / c * (Real.pi / c) = (Real.pi / c) ^ 2 from by ring]
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.pi / c)]

/-! ## Product of Re(1/(1±z)) -/

lemma re_inv_prod_eq (z : ℂ) (hz : z ∈ S) :
    (1 / (1 + z)).re * (1 / (1 - z)).re =
      (1 - z.re ^ 2) / ((1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2) := by
  rw [re_inv_one_add, re_inv_one_sub]
  have hd1 : (0 : ℝ) < (1 + z.re) ^ 2 + z.im ^ 2 := by
    rw [mem_S_iff] at hz; nlinarith [abs_lt.mp hz |>.1]
  have hd2 : (0 : ℝ) < (1 - z.re) ^ 2 + z.im ^ 2 := by
    rw [mem_S_iff] at hz; nlinarith [abs_lt.mp hz |>.2]
  rw [div_mul_div_comm]
  congr 1
  · ring
  · ring

/-! ## The change-of-variable map (u,v) ↔ (x,y) -/

def uvMap : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) :=
  fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => ((x₁ + y₁, x₂ + y₂), (x₁ - y₁, x₂ - y₂))

def uvMapInv : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) :=
  fun ⟨⟨u₁, u₂⟩, ⟨v₁, v₂⟩⟩ => (((u₁ + v₁) / 2, (u₂ + v₂) / 2),
                                   ((u₁ - v₁) / 2, (u₂ - v₂) / 2))

/-! ## Coupled Gaussian integrals -/

lemma integral_four_var_factor
    (f g : ℝ → ℝ → ℝ) :
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      f p.1.1 p.2.1 * g p.1.2 p.2.2 =
    (∫ p : ℝ × ℝ, f p.1 p.2) * (∫ p : ℝ × ℝ, g p.1 p.2) := by
  let inner : ℝ × (ℝ × ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc.symm.trans
      (((MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).prodCongr (MeasurableEquiv.refl ℝ)).trans
        MeasurableEquiv.prodAssoc)
  let e : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl ℝ).prodCongr inner).trans
        MeasurableEquiv.prodAssoc.symm)
  have he : ∀ p : (ℝ × ℝ) × (ℝ × ℝ), e p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := by
    intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  have hmp : MeasurePreserving e volume volume := by
    have h_assoc : MeasurePreserving (MeasurableEquiv.prodAssoc :
        (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ ℝ × ℝ × (ℝ × ℝ)) volume volume := volume_preserving_prodAssoc
    have h_assoc2 : MeasurePreserving (MeasurableEquiv.prodAssoc :
        (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ) volume volume := volume_preserving_prodAssoc
    have h_swap : MeasurePreserving Prod.swap
        (volume : Measure (ℝ × ℝ)) volume :=
      Measure.measurePreserving_swap
    have h_inner : MeasurePreserving inner volume volume :=
      (h_assoc2.comp ((h_swap.prod (MeasurePreserving.id (μ := (volume : Measure ℝ)))))).comp
        h_assoc2.symm
    exact h_assoc.symm.comp
      (((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod h_inner).comp h_assoc)
  rw [← hmp.integral_comp' (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1.1 p.2.1 * g p.1.2 p.2.2)]
  simp_rw [he]
  rw [Measure.volume_eq_prod]
  rw [integral_prod_mul (fun p : ℝ × ℝ => f p.1 p.2) (fun p : ℝ × ℝ => g p.1 p.2)]

lemma coupled_gaussian_integral_2d (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ p : ℝ × ℝ, Real.exp (-(a * (p.1 + p.2) ^ 2 + b * (p.1 - p.2) ^ 2)) =
    Real.pi / (2 * Real.sqrt (a * b)) := by
  have hab_pos : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := ne_of_gt hab_pos
  have h_integrable : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(a * (p.1 + p.2) ^ 2 + b * (p.1 - p.2) ^ 2))) volume := by
    have hm : 0 < min a b := lt_min ha hb
    have hm2 : 0 < 2 * min a b := by positivity
    apply Integrable.mono'
    · show Integrable (fun p : ℝ × ℝ => Real.exp (-(2 * min a b * (p.1 ^ 2 + p.2 ^ 2))))
      rw [Measure.volume_eq_prod]
      simp_rw [show ∀ p : ℝ × ℝ, -(2 * min a b * (p.1 ^ 2 + p.2 ^ 2)) =
          (-(2 * min a b) * p.1 ^ 2) + (-(2 * min a b) * p.2 ^ 2) from by intro p; ring,
        Real.exp_add]
      exact (integrable_exp_neg_mul_sq hm2).mul_prod (integrable_exp_neg_mul_sq hm2)
    · exact (Measurable.aestronglyMeasurable (by measurability))
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp_of_le; apply neg_le_neg
      linarith [mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg (p.1 + p.2)),
        mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg (p.1 - p.2)),
        show (p.1 + p.2) ^ 2 + (p.1 - p.2) ^ 2 = 2 * (p.1 ^ 2 + p.2 ^ 2) from by ring]
  have h_expand : ∀ p : ℝ × ℝ,
      -(a * (p.1 + p.2) ^ 2 + b * (p.1 - p.2) ^ 2) =
      -((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2) +
      (-(4 * a * b / (a + b) * p.1 ^ 2)) := by
    intro p; field_simp; ring
  simp_rw [h_expand, Real.exp_add]
  have h_comm : ∀ p : ℝ × ℝ,
      Real.exp (-((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2)) *
      Real.exp (-(4 * a * b / (a + b) * p.1 ^ 2)) =
      Real.exp (-(4 * a * b / (a + b) * p.1 ^ 2)) *
      Real.exp (-((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2)) := by
    intro p; ring
  simp_rw [h_comm]
  have h_orig_eq : ∀ p : ℝ × ℝ,
      Real.exp (-(4 * a * b / (a + b) * p.1 ^ 2)) *
      Real.exp (-((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2)) =
      Real.exp (-(a * (p.1 + p.2) ^ 2 + b * (p.1 - p.2) ^ 2)) := by
    intro p; rw [← Real.exp_add]; congr 1; field_simp; ring
  have h_int : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(4 * a * b / (a + b) * p.1 ^ 2)) *
      Real.exp (-((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2))) (volume.prod volume) := by
    have heq : (fun p : ℝ × ℝ =>
        Real.exp (-(4 * a * b / (a + b) * p.1 ^ 2)) *
        Real.exp (-((a + b) * (p.2 + (a - b) / (a + b) * p.1) ^ 2))) =
      (fun p : ℝ × ℝ => Real.exp (-(a * (p.1 + p.2) ^ 2 + b * (p.1 - p.2) ^ 2))) := by
      ext p; exact h_orig_eq p
    rw [heq, ← Measure.volume_eq_prod]
    exact h_integrable
  rw [Measure.volume_eq_prod, integral_prod _ h_int]
  simp_rw [integral_const_mul]
  have h_inner : ∀ s : ℝ,
      (∫ t : ℝ, Real.exp (-((a + b) * (t + (a - b) / (a + b) * s) ^ 2))) =
      √(Real.pi / (a + b)) := by
    intro s
    have h1 : ∫ t : ℝ, Real.exp (-((a + b) * (t + (a - b) / (a + b) * s) ^ 2)) =
        ∫ t : ℝ, Real.exp (-((a + b) * t ^ 2)) :=
      integral_add_right_eq_self
        (fun t => Real.exp (-((a + b) * t ^ 2))) ((a - b) / (a + b) * s)
    rw [h1]
    have h2 : (fun t : ℝ => Real.exp (-((a + b) * t ^ 2))) =
        (fun t : ℝ => Real.exp (-(a + b) * t ^ 2)) := by ext t; congr 1; ring
    rw [h2]; exact integral_gaussian (a + b)
  simp_rw [h_inner, integral_mul_const]
  set C := 4 * a * b / (a + b)
  have hC_eq : (fun x : ℝ => Real.exp (-(C * x ^ 2))) = (fun x : ℝ => Real.exp (-C * x ^ 2)) := by
    ext x; congr 1; ring
  rw [hC_eq, integral_gaussian C]
  rw [show Real.pi / C = Real.pi * (a + b) / (4 * a * b) from by simp only [C]; field_simp]
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi * (a + b) / (4 * a * b))]
  rw [show Real.pi * (a + b) / (4 * a * b) * (Real.pi / (a + b)) = Real.pi ^ 2 / (4 * (a * b)) from by
    field_simp]
  rw [Real.sqrt_div' _ (by positivity)]
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.pi)]
  rw [show (4 : ℝ) * (a * b) = (2 * √(a * b)) ^ 2 from by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * √(a * b))]

lemma coupled_gaussian_4d (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-(a * ((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2) +
                  b * ((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2))) =
    Real.pi ^ 2 / (4 * a * b) := by
  have h_factor : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
      -(a * ((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2) +
        b * ((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2)) =
      (-(a * (p.1.1 + p.2.1) ^ 2 + b * (p.1.1 - p.2.1) ^ 2)) +
      (-(a * (p.1.2 + p.2.2) ^ 2 + b * (p.1.2 - p.2.2) ^ 2)) := by
    intro p; ring
  simp_rw [h_factor, Real.exp_add]
  rw [integral_four_var_factor
    (fun x y => Real.exp (-(a * (x + y) ^ 2 + b * (x - y) ^ 2)))
    (fun x y => Real.exp (-(a * (x + y) ^ 2 + b * (x - y) ^ 2)))]
  rw [coupled_gaussian_integral_2d a b ha hb, div_mul_div_comm]
  congr 1
  · ring
  · rw [show 2 * Real.sqrt (a * b) * (2 * Real.sqrt (a * b)) =
        4 * (Real.sqrt (a * b) * Real.sqrt (a * b)) from by ring,
      Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ a * b)]
    ring

/-! ## Main bound theorem -/

lemma integral_exp_re_kernel (z : ℂ) (hz : z ∈ S) :
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re =
    Real.pi ^ 2 * ‖(1 - z ^ 2 : ℂ)‖ ^ 2 / (1 - z.re ^ 2) := by
  have h1z2_ne : (1 : ℂ) - z ^ 2 ≠ 0 := one_sub_sq_ne_zero_on_S z hz
  have h_split : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
    kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z =
    -(↑((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2) / (2 * (1 + z))) +
    -(↑((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2) / (2 * (1 - z))) :=
    fun p => kernel_exponent_uv_split p.1.1 p.1.2 p.2.1 p.2.2 z h1z2_ne
  simp_rw [h_split]
  have h1z : (1 : ℂ) + z ≠ 0 := by
    intro h; apply h1z2_ne
    rw [show (1 : ℂ) - z ^ 2 = (1 - z) * (1 + z) from by ring, h, mul_zero]
  have h1z' : (1 : ℂ) - z ≠ 0 := by
    intro h; apply h1z2_ne
    rw [show (1 : ℂ) - z ^ 2 = (1 + z) * (1 - z) from by ring, h, mul_zero]
  have hc_plus := re_inv_one_add_pos hz
  have hc_minus := re_inv_one_sub_pos hz
  have h_re_neg_real_div (r : ℝ) (w : ℂ) (hw : w ≠ 0) :
      (-(↑r / (2 * w))).re = -(r * (1/w).re / 2) := by
    rw [show (2 : ℂ) * w = ↑(2 : ℝ) * w from by push_cast; ring]
    rw [Complex.neg_re, Complex.div_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
        Complex.normSq_mul, Complex.normSq_ofReal]
    rw [one_div, Complex.inv_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_re_split : ∀ (p : (ℝ × ℝ) × ℝ × ℝ),
    (-(↑((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2) / (2 * (1 + z))) +
     -(↑((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2) / (2 * (1 - z)))).re =
    -((1 / (1 + z)).re / 2 * ((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2)) +
    -((1 / (1 - z)).re / 2 * ((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2)) := by
    intro p
    rw [Complex.add_re, h_re_neg_real_div _ _ h1z, h_re_neg_real_div _ _ h1z']
    ring
  simp_rw [h_re_split]
  set cp := (1 / (1 + z)).re / 2 with hcp_def
  set cm := (1 / (1 - z)).re / 2 with hcm_def
  have hcp_pos : 0 < cp := by positivity
  have hcm_pos : 0 < cm := by positivity
  have h_neg_add : ∀ (p : (ℝ × ℝ) × ℝ × ℝ),
      -(cp * ((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2)) +
      -(cm * ((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2)) =
      -(cp * ((p.1.1 + p.2.1) ^ 2 + (p.1.2 + p.2.2) ^ 2) +
        cm * ((p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2)) := by
    intro p; ring
  simp_rw [h_neg_add]
  rw [coupled_gaussian_4d cp cm hcp_pos hcm_pos]
  rw [hcp_def, hcm_def]
  have h_prod := re_inv_prod_eq z hz
  have ha2 : 0 < 1 - z.re ^ 2 := by
    rw [mem_S_iff] at hz; nlinarith [abs_lt.mp hz |>.1, abs_lt.mp hz |>.2]
  have h_normsq : ‖(1 - z ^ 2 : ℂ)‖ ^ 2 =
      (1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
               Complex.mul_re, Complex.mul_im,
               Complex.ofReal_re, Complex.ofReal_im, sq]
    ring
  rw [h_normsq]
  have hRp : (0 : ℝ) < (1 / (1 + z)).re := hc_plus
  have hRm : (0 : ℝ) < (1 / (1 - z)).re := hc_minus
  have h_normsq_pos : (0 : ℝ) < (1 - z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 := by
    nlinarith [h_prod, mul_pos hRp hRm]
  have h_lhs_simp : Real.pi ^ 2 / (4 * ((1 / (1 + z)).re / 2) * ((1 / (1 - z)).re / 2)) =
      Real.pi ^ 2 / ((1 / (1 + z)).re * (1 / (1 - z)).re) := by
    have : (1 / (1 + z)).re ≠ 0 := ne_of_gt hc_plus
    have : (1 / (1 - z)).re ≠ 0 := ne_of_gt hc_minus
    field_simp; norm_num
  rw [h_lhs_simp, h_prod, div_div_eq_mul_div]

lemma H_eta_integrand_norm_le (η : ℝ) (z : ℂ) (hz : z ∈ S)
    (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))‖ ≤
    Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re /
      ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ := by
  rw [norm_div, norm_mul, Complex.norm_exp]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖(↑(f_eta η p.1 * f_eta η p.2) : ℂ)‖ *
        Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re
      ≤ 1 * Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, f_eta_bounded, f_eta_bounded, mul_one]
    _ = Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re := one_mul _

lemma integrable_exp_re_kernel (z : ℂ) (hz : z ∈ S) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re) volume := by
  have h := (cexp_kernel_integrable z hz).norm
  simp_rw [Complex.norm_exp] at h
  exact h

lemma integrable_exp_re_div_norm (z : ℂ) (hz : z ∈ S) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re /
      ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖) volume := by
  apply Integrable.div_const
  exact integrable_exp_re_kernel z hz

lemma norm_denom_eq (z : ℂ) :
    ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ =
    2 * Real.pi * ‖(1 - z ^ 2 : ℂ)‖ := by
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

lemma integral_norm_le_integral_exp_re_div (η : ℝ) (z : ℂ) (hz : z ∈ S) :
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      ‖↑(f_eta η p.1 * f_eta η p.2) *
      Complex.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))‖ ≤
    (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re) /
    ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ := by
  have h1 : ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      ‖↑(f_eta η p.1 * f_eta η p.2) *
      cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))‖ ≤
    ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re /
      ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ :=
    MeasureTheory.integral_mono
      (H_eta_integrand_integrable η z hz).norm
      (integrable_exp_re_div_norm z hz)
      (H_eta_integrand_norm_le η z hz)
  have h2 : ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re /
      ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ =
    (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re) /
    ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ :=
    integral_div _ _
  linarith

/-- The explicit bound (43) for |H_η(z)| on the strip.
    **Reference:** Braverman–Naor, Lemma 4.2, inequality (43). -/
theorem H_eta_bound_paper (η : ℝ) (z : ℂ) (hz : z ∈ S) :
    ‖H_eta η z‖ ≤ bound_43_paper z.re z.im := by
  rw [bound_43_paper_eq_norm z hz]
  set F := fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    ↑(f_eta η p.1 * f_eta η p.2) *
    cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
    (2 * ↑Real.pi * (1 - z ^ 2)) with hF_def
  set I_exp := ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
    Real.exp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z).re with hI_exp_def
  set D_norm := ‖(2 * ↑Real.pi * (1 - z ^ 2) : ℂ)‖ with hD_norm_def
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1z2_ne : (1 : ℂ) - z ^ 2 ≠ 0 := one_sub_sq_ne_zero_on_S z hz
  have h1z2_pos : 0 < ‖(1 - z ^ 2 : ℂ)‖ := norm_pos_iff.mpr h1z2_ne
  have ha2 : 0 < 1 - z.re ^ 2 := by
    rw [mem_S_iff] at hz; nlinarith [abs_lt.mp hz |>.1, abs_lt.mp hz |>.2]
  have hD_pos : 0 < D_norm := by
    rw [hD_norm_def]; exact norm_pos_iff.mpr (denom_ne_zero_on_S z hz)
  have hD_eq : D_norm = 2 * Real.pi * ‖(1 - z ^ 2 : ℂ)‖ := norm_denom_eq z
  unfold H_eta
  have h_norm_int : ‖∫ p, F p‖ ≤ I_exp / D_norm :=
    le_trans (norm_integral_le_integral_norm _)
      (integral_norm_le_integral_exp_re_div η z hz)
  have h_I_exp : I_exp = Real.pi ^ 2 * ‖(1 - z ^ 2 : ℂ)‖ ^ 2 / (1 - z.re ^ 2) :=
    integral_exp_re_kernel z hz
  have h_bound : I_exp / D_norm =
      Real.pi * ‖(1 - z ^ 2 : ℂ)‖ / (2 * (1 - z.re ^ 2)) := by
    rw [h_I_exp, hD_eq]
    field_simp
  calc ‖∫ p, F p‖
      ≤ I_exp / D_norm := h_norm_int
    _ = Real.pi * ‖(1 - z ^ 2 : ℂ)‖ / (2 * (1 - z.re ^ 2)) := h_bound

/-! ### Oddness -/

/-- The graph {y ∈ ℝ² : y₂ = η · h₅(y₁)} has Lebesgue measure zero.
    This is because it is the graph of a continuous function. -/
lemma graph_h5_null (η : ℝ) :
    MeasureTheory.volume {p : ℝ × ℝ | p.2 = η * h5 p.1} = 0 := by
  -- The graph of a continuous function ℝ → ℝ has measure zero in ℝ²
  -- via Fubini: each fiber {x₂ : x₂ = η * h5 x₁} is a singleton with measure 0.
  have hm : Measurable (fun x : ℝ => η * h5 x) := measurable_const.mul h5_measurable
  simp_rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
  rw [Measure.measure_prod_null (measurableSet_graph hm)]
  filter_upwards with x
  have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = η * h5 p.1} = {η * h5 x} := by
    ext y; simp
  rw [this]
  exact Real.volume_singleton

/-- f_eta composed with negation equals -f_eta almost everywhere. -/
lemma f_eta_neg_ae (η : ℝ) :
    ∀ᵐ (p : ℝ × ℝ) ∂MeasureTheory.volume,
      f_eta η (-p.1, -p.2) = -(f_eta η (p.1, p.2)) := by
  have h_null : MeasureTheory.volume {p : ℝ × ℝ | p.2 = η * h5 p.1} = 0 := graph_h5_null η
  have h_sub : {p : ℝ × ℝ | ¬(f_eta η (-p.1, -p.2) = -(f_eta η (p.1, p.2)))} ⊆
      {p : ℝ × ℝ | p.2 = η * h5 p.1} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra hne
    exact hp (f_eta_neg_of_ne η p.1 p.2 hne)
  exact measure_mono_null h_sub h_null

/-- Negation on ℝ × ℝ preserves volume. -/
lemma measurePreserving_neg_prod :
    MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
      MeasureTheory.volume MeasureTheory.volume :=
  Measure.measurePreserving_neg _

/-- The map (x, y) ↦ (x, -y) on (ℝ²) × (ℝ²) preserves Lebesgue measure. -/
lemma measurePreserving_id_neg :
    MeasurePreserving (Prod.map id (Neg.neg : ℝ × ℝ → ℝ × ℝ))
      (MeasureTheory.volume : Measure ((ℝ × ℝ) × (ℝ × ℝ)))
      (MeasureTheory.volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) :=
  MeasurePreserving.prod
    (MeasurePreserving.id (μ := (MeasureTheory.volume : Measure (ℝ × ℝ))))
    measurePreserving_neg_prod

/-- Key identity: the H_eta integrand at -z, with y negated, equals minus the integrand at z.
    This holds for all p where p.2.2 ≠ η * h5 p.2.1. -/
lemma H_eta_integrand_neg_z_neg_y (η : ℝ) (z : ℂ) (x : ℝ × ℝ) (y₁ y₂ : ℝ)
    (hne : y₂ ≠ η * h5 y₁) :
    (↑(f_eta η x * f_eta η (-y₁, -y₂)) *
      cexp (kernel_exponent x.1 x.2 (-y₁) (-y₂) (-z)) /
      (2 * ↑Real.pi * (1 - z ^ 2))) =
    -(↑(f_eta η x * f_eta η (y₁, y₂)) *
      cexp (kernel_exponent x.1 x.2 y₁ y₂ z) /
      (2 * ↑Real.pi * (1 - z ^ 2))) := by
  rw [kernel_exponent_neg_z_neg_y]
  have hf : f_eta η (-y₁, -y₂) = -(f_eta η (y₁, y₂)) := f_eta_neg_of_ne η y₁ y₂ hne
  rw [hf, mul_neg, ofReal_neg, neg_mul, neg_div]

/-- H_η is odd: H_η(-z) = -H_η(z).
    Follows by the substitution (x,y) ↦ (x,-y) in the integral, using:
    - kernel_exponent(x,-y,-z) = kernel_exponent(x,y,z)
    - f_η(-y) = -f_η(y) a.e. (from h₅ being odd) -/
theorem H_eta_odd (η : ℝ) (z : ℂ) (_hz : z ∈ S) :
    H_eta η (-z) = -H_eta η z := by
  simp only [H_eta, neg_sq]
  suffices h : (∫ (p : (ℝ × ℝ) × ℝ × ℝ),
      ↑(f_eta η p.1 * f_eta η p.2) * cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 (-z)) /
        (2 * ↑Real.pi * (1 - z ^ 2))) =
    -(∫ (p : (ℝ × ℝ) × ℝ × ℝ),
      ↑(f_eta η p.1 * f_eta η p.2) * cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
        (2 * ↑Real.pi * (1 - z ^ 2))) by
    exact h
  -- Step 1: Change variables (x, y) ↦ (x, -y) in the LHS integral.
  -- The map Prod.map id Neg.neg preserves volume.
  have hmeas : MeasurePreserving (Prod.map id (Neg.neg : ℝ × ℝ → ℝ × ℝ))
      MeasureTheory.volume MeasureTheory.volume := measurePreserving_id_neg
  -- The integrand at -z composed with (x,y) ↦ (x,-y) equals -(integrand at z), a.e.
  -- Step 2: Show integrands are a.e. equal after substitution
  have h_ae : ∀ᵐ (p : (ℝ × ℝ) × ℝ × ℝ) ∂MeasureTheory.volume,
      ↑(f_eta η (Prod.map id Neg.neg p).1 * f_eta η (Prod.map id Neg.neg p).2) *
        cexp (kernel_exponent (Prod.map id Neg.neg p).1.1 (Prod.map id Neg.neg p).1.2
          (Prod.map id Neg.neg p).2.1 (Prod.map id Neg.neg p).2.2 (-z)) /
        (2 * ↑Real.pi * (1 - z ^ 2)) =
      -(↑(f_eta η p.1 * f_eta η p.2) * cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
        (2 * ↑Real.pi * (1 - z ^ 2))) := by
    -- Simplify Prod.map id Neg.neg
    simp only [Prod.map, id]
    -- Now need: for a.e. p, the identity holds.
    -- Use f_eta_neg_ae to get f_eta η (-y) = -f_eta η y a.e.,
    -- and kernel_exponent_neg_z_neg_y for the kernel.
    -- The a.e. condition is on p.2 only (the y component)
    have h_neg_ae := f_eta_neg_ae η
    -- Lift the a.e. statement from ℝ × ℝ to (ℝ × ℝ) × (ℝ × ℝ) via the projection
    have h_lift : ∀ᵐ (p : (ℝ × ℝ) × (ℝ × ℝ)) ∂MeasureTheory.volume,
        f_eta η (-p.2.1, -p.2.2) = -(f_eta η (p.2.1, p.2.2)) := by
      -- The exceptional set {(x,y) | y₂ = η · h₅(y₁)} has measure zero
      have h_sub : {q : (ℝ × ℝ) × (ℝ × ℝ) |
          ¬(f_eta η (-q.2.1, -q.2.2) = -(f_eta η (q.2.1, q.2.2)))} ⊆
          Set.univ ×ˢ {y : ℝ × ℝ | y.2 = η * h5 y.1} := by
        intro ⟨x, y⟩ hp
        simp only [Set.mem_setOf_eq] at hp
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]
        by_contra hne
        exact hp (f_eta_neg_of_ne η y.1 y.2 hne)
      have h_zero : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ)))
          (Set.univ ×ˢ {y : ℝ × ℝ | y.2 = η * h5 y.1}) = 0 := by
        rw [show (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))) =
            (volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ)) from rfl]
        rw [Measure.prod_prod]
        simp [graph_h5_null η]
      exact measure_mono_null h_sub h_zero
    filter_upwards [h_lift] with p hp
    -- Now p.2 = (y₁, y₂) and we know f_eta η (-y₁, -y₂) = -f_eta η (y₁, y₂)
    show ↑(f_eta η p.1 * f_eta η (-p.2)) *
        cexp (kernel_exponent p.1.1 p.1.2 (-p.2).1 (-p.2).2 (-z)) /
        (2 * ↑Real.pi * (1 - z ^ 2)) =
      -(↑(f_eta η p.1 * f_eta η p.2) *
        cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
        (2 * ↑Real.pi * (1 - z ^ 2)))
    have h1 : (-p.2).1 = -p.2.1 := rfl
    have h2 : (-p.2).2 = -p.2.2 := rfl
    rw [h1, h2, kernel_exponent_neg_z_neg_y]
    have hf : f_eta η (-p.2) = f_eta η (-p.2.1, -p.2.2) := rfl
    rw [hf, hp, mul_neg, ofReal_neg, neg_mul, neg_div]
  -- Step 3: Use change of variables to rewrite the LHS integral
  -- ∫ F(-z, p) dp = ∫ F(-z, Φ(p)) dp (by measure-preserving Φ)
  --              = ∫ -(F(z, p)) dp (by h_ae)
  --              = -∫ F(z, p) dp
  have h_embed : MeasurableEmbedding (Prod.map id (Neg.neg : ℝ × ℝ → ℝ × ℝ)) :=
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (ℝ × ℝ))
      (MeasurableEquiv.neg (ℝ × ℝ))).measurableEmbedding
  -- Rewrite LHS as integral of composed function
  conv_lhs => rw [← hmeas.integral_comp h_embed]
  -- Now the LHS is ∫ F(-z, Φ(p)) dp, which by h_ae equals ∫ -(F(z, p)) dp
  rw [integral_congr_ae h_ae, integral_neg]

/-- H_η is bounded on compact subsets of S. -/
theorem H_eta_bounded_on_compact (η : ℝ) (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ M : ℝ, ∀ z ∈ K, ‖H_eta η z‖ ≤ M :=
  hK.exists_bound_of_continuousOn ((H_eta_analyticOnNhd η).continuousOn.mono hKS)

/-- The derivative H_η' is also bounded on compact subsets of S. -/
theorem H_eta_deriv_bounded_on_compact (η : ℝ) (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ M : ℝ, ∀ z ∈ K, ‖deriv (H_eta η) z‖ ≤ M :=
  hK.exists_bound_of_continuousOn
    ((H_eta_analyticOnNhd η).deriv.continuousOn.mono hKS)

end Braverman
