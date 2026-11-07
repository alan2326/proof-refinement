/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma43
import LeanProof.Defs.Kernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Theorem 4.4 Core definitions and normalization

## Convention
- `Phi` is the paper's `ϕ`, defined as `4π · Re(H_η(i)/i)`
- `F44` is the paper's symmetric two-parameter function F(u₁,u₂)
- All endpoint values are real — no complex-valued target theorems
- Theorem 4.4 reduces to `Phi η > Phi 0` for small positive η

## Partial derivative notation
- `dAB_F44` means A derivatives in u₁, B derivatives in u₂
  For example, `d13_F44` = ∂⁴F44/(∂u₁ · ∂u₂³)
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## A1. Real-valued target functions -/

/-- The real-valued function `φ(η) = Re(H_η(i)/i)`. -/
def varphi (η : ℝ) : ℝ := (H_eta η Complex.I / Complex.I).re

/-- The scaled version `Φ(η) = 4π · φ(η)`. The main proof works with Φ. -/
def Phi (η : ℝ) : ℝ := (4 * Real.pi) * varphi η

/-! ## A2. The paper's two-parameter function F -/

/-- The two-parameter bridge function `F(u₁,u₂)` for Theorem 4.4.
    Normalized to match `H_eta` at `z = i`:
    F(u₁,u₂) = ∫∫∫∫_{x₂ > u₁·h₅(x₁), y₂ > u₂·h₅(y₁)}
                  exp(-(x₁²+x₂²+y₁²+y₂²)/2) · sin(x₁y₁ + x₂y₂) -/
def F44 (u₁ u₂ : ℝ) : ℝ :=
  ∫ x₁ : ℝ, ∫ y₁ : ℝ,
    ∫ x₂ in Set.Ioi (u₁ * h5 x₁), ∫ y₂ in Set.Ioi (u₂ * h5 y₁),
      Real.exp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
      Real.sin (x₁ * y₁ + x₂ * y₂)

/-! ## Partial derivative definitions

Convention: `dAB_F44 u₁ u₂` = (∂^(A+B) F44 / ∂u₁^A ∂u₂^B)(u₁, u₂) -/

/-- ∂²F44/∂u₁² -/
def d20_F44 (u₁ u₂ : ℝ) : ℝ := iteratedDeriv 2 (fun t => F44 t u₂) u₁

/-- ∂²F44/(∂u₁ ∂u₂) -/
def d11_F44 (u₁ u₂ : ℝ) : ℝ := deriv (fun s => deriv (fun t => F44 t s) u₁) u₂

/-- ∂⁴F44/∂u₁⁴ -/
def d40_F44 (u₁ u₂ : ℝ) : ℝ := iteratedDeriv 4 (fun t => F44 t u₂) u₁

/-- ∂⁴F44/(∂u₁ · ∂u₂³) -/
def d13_F44 (u₁ u₂ : ℝ) : ℝ :=
  iteratedDeriv 3 (fun s => deriv (fun t => F44 t s) u₁) u₂

/-- ∂⁴F44/(∂u₁² · ∂u₂²) -/
def d22_F44 (u₁ u₂ : ℝ) : ℝ :=
  iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun t => F44 t s) u₁) u₂

/-! ## A3. Integrability helpers for F44 -/

/-- The F44 integrand is integrable on restricted product measures (Fubini inner swap). -/
private lemma F44_inner_integrable (x₁ y₁ : ℝ) (a b : ℝ) :
    Integrable (Function.uncurry fun x₂ y₂ =>
      Real.exp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
        Real.sin (x₁ * y₁ + x₂ * y₂))
    ((volume : Measure ℝ).restrict (Set.Ioi a) |>.prod
     ((volume : Measure ℝ).restrict (Set.Ioi b))) := by
  apply (Integrable.mul_prod
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/2)).integrableOn
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1/2)).integrableOn).mono'
  · exact (show Continuous (Function.uncurry fun x₂ y₂ =>
        Real.exp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
          Real.sin (x₁ * y₁ + x₂ * y₂)) by fun_prop).aestronglyMeasurable
  · filter_upwards with ⟨a', b'⟩
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc Real.exp (-(x₁ ^ 2 + a' ^ 2 + y₁ ^ 2 + b' ^ 2) / 2) *
            |Real.sin (x₁ * y₁ + a' * b')|
        ≤ Real.exp (-(x₁ ^ 2 + a' ^ 2 + y₁ ^ 2 + b' ^ 2) / 2) * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = Real.exp (-(x₁ ^ 2 + a' ^ 2 + y₁ ^ 2 + b' ^ 2) / 2) := mul_one _
      _ ≤ Real.exp (-(a' ^ 2 + b' ^ 2) / 2) := by
          apply Real.exp_le_exp.mpr
          gcongr
          nlinarith [sq_nonneg x₁, sq_nonneg y₁]
      _ = Real.exp (-(1 / 2) * a' ^ 2) * Real.exp (-(1 / 2) * b' ^ 2) := by
          rw [← Real.exp_add]; ring_nf

/-! ## A3. Core identities -/

/-- `Φ(η) = F44(η,η)` — connects the 1-parameter and 2-parameter formulations.
    Proof: specialize H_eta at z=i, extract Im, decompose f_eta product into
    four quadrants via negation symmetry, each contributes ∫ G equally. -/
theorem Phi_eq_F44_diag (η : ℝ) : Phi η = 4 * F44 η η := by
  /-
  Proof outline:
    Phi η = 4π · Re(H_eta(η,I)/I)
          = 4π · (1/2) · Re(∫ f·f · cexp(KE) / (4πI))
          = (1/2) · ∫ f·f · exp(-S/4) · sin(D/2)      -- "= (1/2) · ∫ W"
          = (1/2) · 4 · F44(η,η)                        -- quadrant decomposition
          = F44(η,η)
  We prove this in two steps:
    Step A: Phi η = (1/2) * ∫ W   (complex → real reduction)
    Step B: ∫ W = 4 * F44 η η     (quadrant symmetry)
  -/
  -- Abbreviations
  set I := Complex.I with hI_def
  -- I ∈ S (needed for integrability)
  have hI_in_S : I ∈ S := by
    show |Complex.I.re| < 1; simp
  -- The "base" integrand (without sign function)
  let base : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    Real.exp (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) *
      Real.sin (p.1.1 * p.2.1 + p.1.2 * p.2.2)
  -- W = f·f·base
  let W : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    f_eta η p.1 * f_eta η p.2 * base p
  -- F44 integrand (indicator version)
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    if η * h5 p.1.1 < p.1.2 then
      if η * h5 p.2.1 < p.2.2 then base p
      else 0
    else 0
  -- ============================================================
  -- Infrastructure: σ permutation and integrability
  -- ============================================================
  -- σ : ((a,b),(c,d)) ↦ ((a,c),(b,d)) — coordinate permutation
  let σ : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).trans <|
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm.trans <|
        (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ))
          (MeasurableEquiv.refl ℝ)).trans <|
        (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)))).trans <|
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × ℝ)).symm
  have hσ : ∀ a b c d : ℝ, σ ((a, b), (c, d)) = ((a, c), (b, d)) := by
    intro a b c d
    simp [σ, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr,
          MeasurableEquiv.prodComm]
  have hσ_vol : MeasurePreserving σ volume volume := by
    change MeasurePreserving
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl ℝ).prodCongr
          (MeasurableEquiv.prodAssoc.symm.trans
            ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)).trans
              MeasurableEquiv.prodAssoc))).trans
          MeasurableEquiv.prodAssoc.symm))
      volume volume
    apply MeasurePreserving.trans volume_preserving_prodAssoc
    apply MeasurePreserving.trans _ volume_preserving_prodAssoc.symm
    exact (MeasurePreserving.id volume).prod
      (MeasurePreserving.trans volume_preserving_prodAssoc.symm
        (MeasurePreserving.trans
          ((Measure.measurePreserving_swap (α := ℝ) (β := ℝ)).prod
            (MeasurePreserving.id volume))
          volume_preserving_prodAssoc))
  -- Gqr: G in query coordinates ((x₁,y₁),(x₂,y₂)), matching F44's iteration order
  let Gqr : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p =>
    if η * h5 p.1.1 < p.2.1 then
      if η * h5 p.1.2 < p.2.2 then base (σ p)
      else 0
    else 0
  -- 4D Gaussian is integrable (dominates all our integrands)
  have h_gauss4 :
      Integrable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          rexp (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2))
        ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    have h1 := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by positivity)
    have h2 : Integrable (fun q : ℝ × ℝ => rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2))
        ((volume : Measure ℝ).prod volume) := by
      have : ∀ q : ℝ × ℝ, rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2) =
          rexp (-(1/2 : ℝ) * q.1 ^ 2) * rexp (-(1/2 : ℝ) * q.2 ^ 2) := by
        intro q; rw [← Real.exp_add]; congr 1; ring
      simp_rw [this]; exact h1.mul_prod h1
    have : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
        rexp (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) =
          rexp (-(p.1.1 ^ 2 + p.1.2 ^ 2) / 2) *
            rexp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 2) := by
      intro p; rw [← Real.exp_add]; congr 1; ring
    simp_rw [this]; exact h2.mul_prod h2
  have hbase_abs_le_gauss :
      ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
        |base p| ≤ rexp (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) := by
    intro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    simp only [base, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    nlinarith [abs_sin_le_one (x₁ * y₁ + x₂ * y₂),
      Real.exp_nonneg (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2)]
  -- G is integrable on (ℝ²)×(ℝ²)
  have hG_int :
      Integrable G ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    apply h_gauss4.mono'
    · apply Measurable.aestronglyMeasurable
      have hc1 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => η * h5 x.1.1) :=
        continuous_const.mul (h5_continuous.comp (continuous_fst.comp continuous_fst))
      have hc2 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.1.2) :=
        continuous_snd.comp continuous_fst
      have hc3 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => η * h5 x.2.1) :=
        continuous_const.mul (h5_continuous.comp (continuous_fst.comp continuous_snd))
      have hc4 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.2) :=
        continuous_snd.comp continuous_snd
      have hcbody : Continuous (fun p : (ℝ × ℝ) × ℝ × ℝ =>
          rexp (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) *
            Real.sin (p.1.1 * p.2.1 + p.1.2 * p.2.2)) :=
        (Real.continuous_exp.comp (by fun_prop)).mul
          (Real.continuous_sin.comp (by fun_prop))
      exact Measurable.ite (measurableSet_lt hc1.measurable hc2.measurable)
        (Measurable.ite (measurableSet_lt hc3.measurable hc4.measurable)
          hcbody.measurable measurable_const)
        measurable_const
    · filter_upwards with p
      by_cases hxp : η * h5 p.1.1 < p.1.2 <;> by_cases hyp : η * h5 p.2.1 < p.2.2
      · simp only [G, if_pos hxp, if_pos hyp]
        rw [Real.norm_eq_abs]; exact hbase_abs_le_gauss p
      · simp only [G, if_pos hxp, if_neg hyp, norm_zero]; positivity
      · simp only [G, if_neg hxp, norm_zero]; positivity
      · simp only [G, if_neg hxp, norm_zero]; positivity
  -- Gqr is integrable (σ permutes coordinates but preserves sum of squares)
  have hGqr_int :
      Integrable Gqr ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    apply h_gauss4.mono'
    · apply Measurable.aestronglyMeasurable
      have hc1 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => η * h5 x.1.1) :=
        continuous_const.mul (h5_continuous.comp (continuous_fst.comp continuous_fst))
      have hc2 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.1) :=
        continuous_fst.comp continuous_snd
      have hc3 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => η * h5 x.1.2) :=
        continuous_const.mul (h5_continuous.comp (continuous_snd.comp continuous_fst))
      have hc4 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.2) :=
        continuous_snd.comp continuous_snd
      have hcbody : Continuous (fun p : (ℝ × ℝ) × ℝ × ℝ =>
          rexp (-(p.1.1 ^ 2 + p.2.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) / 2) *
            Real.sin (p.1.1 * p.1.2 + p.2.1 * p.2.2)) :=
        (Real.continuous_exp.comp (by fun_prop)).mul
          (Real.continuous_sin.comp (by fun_prop))
      exact Measurable.ite (measurableSet_lt hc1.measurable hc2.measurable)
        (Measurable.ite (measurableSet_lt hc3.measurable hc4.measurable)
          hcbody.measurable measurable_const)
        measurable_const
    · filter_upwards with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      by_cases hx : η * h5 a < c <;> by_cases hy : η * h5 b < d
      · simp only [Gqr, if_pos hx, if_pos hy]
        rw [Real.norm_eq_abs]
        have := hbase_abs_le_gauss (σ ((a, b), (c, d)))
        simp only [hσ] at this
        convert this using 2
        ring
      · simp only [Gqr, if_pos hx, if_neg hy, norm_zero]; positivity
      · simp only [Gqr, if_neg hx, norm_zero]; positivity
      · simp only [Gqr, if_neg hx, norm_zero]; positivity
  -- ============================================================
  -- Step A: Phi η = (1/2) * ∫ W
  -- ============================================================
  have step_A : Phi η = ∫ p, W p := by
    have hI2 : I ^ 2 = -1 := by rw [hI_def]; exact Complex.I_sq
    have hden : (2 * ↑Real.pi * (1 - I ^ 2) : ℂ) = (4 * ↑Real.pi : ℂ) := by
      rw [hI2]; push_cast; ring
    have h4piC_ne : (4 * ↑Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (show (4 * Real.pi : ℝ) ≠ 0 from by positivity)
    have hker : ∀ x₁ x₂ y₁ y₂ : ℝ,
        kernel_exponent x₁ x₂ y₁ y₂ I =
          (↑(-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2 : ℝ) : ℂ) +
            ↑((x₁ * y₁ + x₂ * y₂) : ℝ) * I := by
      intro x₁ x₂ y₁ y₂; unfold kernel_exponent; rw [hI2]; push_cast; ring
    -- Im of the complex integrand = W (pointwise)
    have h_im : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
        (↑(f_eta η p.1 * f_eta η p.2) *
          cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 I)).im = W p := by
      intro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
      simp only [hker]
      rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [W, base, Complex.mul_im, Complex.mul_re,
        Complex.add_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero, mul_one]
      ring
    -- The complex integrand (without denominator) is integrable
    have hJ_int : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ↑(f_eta η p.1 * f_eta η p.2) *
          cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 I)) volume := by
      have h := H_eta_integrand_integrable η I hI_in_S
      rw [hden] at h
      exact (h.mul_const (4 * ↑Real.pi : ℂ)).congr
        (ae_of_all _ fun p => div_mul_cancel₀ _ h4piC_ne)
    -- Pull Im through the integral: (∫ J).im = ∫ W
    set J := fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ↑(f_eta η p.1 * f_eta η p.2) *
        cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 I) with hJ_def
    have hIm_int : (∫ p, J p).im = ∫ p, W p := by
      -- Use: z.im = Re(-I*z), then pull Re through via integral_re
      have h_neg_I_re : ∀ z : ℂ, z.im = (-I * z).re := by
        intro z; simp [Complex.mul_re, Complex.I_re, Complex.I_im, hI_def]
      rw [h_neg_I_re, ← integral_const_mul]
      change RCLike.re (∫ a, -I * J a) = ∫ p, W p
      rw [(integral_re (hJ_int.const_mul (-I))).symm]
      congr 1; ext p
      show RCLike.re (-I * J p) = W p
      rw [show (RCLike.re (-I * J p) : ℝ) = (-I * J p).re from rfl, ← h_neg_I_re]
      exact h_im p
    -- Re(z/I) = Im(z) for any z : ℂ
    have h_div_I_re : ∀ z : ℂ, (z / I).re = z.im := by
      intro z
      rw [div_eq_mul_inv, show I⁻¹ = -I from by rw [hI_def]; exact Complex.inv_I]
      simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im, hI_def]
    -- Algebraic reduction
    unfold Phi varphi H_eta
    simp only [← hI_def]
    rw [hden, h_div_I_re]
    -- Goal: 4π * (1/2 * (∫ f*f*cexp(KE)/(4↑π)).im) = 1/2 * ∫ W
    rw [← hIm_int]
    rw [integral_div]
    -- Goal: 4π * (1/2 * ((∫ ↑(f*f)*cexp(KE)) / (4↑π))).im = 1/2 * (∫ J).im
    -- Identify ∫ with J
    have hJ_eq : (∫ a : (ℝ × ℝ) × (ℝ × ℝ),
        ↑(f_eta η a.1 * f_eta η a.2) *
          cexp (kernel_exponent a.1.1 a.1.2 a.2.1 a.2.2 I)) = ∫ p, J p := rfl
    rw [hJ_eq]
    -- Expand .im through multiplication and division
    rw [show (4 * ↑Real.pi : ℂ) = ↑(4 * Real.pi : ℝ) from by push_cast; ring]
    simp only [Complex.mul_im, Complex.div_ofReal_im, Complex.div_ofReal_re]
    field_simp [Real.pi_ne_zero]
  -- ============================================================
  -- hF44_eq_G: F44 η η = ∫ G (via Gqr collapse + σ permutation)
  -- ============================================================
  have hF44_eq_G : F44 η η = ∫ p, G p := by
    unfold F44
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    simp only [Set.indicator, Set.mem_Ioi]
    simp_rw [show ∀ (P : Prop) [Decidable P] (f : ℝ → ℝ),
        (if P then ∫ y : ℝ, f y else (0 : ℝ)) = ∫ y : ℝ, if P then f y else 0 from by
      intro P _ f; split_ifs <;> simp [MeasureTheory.integral_zero]]
    -- Identify integrand with Gqr
    have h_id : ∀ x₁ y₁ x₂ y₂ : ℝ,
        (if η * h5 x₁ < x₂ then
          if η * h5 y₁ < y₂ then
            rexp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
              Real.sin (x₁ * y₁ + x₂ * y₂)
          else 0
        else 0) = Gqr ((x₁, y₁), (x₂, y₂)) := by
      intro x₁ y₁ x₂ y₂; simp [Gqr, base, hσ]
    simp_rw [h_id]
    -- Inner slice integrability (2D Gaussian dominates Gqr slices)
    have h1 := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/2 by positivity)
    have h2 : Integrable (fun q : ℝ × ℝ => rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2))
        ((volume : Measure ℝ).prod volume) := by
      have : ∀ q : ℝ × ℝ, rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2) =
          rexp (-(1/2 : ℝ) * q.1 ^ 2) * rexp (-(1/2 : ℝ) * q.2 ^ 2) := by
        intro q; rw [← Real.exp_add]; congr 1; ring
      simp_rw [this]; exact h1.mul_prod h1
    have h_slice : ∀ x₁ y₁ : ℝ,
        Integrable (fun r : ℝ × ℝ => Gqr ((x₁, y₁), r))
          ((volume : Measure ℝ).prod volume) := by
      intro x₁ y₁
      -- Rewrite Gqr to explicit form for measurability
      have hbody_eq : (fun r : ℝ × ℝ => Gqr ((x₁, y₁), r)) =
          (fun r : ℝ × ℝ => if η * h5 x₁ < r.1 then
            if η * h5 y₁ < r.2 then
              rexp (-(x₁ ^ 2 + r.1 ^ 2 + y₁ ^ 2 + r.2 ^ 2) / 2) *
                Real.sin (x₁ * y₁ + r.1 * r.2)
            else 0 else 0) := by
        ext ⟨x₂, y₂⟩; simp [Gqr, base, hσ]
      rw [hbody_eq]
      apply h2.mono'
      · exact (Measurable.ite (measurableSet_lt continuous_const.measurable
            continuous_fst.measurable)
          (Measurable.ite (measurableSet_lt continuous_const.measurable
              continuous_snd.measurable)
            ((Real.continuous_exp.comp (by fun_prop)).mul
              (Real.continuous_sin.comp (by fun_prop))).measurable
            measurable_const)
          measurable_const).aestronglyMeasurable
      · filter_upwards with ⟨x₂, y₂⟩
        by_cases hx : η * h5 x₁ < x₂ <;> by_cases hy : η * h5 y₁ < y₂
        · simp only [if_pos hx, if_pos hy]
          rw [Real.norm_eq_abs]
          simp only [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
          calc rexp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
                  |Real.sin (x₁ * y₁ + x₂ * y₂)|
              ≤ rexp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) * 1 := by
                gcongr; exact abs_sin_le_one _
            _ ≤ rexp (-(x₂ ^ 2 + y₂ ^ 2) / 2) := by
                rw [mul_one]; apply Real.exp_le_exp.mpr
                nlinarith [sq_nonneg x₁, sq_nonneg y₁]
        · simp only [if_pos hx, if_neg hy, norm_zero]; positivity
        · simp only [if_neg hx, norm_zero]; positivity
        · simp only [if_neg hx, norm_zero]; positivity
    -- Inner collapse: ∫ x₂ ∫ y₂, Gqr(q,(x₂,y₂)) = ∫ r, Gqr(q,r)
    have h_inner_eq : ∀ q : ℝ × ℝ,
        (∫ r : ℝ × ℝ, Gqr (q, r)) =
        ∫ x₂ : ℝ, ∫ y₂ : ℝ, Gqr (q, (x₂, y₂)) := by
      intro q
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _]
      exact integral_prod _ (h_slice q.1 q.2)
    -- Outer integrability
    have h_outer_int : Integrable
        (fun q : ℝ × ℝ => ∫ x₂ : ℝ, ∫ y₂ : ℝ, Gqr (q, (x₂, y₂)))
        ((volume : Measure ℝ).prod volume) := by
      have : (fun q : ℝ × ℝ => ∫ x₂ : ℝ, ∫ y₂ : ℝ, Gqr (q, (x₂, y₂))) =
          (fun q : ℝ × ℝ => ∫ r : ℝ × ℝ, Gqr (q, r)) := by
        ext q; exact (h_inner_eq q).symm
      rw [this]; exact hGqr_int.integral_prod_left
    -- Collapse iterated integrals → product integral, then apply σ
    trans (∫ p : (ℝ × ℝ) × (ℝ × ℝ), Gqr p)
    · -- Collapse: ∫ x₁ ∫ y₁ ∫ x₂ ∫ y₂, Gqr(...) = ∫ p, Gqr p
      symm
      rw [show (volume : Measure ((ℝ × ℝ) × ℝ × ℝ)) =
        (volume : Measure (ℝ × ℝ)).prod volume from Measure.volume_eq_prod _ _]
      rw [integral_prod _ hGqr_int]
      simp_rw [h_inner_eq]
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _]
      exact integral_prod _ h_outer_int
    · -- Change of variables: ∫ Gqr = ∫ G via σ
      have hGqr_eq_Gσ : ∀ p, Gqr p = G (σ p) := by
        intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp [Gqr, G, hσ]
      simp_rw [hGqr_eq_Gσ]
      exact hσ_vol.integral_comp' G
  -- ============================================================
  -- Step B: ∫ W = 4 * ∫ G (quadrant decomposition)
  -- ============================================================
  have step_B : ∫ p, W p = 4 * ∫ p, G p := by
    -- Negation maps on (ℝ²)×(ℝ²)
    let Tx : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
      (MeasurableEquiv.neg (ℝ × ℝ)).prodCongr (MeasurableEquiv.refl (ℝ × ℝ))
    let Ty : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
      (MeasurableEquiv.refl (ℝ × ℝ)).prodCongr (MeasurableEquiv.neg (ℝ × ℝ))
    let Txy : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
      (MeasurableEquiv.neg (ℝ × ℝ)).prodCongr (MeasurableEquiv.neg (ℝ × ℝ))
    -- Measure preservation
    have hneg_mp := Measure.measurePreserving_neg (volume : Measure (ℝ × ℝ))
    have hid_mp := MeasurePreserving.id (μ := (volume : Measure (ℝ × ℝ)))
    have hTx_mp : MeasurePreserving Tx volume volume := hneg_mp.prod hid_mp
    have hTy_mp : MeasurePreserving Ty volume volume := hid_mp.prod hneg_mp
    have hTxy_mp : MeasurePreserving Txy volume volume := hneg_mp.prod hneg_mp
    -- G∘T integrability (G integrable + T measure-preserving ⇒ G∘T integrable)
    have hGT_int : ∀ (T : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ)),
        MeasurePreserving T volume volume → Integrable (G ∘ T) volume := by
      intro T hT
      have : Integrable G (Measure.map T volume) := by rw [hT.map_eq]; exact hG_int
      exact T.measurableEmbedding.integrable_map_iff.mp this
    have hGTx_int := hGT_int Tx hTx_mp
    have hGTy_int := hGT_int Ty hTy_mp
    have hGTxy_int := hGT_int Txy hTxy_mp
    -- W is integrable (bounded by Gaussian)
    have hW_int : Integrable W (volume.prod volume) := by
      apply h_gauss4.mono'
      · exact ((f_eta_measurable η).comp measurable_fst |>.mul
          ((f_eta_measurable η).comp measurable_snd) |>.mul
          ((Real.continuous_exp.comp (by fun_prop)).mul
            (Real.continuous_sin.comp (by fun_prop))).measurable).aestronglyMeasurable
      · filter_upwards with p
        rw [Real.norm_eq_abs]
        simp only [W, abs_mul]
        rw [f_eta_bounded, f_eta_bounded, one_mul, one_mul]
        exact hbase_abs_le_gauss p
    -- Negation flips the h5 condition (h5 is odd)
    have hx_neg : ∀ x₁ x₂ : ℝ, η * h5 (-x₁) < -x₂ ↔ x₂ < η * h5 x₁ := by
      intro x₁ x₂; rw [h5_odd, mul_neg]; constructor <;> intro h <;> linarith
    -- Evaluation lemmas for Tx, Ty, Txy
    have hTx_eval : ∀ a b : ℝ × ℝ, Tx (a, b) = (-a, b) := fun _ _ => rfl
    have hTy_eval : ∀ a b : ℝ × ℝ, Ty (a, b) = (a, -b) := fun _ _ => rfl
    have hTxy_eval : ∀ a b : ℝ × ℝ, Txy (a, b) = (-a, -b) := fun _ _ => rfl
    -- base symmetries under negation (sin is odd in its argument)
    have hbaseTx : ∀ x₁ x₂ y₁ y₂ : ℝ,
        base ((-x₁, -x₂), (y₁, y₂)) = -base ((x₁, x₂), (y₁, y₂)) := by
      intro x₁ x₂ y₁ y₂; simp only [base, neg_sq]
      rw [show (-x₁) * y₁ + (-x₂) * y₂ = -(x₁ * y₁ + x₂ * y₂) from by ring,
          Real.sin_neg]; ring
    have hbaseTy : ∀ x₁ x₂ y₁ y₂ : ℝ,
        base ((x₁, x₂), (-y₁, -y₂)) = -base ((x₁, x₂), (y₁, y₂)) := by
      intro x₁ x₂ y₁ y₂; simp only [base, neg_sq]
      rw [show x₁ * (-y₁) + x₂ * (-y₂) = -(x₁ * y₁ + x₂ * y₂) from by ring,
          Real.sin_neg]; ring
    have hbaseTxy : ∀ x₁ x₂ y₁ y₂ : ℝ,
        base ((-x₁, -x₂), (-y₁, -y₂)) = base ((x₁, x₂), (y₁, y₂)) := by
      intro x₁ x₂ y₁ y₂; simp only [base, neg_sq]
      rw [show (-x₁) * (-y₁) + (-x₂) * (-y₂) = x₁ * y₁ + x₂ * y₂ from by ring]
    -- ae decomposition: W = G + G∘Tx + G∘Ty + G∘Txy
    have hsplit_ae :
        ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂volume,
          W p = G p + (G ∘ Tx) p + (G ∘ Ty) p + (G ∘ Txy) p := by
      -- Exceptional set: graph of h5 (measure zero) in each component
      have hx_graph : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ)))
          ({x : ℝ × ℝ | x.2 = η * h5 x.1} ×ˢ Set.univ) = 0 := by
        change ((volume : Measure (ℝ × ℝ)).prod volume)
          ({x : ℝ × ℝ | x.2 = η * h5 x.1} ×ˢ Set.univ) = 0
        rw [Measure.prod_prod]; simp [graph_h5_null η]
      have hy_graph : (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ)))
          (Set.univ ×ˢ {y : ℝ × ℝ | y.2 = η * h5 y.1}) = 0 := by
        change ((volume : Measure (ℝ × ℝ)).prod volume)
          (Set.univ ×ˢ {y : ℝ × ℝ | y.2 = η * h5 y.1}) = 0
        rw [Measure.prod_prod]; simp [graph_h5_null η]
      have hae_x : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂volume, p.1.2 ≠ η * h5 p.1.1 :=
        measure_mono_null (fun ⟨x, _⟩ (hp : ¬_) => by
          simp only [Set.mem_setOf_eq, not_not] at hp
          exact ⟨hp, Set.mem_univ _⟩) hx_graph
      have hae_y : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂volume, p.2.2 ≠ η * h5 p.2.1 :=
        measure_mono_null (fun ⟨_, y⟩ (hp : ¬_) => by
          simp only [Set.mem_setOf_eq, not_not] at hp
          exact ⟨Set.mem_univ _, hp⟩) hy_graph
      filter_upwards [hae_x, hae_y] with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ hxne hyne
      simp only [Prod.fst, Prod.snd] at hxne hyne
      -- hxne : x₂ ≠ η * h5 x₁, hyne : y₂ ≠ η * h5 y₁
      simp only [W, G, Function.comp, hTx_eval, hTy_eval, hTxy_eval,
        Prod.neg_mk, Prod.fst, Prod.snd, f_eta]
      by_cases hx : η * h5 x₁ < x₂ <;> by_cases hy : η * h5 y₁ < y₂
      · -- Q1: both above threshold
        have hx' : ¬ (η * h5 (-x₁) < -x₂) := by rw [hx_neg]; linarith
        have hy' : ¬ (η * h5 (-y₁) < -y₂) := by rw [hx_neg]; linarith
        simp only [hx, hy, hx', hy', ite_true, ite_false, not_true, not_false_eq_true]; ring
      · -- Q2: x above, y below
        have hx' : ¬ (η * h5 (-x₁) < -x₂) := by rw [hx_neg]; linarith
        have hy' : η * h5 (-y₁) < -y₂ := by
          rw [hx_neg]; exact lt_of_le_of_ne (not_lt.mp hy) hyne
        simp only [hx, hy, hx', hy', ite_true, ite_false, not_true, not_false_eq_true]
        rw [hbaseTy]; ring
      · -- Q3: x below, y above
        have hx' : η * h5 (-x₁) < -x₂ := by
          rw [hx_neg]; exact lt_of_le_of_ne (not_lt.mp hx) hxne
        have hy' : ¬ (η * h5 (-y₁) < -y₂) := by rw [hx_neg]; linarith
        simp only [hx, hy, hx', hy', ite_true, ite_false, not_true, not_false_eq_true]
        rw [hbaseTx]; ring
      · -- Q4: both below threshold
        have hx' : η * h5 (-x₁) < -x₂ := by
          rw [hx_neg]; exact lt_of_le_of_ne (not_lt.mp hx) hxne
        have hy' : η * h5 (-y₁) < -y₂ := by
          rw [hx_neg]; exact lt_of_le_of_ne (not_lt.mp hy) hyne
        simp only [hx, hy, hx', hy', ite_true, ite_false, not_true, not_false_eq_true]
        rw [hbaseTxy]; ring
    -- Integrate: ∫ W = 4 ∫ G
    -- First split the sum integral, then each G∘T integral = ∫ G
    have hTx_eq : ∫ p, (G ∘ ↑Tx) p = ∫ p, G p := hTx_mp.integral_comp' G
    have hTy_eq : ∫ p, (G ∘ ↑Ty) p = ∫ p, G p := hTy_mp.integral_comp' G
    have hTxy_eq : ∫ p, (G ∘ ↑Txy) p = ∫ p, G p := hTxy_mp.integral_comp' G
    calc ∫ p, W p
        = ∫ p, (G p + (G ∘ ↑Tx) p + (G ∘ ↑Ty) p + (G ∘ ↑Txy) p) :=
          integral_congr_ae hsplit_ae
      _ = 4 * ∫ p, G p := by
          simp_rw [show ∀ p, (G ∘ ↑Tx) p = G (Tx p) from fun _ => rfl,
                   show ∀ p, (G ∘ ↑Ty) p = G (Ty p) from fun _ => rfl,
                   show ∀ p, (G ∘ ↑Txy) p = G (Txy p) from fun _ => rfl]
          have hG' : Integrable G volume := hG_int
          have hGTx' : Integrable (fun p => G (Tx p)) volume := hGTx_int
          have hGTy' : Integrable (fun p => G (Ty p)) volume := hGTy_int
          have hGTxy' : Integrable (fun p => G (Txy p)) volume := hGTxy_int
          have h1 : ∫ p, G p + G (Tx p) + (G (Ty p) + G (Txy p)) =
              (∫ p, G p + G (Tx p)) + ∫ p, G (Ty p) + G (Txy p) :=
            integral_add (hG'.add hGTx') (hGTy'.add hGTxy')
          have h2 : ∫ p, G p + G (Tx p) = (∫ p, G p) + ∫ p, G (Tx p) :=
            integral_add hG' hGTx'
          have h3 : ∫ p, G (Ty p) + G (Txy p) = (∫ p, G (Ty p)) + ∫ p, G (Txy p) :=
            integral_add hGTy' hGTxy'
          have hTx' : ∫ p, G (Tx p) = ∫ p, G p := hTx_eq
          have hTy' : ∫ p, G (Ty p) = ∫ p, G p := hTy_eq
          have hTxy' : ∫ p, G (Txy p) = ∫ p, G p := hTxy_eq
          rw [show (fun p => G p + G (Tx p) + G (Ty p) + G (Txy p)) =
            (fun p => G p + G (Tx p) + (G (Ty p) + G (Txy p))) from by ext; ring,
            h1, h2, h3, hTx', hTy', hTxy']; ring
  -- ============================================================
  -- Combine
  -- ============================================================
  rw [step_A, step_B, hF44_eq_G]

/-- `F44` is symmetric: swapping (x₁,x₂) ↔ (y₁,y₂) and using sin(a+b) = sin(b+a).
    Proof strategy: rewrite F44 as a single integral over (ℝ×ℝ)×(ℝ×ℝ) using indicators
    (avoiding parameter-dependent integration domains), then apply a coordinate swap
    that preserves the product Lebesgue measure. -/
theorem F44_swap (u₁ u₂ : ℝ) : F44 u₁ u₂ = F44 u₂ u₁ := by
  -- G a b: the integrand with indicator-style conditions (no restricted measures)
  let G : ℝ → ℝ → (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun a b p =>
    if a * h5 p.1.1 < p.2.1 then
      if b * h5 p.1.2 < p.2.2 then
        Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) / 2) *
          Real.sin (p.1.1 * p.1.2 + p.2.1 * p.2.2)
      else 0
    else 0
  -- 4D Gaussian dominates |G|
  have h_gauss4 :
      Integrable
        (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) / 2))
        ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    have h1 := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by positivity)
    have h2 : Integrable (fun q : ℝ × ℝ => Real.exp (-(q.1 ^ 2 + q.2 ^ 2) / 2))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      have : ∀ q : ℝ × ℝ, Real.exp (-(q.1 ^ 2 + q.2 ^ 2) / 2) =
          Real.exp (-(1 / 2 : ℝ) * q.1 ^ 2) * Real.exp (-(1 / 2 : ℝ) * q.2 ^ 2) := by
        intro q; rw [← Real.exp_add]; congr 1; ring
      simp_rw [this]; exact h1.mul_prod h1
    have : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
        Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) / 2) =
          Real.exp (-(p.1.1 ^ 2 + p.1.2 ^ 2) / 2) *
            Real.exp (-(p.2.1 ^ 2 + p.2.2 ^ 2) / 2) := by
      intro p; rw [← Real.exp_add]; congr 1; ring
    simp_rw [this]; exact h2.mul_prod h2
  -- G is integrable on the 4D product (dominated by the Gaussian)
  have hG_int :
      ∀ a b : ℝ,
        Integrable (G a b)
          ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    intro a b
    apply h_gauss4.mono'
    · -- AEStronglyMeasurable: G is measurable (if-then-else of measurable functions)
      apply Measurable.aestronglyMeasurable
      have hc1 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => a * h5 x.1.1) :=
        continuous_const.mul (h5_continuous.comp (continuous_fst.comp continuous_fst))
      have hc2 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.1) :=
        continuous_fst.comp continuous_snd
      have hc3 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => b * h5 x.1.2) :=
        continuous_const.mul (h5_continuous.comp (continuous_snd.comp continuous_fst))
      have hc4 : Continuous (fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.2) :=
        continuous_snd.comp continuous_snd
      have hcbody : Continuous (fun p : (ℝ × ℝ) × ℝ × ℝ =>
          rexp (-(p.1.1 ^ 2 + p.2.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) / 2) *
            Real.sin (p.1.1 * p.1.2 + p.2.1 * p.2.2)) :=
        (Real.continuous_exp.comp (by fun_prop)).mul
          (Real.continuous_sin.comp (by fun_prop))
      exact Measurable.ite (measurableSet_lt hc1.measurable hc2.measurable)
        (Measurable.ite (measurableSet_lt hc3.measurable hc4.measurable)
          hcbody.measurable measurable_const)
        measurable_const
    · filter_upwards with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
      simp only [G]
      by_cases hx : a * h5 x₁ < x₂ <;> by_cases hy : b * h5 y₁ < y₂
      · simp only [if_pos hx, if_pos hy]
        rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        nlinarith [Real.abs_sin_le_one (x₁ * y₁ + x₂ * y₂),
          Real.exp_nonneg (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2)]
      · simp only [if_pos hx, if_neg hy, norm_zero]; positivity
      · simp only [if_neg hx, norm_zero]; positivity
      · simp only [if_neg hx, norm_zero]; positivity
  -- F44 a b = ∫ G a b (convert iterated restricted integrals to product integral)
  have hF44_eq :
      ∀ a b : ℝ,
        F44 a b = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), G a b p := by
    intro a b
    unfold F44
    -- Convert restricted integrals to indicators
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    simp only [Set.indicator, Set.mem_Ioi]
    -- Pull if-conditions inside integrals
    -- Key: if P then ∫ y, f y else 0 = ∫ y, if P then f y else 0 (when P indep. of y)
    simp_rw [show ∀ (P : Prop) [Decidable P] (f : ℝ → ℝ),
        (if P then ∫ y : ℝ, f y else (0 : ℝ)) = ∫ y : ℝ, if P then f y else 0 from by
      intro P _ f; split_ifs <;> simp [MeasureTheory.integral_zero]]
    -- Now goal is: ∫ x₁ ∫ y₁ ∫ x₂ ∫ y₂, G((x₁,y₁),(x₂,y₂)) = ∫ p, G p
    -- Collapse iterated integrals into product integral via integral_prod
    -- Inner slice integrability: G is dominated by 2D Gaussian on each slice
    have h1 := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/2 by positivity)
    have h2 : Integrable (fun q : ℝ × ℝ => rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2))
        ((volume : Measure ℝ).prod volume) := by
      have : ∀ q : ℝ × ℝ, rexp (-(q.1 ^ 2 + q.2 ^ 2) / 2) =
          rexp (-(1/2 : ℝ) * q.1 ^ 2) * rexp (-(1/2 : ℝ) * q.2 ^ 2) := by
        intro q; rw [← Real.exp_add]; congr 1; ring
      simp_rw [this]; exact h1.mul_prod h1
    have h_slice : ∀ x₁ y₁ : ℝ,
        Integrable (fun r : ℝ × ℝ => G a b ((x₁, y₁), r))
          ((volume : Measure ℝ).prod volume) := by
      intro x₁ y₁
      apply h2.mono'
      · have hc1 : Continuous (fun x : ℝ × ℝ => a * h5 x₁) := continuous_const
        have hc3 : Continuous (fun x : ℝ × ℝ => b * h5 y₁) := continuous_const
        exact (Measurable.ite (measurableSet_lt hc1.measurable continuous_fst.measurable)
          (Measurable.ite (measurableSet_lt hc3.measurable continuous_snd.measurable)
            ((Real.continuous_exp.comp (by fun_prop)).mul
              (Real.continuous_sin.comp (by fun_prop))).measurable
            measurable_const)
          measurable_const).aestronglyMeasurable
      · filter_upwards with ⟨x₂, y₂⟩
        simp only [G]
        by_cases hx : a * h5 x₁ < x₂ <;> by_cases hy : b * h5 y₁ < y₂
        · simp only [if_pos hx, if_pos hy]
          rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
          have : rexp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) ≤
              rexp (-(x₂ ^ 2 + y₂ ^ 2) / 2) := by
            apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg x₁, sq_nonneg y₁]
          nlinarith [Real.abs_sin_le_one (x₁ * y₁ + x₂ * y₂),
            Real.exp_nonneg (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2)]
        · simp only [if_pos hx, if_neg hy, norm_zero]; positivity
        · simp only [if_neg hx, norm_zero]; positivity
        · simp only [if_neg hx, norm_zero]; positivity
    -- Collapse inner pair: ∫ x₂ ∫ y₂, G((x₁,y₁),(x₂,y₂)) = ∫ r, G((x₁,y₁), r)
    have h_inner_eq : ∀ q : ℝ × ℝ,
        (∫ r : ℝ × ℝ, G a b (q, r)) =
        ∫ x₂ : ℝ, ∫ y₂ : ℝ, G a b (q, (x₂, y₂)) := by
      intro q
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
        Measure.volume_eq_prod _ _]
      exact integral_prod _ (h_slice q.1 q.2)
    symm
    rw [show (volume : Measure ((ℝ × ℝ) × ℝ × ℝ)) =
      (volume : Measure (ℝ × ℝ)).prod volume from Measure.volume_eq_prod _ _]
    rw [integral_prod _ (hG_int a b)]
    simp_rw [h_inner_eq]
    -- Collapse outer pair: ∫ q, f(q) ∂volume = ∫ x₁ ∫ y₁, f(x₁,y₁)
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _]
    have h_outer_int : Integrable
        (fun q : ℝ × ℝ => ∫ x₂ : ℝ, ∫ y₂ : ℝ, G a b (q, (x₂, y₂)))
        ((volume : Measure ℝ).prod volume) := by
      have : (fun q : ℝ × ℝ => ∫ x₂ : ℝ, ∫ y₂ : ℝ, G a b (q, (x₂, y₂))) =
          (fun q : ℝ × ℝ => ∫ r : ℝ × ℝ, G a b (q, r)) := by
        ext q; exact (h_inner_eq q).symm
      rw [this]; exact (hG_int a b).integral_prod_left
    exact integral_prod _ h_outer_int
  -- Symmetry: G u₁ u₂ ((x₁,y₁),(x₂,y₂)) = G u₂ u₁ ((y₁,x₁),(y₂,x₂))
  have hG_symm : ∀ x₁ y₁ x₂ y₂ : ℝ,
      G u₁ u₂ ((x₁, y₁), (x₂, y₂)) = G u₂ u₁ ((y₁, x₁), (y₂, x₂)) := by
    intro x₁ y₁ x₂ y₂
    simp only [G]
    by_cases hx : u₁ * h5 x₁ < x₂ <;> by_cases hy : u₂ * h5 y₁ < y₂
    · simp only [if_pos hx, if_pos hy]
      congr 1 <;> (congr 1; ring)
    · simp only [if_pos hx, if_neg hy]
    · simp only [if_neg hx, if_pos hy]
    · simp only [if_neg hx, if_neg hy]
  -- Change of variable: ∫ G u₁ u₂ = ∫ G u₂ u₁ (via coordinate swap + measure preservation)
  have hG_eq : (∫ p : (ℝ × ℝ) × (ℝ × ℝ), G u₁ u₂ p) = ∫ p, G u₂ u₁ p := by
    -- Expand to iterated integrals via integral_prod
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ)]
    rw [integral_prod _ (hG_int u₁ u₂), integral_prod _ (hG_int u₂ u₁)]
    -- Apply pointwise symmetry: G u₁ u₂ (q,r) = G u₂ u₁ (q.swap, r.swap)
    simp_rw [show ∀ (q r : ℝ × ℝ), G u₁ u₂ (q, r) =
        G u₂ u₁ (q.swap, r.swap) from fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => hG_symm x₁ y₁ x₂ y₂]
    -- Use measurePreserving_swap to swap variables
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
      Measure.measurePreserving_swap
    -- Inner swap: ∫ r, f(r.swap) = ∫ r, f(r) for each fixed q
    have h_inner_swap : ∀ q : ℝ × ℝ,
        (∫ r : ℝ × ℝ, G u₂ u₁ (q.swap, r.swap)) =
        (∫ r : ℝ × ℝ, G u₂ u₁ (q.swap, r)) := fun q => by
      have h := hswap.integral_comp
        (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).measurableEmbedding
        (fun r : ℝ × ℝ => G u₂ u₁ (q.swap, r))
      rwa [← Measure.volume_eq_prod ℝ ℝ] at h
    simp_rw [h_inner_swap]
    -- Outer swap: ∫ q, f(q.swap) = ∫ q, f(q)
    have h := hswap.integral_comp
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).measurableEmbedding
      (fun q : ℝ × ℝ => ∫ r : ℝ × ℝ, G u₂ u₁ (q, r))
    rwa [← Measure.volume_eq_prod ℝ ℝ] at h
  calc F44 u₁ u₂ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), G u₁ u₂ p := hF44_eq u₁ u₂
    _ = ∫ p, G u₂ u₁ p := hG_eq
    _ = F44 u₂ u₁ := (hF44_eq u₂ u₁).symm

/-! ## A4. Evenness -/

/-- `Φ` is even: `Φ(-η) = Φ(η)`. Follows from oddness of h₅ and
    the change of variables x₂ ↦ -x₂, y₂ ↦ -y₂. -/
-- Helper: f_eta (-η) (-x₁, x₂) = f_eta η (x₁, x₂) using h5 oddness
private theorem f_eta_neg_eta (η : ℝ) (x₁ x₂ : ℝ) :
    f_eta (-η) (-x₁, x₂) = f_eta η (x₁, x₂) := by
  simp [f_eta, h5_odd, neg_mul, neg_neg]

-- Helper: kernel_exponent is invariant under (x₁,y₁) → (-x₁,-y₁)
private theorem kernel_exponent_neg_fst (x₁ x₂ y₁ y₂ : ℝ) (z : ℂ) :
    kernel_exponent (-x₁) x₂ (-y₁) y₂ z = kernel_exponent x₁ x₂ y₁ y₂ z := by
  simp [kernel_exponent, neg_sq, neg_mul_neg]

-- Helper: H_eta is even in η
theorem H_eta_even (η : ℝ) (z : ℂ) : H_eta (-η) z = H_eta η z := by
  simp only [H_eta]
  -- Define the measure-preserving substitution T((x₁,x₂),(y₁,y₂)) = ((-x₁,x₂),(-y₁,y₂))
  let T : (ℝ × ℝ) × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).prodCongr
      ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ))
  have hT_mp : MeasurePreserving T volume volume := by
    have h_neg_mp : MeasurePreserving (MeasurableEquiv.neg ℝ) (volume : Measure ℝ) volume :=
      Measure.measurePreserving_neg volume
    have h_id_mp : MeasurePreserving (MeasurableEquiv.refl ℝ) (volume : Measure ℝ) volume :=
      MeasurePreserving.id volume
    have h_negFst : MeasurePreserving
        ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ))
        (volume : Measure (ℝ × ℝ)) volume :=
      h_neg_mp.prod h_id_mp
    exact h_negFst.prod h_negFst
  have hf' : ∀ (x₁ x₂ : ℝ), f_eta (-η) (x₁, x₂) = f_eta η (-x₁, x₂) := by
    intro x₁ x₂; have := f_eta_neg_eta η (-x₁) x₂; simp only [neg_neg] at this; exact this
  let g := fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
    ↑(f_eta η p.1 * f_eta η p.2) * cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
      (2 * ↑Real.pi * (1 - z ^ 2))
  -- Show LHS integrand = g ∘ T
  have heq : (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ↑(f_eta (-η) p.1 * f_eta (-η) p.2) * cexp (kernel_exponent p.1.1 p.1.2 p.2.1 p.2.2 z) /
        (2 * ↑Real.pi * (1 - z ^ 2))) = g ∘ T := by
    ext ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    simp only [g, T, Function.comp]
    dsimp [MeasurableEquiv.prodCongr, MeasurableEquiv.neg, MeasurableEquiv.refl, Equiv.prodCongr]
    rw [hf' x₁ x₂, hf' y₁ y₂, kernel_exponent_neg_fst]
  rw [heq]
  exact hT_mp.integral_comp' g

theorem Phi_even (η : ℝ) : Phi (-η) = Phi η := by
  simp only [Phi, varphi, H_eta_even]

/-! ## Conversion lemma -/

/-- At η = 0, `φ(0) = Re(H₀(i)/i) = log(1+√2)`.
    Uses Lemma 4.3: `sin(H₀(z)) = z` on S, so H₀(i) = arcsin(i) = i·log(1+√2). -/
theorem varphi_zero : varphi 0 = Real.log (1 + Real.sqrt 2) := by
  unfold varphi
  -- H_eta 0 = H0 by definition
  show (H0 Complex.I / Complex.I).re = Real.log (1 + Real.sqrt 2)
  -- Key: H0(I) = ↑(arsinh 1) * I, via H0_sin_eq and sin(↑t * I) = I
  set t := Real.arsinh 1 with ht_def
  -- Step 1: sin(↑t * I) = I
  have h_sin_z : Complex.sin ((↑t : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.sin_mul_I, ← Complex.ofReal_sinh, Real.sinh_arsinh]
    simp
  -- Step 2: ↑t * I satisfies hypotheses of H0_sin_eq
  have h_re : |((↑t : ℂ) * Complex.I).re| < Real.pi / 2 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    positivity
  have h_mem : Complex.sin ((↑t : ℂ) * Complex.I) ∈ S := by
    rw [h_sin_z, mem_S_iff, Complex.I_re, abs_zero]; exact one_pos
  -- Step 3: H0(I) = ↑t * I
  have h_H0 : H0 Complex.I = (↑t : ℂ) * Complex.I := by
    conv_lhs => rw [← h_sin_z]
    exact H0_sin_eq ((↑t : ℂ) * Complex.I) h_re h_mem
  -- Step 4: Simplify H0(I)/I
  rw [h_H0, mul_div_cancel_right₀ _ Complex.I_ne_zero, Complex.ofReal_re]
  -- Step 5: arsinh 1 = log(1+√2)
  simp [ht_def, Real.arsinh]
  congr 1; norm_num


/-- Converting `Φ(η) > Φ(0)` back to the original theorem statement.
    Since Φ = 4π · φ and 4π > 0, we have φ(η) > φ(0) = log(1+√2). -/
theorem theorem_4_4_of_Phi_pos
    (h : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → Phi η > Phi 0) :
    ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
      (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2) := by
  obtain ⟨η₀, hη₀pos, hmain⟩ := h
  refine ⟨η₀, hη₀pos, fun η hηpos hηlt => ?_⟩
  have hPhi := hmain η hηpos hηlt
  unfold Phi at hPhi
  have hpi : (0 : ℝ) < 4 * Real.pi := by positivity
  have h1 : varphi η > varphi 0 := by nlinarith
  have h2 := varphi_zero
  unfold varphi at h1 h2
  linarith


end Braverman
