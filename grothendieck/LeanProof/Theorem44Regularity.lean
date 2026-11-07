/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Theorem 4.4 Regularity

Local C⁴ regularity of Φ near 0, plus odd-derivative vanishing.

## Strategy (from the plan)
Work with the one-parameter integrand of Φ directly. The exponent is
quadratic in η, so K''' = K'''' = 0, and all derivatives of exp(K(η))
up to order 4 are explicit polynomials times exp(K(η)).

Use `hasDerivAt_integral_of_dominated_loc_of_deriv_le` iterated 4 times.

## What NOT to do
- Do not prove ContDiff ℝ ∞
- Do not prove a generic theorem for all kernels
- Do not use F_reduced
- Do not introduce iteratedFDeriv
-/

open Complex Set Real MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Braverman

attribute [fun_prop] h5_continuous

/-! ## E1. Local C⁴ regularity -/

/-! ### Shifted integrand for the regularity proof

After the substitution x₂ = u + η·h₅(x₁), y₂ = v + η·h₅(y₁) in F44(η,η),
the integration domain becomes fixed (u > 0, v > 0) and the integrand
is smooth in η (the exponent is quadratic in η). -/

abbrev P44 := (ℝ × ℝ) × (ℝ × ℝ)

/-- Shifted integrand: 1_{u>0} · 1_{v>0} · exp(−Q/2) · sin(D)
    where Q, D are quadratic in η. -/
def Phi_integrand (η : ℝ) (p : P44) : ℝ :=
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let x₂ := u + η * h5 x₁; let y₂ := v + η * h5 y₁
  4 * ((if 0 < u then 1 else 0) * (if 0 < v then 1 else 0) *
    (Real.exp (-(x₁ ^ 2 + x₂ ^ 2 + y₁ ^ 2 + y₂ ^ 2) / 2) *
      Real.sin (x₁ * y₁ + x₂ * y₂)))

/-- The connection: Phi η = ∫ Phi_integrand η for all η.
    This follows from Phi_eq_F44_diag and the shift substitution. -/
-- Helper: shifting an Ioi set integral by translation
private lemma setIntegral_Ioi_comp_add (f : ℝ → ℝ) (c : ℝ) :
    ∫ x in Ioi c, f x = ∫ u, (if (0 : ℝ) < u then f (u + c) else 0) := by
  calc ∫ x in Ioi c, f x
      = ∫ x, (Ioi c).indicator f x :=
        (integral_indicator measurableSet_Ioi).symm
    _ = ∫ u, (Ioi c).indicator f (u + c) :=
        (integral_add_right_eq_self _ c).symm
    _ = ∫ u, (if 0 < u then f (u + c) else 0) := by
        congr 1; ext u; simp only [indicator, mem_Ioi]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by linarith : 0 < u) h2
        · exact absurd (show c < u + c by linarith) (not_lt.mpr (not_lt.mp h1))
        · rfl

/-- The base integrand is measurable in p for each fixed η. -/
lemma Phi_integrand_measurable (η : ℝ) :
    Measurable (fun p : P44 => Phi_integrand η p) := by
  unfold Phi_integrand; simp only []
  apply Measurable.const_mul
  apply Measurable.mul
  · apply Measurable.mul
    · exact measurable_const.ite
        (measurableSet_lt measurable_const measurable_fst.snd)
        measurable_const
    · exact measurable_const.ite
        (measurableSet_lt measurable_const measurable_snd.snd)
        measurable_const
  · exact (show Continuous (fun p : P44 =>
        Real.exp (-(p.1.1 ^ 2 + (p.1.2 + η * h5 p.1.1) ^ 2 +
          p.2.1 ^ 2 + (p.2.2 + η * h5 p.2.1) ^ 2) / 2) *
        Real.sin (p.1.1 * p.2.1 +
          (p.1.2 + η * h5 p.1.1) *
            (p.2.2 + η * h5 p.2.1)))
      by fun_prop).measurable

-- Integrability of Phi_integrand via Gaussian domination.
lemma Phi_integrand_integrable (η : ℝ) :
    Integrable (fun p : P44 => Phi_integrand η p) volume := by
  -- 1D Gaussian is integrable
  have hg : Integrable (fun x : ℝ =>
      Real.exp (-(1 / 2 : ℝ) * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by positivity)
  -- Helper: translated Gaussian integrability
  have htg : ∀ c : ℝ, Integrable (fun u : ℝ =>
      Real.exp (-((u + c) ^ 2 / 2))) volume := by
    intro c
    exact (hg.comp_add_right c).congr
      (Filter.Eventually.of_forall fun u => by
        change Real.exp (-(1 / 2) * (u + c) ^ 2) =
          Real.exp (-((u + c) ^ 2 / 2))
        congr 1; ring)
  -- Helper: translation invariance of the Gaussian integral
  have htrans : ∀ c : ℝ,
      ∫ u, Real.exp (-((u + c) ^ 2 / 2)) =
      ∫ u, Real.exp (-(u ^ 2 / 2)) :=
    fun c => integral_add_right_eq_self
      (μ := (volume : Measure ℝ))
      (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) c
  -- Shifted 2D Gaussian is integrable on ℝ²
  have hF : Integrable (fun q : ℝ × ℝ =>
      Real.exp (-(q.1 ^ 2 +
        (q.2 + η * h5 q.1) ^ 2) / 2)) volume := by
    have hcont : Continuous (fun q : ℝ × ℝ =>
        Real.exp (-(q.1 ^ 2 +
          (q.2 + η * h5 q.1) ^ 2) / 2)) := by fun_prop
    rw [show (volume : Measure (ℝ × ℝ)) =
          volume.prod volume from rfl,
        integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun x₁ => ?_, ?_⟩
    · -- Inner: u ↦ exp(-(x₁²+(u+c)²)/4) is integrable
      have hfact : ∀ u,
          Real.exp (-(x₁ ^ 2 +
            (u + η * h5 x₁) ^ 2) / 2) =
          Real.exp (-(x₁ ^ 2) / 2) *
            Real.exp (-((u + η * h5 x₁) ^ 2 / 2)) := by
        intro u; rw [← Real.exp_add]; congr 1; ring
      simp_rw [hfact]
      exact (htg (η * h5 x₁)).const_mul _
    · -- Outer: x₁ ↦ ∫ ‖F(x₁,u)‖ du is integrable
      simp_rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      have hfact : ∀ x₁ u,
          Real.exp (-(x₁ ^ 2 +
            (u + η * h5 x₁) ^ 2) / 2) =
          Real.exp (-(x₁ ^ 2) / 2) *
            Real.exp (-((u + η * h5 x₁) ^ 2 / 2)) := by
        intro x₁ u; rw [← Real.exp_add]; congr 1; ring
      simp_rw [hfact, integral_const_mul, htrans]
      exact (hg.congr (Filter.Eventually.of_forall
        fun x₁ => by
          show Real.exp (-(1 / 2) * x₁ ^ 2) =
            Real.exp (-(x₁ ^ 2) / 2)
          congr 1; ring)).mul_const _
  -- Product of two 2D Gaussians is integrable on (ℝ²)²
  -- With the factor 4, we dominate by 4 * (F₁ * F₂) which is still integrable
  have hdom := hF.mul_prod hF
  exact (hdom.const_mul 4).mono'
    (Phi_integrand_measurable η).aestronglyMeasurable
    (ae_of_all _ fun p => by
      unfold Phi_integrand; simp only []
      -- Bound: ‖4 * (ind * ind * (exp * sin))‖ ≤ 4 * (F₁ * F₂)
      rw [norm_mul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 4)]
      simp only [Real.norm_eq_abs]
      gcongr
      -- Step 1: |product| ≤ exp(full exponent)
      have h1 : ∀ (a b : ℝ) (_ : |a| ≤ 1) (_ : |b| ≤ 1)
          (E : ℝ) (_ : 0 ≤ E) (S : ℝ) (_ : |S| ≤ 1),
          |a * b * (E * S)| ≤ E := by
        intro a b ha hb E hE S hS
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg hE]
        calc |a| * |b| * (E * |S|)
            ≤ 1 * 1 * (E * 1) := by gcongr
          _ = E := by ring
      -- Step 2: exp(Q) = exp(Q₁) * exp(Q₂)
      have h2 : Real.exp (-(p.1.1 ^ 2 +
            (p.1.2 + η * h5 p.1.1) ^ 2 + p.2.1 ^ 2 +
            (p.2.2 + η * h5 p.2.1) ^ 2) / 2) =
          Real.exp (-(p.1.1 ^ 2 +
            (p.1.2 + η * h5 p.1.1) ^ 2) / 2) *
          Real.exp (-(p.2.1 ^ 2 +
            (p.2.2 + η * h5 p.2.1) ^ 2) / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h2]
      exact h1 _ _ (by split_ifs <;> simp)
        (by split_ifs <;> simp) _ (by positivity) _
        (abs_sin_le_one _))

theorem Phi_eq_shifted_integral (η : ℝ) :
    Phi η = ∫ p : P44, Phi_integrand η p := by
  rw [Phi_eq_F44_diag]; unfold F44
  -- Apply the translation shift to both Ioi integrals
  simp_rw [setIntegral_Ioi_comp_add]
  -- Push the factor 4 inside all integrals
  simp_rw [← MeasureTheory.integral_const_mul]
  -- After shift, LHS = ∫ x₁ ∫ y₁ ∫ u, (if 0 < u then ∫ v, (if 0 < v then base_shifted else 0) else 0)
  -- RHS = ∫ p : P44, Phi_integrand η p = ∫ x₁ ∫ u ∫ y₁ ∫ v, ind(u>0)*ind(v>0)*base_shifted
  -- These are equal: integral_prod to decompose RHS, Fubini to swap y₁ ↔ u, then
  -- pull indicators into the if-then-else form. All steps need Phi_integrand_integrable η.
  -- Define the coordinate permutation ((a,b),(c,d)) ↦ ((a,c),(b,d))
  let inner : MeasurableEquiv (ℝ × (ℝ × ℝ)) (ℝ × (ℝ × ℝ)) :=
    MeasurableEquiv.prodAssoc.symm.trans
      (((MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).prodCongr (MeasurableEquiv.refl ℝ)).trans
        MeasurableEquiv.prodAssoc)
  let e : MeasurableEquiv P44 P44 :=
    MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl ℝ).prodCongr inner).trans
        MeasurableEquiv.prodAssoc.symm)
  have he : ∀ p : P44, e p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := by
    intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  have hmp : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc :
        MeasurableEquiv ((ℝ × ℝ) × (ℝ × ℝ)) (ℝ × ℝ × (ℝ × ℝ))) volume volume :=
      volume_preserving_prodAssoc
    have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc :
        MeasurableEquiv ((ℝ × ℝ) × ℝ) (ℝ × ℝ × ℝ)) volume volume :=
      volume_preserving_prodAssoc
    exact h1.symm.comp
      (((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
        ((h2.comp ((Measure.measurePreserving_swap.prod
          (MeasurePreserving.id (μ := (volume : Measure ℝ)))))).comp
            h2.symm)).comp h1)
  have hie : Integrable ((Phi_integrand η) ∘ e) volume :=
    (hmp.integrable_comp_emb e.measurableEmbedding).mpr (Phi_integrand_integrable η)
  have h_sec_r := Integrable.prod_right_ae hie
  have h_ipl := Integrable.integral_prod_left hie
  have h_inner_ae : ∀ᵐ (a : ℝ × ℝ) ∂volume,
      (∫ u, ∫ v, (Phi_integrand η ∘ e) (a, (u, v))) = ∫ (b : ℝ × ℝ), (Phi_integrand η ∘ e) (a, b) := by
    filter_upwards [h_sec_r] with a ha
    exact integral_integral (f := fun u v => (Phi_integrand η ∘ e) (a, (u, v))) ha
  have h_outer_int : Integrable
      (Function.uncurry fun x₁ y₁ => ∫ u, ∫ v, (Phi_integrand η ∘ e) ((x₁, y₁), (u, v)))
      (volume.prod volume) :=
    h_ipl.congr (h_inner_ae.mono fun a ha => ha.symm)
  -- Convert LHS if-then-else to (Phi_integrand η ∘ e) iterated integral form
  have hLHS : (∫ (x₁ : ℝ) (y₁ : ℝ) (u : ℝ),
      4 * (if 0 < u then ∫ (v : ℝ),
        if 0 < v then
          rexp (-(x₁ ^ 2 + (u + η * h5 x₁) ^ 2 + y₁ ^ 2 + (v + η * h5 y₁) ^ 2) / 2) *
            Real.sin (x₁ * y₁ + (u + η * h5 x₁) * (v + η * h5 y₁))
        else 0 else 0)) =
      ∫ x₁, ∫ y₁, ∫ u, ∫ v, (Phi_integrand η ∘ e) ((x₁, y₁), (u, v)) := by
    congr 1; ext x₁; congr 1; ext y₁; congr 1; ext u
    simp only [Phi_integrand, Function.comp, he]; split_ifs with hu
    · rw [← MeasureTheory.integral_const_mul]; congr 1; ext v; split_ifs <;> simp [mul_comm]
    · simp
  rw [hLHS]; symm
  -- Decompose the RHS product integral into iterated integrals
  rw [← hmp.integral_comp' (Phi_integrand η)]
  change (∫ (p : P44), (Phi_integrand η ∘ e) p ∂volume.prod volume) = _
  rw [integral_prod _ hie, ← integral_congr_ae h_inner_ae]
  convert (integral_integral
    (f := fun x₁ y₁ => ∫ u, ∫ v, (Phi_integrand η ∘ e) ((x₁, y₁), (u, v))) h_outer_int).symm using 1

/-- The shifted integrand is smooth in η for each fixed p (the exponent is
    quadratic in η, so all derivatives are polynomial × exp × trig). -/
lemma Phi_integrand_contDiff_eta (p : P44) : ContDiff ℝ ⊤ (Phi_integrand · p) := by
  unfold Phi_integrand; fun_prop

/-! ### Envelope and domination helpers for Phi_integrand_dominated -/

/-- Envelope function for shifted Gaussian: dominates exp(-(u+ηh)²/8) for |η| ≤ 2. -/
private noncomputable def φ_env (u h : ℝ) : ℝ :=
  Real.exp (-(max 0 (u - 2 * |h|)) ^ 2 / 8)

private lemma φ_env_nonneg (u h : ℝ) : 0 ≤ φ_env u h := Real.exp_nonneg _

private lemma φ_env_le_one (u h : ℝ) : φ_env u h ≤ 1 :=
  Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos_of_nonneg (sq_nonneg _)) (by norm_num))

/-- Key envelope domination: for u > 0, |η| ≤ 2, the shifted Gaussian is bounded. -/
private lemma φ_env_dominates {u h η : ℝ} (hu : 0 < u) (hη : |η| ≤ 2) :
    Real.exp (-(u + η * h) ^ 2 / 8) ≤ φ_env u h := by
  unfold φ_env; rw [Real.exp_le_exp]
  suffices hsq : (max 0 (u - 2 * |h|)) ^ 2 ≤ (u + η * h) ^ 2 by linarith
  by_cases hle : u ≤ 2 * |h|
  · simp [show u - 2 * |h| ≤ 0 from by linarith, sq_nonneg]
  · push_neg at hle
    have hmax : max 0 (u - 2 * |h|) = u - 2 * |h| :=
      max_eq_right (by linarith)
    rw [hmax]
    have hshift : u - 2 * |h| ≤ u + η * h := by
      suffices η * h ≥ -(2 * |h|) by linarith
      calc η * h ≥ -(|η * h|) := neg_abs_le _
        _ = -(|η| * |h|) := by rw [abs_mul]
        _ ≥ -(2 * |h|) := by linarith [mul_le_mul_of_nonneg_right hη (abs_nonneg h)]
    have hpos : 0 < u + η * h := by linarith
    exact sq_le_sq' (by linarith) hshift

/-- The smooth part of Phi_integrand (without indicators), as a function of η. -/
private def Φ_smooth (p : P44) (η : ℝ) : ℝ :=
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 + y₁ ^ 2 + (v + η * g) ^ 2) / 2) *
    Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g))

private lemma Φ_smooth_contDiff (p : P44) : ContDiff ℝ ⊤ (Φ_smooth p) := by
  unfold Φ_smooth; fun_prop

/-- Phi_integrand factors as indicators × smooth part. -/
private lemma Phi_integrand_eq_ind_mul_smooth (η : ℝ) (p : P44) :
    Phi_integrand η p = 4 * ((if 0 < p.1.2 then 1 else 0) * (if 0 < p.2.2 then 1 else 0) *
      Φ_smooth p η) := by
  unfold Phi_integrand Φ_smooth; ring

/-- The explicit domination bound. -/
private noncomputable def Φ_bound (p : P44) : ℝ :=
  let h := h5 p.1.1; let g := h5 p.2.1
  (10 ^ 10 : ℝ) *
  (if 0 < p.1.2 then (1 : ℝ) else 0) * (if 0 < p.2.2 then (1 : ℝ) else 0) *
  (1 + h ^ 2 + g ^ 2) ^ 10 *
  Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
  φ_env p.1.2 h * φ_env p.2.2 g

private lemma Φ_bound_nonneg (p : P44) : 0 ≤ Φ_bound p := by
  unfold Φ_bound
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · split_ifs <;> positivity
          · split_ifs <;> positivity
        · positivity
      · exact Real.exp_nonneg _
    · exact φ_env_nonneg _ _
  · exact φ_env_nonneg _ _

/-! ### Helper lemmas for Φ_smooth_deriv_le -/

/-- Taylor bound: xⁿ/n! ≤ exp(x) for x ≥ 0. -/
private lemma pow_div_factorial_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / n.factorial ≤ Real.exp x :=
  le_trans (Finset.single_le_sum (f := fun i => x ^ i / ↑i.factorial)
      (fun _ _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)))
    (Real.sum_le_exp_of_nonneg hx (n + 1))

/-- Polynomial absorption: xⁿ * exp(-x) ≤ n! for x ≥ 0. -/
private lemma pow_mul_exp_neg_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-x) ≤ n.factorial := by
  have h := pow_div_factorial_le_exp x hx n
  have := mul_le_mul_of_nonneg_right
    (show x ^ n ≤ ↑n.factorial * Real.exp x by
      rwa [div_le_iff₀ (Nat.cast_pos.mpr n.factorial_pos), mul_comm] at h)
    (Real.exp_nonneg (-x))
  simp only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
  exact this

/-- Gaussian absorption: s⁴ * exp(-s/8) ≤ 98304 for s ≥ 0. -/
private lemma pow4_mul_exp_neg_div8_le (s : ℝ) (hs : 0 ≤ s) :
    s ^ 4 * Real.exp (-(s / 8)) ≤ 98304 := by
  have hs8 : 0 ≤ s / 8 := div_nonneg hs (by norm_num)
  have h1 := pow_mul_exp_neg_le (s / 8) hs8 4
  have : s ^ 4 * Real.exp (-(s / 8)) =
      (8 : ℝ) ^ 4 * ((s / 8) ^ 4 * Real.exp (-(s / 8))) := by ring
  rw [this]; nlinarith [Nat.factorial]

/-- The exponent function Q(η) = -(x₁²+(u+ηh)²+y₁²+(v+ηg)²)/2. -/
private def Q_fun (p : P44) (η : ℝ) : ℝ :=
  -(p.1.1 ^ 2 + (p.1.2 + η * h5 p.1.1) ^ 2 +
    p.2.1 ^ 2 + (p.2.2 + η * h5 p.2.1) ^ 2) / 2

/-- The sin-argument function L(η) = x₁y₁+(u+ηh)(v+ηg). -/
private def L_fun (p : P44) (η : ℝ) : ℝ :=
  p.1.1 * p.2.1 +
    (p.1.2 + η * h5 p.1.1) * (p.2.2 + η * h5 p.2.1)

private lemma Q_fun_contDiff (p : P44) : ContDiff ℝ ⊤ (Q_fun p) := by
  unfold Q_fun; fun_prop

private lemma L_fun_contDiff (p : P44) : ContDiff ℝ ⊤ (L_fun p) := by
  unfold L_fun; fun_prop

/-- Φ_smooth factors as exp(Q) * sin(L). -/
private lemma Φ_smooth_eq_exp_mul_sin (p : P44) (η : ℝ) :
    Φ_smooth p η = Real.exp (Q_fun p η) * Real.sin (L_fun p η) := by
  simp only [Φ_smooth, Q_fun, L_fun]

/-- Q_fun is quadratic in η. -/
private lemma Q_fun_eq_quad (p : P44) (η : ℝ) :
    Q_fun p η =
    (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) +
    (-(p.1.2 * h5 p.1.1 + p.2.2 * h5 p.2.1)) * η +
    (-(h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) / 2) * η ^ 2 := by
  unfold Q_fun; ring

/-- L_fun is quadratic in η. -/
private lemma L_fun_eq_quad (p : P44) (η : ℝ) :
    L_fun p η =
    (p.1.1 * p.2.1 + p.1.2 * p.2.2) +
    (p.1.2 * h5 p.2.1 + p.2.2 * h5 p.1.1) * η +
    (h5 p.1.1 * h5 p.2.1) * η ^ 2 := by
  unfold L_fun; ring

/-- iteratedDeriv of a quadratic polynomial vanishes for k ≥ 3. -/
private lemma iteratedDeriv_quad_vanish (c₀ c₁ c₂ : ℝ)
    (k : ℕ) (hk : 3 ≤ k) (η : ℝ) :
    iteratedDeriv k (fun η => c₀ + c₁ * η + c₂ * η ^ 2) η = 0 := by
  have heq1 : (fun η : ℝ => c₀ + c₁ * η + c₂ * η ^ 2) =ᶠ[nhds η]
      ((fun _ => c₀) + fun η => c₁ * η + c₂ * η ^ 2) := by
    filter_upwards with t; simp [Pi.add_apply]; ring
  have heq2 : (fun η : ℝ => c₁ * η + c₂ * η ^ 2) =ᶠ[nhds η]
      ((fun η => c₁ * η) + fun η => c₂ * η ^ 2) := by
    filter_upwards with t; simp [Pi.add_apply]
  rw [heq1.iteratedDeriv_eq k,
      iteratedDeriv_add contDiffAt_const (by fun_prop)]
  simp only [iteratedDeriv_const, show k ≠ 0 from by omega, ite_false,
    zero_add]
  rw [heq2.iteratedDeriv_eq k,
      iteratedDeriv_add (by fun_prop) (by fun_prop),
      iteratedDeriv_const_mul c₁
        (by fun_prop : ContDiffAt ℝ (↑k) (fun η : ℝ => η) η),
      show (fun η : ℝ => η) = (· ^ 1) from by ext; simp,
      iteratedDeriv_pow 1 k,
      show (1 : ℕ).descFactorial k = 0 from
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),
      iteratedDeriv_const_mul c₂
        (by fun_prop : ContDiffAt ℝ (↑k) (fun η : ℝ => η ^ 2) η),
      iteratedDeriv_pow 2 k,
      show (2 : ℕ).descFactorial k = 0 from
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
  simp

/-- iteratedDeriv k of Q_fun vanishes for k ≥ 3. -/
private lemma Q_fun_iteratedDeriv_vanish (p : P44) (k : ℕ) (hk : 3 ≤ k)
    (η : ℝ) : iteratedDeriv k (Q_fun p) η = 0 := by
  rw [(show Q_fun p =ᶠ[nhds η] (fun η =>
      (-(p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / 2) +
      (-(p.1.2 * h5 p.1.1 + p.2.2 * h5 p.2.1)) * η +
      (-(h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) / 2) * η ^ 2) from by
    filter_upwards with t; exact Q_fun_eq_quad p t).iteratedDeriv_eq k]
  exact iteratedDeriv_quad_vanish _ _ _ k hk η

/-- iteratedDeriv k of L_fun vanishes for k ≥ 3. -/
private lemma L_fun_iteratedDeriv_vanish (p : P44) (k : ℕ) (hk : 3 ≤ k)
    (η : ℝ) : iteratedDeriv k (L_fun p) η = 0 := by
  rw [(show L_fun p =ᶠ[nhds η] (fun η =>
      (p.1.1 * p.2.1 + p.1.2 * p.2.2) +
      (p.1.2 * h5 p.2.1 + p.2.2 * h5 p.1.1) * η +
      (h5 p.1.1 * h5 p.2.1) * η ^ 2) from by
    filter_upwards with t; exact L_fun_eq_quad p t).iteratedDeriv_eq k]
  exact iteratedDeriv_quad_vanish _ _ _ k hk η

/-- HasDerivAt for Q_fun. -/
private lemma Q_fun_hasDerivAt (p : P44) (η : ℝ) :
    HasDerivAt (Q_fun p)
    (-(h5 p.1.1 * (p.1.2 + η * h5 p.1.1) +
       h5 p.2.1 * (p.2.2 + η * h5 p.2.1))) η := by
  have h1 := ((hasDerivAt_id η).mul_const (h5 p.1.1)).const_add p.1.2
  have h3 : HasDerivAt (fun η => (p.1.2 + η * h5 p.1.1) ^ 2)
      (2 * h5 p.1.1 * (p.1.2 + η * h5 p.1.1)) η := by
    convert h1.pow 2 using 1; simp [Nat.cast_ofNat]; ring
  have h2 := ((hasDerivAt_id η).mul_const (h5 p.2.1)).const_add p.2.2
  have h4 : HasDerivAt (fun η => (p.2.2 + η * h5 p.2.1) ^ 2)
      (2 * h5 p.2.1 * (p.2.2 + η * h5 p.2.1)) η := by
    convert h2.pow 2 using 1; simp [Nat.cast_ofNat]; ring
  have h5' := ((hasDerivAt_const η (p.1.1 ^ 2)).add h3).add
              ((hasDerivAt_const η (p.2.1 ^ 2)).add h4)
  show HasDerivAt (Q_fun p) _ η
  unfold Q_fun
  convert (h5'.neg.div_const 2) using 1
  · funext t; simp [Pi.add_apply, Pi.neg_apply]; ring
  · ring

/-- HasDerivAt for L_fun. -/
private lemma L_fun_hasDerivAt (p : P44) (η : ℝ) :
    HasDerivAt (L_fun p)
    (h5 p.2.1 * (p.1.2 + η * h5 p.1.1) +
      h5 p.1.1 * (p.2.2 + η * h5 p.2.1)) η := by
  have h1 := ((hasDerivAt_id η).mul_const (h5 p.1.1)).const_add p.1.2
  have h2 := ((hasDerivAt_id η).mul_const (h5 p.2.1)).const_add p.2.2
  have h3 : HasDerivAt (fun η => (p.1.2 + η * h5 p.1.1) *
      (p.2.2 + η * h5 p.2.1))
    (h5 p.1.1 * (p.2.2 + η * h5 p.2.1) +
     (p.1.2 + η * h5 p.1.1) * h5 p.2.1) η := by
    convert h1.mul h2 using 1; simp [id]
  show HasDerivAt (L_fun p) _ η
  unfold L_fun
  convert h3.const_add (p.1.1 * p.2.1) using 1 <;>
    first | (funext t; simp [Pi.add_apply]; ring) | ring

/-- HasDerivAt for the first derivative of Q_fun (yielding Q''). -/
private lemma Q_fun_hasDerivAt2 (p : P44) (η : ℝ) :
    HasDerivAt (fun η => -(h5 p.1.1 * (p.1.2 + η * h5 p.1.1) +
       h5 p.2.1 * (p.2.2 + η * h5 p.2.1)))
    (-(h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2)) η := by
  have h1 := ((hasDerivAt_id η).mul_const (h5 p.1.1)).const_add p.1.2
  have h2 := ((hasDerivAt_id η).mul_const (h5 p.2.1)).const_add p.2.2
  have h3 := (h1.const_mul (h5 p.1.1)).add (h2.const_mul (h5 p.2.1))
  convert h3.neg using 1 <;>
    first | (funext t; ring) | ring

/-- HasDerivAt for the first derivative of L_fun (yielding L''). -/
private lemma L_fun_hasDerivAt2 (p : P44) (η : ℝ) :
    HasDerivAt (fun η => h5 p.2.1 * (p.1.2 + η * h5 p.1.1) +
      h5 p.1.1 * (p.2.2 + η * h5 p.2.1))
    (2 * h5 p.1.1 * h5 p.2.1) η := by
  have h1 := ((hasDerivAt_id η).mul_const (h5 p.1.1)).const_add p.1.2
  have h2 := ((hasDerivAt_id η).mul_const (h5 p.2.1)).const_add p.2.2
  have h3 := (h1.const_mul (h5 p.2.1)).add (h2.const_mul (h5 p.1.1))
  convert h3 using 1 <;>
    first | (funext t; ring) | ring

/-- iteratedDeriv 2 of Q_fun is constant: -(h²+g²). -/
private lemma Q_fun_iteratedDeriv2 (p : P44) (η : ℝ) :
    iteratedDeriv 2 (Q_fun p) η = -(h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) := by
  -- iteratedDeriv 2 f = deriv (iteratedDeriv 1 f) = deriv (deriv f)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- Now goal: deriv (deriv (Q_fun p)) η = ...
  have h1 : deriv (Q_fun p) =ᶠ[nhds η]
      (fun η => -(h5 p.1.1 * (p.1.2 + η * h5 p.1.1) +
        h5 p.2.1 * (p.2.2 + η * h5 p.2.1))) := by
    filter_upwards with t; exact (Q_fun_hasDerivAt p t).deriv
  rw [h1.deriv_eq]
  exact (Q_fun_hasDerivAt2 p η).deriv

/-- iteratedDeriv 2 of L_fun is constant: 2*h*g. -/
private lemma L_fun_iteratedDeriv2 (p : P44) (η : ℝ) :
    iteratedDeriv 2 (L_fun p) η = 2 * h5 p.1.1 * h5 p.2.1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (L_fun p) =ᶠ[nhds η]
      (fun η => h5 p.2.1 * (p.1.2 + η * h5 p.1.1) +
        h5 p.1.1 * (p.2.2 + η * h5 p.2.1)) := by
    filter_upwards with t; exact (L_fun_hasDerivAt p t).deriv
  rw [h1.deriv_eq]
  exact (L_fun_hasDerivAt2 p η).deriv

/-- Translating Leibniz rule to iteratedDeriv. -/
private lemma norm_iteratedDeriv_mul_le {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (x : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedDeriv i f x‖ * ‖iteratedDeriv (k - i) g x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  calc ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k - i) g x‖ :=
        norm_iteratedFDeriv_mul_le hf hg x le_top
    _ = _ := by congr 1; ext i; simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- Translating chain rule bound to iteratedDeriv. -/
private lemma norm_iteratedDeriv_comp_le {g : ℝ → ℝ} {f : ℝ → ℝ} {k : ℕ}
    (hg : ContDiff ℝ ⊤ g) (hf : ContDiff ℝ ⊤ f) (x : ℝ) {C D : ℝ}
    (hC : ∀ i ≤ k, ‖iteratedDeriv i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedDeriv i f x‖ ≤ D ^ i) :
    ‖iteratedDeriv k (g ∘ f) x‖ ≤ k.factorial * C * D ^ k := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedFDeriv_comp_le hg hf le_top x
    (fun i hi => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC i hi)
    (fun i h1 h2 => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hD i h1 h2)

/-- D parameter for the chain rule bounds. -/
private noncomputable def D_val (h g α β : ℝ) : ℝ :=
  1 + h ^ 2 + g ^ 2 + α ^ 2 + β ^ 2

private lemma D_val_pos (h g α β : ℝ) : 0 < D_val h g α β := by
  unfold D_val; positivity

private lemma D_val_ge_one (h g α β : ℝ) : 1 ≤ D_val h g α β := by
  unfold D_val; nlinarith [sq_nonneg h, sq_nonneg g, sq_nonneg α, sq_nonneg β]

/-- AM-GM helper: |a*b| ≤ (a²+b²)/2. -/
private lemma abs_mul_le_sq_add_sq_div2 (a b : ℝ) :
    |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have := sq_abs a; have := sq_abs b; have := sq_nonneg (|a| - |b|)
  rw [abs_mul]; nlinarith

/-- First derivative of Q_fun is bounded by D_val. -/
private lemma Q_fun_deriv_bound (p : P44) (η : ℝ) :
    |deriv (Q_fun p) η| ≤ D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) := by
  rw [(Q_fun_hasDerivAt p η).deriv]
  set h := h5 p.1.1; set g := h5 p.2.1
  set α := p.1.2 + η * h; set β := p.2.2 + η * g
  have hab := abs_mul_le_sq_add_sq_div2 h α
  have hgb := abs_mul_le_sq_add_sq_div2 g β
  calc |-(h * α + g * β)|
      = |h * α + g * β| := abs_neg _
    _ ≤ |h * α| + |g * β| := abs_add_le _ _
    _ ≤ (h ^ 2 + α ^ 2) / 2 + (g ^ 2 + β ^ 2) / 2 := by linarith
    _ = (h ^ 2 + g ^ 2 + α ^ 2 + β ^ 2) / 2 := by ring
    _ ≤ D_val h g α β := by
        unfold D_val; nlinarith [sq_nonneg h, sq_nonneg g, sq_nonneg α, sq_nonneg β]

/-- First derivative of L_fun is bounded by D_val. -/
private lemma L_fun_deriv_bound (p : P44) (η : ℝ) :
    |deriv (L_fun p) η| ≤ D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) := by
  rw [(L_fun_hasDerivAt p η).deriv]
  set h := h5 p.1.1; set g := h5 p.2.1
  set α := p.1.2 + η * h; set β := p.2.2 + η * g
  have hga := abs_mul_le_sq_add_sq_div2 g α
  have hhb := abs_mul_le_sq_add_sq_div2 h β
  calc |g * α + h * β|
      ≤ |g * α| + |h * β| := abs_add_le _ _
    _ ≤ (g ^ 2 + α ^ 2) / 2 + (h ^ 2 + β ^ 2) / 2 := by linarith
    _ = (h ^ 2 + g ^ 2 + α ^ 2 + β ^ 2) / 2 := by ring
    _ ≤ D_val h g α β := by
        unfold D_val; nlinarith [sq_nonneg h, sq_nonneg g, sq_nonneg α, sq_nonneg β]

/-- Second derivative of Q_fun is bounded by D_val². -/
private lemma Q_fun_deriv2_bound (p : P44) (η : ℝ) :
    |iteratedDeriv 2 (Q_fun p) η| ≤
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ 2 := by
  rw [Q_fun_iteratedDeriv2]
  set h := h5 p.1.1; set g := h5 p.2.1
  set D := D_val h g (p.1.2 + η * h) (p.2.2 + η * g)
  have hD1 : 1 ≤ D := D_val_ge_one _ _ _ _
  have hDhg : h ^ 2 + g ^ 2 ≤ D := by
    simp only [D, D_val]; nlinarith [sq_nonneg (p.1.2 + η * h), sq_nonneg (p.2.2 + η * g)]
  have hval : |-(h ^ 2 + g ^ 2)| = h ^ 2 + g ^ 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg h, sq_nonneg g])]; ring
  rw [hval]
  calc h ^ 2 + g ^ 2 ≤ D := hDhg
    _ ≤ D ^ 2 := le_self_pow₀ hD1 (by omega)

/-- Second derivative of L_fun is bounded by D_val². -/
private lemma L_fun_deriv2_bound (p : P44) (η : ℝ) :
    |iteratedDeriv 2 (L_fun p) η| ≤
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ 2 := by
  rw [L_fun_iteratedDeriv2]
  set h := h5 p.1.1; set g := h5 p.2.1
  set D := D_val h g (p.1.2 + η * h) (p.2.2 + η * g)
  have hD1 : 1 ≤ D := D_val_ge_one _ _ _ _
  calc |2 * h * g| ≤ 2 * ((h ^ 2 + g ^ 2) / 2) := by
        rw [show (2 : ℝ) * h * g = 2 * (h * g) from by ring]
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2)]
        linarith [abs_mul_le_sq_add_sq_div2 h g]
    _ = h ^ 2 + g ^ 2 := by ring
    _ ≤ D := by simp only [D, D_val]; nlinarith [sq_nonneg (p.1.2 + η * h),
        sq_nonneg (p.2.2 + η * g)]
    _ ≤ D ^ 2 := le_self_pow₀ hD1 (by omega)

/-- iteratedDeriv bound for Q_fun at all orders 1 ≤ i ≤ k. -/
private lemma Q_fun_iteratedDeriv_le_D (p : P44) (η : ℝ) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    ‖iteratedDeriv i (Q_fun p) η‖ ≤
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ i := by
  set D := D_val (h5 p.1.1) (h5 p.2.1) (p.1.2 + η * h5 p.1.1)
    (p.2.2 + η * h5 p.2.1)
  have hD1 : 1 ≤ D := D_val_ge_one _ _ _ _
  have hD0 : 0 < D := D_val_pos _ _ _ _
  interval_cases i
  · -- i = 1
    simp only [iteratedDeriv_one, Real.norm_eq_abs]
    calc |deriv (Q_fun p) η| ≤ D := Q_fun_deriv_bound p η
      _ = D ^ 1 := (pow_one D).symm
  · -- i = 2
    rw [Real.norm_eq_abs]; exact Q_fun_deriv2_bound p η
  · -- i = 3
    rw [Q_fun_iteratedDeriv_vanish p 3 le_rfl η]; simp; positivity
  · -- i = 4
    rw [Q_fun_iteratedDeriv_vanish p 4 (by omega) η]; simp; positivity

/-- iteratedDeriv bound for L_fun at all orders 1 ≤ i ≤ k. -/
private lemma L_fun_iteratedDeriv_le_D (p : P44) (η : ℝ) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ 4) :
    ‖iteratedDeriv i (L_fun p) η‖ ≤
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ i := by
  set D := D_val (h5 p.1.1) (h5 p.2.1) (p.1.2 + η * h5 p.1.1)
    (p.2.2 + η * h5 p.2.1)
  have hD1 : 1 ≤ D := D_val_ge_one _ _ _ _
  have hD0 : 0 < D := D_val_pos _ _ _ _
  interval_cases i
  · simp only [iteratedDeriv_one, Real.norm_eq_abs]
    calc |deriv (L_fun p) η| ≤ D := L_fun_deriv_bound p η
      _ = D ^ 1 := (pow_one D).symm
  · rw [Real.norm_eq_abs]; exact L_fun_deriv2_bound p η
  · rw [L_fun_iteratedDeriv_vanish p 3 le_rfl η]; simp; positivity
  · rw [L_fun_iteratedDeriv_vanish p 4 (by omega) η]; simp; positivity

/-- exp(Q(η)) bounds: ‖iteratedDeriv i exp (Q_fun p η)‖ ≤ exp(Q(η)). -/
private lemma exp_iteratedDeriv_bound (y : ℝ) (i : ℕ) :
    ‖iteratedDeriv i Real.exp y‖ = Real.exp y := by
  rw [iteratedDeriv_eq_iterate,
    show deriv^[i] Real.exp y = Real.exp y from
      congr_fun (Real.iter_deriv_exp i) y,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

/-- sin derivatives bounded: ‖iteratedDeriv i sin y‖ ≤ 1. -/
private lemma sin_iteratedDeriv_bound (y : ℝ) (i : ℕ) :
    ‖iteratedDeriv i Real.sin y‖ ≤ 1 := by
  rw [Real.norm_eq_abs]; exact Real.abs_iteratedDeriv_sin_le_one i y

/-- Chain rule bound for exp ∘ Q_fun. -/
private lemma exp_Q_deriv_bound (p : P44) (η : ℝ) (k : ℕ) (hk : k ≤ 4) :
    ‖iteratedDeriv k (fun η => Real.exp (Q_fun p η)) η‖ ≤
    k.factorial * Real.exp (Q_fun p η) *
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ k := by
  have hcomp : (fun η => Real.exp (Q_fun p η)) = Real.exp ∘ Q_fun p := rfl
  rw [hcomp]
  exact norm_iteratedDeriv_comp_le Real.contDiff_exp (Q_fun_contDiff p) η
    (fun i _ => by rw [exp_iteratedDeriv_bound])
    (fun i h1 h2 => Q_fun_iteratedDeriv_le_D p η i h1 (le_trans h2 hk))

/-- Chain rule bound for sin ∘ L_fun. -/
private lemma sin_L_deriv_bound (p : P44) (η : ℝ) (k : ℕ) (hk : k ≤ 4) :
    ‖iteratedDeriv k (fun η => Real.sin (L_fun p η)) η‖ ≤
    k.factorial * 1 *
    D_val (h5 p.1.1) (h5 p.2.1)
      (p.1.2 + η * h5 p.1.1) (p.2.2 + η * h5 p.2.1) ^ k := by
  have hcomp : (fun η => Real.sin (L_fun p η)) = Real.sin ∘ L_fun p := rfl
  rw [hcomp]
  exact norm_iteratedDeriv_comp_le Real.contDiff_sin (L_fun_contDiff p) η
    (fun i _ => sin_iteratedDeriv_bound _ _)
    (fun i h1 h2 => L_fun_iteratedDeriv_le_D p η i h1 (le_trans h2 hk))

set_option maxHeartbeats 400000 in
/-- (a+b)⁴ ≤ 8(a⁴+b⁴) for a,b ≥ 0. -/
private lemma add_pow4_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b),
    sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b)]

set_option maxHeartbeats 6400000 in
/-- Derivative bound for the smooth part via Faà di Bruno + Leibniz.
    For k ≤ 4 and |η| ≤ 2, the k-th derivative of the smooth part is bounded
    by a polynomial in |h5|, |h5| times a Gaussian with halved exponent. -/
private lemma Φ_smooth_deriv_le (k : ℕ) (hk : k ≤ 4) (η : ℝ) (hη : |η| ≤ 2) (p : P44) :
    let h := h5 p.1.1; let g := h5 p.2.1
    let α := p.1.2 + η * h; let β := p.2.2 + η * g
    ‖iteratedDeriv k (Φ_smooth p) η‖ ≤
      (10 ^ 8 : ℝ) * (1 + h ^ 2 + g ^ 2) ^ 10 *
      Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
      Real.exp (-(α ^ 2 + β ^ 2) / 8) := by
  simp only []
  set h := h5 p.1.1; set g := h5 p.2.1
  set α := p.1.2 + η * h; set β := p.2.2 + η * g
  set D := D_val h g α β; set Qη := Q_fun p η
  have hD0 : 0 < D := D_val_pos _ _ _ _
  have hD1 : 1 ≤ D := D_val_ge_one _ _ _ _
  -- Factor Φ_smooth as exp(Q) * sin(L)
  have hΦ_eq : Φ_smooth p =ᶠ[nhds η]
      (fun η => Real.exp (Q_fun p η) * Real.sin (L_fun p η)) := by
    filter_upwards with t; exact Φ_smooth_eq_exp_mul_sin p t
  rw [hΦ_eq.iteratedDeriv_eq k]
  have hexp_cd : ContDiff ℝ ⊤ (fun η => Real.exp (Q_fun p η)) :=
    Real.contDiff_exp.comp (Q_fun_contDiff p)
  have hsin_cd : ContDiff ℝ ⊤ (fun η => Real.sin (L_fun p η)) :=
    Real.contDiff_sin.comp (L_fun_contDiff p)
  -- Part 1: Leibniz + chain rule → ≤ 120 * exp(Qη) * D^4
  have h_each : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedDeriv i (fun η => Real.exp (Q_fun p η)) η‖ *
      ‖iteratedDeriv (k - i) (fun η => Real.sin (L_fun p η)) η‖ ≤
      ↑k.factorial * Real.exp Qη * D ^ k := by
    intro i hi
    have hi' : i ≤ k := Finset.mem_range_succ_iff.mp hi
    have hpow : D ^ i * D ^ (k - i) = D ^ k := by rw [← pow_add]; congr 1; omega
    have hC : ↑(k.choose i) * ↑i.factorial * ↑(k - i).factorial ≤ (↑k.factorial : ℝ) := by
      by_cases hik : i ≤ k
      · exact_mod_cast le_of_eq (Nat.choose_mul_factorial_mul_factorial hik)
      · simp [Nat.choose_eq_zero_of_lt (by omega : k < i)]
    have hexp_i := exp_Q_deriv_bound p η i (le_trans hi' hk)
    have hsin_ki := sin_L_deriv_bound p η (k - i) (by omega)
    calc _ ≤ ↑(k.choose i) * (↑i.factorial * Real.exp Qη * D ^ i) *
          (↑(k - i).factorial * 1 * D ^ (k - i)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_i (Nat.cast_nonneg _))
            hsin_ki (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      _ = (↑(k.choose i) * ↑i.factorial * ↑(k - i).factorial) *
          Real.exp Qη * D ^ k := by rw [← hpow]; ring
      _ ≤ ↑k.factorial * Real.exp Qη * D ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC
            (Real.exp_nonneg _)) (pow_nonneg hD0.le _)
  have h120 : ‖iteratedDeriv k (fun y => Real.exp (Q_fun p y) *
      Real.sin (L_fun p y)) η‖ ≤ 120 * Real.exp Qη * D ^ 4 :=
    calc _ ≤ ∑ _ ∈ Finset.range (k + 1), (↑k.factorial * Real.exp Qη * D ^ k) :=
          le_trans (norm_iteratedDeriv_mul_le hexp_cd hsin_cd η k)
            (Finset.sum_le_sum h_each)
      _ = ↑(k + 1) * ↑k.factorial * Real.exp Qη * D ^ k := by
          simp [Finset.sum_const, Finset.card_range]; ring
      _ ≤ 120 * Real.exp Qη * D ^ k := by
          have : (↑(k + 1) : ℝ) * ↑k.factorial ≤ 120 := by
            interval_cases k <;> simp [Nat.factorial] <;> norm_num
          nlinarith [mul_nonneg (Real.exp_nonneg Qη) (pow_nonneg hD0.le k)]
      _ ≤ 120 * Real.exp Qη * D ^ 4 := by
          have : D ^ k ≤ D ^ 4 := by
            interval_cases k <;>
              nlinarith [pow_nonneg hD0.le 1, pow_nonneg hD0.le 2, pow_nonneg hD0.le 3]
          exact mul_le_mul_of_nonneg_left this
            (mul_nonneg (by norm_num) (Real.exp_nonneg _))
  -- Part 2: polynomial absorption
  set s := α ^ 2 + β ^ 2; set t := 1 + h ^ 2 + g ^ 2
  have hs : 0 ≤ s := by positivity
  have ht1 : 1 ≤ t := by simp only [t]; nlinarith [sq_nonneg h, sq_nonneg g]
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
  have hQ_le : Real.exp Qη ≤ Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
      Real.exp (-(s / 8)) * Real.exp (-(s / 8)) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    simp only [Qη, Q_fun, s]; nlinarith [sq_nonneg p.1.1, sq_nonneg p.2.1]
  have hD_ts : D = t + s := by simp only [D, D_val, t, s]; ring
  have h_D4 : D ^ 4 * Real.exp (-(s / 8)) ≤ 8 * 98305 * t ^ 10 := by
    have h1 := pow4_mul_exp_neg_div8_le s hs
    have h2 := Real.exp_le_one_iff.mpr (show -(s / 8) ≤ 0 by linarith)
    have h3 := add_pow4_le t s ht0 hs
    have h4 : t ^ 4 ≤ t ^ 10 := by
      have h41 : 1 ≤ t ^ 4 := by nlinarith [sq_nonneg (t - 1), sq_nonneg t]
      have h46 : 1 ≤ t ^ 6 := by
        have := sq_nonneg (t ^ 2 - 1); have := sq_nonneg (t ^ 2)
        have := pow_nonneg ht0 2; nlinarith
      nlinarith
    have hexp_s_nn := Real.exp_nonneg (-(s / 8))
    have ht4_nn := pow_nonneg ht0 4
    -- (t+s)^4 * exp ≤ 8*(t^4+s^4) * exp = 8*(t^4*exp + s^4*exp)
    -- ≤ 8*(t^4 + 98304) ≤ 8*98305*t^4 ≤ 8*98305*t^10
    have step1 : (t + s) ^ 4 * Real.exp (-(s / 8)) ≤
        8 * (t ^ 4 + s ^ 4) * Real.exp (-(s / 8)) := by nlinarith
    have step2 : t ^ 4 * Real.exp (-(s / 8)) ≤ t ^ 4 := by nlinarith
    have step3 : 8 * (t ^ 4 + s ^ 4) * Real.exp (-(s / 8)) ≤
        8 * (t ^ 4 + 98304) := by
      have : 8 * (t ^ 4 + s ^ 4) * Real.exp (-(s / 8)) =
        8 * t ^ 4 * Real.exp (-(s / 8)) + 8 * (s ^ 4 * Real.exp (-(s / 8))) := by ring
      linarith
    have ht4_pos : 1 ≤ t ^ 4 := by
      have : (1:ℝ) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by positivity) ht1 4
      simpa using this
    have step4 : 8 * (t ^ 4 + 98304) ≤ 8 * 98305 * t ^ 4 := by linarith
    rw [hD_ts]; linarith [h4]
  have hexp_xy := Real.exp_nonneg (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8)
  have hexp_s := Real.exp_nonneg (-(s / 8))
  -- Final assembly: replace exp(Qη) with split form, then absorb D^4 * exp(-s/8)
  calc ‖iteratedDeriv k (fun y => Real.exp (Q_fun p y) *
          Real.sin (L_fun p y)) η‖
      ≤ 120 * Real.exp Qη * D ^ 4 := h120
    _ ≤ 120 * (Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
          Real.exp (-(s / 8)) * Real.exp (-(s / 8))) * D ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQ_le (by norm_num))
          (pow_nonneg hD0.le _)
    _ = 120 * Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
        Real.exp (-(s / 8)) * (D ^ 4 * Real.exp (-(s / 8))) := by ring
    _ ≤ 120 * Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
        Real.exp (-(s / 8)) * (8 * 98305 * t ^ 10) :=
        mul_le_mul_of_nonneg_left h_D4
          (mul_nonneg (mul_nonneg (by norm_num) hexp_xy) hexp_s)
    _ = (120 * 8 * 98305) * (t ^ 10 *
        Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) * Real.exp (-(s / 8))) := by ring
    _ ≤ (10 : ℝ) ^ 8 * (t ^ 10 *
        Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) * Real.exp (-(s / 8))) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (mul_nonneg (pow_nonneg ht0 10) hexp_xy) hexp_s)
    _ = (10 : ℝ) ^ 8 * (1 + h ^ 2 + g ^ 2) ^ 10 *
        Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
        Real.exp (-(α ^ 2 + β ^ 2) / 8) := by
        simp only [t, s]; ring

/-! ### Helpers for Φ_bound_integrable -/

private noncomputable def C₀ : ℝ := ∫ w : ℝ, Real.exp (-(1 / 8 : ℝ) * w ^ 2)

private def φ_maj (K : ℝ) (v : ℝ) : ℝ :=
  (Icc 0 K).indicator (fun _ => (1 : ℝ)) v + Real.exp (-(1 / 8 : ℝ) * (v - K) ^ 2)

private lemma φ_maj_integrable (K : ℝ) : Integrable (φ_maj K) volume := by
  unfold φ_maj
  exact (IntegrableOn.integrable_indicator
    (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc).add
    ((integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 8 by positivity)).comp_sub_right K)

private lemma ind_φ_env_le_φ_maj (v g : ℝ) :
    (if 0 < v then (1 : ℝ) else 0) * φ_env v g ≤ φ_maj (2 * |g|) v := by
  set K := 2 * |g|
  by_cases hv : 0 < v
  · simp only [hv, ite_true, one_mul]; unfold φ_maj
    by_cases hv2 : v ≤ K
    · calc φ_env v g ≤ 1 := φ_env_le_one v g
        _ = (Icc 0 K).indicator (fun _ => (1 : ℝ)) v := by
            simp [indicator, mem_Icc, hv.le, hv2]
        _ ≤ _ := le_add_of_nonneg_right (Real.exp_nonneg _)
    · push_neg at hv2
      have : φ_env v g = Real.exp (-(1 / 8) * (v - K) ^ 2) := by
        unfold φ_env; rw [max_eq_right (by linarith)]; congr 1; ring
      rw [this]; exact le_add_of_nonneg_left (indicator_nonneg (fun _ _ => zero_le_one) v)
  · push_neg at hv
    simp only [show ¬(0 < v) from not_lt.mpr hv, ite_false, zero_mul]; unfold φ_maj
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) v) (Real.exp_nonneg _)

private lemma ind_φ_env_integrable (g : ℝ) :
    Integrable (fun v : ℝ => (if 0 < v then (1 : ℝ) else 0) * φ_env v g) volume :=
  (φ_maj_integrable (2 * |g|)).mono'
    ((Measurable.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const measurable_const |>.mul
      (show Continuous (fun v => φ_env v g) by unfold φ_env; fun_prop).measurable
    ).aestronglyMeasurable)
    (ae_of_all _ fun v => by
      rw [Real.norm_of_nonneg (mul_nonneg (by split_ifs <;> positivity) (φ_env_nonneg v g))]
      exact ind_φ_env_le_φ_maj v g)

private lemma pow_mul_gauss_le' (N : ℕ) {b : ℝ} (hb : 0 < b) (y : ℝ) :
    y ^ (2 * N) * Real.exp (-b * y ^ 2) ≤
    ↑(N.factorial) * (2 / b) ^ N * Real.exp (-(b / 2) * y ^ 2) := by
  have hby : 0 ≤ b / 2 * y ^ 2 := by positivity
  have htaylor := pow_div_factorial_le_exp (b / 2 * y ^ 2) hby N
  have hfact_pos : (0 : ℝ) < ↑(N.factorial) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hbN : (0 : ℝ) < (b / 2) ^ N := by positivity
  rw [show (b / 2 * y ^ 2) ^ N = (b / 2) ^ N * y ^ (2 * N) from by
    rw [mul_pow, ← pow_mul]] at htaylor
  rw [show ↑(N.factorial) * (2 / b) ^ N = ↑(N.factorial) / (b / 2) ^ N from by
    rw [div_eq_mul_inv]; congr 1; rw [← inv_pow]; congr 1; field_simp]
  rw [div_mul_eq_mul_div, le_div_iff₀ hbN]
  have key : (b / 2) ^ N * y ^ (2 * N) ≤ ↑(N.factorial) * Real.exp (b / 2 * y ^ 2) := by
    have h := mul_le_mul_of_nonneg_right htaylor hfact_pos.le
    rw [div_mul_cancel₀ _ hfact_pos.ne'] at h; linarith
  calc y ^ (2 * N) * Real.exp (-b * y ^ 2) * (b / 2) ^ N
      = (b / 2) ^ N * y ^ (2 * N) * Real.exp (-b * y ^ 2) := by ring
    _ ≤ ↑(N.factorial) * Real.exp (b / 2 * y ^ 2) * Real.exp (-b * y ^ 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_nonneg _)
    _ = ↑(N.factorial) * (Real.exp (b / 2 * y ^ 2) * Real.exp (-b * y ^ 2)) := by ring
    _ = ↑(N.factorial) * Real.exp (-(b / 2) * y ^ 2) := by
        congr 1; rw [← Real.exp_add]; congr 1; ring

private lemma even_pow_mul_gauss_integrable (N : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ (2 * N) * Real.exp (-b * x ^ 2)) volume := by
  have hnn : ∀ x : ℝ, 0 ≤ x ^ (2 * N) * Real.exp (-b * x ^ 2) := fun x =>
    mul_nonneg (by rw [show 2 * N = N + N from by omega]; exact Even.pow_nonneg ⟨N, rfl⟩ x)
      (exp_nonneg _)
  exact (integrable_exp_neg_mul_sq (show (0 : ℝ) < b / 2 by linarith) |>.const_mul
    (↑(N.factorial) * (2 / b) ^ N)).mono'
    ((by fun_prop : Measurable (fun x : ℝ => x ^ (2 * N) * Real.exp (-b * x ^ 2))
      ).aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [norm_of_nonneg (hnn x)]; exact pow_mul_gauss_le' N hb x)

/-! ### Helpers for Φ_factor_integrable -/

private lemma aux_ineq (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    s + s ^ n ≤ 1 + s ^ n * s := by
  rcases le_or_gt s 1 with h | h
  · have hsn : s ^ n ≤ 1 := by
      calc s ^ n ≤ 1 ^ n := pow_le_pow_left₀ hs h n
        _ = 1 := one_pow n
    nlinarith [mul_le_mul_of_nonneg_right h
      (show 0 ≤ 1 - s ^ n by linarith)]
  · have hsn : 1 ≤ s ^ n := by
      calc 1 = 1 ^ n := (one_pow n).symm
        _ ≤ s ^ n := pow_le_pow_left₀ (by linarith) h.le n
    nlinarith [mul_le_mul_of_nonneg_right h.le
      (show 0 ≤ s ^ n - 1 by linarith)]

private lemma one_add_pow_le (s : ℝ) (hs : 0 ≤ s) (N : ℕ) :
    (1 + s) ^ N ≤ 2 ^ N * (1 + s ^ N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ]
    have key : (1 + s ^ n) * (1 + s) ≤ 2 * (1 + s ^ n * s) := by
      have := aux_ineq s hs n; nlinarith
    calc (1 + s) ^ n * (1 + s)
        ≤ 2 ^ n * (1 + s ^ n) * (1 + s) := by nlinarith
      _ = 2 ^ n * ((1 + s ^ n) * (1 + s)) := by ring
      _ ≤ 2 ^ n * (2 * (1 + s ^ n * s)) := by
          nlinarith [show (0:ℝ) ≤ 2 ^ n by positivity]
      _ = 2 ^ n * 2 * (1 + s ^ n * s) := by ring

private lemma one_add_sq_pow_le (t : ℝ) (N : ℕ) :
    (1 + t ^ 2) ^ N ≤ 2 ^ N * (1 + t ^ (2 * N)) := by
  have h := one_add_pow_le (t ^ 2) (sq_nonneg t) N
  rwa [← pow_mul] at h

private lemma one_add_sq_pow_mul_gauss_integrable (N : ℕ) {b : ℝ}
    (hb : 0 < b) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ N *
      Real.exp (-b * x ^ 2)) volume := by
  exact (((integrable_exp_neg_mul_sq hb).const_mul ((2:ℝ) ^ N)).add
    ((even_pow_mul_gauss_integrable N hb).const_mul ((2:ℝ) ^ N))).mono'
    ((show Continuous (fun x : ℝ => (1 + x ^ 2) ^ N *
      rexp (-b * x ^ 2)) by fun_prop).measurable.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_of_nonneg (mul_nonneg (by positivity) (exp_nonneg _))]
      simp only [Pi.add_apply]
      nlinarith [one_add_sq_pow_le x N, exp_nonneg (-b * x ^ 2)])

private lemma integral_φ_maj_eq (K : ℝ) (hK : 0 ≤ K) :
    ∫ y, φ_maj K y = K + C₀ := by
  unfold φ_maj
  rw [integral_add
    (IntegrableOn.integrable_indicator
      (integrableOn_const (hs := measure_Icc_lt_top.ne))
      measurableSet_Icc)
    ((integrable_exp_neg_mul_sq (show (0:ℝ) < 1/8 by positivity)
      ).comp_sub_right K)]
  congr 1
  · rw [integral_indicator measurableSet_Icc]; simp [hK]
  · exact integral_sub_right_eq_self
      (fun w => Real.exp (-(1/8 : ℝ) * w ^ 2)) K

private lemma ind_φ_env_integral_le (g : ℝ) :
    ∫ v, (if 0 < v then (1 : ℝ) else 0) * φ_env v g ≤
      2 * |g| + C₀ := by
  calc ∫ v, (if 0 < v then (1 : ℝ) else 0) * φ_env v g
      ≤ ∫ v, φ_maj (2 * |g|) v := by
        apply integral_mono_of_nonneg
          (ae_of_all _ fun v => mul_nonneg
            (by split_ifs <;> positivity) (φ_env_nonneg v g))
          (φ_maj_integrable _)
          (ae_of_all _ fun v => ind_φ_env_le_φ_maj v g)
    _ = 2 * |g| + C₀ := integral_φ_maj_eq _ (by positivity)

/-- `h5_unnorm(x)²` is bounded by a power of `1 + x²`. -/
private lemma h5_unnorm_sq_le (x : ℝ) :
    h5_unnorm x ^ 2 ≤ 1600 * (1 + x ^ 2) ^ 5 := by
  unfold h5_unnorm
  nlinarith [sq_nonneg x, sq_nonneg (x^2), sq_nonneg (x^3),
    sq_nonneg (x^4), sq_nonneg (x^5),
    sq_nonneg (x*x^2 - 1), sq_nonneg (x^2 - 1),
    sq_nonneg (x^3 - 1)]

private noncomputable def Φ_factor (q : ℝ × ℝ) : ℝ :=
  (1 + (h5 q.1) ^ 2) ^ 10 * Real.exp (-(q.1 ^ 2) / 8) *
  ((if 0 < q.2 then (1 : ℝ) else 0) * φ_env q.2 (h5 q.1))

private lemma Φ_factor_nonneg (q : ℝ × ℝ) : 0 ≤ Φ_factor q := by
  unfold Φ_factor
  exact mul_nonneg (mul_nonneg (by positivity) (exp_nonneg _))
    (mul_nonneg (by split_ifs <;> positivity) (φ_env_nonneg _ _))

private lemma Φ_bound_le_factor_prod (p : P44) :
    Φ_bound p ≤ (10 ^ 10 : ℝ) * Φ_factor p.1 * Φ_factor p.2 := by
  unfold Φ_bound Φ_factor; simp only []
  have hfact : (1 + h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) ^ 10 ≤
      (1 + h5 p.1.1 ^ 2) ^ 10 * (1 + h5 p.2.1 ^ 2) ^ 10 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [sq_nonneg (h5 p.1.1), sq_nonneg (h5 p.2.1)]) 10
  have hexp : Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) =
      Real.exp (-(p.1.1 ^ 2) / 8) * Real.exp (-(p.2.1 ^ 2) / 8) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc ((10 ^ 10 * if 0 < p.1.2 then 1 else 0) *
        if 0 < p.2.2 then 1 else 0) *
        (1 + h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) ^ 10 *
        (rexp (-p.1.1 ^ 2 / 8) * rexp (-p.2.1 ^ 2 / 8)) *
        φ_env p.1.2 (h5 p.1.1) * φ_env p.2.2 (h5 p.2.1)
      ≤ ((10 ^ 10 * if 0 < p.1.2 then 1 else 0) *
        if 0 < p.2.2 then 1 else 0) *
        ((1 + h5 p.1.1 ^ 2) ^ 10 *
          (1 + h5 p.2.1 ^ 2) ^ 10) *
        (rexp (-p.1.1 ^ 2 / 8) * rexp (-p.2.1 ^ 2 / 8)) *
        φ_env p.1.2 (h5 p.1.1) *
        φ_env p.2.2 (h5 p.2.1) := by
        gcongr
        · exact φ_env_nonneg _ _
        · exact φ_env_nonneg _ _
    _ = 10 ^ 10 *
        ((1 + h5 p.1.1 ^ 2) ^ 10 * rexp (-p.1.1 ^ 2 / 8) *
          ((if 0 < p.1.2 then 1 else 0) *
            φ_env p.1.2 (h5 p.1.1))) *
        ((1 + h5 p.2.1 ^ 2) ^ 10 * rexp (-p.2.1 ^ 2 / 8) *
          ((if 0 < p.2.2 then 1 else 0) *
            φ_env p.2.2 (h5 p.2.1))) := by ring

private lemma Φ_factor_measurable : Measurable (fun q : ℝ × ℝ => Φ_factor q) := by
  unfold Φ_factor φ_env
  apply Measurable.mul
  · apply Measurable.mul
    · exact (show Continuous (fun q : ℝ × ℝ => (1 + (h5 q.1) ^ 2) ^ 10) by fun_prop).measurable
    · exact (show Continuous (fun q : ℝ × ℝ => Real.exp (-(q.1 ^ 2) / 8)) by fun_prop).measurable
  · exact (Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      measurable_const measurable_const).mul
      (show Continuous (fun q : ℝ × ℝ => Real.exp (-(max 0 (q.2 - 2 * |h5 q.1|)) ^ 2 / 8)) by
        fun_prop).measurable

private lemma Φ_factor_integrable : Integrable Φ_factor (volume : Measure (ℝ × ℝ)) := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
  rw [integrable_prod_iff Φ_factor_measurable.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x₁ => ?_, ?_⟩
  · -- Inner: Φ_factor(x₁, ·) integrable in u
    show Integrable (fun u => Φ_factor (x₁, u)) volume
    unfold Φ_factor; simp only []
    exact ((ind_φ_env_integrable (h5 x₁)).const_mul
      ((1 + h5 x₁ ^ 2) ^ 10 * Real.exp (-(x₁ ^ 2) / 8))).congr
      (ae_of_all _ fun u => by ring)
  · -- Outer: ∫ ‖Φ_factor(x,·)‖ du is integrable as a function of x
    -- Bound h5(x)² using h5_unnorm_sq_le
    have h_h5_sq_le : ∀ x : ℝ,
        h5 x ^ 2 ≤ 1600 / h5_norm_const ^ 2 * (1 + x ^ 2) ^ 5 := by
      intro x; unfold h5
      have hD : (0:ℝ) < h5_norm_const := by unfold h5_norm_const; positivity
      have hD2 : (0:ℝ) < h5_norm_const ^ 2 := sq_pos_of_pos hD
      rw [div_pow, show (1600 : ℝ) / h5_norm_const ^ 2 * (1 + x ^ 2) ^ 5 =
        1600 * (1 + x ^ 2) ^ 5 / h5_norm_const ^ 2 from by ring]
      exact div_le_div_of_nonneg_right (h5_unnorm_sq_le x) hD2.le
    set A := 1600 / h5_norm_const ^ 2
    -- (1+h5(x)²) ≤ (1+A)*(1+x²)^5
    have h_one_add : ∀ x : ℝ,
        1 + h5 x ^ 2 ≤ (1 + A) * (1 + x ^ 2) ^ 5 := by
      intro x
      have : (1:ℝ) ≤ (1 + x ^ 2) ^ 5 := by
        calc (1:ℝ) = 1 ^ 5 := by norm_num
          _ ≤ (1 + x ^ 2) ^ 5 :=
            pow_le_pow_left₀ (by linarith) (by nlinarith [sq_nonneg x]) 5
      nlinarith [h_h5_sq_le x]
    -- (1+h5(x)²)^10 ≤ (1+A)^10*(1+x²)^50
    have h_pow10 : ∀ x : ℝ,
        (1 + h5 x ^ 2) ^ 10 ≤ (1 + A) ^ 10 * (1 + x ^ 2) ^ 50 := by
      intro x
      calc (1 + h5 x ^ 2) ^ 10
          ≤ ((1 + A) * (1 + x ^ 2) ^ 5) ^ 10 :=
            pow_le_pow_left₀ (by positivity) (h_one_add x) 10
        _ = (1 + A) ^ 10 * ((1 + x ^ 2) ^ 5) ^ 10 := mul_pow _ _ 10
        _ = (1 + A) ^ 10 * (1 + x ^ 2) ^ 50 := by
            congr 1; rw [← pow_mul]
    -- inner integral bound: ∫ ind*φ_env ≤ 2|h5(x)|+C₀ ≤ (1+C₀)*(1+h5(x)²)
    have h_inner_le : ∀ x : ℝ,
        ∫ y, (if 0 < y then (1:ℝ) else 0) * φ_env y (h5 x) ≤
        (1 + C₀) * (1 + h5 x ^ 2) := by
      intro x
      have h1 := ind_φ_env_integral_le (h5 x)
      have h2 : 2 * |h5 x| ≤ 1 + h5 x ^ 2 := by
        nlinarith [sq_abs (h5 x), sq_nonneg (|h5 x| - 1)]
      have hC₀_nn : 0 ≤ C₀ := integral_nonneg fun w => exp_nonneg _
      nlinarith [sq_nonneg (h5 x)]
    -- Combine: (1+h5(x)²)^10 * (1+C₀)*(1+h5(x)²) ≤ (1+C₀)*(1+A)^11*(1+x²)^55
    have h_pow11 : ∀ x : ℝ,
        (1 + h5 x ^ 2) ^ 10 * ((1 + C₀) * (1 + h5 x ^ 2)) ≤
        (1 + C₀) * ((1 + A) ^ 11 * (1 + x ^ 2) ^ 55) := by
      intro x
      have h11 : (1 + h5 x ^ 2) ^ 11 ≤ (1 + A) ^ 11 * (1 + x ^ 2) ^ 55 := by
        calc (1 + h5 x ^ 2) ^ 11
            ≤ ((1 + A) * (1 + x ^ 2) ^ 5) ^ 11 :=
              pow_le_pow_left₀ (by positivity) (h_one_add x) 11
          _ = (1 + A) ^ 11 * (1 + x ^ 2) ^ 55 := by
              rw [mul_pow]; congr 1; rw [← pow_mul]
      have hC₀_nn : 0 ≤ C₀ := integral_nonneg fun w => exp_nonneg _
      rw [show (1 + h5 x ^ 2) ^ 10 * ((1 + C₀) * (1 + h5 x ^ 2)) =
        (1 + C₀) * (1 + h5 x ^ 2) ^ 11 from by ring]
      exact mul_le_mul_of_nonneg_left h11 (by linarith)
    -- The majorant: M * (1+x²)^55 * exp(-x²/8)
    set M := (1 + C₀) * (1 + A) ^ 11
    -- Use Integrable.mono'
    have h_inner_nn : ∀ x : ℝ,
        0 ≤ ∫ y, (if 0 < y then (1:ℝ) else 0) * φ_env y (h5 x) :=
      fun x => integral_nonneg fun y => mul_nonneg
        (by split_ifs <;> positivity) (φ_env_nonneg y (h5 x))
    -- Rewrite ∫ ‖Φ_factor(x,·)‖ = (1+h5(x)²)^10 * exp(-x²/8) * ∫ ind*φ_env
    have h_eq : ∀ x₁ : ℝ, ∫ y, ‖Φ_factor (x₁, y)‖ =
        (1 + h5 x₁ ^ 2) ^ 10 * rexp (-(x₁ ^ 2) / 8) *
        (∫ y, (if 0 < y then (1:ℝ) else 0) * φ_env y (h5 x₁)) := by
      intro x₁
      simp_rw [show ∀ y : ℝ, ‖Φ_factor (x₁, y)‖ = Φ_factor (x₁, y) from
        fun y => Real.norm_of_nonneg (Φ_factor_nonneg (x₁, y))]
      simp_rw [Φ_factor]; rw [integral_const_mul]
    -- The pointwise bound
    have h_pointwise : ∀ x : ℝ,
        ∫ y, ‖Φ_factor (x, y)‖ ≤
        M * ((1 + x ^ 2) ^ 55 * rexp (-(1/8) * x ^ 2)) := by
      intro x
      rw [h_eq]
      have h1 := h_pow10 x
      have h2 := h_inner_le x
      have h3 := h_inner_nn x
      have hpow_nn : (0:ℝ) ≤ (1 + h5 x ^ 2) ^ 10 := by positivity
      have hexp_nn : (0:ℝ) ≤ rexp (-(x ^ 2) / 8) := exp_nonneg _
      have h4 : (1 + h5 x ^ 2) ^ 10 * rexp (-(x ^ 2) / 8) *
          ∫ y, (if 0 < y then (1:ℝ) else 0) * φ_env y (h5 x) ≤
          (1 + h5 x ^ 2) ^ 10 * rexp (-(x ^ 2) / 8) *
          ((1 + C₀) * (1 + h5 x ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hpow_nn hexp_nn)
      have h5' : (1 + h5 x ^ 2) ^ 10 * rexp (-(x ^ 2) / 8) *
          ((1 + C₀) * (1 + h5 x ^ 2)) =
          rexp (-(x ^ 2) / 8) *
          ((1 + h5 x ^ 2) ^ 10 * ((1 + C₀) * (1 + h5 x ^ 2))) := by ring
      have h6 := h_pow11 x
      calc (1 + h5 x ^ 2) ^ 10 * rexp (-(x ^ 2) / 8) *
              ∫ y, (if 0 < y then (1:ℝ) else 0) * φ_env y (h5 x)
          ≤ rexp (-(x ^ 2) / 8) *
            ((1 + h5 x ^ 2) ^ 10 * ((1 + C₀) * (1 + h5 x ^ 2))) := by linarith
        _ ≤ rexp (-(x ^ 2) / 8) *
            ((1 + C₀) * ((1 + A) ^ 11 * (1 + x ^ 2) ^ 55)) :=
            mul_le_mul_of_nonneg_left h6 hexp_nn
        _ = M * ((1 + x ^ 2) ^ 55 * rexp (-(1/8) * x ^ 2)) := by
            have : -(x ^ 2) / 8 = -(1/8 : ℝ) * x ^ 2 := by ring
            rw [this]; ring
    -- Apply Integrable.mono'
    exact ((one_add_sq_pow_mul_gauss_integrable 55
      (show (0:ℝ) < 1/8 by positivity)).const_mul M).mono'
      (Φ_factor_measurable.norm.aestronglyMeasurable.integral_prod_right')
      (ae_of_all _ fun x => by
        rw [norm_of_nonneg (integral_nonneg fun y =>
          norm_nonneg (Φ_factor (x, y)))]
        exact h_pointwise x)

private lemma Φ_bound_measurable : Measurable Φ_bound := by
  unfold Φ_bound φ_env; simp only []
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.mul
          · exact (measurable_const.mul (Measurable.ite
              (measurableSet_lt measurable_const measurable_fst.snd)
              measurable_const measurable_const))
          · exact measurable_const.ite
              (measurableSet_lt measurable_const measurable_snd.snd) measurable_const
        · exact (show Continuous (fun p : P44 =>
            (1 + (h5 p.1.1) ^ 2 + (h5 p.2.1) ^ 2) ^ 10) by fun_prop).measurable
      · exact (show Continuous (fun p : P44 =>
          Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8)) by fun_prop).measurable
    · exact (show Continuous (fun p : P44 =>
        Real.exp (-(max 0 (p.1.2 - 2 * |h5 p.1.1|)) ^ 2 / 8)) by fun_prop).measurable
  · exact (show Continuous (fun p : P44 =>
      Real.exp (-(max 0 (p.2.2 - 2 * |h5 p.2.1|)) ^ 2 / 8)) by fun_prop).measurable

/-- Integrability of the bound function Φ_bound on (ℝ²)². -/
private lemma Φ_bound_integrable : Integrable Φ_bound volume := by
  have hprod : Integrable (fun p : P44 =>
      (10 ^ 10 : ℝ) * Φ_factor p.1 * Φ_factor p.2) volume := by
    rw [show (volume : Measure P44) = volume.prod volume from rfl]
    exact (Φ_factor_integrable.mul_prod Φ_factor_integrable |>.const_mul
      (10 ^ 10 : ℝ)).congr (ae_of_all _ fun p => by ring)
  exact hprod.mono' Φ_bound_measurable.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (Φ_bound_nonneg p)]; exact Φ_bound_le_factor_prod p)

/-- Uniform Gaussian domination: for |η| ≤ 2, all derivatives of Phi_integrand up to
    order 4 are bounded by an integrable function independent of η. -/
lemma Phi_integrand_dominated :
    ∃ (bound : P44 → ℝ), Integrable bound volume ∧
      ∀ k : ℕ, k ≤ 4 →
        ∀ η : ℝ, |η| ≤ 2 →
          ∀ p : P44, ‖iteratedDeriv k (Phi_integrand · p) η‖ ≤ bound p := by
  refine ⟨Φ_bound, Φ_bound_integrable, fun k hk η hη p => ?_⟩
  -- Factor out the indicators
  have hfact : (fun η' => Phi_integrand η' p) = fun η' =>
      (4 * ((if 0 < p.1.2 then (1:ℝ) else 0) * (if 0 < p.2.2 then (1:ℝ) else 0))) *
      Φ_smooth p η' := by
    ext η'; rw [Phi_integrand_eq_ind_mul_smooth]; ring
  rw [hfact, iteratedDeriv_const_mul _
    ((Φ_smooth_contDiff p).contDiffAt.of_le le_top)]
  simp only [Real.norm_eq_abs, abs_mul]
  -- When either indicator is 0, the whole thing is 0 ≤ Φ_bound p
  by_cases hu : 0 < p.1.2 <;> by_cases hv : 0 < p.2.2
  · -- Both u > 0, v > 0
    simp only [hu, hv, ite_true, one_mul, abs_one]
    -- Bound |iteratedDeriv k (Φ_smooth p) η| using Φ_smooth_deriv_le
    have hsm := Φ_smooth_deriv_le k hk η hη p
    rw [Real.norm_eq_abs] at hsm
    -- Goal: |4| * 1 * |iteratedDeriv k (Φ_smooth p) η| ≤ Φ_bound p
    -- First bound |4| * 1 * |iteratedDeriv| ≤ 4 * smooth_bound
    have h4pos : |4| = (4 : ℝ) := by norm_num
    rw [h4pos, mul_one]
    -- Need: 4 * |iteratedDeriv k (Φ_smooth p) η| ≤ Φ_bound p
    -- From hsm: |iteratedDeriv| ≤ 10^8 * ...
    -- So 4 * |iteratedDeriv| ≤ 4 * 10^8 * ...
    calc 4 * |iteratedDeriv k (Φ_smooth p) η|
        ≤ 4 * (10 ^ 8 * (1 + h5 p.1.1 ^ 2 + h5 p.2.1 ^ 2) ^ 10 *
            rexp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
            rexp (-((p.1.2 + η * h5 p.1.1) ^ 2 +
              (p.2.2 + η * h5 p.2.1) ^ 2) / 8)) := by gcongr
      _ ≤ Φ_bound p := by
          -- 4 * 10^8 * ... ≤ 10^10 * ... = Φ_bound
          unfold Φ_bound; simp only [hu, hv, ite_true, one_mul]
          -- exp(-(α²+β²)/8) ≤ φ_env * φ_env
          have henv_u := φ_env_dominates hu hη (h := h5 p.1.1)
          have henv_v := φ_env_dominates hv hη (h := h5 p.2.1)
          have hsplit : Real.exp (-((p.1.2 + η * h5 p.1.1) ^ 2 +
              (p.2.2 + η * h5 p.2.1) ^ 2) / 8) ≤
            φ_env p.1.2 (h5 p.1.1) * φ_env p.2.2 (h5 p.2.1) := by
            calc Real.exp (-((p.1.2 + η * h5 p.1.1) ^ 2 +
                    (p.2.2 + η * h5 p.2.1) ^ 2) / 8)
                = Real.exp (-(p.1.2 + η * h5 p.1.1) ^ 2 / 8) *
                  Real.exp (-(p.2.2 + η * h5 p.2.1) ^ 2 / 8) := by
                    rw [← Real.exp_add]; congr 1; ring
              _ ≤ φ_env p.1.2 (h5 p.1.1) * φ_env p.2.2 (h5 p.2.1) :=
                  mul_le_mul henv_u henv_v (Real.exp_nonneg _) (φ_env_nonneg _ _)
          have hP : (0:ℝ) ≤ (1 + (h5 p.1.1) ^ 2 + (h5 p.2.1) ^ 2) ^ 10 := by positivity
          have hE : (0:ℝ) ≤ Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) := Real.exp_nonneg _
          have hφ1 := φ_env_nonneg p.1.2 (h5 p.1.1)
          have hφ2 := φ_env_nonneg p.2.2 (h5 p.2.1)
          have h1 : 4 * (10:ℝ) ^ 8 * (1 + (h5 p.1.1) ^ 2 + (h5 p.2.1) ^ 2) ^ 10 *
              Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
              Real.exp (-((p.1.2 + η * h5 p.1.1) ^ 2 +
                (p.2.2 + η * h5 p.2.1) ^ 2) / 8)
            ≤ 4 * (10:ℝ) ^ 8 * (1 + (h5 p.1.1) ^ 2 + (h5 p.2.1) ^ 2) ^ 10 *
              Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
              (φ_env p.1.2 (h5 p.1.1) * φ_env p.2.2 (h5 p.2.1)) := by gcongr
          -- 4 * 10^8 ≤ 10^10
          linarith [show (0:ℝ) ≤ ((10:ℝ) ^ 10 - 4 * (10:ℝ) ^ 8) *
            ((1 + (h5 p.1.1) ^ 2 + (h5 p.2.1) ^ 2) ^ 10 *
             Real.exp (-(p.1.1 ^ 2 + p.2.1 ^ 2) / 8) *
             (φ_env p.1.2 (h5 p.1.1) * φ_env p.2.2 (h5 p.2.1))) from
             mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hP hE) (mul_nonneg hφ1 hφ2))]
  · -- u > 0, v ≤ 0: indicator is 0
    simp only [hu, show ¬(0 < p.2.2) from hv, ite_true, ite_false, mul_zero, abs_zero,
               zero_mul, Φ_bound_nonneg]
  · simp only [show ¬(0 < p.1.2) from hu, ite_false, mul_zero, zero_mul, abs_zero,
               Φ_bound_nonneg]
  · simp only [show ¬(0 < p.1.2) from hu, ite_false, mul_zero, zero_mul, abs_zero,
               Φ_bound_nonneg]

/-- Measurability of each derivative layer.
    Proof by induction: the base case is explicit measurability;
    the inductive step uses that iteratedDeriv (n+1) is the pointwise limit
    of difference quotients of iteratedDeriv n (each measurable by IH). -/
lemma Phi_integrand_deriv_aestronglyMeasurable (k : ℕ) (η : ℝ) :
    AEStronglyMeasurable (fun p : P44 => iteratedDeriv k (Phi_integrand · p) η) volume := by
  -- Prove the stronger StronglyMeasurable by induction on k, universally in η
  suffices h : ∀ (k : ℕ) (η : ℝ),
      StronglyMeasurable (fun p : P44 => iteratedDeriv k (fun x => Phi_integrand x p) η) by
    exact (h k η).aestronglyMeasurable
  intro k
  induction k with
  | zero =>
    intro η
    simp only [iteratedDeriv_zero]
    exact (Phi_integrand_measurable η).stronglyMeasurable
  | succ n ih =>
    intro η
    -- The (n+1)-th derivative is the pointwise limit of difference quotients
    -- of the n-th derivative, and StronglyMeasurable is closed under limits.
    let f : ℕ → P44 → ℝ := fun m p =>
      (↑(m + 1) : ℝ) * (iteratedDeriv n (fun x => Phi_integrand x p) (η + (↑(m + 1) : ℝ)⁻¹) -
        iteratedDeriv n (fun x => Phi_integrand x p) η)
    let g : P44 → ℝ := fun p => iteratedDeriv (n + 1) (fun x => Phi_integrand x p) η
    -- Each f m is StronglyMeasurable by IH
    have hf_meas : ∀ m, StronglyMeasurable (f m) := by
      intro m
      show StronglyMeasurable (fun p =>
        (↑(m + 1) : ℝ) * (iteratedDeriv n (fun x => Phi_integrand x p) (η + (↑(m + 1) : ℝ)⁻¹) -
          iteratedDeriv n (fun x => Phi_integrand x p) η))
      exact ((ih (η + (↑(m + 1) : ℝ)⁻¹)).sub (ih η)).const_smul ((m + 1 : ℕ) : ℝ)
    -- Pointwise convergence: f m p → g p for each p
    have hf_lim : ∀ p, Tendsto (fun m => f m p) atTop (nhds (g p)) := by
      intro p
      -- The n-th iterated derivative of the C^∞ function is differentiable
      have hcont := Phi_integrand_contDiff_eta p
      have hdiff : Differentiable ℝ (iteratedDeriv n (fun x => Phi_integrand x p)) :=
        hcont.differentiable_iteratedDeriv n
          (show (↑n : WithTop ℕ∞) < ⊤ by simp)
      -- HasDerivAt with value = iteratedDeriv (n+1)
      have hda : HasDerivAt (iteratedDeriv n (fun x => Phi_integrand x p)) (g p) η := by
        have := (hdiff η).hasDerivAt
        rwa [show deriv (iteratedDeriv n (fun x => Phi_integrand x p)) η = g p from
          (congr_fun iteratedDeriv_succ η).symm] at this
      -- The slope converges to the derivative
      have hslope := hda.tendsto_slope_zero
      -- Compose with sequence 1/(m+1) → 0
      have hseq : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) atTop
          (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact tendsto_inv_atTop_zero.comp
            (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
        · exact Eventually.of_forall fun m => inv_ne_zero (by positivity)
      have key := hslope.comp hseq
      -- The composed slope equals our difference quotient
      refine (key.congr fun m => ?_)
      show ((↑(m + 1) : ℝ)⁻¹)⁻¹ • (iteratedDeriv n (fun x => Phi_integrand x p)
          (η + ((m + 1 : ℕ) : ℝ)⁻¹) - iteratedDeriv n (fun x => Phi_integrand x p) η) =
        f m p
      simp [smul_eq_mul, inv_inv, f]
    -- Apply stronglyMeasurable_of_tendsto
    exact stronglyMeasurable_of_tendsto atTop hf_meas (tendsto_pi_nhds.mpr hf_lim)

/-- The hard analytic core: 4 layers of differentiation under the integral sign.
    Proof: rewrite Phi as a shifted integral, compute derivatives of the integrand
    (which is exp of a quadratic in η, so K''' = K'''' = 0), verify a single
    Gaussian-dominated bound on [-r,r], apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    four times. -/
private lemma Phi_order4_local_data :
    ∃ r > 0, ∃ Φ1 Φ2 Φ3 Φ4 : ℝ → ℝ,
      (∀ η ∈ Set.Icc (-r) r, HasDerivWithinAt Phi (Φ1 η) (Set.Icc (-r) r) η) ∧
      (∀ η ∈ Set.Icc (-r) r, HasDerivWithinAt Φ1 (Φ2 η) (Set.Icc (-r) r) η) ∧
      (∀ η ∈ Set.Icc (-r) r, HasDerivWithinAt Φ2 (Φ3 η) (Set.Icc (-r) r) η) ∧
      (∀ η ∈ Set.Icc (-r) r, HasDerivWithinAt Φ3 (Φ4 η) (Set.Icc (-r) r) η) ∧
      ContinuousOn Φ4 (Set.Icc (-r) r) := by
  -- Obtain the domination bound
  obtain ⟨bound, hbound_int, hbound_le⟩ := Phi_integrand_dominated
  -- Abbreviation for the k-th derivative integrand
  let D (k : ℕ) (η : ℝ) (p : P44) : ℝ := iteratedDeriv k (Phi_integrand · p) η
  -- Helper: integrability of D k η from domination
  have hD_int : ∀ k ≤ 4, ∀ η : ℝ, |η| ≤ 2 → Integrable (D k η) volume := by
    intro k hk η hη
    exact hbound_int.mono' (Phi_integrand_deriv_aestronglyMeasurable k η)
      (ae_of_all _ fun p => hbound_le k hk η hη p)
  -- Helper: HasDerivAt for one layer via hasDerivAt_integral_of_dominated_loc_of_deriv_le
  have hderiv_layer : ∀ (k : ℕ) (_ : k ≤ 3) (η : ℝ) (_ : η ∈ Set.Icc (-1 : ℝ) 1),
      HasDerivAt (fun η' => ∫ p, D k η' p) (∫ p, D (k + 1) η p) η := by
    intro k hk η hη
    have hη_abs : |η| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hη.1], by linarith [hη.2]⟩
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball η 1) (Metric.ball_mem_nhds η one_pos)
      (Filter.Eventually.of_forall fun η' => Phi_integrand_deriv_aestronglyMeasurable k η')
      (hD_int k (by omega) η (by linarith))
      (Phi_integrand_deriv_aestronglyMeasurable (k + 1) η)
      (ae_of_all _ fun p η' (hη' : η' ∈ Metric.ball η 1) =>
        hbound_le (k + 1) (by omega) η'
          (by have := (Metric.mem_ball.mp hη').le
              rw [Real.dist_eq] at this; linarith [abs_sub_abs_le_abs_sub η' η]) p)
      hbound_int
      (ae_of_all _ fun p η' (_ : η' ∈ Metric.ball η 1) => by
        -- iteratedDeriv k of a C^∞ function has derivative = iteratedDeriv (k+1)
        have hdiff := (Phi_integrand_contDiff_eta p).differentiable_iteratedDeriv k
          (by simp : (↑k : WithTop ℕ∞) < ⊤) η'
        suffices HasDerivAt (iteratedDeriv k (fun x => Phi_integrand x p))
            (deriv (iteratedDeriv k (fun x => Phi_integrand x p)) η') η' by
          rwa [show deriv (iteratedDeriv k (fun x => Phi_integrand x p)) η' =
            iteratedDeriv (k + 1) (fun x => Phi_integrand x p) η' from
              (congr_fun iteratedDeriv_succ η').symm] at this
        exact hdiff.hasDerivAt)).2
  -- Define the 4 derivative layers as integrals
  refine ⟨1, one_pos, fun η => ∫ p, D 1 η p, fun η => ∫ p, D 2 η p,
    fun η => ∫ p, D 3 η p, fun η => ∫ p, D 4 η p, ?_, ?_, ?_, ?_, ?_⟩
  -- Layer 0 → 1: HasDerivWithinAt Phi (∫ D 1) on [-1,1]
  · intro η hη
    rw [show Phi = (fun η' => ∫ p, D 0 η' p) from funext fun η' => by
      simp only [D, iteratedDeriv_zero]; exact Phi_eq_shifted_integral η']
    exact (hderiv_layer 0 (by omega) η hη).hasDerivWithinAt
  -- Layer 1 → 2
  · intro η hη; exact (hderiv_layer 1 (by omega) η hη).hasDerivWithinAt
  -- Layer 2 → 3
  · intro η hη; exact (hderiv_layer 2 (by omega) η hη).hasDerivWithinAt
  -- Layer 3 → 4
  · intro η hη; exact (hderiv_layer 3 (by omega) η hη).hasDerivWithinAt
  -- Continuity of Φ4 on [-1,1]
  · -- Use continuousOn_of_dominated (only needs bound on the set, not globally)
    exact continuousOn_of_dominated
      (fun η _ => Phi_integrand_deriv_aestronglyMeasurable 4 η)
      (fun η hη => ae_of_all _ fun p =>
        hbound_le 4 le_rfl η (by rw [abs_le]; exact ⟨by linarith [hη.1], by linarith [hη.2]⟩) p)
      hbound_int
      (ae_of_all _ fun p =>
        ((Phi_integrand_contDiff_eta p).continuous_iteratedDeriv 4 le_top).continuousOn)

/-- Φ is C⁴ on a small closed interval around 0.
    Proved by differentiating under the integral sign 4 times. -/
theorem Phi_contDiffOn_order4 :
    ∃ r > 0, ContDiffOn ℝ 4 Phi (Set.Icc (-r) r) := by
  obtain ⟨r, hr, Φ1, Φ2, Φ3, Φ4, hder0, hder1, hder2, hder3, hcont4⟩ :=
    Phi_order4_local_data
  refine ⟨r, hr, ?_⟩
  have hs : UniqueDiffOn ℝ (Set.Icc (-r) r) := uniqueDiffOn_Icc (by linarith)
  -- Build ContDiffOn layer by layer using derivWithin
  suffices h : ∀ (n : ℕ) (f g : ℝ → ℝ),
      (∀ x ∈ Set.Icc (-r) r, HasDerivWithinAt f (g x) (Set.Icc (-r) r) x) →
      ContDiffOn ℝ n g (Set.Icc (-r) r) →
      ContDiffOn ℝ (n + 1) f (Set.Icc (-r) r) by
    exact h 3 Phi Φ1 hder0
      (h 2 Φ1 Φ2 hder1
        (h 1 Φ2 Φ3 hder2
          (h 0 Φ3 Φ4 hder3 (contDiffOn_zero.mpr hcont4))))
  -- Prove the inductive step
  intro n f g hfg hg
  rw [contDiffOn_succ_iff_derivWithin hs]
  exact ⟨fun x hx => (hfg x hx).differentiableWithinAt,
    fun h => absurd h (by simp),
    hg.congr fun x hx => (hfg x hx).derivWithin (hs x hx)⟩

/-! ## E5. Odd-derivative vanishing from evenness -/

/-- Φ'(0) = 0, from evenness of Φ. -/
theorem Phi_deriv_zero : deriv Phi 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ Phi 0
  · have heven : ∀ x, Phi (-x) = Phi x := Phi_even
    have h1 : deriv (fun x => Phi (-x)) 0 = deriv Phi 0 := by
      congr 1; ext x; exact heven x
    have h2 : deriv (fun x => Phi (-x)) 0 = -deriv Phi 0 := by
      have key : HasDerivAt (fun x => Phi (-x)) (deriv Phi 0 * (-1)) 0 := by
        have hPhi0 : HasDerivAt Phi (deriv Phi 0) (-(0 : ℝ)) := by
          rw [neg_zero]; exact hd.hasDerivAt
        exact hPhi0.comp 0 (hasDerivAt_neg 0)
      rw [key.deriv]; ring
    linarith
  · exact deriv_zero_of_not_differentiableAt hd

/-- Φ'''(0) = 0, from evenness of Φ. -/
theorem Phi_iteratedDeriv3_zero : iteratedDeriv 3 Phi 0 = 0 := by
  obtain ⟨r, hr, hcd⟩ := Phi_contDiffOn_order4
  have hmem : Icc (-r) r ∈ nhds (0 : ℝ) := by
    apply Icc_mem_nhds <;> linarith
  have hcd4 : ContDiffAt ℝ 4 Phi 0 := hcd.contDiffAt hmem
  have hcd3 : ContDiffAt ℝ 3 Phi 0 := hcd4.of_le (by norm_num)
  have hneg3 : ContDiffAt ℝ 3 (fun x : ℝ => -x) 0 := contDiff_neg.contDiffAt
  have heven : (Phi ∘ fun x => -x) = Phi := by ext x; simp [Function.comp, Phi_even]
  have hPhi_neg0 : ContDiffAt ℝ 3 Phi (-(0 : ℝ)) := by rw [neg_zero]; exact hcd3
  have h3 := iteratedDeriv_comp_three hPhi_neg0 hneg3
  simp [heven] at h3
  have hid2 : iteratedDeriv 2 Neg.neg (0 : ℝ) = 0 := by
    rw [iteratedDeriv_eq_iterate]
    simp [Function.iterate_succ, Function.comp_def]
  have hid3 : iteratedDeriv 3 Neg.neg (0 : ℝ) = 0 := by
    rw [iteratedDeriv_eq_iterate]
    simp [Function.iterate_succ, Function.comp_def]
  rw [hid2, hid3] at h3
  linarith

/-! ## E6. Derivative-integral identities

The derivative layers from `Phi_order4_local_data` show that
`iteratedDeriv k Phi 0 = ∫ iteratedDeriv k (Phi_integrand · p) 0 dp`
for k ≤ 4. We extract this for k = 2 and k = 4. -/

/-- Helper: extract HasDerivAt from HasDerivWithinAt at an interior point. -/
private lemma hasDerivAt_of_interior {f : ℝ → ℝ} {f' : ℝ} {r : ℝ} (hr : 0 < r)
    {η : ℝ} (hη : η ∈ Set.Ioo (-r) r)
    (h : HasDerivWithinAt f f' (Set.Icc (-r) r) η) : HasDerivAt f f' η :=
  h.hasDerivAt (Icc_mem_nhds hη.1 hη.2)

/-- Helper: promote HasDerivWithinAt on [-r,r] to HasDerivAt near 0. -/
private lemma mk_nhds_deriv {r : ℝ} (hr : 0 < r) {f g : ℝ → ℝ}
    (hfg : ∀ η ∈ Set.Icc (-r) r, HasDerivWithinAt f (g η) (Set.Icc (-r) r) η) :
    ∀ᶠ η in nhds 0, HasDerivAt f (g η) η := by
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with η hη
  exact hasDerivAt_of_interior hr hη (hfg η (Set.Ioo_subset_Icc_self hη))

/-- Differentiation under the integral sign for Phi_integrand, layer k → k+1. -/
theorem Phi_integrand_hasDerivAt_layer (k : ℕ) (hk : k ≤ 3) (η : ℝ) (hη : |η| ≤ 1) :
    HasDerivAt (fun η' => ∫ p : P44, iteratedDeriv k (Phi_integrand · p) η')
      (∫ p : P44, iteratedDeriv (k + 1) (Phi_integrand · p) η) η := by
  obtain ⟨bound, hbound_int, hbound_le⟩ := Phi_integrand_dominated
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball η 1) (Metric.ball_mem_nhds η one_pos)
    (Filter.Eventually.of_forall fun η' => Phi_integrand_deriv_aestronglyMeasurable k η')
    ((hbound_int.mono' (Phi_integrand_deriv_aestronglyMeasurable k η)
      (ae_of_all _ fun p => hbound_le k (by omega) η (by linarith) p)))
    (Phi_integrand_deriv_aestronglyMeasurable (k + 1) η)
    (ae_of_all _ fun p η' (hη' : η' ∈ Metric.ball η 1) =>
      hbound_le (k + 1) (by omega) η'
        (by have := (Metric.mem_ball.mp hη').le
            rw [Real.dist_eq] at this; linarith [abs_sub_abs_le_abs_sub η' η]) p)
    hbound_int
    (ae_of_all _ fun p η' (_ : η' ∈ Metric.ball η 1) => by
      have hdiff := (Phi_integrand_contDiff_eta p).differentiable_iteratedDeriv k
        (by simp : (↑k : WithTop ℕ∞) < ⊤) η'
      suffices HasDerivAt (iteratedDeriv k (fun x => Phi_integrand x p))
          (deriv (iteratedDeriv k (fun x => Phi_integrand x p)) η') η' by
        rwa [show deriv (iteratedDeriv k (fun x => Phi_integrand x p)) η' =
          iteratedDeriv (k + 1) (fun x => Phi_integrand x p) η' from
            (congr_fun iteratedDeriv_succ η').symm] at this
      exact hdiff.hasDerivAt)).2

/-- On Ioo(-1/2, 1/2), iteratedDeriv k Phi agrees with the integral of
    iteratedDeriv k of the shifted integrand, for k ≤ 4. -/
private lemma iteratedDeriv_Phi_eq_on (k : ℕ) (hk : k ≤ 4) :
    ∀ η ∈ Set.Ioo (-1/2 : ℝ) (1/2),
      iteratedDeriv k Phi η =
        ∫ p : P44, iteratedDeriv k (Phi_integrand · p) η := by
  induction k with
  | zero => intro η _; simp [Phi_eq_shifted_integral]
  | succ k ih =>
    intro η hη
    rw [iteratedDeriv_succ]
    have h_eq_nhds : (fun η' => iteratedDeriv k Phi η') =ᶠ[nhds η]
        (fun η' => ∫ p, iteratedDeriv k (Phi_integrand · p) η') := by
      filter_upwards [Ioo_mem_nhds hη.1 hη.2]
        with η' hη'
      exact ih (by omega) η' hη'
    rw [Filter.EventuallyEq.deriv_eq h_eq_nhds]
    have hη_abs : |η| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hη.1, hη.2]
    exact (Phi_integrand_hasDerivAt_layer k (by omega) η hη_abs).deriv

/-- The second derivative of Φ equals the integral of the second derivative of the integrand. -/
theorem Phi_iteratedDeriv2_eq_integral :
    iteratedDeriv 2 Phi 0 =
      ∫ p : P44, iteratedDeriv 2 (Phi_integrand · p) 0 :=
  iteratedDeriv_Phi_eq_on 2 (by omega) 0 ⟨by norm_num, by norm_num⟩

/-- The fourth derivative of Φ equals the integral of the fourth derivative of the integrand. -/
theorem Phi_iteratedDeriv4_eq_integral :
    iteratedDeriv 4 Phi 0 =
      ∫ p : P44, iteratedDeriv 4 (Phi_integrand · p) 0 :=
  iteratedDeriv_Phi_eq_on 4 (by omega) 0 ⟨by norm_num, by norm_num⟩

end Braverman
