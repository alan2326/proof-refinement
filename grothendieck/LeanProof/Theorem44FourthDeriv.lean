/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44DirectValues
import LeanProof.Lemma41

/-!
# Fourth Derivative of Φ at Zero

This file proves `Phi_iteratedDeriv4_at_zero : iteratedDeriv 4 Phi 0 = 38400 * Real.sqrt 2`.

The approach mirrors the second derivative proof in `Theorem44DirectValues.lean`:
1. Compute the explicit 4th derivative `D4_val` using HasDerivAt four times
2. Decompose as h⁴·K₄₀ + 4h³g·K₃₁ + 6h²g²·K₂₂ + 4hg³·K₁₃ + g⁴·K₀₄
3. FTC on each kernel (half-line integrals)
4. Quadrant integrals via Gaussian moments
5. Boundary integral evaluation via Fourier transforms
6. Fubini assembly connecting 4D → 2D → numerical value
-/

noncomputable section

namespace Braverman

open MeasureTheory Set Real Filter
open scoped Topology

attribute [local fun_prop] h5_continuous

/-! ## Utility Lemmas -/

/-- Amplitude recurrence: derivative of `exp(Q) · (a·sin(L) + b·cos(L))`.
The new amplitudes are `(Q'·a + a' - L'·b)` (sin) and `(Q'·b + b' + L'·a)` (cos). -/
lemma hasDerivAt_expQ_sincos_amp
    {Q L a b : ℝ → ℝ} {Q' L' a' b' : ℝ} {η : ℝ}
    (hQ : HasDerivAt Q Q' η) (hL : HasDerivAt L L' η)
    (ha : HasDerivAt a a' η) (hb : HasDerivAt b b' η) :
    HasDerivAt (fun η => Real.exp (Q η) * (a η * Real.sin (L η) + b η * Real.cos (L η)))
      (Real.exp (Q η) * ((Q' * a η + a' - L' * b η) * Real.sin (L η) +
                          (Q' * b η + b' + L' * a η) * Real.cos (L η))) η := by
  have h1 := hQ.exp.mul ((ha.mul hL.sin).add (hb.mul hL.cos))
  refine h1.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply]
  ring

/-- |a·sin(θ) + b·cos(θ)| ≤ |a| + |b|. -/
lemma abs_sin_cos_le (a b θ : ℝ) :
    |a * Real.sin θ + b * Real.cos θ| ≤ |a| + |b| :=
  calc |a * Real.sin θ + b * Real.cos θ|
      ≤ |a * Real.sin θ| + |b * Real.cos θ| := abs_add_le _ _
    _ = |a| * |Real.sin θ| + |b| * |Real.cos θ| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * 1 + |b| * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _))
    _ = |a| + |b| := by ring

/-! ## D4_val — Explicit 4th derivative formula -/

/-- The explicit fourth derivative of `Phi_smooth_part p` at η = 0.

This equals `exp(Q₀) · (a₄·sin(L₀) + b₄·cos(L₀))` where a₄, b₄ are computed
from the amplitude recurrence with Q₁=-(uh+vg), Q₂=-(h²+g²), L₁=ug+vh, L₂=2hg. -/
private def D4_val (p : P44) : ℝ :=
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  let E₀ := Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2)
  let S₀ := Real.sin (x₁ * y₁ + u * v)
  let C₀ := Real.cos (x₁ * y₁ + u * v)
  let Q₁ := -(u * h + v * g)
  let Q₂ := -(h ^ 2 + g ^ 2)
  let L₁ := u * g + v * h
  let L₂ := 2 * h * g
  let a₄ := Q₁ ^ 4 + 6 * Q₁ ^ 2 * Q₂ + 3 * Q₂ ^ 2 - 6 * Q₁ ^ 2 * L₁ ^ 2 -
             6 * Q₂ * L₁ ^ 2 + L₁ ^ 4 - 12 * Q₁ * L₁ * L₂ - 3 * L₂ ^ 2
  let b₄ := 4 * Q₁ ^ 3 * L₁ + 12 * Q₁ * Q₂ * L₁ + 6 * Q₁ ^ 2 * L₂ +
             6 * Q₂ * L₂ - 4 * Q₁ * L₁ ^ 3 - 6 * L₁ ^ 2 * L₂
  E₀ * (a₄ * S₀ + b₄ * C₀)

/-! ## iteratedDeriv 4 = D4_val

The proof applies HasDerivAt four times using `hasDerivAt_expQ_sincos_amp`, then
evaluates at η=0 to match the D4_val formula. -/

/-- The fourth derivative of `Phi_smooth_part p` at η=0 equals `D4_val p`. -/
private lemma iteratedDeriv4_Phi_smooth_eq (p : P44) :
    iteratedDeriv 4 (Phi_smooth_part p) 0 = D4_val p := by
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  -- Key sub-expressions as functions of η
  let Qf : ℝ → ℝ := fun η => -(x₁ ^ 2 + (u + η * h) ^ 2 + y₁ ^ 2 + (v + η * g) ^ 2) / 2
  let Lf : ℝ → ℝ := fun η => x₁ * y₁ + (u + η * h) * (v + η * g)
  let Qd : ℝ → ℝ := fun η => -((u + η * h) * h + (v + η * g) * g)
  let Ld : ℝ → ℝ := fun η => h * (v + η * g) + (u + η * h) * g
  let Q₂ : ℝ := -(h ^ 2 + g ^ 2)
  let L₂ : ℝ := 2 * h * g
  -- HasDerivAt building blocks
  have hQ : ∀ η, HasDerivAt Qf (Qd η) η := fun η => hasDerivAt_Q u h x₁ y₁ v g η
  have hL : ∀ η, HasDerivAt Lf (Ld η) η := fun η => hasDerivAt_L u h x₁ y₁ v g η
  have hQd : ∀ η, HasDerivAt Qd Q₂ η := by
    intro η
    exact (((hasDerivAt_affine u h η).mul_const h).add
      ((hasDerivAt_affine v g η).mul_const g) |>.neg).congr_deriv (by ring)
  have hLd : ∀ η, HasDerivAt Ld L₂ η := by
    intro η
    exact (((hasDerivAt_affine v g η).const_mul h).add
      ((hasDerivAt_affine u h η).mul_const g)).congr_deriv (by ring)
  -- ═══ Layer 0→1 ═══
  have e1 : deriv (Phi_smooth_part p) = fun η =>
      Real.exp (Qf η) * (Qd η * Real.sin (Lf η) + Ld η * Real.cos (Lf η)) := by
    ext η; exact (hasDerivAt_exp_Q_sin_L u h x₁ y₁ v g η).deriv
  rw [e1]
  -- ═══ Layer 1→2 ═══
  -- hasDerivAt_expQ_sincos_amp gives derivative with:
  --   sin coeff: Qd(η)*Qd(η) + Q₂ - Ld(η)*Ld(η)
  --   cos coeff: Qd(η)*Ld(η) + L₂ + Ld(η)*Qd(η)
  have e2 : deriv (fun η => Real.exp (Qf η) *
      (Qd η * Real.sin (Lf η) + Ld η * Real.cos (Lf η))) = fun η =>
      Real.exp (Qf η) *
        ((Qd η * Qd η + Q₂ - Ld η * Ld η) * Real.sin (Lf η) +
         (Qd η * Ld η + L₂ + Ld η * Qd η) * Real.cos (Lf η)) := by
    ext η; exact (hasDerivAt_expQ_sincos_amp (hQ η) (hL η) (hQd η) (hLd η)).deriv
  rw [e2]
  -- ═══ Layer 2→3 ═══
  -- HasDerivAt for a₂(η) = Qd²+Q₂-Ld², using exact derivative from product rule
  have hda₂ : ∀ η, HasDerivAt (fun η => Qd η * Qd η + Q₂ - Ld η * Ld η)
      (Q₂ * Qd η + Qd η * Q₂ - (L₂ * Ld η + Ld η * L₂)) η := fun η =>
    hasDerivAt_of_funEq
      (((hQd η).mul (hQd η)).const_add Q₂ |>.sub ((hLd η).mul (hLd η)))
      (by ext η; simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, sq]; ring)
  -- HasDerivAt for b₂(η) = Qd*Ld+L₂+Ld*Qd
  have hdb₂ : ∀ η, HasDerivAt (fun η => Qd η * Ld η + L₂ + Ld η * Qd η)
      (Q₂ * Ld η + Qd η * L₂ + (L₂ * Qd η + Ld η * Q₂)) η := fun η =>
    hasDerivAt_of_funEq
      (((hQd η).mul (hLd η)).const_add L₂ |>.add ((hLd η).mul (hQd η)))
      (by ext η; simp only [Pi.add_apply, Pi.mul_apply]; ring)
  -- Layer 2→3 derivative using hasDerivAt_expQ_sincos_amp
  -- The exact derivative value has:
  --   sin coeff: Qd(η)*(Qd(η)*Qd(η)+Q₂-Ld(η)*Ld(η)) + (Q₂*Qd(η)+Qd(η)*Q₂-(L₂*Ld(η)+Ld(η)*L₂)) - Ld(η)*(Qd(η)*Ld(η)+L₂+Ld(η)*Qd(η))
  --   cos coeff: Qd(η)*(Qd(η)*Ld(η)+L₂+Ld(η)*Qd(η)) + (Q₂*Ld(η)+Qd(η)*L₂+(L₂*Qd(η)+Ld(η)*Q₂)) + Ld(η)*(Qd(η)*Qd(η)+Q₂-Ld(η)*Ld(η))
  let a₃ : ℝ → ℝ := fun η =>
    Qd η * (Qd η * Qd η + Q₂ - Ld η * Ld η) +
      (Q₂ * Qd η + Qd η * Q₂ - (L₂ * Ld η + Ld η * L₂)) -
      Ld η * (Qd η * Ld η + L₂ + Ld η * Qd η)
  let b₃ : ℝ → ℝ := fun η =>
    Qd η * (Qd η * Ld η + L₂ + Ld η * Qd η) +
      (Q₂ * Ld η + Qd η * L₂ + (L₂ * Qd η + Ld η * Q₂)) +
      Ld η * (Qd η * Qd η + Q₂ - Ld η * Ld η)
  have e3 : deriv (fun η => Real.exp (Qf η) *
      ((Qd η * Qd η + Q₂ - Ld η * Ld η) * Real.sin (Lf η) +
       (Qd η * Ld η + L₂ + Ld η * Qd η) * Real.cos (Lf η))) = fun η =>
      Real.exp (Qf η) * (a₃ η * Real.sin (Lf η) + b₃ η * Real.cos (Lf η)) := by
    ext η; exact (hasDerivAt_expQ_sincos_amp (hQ η) (hL η) (hda₂ η) (hdb₂ η)).deriv
  rw [e3]
  -- ═══ Layer 3→4 (at η = 0 only) ═══
  -- Need HasDerivAt for a₃ and b₃ at η = 0
  -- a₃(η) = Qd(η)*A₂(η) + da₂(η) - Ld(η)*B₂(η)
  -- where A₂ = Qd²+Q₂-Ld², B₂ = Qd*Ld+L₂+Ld*Qd, da₂ = Q₂*Qd+Qd*Q₂-(L₂*Ld+Ld*L₂)
  -- Build HasDerivAt from product/sum rules
  -- For the middle term da₂(η) = Q₂*Qd(η)+Qd(η)*Q₂-(L₂*Ld(η)+Ld(η)*L₂):
  have h_mid_a : HasDerivAt (fun η => Q₂ * Qd η + Qd η * Q₂ - (L₂ * Ld η + Ld η * L₂))
      (Q₂ * Q₂ + Q₂ * Q₂ - (L₂ * L₂ + L₂ * L₂)) 0 :=
    ((hQd 0).const_mul Q₂ |>.add ((hQd 0).mul_const Q₂)).sub
      ((hLd 0).const_mul L₂ |>.add ((hLd 0).mul_const L₂))
  have hda₃ : HasDerivAt a₃
      (Q₂ * (Qd 0 * Qd 0 + Q₂ - Ld 0 * Ld 0) +
        Qd 0 * (Q₂ * Qd 0 + Qd 0 * Q₂ - (L₂ * Ld 0 + Ld 0 * L₂)) +
        (Q₂ * Q₂ + Q₂ * Q₂ - (L₂ * L₂ + L₂ * L₂)) -
        (L₂ * (Qd 0 * Ld 0 + L₂ + Ld 0 * Qd 0) +
          Ld 0 * (Q₂ * Ld 0 + Qd 0 * L₂ + (L₂ * Qd 0 + Ld 0 * Q₂)))) 0 :=
    ((hQd 0).mul (hda₂ 0)).add h_mid_a |>.sub ((hLd 0).mul (hdb₂ 0))
  -- For b₃: b₃(η) = Qd(η)*B₂(η) + db₂(η) + Ld(η)*A₂(η)
  -- db₂(η) = Q₂*Ld(η)+Qd(η)*L₂+(L₂*Qd(η)+Ld(η)*Q₂)
  have h_mid_b : HasDerivAt (fun η => Q₂ * Ld η + Qd η * L₂ + (L₂ * Qd η + Ld η * Q₂))
      (Q₂ * L₂ + Q₂ * L₂ + (L₂ * Q₂ + L₂ * Q₂)) 0 :=
    ((hLd 0).const_mul Q₂ |>.add ((hQd 0).mul_const L₂)).add
      ((hQd 0).const_mul L₂ |>.add ((hLd 0).mul_const Q₂))
  have hdb₃ : HasDerivAt b₃
      (Q₂ * (Qd 0 * Ld 0 + L₂ + Ld 0 * Qd 0) +
        Qd 0 * (Q₂ * Ld 0 + Qd 0 * L₂ + (L₂ * Qd 0 + Ld 0 * Q₂)) +
        (Q₂ * L₂ + Q₂ * L₂ + (L₂ * Q₂ + L₂ * Q₂)) +
        (L₂ * (Qd 0 * Qd 0 + Q₂ - Ld 0 * Ld 0) +
          Ld 0 * (Q₂ * Qd 0 + Qd 0 * Q₂ - (L₂ * Ld 0 + Ld 0 * L₂)))) 0 :=
    ((hQd 0).mul (hdb₂ 0)).add h_mid_b |>.add ((hLd 0).mul (hda₂ 0))
  -- Apply the recurrence one last time at η = 0
  have hd4 := hasDerivAt_expQ_sincos_amp (hQ 0) (hL 0) hda₃ hdb₃
  have key := hd4.deriv
  rw [key]
  unfold D4_val
  simp only [show Qf 0 = -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2 from by dsimp [Qf]; ring,
    show Lf 0 = x₁ * y₁ + u * v from by dsimp [Lf]; ring]
  ring

/-! ## Chain rule decomposition: D4_val = h⁴K₄₀ + 4h³gK₃₁ + ... -/

/-- The five kernels: 4th partial derivatives of F(u,v) = exp(Q₀)·sin(L₀). -/
private def K40 (x₁ u y₁ v : ℝ) : ℝ :=
  Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3) *
      Real.sin (x₁ * y₁ + u * v) +
     (-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v) *
      Real.cos (x₁ * y₁ + u * v))

private def K31 (x₁ u y₁ v : ℝ) : ℝ :=
  Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
      Real.sin (x₁ * y₁ + u * v) +
     (-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3) *
      Real.cos (x₁ * y₁ + u * v))

private def K22 (x₁ u y₁ v : ℝ) : ℝ :=
  Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1) *
      Real.sin (x₁ * y₁ + u * v) +
     (4 * u * v) *
      Real.cos (x₁ * y₁ + u * v))

private def K13 (x₁ u y₁ v : ℝ) : ℝ :=
  Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
      Real.sin (x₁ * y₁ + u * v) +
     (u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3) *
      Real.cos (x₁ * y₁ + u * v))

private def K04 (x₁ u y₁ v : ℝ) : ℝ :=
  Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3) *
      Real.sin (x₁ * y₁ + u * v) +
     (4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v) *
      Real.cos (x₁ * y₁ + u * v))

/-- D4_val decomposes as h⁴·K₄₀ + 4h³g·K₃₁ + 6h²g²·K₂₂ + 4hg³·K₁₃ + g⁴·K₀₄. -/
private lemma D4_val_eq_chain (p : P44) :
    D4_val p =
      let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
      let h := h5 x₁; let g := h5 y₁
      h ^ 4 * K40 x₁ u y₁ v +
      4 * h ^ 3 * g * K31 x₁ u y₁ v +
      6 * h ^ 2 * g ^ 2 * K22 x₁ u y₁ v +
      4 * h * g ^ 3 * K13 x₁ u y₁ v +
      g ^ 4 * K04 x₁ u y₁ v := by
  unfold D4_val K40 K31 K22 K13 K04; ring

/-! ## FTC lemmas: half-line integrals of each kernel

Each follows the pattern of `ftc_Ku_u` from DirectValues:
1. Define antiderivative
2. HasDerivAt
3. ContinuousWithinAt at 0
4. Tendsto at ∞
5. IntegrableOn
6. Apply integral_Ioi_of_hasDerivAt_of_tendsto -/

/-- FTC: ∫_{u>0} K₄₀ du = exp(-(x₁²+y₁²+v²)/2)·(v³+3v)·cos(x₁y₁).
Antiderivative: F_uuu(u,v) = exp(Q)·((-u³+3uv²+3u)sin(L)+(3u²v-v³-3v)cos(L)). -/
private lemma ftc_K40_u (x₁ y₁ v : ℝ) :
    ∫ u in Ioi (0 : ℝ), K40 x₁ u y₁ v =
    Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 + 3 * v) * Real.cos (x₁ * y₁)) := by
  -- Antiderivative: f(u) = exp(Q)·((-u³+3uv²+3u)·sin(L)+(3u²v-v³-3v)·cos(L))
  set f := fun u : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-u ^ 3 + 3 * u * v ^ 2 + 3 * u) * Real.sin (x₁ * y₁ + u * v) +
     (3 * u ^ 2 * v - v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v))
  -- 1. HasDerivAt: f'(u) = K40(x₁,u,y₁,v)
  have hd : ∀ u : ℝ, HasDerivAt f (K40 x₁ u y₁ v) u := by
    intro u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- HasDerivAt for amplitude a(u) = -u³+3uv²+3u, a'(u) = -3u²+3v²+3
    have ha : HasDerivAt (fun u => -u ^ 3 + 3 * u * v ^ 2 + 3 * u)
        (-3 * u ^ 2 + 3 * v ^ 2 + 3) u := by
      have hid := hasDerivAt_id u
      -- d/du(u³) = 3u², d/du(u) = 1, combine
      have h_u3 := hid.mul (hid.mul hid)  -- HasDerivAt (id * (id * id)) ... u
      have h_u := hid  -- HasDerivAt id 1 u
      -- -u³ + 3uv² + 3u = -u*u*u + 3v²*u + 3*u = (-1)*u*u*u + (3v²+3)*u
      have h_neg_u3 := h_u3.neg
      have h_rest := hid.const_mul (3 * v ^ 2 + 3)
      have h_sum := h_neg_u3.add h_rest
      -- h_sum : HasDerivAt (fun x => -(id x * (id x * id x)) + (3 * v ^ 2 + 3) * id x) ... u
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    -- HasDerivAt for amplitude b(u) = 3u²v-v³-3v, b'(u) = 6uv
    have hb : HasDerivAt (fun u => 3 * u ^ 2 * v - v ^ 3 - 3 * v)
        (6 * u * v) u := by
      have hid := hasDerivAt_id u
      have h_u2 := hid.mul hid  -- HasDerivAt (id * id) ... u
      have h_scaled := h_u2.const_mul (3 * v)
      have h_const : HasDerivAt (fun _ : ℝ => -(v ^ 3) - 3 * v) 0 u := hasDerivAt_const u _
      have h_sum := h_scaled.add h_const
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    have step := hasDerivAt_expQ_sincos_amp hQ hL ha hb
    have heq : f = fun η => Real.exp ((fun u => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) η) *
        ((fun u => -u ^ 3 + 3 * u * v ^ 2 + 3 * u) η *
          Real.sin ((fun u => x₁ * y₁ + u * v) η) +
         (fun u => 3 * u ^ 2 * v - v ^ 3 - 3 * v) η *
          Real.cos ((fun u => x₁ * y₁ + u * v) η)) := by
      ext; dsimp
    exact (hasDerivAt_of_funEq step heq).congr_deriv (by unfold K40; ring)
  -- 2. ContinuousWithinAt at 0
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((-u ^ 3 + 3 * u * v ^ 2 + 3 * u) * Real.sin (x₁ * y₁ + u * v) +
       (3 * u ^ 2 * v - v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- 3. Tendsto at ∞
  -- f(u) = exp(-(c+u²)/2) * polynomial_trig(u)
  -- |polynomial_trig| ≤ C₀ + C₁|u| + C₂u² + C₃|u|³ for suitable constants
  -- Each |u|^k * exp(-(1/2)u²) → 0 by Gaussian decay
  have htend : Tendsto f atTop (nhds 0) := by
    -- Helper: |u|^k * exp(-u²/2) → 0 at atTop for k = 0,1,2,3
    set c := x₁ ^ 2 + y₁ ^ 2 + v ^ 2
    have hexp_factor : ∀ u, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) := by
      intro u; rw [← Real.exp_add]; congr 1; show _ = -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 + _; ring
    -- Tendsto for |u|^k * exp(-u²/2) → 0 at cocompact, hence at atTop
    have htk : ∀ (k : ℕ), Tendsto (fun u : ℝ => |u| ^ k * Real.exp (-(1/2) * u ^ 2))
        atTop (nhds 0) := by
      intro k
      exact ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (show (0:ℝ) < 1/2 by positivity) k).mono_left
        atTop_le_cocompact).congr' (eventually_atTop.mpr
        ⟨0, fun u hu => by simp [rpow_natCast, abs_of_nonneg hu]⟩)
    -- Bound ‖f(u)‖
    set C₀ := |v| ^ 3 + 3 * |v| with hC₀_def
    set C₁ := 3 * v ^ 2 + 3 with hC₁_def
    set C₂ := 3 * |v| with hC₂_def
    set C₃ := (1 : ℝ) with hC₃_def
    apply squeeze_zero_norm (a := fun u =>
      Real.exp (-c / 2) * (C₀ * (|u| ^ 0 * Real.exp (-(1/2) * u ^ 2)) +
                            C₁ * (|u| ^ 1 * Real.exp (-(1/2) * u ^ 2)) +
                            C₂ * (|u| ^ 2 * Real.exp (-(1/2) * u ^ 2)) +
                            C₃ * (|u| ^ 3 * Real.exp (-(1/2) * u ^ 2))))
    · intro u; simp only [f]
      rw [hexp_factor]
      have hB : ‖(-u ^ 3 + 3 * u * v ^ 2 + 3 * u) * Real.sin (x₁ * y₁ + u * v) +
          (3 * u ^ 2 * v - v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v)‖ ≤
          C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3 := by
        calc ‖_‖ ≤ |-u ^ 3 + 3 * u * v ^ 2 + 3 * u| +
            |3 * u ^ 2 * v - v ^ 3 - 3 * v| := abs_sin_cos_le _ _ _
          _ ≤ _ := by
            have hav := abs_nonneg v
            have hau := abs_nonneg u
            -- |-u³+3uv²+3u| ≤ |u|³+(3v²+3)|u|
            have h1 : |-u ^ 3 + 3 * u * v ^ 2 + 3 * u| ≤ |u| ^ 3 + (3 * v ^ 2 + 3) * |u| := by
              rw [show -u ^ 3 + 3 * u * v ^ 2 + 3 * u = u * (3 * v ^ 2 + 3 - u ^ 2) from by ring]
              calc |u * (3 * v ^ 2 + 3 - u ^ 2)| = |u| * |3 * v ^ 2 + 3 - u ^ 2| := abs_mul _ _
                _ ≤ |u| * (u ^ 2 + (3 * v ^ 2 + 3)) := by
                  apply mul_le_mul_of_nonneg_left _ hau
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |u| ^ 3 + (3 * v ^ 2 + 3) * |u| := by nlinarith [sq_abs u]
            -- |3u²v-v³-3v| ≤ 3|v||u|²+|v|³+3|v|
            have h2 : |3 * u ^ 2 * v - v ^ 3 - 3 * v| ≤ 3 * |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by
              rw [show 3 * u ^ 2 * v - v ^ 3 - 3 * v = v * (3 * u ^ 2 - v ^ 2 - 3) from by ring]
              calc |v * (3 * u ^ 2 - v ^ 2 - 3)| = |v| * |3 * u ^ 2 - v ^ 2 - 3| := abs_mul _ _
                _ ≤ |v| * (3 * u ^ 2 + v ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hav
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = 3 * |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by
                  nlinarith [sq_abs u, sq_abs v]
            -- C₀ = |v|³+3|v|, C₁ = 3v²+3, C₂ = 3|v|, C₃ = 1
            simp only [hC₀_def, hC₁_def, hC₂_def, hC₃_def, one_mul]
            nlinarith [sq_abs u, sq_abs v]
      calc ‖Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * _‖
          = Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * ‖_‖ := by
            rw [norm_mul, norm_mul, norm_of_nonneg (Real.exp_nonneg _),
              norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) *
            (C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by
            simp only [pow_succ, pow_zero, mul_one]
            ring
    · -- Each term → 0
      have h0 := (htk 0).const_mul C₀
      have h1 := (htk 1).const_mul C₁
      have h2 := (htk 2).const_mul C₂
      have h3 := (htk 3).const_mul C₃
      rw [show (0 : ℝ) = Real.exp (-c / 2) * (C₀ * 0 + C₁ * 0 + C₂ * 0 + C₃ * 0) by
        simp]
      exact (((h0.add h1).add h2).add h3).const_mul _
  -- 4. IntegrableOn
  have hint : IntegrableOn (fun u => K40 x₁ u y₁ v) (Ioi 0) := by
    show IntegrableOn (fun u =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3) *
          Real.sin (x₁ * y₁ + u * v) +
         (-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v) *
          Real.cos (x₁ * y₁ + u * v))) (Ioi 0)
    -- Bound: |trig part| ≤ (3v⁴+12v²+3) + (10v²+12)u² + 3u⁴ (uses AM-GM for u³v terms)
    refine (((integrableOn_pow_mul_gauss 0).const_mul
        (3 * v ^ 4 + 12 * v ^ 2 + 3)).add
      ((integrableOn_pow_mul_gauss 2).const_mul (10 * v ^ 2 + 12))).add
      ((integrableOn_pow_mul_gauss 4).const_mul 3) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) ≤
        Real.exp (-(1 / 2) * u ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3) *
        Real.sin (x₁ * y₁ + u * v) +
       (-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v) *
        Real.cos (x₁ * y₁ + u * v))| ≤
      (3 * v ^ 4 + 12 * v ^ 2 + 3) +
      (10 * v ^ 2 + 12) * u ^ 2 + 3 * u ^ 4 := by
      calc _ ≤ |u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3| +
              |-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v| :=
            abs_sin_cos_le _ _ _
        _ ≤ _ := by
          have hsu := sq_nonneg u
          have hsv := sq_nonneg v
          have ha1 : |u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3|
              ≤ u ^ 4 + 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 + 6 * v ^ 2 + 3 :=
            abs_le.mpr ⟨by nlinarith [sq_nonneg (u * v), sq_nonneg (u ^ 2 - v ^ 2)],
              by nlinarith⟩
          -- |cos amplitude| ≤ 2u⁴+4u²v²+2v⁴+6u²+6v² (AM-GM: 4u³|v| ≤ 2u⁴+2u²v²)
          have ha2 : |-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v|
              ≤ 2 * u ^ 4 + 4 * u ^ 2 * v ^ 2 + 2 * v ^ 4 + 6 * u ^ 2 + 6 * v ^ 2 := by
            rw [abs_le]; constructor
            · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (u - v),
                sq_nonneg (u + v), sq_nonneg (u * v)]
            · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (u - v),
                sq_nonneg (u + v), sq_nonneg (u * v)]
          linarith
    nlinarith [Real.exp_nonneg (-(1 / 2) * u ^ 2),
      abs_nonneg ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 - 6 * u ^ 2 + 6 * v ^ 2 + 3) *
        Real.sin (x₁ * y₁ + u * v) +
       (-4 * u ^ 3 * v + 4 * u * v ^ 3 + 12 * u * v) *
        Real.cos (x₁ * y₁ + u * v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) (by exact hint) htend
  rw [this]
  -- Compute f(0): f(0) = exp(-(x₁²+y₁²+v²)/2) * (0 + (-v³-3v)*cos(x₁y₁))
  -- So 0 - f(0) = exp(...) * (v³+3v)*cos(x₁y₁)
  show 0 - f 0 = _
  simp only [f, zero_pow, mul_zero, zero_mul, neg_zero, zero_add, mul_one, sub_zero,
    zero_sub, neg_mul, neg_neg]
  ring

/-- FTC: ∫_{u>0} K₃₁ du = -exp(-(x₁²+y₁²+v²)/2)·(v³-v)·sin(x₁y₁). -/
private lemma ftc_K31_u (x₁ y₁ v : ℝ) :
    ∫ u in Ioi (0 : ℝ), K31 x₁ u y₁ v =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - v) * Real.sin (x₁ * y₁)) := by
  -- Antiderivative: f(u) = exp(Q)·((u²v+v³-v)·sin(L)+(u³+uv²-3u)·cos(L))
  set f := fun u : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((u ^ 2 * v + v ^ 3 - v) * Real.sin (x₁ * y₁ + u * v) +
     (u ^ 3 + u * v ^ 2 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
  -- 1. HasDerivAt: f'(u) = K31(x₁,u,y₁,v)
  have hd : ∀ u : ℝ, HasDerivAt f (K31 x₁ u y₁ v) u := by
    intro u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- HasDerivAt for amplitude a(u) = u²v+v³-v, a'(u) = 2uv
    have ha : HasDerivAt (fun u => u ^ 2 * v + v ^ 3 - v)
        (2 * u * v) u := by
      have hid := hasDerivAt_id u
      have h_u2 := hid.mul hid
      have h_scaled := h_u2.const_mul v
      have h_const : HasDerivAt (fun _ : ℝ => v ^ 3 - v) 0 u := hasDerivAt_const u _
      have h_sum := h_scaled.add h_const
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    -- HasDerivAt for amplitude b(u) = u³+uv²-3u, b'(u) = 3u²+v²-3
    have hb : HasDerivAt (fun u => u ^ 3 + u * v ^ 2 - 3 * u)
        (3 * u ^ 2 + v ^ 2 - 3) u := by
      have hid := hasDerivAt_id u
      have h_u3 := hid.mul (hid.mul hid)
      have h_rest := hid.const_mul (v ^ 2 - 3)
      have h_sum := h_u3.add h_rest
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    have step := hasDerivAt_expQ_sincos_amp hQ hL ha hb
    have heq : f = fun η => Real.exp ((fun u => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) η) *
        ((fun u => u ^ 2 * v + v ^ 3 - v) η *
          Real.sin ((fun u => x₁ * y₁ + u * v) η) +
         (fun u => u ^ 3 + u * v ^ 2 - 3 * u) η *
          Real.cos ((fun u => x₁ * y₁ + u * v) η)) := by
      ext; dsimp
    exact (hasDerivAt_of_funEq step heq).congr_deriv (by unfold K31; ring)
  -- 2. ContinuousWithinAt at 0
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((u ^ 2 * v + v ^ 3 - v) * Real.sin (x₁ * y₁ + u * v) +
       (u ^ 3 + u * v ^ 2 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- 3. Tendsto at ∞
  have htend : Tendsto f atTop (nhds 0) := by
    set c := x₁ ^ 2 + y₁ ^ 2 + v ^ 2
    have hexp_factor : ∀ u, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) := by
      intro u; rw [← Real.exp_add]; congr 1; show _ = -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 + _; ring
    have htk : ∀ (k : ℕ), Tendsto (fun u : ℝ => |u| ^ k * Real.exp (-(1/2) * u ^ 2))
        atTop (nhds 0) := by
      intro k
      exact ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (show (0:ℝ) < 1/2 by positivity) k).mono_left
        atTop_le_cocompact).congr' (eventually_atTop.mpr
        ⟨0, fun u hu => by simp [rpow_natCast, abs_of_nonneg hu]⟩)
    set C₀ := |v| ^ 3 + |v| with hC₀_def
    set C₁ := v ^ 2 + 3 with hC₁_def
    set C₂ := |v| with hC₂_def
    set C₃ := (1 : ℝ) with hC₃_def
    apply squeeze_zero_norm (a := fun u =>
      Real.exp (-c / 2) * (C₀ * (|u| ^ 0 * Real.exp (-(1/2) * u ^ 2)) +
                            C₁ * (|u| ^ 1 * Real.exp (-(1/2) * u ^ 2)) +
                            C₂ * (|u| ^ 2 * Real.exp (-(1/2) * u ^ 2)) +
                            C₃ * (|u| ^ 3 * Real.exp (-(1/2) * u ^ 2))))
    · intro u; simp only [f]
      rw [hexp_factor]
      have hB : ‖(u ^ 2 * v + v ^ 3 - v) * Real.sin (x₁ * y₁ + u * v) +
          (u ^ 3 + u * v ^ 2 - 3 * u) * Real.cos (x₁ * y₁ + u * v)‖ ≤
          C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3 := by
        calc ‖_‖ ≤ |u ^ 2 * v + v ^ 3 - v| +
            |u ^ 3 + u * v ^ 2 - 3 * u| := abs_sin_cos_le _ _ _
          _ ≤ _ := by
            have hav := abs_nonneg v
            have hau := abs_nonneg u
            have h1 : |u ^ 2 * v + v ^ 3 - v| ≤ |v| * u ^ 2 + (|v| ^ 3 + |v|) := by
              rw [show u ^ 2 * v + v ^ 3 - v = v * (u ^ 2 + v ^ 2 - 1) from by ring]
              calc |v * (u ^ 2 + v ^ 2 - 1)| = |v| * |u ^ 2 + v ^ 2 - 1| := abs_mul _ _
                _ ≤ |v| * (u ^ 2 + v ^ 2 + 1) := by
                  apply mul_le_mul_of_nonneg_left _ hav
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |v| * u ^ 2 + (|v| ^ 3 + |v|) := by nlinarith [sq_abs v]
            have h2 : |u ^ 3 + u * v ^ 2 - 3 * u| ≤ |u| ^ 3 + (v ^ 2 + 3) * |u| := by
              rw [show u ^ 3 + u * v ^ 2 - 3 * u = u * (u ^ 2 + v ^ 2 - 3) from by ring]
              calc |u * (u ^ 2 + v ^ 2 - 3)| = |u| * |u ^ 2 + v ^ 2 - 3| := abs_mul _ _
                _ ≤ |u| * (u ^ 2 + v ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hau
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |u| ^ 3 + (v ^ 2 + 3) * |u| := by nlinarith [sq_abs u]
            -- Combine: sum = (|v|³+|v|) + (v²+3)|u| + |v|·u² + |u|³ = C₀ + C₁|u| + C₂|u|² + C₃|u|³
            show |u ^ 2 * v + v ^ 3 - v| + |u ^ 3 + u * v ^ 2 - 3 * u| ≤
              (|v| ^ 3 + |v|) + (v ^ 2 + 3) * |u| + |v| * |u| ^ 2 + 1 * |u| ^ 3
            nlinarith [h1, h2, sq_abs u]
      calc ‖Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * _‖
          = Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * ‖_‖ := by
            rw [norm_mul, norm_mul, norm_of_nonneg (Real.exp_nonneg _),
              norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) *
            (C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by
            simp only [pow_succ, pow_zero, mul_one]
            ring
    · have h0 := (htk 0).const_mul C₀
      have h1 := (htk 1).const_mul C₁
      have h2 := (htk 2).const_mul C₂
      have h3 := (htk 3).const_mul C₃
      rw [show (0 : ℝ) = Real.exp (-c / 2) * (C₀ * 0 + C₁ * 0 + C₂ * 0 + C₃ * 0) by
        simp]
      exact (((h0.add h1).add h2).add h3).const_mul _
  -- 4. IntegrableOn
  have hint : IntegrableOn (fun u => K31 x₁ u y₁ v) (Ioi 0) := by
    show IntegrableOn (fun u =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
          Real.sin (x₁ * y₁ + u * v) +
         (-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3) *
          Real.cos (x₁ * y₁ + u * v))) (Ioi 0)
    refine (((integrableOn_pow_mul_gauss 0).const_mul
        (2 * v ^ 4 + 3 * v ^ 2 + 3)).add
      ((integrableOn_pow_mul_gauss 2).const_mul (2 * v ^ 2 + 9))).add
      ((integrableOn_pow_mul_gauss 4).const_mul 2) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) ≤
        Real.exp (-(1 / 2) * u ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
        Real.sin (x₁ * y₁ + u * v) +
       (-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3) *
        Real.cos (x₁ * y₁ + u * v))| ≤
      (2 * v ^ 4 + 3 * v ^ 2 + 3) +
      (2 * v ^ 2 + 9) * u ^ 2 + 2 * u ^ 4 := by
      calc _ ≤ |-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v| +
              |-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3| :=
            abs_sin_cos_le _ _ _
        _ ≤ _ := by
          have ha1 : |-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v|
              ≤ u ^ 4 + 2 * u ^ 2 * v ^ 2 + v ^ 4 + 3 * u ^ 2 + 3 * v ^ 2 := by
            rw [abs_le]; constructor
            · nlinarith [sq_nonneg (u ^ 2 - u * v), sq_nonneg (u * v - v ^ 2),
                sq_nonneg (u + v)]
            · nlinarith [sq_nonneg (u ^ 2 + u * v), sq_nonneg (u * v + v ^ 2),
                sq_nonneg (u - v)]
          have ha2 : |-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3|
              ≤ u ^ 4 + v ^ 4 + 6 * u ^ 2 + 3 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u ^ 2 - v ^ 2)]
          linarith
    nlinarith [Real.exp_nonneg (-(1 / 2) * u ^ 2),
      abs_nonneg ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
        Real.sin (x₁ * y₁ + u * v) +
       (-u ^ 4 + v ^ 4 + 6 * u ^ 2 - 3) *
        Real.cos (x₁ * y₁ + u * v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) (by exact hint) htend
  rw [this]
  show 0 - f 0 = _
  simp only [f, zero_pow, mul_zero, zero_mul, neg_zero, zero_add, mul_one, sub_zero,
    zero_sub, neg_mul, neg_neg]
  ring

/-- FTC: ∫_{u>0} K₂₂ du = -exp(-(x₁²+y₁²+v²)/2)·(v³-3v)·cos(x₁y₁). -/
private lemma ftc_K22_u (x₁ y₁ v : ℝ) :
    ∫ u in Ioi (0 : ℝ), K22 x₁ u y₁ v =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - 3 * v) * Real.cos (x₁ * y₁)) := by
  -- Antiderivative: f(u) = exp(Q)·((u³+uv²-u)·sin(L)+(u²v+v³-3v)·cos(L))
  set f := fun u : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((u ^ 3 + u * v ^ 2 - u) * Real.sin (x₁ * y₁ + u * v) +
     (u ^ 2 * v + v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v))
  -- 1. HasDerivAt: f'(u) = K22(x₁,u,y₁,v)
  have hd : ∀ u : ℝ, HasDerivAt f (K22 x₁ u y₁ v) u := by
    intro u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- HasDerivAt for amplitude a(u) = u³+uv²-u, a'(u) = 3u²+v²-1
    have ha : HasDerivAt (fun u => u ^ 3 + u * v ^ 2 - u)
        (3 * u ^ 2 + v ^ 2 - 1) u := by
      have hid := hasDerivAt_id u
      have h_u3 := hid.mul (hid.mul hid)
      have h_rest := hid.const_mul (v ^ 2 - 1)
      have h_sum := h_u3.add h_rest
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    -- HasDerivAt for amplitude b(u) = u²v+v³-3v, b'(u) = 2uv
    have hb : HasDerivAt (fun u => u ^ 2 * v + v ^ 3 - 3 * v)
        (2 * u * v) u := by
      have hid := hasDerivAt_id u
      have h_u2 := hid.mul hid
      have h_scaled := h_u2.const_mul v
      have h_const : HasDerivAt (fun _ : ℝ => v ^ 3 - 3 * v) 0 u := hasDerivAt_const u _
      have h_sum := h_scaled.add h_const
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    have step := hasDerivAt_expQ_sincos_amp hQ hL ha hb
    have heq : f = fun η => Real.exp ((fun u => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) η) *
        ((fun u => u ^ 3 + u * v ^ 2 - u) η *
          Real.sin ((fun u => x₁ * y₁ + u * v) η) +
         (fun u => u ^ 2 * v + v ^ 3 - 3 * v) η *
          Real.cos ((fun u => x₁ * y₁ + u * v) η)) := by
      ext; dsimp
    exact (hasDerivAt_of_funEq step heq).congr_deriv (by unfold K22; ring)
  -- 2. ContinuousWithinAt at 0
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((u ^ 3 + u * v ^ 2 - u) * Real.sin (x₁ * y₁ + u * v) +
       (u ^ 2 * v + v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- 3. Tendsto at ∞
  have htend : Tendsto f atTop (nhds 0) := by
    set c := x₁ ^ 2 + y₁ ^ 2 + v ^ 2
    have hexp_factor : ∀ u, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) := by
      intro u; rw [← Real.exp_add]; congr 1; show _ = -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 + _; ring
    have htk : ∀ (k : ℕ), Tendsto (fun u : ℝ => |u| ^ k * Real.exp (-(1/2) * u ^ 2))
        atTop (nhds 0) := by
      intro k
      exact ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (show (0:ℝ) < 1/2 by positivity) k).mono_left
        atTop_le_cocompact).congr' (eventually_atTop.mpr
        ⟨0, fun u hu => by simp [rpow_natCast, abs_of_nonneg hu]⟩)
    set C₀ := |v| ^ 3 + 3 * |v| with hC₀_def
    set C₁ := v ^ 2 + 1 with hC₁_def
    set C₂ := |v| with hC₂_def
    set C₃ := (1 : ℝ) with hC₃_def
    apply squeeze_zero_norm (a := fun u =>
      Real.exp (-c / 2) * (C₀ * (|u| ^ 0 * Real.exp (-(1/2) * u ^ 2)) +
                            C₁ * (|u| ^ 1 * Real.exp (-(1/2) * u ^ 2)) +
                            C₂ * (|u| ^ 2 * Real.exp (-(1/2) * u ^ 2)) +
                            C₃ * (|u| ^ 3 * Real.exp (-(1/2) * u ^ 2))))
    · intro u; simp only [f]
      rw [hexp_factor]
      have hB : ‖(u ^ 3 + u * v ^ 2 - u) * Real.sin (x₁ * y₁ + u * v) +
          (u ^ 2 * v + v ^ 3 - 3 * v) * Real.cos (x₁ * y₁ + u * v)‖ ≤
          C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3 := by
        calc ‖_‖ ≤ |u ^ 3 + u * v ^ 2 - u| +
            |u ^ 2 * v + v ^ 3 - 3 * v| := abs_sin_cos_le _ _ _
          _ ≤ _ := by
            have hav := abs_nonneg v
            have hau := abs_nonneg u
            have h1 : |u ^ 3 + u * v ^ 2 - u| ≤ |u| ^ 3 + (v ^ 2 + 1) * |u| := by
              rw [show u ^ 3 + u * v ^ 2 - u = u * (u ^ 2 + v ^ 2 - 1) from by ring]
              calc |u * (u ^ 2 + v ^ 2 - 1)| = |u| * |u ^ 2 + v ^ 2 - 1| := abs_mul _ _
                _ ≤ |u| * (u ^ 2 + v ^ 2 + 1) := by
                  apply mul_le_mul_of_nonneg_left _ hau
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |u| ^ 3 + (v ^ 2 + 1) * |u| := by nlinarith [sq_abs u]
            have h2 : |u ^ 2 * v + v ^ 3 - 3 * v| ≤ |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by
              rw [show u ^ 2 * v + v ^ 3 - 3 * v = v * (u ^ 2 + v ^ 2 - 3) from by ring]
              calc |v * (u ^ 2 + v ^ 2 - 3)| = |v| * |u ^ 2 + v ^ 2 - 3| := abs_mul _ _
                _ ≤ |v| * (u ^ 2 + v ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hav
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by nlinarith [sq_abs u, sq_abs v]
            have hsau : |u| ^ 2 = u ^ 2 := sq_abs u
            linarith
      calc ‖Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * _‖
          = Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * ‖_‖ := by
            rw [norm_mul, norm_mul, norm_of_nonneg (Real.exp_nonneg _),
              norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) *
            (C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by
            simp only [pow_succ, pow_zero, mul_one]
            ring
    · have h0 := (htk 0).const_mul C₀
      have h1 := (htk 1).const_mul C₁
      have h2 := (htk 2).const_mul C₂
      have h3 := (htk 3).const_mul C₃
      rw [show (0 : ℝ) = Real.exp (-c / 2) * (C₀ * 0 + C₁ * 0 + C₂ * 0 + C₃ * 0) by
        simp]
      exact (((h0.add h1).add h2).add h3).const_mul _
  -- 4. IntegrableOn
  have hint : IntegrableOn (fun u => K22 x₁ u y₁ v) (Ioi 0) := by
    show IntegrableOn (fun u =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1) *
          Real.sin (x₁ * y₁ + u * v) +
         (4 * u * v) *
          Real.cos (x₁ * y₁ + u * v))) (Ioi 0)
    refine (((integrableOn_pow_mul_gauss 0).const_mul
        (v ^ 4 + 6 * v ^ 2 + 1)).add
      ((integrableOn_pow_mul_gauss 2).const_mul (2 * v ^ 2 + 6))).add
      ((integrableOn_pow_mul_gauss 4).const_mul 1) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) ≤
        Real.exp (-(1 / 2) * u ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1) *
        Real.sin (x₁ * y₁ + u * v) +
       (4 * u * v) *
        Real.cos (x₁ * y₁ + u * v))| ≤
      (v ^ 4 + 6 * v ^ 2 + 1) +
      (2 * v ^ 2 + 6) * u ^ 2 + 1 * u ^ 4 := by
      calc _ ≤ |-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1| +
              |4 * u * v| :=
            abs_sin_cos_le _ _ _
        _ ≤ _ := by
          have ha1 : |-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1|
              ≤ u ^ 4 + 2 * u ^ 2 * v ^ 2 + v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 + 1 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u ^ 2 + v ^ 2)]
          have ha2 : |4 * u * v| ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u - v), sq_nonneg (u + v)]
          linarith
    nlinarith [Real.exp_nonneg (-(1 / 2) * u ^ 2),
      abs_nonneg ((-u ^ 4 - 2 * u ^ 2 * v ^ 2 - v ^ 4 + 4 * u ^ 2 + 4 * v ^ 2 - 1) *
        Real.sin (x₁ * y₁ + u * v) +
       (4 * u * v) *
        Real.cos (x₁ * y₁ + u * v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) (by exact hint) htend
  rw [this]
  show 0 - f 0 = _
  simp only [f, zero_pow, mul_zero, zero_mul, neg_zero, zero_add, mul_one, sub_zero,
    zero_sub, neg_mul, neg_neg]
  ring

/-- FTC: ∫_{u>0} K₁₃ du = exp(-(x₁²+y₁²+v²)/2)·(v³-3v)·sin(x₁y₁). -/
private lemma ftc_K13_u (x₁ y₁ v : ℝ) :
    ∫ u in Ioi (0 : ℝ), K13 x₁ u y₁ v =
    Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - 3 * v) * Real.sin (x₁ * y₁)) := by
  -- Antiderivative: f(u) = exp(Q)·((-v³+3u²v+3v)·sin(L)+(3uv²-u³-3u)·cos(L))
  set f := fun u : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
     (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
  -- 1. HasDerivAt: f'(u) = K13(x₁,u,y₁,v)
  have hd : ∀ u : ℝ, HasDerivAt f (K13 x₁ u y₁ v) u := by
    intro u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- HasDerivAt for amplitude a(u) = -v³+3u²v+3v, a'(u) = 6uv
    have ha : HasDerivAt (fun u => -v ^ 3 + 3 * u ^ 2 * v + 3 * v)
        (6 * u * v) u := by
      have hid := hasDerivAt_id u
      have h_u2 := hid.mul hid
      have h_scaled := h_u2.const_mul (3 * v)
      have h_const : HasDerivAt (fun _ : ℝ => -v ^ 3 + 3 * v) 0 u := hasDerivAt_const u _
      have h_sum := h_scaled.add h_const
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    -- HasDerivAt for amplitude b(u) = 3uv²-u³-3u, b'(u) = 3v²-3u²-3
    have hb : HasDerivAt (fun u => 3 * u * v ^ 2 - u ^ 3 - 3 * u)
        (3 * v ^ 2 - 3 * u ^ 2 - 3) u := by
      have hid := hasDerivAt_id u
      have h_u3 := hid.mul (hid.mul hid)
      have h_lin := hid.const_mul (3 * v ^ 2 - 3)
      have h_sum := h_lin.sub h_u3
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext u; simp [id]; ring
    have step := hasDerivAt_expQ_sincos_amp hQ hL ha hb
    have heq : f = fun η => Real.exp ((fun u => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) η) *
        ((fun u => -v ^ 3 + 3 * u ^ 2 * v + 3 * v) η *
          Real.sin ((fun u => x₁ * y₁ + u * v) η) +
         (fun u => 3 * u * v ^ 2 - u ^ 3 - 3 * u) η *
          Real.cos ((fun u => x₁ * y₁ + u * v) η)) := by
      ext; dsimp
    exact (hasDerivAt_of_funEq step heq).congr_deriv (by unfold K13; ring)
  -- 2. ContinuousWithinAt at 0
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
       (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- 3. Tendsto at ∞
  have htend : Tendsto f atTop (nhds 0) := by
    set c := x₁ ^ 2 + y₁ ^ 2 + v ^ 2
    have hexp_factor : ∀ u, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) := by
      intro u; rw [← Real.exp_add]; congr 1; show _ = -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 + _; ring
    have htk : ∀ (k : ℕ), Tendsto (fun u : ℝ => |u| ^ k * Real.exp (-(1/2) * u ^ 2))
        atTop (nhds 0) := by
      intro k
      exact ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (show (0:ℝ) < 1/2 by positivity) k).mono_left
        atTop_le_cocompact).congr' (eventually_atTop.mpr
        ⟨0, fun u hu => by simp [rpow_natCast, abs_of_nonneg hu]⟩)
    set C₀ := |v| ^ 3 + 3 * |v| with hC₀_def
    set C₁ := 3 * v ^ 2 + 3 with hC₁_def
    set C₂ := 3 * |v| with hC₂_def
    set C₃ := (1 : ℝ) with hC₃_def
    apply squeeze_zero_norm (a := fun u =>
      Real.exp (-c / 2) * (C₀ * (|u| ^ 0 * Real.exp (-(1/2) * u ^ 2)) +
                            C₁ * (|u| ^ 1 * Real.exp (-(1/2) * u ^ 2)) +
                            C₂ * (|u| ^ 2 * Real.exp (-(1/2) * u ^ 2)) +
                            C₃ * (|u| ^ 3 * Real.exp (-(1/2) * u ^ 2))))
    · intro u; simp only [f]
      rw [hexp_factor]
      have hB : ‖(-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
          (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v)‖ ≤
          C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3 := by
        calc ‖_‖ ≤ |-v ^ 3 + 3 * u ^ 2 * v + 3 * v| +
            |3 * u * v ^ 2 - u ^ 3 - 3 * u| := abs_sin_cos_le _ _ _
          _ ≤ _ := by
            have hav := abs_nonneg v
            have hau := abs_nonneg u
            have h1 : |-v ^ 3 + 3 * u ^ 2 * v + 3 * v| ≤ 3 * |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by
              rw [show -v ^ 3 + 3 * u ^ 2 * v + 3 * v = v * (-v ^ 2 + 3 * u ^ 2 + 3) from by ring]
              calc |v * (-v ^ 2 + 3 * u ^ 2 + 3)| = |v| * |-v ^ 2 + 3 * u ^ 2 + 3| := abs_mul _ _
                _ ≤ |v| * (3 * u ^ 2 + v ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hav
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = 3 * |v| * |u| ^ 2 + (|v| ^ 3 + 3 * |v|) := by nlinarith [sq_abs u, sq_abs v]
            have h2 : |3 * u * v ^ 2 - u ^ 3 - 3 * u| ≤ |u| ^ 3 + (3 * v ^ 2 + 3) * |u| := by
              rw [show 3 * u * v ^ 2 - u ^ 3 - 3 * u = u * (3 * v ^ 2 - u ^ 2 - 3) from by ring]
              calc |u * (3 * v ^ 2 - u ^ 2 - 3)| = |u| * |3 * v ^ 2 - u ^ 2 - 3| := abs_mul _ _
                _ ≤ |u| * (3 * v ^ 2 + u ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hau
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = |u| ^ 3 + (3 * v ^ 2 + 3) * |u| := by nlinarith [sq_abs u]
            have hsau : |u| ^ 2 = u ^ 2 := sq_abs u
            linarith
      calc ‖Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * _‖
          = Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) * ‖_‖ := by
            rw [norm_mul, norm_mul, norm_of_nonneg (Real.exp_nonneg _),
              norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-c / 2) * Real.exp (-(1 / 2) * u ^ 2) *
            (C₀ + C₁ * |u| + C₂ * |u| ^ 2 + C₃ * |u| ^ 3) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by
            simp only [pow_succ, pow_zero, mul_one]
            ring
    · have h0 := (htk 0).const_mul C₀
      have h1 := (htk 1).const_mul C₁
      have h2 := (htk 2).const_mul C₂
      have h3 := (htk 3).const_mul C₃
      rw [show (0 : ℝ) = Real.exp (-c / 2) * (C₀ * 0 + C₁ * 0 + C₂ * 0 + C₃ * 0) by
        simp]
      exact (((h0.add h1).add h2).add h3).const_mul _
  -- 4. IntegrableOn
  have hint : IntegrableOn (fun u => K13 x₁ u y₁ v) (Ioi 0) := by
    show IntegrableOn (fun u =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
          Real.sin (x₁ * y₁ + u * v) +
         (u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3) *
          Real.cos (x₁ * y₁ + u * v))) (Ioi 0)
    refine (((integrableOn_pow_mul_gauss 0).const_mul
        (2 * v ^ 4 + 9 * v ^ 2 + 3)).add
      ((integrableOn_pow_mul_gauss 2).const_mul (2 * v ^ 2 + 3))).add
      ((integrableOn_pow_mul_gauss 4).const_mul 2) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) ≤
        Real.exp (-(1 / 2) * u ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
        Real.sin (x₁ * y₁ + u * v) +
       (u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3) *
        Real.cos (x₁ * y₁ + u * v))| ≤
      (2 * v ^ 4 + 9 * v ^ 2 + 3) +
      (2 * v ^ 2 + 3) * u ^ 2 + 2 * u ^ 4 := by
      calc _ ≤ |-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v| +
              |u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3| :=
            abs_sin_cos_le _ _ _
        _ ≤ _ := by
          have ha1 : |-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v|
              ≤ u ^ 4 + 2 * u ^ 2 * v ^ 2 + v ^ 4 + 3 * u ^ 2 + 3 * v ^ 2 := by
            rw [abs_le]; constructor
            · nlinarith [sq_nonneg (u ^ 2 - u * v), sq_nonneg (u * v - v ^ 2),
                sq_nonneg (u + v)]
            · nlinarith [sq_nonneg (u ^ 2 + u * v), sq_nonneg (u * v + v ^ 2),
                sq_nonneg (u - v)]
          have ha2 : |u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3|
              ≤ u ^ 4 + v ^ 4 + 6 * v ^ 2 + 3 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u ^ 2 - v ^ 2)]
          linarith
    nlinarith [Real.exp_nonneg (-(1 / 2) * u ^ 2),
      abs_nonneg ((-2 * u ^ 3 * v - 2 * u * v ^ 3 + 6 * u * v) *
        Real.sin (x₁ * y₁ + u * v) +
       (u ^ 4 - v ^ 4 + 6 * v ^ 2 - 3) *
        Real.cos (x₁ * y₁ + u * v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) (by exact hint) htend
  rw [this]
  show 0 - f 0 = _
  simp only [f, zero_pow, mul_zero, zero_mul, neg_zero, zero_add, mul_one, sub_zero,
    zero_sub, neg_mul, neg_neg]
  ring

/-- FTC: ∫_{v>0} K₀₄ dv = exp(-(x₁²+u²+y₁²)/2)·(u³+3u)·cos(x₁y₁). -/
private lemma ftc_K04_v (x₁ y₁ u : ℝ) :
    ∫ v in Ioi (0 : ℝ), K04 x₁ u y₁ v =
    Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2) *
      ((u ^ 3 + 3 * u) * Real.cos (x₁ * y₁)) := by
  -- Antiderivative w.r.t. v: f(v) = exp(Q)·((-v³+3u²v+3v)·sin(L)+(3uv²-u³-3u)·cos(L))
  set f := fun v : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    ((-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
     (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
  -- 1. HasDerivAt: f'(v) = K04(x₁,u,y₁,v)
  have hd : ∀ v : ℝ, HasDerivAt f (K04 x₁ u y₁ v) v := by
    intro v
    -- Q(v) = -(x₁²+u²+y₁²+(0+v·1)²)/2, integrate w.r.t. v
    have hQ := hasDerivAt_Q u 0 x₁ y₁ 0 1 v
    have hL := hasDerivAt_L u 0 x₁ y₁ 0 1 v
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- Need to rewrite Q to match: -(x₁²+u²+y₁²+v²)/2
    have hQ' : HasDerivAt (fun v => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) (-v) v := by
      exact hasDerivAt_of_funEq (hQ.congr_deriv (by ring)) (by ext v; ring)
    -- L(v) = x₁y₁ + u·v
    have hL' : HasDerivAt (fun v => x₁ * y₁ + u * v) u v := by
      exact hasDerivAt_of_funEq (hL.congr_deriv (by ring)) (by ext v; ring)
    -- HasDerivAt for amplitude a(v) = -v³+3u²v+3v, a'(v) = -3v²+3u²+3
    have ha : HasDerivAt (fun v => -v ^ 3 + 3 * u ^ 2 * v + 3 * v)
        (-3 * v ^ 2 + 3 * u ^ 2 + 3) v := by
      have hid := hasDerivAt_id v
      have h_v3 := hid.mul (hid.mul hid)
      have h_neg_v3 := h_v3.neg
      have h_rest := hid.const_mul (3 * u ^ 2 + 3)
      have h_sum := h_neg_v3.add h_rest
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext v; simp [id]; ring
    -- HasDerivAt for amplitude b(v) = 3uv²-u³-3u, b'(v) = 6uv
    have hb : HasDerivAt (fun v => 3 * u * v ^ 2 - u ^ 3 - 3 * u)
        (6 * u * v) v := by
      have hid := hasDerivAt_id v
      have h_v2 := hid.mul hid
      have h_scaled := h_v2.const_mul (3 * u)
      have h_const : HasDerivAt (fun _ : ℝ => -(u ^ 3) - 3 * u) 0 v := hasDerivAt_const v _
      have h_sum := h_scaled.add h_const
      refine hasDerivAt_of_funEq (h_sum.congr_deriv ?_) ?_
      · simp [id]; ring
      · ext v; simp [id]; ring
    have step := hasDerivAt_expQ_sincos_amp hQ' hL' ha hb
    have heq : f = fun η => Real.exp ((fun v => -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) η) *
        ((fun v => -v ^ 3 + 3 * u ^ 2 * v + 3 * v) η *
          Real.sin ((fun v => x₁ * y₁ + u * v) η) +
         (fun v => 3 * u * v ^ 2 - u ^ 3 - 3 * u) η *
          Real.cos ((fun v => x₁ * y₁ + u * v) η)) := by
      ext; dsimp
    exact (hasDerivAt_of_funEq step heq).congr_deriv (by unfold K04; ring)
  -- 2. ContinuousWithinAt at 0
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun v => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
       (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- 3. Tendsto at ∞
  have htend : Tendsto f atTop (nhds 0) := by
    set c := x₁ ^ 2 + u ^ 2 + y₁ ^ 2
    have hexp_factor : ∀ v, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-c / 2) * Real.exp (-(1 / 2) * v ^ 2) := by
      intro v; rw [← Real.exp_add]; congr 1; show _ = -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2 + _; ring
    have htk : ∀ (k : ℕ), Tendsto (fun v : ℝ => |v| ^ k * Real.exp (-(1/2) * v ^ 2))
        atTop (nhds 0) := by
      intro k
      exact ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (show (0:ℝ) < 1/2 by positivity) k).mono_left
        atTop_le_cocompact).congr' (eventually_atTop.mpr
        ⟨0, fun v hv => by simp [rpow_natCast, abs_of_nonneg hv]⟩)
    set C₀ := |u| ^ 3 + 3 * |u| with hC₀_def
    set C₁ := 3 * u ^ 2 + 3 with hC₁_def
    set C₂ := 3 * |u| with hC₂_def
    set C₃ := (1 : ℝ) with hC₃_def
    apply squeeze_zero_norm (a := fun v =>
      Real.exp (-c / 2) * (C₀ * (|v| ^ 0 * Real.exp (-(1/2) * v ^ 2)) +
                            C₁ * (|v| ^ 1 * Real.exp (-(1/2) * v ^ 2)) +
                            C₂ * (|v| ^ 2 * Real.exp (-(1/2) * v ^ 2)) +
                            C₃ * (|v| ^ 3 * Real.exp (-(1/2) * v ^ 2))))
    · intro v; simp only [f]
      rw [hexp_factor]
      have hB : ‖(-v ^ 3 + 3 * u ^ 2 * v + 3 * v) * Real.sin (x₁ * y₁ + u * v) +
          (3 * u * v ^ 2 - u ^ 3 - 3 * u) * Real.cos (x₁ * y₁ + u * v)‖ ≤
          C₀ + C₁ * |v| + C₂ * |v| ^ 2 + C₃ * |v| ^ 3 := by
        calc ‖_‖ ≤ |-v ^ 3 + 3 * u ^ 2 * v + 3 * v| +
            |3 * u * v ^ 2 - u ^ 3 - 3 * u| := abs_sin_cos_le _ _ _
          _ ≤ _ := by
            have hav := abs_nonneg v
            have hau := abs_nonneg u
            have h1 : |-v ^ 3 + 3 * u ^ 2 * v + 3 * v| ≤ |v| ^ 3 + (3 * u ^ 2 + 3) * |v| := by
              rw [show -v ^ 3 + 3 * u ^ 2 * v + 3 * v = v * (3 * u ^ 2 + 3 - v ^ 2) from by ring]
              calc |v * (3 * u ^ 2 + 3 - v ^ 2)| = |v| * |3 * u ^ 2 + 3 - v ^ 2| := abs_mul _ _
                _ ≤ |v| * (v ^ 2 + (3 * u ^ 2 + 3)) := by
                  apply mul_le_mul_of_nonneg_left _ hav
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg v, sq_nonneg u]
                _ = |v| ^ 3 + (3 * u ^ 2 + 3) * |v| := by nlinarith [sq_abs v]
            have h2 : |3 * u * v ^ 2 - u ^ 3 - 3 * u| ≤ 3 * |u| * |v| ^ 2 + (|u| ^ 3 + 3 * |u|) := by
              rw [show 3 * u * v ^ 2 - u ^ 3 - 3 * u = u * (3 * v ^ 2 - u ^ 2 - 3) from by ring]
              calc |u * (3 * v ^ 2 - u ^ 2 - 3)| = |u| * |3 * v ^ 2 - u ^ 2 - 3| := abs_mul _ _
                _ ≤ |u| * (3 * v ^ 2 + u ^ 2 + 3) := by
                  apply mul_le_mul_of_nonneg_left _ hau
                  rw [abs_le]; constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
                _ = 3 * |u| * |v| ^ 2 + (|u| ^ 3 + 3 * |u|) := by
                  nlinarith [sq_abs v, sq_abs u]
            simp only [hC₀_def, hC₁_def, hC₂_def, hC₃_def, one_mul]
            linarith
      calc ‖Real.exp (-c / 2) * Real.exp (-(1 / 2) * v ^ 2) * _‖
          = Real.exp (-c / 2) * Real.exp (-(1 / 2) * v ^ 2) * ‖_‖ := by
            rw [norm_mul, norm_mul, norm_of_nonneg (Real.exp_nonneg _),
              norm_of_nonneg (Real.exp_nonneg _)]
        _ ≤ Real.exp (-c / 2) * Real.exp (-(1 / 2) * v ^ 2) *
            (C₀ + C₁ * |v| + C₂ * |v| ^ 2 + C₃ * |v| ^ 3) :=
            mul_le_mul_of_nonneg_left hB (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by
            simp only [pow_succ, pow_zero, mul_one]
            ring
    · have h0 := (htk 0).const_mul C₀
      have h1 := (htk 1).const_mul C₁
      have h2 := (htk 2).const_mul C₂
      have h3 := (htk 3).const_mul C₃
      rw [show (0 : ℝ) = Real.exp (-c / 2) * (C₀ * 0 + C₁ * 0 + C₂ * 0 + C₃ * 0) by
        simp]
      exact (((h0.add h1).add h2).add h3).const_mul _
  -- 4. IntegrableOn
  have hint : IntegrableOn (fun v => K04 x₁ u y₁ v) (Ioi 0) := by
    show IntegrableOn (fun v =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3) *
          Real.sin (x₁ * y₁ + u * v) +
         (4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v) *
          Real.cos (x₁ * y₁ + u * v))) (Ioi 0)
    refine (((integrableOn_pow_mul_gauss 0).const_mul
        (3 * u ^ 4 + 12 * u ^ 2 + 3)).add
      ((integrableOn_pow_mul_gauss 2).const_mul (10 * u ^ 2 + 12))).add
      ((integrableOn_pow_mul_gauss 4).const_mul 3) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    rw [mem_Ioi] at hv
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) ≤
        Real.exp (-(1 / 2) * v ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x₁, sq_nonneg u, sq_nonneg y₁])
    have hB : |((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3) *
        Real.sin (x₁ * y₁ + u * v) +
       (4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v) *
        Real.cos (x₁ * y₁ + u * v))| ≤
      (3 * u ^ 4 + 12 * u ^ 2 + 3) +
      (10 * u ^ 2 + 12) * v ^ 2 + 3 * v ^ 4 := by
      calc _ ≤ |u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3| +
              |4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v| :=
            abs_sin_cos_le _ _ _
        _ ≤ _ := by
          have hsu := sq_nonneg u
          have hsv := sq_nonneg v
          have ha1 : |u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3|
              ≤ u ^ 4 + 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 + 6 * v ^ 2 + 3 :=
            abs_le.mpr ⟨by nlinarith [sq_nonneg (u * v), sq_nonneg (u ^ 2 - v ^ 2)],
              by nlinarith⟩
          have ha2 : |4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v|
              ≤ 2 * u ^ 4 + 4 * u ^ 2 * v ^ 2 + 2 * v ^ 4 + 6 * u ^ 2 + 6 * v ^ 2 := by
            rw [abs_le]; constructor
            · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (u - v),
                sq_nonneg (u + v), sq_nonneg (u * v)]
            · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (u - v),
                sq_nonneg (u + v), sq_nonneg (u * v)]
          linarith
    nlinarith [Real.exp_nonneg (-(1 / 2) * v ^ 2),
      abs_nonneg ((u ^ 4 - 6 * u ^ 2 * v ^ 2 + v ^ 4 + 6 * u ^ 2 - 6 * v ^ 2 + 3) *
        Real.sin (x₁ * y₁ + u * v) +
       (4 * u ^ 3 * v - 4 * u * v ^ 3 + 12 * u * v) *
        Real.cos (x₁ * y₁ + u * v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun v hv => hd v) (by exact hint) htend
  rw [this]
  -- f(0) = exp(-(x₁²+u²+y₁²)/2) * (0 + (-u³-3u)·cos(x₁y₁))
  -- So 0 - f(0) = exp(...) * (u³+3u)·cos(x₁y₁)
  show 0 - f 0 = _
  simp only [f, zero_pow, mul_zero, zero_mul, neg_zero, zero_add, mul_one, sub_zero,
    zero_sub, neg_mul, neg_neg]
  ring

/-! ## Quadrant integrals

Apply FTC to inner integral, factor exp, use gaussian_Ioi_y (=1) and gaussian_Ioi_y3 (=2). -/

/-- Quadrant integral of K₄₀: 5·exp(-(x₁²+y₁²)/2)·cos(x₁y₁). -/
private lemma quadrant_integral_K40 (x₁ y₁ : ℝ) :
    ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), K40 x₁ u y₁ v =
    5 * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁) := by
  simp_rw [ftc_K40_u]
  rw [show (fun v => Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 + 3 * v) * Real.cos (x₁ * y₁))) =
    fun v => Real.cos (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
      (Real.exp (-(v ^ 2) / 2) * (v ^ 3 + 3 * v)) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul]
  rw [show (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * (v ^ 3 + 3 * v)) =
    fun v => Real.exp (-(v ^ 2) / 2) * v ^ 3 + 3 * (Real.exp (-(v ^ 2) / 2) * v) from by
      ext v; ring]
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ 3) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 3).congr_fun (fun v _ => by
      show v ^ 3 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v ^ 3
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring) measurableSet_Ioi
  have h2 : IntegrableOn (fun v : ℝ => 3 * (Real.exp (-(v ^ 2) / 2) * v)) (Ioi 0) := by
    exact ((integrableOn_pow_mul_gauss 1).congr_fun (fun v _ => by
      show v ^ 1 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring)
      measurableSet_Ioi).const_mul 3
  rw [integral_add h1 h2, integral_const_mul, gaussian_Ioi_y3, gaussian_Ioi_y]; ring

/-- Quadrant integral of K₃₁: -exp(-(x₁²+y₁²)/2)·sin(x₁y₁). -/
private lemma quadrant_integral_K31 (x₁ y₁ : ℝ) :
    ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), K31 x₁ u y₁ v =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁) := by
  simp_rw [ftc_K31_u]
  rw [show (fun v => -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - v) * Real.sin (x₁ * y₁))) =
    fun v => (-Real.sin (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(v ^ 2) / 2) * (v ^ 3 - v)) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul]
  rw [show (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * (v ^ 3 - v)) =
    fun v => Real.exp (-(v ^ 2) / 2) * v ^ 3 - Real.exp (-(v ^ 2) / 2) * v from by
      ext v; ring]
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ 3) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 3).congr_fun (fun v _ => by
      show v ^ 3 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v ^ 3
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring) measurableSet_Ioi
  have h2 : IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 1).congr_fun (fun v _ => by
      show v ^ 1 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring) measurableSet_Ioi
  rw [integral_sub h1 h2, gaussian_Ioi_y3, gaussian_Ioi_y]; ring

/-- Quadrant integral of K₂₂: exp(-(x₁²+y₁²)/2)·cos(x₁y₁). -/
private lemma quadrant_integral_K22 (x₁ y₁ : ℝ) :
    ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), K22 x₁ u y₁ v =
    Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁) := by
  simp_rw [ftc_K22_u]
  rw [show (fun v => -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - 3 * v) * Real.cos (x₁ * y₁))) =
    fun v => (-Real.cos (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(v ^ 2) / 2) * (v ^ 3 - 3 * v)) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul]
  rw [show (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * (v ^ 3 - 3 * v)) =
    fun v => Real.exp (-(v ^ 2) / 2) * v ^ 3 - 3 * (Real.exp (-(v ^ 2) / 2) * v) from by
      ext v; ring]
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ 3) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 3).congr_fun (fun v _ => by
      show v ^ 3 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v ^ 3
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring) measurableSet_Ioi
  have h2 : IntegrableOn (fun v : ℝ => 3 * (Real.exp (-(v ^ 2) / 2) * v)) (Ioi 0) := by
    exact ((integrableOn_pow_mul_gauss 1).congr_fun (fun v _ => by
      show v ^ 1 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring)
      measurableSet_Ioi).const_mul 3
  rw [integral_sub h1 h2, integral_const_mul, gaussian_Ioi_y3, gaussian_Ioi_y]; ring

/-- Quadrant integral of K₁₃: -exp(-(x₁²+y₁²)/2)·sin(x₁y₁). -/
private lemma quadrant_integral_K13 (x₁ y₁ : ℝ) :
    ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), K13 x₁ u y₁ v =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁) := by
  simp_rw [ftc_K13_u]
  rw [show (fun v => Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      ((v ^ 3 - 3 * v) * Real.sin (x₁ * y₁))) =
    fun v => (Real.sin (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(v ^ 2) / 2) * (v ^ 3 - 3 * v)) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul]
  rw [show (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * (v ^ 3 - 3 * v)) =
    fun v => Real.exp (-(v ^ 2) / 2) * v ^ 3 - 3 * (Real.exp (-(v ^ 2) / 2) * v) from by
      ext v; ring]
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ 3) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 3).congr_fun (fun v _ => by
      show v ^ 3 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v ^ 3
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring) measurableSet_Ioi
  have h2 : IntegrableOn (fun v : ℝ => 3 * (Real.exp (-(v ^ 2) / 2) * v)) (Ioi 0) := by
    exact ((integrableOn_pow_mul_gauss 1).congr_fun (fun v _ => by
      show v ^ 1 * Real.exp (-(1 / 2) * v ^ 2) = Real.exp (-(v ^ 2) / 2) * v
      rw [show -(v ^ 2) / 2 = -(1 / 2) * v ^ 2 from by ring]; ring)
      measurableSet_Ioi).const_mul 3
  rw [integral_sub h1 h2, integral_const_mul, gaussian_Ioi_y3, gaussian_Ioi_y]; ring

/-- Quadrant integral of K₀₄: 5·exp(-(x₁²+y₁²)/2)·cos(x₁y₁).
Note: u-outer, v-inner (like Kvv in D2). -/
private lemma quadrant_integral_K04 (x₁ y₁ : ℝ) :
    ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), K04 x₁ u y₁ v =
    5 * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁) := by
  simp_rw [ftc_K04_v]
  rw [show (fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2) *
      ((u ^ 3 + 3 * u) * Real.cos (x₁ * y₁))) =
    fun u => Real.cos (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
      (Real.exp (-(u ^ 2) / 2) * (u ^ 3 + 3 * u)) from by
      ext u; rw [show -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(u ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul]
  rw [show (fun u : ℝ => Real.exp (-(u ^ 2) / 2) * (u ^ 3 + 3 * u)) =
    fun u => Real.exp (-(u ^ 2) / 2) * u ^ 3 + 3 * (Real.exp (-(u ^ 2) / 2) * u) from by
      ext u; ring]
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2) / 2) * u ^ 3) (Ioi 0) := by
    exact (integrableOn_pow_mul_gauss 3).congr_fun (fun u _ => by
      show u ^ 3 * Real.exp (-(1 / 2) * u ^ 2) = Real.exp (-(u ^ 2) / 2) * u ^ 3
      rw [show -(u ^ 2) / 2 = -(1 / 2) * u ^ 2 from by ring]; ring) measurableSet_Ioi
  have h2 : IntegrableOn (fun u : ℝ => 3 * (Real.exp (-(u ^ 2) / 2) * u)) (Ioi 0) := by
    exact ((integrableOn_pow_mul_gauss 1).congr_fun (fun u _ => by
      show u ^ 1 * Real.exp (-(1 / 2) * u ^ 2) = Real.exp (-(u ^ 2) / 2) * u
      rw [show -(u ^ 2) / 2 = -(1 / 2) * u ^ 2 from by ring]; ring)
      measurableSet_Ioi).const_mul 3
  rw [integral_add h1 h2, integral_const_mul, gaussian_Ioi_y3, gaussian_Ioi_y]; ring

/-! ## Boundary integral evaluation

After quadrant integrals, the inner (u,v) integral for fixed (x₁,y₁) gives:
  exp(-(x₁²+y₁²)/2) · [(5h⁴+6h²g²+5g⁴)·cos(x₁y₁) - (4h³g+4hg³)·sin(x₁y₁)]

This integrates over (x₁,y₁) using:
- gaussian_cos_transform (inner y integral for cos terms)
- gaussian_h5_sin_transform (inner y integral for sin terms)
- lemma_4_1_eq26 (∫ h5⁴·exp(-x²))
- lemma_4_1_eq27 (∫∫ h5²h5²·exp·cos) -/

-- Helper: h5(x)^4 * exp(-x²/2) is integrable (degree-20 polynomial × Gaussian).
private lemma h5_pow4_mul_gauss_integrable :
    Integrable (fun x : ℝ => h5 x ^ 4 * Real.exp (-(x ^ 2) / 2)) volume := by
  have hC4pos : (0:ℝ) < h5_norm_const ^ 4 := pow_pos h5_norm_const_pos 4
  have heq : (fun x : ℝ => h5 x ^ 4 * Real.exp (-(x ^ 2) / 2)) =
      fun x => (1 / h5_norm_const ^ 4) *
        (h5_unnorm x ^ 4 * Real.exp (-(1/2) * x ^ 2)) := by
    ext x; simp only [h5, h5_unnorm]
    rw [show -(x ^ 2) / 2 = -(1/2) * x ^ 2 from by ring]; field_simp
  rw [heq]
  apply Integrable.const_mul
  -- Bound |h5_unnorm(x)|^4 ≤ 27(256x^20+160000x^12+50625x^4) via triangle + power mean
  have hb := fun k => integrable_pow_mul_gauss k
  have hbound : ∀ x : ℝ,
      |h5_unnorm x ^ 4 * Real.exp (-(1/2) * x ^ 2)| ≤
      (6912 * (x ^ 20 * Real.exp (-(1/2) * x ^ 2)) +
       4320000 * (x ^ 12 * Real.exp (-(1/2) * x ^ 2)) +
       1366875 * (x ^ 4 * Real.exp (-(1/2) * x ^ 2))) := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [show 6912 * (x ^ 20 * Real.exp (-(1 / 2) * x ^ 2)) +
      4320000 * (x ^ 12 * Real.exp (-(1 / 2) * x ^ 2)) +
      1366875 * (x ^ 4 * Real.exp (-(1 / 2) * x ^ 2)) =
      (6912 * x ^ 20 + 4320000 * x ^ 12 + 1366875 * x ^ 4) *
        Real.exp (-(1 / 2) * x ^ 2) from by ring]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    rw [show h5_unnorm x ^ 4 = ((4 * x ^ 5 - 20 * x ^ 3 + 15 * x) ^ 2) ^ 2 from by
      simp [h5_unnorm]; ring]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hub : |4 * x ^ 5 - 20 * x ^ 3 + 15 * x| ≤
        4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x| := by
      calc |4 * x ^ 5 - 20 * x ^ 3 + 15 * x|
          = |4 * x ^ 5 + (-(20 * x ^ 3) + 15 * x)| := by congr 1; ring
        _ ≤ |4 * x ^ 5| + |-(20 * x ^ 3) + 15 * x| := abs_add_le _ _
        _ ≤ |4 * x ^ 5| + (|-(20 * x ^ 3)| + |15 * x|) := by
            linarith [abs_add_le (-(20 * x ^ 3)) (15 * x)]
        _ = 4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x| := by
            simp [abs_mul, abs_pow, abs_neg,
              show |(4:ℝ)| = 4 from abs_of_nonneg (by norm_num),
              show |(20:ℝ)| = 20 from abs_of_nonneg (by norm_num),
              show |(15:ℝ)| = 15 from abs_of_nonneg (by norm_num)]
            ring
    have h1 : (4 * x ^ 5 - 20 * x ^ 3 + 15 * x) ^ 2 ≤
        (4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x|) ^ 2 := by
      have := abs_le.mp (show |4 * x ^ 5 - 20 * x ^ 3 + 15 * x| ≤
        4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x| from hub)
      nlinarith [this.1, this.2]
    have h2 : ((4 * x ^ 5 - 20 * x ^ 3 + 15 * x) ^ 2) ^ 2 ≤
        ((4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x|) ^ 2) ^ 2 :=
      sq_le_sq' (by nlinarith [sq_nonneg (4 * x ^ 5 - 20 * x ^ 3 + 15 * x)]) h1
    have ha := abs_nonneg x
    have h3 : ((4 * |x| ^ 5 + 20 * |x| ^ 3 + 15 * |x|) ^ 2) ^ 2 ≤
        27 * (256 * |x| ^ 20 + 160000 * |x| ^ 12 + 50625 * |x| ^ 4) := by
      nlinarith [sq_nonneg (4 * |x| ^ 5 - 20 * |x| ^ 3),
                 sq_nonneg (4 * |x| ^ 5 - 15 * |x|),
                 sq_nonneg (20 * |x| ^ 3 - 15 * |x|),
                 sq_nonneg ((4 * |x| ^ 5) ^ 2 - (20 * |x| ^ 3) ^ 2),
                 sq_nonneg ((4 * |x| ^ 5) ^ 2 - (15 * |x|) ^ 2),
                 sq_nonneg ((20 * |x| ^ 3) ^ 2 - (15 * |x|) ^ 2),
                 pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4,
                 pow_nonneg ha 5, pow_nonneg ha 6, pow_nonneg ha 7,
                 pow_nonneg ha 8, pow_nonneg ha 10, pow_nonneg ha 12,
                 pow_nonneg ha 20]
    have heven20 : |x| ^ 20 = x ^ 20 := by
      rw [show (20:ℕ) = 2 * 10 from rfl, pow_mul, sq_abs, pow_mul]
    have heven12 : |x| ^ 12 = x ^ 12 := by
      rw [show (12:ℕ) = 2 * 6 from rfl, pow_mul, sq_abs, pow_mul]
    have heven4 : |x| ^ 4 = x ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, pow_mul]
    calc ((4 * x ^ 5 - 20 * x ^ 3 + 15 * x) ^ 2) ^ 2
        ≤ 27 * (256 * |x| ^ 20 + 160000 * |x| ^ 12 + 50625 * |x| ^ 4) :=
          le_trans h2 h3
      _ = 6912 * x ^ 20 + 4320000 * x ^ 12 + 1366875 * x ^ 4 := by
          rw [heven20, heven12, heven4]; ring
  have hdom_int : Integrable (fun x : ℝ =>
      6912 * (x ^ 20 * Real.exp (-(1/2) * x ^ 2)) +
      4320000 * (x ^ 12 * Real.exp (-(1/2) * x ^ 2)) +
      1366875 * (x ^ 4 * Real.exp (-(1/2) * x ^ 2))) volume :=
    (((hb 20).const_mul 6912).add
      ((hb 12).const_mul 4320000)).add
      ((hb 4).const_mul 1366875)
    |>.congr (ae_of_all _ fun x => by simp [Pi.add_apply])
  exact hdom_int.mono'
    (by unfold h5_unnorm; fun_prop)
    (Filter.Eventually.of_forall hbound)

private lemma integral_boundary_val_D4 :
    ∫ z : ℝ × ℝ,
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
      ((5 * h5 z.1 ^ 4 + 6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 + 5 * h5 z.2 ^ 4) *
        Real.cos (z.1 * z.2) -
       (4 * h5 z.1 ^ 3 * h5 z.2 + 4 * h5 z.1 * h5 z.2 ^ 3) *
        Real.sin (z.1 * z.2)) =
    75 * Real.sqrt 2 / (32 * Real.pi) := by
  -- proof body: split into T_xy + T_yx + T_C, evaluate each via Gaussian transforms
  let T_xy : ℝ × ℝ → ℝ := fun z => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * (5 * h5 z.1 ^ 4 * Real.cos (z.1 * z.2) - 4 * h5 z.1 ^ 3 * h5 z.2 * Real.sin (z.1 * z.2))
  let T_yx : ℝ × ℝ → ℝ := fun z => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * (5 * h5 z.2 ^ 4 * Real.cos (z.1 * z.2) - 4 * h5 z.1 * h5 z.2 ^ 3 * Real.sin (z.1 * z.2))
  let T_C : ℝ × ℝ → ℝ := fun z => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * (6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 * Real.cos (z.1 * z.2))
  have hspl : (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * ((5 * h5 z.1 ^ 4 + 6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 + 5 * h5 z.2 ^ 4) * Real.cos (z.1 * z.2) - (4 * h5 z.1 ^ 3 * h5 z.2 + 4 * h5 z.1 * h5 z.2 ^ 3) * Real.sin (z.1 * z.2))) = fun z => T_xy z + T_yx z + T_C z := by ext z; simp only [T_xy, T_yx, T_C]; ring
  rw [hspl]
  have hg : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) volume := (integrable_pow_mul_gauss 0).congr (ae_of_all _ fun x => by show x ^ 0 * Real.exp (-(1 / 2) * x ^ 2) = Real.exp (-(x ^ 2) / 2); rw [pow_zero, one_mul]; congr 1; ring)
  have hint4 := h5_pow4_mul_gauss_integrable
  -- Integrability: each group dominated by products of 1D integrable functions
  have hT_xy_int : Integrable T_xy volume := by
    refine (((hint4.mul_prod hg).const_mul 8).add
      ((hg.mul_prod hint4).const_mul 1)).mono'
      (show Continuous T_xy by fun_prop).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [T_xy, Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      show -(z.1 ^ 2 + z.2 ^ 2) / 2 = -(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2 from by ring,
      Real.exp_add]
    have hb : |5 * h5 z.1 ^ 4 * Real.cos (z.1 * z.2) -
        4 * h5 z.1 ^ 3 * h5 z.2 * Real.sin (z.1 * z.2)| ≤
        8 * h5 z.1 ^ 4 + h5 z.2 ^ 4 := by
      calc _
          = |(-4 * h5 z.1 ^ 3 * h5 z.2) * Real.sin _ +
              (5 * h5 z.1 ^ 4) * Real.cos _| := by congr 1; ring
        _ ≤ |-4 * h5 z.1 ^ 3 * h5 z.2| + |5 * h5 z.1 ^ 4| := abs_sin_cos_le _ _ _
        _ ≤ 8 * h5 z.1 ^ 4 + h5 z.2 ^ 4 := by
            simp only [abs_mul, abs_neg, abs_pow, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num),
              abs_of_nonneg (show (0:ℝ) ≤ 5 by norm_num)]
            nlinarith [sq_abs (h5 z.1), sq_abs (h5 z.2),
              sq_nonneg (|h5 z.1| ^ 2 - |h5 z.1| * |h5 z.2|),
              sq_nonneg (|h5 z.1| ^ 2 - |h5 z.2| ^ 2)]
    exact le_trans (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) (le_of_eq (by ring))
  have hT_yx_int : Integrable T_yx volume := by
    refine (((hg.mul_prod hint4).const_mul 8).add
      ((hint4.mul_prod hg).const_mul 1)).mono'
      (show Continuous T_yx by fun_prop).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [T_yx, Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      show -(z.1 ^ 2 + z.2 ^ 2) / 2 = -(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2 from by ring,
      Real.exp_add]
    have hb : |5 * h5 z.2 ^ 4 * Real.cos (z.1 * z.2) -
        4 * h5 z.1 * h5 z.2 ^ 3 * Real.sin (z.1 * z.2)| ≤
        h5 z.1 ^ 4 + 8 * h5 z.2 ^ 4 := by
      calc _
          = |(-4 * h5 z.1 * h5 z.2 ^ 3) * Real.sin _ +
              (5 * h5 z.2 ^ 4) * Real.cos _| := by congr 1; ring
        _ ≤ |-4 * h5 z.1 * h5 z.2 ^ 3| + |5 * h5 z.2 ^ 4| := abs_sin_cos_le _ _ _
        _ ≤ h5 z.1 ^ 4 + 8 * h5 z.2 ^ 4 := by
            simp only [abs_mul, abs_neg, abs_pow, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num),
              abs_of_nonneg (show (0:ℝ) ≤ 5 by norm_num)]
            nlinarith [sq_abs (h5 z.1), sq_abs (h5 z.2),
              sq_nonneg (|h5 z.1| * |h5 z.2| - |h5 z.2| ^ 2),
              sq_nonneg (|h5 z.1| ^ 2 - |h5 z.2| ^ 2)]
    exact le_trans (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) (le_of_eq (by ring))
  have hT_C_int : Integrable T_C volume := by
    refine ((h5_sq_mul_gauss_integrable.mul_prod h5_sq_mul_gauss_integrable).const_mul 6).mono'
      (show Continuous T_C by fun_prop).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [T_C, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      show -(z.1 ^ 2 + z.2 ^ 2) / 2 = -(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2 from by ring,
      Real.exp_add]
    have hb : |6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 * Real.cos (z.1 * z.2)| ≤
        6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 := by
      rw [show (6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 * Real.cos (z.1 * z.2) : ℝ) =
        (6 * h5 z.1 ^ 2 * h5 z.2 ^ 2) * Real.cos (z.1 * z.2) from by ring,
        abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
    exact le_trans (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) (le_of_eq (by ring))
  -- Split integral: ∫(T_xy + T_yx + T_C) = ∫T_xy + ∫T_yx + ∫T_C
  have hsum_split : ∫ z, T_xy z + T_yx z + T_C z = (∫ z, T_xy z) + (∫ z, T_yx z) + ∫ z, T_C z := by
    have h1 : ∫ z, T_xy z + T_yx z + T_C z = (∫ z, T_xy z + T_yx z) + ∫ z, T_C z := by
      have : (fun z => T_xy z + T_yx z + T_C z) = (fun z => T_xy z + T_yx z) + T_C := by ext z; simp [Pi.add_apply]
      rw [this]; exact MeasureTheory.integral_add (hT_xy_int.add hT_yx_int) hT_C_int
    have h2 : ∫ z, T_xy z + T_yx z = (∫ z, T_xy z) + ∫ z, T_yx z := by
      have : (fun z => T_xy z + T_yx z) = T_xy + T_yx := by ext z; simp [Pi.add_apply]
      rw [this]; exact MeasureTheory.integral_add hT_xy_int hT_yx_int
    rw [h1, h2]
  rw [hsum_split]
  -- ∫ T_xy = √(2π) · ∫ h5⁴·exp(-x²): factor inner y-integral via Gaussian transforms
  have hT_xy_val : ∫ z, T_xy z = Real.sqrt (2 * Real.pi) * ∫ t : ℝ, h5 t ^ 4 * Real.exp (-t ^ 2) := by
    rw [show ∫ z, T_xy z = ∫ x : ℝ, ∫ y : ℝ, T_xy (x, y) from MeasureTheory.integral_prod T_xy hT_xy_int]; simp only [T_xy]
    have inner_eq : ∀ x : ℝ, (∫ y, Real.exp (-(x ^ 2 + y ^ 2) / 2) * (5 * h5 x ^ 4 * Real.cos (x * y) - 4 * h5 x ^ 3 * h5 y * Real.sin (x * y))) = Real.sqrt (2 * Real.pi) * h5 x ^ 4 * Real.exp (-x ^ 2) := by
      intro x
      have hfact : (fun y : ℝ => Real.exp (-(x ^ 2 + y ^ 2) / 2) * (5 * h5 x ^ 4 * Real.cos (x * y) - 4 * h5 x ^ 3 * h5 y * Real.sin (x * y))) = fun y => (5 * h5 x ^ 4 * Real.exp (-(x ^ 2) / 2)) * (Real.exp (-(y ^ 2) / 2) * Real.cos (x * y)) + (-4 * h5 x ^ 3 * Real.exp (-(x ^ 2) / 2)) * (h5 y * Real.exp (-(y ^ 2) / 2) * Real.sin (x * y)) := by ext y; rw [show -(x ^ 2 + y ^ 2) / 2 = -(x ^ 2) / 2 + -(y ^ 2) / 2 from by ring, Real.exp_add]; ring
      have hcos_int : Integrable (fun y => Real.exp (-(y ^ 2) / 2) * Real.cos (x * y)) volume := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by positivity)).mono' (by fun_prop) (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), show -(y ^ 2) / 2 = -(1 / 2) * y ^ 2 from by ring]; exact mul_le_of_le_one_right (Real.exp_nonneg _) (abs_cos_le_one _))
      have hsin_int : Integrable (fun y => h5 y * Real.exp (-(y ^ 2) / 2) * Real.sin (x * y)) volume := h5_mul_gauss_integrable.norm.mono' (by fun_prop) (ae_of_all _ fun y => by simp only [Real.norm_eq_abs]; exact le_trans (le_of_eq (abs_mul _ _)) (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)))
      rw [hfact, MeasureTheory.integral_add (hcos_int.const_mul _) (hsin_int.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, gaussian_cos_transform, gaussian_h5_sin_transform]
      have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-x ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      have hrearr : 5 * h5 x ^ 4 * Real.exp (-(x ^ 2) / 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2)) + -4 * h5 x ^ 3 * Real.exp (-(x ^ 2) / 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2) * h5 x) = Real.sqrt (2 * Real.pi) * h5 x ^ 4 * (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)) := by ring
      rw [hrearr, hexp]
    simp_rw [inner_eq]; rw [show (fun x : ℝ => Real.sqrt (2 * Real.pi) * h5 x ^ 4 * Real.exp (-x ^ 2)) = fun x => Real.sqrt (2 * Real.pi) * (h5 x ^ 4 * Real.exp (-x ^ 2)) from by ext x; ring, MeasureTheory.integral_const_mul]
  -- ∫ T_yx = √(2π) · ∫ h5⁴·exp(-x²): Fubini swap then same argument
  have hT_yx_val : ∫ z, T_yx z = Real.sqrt (2 * Real.pi) * ∫ t : ℝ, h5 t ^ 4 * Real.exp (-t ^ 2) := by
    calc ∫ z, T_yx z = ∫ y : ℝ, ∫ x : ℝ, T_yx (x, y) := (MeasureTheory.integral_prod T_yx hT_yx_int).trans (MeasureTheory.integral_integral_swap hT_yx_int)
      _ = ∫ y : ℝ, Real.sqrt (2 * Real.pi) * h5 y ^ 4 * Real.exp (-y ^ 2) := by
          congr 1; ext y; simp only [T_yx]
          have hfact : (fun x : ℝ => Real.exp (-(x ^ 2 + y ^ 2) / 2) * (5 * h5 y ^ 4 * Real.cos (x * y) - 4 * h5 x * h5 y ^ 3 * Real.sin (x * y))) = fun x => (5 * h5 y ^ 4 * Real.exp (-(y ^ 2) / 2)) * (Real.exp (-(x ^ 2) / 2) * Real.cos (y * x)) + (-4 * h5 y ^ 3 * Real.exp (-(y ^ 2) / 2)) * (h5 x * Real.exp (-(x ^ 2) / 2) * Real.sin (y * x)) := by ext x; rw [show -(x ^ 2 + y ^ 2) / 2 = -(x ^ 2) / 2 + -(y ^ 2) / 2 from by ring, Real.exp_add, show x * y = y * x from mul_comm x y]; ring
          have hcos_int : Integrable (fun x => Real.exp (-(x ^ 2) / 2) * Real.cos (y * x)) volume := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by positivity)).mono' (by fun_prop) (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), show -(x ^ 2) / 2 = -(1 / 2) * x ^ 2 from by ring]; exact mul_le_of_le_one_right (Real.exp_nonneg _) (abs_cos_le_one _))
          have hsin_int : Integrable (fun x => h5 x * Real.exp (-(x ^ 2) / 2) * Real.sin (y * x)) volume := h5_mul_gauss_integrable.norm.mono' (by fun_prop) (ae_of_all _ fun x => by simp only [Real.norm_eq_abs]; exact le_trans (le_of_eq (abs_mul _ _)) (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)))
          rw [hfact, MeasureTheory.integral_add (hcos_int.const_mul _) (hsin_int.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, gaussian_cos_transform, gaussian_h5_sin_transform]
          have hexp : Real.exp (-(y ^ 2) / 2) * Real.exp (-(y ^ 2) / 2) = Real.exp (-y ^ 2) := by rw [← Real.exp_add]; congr 1; ring
          have hrearr : 5 * h5 y ^ 4 * Real.exp (-(y ^ 2) / 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2) / 2)) + -4 * h5 y ^ 3 * Real.exp (-(y ^ 2) / 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2) / 2) * h5 y) = Real.sqrt (2 * Real.pi) * h5 y ^ 4 * (Real.exp (-(y ^ 2) / 2) * Real.exp (-(y ^ 2) / 2)) := by ring
          rw [hrearr, hexp]
      _ = Real.sqrt (2 * Real.pi) * ∫ t : ℝ, h5 t ^ 4 * Real.exp (-t ^ 2) := by rw [show (fun y : ℝ => Real.sqrt (2 * Real.pi) * h5 y ^ 4 * Real.exp (-y ^ 2)) = fun y => Real.sqrt (2 * Real.pi) * (h5 y ^ 4 * Real.exp (-y ^ 2)) from by ext y; ring, MeasureTheory.integral_const_mul]
  -- ∫ T_C = 6 · lemma_4_1_eq27
  have hT_C_val : ∫ z, T_C z = 6 * (176400 * Real.sqrt 2 * Real.pi / h5_norm_const ^ 4) := by
    simp only [T_C]; rw [show (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * (6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 * Real.cos (z.1 * z.2))) = fun z => 6 * (h5 z.1 ^ 2 * h5 z.2 ^ 2 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) * Real.cos (z.1 * z.2)) from by ext z; ring, MeasureTheory.integral_const_mul, lemma_4_1_eq27]
  -- Combine: 2·√(2π)·eq26 + 6·eq27 = 75·√2/(32·π)
  rw [hT_xy_val, hT_yx_val, hT_C_val, lemma_4_1_eq26]
  have hsqpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt (le_of_lt Real.pi_pos)
  have h2pi_eq : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := Real.sqrt_mul (le_of_lt two_pos) _
  have hC4_val : h5_norm_const ^ 4 = 14745600 * Real.pi ^ 2 := by unfold h5_norm_const; rw [show (16 * Real.sqrt (Real.pi * 15)) ^ 4 = 16 ^ 4 * (Real.sqrt (Real.pi * 15)) ^ 4 from by ring, show (Real.sqrt (Real.pi * 15)) ^ 4 = ((Real.sqrt (Real.pi * 15)) ^ 2) ^ 2 from by ring, Real.sq_sqrt (by positivity : (0:ℝ) ≤ Real.pi * 15)]; norm_num; ring
  rw [h2pi_eq, hC4_val]; field_simp; rw [show Real.sqrt Real.pi ^ 2 = Real.pi from Real.sq_sqrt (le_of_lt Real.pi_pos)]; ring

/-! ## Fubini assembly: 4D integral → 2D boundary integral → numerical value -/

private lemma integral_D4_val :
    ∫ p : P44,
      (if 0 < p.1.2 then (1 : ℝ) else 0) *
      (if 0 < p.2.2 then (1 : ℝ) else 0) * D4_val p =
    75 * Real.sqrt 2 / (32 * Real.pi) := by
  -- indicator integral helper
  have integral_if_pos : ∀ f : ℝ → ℝ,
      ∫ t : ℝ, (if 0 < t then (1 : ℝ) else 0) * f t
        = ∫ t in Set.Ioi (0 : ℝ), f t := by
    intro f
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; ext t; by_cases ht : 0 < t <;> simp [Set.indicator, ht]
  -- Integrability from Phi_integrand_dominated
  have hd4_int : Integrable (fun p => iteratedDeriv 4 (Phi_integrand · p) 0) volume := by
    obtain ⟨bound, hbound_int, hbound_le⟩ := Phi_integrand_dominated
    exact hbound_int.mono' (Phi_integrand_deriv_aestronglyMeasurable 4 0)
      (ae_of_all _ fun p => hbound_le 4 (by omega) 0 (by norm_num) p)
  have hIDD_int : Integrable (fun p : P44 =>
      (if 0 < p.1.2 then (1:ℝ) else 0) * (if 0 < p.2.2 then (1:ℝ) else 0) *
        D4_val p) volume := by
    have heq : (fun p => iteratedDeriv 4 (Phi_integrand · p) 0) =
        (fun p => 4 * ((if 0 < p.1.2 then (1:ℝ) else 0) *
          (if 0 < p.2.2 then (1:ℝ) else 0) * D4_val p)) := by
      ext p; rw [iteratedDeriv_Phi_integrand_eq, iteratedDeriv4_Phi_smooth_eq]
    rw [heq] at hd4_int
    exact (hd4_int.div_const 4).congr (ae_of_all _ fun p => by ring)
  -- σ coordinate swap: ((x₁,u),(y₁,v)) ↦ ((x₁,y₁),(u,v))
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
  -- Transform integral via σ
  rw [← hσ_vol.integral_comp σ.measurableEmbedding]
  have h_sig : ∀ q : P44,
      ((if 0 < (σ q).1.2 then (1:ℝ) else 0) * if 0 < (σ q).2.2 then (1:ℝ) else 0) *
        D4_val (σ q) =
      ((if 0 < q.2.1 then (1:ℝ) else 0) * if 0 < q.2.2 then (1:ℝ) else 0) *
        D4_val ((q.1.1, q.2.1), (q.1.2, q.2.2)) := by
    intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [hσ]
  simp_rw [h_sig]
  have hIDD_int_σ : Integrable (fun q : P44 =>
      ((if 0 < q.2.1 then (1:ℝ) else 0) * if 0 < q.2.2 then (1:ℝ) else 0) *
        D4_val ((q.1.1, q.2.1), (q.1.2, q.2.2))) volume := by
    exact (hσ_vol.integrable_comp_emb σ.measurableEmbedding).mpr hIDD_int
      |>.congr (ae_of_all _ fun q => h_sig q)
  -- Apply Fubini
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod _ hIDD_int_σ]
  -- Inner (u,v) integral = boundary function
  have h_inner : ∀ z : ℝ × ℝ,
      ∫ w : ℝ × ℝ, ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        D4_val ((z.1, w.1), (z.2, w.2)) =
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
        ((5 * h5 z.1 ^ 4 + 6 * h5 z.1 ^ 2 * h5 z.2 ^ 2 + 5 * h5 z.2 ^ 4) *
          Real.cos (z.1 * z.2) -
         (4 * h5 z.1 ^ 3 * h5 z.2 + 4 * h5 z.1 * h5 z.2 ^ 3) *
          Real.sin (z.1 * z.2)) := by
    -- This uses D4_val_eq_chain to decompose, then quadrant integrals
    -- The full proof mirrors the h_inner in integral_D2_val_zero
    intro ⟨x₁, y₁⟩
    simp only []
    -- Decompose D4_val using D4_val_eq_chain into 5 kernel terms
    have h_d4_eq : ∀ u v : ℝ,
        ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
          D4_val ((x₁, u), (y₁, v)) =
        h5 x₁ ^ 4 * ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            K40 x₁ u y₁ v +
          4 * h5 x₁ ^ 3 * h5 y₁ *
            ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            K31 x₁ u y₁ v +
          6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
            ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            K22 x₁ u y₁ v +
          4 * h5 x₁ * h5 y₁ ^ 3 *
            ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            K13 x₁ u y₁ v +
          h5 y₁ ^ 4 * ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            K04 x₁ u y₁ v := by
      intro u v
      have hchain := D4_val_eq_chain ((x₁, u), (y₁, v))
      simp only [K40, K31, K22, K13, K04] at hchain ⊢
      rw [hchain]; ring
    simp_rw [show (fun w : ℝ × ℝ => ((if 0 < w.1 then (1:ℝ) else 0) *
        if 0 < w.2 then (1:ℝ) else 0) * D4_val ((x₁, w.1), (y₁, w.2))) =
      fun w => h5 x₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) *
            if 0 < w.2 then (1:ℝ) else 0) * K40 x₁ w.1 y₁ w.2 +
          4 * h5 x₁ ^ 3 * h5 y₁ *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K31 x₁ w.1 y₁ w.2 +
          6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K22 x₁ w.1 y₁ w.2 +
          4 * h5 x₁ * h5 y₁ ^ 3 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K13 x₁ w.1 y₁ w.2 +
          h5 y₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) *
            if 0 < w.2 then (1:ℝ) else 0) * K04 x₁ w.1 y₁ w.2 from
      funext fun w => h_d4_eq w.1 w.2]
    -- 2D integrability of each indicator-weighted K-kernel
    -- Shared dominator: all kernels bounded by C*(u⁴+v⁴+u²+v²+1)*exp(-u²/2)*exp(-v²/2)
    have hg0 : Integrable (fun u : ℝ => Real.exp (-(1/2) * u ^ 2)) volume :=
      (integrable_pow_mul_gauss 0).congr (ae_of_all _ fun u => by
        show u ^ 0 * Real.exp (-(1/2) * u ^ 2) = _; rw [pow_zero, one_mul])
    have hg2 := integrable_pow_mul_gauss 2
    have hg4 := integrable_pow_mul_gauss 4
    have hdom : ∀ (c : ℝ), Integrable (fun w : ℝ × ℝ =>
        c * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1) *
        Real.exp (-(1/2) * w.1 ^ 2) * Real.exp (-(1/2) * w.2 ^ 2))
        (volume.prod volume) := by
      intro c
      exact ((((hg4.mul_prod hg0).add (hg0.mul_prod hg4)).add
        ((hg2.mul_prod hg0).add (hg0.mul_prod hg2))).add
        (hg0.mul_prod hg0)).const_mul c |>.congr
        (ae_of_all _ fun w => by simp [Pi.add_apply]; ring)
    have hexp_eq : ∀ u v : ℝ, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
        Real.exp (-(1/2) * u ^ 2) * Real.exp (-(1/2) * v ^ 2) := fun u v => by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    -- For each kernel: |ind*ind*K| ≤ |K| ≤ exp(-(x²+y²)/2) * bound(u,v) * exp(-u²/2) * exp(-v²/2)
    -- where bound(u,v) ≤ C*(u⁴+v⁴+u²+v²+1) for suitable C
    have hind_le : ∀ (a b : ℝ), |(if 0 < a then (1:ℝ) else 0)| ≤ 1 := by
      intro a b; split_ifs <;> norm_num
    -- All 5 kernels share the same integrability argument
    have hK_int : ∀ (K : ℝ → ℝ → ℝ → ℝ → ℝ), Continuous (fun w : ℝ × ℝ => K x₁ w.1 y₁ w.2) →
        (∀ u v : ℝ, |K x₁ u y₁ v| ≤ Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
          (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
          Real.exp (-(1/2) * u ^ 2) * Real.exp (-(1/2) * v ^ 2)) →
        Integrable (fun w : ℝ × ℝ =>
          (if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * K x₁ w.1 y₁ w.2))
          (volume.prod volume) := by
      intro K hcont hbound
      refine (hdom (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * 20)).mono'
        ((((measurable_const.indicator measurableSet_Ioi).comp measurable_snd).mul
          ((measurable_const.indicator measurableSet_Ioi).comp measurable_fst |>.mul
            hcont.measurable)).aestronglyMeasurable) (ae_of_all _ fun w => ?_)
      simp only [Real.norm_eq_abs]
      have h1 : |(if 0 < w.2 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have h2 : |(if 0 < w.1 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      calc |(if 0 < w.2 then (1:ℝ) else 0) * ((if 0 < w.1 then (1:ℝ) else 0) * K x₁ w.1 y₁ w.2)|
          = |(if 0 < w.2 then (1:ℝ) else 0)| * (|(if 0 < w.1 then (1:ℝ) else 0)| * |K x₁ w.1 y₁ w.2|) := by
            rw [abs_mul, abs_mul]
        _ ≤ 1 * (1 * |K x₁ w.1 y₁ w.2|) := by
            apply mul_le_mul h1 (mul_le_mul h2 le_rfl (abs_nonneg _) (by linarith))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith)
        _ = |K x₁ w.1 y₁ w.2| := by ring
        _ ≤ _ := le_trans (hbound w.1 w.2) (le_of_eq (by ring))
    -- Each kernel's absolute bound (using abs_sin_cos_le + polynomial bound)
    -- For K40-K04: |trig part| ≤ C*(u⁴+v⁴+u²+v²+1) for C ≤ 20
    have hK40_bound : ∀ u v : ℝ, |K40 x₁ u y₁ v| ≤ Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
        (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
        Real.exp (-(1/2) * u ^ 2) * Real.exp (-(1/2) * v ^ 2) := by
      intro u v; simp only [K40]; rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp_eq]
      rw [show Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.exp (-(1 / 2) * u ^ 2) *
        Real.exp (-(1 / 2) * v ^ 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ _ := abs_sin_cos_le _ _ _
        _ ≤ 20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) := by
          have := abs_nonneg u; have := abs_nonneg v
          rw [show (20 : ℝ) * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) =
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) +
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
          apply add_le_add
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)]
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)]
    have hK40_int2D := hK_int K40 (by unfold K40; fun_prop) hK40_bound
    have hK31_int2D := hK_int K31 (by unfold K31; fun_prop) (by
      intro u v; simp only [K31]; rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp_eq]
      rw [show Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.exp (-(1 / 2) * u ^ 2) *
        Real.exp (-(1 / 2) * v ^ 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ _ := abs_sin_cos_le _ _ _
        _ ≤ 20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) := by
          have := abs_nonneg u; have := abs_nonneg v
          rw [show (20 : ℝ) * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) =
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) +
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
          apply add_le_add
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)]
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)])
    have hK22_int2D := hK_int K22 (by unfold K22; fun_prop) (by
      intro u v; simp only [K22]; rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp_eq]
      rw [show Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.exp (-(1 / 2) * u ^ 2) *
        Real.exp (-(1 / 2) * v ^ 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ _ := abs_sin_cos_le _ _ _
        _ ≤ 20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) := by
          have := abs_nonneg u; have := abs_nonneg v
          rw [show (20 : ℝ) * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) =
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) +
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
          apply add_le_add
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)]
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)])
    have hK13_int2D := hK_int K13 (by unfold K13; fun_prop) (by
      intro u v; simp only [K13]; rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp_eq]
      rw [show Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.exp (-(1 / 2) * u ^ 2) *
        Real.exp (-(1 / 2) * v ^ 2) * (20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ _ := abs_sin_cos_le _ _ _
        _ ≤ 20 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) := by
          have := abs_nonneg u; have := abs_nonneg v
          rw [show (20 : ℝ) * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1) =
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) +
            (10 * (u ^ 4 + v ^ 4 + u ^ 2 + v ^ 2 + 1)) from by ring]
          apply add_le_add
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)]
          · rw [abs_le]; constructor <;>
              nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u*v), sq_nonneg (u^2-v^2),
                sq_nonneg (u-v), sq_nonneg (u+v)])
    -- K04: different indicator order (w.1 outer, w.2 inner)
    have hK04_int2D : Integrable (fun w : ℝ × ℝ =>
        (if 0 < w.1 then (1:ℝ) else 0) *
        ((if 0 < w.2 then (1:ℝ) else 0) * K04 x₁ w.1 y₁ w.2))
        (volume.prod volume) := by
      refine (hdom (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * 20)).mono'
        ((((measurable_const.indicator measurableSet_Ioi).comp measurable_fst).mul
          ((measurable_const.indicator measurableSet_Ioi).comp measurable_snd |>.mul
            (show Continuous (fun w : ℝ × ℝ => K04 x₁ w.1 y₁ w.2) by unfold K04; fun_prop).measurable)).aestronglyMeasurable) (ae_of_all _ fun w => ?_)
      simp only [Real.norm_eq_abs]
      have h1 : |(if 0 < w.1 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have h2 : |(if 0 < w.2 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have hK04_abs : |K04 x₁ w.1 y₁ w.2| ≤
          Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.exp (-(1/2) * w.1 ^ 2) *
          Real.exp (-(1/2) * w.2 ^ 2) * (20 * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1)) := by
        simp only [K04]; rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp_eq]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc _ ≤ _ := abs_sin_cos_le _ _ _
          _ ≤ 20 * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1) := by
            have := abs_nonneg w.1; have := abs_nonneg w.2
            rw [show (20 : ℝ) * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1) =
              (10 * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1)) +
              (10 * (w.1 ^ 4 + w.2 ^ 4 + w.1 ^ 2 + w.2 ^ 2 + 1)) from by ring]
            apply add_le_add
            · rw [abs_le]; constructor <;>
                nlinarith [sq_nonneg w.1, sq_nonneg w.2, sq_nonneg (w.1*w.2), sq_nonneg (w.1^2-w.2^2),
                  sq_nonneg (w.1-w.2), sq_nonneg (w.1+w.2)]
            · rw [abs_le]; constructor <;>
                nlinarith [sq_nonneg w.1, sq_nonneg w.2, sq_nonneg (w.1*w.2), sq_nonneg (w.1^2-w.2^2),
                  sq_nonneg (w.1-w.2), sq_nonneg (w.1+w.2)]
      calc _ ≤ 1 * (1 * |K04 x₁ w.1 y₁ w.2|) := by
            rw [abs_mul, abs_mul]
            have ha := abs_nonneg (K04 x₁ w.1 y₁ w.2)
            exact mul_le_mul h1 (mul_le_mul h2 le_rfl ha (by linarith))
              (mul_nonneg (abs_nonneg _) ha) (by linarith)
        _ = |K04 x₁ w.1 y₁ w.2| := by ring
        _ ≤ _ := hK04_abs
        _ = _ := by ring
    -- Compute each piece's integral
    have hK40_piece : ∫ w : ℝ × ℝ, h5 x₁ ^ 4 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K40 x₁ w.1 y₁ w.2 =
        h5 x₁ ^ 4 * (5 * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => h5 x₁ ^ 4 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          K40 x₁ w.1 y₁ w.2) =
        fun w => h5 x₁ ^ 4 * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * K40 x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hK40_int2D]
      simp only []
      congr 1
      rw [MeasureTheory.integral_integral_swap hK40_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * K40 x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * K40 x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]
      exact quadrant_integral_K40 x₁ y₁
    have hK31_piece : ∫ w : ℝ × ℝ, 4 * h5 x₁ ^ 3 * h5 y₁ *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K31 x₁ w.1 y₁ w.2 =
        4 * h5 x₁ ^ 3 * h5 y₁ * (-Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => 4 * h5 x₁ ^ 3 * h5 y₁ *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          K31 x₁ w.1 y₁ w.2) =
        fun w => 4 * h5 x₁ ^ 3 * h5 y₁ * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * K31 x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hK31_int2D]
      simp only []
      congr 1
      rw [MeasureTheory.integral_integral_swap hK31_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * K31 x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * K31 x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]
      exact quadrant_integral_K31 x₁ y₁
    have hK22_piece : ∫ w : ℝ × ℝ, 6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K22 x₁ w.1 y₁ w.2 =
        6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 * (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => 6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          K22 x₁ w.1 y₁ w.2) =
        fun w => 6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * K22 x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hK22_int2D]
      simp only []
      congr 1
      rw [MeasureTheory.integral_integral_swap hK22_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * K22 x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * K22 x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]
      exact quadrant_integral_K22 x₁ y₁
    have hK13_piece : ∫ w : ℝ × ℝ, 4 * h5 x₁ * h5 y₁ ^ 3 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K13 x₁ w.1 y₁ w.2 =
        4 * h5 x₁ * h5 y₁ ^ 3 * (-Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => 4 * h5 x₁ * h5 y₁ ^ 3 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          K13 x₁ w.1 y₁ w.2) =
        fun w => 4 * h5 x₁ * h5 y₁ ^ 3 * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * K13 x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hK13_int2D]
      simp only []
      congr 1
      rw [MeasureTheory.integral_integral_swap hK13_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * K13 x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * K13 x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]
      exact quadrant_integral_K13 x₁ y₁
    -- K04 uses u-outer, v-inner (like Kvv in D2)
    have hK04_piece : ∫ w : ℝ × ℝ, h5 y₁ ^ 4 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K04 x₁ w.1 y₁ w.2 =
        h5 y₁ ^ 4 * (5 * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => h5 y₁ ^ 4 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          K04 x₁ w.1 y₁ w.2) =
        fun w => h5 y₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) *
          ((if 0 < w.2 then (1:ℝ) else 0) * K04 x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hK04_int2D]
      simp only []
      congr 1
      rw [show (fun x : ℝ => ∫ (y : ℝ), (if 0 < x then (1:ℝ) else 0) *
            ((if 0 < y then (1:ℝ) else 0) * K04 x₁ x y₁ y)) =
          fun x => (if 0 < x then (1:ℝ) else 0) *
            ∫ (y : ℝ), (if 0 < y then (1:ℝ) else 0) * K04 x₁ x y₁ y from by
          ext x; rw [MeasureTheory.integral_const_mul]]
      rw [integral_if_pos]; simp_rw [integral_if_pos]
      exact quadrant_integral_K04 x₁ y₁
    -- Weighted integrability for integral_add
    have hK40_w_int : Integrable (fun w : ℝ × ℝ =>
        h5 x₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K40 x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hK40_int2D.const_mul (h5 x₁ ^ 4)).congr
        (ae_of_all _ fun w => by ring)
    have hK31_w_int : Integrable (fun w : ℝ × ℝ =>
        4 * h5 x₁ ^ 3 * h5 y₁ * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K31 x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hK31_int2D.const_mul (4 * h5 x₁ ^ 3 * h5 y₁)).congr
        (ae_of_all _ fun w => by ring)
    have hK22_w_int : Integrable (fun w : ℝ × ℝ =>
        6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K22 x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hK22_int2D.const_mul (6 * h5 x₁ ^ 2 * h5 y₁ ^ 2)).congr
        (ae_of_all _ fun w => by ring)
    have hK13_w_int : Integrable (fun w : ℝ × ℝ =>
        4 * h5 x₁ * h5 y₁ ^ 3 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K13 x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hK13_int2D.const_mul (4 * h5 x₁ * h5 y₁ ^ 3)).congr
        (ae_of_all _ fun w => by ring)
    have hK04_w_int : Integrable (fun w : ℝ × ℝ =>
        h5 y₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        K04 x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hK04_int2D.const_mul (h5 y₁ ^ 4)).congr
        (ae_of_all _ fun w => by ring)
    -- Re-associate integrand: left-assoc (A+B+C+D+E) → (A+(B+C))+(D+E) for integral_add
    have h_reassoc : (fun w : ℝ × ℝ =>
        h5 x₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K40 x₁ w.1 y₁ w.2 +
          4 * h5 x₁ ^ 3 * h5 y₁ *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K31 x₁ w.1 y₁ w.2 +
          6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K22 x₁ w.1 y₁ w.2 +
          4 * h5 x₁ * h5 y₁ ^ 3 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K13 x₁ w.1 y₁ w.2 +
          h5 y₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K04 x₁ w.1 y₁ w.2) =
      fun w =>
        (h5 x₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K40 x₁ w.1 y₁ w.2 +
          (4 * h5 x₁ ^ 3 * h5 y₁ *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K31 x₁ w.1 y₁ w.2 +
          6 * h5 x₁ ^ 2 * h5 y₁ ^ 2 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K22 x₁ w.1 y₁ w.2)) +
        (4 * h5 x₁ * h5 y₁ ^ 3 *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K13 x₁ w.1 y₁ w.2 +
          h5 y₁ ^ 4 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            K04 x₁ w.1 y₁ w.2) :=
      funext fun w => by ring
    rw [h_reassoc]
    -- Split integral: ∫(A+B+C+D+E) = ∫A + ∫B + ∫C + ∫D + ∫E
    have h1 := MeasureTheory.integral_add
      (hK40_w_int.add (hK31_w_int.add hK22_w_int)) (hK13_w_int.add hK04_w_int)
    simp only [Pi.add_apply] at h1
    have h2 := MeasureTheory.integral_add hK40_w_int (hK31_w_int.add hK22_w_int)
    simp only [Pi.add_apply] at h2
    have h3 := MeasureTheory.integral_add hK31_w_int hK22_w_int
    have h4 := MeasureTheory.integral_add hK13_w_int hK04_w_int
    linarith [hK40_piece, hK31_piece, hK22_piece, hK13_piece, hK04_piece]
  simp_rw [h_inner]
  exact integral_boundary_val_D4

/-! ## Final theorem -/

/-- **Φ''''(0) = 75√2/(8π)**: The fourth derivative of Φ at zero. -/
theorem Phi_iteratedDeriv4_at_zero :
    iteratedDeriv 4 Phi 0 = 75 * Real.sqrt 2 / (8 * Real.pi) := by
  rw [Phi_iteratedDeriv4_eq_integral]
  simp_rw [iteratedDeriv_Phi_integrand_eq]
  rw [MeasureTheory.integral_const_mul]
  simp_rw [iteratedDeriv4_Phi_smooth_eq]
  have h := integral_D4_val
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp at h ⊢
  linarith

end Braverman
