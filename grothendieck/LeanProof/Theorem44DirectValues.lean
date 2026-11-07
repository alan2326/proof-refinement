/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Regularity
import LeanProof.Theorem44Support
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Theorem 4.4 — Direct derivative value computation

Computes `Φ''(0) = 0` and `Φ''''(0) = 38400·√2` by evaluating the integrals
from `Phi_iteratedDeriv2_eq_integral` and `Phi_iteratedDeriv4_eq_integral`.

## Strategy

From the regularity file:
  iteratedDeriv k Phi 0 = ∫ p, iteratedDeriv k (Phi_integrand · p) 0

The integrand `Phi_integrand η p` factors as indicators × smooth part,
where the smooth part is `exp(Q(η)) · sin(L(η))` with Q, L quadratic in η.

We compute the 2nd and 4th derivatives of this explicitly at η = 0,
then evaluate the resulting 4D Gaussian integrals using the support lemmas.

## Key results

- `Phi_iteratedDeriv2_at_zero : iteratedDeriv 2 Phi 0 = 0`
- `Phi_iteratedDeriv4_at_zero : iteratedDeriv 4 Phi 0 = 38400 * √2`
-/

open Complex Set Real MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Braverman

/-! ## Step 1: Factor out indicators from the iterated derivative

Since the indicators `1_{u>0}`, `1_{v>0}` don't depend on η,
iteratedDeriv k (Phi_integrand · p) = ind · iteratedDeriv k (smooth part). -/

/-- The smooth (indicator-free) part of the shifted integrand. -/
def Phi_smooth_part (p : (ℝ × ℝ) × (ℝ × ℝ)) (η : ℝ) : ℝ :=
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 + y₁ ^ 2 + (v + η * g) ^ 2) / 2) *
    Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g))

lemma Phi_smooth_part_contDiff (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiff ℝ ⊤ (Phi_smooth_part p) := by
  unfold Phi_smooth_part; fun_prop

lemma Phi_integrand_eq_ind_smooth (η : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    Phi_integrand η p =
      4 * ((if 0 < p.1.2 then (1 : ℝ) else 0) * (if 0 < p.2.2 then (1 : ℝ) else 0) *
      Phi_smooth_part p η) := by
  unfold Phi_integrand Phi_smooth_part; ring

lemma iteratedDeriv_Phi_integrand_eq (k : ℕ) (p : (ℝ × ℝ) × (ℝ × ℝ)) (η : ℝ) :
    iteratedDeriv k (Phi_integrand · p) η =
      4 * ((if 0 < p.1.2 then (1 : ℝ) else 0) * (if 0 < p.2.2 then (1 : ℝ) else 0) *
      iteratedDeriv k (Phi_smooth_part p) η) := by
  have heq : (Phi_integrand · p) = fun η =>
      (4 * ((if 0 < p.1.2 then (1 : ℝ) else 0) * (if 0 < p.2.2 then (1 : ℝ) else 0))) *
      Phi_smooth_part p η := by
    ext η'; rw [Phi_integrand_eq_ind_smooth]; ring
  rw [heq, iteratedDeriv_const_mul _
    ((Phi_smooth_part_contDiff p).contDiffAt.of_le le_top)]
  ring

/-! ## Step 2: Compute iteratedDeriv 2 of the smooth part at η = 0

The smooth part is exp(Q(η)) · sin(L(η)) where:
  Q(η) = -(x₁² + (u+ηh)² + y₁² + (v+ηg)²) / 2
  L(η) = (x₁y₁ + (u+ηh)(v+ηg)) / 2

At η = 0:
  Q(0) = -(x₁² + u² + y₁² + v²) / 2
  Q'(0) = -(uh + vg) / 2
  Q''(0) = -(h² + g²) / 2
  L(0) = (x₁y₁ + uv) / 2
  L'(0) = (ug + vh) / 2
  L''(0) = hg

The second derivative of exp(Q)·sin(L) is:
  d²/dη²[exp(Q)·sin(L)] = exp(Q)·[(Q'²+Q''-L'²)·sin(L) + (2Q'L'+L'')·cos(L)]
-/

/-! ## Step 2a: Symmetry of the smooth part under sign flip

Key symmetry: `Phi_smooth_part ((-x₁,u),(-y₁,v)) η = Phi_smooth_part ((x₁,u),(y₁,v)) (-η)`.
This follows from `h5_odd` and the structure of Q and L.

Since Phi_smooth_part is C^∞, this gives us:
`iteratedDeriv k (Phi_smooth_part ((-x₁,u),(-y₁,v))) 0
  = (-1)^k · iteratedDeriv k (Phi_smooth_part ((x₁,u),(y₁,v))) 0`

Similarly: `Phi_smooth_part ((x₁,-u),(y₁,-v)) η = Phi_smooth_part ((x₁,u),(y₁,v)) (-η)`.
-/

/-- The smooth part satisfies: flipping signs of x₁ and y₁ is the same as negating η. -/
lemma Phi_smooth_part_neg_xy (x₁ u y₁ v η : ℝ) :
    Phi_smooth_part ((-x₁, u), (-y₁, v)) η =
    Phi_smooth_part ((x₁, u), (y₁, v)) (-η) := by
  unfold Phi_smooth_part
  simp only [h5_odd]
  ring_nf

/-- The smooth part satisfies: flipping signs of u and v is the same as negating η. -/
lemma Phi_smooth_part_neg_uv (x₁ u y₁ v η : ℝ) :
    Phi_smooth_part ((x₁, -u), (y₁, -v)) η =
    Phi_smooth_part ((x₁, u), (y₁, v)) (-η) := by
  unfold Phi_smooth_part
  simp only
  congr 1 <;> (congr 1; ring)

/-! ## Step 2b: The second derivative integrand is even in (u,v)

From `Phi_smooth_part_neg_uv`, we get that
  `iteratedDeriv 2 (Phi_smooth_part ((x₁,-u),(y₁,-v))) 0
   = iteratedDeriv 2 (Phi_smooth_part ((x₁,u),(y₁,v))) 0`

because the second derivative of f(-·) at 0 equals f''(0) (even-order chain rule). -/

/-- For an even-order iterated derivative, composing with negation doesn't change the value at 0. -/
lemma iteratedDeriv_even_neg {f : ℝ → ℝ} (k : ℕ) :
    iteratedDeriv (2 * k) (fun η => f (-η)) 0 = iteratedDeriv (2 * k) f 0 := by
  rw [iteratedDeriv_comp_neg, neg_zero, Even.neg_one_pow (even_two_mul k), one_smul]

/-! ## Step 2c: Additional symmetries of the smooth part

The smooth part is **antisymmetric** (negated) under (x₁,u) → (-x₁,-u)
or (y₁,v) → (-y₁,-v). These reflect the oddness of the sin factor
combined with the sign flips. -/

/-- Flipping signs of x₁ and u simultaneously negates the smooth part. -/
lemma Phi_smooth_part_neg_x1u (x₁ u y₁ v η : ℝ) :
    Phi_smooth_part ((-x₁, -u), (y₁, v)) η =
    -Phi_smooth_part ((x₁, u), (y₁, v)) η := by
  unfold Phi_smooth_part
  simp only [h5_odd, neg_mul, mul_neg]
  set a := x₁ * y₁
  set b := u
  set c := η * h5 x₁
  set d := v + η * h5 y₁
  rw [show -a + (-b + -c) * d = -((a + (b + c) * d)) from by ring]
  rw [Real.sin_neg]
  rw [show (-x₁) ^ 2 = x₁ ^ 2 from by ring]
  rw [show (-b + -c) ^ 2 = (b + c) ^ 2 from by ring]
  ring

/-- Flipping signs of y₁ and v simultaneously negates the smooth part. -/
lemma Phi_smooth_part_neg_y1v (x₁ u y₁ v η : ℝ) :
    Phi_smooth_part ((x₁, u), (-y₁, -v)) η =
    -Phi_smooth_part ((x₁, u), (y₁, v)) η := by
  unfold Phi_smooth_part
  simp only [h5_odd, mul_neg]
  set a := x₁ * y₁
  set b := v
  set c := η * h5 y₁
  set d := u + η * h5 x₁
  rw [show -a + d * (-b + -c) = -((a + d * (b + c))) from by ring]
  rw [Real.sin_neg]
  rw [show (-y₁) ^ 2 = y₁ ^ 2 from by ring]
  rw [show (-b + -c) ^ 2 = (b + c) ^ 2 from by ring]
  ring

/-! ## Step 3: The integral vanishes

We prove `∫ p : P44, iteratedDeriv 2 (Phi_integrand · p) 0 = 0`.

The antisymmetry `Phi_smooth_part ((-x₁,-u),(y₁,v)) = -Phi_smooth_part ((x₁,u),(y₁,v))`
implies that the second derivative `D²` is also antisymmetric:
  `D²((-x₁,-u),(y₁,v)) = -D²((x₁,u),(y₁,v))`

Similarly for the (y₁,v) variables. These antisymmetries show:
  `∫_{x₁∈ℝ, u∈ℝ} D²(x₁,u,y₁,v) = 0`  for all (y₁,v)

However, the indicator-weighted integral `∫_{u>0,v>0} D²` does NOT
vanish by antisymmetry alone, since {u>0} is not invariant under u→-u.
The vanishing requires the full integral computation:

1. Compute iteratedDeriv 2 (Phi_smooth_part p) 0 explicitly
   (product rule + chain rule for exp(Q)·sin(L))
2. Evaluate the resulting 4D Gaussian-Hermite integrals term by term:
   - Some terms vanish by the u↔v swap symmetry on (0,∞)²
   - Remaining terms cancel by the Hermite-Fourier identity
     (`gaussian_h5_sin_transform`), equation (55) in the paper

This is a genuine multi-step integral computation. -/

/-- The second derivative of Phi_smooth_part is antisymmetric under
(x₁,u) → (-x₁,-u), i.e., it negates when we flip the signs of x₁ and u. -/
lemma iteratedDeriv2_smooth_antisymm_x1u (x₁ u y₁ v : ℝ) :
    iteratedDeriv 2 (Phi_smooth_part ((-x₁, -u), (y₁, v))) 0 =
    -iteratedDeriv 2 (Phi_smooth_part ((x₁, u), (y₁, v))) 0 := by
  have heq : Phi_smooth_part ((-x₁, -u), (y₁, v)) =
      -Phi_smooth_part ((x₁, u), (y₁, v)) := by
    ext η; exact Phi_smooth_part_neg_x1u x₁ u y₁ v η
  rw [heq, iteratedDeriv_neg]

/-- The second derivative of Phi_smooth_part is antisymmetric under
(y₁,v) → (-y₁,-v), i.e., it negates when we flip the signs of y₁ and v. -/
lemma iteratedDeriv2_smooth_antisymm_y1v (x₁ u y₁ v : ℝ) :
    iteratedDeriv 2 (Phi_smooth_part ((x₁, u), (-y₁, -v))) 0 =
    -iteratedDeriv 2 (Phi_smooth_part ((x₁, u), (y₁, v))) 0 := by
  have heq : Phi_smooth_part ((x₁, u), (-y₁, -v)) =
      -Phi_smooth_part ((x₁, u), (y₁, v)) := by
    ext η; exact Phi_smooth_part_neg_y1v x₁ u y₁ v η
  rw [heq, iteratedDeriv_neg]

/-! ## HasDerivAt building blocks and analysis helpers -/

/-- Gaussian decay: `(a + |u|) * exp(-(c+u²)/2) → 0` as `u → ∞`. -/
lemma tendsto_gauss_bound (c a : ℝ) :
    Tendsto (fun u : ℝ => (a + |u|) * Real.exp (-(c + u ^ 2) / 2))
      atTop (nhds 0) := by
  have h0 : Tendsto (fun u : ℝ => Real.exp (-(1/2) * u ^ 2))
      atTop (nhds 0) :=
    ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (by positivity : (0:ℝ) < 1/2) 0).mono_left
      atTop_le_cocompact).congr (fun u => by simp)
  have h1 : Tendsto (fun u : ℝ => |u| * Real.exp (-(1/2) * u ^ 2))
      atTop (nhds 0) :=
    ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (by positivity : (0:ℝ) < 1/2) 1).mono_left
      atTop_le_cocompact).congr' (eventually_atTop.mpr
      ⟨0, fun u hu => by simp [rpow_one, abs_of_nonneg hu]⟩)
  suffices hs : Tendsto (fun u : ℝ => a * Real.exp (-(1/2) * u ^ 2) +
      |u| * Real.exp (-(1/2) * u ^ 2)) atTop (nhds 0) by
    rw [show (0:ℝ) = Real.exp (-c/2) * 0 from by ring]
    refine ((hs.const_mul (Real.exp (-c/2))).congr' ?_)
    filter_upwards with u
    show Real.exp (-c / 2) * (a * Real.exp (-(1 / 2) * u ^ 2) +
      |u| * Real.exp (-(1 / 2) * u ^ 2)) =
      (a + |u|) * Real.exp (-(c + u ^ 2) / 2)
    calc _ = (a + |u|) * (Real.exp (-c/2) * Real.exp (-(1/2) * u ^ 2)) :=
          by ring
      _ = (a + |u|) * Real.exp (-c/2 + -(1/2) * u ^ 2) := by
          rw [← Real.exp_add]
      _ = _ := by congr 1; ring
  rw [show (0:ℝ) = a * 0 + 0 from by ring]
  exact (h0.const_mul a).add h1

/-- `u^k * exp(-u²/2)` is integrable on `(0,∞)`. -/
lemma integrableOn_pow_mul_gauss (k : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-(1/2) * u ^ 2))
      (Set.Ioi 0) := by
  exact (integrableOn_rpow_mul_exp_neg_mul_sq
    (show (0:ℝ) < 1/2 by positivity)
    (show (-1:ℝ) < ↑k by linarith [Nat.cast_nonneg (α := ℝ) k])).congr_fun
    (fun u _ => by norm_cast) measurableSet_Ioi

/-- `u^k * exp(-u²/2)` is integrable on all of `ℝ`. -/
lemma integrable_pow_mul_gauss (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k * Real.exp (-(1/2) * u ^ 2)) volume :=
  (integrable_rpow_mul_exp_neg_mul_sq (show (0:ℝ) < 1/2 by positivity)
    (show (-1:ℝ) < ↑k by linarith [Nat.cast_nonneg (α := ℝ) k])).congr
    (ae_of_all _ fun u => by norm_cast)

/-- `h5(y) * exp(-y²/2)` is integrable on `ℝ` (polynomial × Gaussian). -/
lemma h5_mul_gauss_integrable :
    Integrable (fun y : ℝ => h5 y * Real.exp (-(y ^ 2) / 2)) volume := by
  -- h5 y = (4y^5-20y^3+15y) / h5_norm_const
  -- So |h5 y * exp(-y²/2)| ≤ (4|y|^5+20|y|^3+15|y|)/h5_norm_const * exp(-y²/2)
  -- Each |y|^k * exp(-y²/2) is integrable by integrable_pow_mul_gauss
  have hb := fun k => integrable_pow_mul_gauss k
  -- Combine using linearity
  have : Integrable (fun y : ℝ =>
      (4 * y ^ 5 - 20 * y ^ 3 + 15 * y) * Real.exp (-(1/2) * y ^ 2))
      volume := by
    have := ((hb 5).const_mul 4).sub ((hb 3).const_mul 20) |>.add ((hb 1).const_mul 15)
    exact this.congr (ae_of_all _ fun y => by simp [Pi.add_apply, Pi.sub_apply]; ring)
  exact (this.div_const h5_norm_const).congr (ae_of_all _ fun y => by
    simp only [h5, h5_unnorm]; ring)

/-- `h5(y)² * exp(-y²/2)` is integrable on `ℝ` (degree-10 polynomial × Gaussian). -/
lemma h5_sq_mul_gauss_integrable :
    Integrable (fun y : ℝ => h5 y ^ 2 * Real.exp (-(y ^ 2) / 2)) volume := by
  have hb := fun k => integrable_pow_mul_gauss k
  have : Integrable (fun y : ℝ =>
      (16 * y ^ 10 - 160 * y ^ 8 + 520 * y ^ 6 - 600 * y ^ 4 + 225 * y ^ 2) *
        Real.exp (-(1/2) * y ^ 2)) volume := by
    have := ((hb 10).const_mul 16).sub ((hb 8).const_mul 160)
      |>.add ((hb 6).const_mul 520)
      |>.sub ((hb 4).const_mul 600)
      |>.add ((hb 2).const_mul 225)
    exact this.congr (ae_of_all _ fun y => by simp [Pi.add_apply, Pi.sub_apply]; ring)
  exact (this.div_const (h5_norm_const ^ 2)).congr (ae_of_all _ fun y => by
    simp only [h5, h5_unnorm]; ring)

attribute [local fun_prop] h5_continuous

/-- Rewrite function form in HasDerivAt. -/
lemma hasDerivAt_of_funEq {f g : ℝ → ℝ} {f' : ℝ} {x : ℝ}
    (h : HasDerivAt f f' x) (hfg : f = g) : HasDerivAt g f' x := hfg ▸ h

/-- HasDerivAt for affine function η ↦ a + η * b. -/
lemma hasDerivAt_affine (a b η : ℝ) :
    HasDerivAt (fun η => a + η * b) b η := by
  have h1 := (hasDerivAt_id η).const_mul b |>.const_add a |>.congr_deriv (by ring)
  exact hasDerivAt_of_funEq h1 (by ext x; simp [mul_comm])

/-- HasDerivAt for Q(η) = -(x₁²+(u+ηh)²+y₁²+(v+ηg)²)/2. -/
lemma hasDerivAt_Q (u h x₁ y₁ v g η : ℝ) :
    HasDerivAt (fun η => -(x₁ ^ 2 + (u + η * h) ^ 2 +
        y₁ ^ 2 + (v + η * g) ^ 2) / 2)
      (-((u + η * h) * h + (v + η * g) * g)) η := by
  have h1 := hasDerivAt_affine u h η
  have h2 := hasDerivAt_affine v g η
  have hp := (h1.mul h1).add (h2.mul h2)
    |>.const_add (x₁ ^ 2 + y₁ ^ 2) |>.neg |>.div_const 2
  exact (hasDerivAt_of_funEq hp (by ext x; dsimp [sq]; ring)).congr_deriv
    (by ring)

/-- HasDerivAt for L(η) = x₁y₁ + (u+ηh)(v+ηg). -/
lemma hasDerivAt_L (u h x₁ y₁ v g η : ℝ) :
    HasDerivAt (fun η => x₁ * y₁ + (u + η * h) * (v + η * g))
      (h * (v + η * g) + (u + η * h) * g) η :=
  ((hasDerivAt_affine u h η).mul (hasDerivAt_affine v g η)).const_add _

/-- First derivative of exp(Q)·sin(L) as a function. -/
lemma hasDerivAt_exp_Q_sin_L (u h x₁ y₁ v g η : ℝ) :
    HasDerivAt
      (fun η => Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 +
          y₁ ^ 2 + (v + η * g) ^ 2) / 2) *
        Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g)))
      (Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 +
          y₁ ^ 2 + (v + η * g) ^ 2) / 2) *
        (-((u + η * h) * h + (v + η * g) * g) *
          Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g)) +
         (h * (v + η * g) + (u + η * h) * g) *
          Real.cos (x₁ * y₁ + (u + η * h) * (v + η * g))))
      η := by
  have hQ := hasDerivAt_Q u h x₁ y₁ v g η
  have hL := hasDerivAt_L u h x₁ y₁ v g η
  exact (hQ.exp.mul hL.sin).congr_deriv (by ring)

/-- The explicit second derivative of Phi_smooth_part at η = 0.

This is `exp(Q₀) · [(Q₁² + Q₂ - L₁²)·sin(L₀) + (2·Q₁·L₁ + L₂)·cos(L₀)]`
where Q₁ = -(uh+vg), Q₂ = -(h²+g²), L₁ = ug+vh, L₂ = 2hg, etc. -/
private def D2_val (p : P44) : ℝ :=
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  let E₀ := Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2)
  let S₀ := Real.sin (x₁ * y₁ + u * v)
  let C₀ := Real.cos (x₁ * y₁ + u * v)
  let As := (u * h + v * g) ^ 2 - (h ^ 2 + g ^ 2) - (u * g + v * h) ^ 2
  let Ac := -2 * (u * h + v * g) * (u * g + v * h) + 2 * h * g
  E₀ * (As * S₀ + Ac * C₀)

/-- The second derivative of Phi_smooth_part at η=0 equals the explicit formula.
Proved using HasDerivAt (product rule + chain rule) twice. -/
private lemma iteratedDeriv2_Phi_smooth_eq (p : P44) :
    iteratedDeriv 2 (Phi_smooth_part p) 0 = D2_val p := by
  let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
  let h := h5 x₁; let g := h5 y₁
  -- Convert iteratedDeriv 2 to deriv ∘ deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  -- Step 1: Show deriv (Phi_smooth_part p) = explicit first derivative function
  have hd1 : ∀ η, HasDerivAt (Phi_smooth_part p)
      (Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 + y₁ ^ 2 +
          (v + η * g) ^ 2) / 2) *
        (-((u + η * h) * h + (v + η * g) * g) *
          Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g)) +
         (h * (v + η * g) + (u + η * h) * g) *
          Real.cos (x₁ * y₁ + (u + η * h) * (v + η * g)))) η :=
    fun η => hasDerivAt_exp_Q_sin_L u h x₁ y₁ v g η
  -- Extract the first derivative as a function
  have e1 : deriv (Phi_smooth_part p) = fun η =>
      Real.exp (-(x₁ ^ 2 + (u + η * h) ^ 2 + y₁ ^ 2 +
          (v + η * g) ^ 2) / 2) *
        (-((u + η * h) * h + (v + η * g) * g) *
          Real.sin (x₁ * y₁ + (u + η * h) * (v + η * g)) +
         (h * (v + η * g) + (u + η * h) * g) *
          Real.cos (x₁ * y₁ + (u + η * h) * (v + η * g))) := by
    ext η; exact (hd1 η).deriv
  rw [e1]
  -- Step 2: Compute deriv of the explicit first-derivative function at η = 0
  -- Build HasDerivAt for each subexpression at η = 0
  have hQ0 := hasDerivAt_Q u h x₁ y₁ v g 0
  have hL0 := hasDerivAt_L u h x₁ y₁ v g 0
  -- Q'(η) is affine → derivative at 0 is -(h²+g²)
  have hQ' : HasDerivAt (fun η => -((u + η * h) * h + (v + η * g) * g))
      (-(h ^ 2 + g ^ 2)) 0 := by
    have h1 := ((hasDerivAt_affine u h 0).mul_const h).add
      ((hasDerivAt_affine v g 0).mul_const g) |>.neg
    exact hasDerivAt_of_funEq (h1.congr_deriv (by ring))
      (by ext x; dsimp)
  -- L'(η) is affine → derivative at 0 is 2hg
  have hL' : HasDerivAt (fun η => h * (v + η * g) + (u + η * h) * g)
      (2 * h * g) 0 := by
    have h1 := ((hasDerivAt_affine v g 0).const_mul h).add
      ((hasDerivAt_affine u h 0).mul_const g)
    exact hasDerivAt_of_funEq (h1.congr_deriv (by ring))
      (by ext x; dsimp)
  -- Combine: a(η) = Q'*sin(L) + L'*cos(L) at η=0
  have ha := hasDerivAt_of_funEq
    ((hQ'.mul hL0.sin).add (hL'.mul hL0.cos))
    (by ext η; dsimp)
  -- exp(Q)*(Q'*sin(L)+L'*cos(L)) product at η=0
  have hd2 := hasDerivAt_of_funEq (hQ0.exp.mul ha)
    (by ext η; dsimp)
  -- The derivative value from hd2 equals D2_val
  convert hd2.deriv using 1
  unfold D2_val
  simp only [zero_mul, add_zero, mul_zero, mul_one, one_mul]
  ring

/-- FTC helper: for fixed (x₁,y₁,v), ∫_{u>0} Kuu du = -Ku(0,v).
The antiderivative is `Ku = exp(Q)·(-u·sin(L)+v·cos(L))` with Q=-(x₁²+u²+y₁²+v²)/2, L=x₁y₁+uv.
HasDerivAt follows from `hasDerivAt_Q`/`hasDerivAt_L`. -/
private lemma ftc_Ku_u (x₁ y₁ v : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)) =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      (v * Real.cos (x₁ * y₁)) := by
  -- Antiderivative: f(u) = exp(Q)·(-u·sin(L)+v·cos(L)) where Q=-(x₁²+u²+y₁²+v²)/2, L=x₁y₁+uv
  -- f'(u) = Kuu = integrand, f(0) = exp(-(x₁²+y₁²+v²)/2)·v·cos(x₁y₁), f(∞)→0
  set f := fun u : ℝ => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
    (-u * Real.sin (x₁ * y₁ + u * v) + v * Real.cos (x₁ * y₁ + u * v))
  -- HasDerivAt for the antiderivative: f is the first u-derivative of K(x₁,·,y₁,v)
  -- Use hasDerivAt_exp_Q_sin_L with (a=0, h=1, x₁, y₁, v=v, g=0, η=u)
  have hd : ∀ u : ℝ, HasDerivAt f
      (Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v))) u := by
    intro u
    -- f(u) = deriv_η [exp(Q(η))*sin(L(η))] evaluated at specific params
    -- Use the second derivative of K w.r.t. u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    -- hQ : HasDerivAt (fun η => Q(η)) (-u) u
    -- hL : HasDerivAt (fun η => L(η)) v u
    -- f = exp(Q)*(-u*sin(L)+v*cos(L)) = exp(Q)*(Q'*sin(L)+L'*cos(L))
    -- f' = exp(Q)*(Q'*(Q'*sin+L'*cos) + Q''*sin+Q'L'*cos+L''*cos-L'²*sin)
    --    = exp(Q)*((Q'²+Q''-L'²)*sin + (2Q'L'+L'')*cos)
    --    = exp(Q)*((u²-1-v²)*sin - 2uv*cos) ✓
    -- Build HasDerivAt for each piece
    have hQd : HasDerivAt (fun u => -u) (-1 : ℝ) u := (hasDerivAt_id u).neg
    have hLd : HasDerivAt (fun u : ℝ => v) (0 : ℝ) u := hasDerivAt_const u v
    have ha := hasDerivAt_of_funEq
      ((hQd.mul hL.sin).add (hLd.mul hL.cos))
      (by ext; dsimp)
    have step := hasDerivAt_of_funEq (hQ.exp.mul ha) (by ext; dsimp)
    exact step.congr_deriv (by ring)
  -- Continuity at 0
  have hcont : ContinuousWithinAt f (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      (-u * Real.sin (x₁ * y₁ + u * v) + v * Real.cos (x₁ * y₁ + u * v))
    fun_prop
  -- Tendsto at ∞: |f(u)| ≤ (|v|+|u|)*exp(-(x₁²+y₁²+v²+u²)/2) → 0
  have htend : Tendsto f atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun u =>
      (|v| + |u|) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2 + u ^ 2) / 2))
    · intro u; simp only [f]
      rw [show -(x₁^2+u^2+y₁^2+v^2)/2 = -(x₁^2+y₁^2+v^2+u^2)/2
        from by ring]
      have hB : ‖-u * Real.sin (x₁*y₁+u*v) + v * Real.cos (x₁*y₁+u*v)‖
          ≤ |v| + |u| := by
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, Real.norm_eq_abs, abs_neg]
        linarith [mul_le_of_le_one_right (abs_nonneg u)
            (abs_sin_le_one (x₁ * y₁ + u * v)),
          mul_le_of_le_one_right (abs_nonneg v)
            (abs_cos_le_one (x₁ * y₁ + u * v))]
      calc ‖Real.exp _ * _‖
          = Real.exp _ * ‖_‖ := by rw [norm_mul, norm_of_nonneg
              (Real.exp_nonneg _)]
        _ ≤ Real.exp _ * (|v| + |u|) :=
            mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _)
        _ = _ := by ring
    · exact tendsto_gauss_bound (x₁^2+y₁^2+v^2) |v|
  -- Integrability
  have hint : IntegrableOn (fun u =>
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v))) (Set.Ioi 0) := by
    refine ((integrableOn_pow_mul_gauss 0).const_mul (3*(v^2+1))).add
      ((integrableOn_pow_mul_gauss 2).const_mul 3) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Set.mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) ≤
        Real.exp (-(1/2)*u^2) :=
      Real.exp_le_exp.mpr (by
        nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((u^2-v^2-1) * Real.sin (x₁*y₁+u*v) -
        2*u*v * Real.cos (x₁*y₁+u*v))| ≤ 3*(v^2+1)+3*u^2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg u, sq_nonneg v,
        sq_nonneg (u-v), sq_nonneg (u+v),
        neg_one_le_sin (x₁*y₁+u*v), sin_le_one (x₁*y₁+u*v),
        neg_one_le_cos (x₁*y₁+u*v), cos_le_one (x₁*y₁+u*v)]
    nlinarith [Real.exp_nonneg (-(1/2)*u^2),
      abs_nonneg ((u^2-v^2-1) * Real.sin (x₁*y₁+u*v) -
        2*u*v * Real.cos (x₁*y₁+u*v))]
  -- Apply FTC
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) hint htend
  rw [this]
  -- Compute f(0)
  show 0 - f 0 = _
  simp [f]

/-- FTC helper: for fixed (x₁,y₁,v), ∫_{u>0} Kuv du = -Kv(0,v). -/
private lemma ftc_Kv_u (x₁ y₁ v : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((1 - u ^ 2 - v ^ 2) * Real.cos (x₁ * y₁ + u * v)) =
    Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      (v * Real.sin (x₁ * y₁)) := by
  -- Antiderivative: Kv(u) = exp(Q)*(-v*sin(L)+u*cos(L))
  set f := fun u : ℝ => Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
    (-v * Real.sin (x₁*y₁+u*v) + u * Real.cos (x₁*y₁+u*v))
  have hd : ∀ u : ℝ, HasDerivAt f
      (Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
        ((1-u^2-v^2) * Real.cos (x₁*y₁+u*v))) u := by
    intro u
    have hQ := hasDerivAt_Q 0 1 x₁ y₁ v 0 u
    have hL := hasDerivAt_L 0 1 x₁ y₁ v 0 u
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul] at hQ hL
    have hQd : HasDerivAt (fun u => -u) (-1 : ℝ) u := (hasDerivAt_id u).neg
    have hLd : HasDerivAt (fun u : ℝ => v) (0 : ℝ) u := hasDerivAt_const u v
    have huid : HasDerivAt (fun u : ℝ => u) 1 u := hasDerivAt_id u
    have ha := hasDerivAt_of_funEq
      ((hLd.neg.mul hL.sin).add (huid.mul hL.cos))
      (by ext; dsimp)
    have step := hasDerivAt_of_funEq (hQ.exp.mul ha) (by ext; dsimp)
    exact step.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hcont : ContinuousWithinAt f (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun u => Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
      (-v * Real.sin (x₁*y₁+u*v) + u * Real.cos (x₁*y₁+u*v))
    fun_prop
  have htend : Tendsto f atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun u =>
      (|v|+|u|) * Real.exp (-(x₁^2+y₁^2+v^2+u^2)/2))
    · intro u; simp only [f]
      rw [show -(x₁^2+u^2+y₁^2+v^2)/2 = -(x₁^2+y₁^2+v^2+u^2)/2
        from by ring]
      have hB : ‖-v * Real.sin (x₁*y₁+u*v) +
          u * Real.cos (x₁*y₁+u*v)‖ ≤ |v| + |u| := by
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, Real.norm_eq_abs, abs_neg]
        linarith [mul_le_of_le_one_right (abs_nonneg v)
            (abs_sin_le_one (x₁*y₁+u*v)),
          mul_le_of_le_one_right (abs_nonneg u)
            (abs_cos_le_one (x₁*y₁+u*v))]
      calc ‖Real.exp _ * _‖
          = Real.exp _ * ‖_‖ := by rw [norm_mul, norm_of_nonneg
              (Real.exp_nonneg _)]
        _ ≤ Real.exp _ * (|v| + |u|) :=
            mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _)
        _ = _ := by ring
    · exact tendsto_gauss_bound (x₁^2+y₁^2+v^2) |v|
  have hint : IntegrableOn (fun u =>
      Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
        ((1-u^2-v^2) * Real.cos (x₁*y₁+u*v))) (Set.Ioi 0) := by
    refine ((integrableOn_pow_mul_gauss 0).const_mul (3*(v^2+1))).add
      ((integrableOn_pow_mul_gauss 2).const_mul 3) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Set.mem_Ioi] at hu
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) ≤
        Real.exp (-(1/2)*u^2) :=
      Real.exp_le_exp.mpr (by
        nlinarith [sq_nonneg x₁, sq_nonneg y₁, sq_nonneg v])
    have hB : |((1-u^2-v^2) * Real.cos (x₁*y₁+u*v))| ≤
        3*(v^2+1)+3*u^2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg u, sq_nonneg v,
        neg_one_le_cos (x₁*y₁+u*v), cos_le_one (x₁*y₁+u*v)]
    nlinarith [Real.exp_nonneg (-(1/2)*u^2),
      abs_nonneg ((1-u^2-v^2) * Real.cos (x₁*y₁+u*v))]
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun u hu => hd u) hint htend
  rw [this]; show 0 - f 0 = _; simp [f]

/-- FTC helper: for fixed (x₁,y₁,u), ∫_{v>0} Kvv dv = -Kv(u,0). -/
private lemma ftc_Kv_v (x₁ y₁ u : ℝ) :
    ∫ v in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((v ^ 2 - u ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)) =
    -Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2) *
      (u * Real.cos (x₁ * y₁)) := by
  -- Antiderivative: Kv(v) = exp(Q)*(-v*sin(L)+u*cos(L))
  set f := fun v : ℝ => Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
    (-v * Real.sin (x₁*y₁+u*v) + u * Real.cos (x₁*y₁+u*v))
  have hd : ∀ v : ℝ, HasDerivAt f
      (Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
        ((v^2-u^2-1) * Real.sin (x₁*y₁+u*v) -
         2*u*v * Real.cos (x₁*y₁+u*v))) v := by
    intro v
    have hQ := hasDerivAt_Q u 0 x₁ y₁ 0 1 v
    have hL := hasDerivAt_L u 0 x₁ y₁ 0 1 v
    simp only [zero_add, mul_one, mul_zero, add_zero, one_mul, zero_mul] at hQ hL
    have hQd : HasDerivAt (fun v => -v) (-1 : ℝ) v := (hasDerivAt_id v).neg
    have hLd : HasDerivAt (fun v : ℝ => u) (0 : ℝ) v := hasDerivAt_const v u
    have hvid : HasDerivAt (fun v : ℝ => v) 1 v := hasDerivAt_id v
    have ha := hasDerivAt_of_funEq
      ((hvid.neg.mul hL.sin).add (hLd.mul hL.cos))
      (by ext; dsimp)
    have step := hasDerivAt_of_funEq (hQ.exp.mul ha) (by ext; dsimp)
    exact step.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hcont : ContinuousWithinAt f (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    show Continuous fun v => Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
      (-v * Real.sin (x₁*y₁+u*v) + u * Real.cos (x₁*y₁+u*v))
    fun_prop
  have htend : Tendsto f atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun v =>
      (|u|+|v|) * Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2))
    · intro v; simp only [f]
      have hB : ‖-v * Real.sin (x₁*y₁+u*v) +
          u * Real.cos (x₁*y₁+u*v)‖ ≤ |u| + |v| := by
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, Real.norm_eq_abs, abs_neg]
        linarith [mul_le_of_le_one_right (abs_nonneg v)
            (abs_sin_le_one (x₁*y₁+u*v)),
          mul_le_of_le_one_right (abs_nonneg u)
            (abs_cos_le_one (x₁*y₁+u*v))]
      rw [show -(x₁^2+u^2+y₁^2+v^2)/2 = -(x₁^2+u^2+y₁^2+v^2)/2
        from rfl]
      calc ‖Real.exp _ * _‖
          = Real.exp _ * ‖_‖ := by rw [norm_mul, norm_of_nonneg
              (Real.exp_nonneg _)]
        _ ≤ Real.exp _ * (|u| + |v|) :=
            mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _)
        _ = (|u| + |v|) * Real.exp _ := by ring
    · exact tendsto_gauss_bound (x₁^2+u^2+y₁^2) |u|
  have hint : IntegrableOn (fun v =>
      Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) *
        ((v^2-u^2-1) * Real.sin (x₁*y₁+u*v) -
         2*u*v * Real.cos (x₁*y₁+u*v))) (Set.Ioi 0) := by
    refine ((integrableOn_pow_mul_gauss 0).const_mul (3*(u^2+1))).add
      ((integrableOn_pow_mul_gauss 2).const_mul 3) |>.mono'
      ((by fun_prop : Continuous _).aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    rw [Set.mem_Ioi] at hv
    simp only [Real.norm_eq_abs, Pi.add_apply, pow_zero, one_mul]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x₁^2+u^2+y₁^2+v^2)/2) ≤
        Real.exp (-(1/2)*v^2) :=
      Real.exp_le_exp.mpr (by
        nlinarith [sq_nonneg x₁, sq_nonneg u, sq_nonneg y₁])
    have hB : |((v^2-u^2-1) * Real.sin (x₁*y₁+u*v) -
        2*u*v * Real.cos (x₁*y₁+u*v))| ≤ 3*(u^2+1)+3*v^2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg u, sq_nonneg v,
        sq_nonneg (u-v), sq_nonneg (u+v),
        neg_one_le_sin (x₁*y₁+u*v), sin_le_one (x₁*y₁+u*v),
        neg_one_le_cos (x₁*y₁+u*v), cos_le_one (x₁*y₁+u*v)]
    nlinarith [Real.exp_nonneg (-(1/2)*v^2),
      abs_nonneg ((v^2-u^2-1) * Real.sin (x₁*y₁+u*v) -
        2*u*v * Real.cos (x₁*y₁+u*v))]
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun v hv => hd v) hint htend
  rw [this]; show 0 - f 0 = _; simp [f]

/-- D2_val decomposes as h²·Kuu + 2hg·Kuv + g²·Kvv (chain rule). -/
private lemma D2_val_eq_chain (p : P44) :
    D2_val p =
      let x₁ := p.1.1; let u := p.1.2; let y₁ := p.2.1; let v := p.2.2
      let h := h5 x₁; let g := h5 y₁
      h ^ 2 * (Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v))) +
      2 * h * g * (Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((1 - u ^ 2 - v ^ 2) * Real.cos (x₁ * y₁ + u * v))) +
      g ^ 2 * (Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((v ^ 2 - u ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v))) := by
  unfold D2_val; ring

/-- The (x₁,y₁)-integral of the boundary value function vanishes.
After computing the (u,v) quadrant integral of D2_val for fixed (x₁,y₁),
the result is `Boundary_val x₁ y₁ := exp(-(x₁²+y₁²)/2) * [-(h²+g²)cos + 2hg·sin]`.
This vanishes upon integration over (x₁,y₁) because:
- The h²·cos and 2hg·sin terms give √(2π)·∫h5²exp(-x²) each (via `gaussian_cos_transform`
  and `gaussian_h5_sin_transform`), with coefficients -1 and +2.
- The g²·cos term (swapping x↔y integration order) also gives √(2π)·∫h5²exp(-y²),
  with coefficient -1.
- Total: (-1+2-1)·√(2π)·N = 0. -/
private lemma integral_boundary_val_zero :
    ∫ z : ℝ × ℝ,
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
      (-(h5 z.1 ^ 2 + h5 z.2 ^ 2) * Real.cos (z.1 * z.2) +
        2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2)) = 0 := by
  -- Split: terms 1,2 (h5(x)²·cos and 2h5(x)h5(y)·sin) vs term 3 (h5(y)²·cos)
  -- Terms 1+2 integrate to +√(2π)·N, term 3 to -√(2π)·N, cancelling to 0.
  set N := Real.sqrt (2 * Real.pi) * ∫ t : ℝ, h5 t ^ 2 * Real.exp (-t ^ 2) with hN_def
  -- Define the two groups
  let T12 : ℝ × ℝ → ℝ := fun z =>
    Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
      (-h5 z.1 ^ 2 * Real.cos (z.1 * z.2) +
        2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2))
  let T3 : ℝ × ℝ → ℝ := fun z =>
    Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
      (-h5 z.2 ^ 2 * Real.cos (z.1 * z.2))
  -- The integrand = T12 + T3
  have hspl : (fun z : ℝ × ℝ =>
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
      (-(h5 z.1 ^ 2 + h5 z.2 ^ 2) * Real.cos (z.1 * z.2) +
        2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2))) =
      fun z => T12 z + T3 z := by
    ext z; simp only [T12, T3]; ring
  rw [hspl]
  -- Gaussian exp(-x²/2) is integrable on ℝ
  have hg : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) volume :=
    (integrable_pow_mul_gauss 0).congr (ae_of_all _ fun x => by
      show x ^ 0 * Real.exp (-(1 / 2) * x ^ 2) = Real.exp (-(x ^ 2) / 2)
      rw [pow_zero, one_mul]; congr 1; ring)
  -- Integrability of T3: bound by product of 1D integrable functions
  have hT3_int : Integrable T3 volume := by
    refine (hg.mul_prod h5_sq_mul_gauss_integrable).mono'
      (show Continuous T3 by fun_prop).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [T3, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      show -(z.1 ^ 2 + z.2 ^ 2) / 2 = -(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2 from by ring,
      Real.exp_add]
    have habs : |-h5 z.2 ^ 2 * Real.cos (z.1 * z.2)| ≤ h5 z.2 ^ 2 := by
      rw [show (-h5 z.2 ^ 2 * Real.cos (z.1 * z.2) : ℝ) =
        -(h5 z.2 ^ 2 * Real.cos (z.1 * z.2)) from by ring,
        abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (abs_cos_le_one _)
    calc Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2) *
          |-h5 z.2 ^ 2 * Real.cos (z.1 * z.2)|
        ≤ Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2) * h5 z.2 ^ 2 :=
        mul_le_mul_of_nonneg_left habs
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = Real.exp (-(z.1 ^ 2) / 2) * (h5 z.2 ^ 2 * Real.exp (-(z.2 ^ 2) / 2)) := by ring
  -- Integrability of T12: bound by sum of products of 1D integrable functions
  have hT12_int : Integrable T12 volume := by
    have hb := ((h5_sq_mul_gauss_integrable.mul_prod hg).const_mul 2).add
        (hg.mul_prod h5_sq_mul_gauss_integrable)
    refine hb.mono' (show Continuous T12 by fun_prop).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
    simp only [T12, Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      show -(z.1 ^ 2 + z.2 ^ 2) / 2 = -(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2 from by ring,
      Real.exp_add]
    -- Step 1: bound the trig expression
    have h1 : |-h5 z.1 ^ 2 * Real.cos (z.1 * z.2)| ≤ h5 z.1 ^ 2 := by
      rw [show (-h5 z.1 ^ 2 * Real.cos (z.1 * z.2) : ℝ) =
        -(h5 z.1 ^ 2 * Real.cos (z.1 * z.2)) from by ring,
        abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (abs_cos_le_one _)
    have h2 : |2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2)| ≤
        2 * |h5 z.1| * |h5 z.2| := by
      calc _ = |2 * h5 z.1 * h5 z.2| * |Real.sin (z.1 * z.2)| := abs_mul _ _
        _ ≤ |2 * h5 z.1 * h5 z.2| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = 2 * |h5 z.1| * |h5 z.2| := by
            rw [mul_one, abs_mul (2 * h5 z.1), abs_mul (2 : ℝ),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 2)]
    -- Step 2: combine via triangle + AM-GM
    have htri : |-h5 z.1 ^ 2 * Real.cos (z.1 * z.2) +
        2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2)| ≤
        2 * h5 z.1 ^ 2 + h5 z.2 ^ 2 :=
      calc _ ≤ h5 z.1 ^ 2 + 2 * |h5 z.1| * |h5 z.2| :=
            (abs_add_le _ _).trans (add_le_add h1 h2)
        _ ≤ _ := by nlinarith [sq_abs (h5 z.1), sq_abs (h5 z.2),
            sq_nonneg (|h5 z.1| - |h5 z.2|)]
    -- Step 3: multiply by Gaussians
    calc Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2) *
          |-h5 z.1 ^ 2 * Real.cos (z.1 * z.2) +
            2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2)|
        ≤ Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2) *
          (2 * h5 z.1 ^ 2 + h5 z.2 ^ 2) :=
        mul_le_mul_of_nonneg_left htri
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = 2 * (h5 z.1 ^ 2 * Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2)) +
          Real.exp (-(z.1 ^ 2) / 2) * (h5 z.2 ^ 2 * Real.exp (-(z.2 ^ 2) / 2)) := by
        ring
  rw [integral_add hT12_int hT3_int]
  -- Compute ∫ T12 = N (using y-integral with gaussian_cos_transform, gaussian_h5_sin_transform)
  have hT12_val : ∫ z, T12 z = N := by
    rw [show ∫ z, T12 z = ∫ x : ℝ, ∫ y : ℝ, T12 (x, y) from
      MeasureTheory.integral_prod T12 hT12_int]
    simp only [T12]
    -- Inner integral: factor exp, split, apply Gaussian transforms
    have inner_eq : ∀ x : ℝ,
        (∫ y, Real.exp (-(x ^ 2 + y ^ 2) / 2) *
          (-h5 x ^ 2 * Real.cos (x * y) +
            2 * h5 x * h5 y * Real.sin (x * y))) =
        Real.sqrt (2 * Real.pi) * h5 x ^ 2 * Real.exp (-x ^ 2) := by
      intro x
      have hfact : (fun y : ℝ => Real.exp (-(x ^ 2 + y ^ 2) / 2) *
            (-h5 x ^ 2 * Real.cos (x * y) +
              2 * h5 x * h5 y * Real.sin (x * y))) =
          fun y => (-h5 x ^ 2 * Real.exp (-(x ^ 2) / 2)) *
              (Real.exp (-(y ^ 2) / 2) * Real.cos (x * y)) +
            (2 * h5 x * Real.exp (-(x ^ 2) / 2)) *
              (h5 y * Real.exp (-(y ^ 2) / 2) * Real.sin (x * y)) := by
        ext y
        rw [show -(x ^ 2 + y ^ 2) / 2 = -(x ^ 2) / 2 + -(y ^ 2) / 2 from by ring,
          Real.exp_add]; ring
      -- Integrability of the cos and sin terms (bounded by Gaussians)
      have hcos_int : Integrable (fun y => Real.exp (-(y ^ 2) / 2) *
          Real.cos (x * y)) volume := by
        obtain ⟨bound, hbound_int, hbound_le⟩ := Phi_integrand_dominated
        exact (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by positivity)).mono'
          (by fun_prop) (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _),
              show -(y ^ 2) / 2 = -(1 / 2) * y ^ 2 from by ring]
            exact mul_le_of_le_one_right (Real.exp_nonneg _) (abs_cos_le_one _))
      have hsin_int : Integrable (fun y => h5 y * Real.exp (-(y ^ 2) / 2) *
          Real.sin (x * y)) volume :=
        h5_mul_gauss_integrable.norm.mono' (by fun_prop) (ae_of_all _ fun y => by
          simp only [Real.norm_eq_abs]
          calc |h5 y * Real.exp (-(y ^ 2) / 2) * Real.sin (x * y)|
            = |h5 y * Real.exp (-(y ^ 2) / 2)| * |Real.sin (x * y)| := abs_mul _ _
            _ ≤ |h5 y * Real.exp (-(y ^ 2) / 2)| * 1 :=
              mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _)
            _ = |h5 y * Real.exp (-(y ^ 2) / 2)| := mul_one _)
      rw [hfact,
        MeasureTheory.integral_add (hcos_int.const_mul _) (hsin_int.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        gaussian_cos_transform, gaussian_h5_sin_transform]
      -- Combine exp(-x²/2)*exp(-x²/2) = exp(-x²) via exp_add
      have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) =
          Real.exp (-x ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have hrearr : -h5 x ^ 2 * Real.exp (-(x ^ 2) / 2) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2)) +
          2 * h5 x * Real.exp (-(x ^ 2) / 2) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(x ^ 2) / 2) * h5 x) =
        Real.sqrt (2 * Real.pi) * h5 x ^ 2 *
            (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)) := by ring
      rw [hrearr, hexp]
    simp_rw [inner_eq]
    -- Now: ∫ x, √(2π)·h5(x)²·exp(-x²) = N
    rw [show (fun x : ℝ => Real.sqrt (2 * Real.pi) * h5 x ^ 2 * Real.exp (-x ^ 2)) =
      fun x => Real.sqrt (2 * Real.pi) * (h5 x ^ 2 * Real.exp (-x ^ 2)) from by
        ext x; ring,
      MeasureTheory.integral_const_mul, hN_def]
  -- Compute ∫ T3 = -N (using x-integral with gaussian_cos_transform after swap)
  have hT3_val : ∫ z, T3 z = -N := by
    calc ∫ z, T3 z
        = ∫ y : ℝ, ∫ x : ℝ, T3 (x, y) :=
          (MeasureTheory.integral_prod T3 hT3_int).trans
            (MeasureTheory.integral_integral_swap hT3_int)
      _ = ∫ y : ℝ, -h5 y ^ 2 * Real.exp (-(y ^ 2) / 2) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2) / 2)) := by
          congr 1; ext y; simp only [T3]
          have h1 : (fun x : ℝ => Real.exp (-(x ^ 2 + y ^ 2) / 2) *
                (-h5 y ^ 2 * Real.cos (x * y))) =
              fun x => (-h5 y ^ 2 * Real.exp (-(y ^ 2) / 2)) *
                (Real.exp (-(x ^ 2) / 2) * Real.cos (y * x)) := by
            ext x
            rw [show -(x ^ 2 + y ^ 2) / 2 = -(x ^ 2) / 2 + -(y ^ 2) / 2
              from by ring, Real.exp_add, show x * y = y * x from mul_comm x y]
            ring
          rw [h1, MeasureTheory.integral_const_mul, gaussian_cos_transform]
      _ = -N := by
          have h2 : (fun y : ℝ => -h5 y ^ 2 * Real.exp (-(y ^ 2) / 2) *
              (Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2) / 2))) =
            fun y => -(Real.sqrt (2 * Real.pi)) * (h5 y ^ 2 * Real.exp (-y ^ 2)) := by
            ext y
            have hexp : Real.exp (-(y ^ 2) / 2) * Real.exp (-(y ^ 2) / 2) =
                Real.exp (-y ^ 2) := by
              rw [← Real.exp_add]; congr 1; ring
            have hrearr : -h5 y ^ 2 * Real.exp (-(y ^ 2) / 2) *
                (Real.sqrt (2 * Real.pi) * Real.exp (-(y ^ 2) / 2)) =
              -(Real.sqrt (2 * Real.pi)) *
                (h5 y ^ 2 * (Real.exp (-(y ^ 2) / 2) * Real.exp (-(y ^ 2) / 2))) := by
              ring
            rw [hrearr, hexp]
          rw [h2, MeasureTheory.integral_const_mul, neg_mul, hN_def]
  rw [hT12_val, hT3_val]; ring

/-- For fixed (x₁,y₁), the quadrant integral of the g²·Kvv term:
∫_{v>0} Kvv dv = -exp(-(x₁²+u²+y₁²)/2)·u·cos(x₁y₁) (by ftc_Kv_v),
then ∫_{u>0} u·exp(-u²/2) du = 1 (by gaussian_Ioi_y).
Combined: ∫_{u>0,v>0} Kvv = -exp(-(x₁²+y₁²)/2)·cos(x₁y₁). -/
private lemma quadrant_integral_Kvv (x₁ y₁ : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), ∫ v in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((v ^ 2 - u ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)) =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁) := by
  -- Inner v-integral by ftc_Kv_v
  simp_rw [ftc_Kv_v]
  -- Now: ∫_{u>0} -exp(-(x₁²+u²+y₁²)/2)·u·cos(x₁y₁) = -exp(-(x₁²+y₁²)/2)·cos(x₁y₁)
  rw [show (fun u => -Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2) *
      (u * Real.cos (x₁ * y₁))) =
    fun u => (-Real.cos (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(u ^ 2) / 2) * u) from by
      ext u; rw [show -(x₁ ^ 2 + u ^ 2 + y₁ ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(u ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul,
    gaussian_Ioi_y, mul_one]; ring

/-- Quadrant integral of Kuu: ∫_{u>0,v>0} Kuu = -exp(-(x₁²+y₁²)/2)·cos(x₁y₁).
Uses ftc_Ku_u (u-integral) then gaussian_Ioi_y (v-integral). -/
private lemma quadrant_integral_Kuu (x₁ y₁ : ℝ) :
    ∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)) =
    -Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁) := by
  simp_rw [ftc_Ku_u]
  rw [show (fun v => -Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      (v * Real.cos (x₁ * y₁))) =
    fun v => (-Real.cos (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(v ^ 2) / 2) * v) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul,
    gaussian_Ioi_y, mul_one]; ring

/-- Quadrant integral of Kuv: ∫_{u>0,v>0} Kuv = exp(-(x₁²+y₁²)/2)·sin(x₁y₁).
Uses ftc_Kv_u (u-integral) then gaussian_Ioi_y (v-integral). -/
private lemma quadrant_integral_Kuv (x₁ y₁ : ℝ) :
    ∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
        ((1 - u ^ 2 - v ^ 2) * Real.cos (x₁ * y₁ + u * v)) =
    Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁) := by
  simp_rw [ftc_Kv_u]
  rw [show (fun v => Real.exp (-(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
      (v * Real.sin (x₁ * y₁))) =
    fun v => (Real.sin (x₁ * y₁) * Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2)) *
      (Real.exp (-(v ^ 2) / 2) * v) from by
      ext v; rw [show -(x₁ ^ 2 + y₁ ^ 2 + v ^ 2) / 2 =
        -(x₁ ^ 2 + y₁ ^ 2) / 2 + -(v ^ 2) / 2 from by ring, Real.exp_add]; ring,
    MeasureTheory.integral_const_mul,
    gaussian_Ioi_y, mul_one]; ring

private lemma integral_D2_val_zero :
    ∫ p : P44,
      (if 0 < p.1.2 then (1 : ℝ) else 0) *
      (if 0 < p.2.2 then (1 : ℝ) else 0) * D2_val p = 0 := by
  -- Convert indicator to set integral
  have integral_if_pos : ∀ f : ℝ → ℝ,
      ∫ t : ℝ, (if 0 < t then (1 : ℝ) else 0) * f t
        = ∫ t in Set.Ioi (0 : ℝ), f t := by
    intro f
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1; ext t
    by_cases ht : 0 < t <;> simp [Set.indicator, ht]
  -- Define the three kernel pieces (matching FTC lemma forms)
  let Kuu := fun x u y v =>
    Real.exp (-(x ^ 2 + u ^ 2 + y ^ 2 + v ^ 2) / 2) *
      ((u ^ 2 - v ^ 2 - 1) * Real.sin (x * y + u * v) -
       2 * u * v * Real.cos (x * y + u * v))
  let Kuv := fun x u y v =>
    Real.exp (-(x ^ 2 + u ^ 2 + y ^ 2 + v ^ 2) / 2) *
      ((1 - u ^ 2 - v ^ 2) * Real.cos (x * y + u * v))
  let Kvv := fun x u y v =>
    Real.exp (-(x ^ 2 + u ^ 2 + y ^ 2 + v ^ 2) / 2) *
      ((v ^ 2 - u ^ 2 - 1) * Real.sin (x * y + u * v) -
       2 * u * v * Real.cos (x * y + u * v))
  -- The three indicator-weighted pieces
  let A : P44 → ℝ := fun p =>
    (if 0 < p.1.2 then (1 : ℝ) else 0) *
    (if 0 < p.2.2 then (1 : ℝ) else 0) *
    h5 p.1.1 ^ 2 * Kuu p.1.1 p.1.2 p.2.1 p.2.2
  let B : P44 → ℝ := fun p =>
    (if 0 < p.1.2 then (1 : ℝ) else 0) *
    (if 0 < p.2.2 then (1 : ℝ) else 0) *
    (2 * h5 p.1.1 * h5 p.2.1) * Kuv p.1.1 p.1.2 p.2.1 p.2.2
  let C : P44 → ℝ := fun p =>
    (if 0 < p.1.2 then (1 : ℝ) else 0) *
    (if 0 < p.2.2 then (1 : ℝ) else 0) *
    h5 p.2.1 ^ 2 * Kvv p.1.1 p.1.2 p.2.1 p.2.2
  -- The common value: J = √(2π) · ∫ h5(x)² exp(-x²) dx
  let J : ℝ := Real.sqrt (2 * Real.pi) * ∫ x : ℝ, h5 x ^ 2 * Real.exp (-x ^ 2)
  -- Step 1: D2_val splits as A + B + C
  have hsplit : (fun p : P44 =>
      (if 0 < p.1.2 then (1 : ℝ) else 0) *
      (if 0 < p.2.2 then (1 : ℝ) else 0) * D2_val p) =
      fun p => A p + B p + C p := by
    ext p; rcases p with ⟨⟨x, u⟩, ⟨y, v⟩⟩
    simp only [A, B, C, Kuu, Kuv, Kvv, D2_val_eq_chain]
    ring
  -- Step 2: Integrability from Phi_integrand_dominated
  -- First show iteratedDeriv 2 (Phi_integrand · p) 0 is integrable
  have hd2_int : Integrable (fun p => iteratedDeriv 2 (Phi_integrand · p) 0) volume := by
    obtain ⟨bound, hbound_int, hbound_le⟩ := Phi_integrand_dominated
    exact hbound_int.mono' (Phi_integrand_deriv_aestronglyMeasurable 2 0)
      (ae_of_all _ fun p => hbound_le 2 (by omega) 0 (by norm_num) p)
  -- iteratedDeriv 2 (Phi_integrand · p) 0 = 4 * (A p + B p + C p) by hsplit
  have hABC_int : Integrable (fun p => A p + B p + C p) volume := by
    have heq : (fun p => iteratedDeriv 2 (Phi_integrand · p) 0) =
        (fun p => 4 * (A p + B p + C p)) := by
      ext p; rw [iteratedDeriv_Phi_integrand_eq, iteratedDeriv2_Phi_smooth_eq]
      have := congr_fun hsplit p; linarith
    rw [heq] at hd2_int
    exact (hd2_int.div_const 4).congr (ae_of_all _ fun p => by ring)
  -- Step 3: Show the integral is 0
  suffices key : ∫ p : P44, (A p + B p + C p) = 0 by rw [hsplit, key]
  -- Rewrite to ind*ind*D2_val, apply Fubini, compute inner integral, use boundary_val_zero
  conv_lhs => rw [show (fun p : P44 => A p + B p + C p) =
    (fun p => (if 0 < p.1.2 then (1:ℝ) else 0) *
      (if 0 < p.2.2 then (1:ℝ) else 0) * D2_val p) from hsplit.symm]
  -- This 4D integral equals the 2D boundary integral, which vanishes
  -- The connection requires Fubini + (u,v) quadrant integral computation
  -- using quadrant_integral_Kuu, quadrant_integral_Kuv, quadrant_integral_Kvv
  -- Step A: Define coordinate swap σ : ((x₁,u),(y₁,v)) ↦ ((x₁,y₁),(u,v))
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
  -- Step B: Show σ preserves volume
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
  -- Step C: Transform integral via σ
  rw [← hσ_vol.integral_comp σ.measurableEmbedding]
  -- After σ, the integrand in terms of q = ((x₁,y₁),(u,v)):
  -- (σq).1.2 = u = q.2.1, (σq).2.2 = v = q.2.2
  -- D2_val(σq) = D2_val((q.1.1, q.2.1), (q.1.2, q.2.2))
  have h_sig_integrand : ∀ q : P44,
      ((if 0 < (σ q).1.2 then (1:ℝ) else 0) * if 0 < (σ q).2.2 then (1:ℝ) else 0) *
        D2_val (σ q) =
      ((if 0 < q.2.1 then (1:ℝ) else 0) * if 0 < q.2.2 then (1:ℝ) else 0) *
        D2_val ((q.1.1, q.2.1), (q.1.2, q.2.2)) := by
    intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; simp only [hσ]
  simp_rw [h_sig_integrand]
  -- Integrability of σ-transformed integrand from hABC_int
  have hABC_int_σ : Integrable (fun q : P44 =>
      ((if 0 < q.2.1 then (1:ℝ) else 0) * if 0 < q.2.2 then (1:ℝ) else 0) *
        D2_val ((q.1.1, q.2.1), (q.1.2, q.2.2))) volume := by
    have hind_D2_int : Integrable (fun p : P44 => ((if 0 < p.1.2 then (1:ℝ) else 0) *
        if 0 < p.2.2 then (1:ℝ) else 0) * D2_val p) volume :=
      hABC_int.congr (ae_of_all _ fun p => (congr_fun hsplit p).symm)
    have hcomp := (hσ_vol.integrable_comp_emb σ.measurableEmbedding).mpr hind_D2_int
    exact hcomp.congr (ae_of_all _ fun q => h_sig_integrand q)
  -- Step D: Apply Fubini to separate (x₁,y₁) from (u,v)
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod _ hABC_int_σ]
  -- Step E: For each fixed (x₁,y₁), compute the inner (u,v) integral
  have h_inner : ∀ z : ℝ × ℝ,
      ∫ w : ℝ × ℝ, ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        D2_val ((z.1, w.1), (z.2, w.2)) =
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) *
        (-(h5 z.1 ^ 2 + h5 z.2 ^ 2) * Real.cos (z.1 * z.2) +
          2 * h5 z.1 * h5 z.2 * Real.sin (z.1 * z.2)) := by
    intro ⟨x₁, y₁⟩
    simp only []
    -- Rewrite D2_val using D2_val_eq_chain: h5²Kuu + 2h5g·Kuv + g²Kvv
    have h_d2_eq : ∀ u v : ℝ,
        ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
          D2_val ((x₁, u), (y₁, v)) =
        h5 x₁ ^ 2 * ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            Kuu x₁ u y₁ v +
          2 * h5 x₁ * h5 y₁ *
            ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            Kuv x₁ u y₁ v +
          h5 y₁ ^ 2 * ((if 0 < u then (1:ℝ) else 0) * if 0 < v then (1:ℝ) else 0) *
            Kvv x₁ u y₁ v := by
      intro u v
      have hchain := D2_val_eq_chain ((x₁, u), (y₁, v))
      simp only [Kuu, Kuv, Kvv] at hchain ⊢
      rw [hchain]; ring
    simp_rw [show (fun w : ℝ × ℝ => ((if 0 < w.1 then (1:ℝ) else 0) *
        if 0 < w.2 then (1:ℝ) else 0) * D2_val ((x₁, w.1), (y₁, w.2))) =
      fun w => h5 x₁ ^ 2 * ((if 0 < w.1 then (1:ℝ) else 0) *
            if 0 < w.2 then (1:ℝ) else 0) * Kuu x₁ w.1 y₁ w.2 +
          2 * h5 x₁ * h5 y₁ *
            ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
            Kuv x₁ w.1 y₁ w.2 +
          h5 y₁ ^ 2 * ((if 0 < w.1 then (1:ℝ) else 0) *
            if 0 < w.2 then (1:ℝ) else 0) * Kvv x₁ w.1 y₁ w.2 from
      funext fun w => h_d2_eq w.1 w.2]
    -- Compute each term's integral
    -- Term 1: h5(x₁)² * ∫_{u,v} [u>0][v>0] Kuu
    --         = h5(x₁)² * (∫_v>0 ∫_u>0 Kuu) = h5(x₁)² * (-exp*cos)
    -- Term 2: 2h5(x₁)h5(y₁) * ∫_{u,v} [u>0][v>0] Kuv
    --         = 2h5(x₁)h5(y₁) * (∫_v>0 ∫_u>0 Kuv) = 2h5(x₁)h5(y₁) * (exp*sin)
    -- Term 3: h5(y₁)² * ∫_{u,v} [u>0][v>0] Kvv
    --         = h5(y₁)² * (∫_u>0 ∫_v>0 Kvv) = h5(y₁)² * (-exp*cos)
    -- Each indicator integral: ∫ (u,v) [ind_u * ind_v * K(u,v)]
    -- = ∫ v [ind_v * (∫ u [ind_u * K(u,v)])]   (Fubini)
    -- = ∫_{v>0} ∫_{u>0} K(u,v)                 (integral_if_pos twice)
    -- For the Kuu, Kuv terms we use the v-outer u-inner form (quadrant_integral_Kuu/Kuv say ∫_v>0 ∫_u>0)
    -- For the Kvv term we use the u-outer v-inner form (quadrant_integral_Kvv says ∫_u>0 ∫_v>0)
    -- 2D Gaussian building blocks for integrability
    have hg0 : Integrable (fun u : ℝ => Real.exp (-(1 / 2) * u ^ 2)) volume :=
      (integrable_pow_mul_gauss 0).congr (ae_of_all _ fun u => by
        show u ^ 0 * Real.exp (-(1 / 2) * u ^ 2) = Real.exp (-(1 / 2) * u ^ 2); ring)
    have hg2 : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / 2) * u ^ 2)) volume :=
      integrable_pow_mul_gauss 2
    -- The dominating 2D function: exp(-(x₁²+y₁²)/2) * (3u²+3v²+3) * exp(-(u²+v²)/2)
    -- factored as a sum of mul_prod terms, is integrable on ℝ × ℝ
    have hdom2D : ∀ (c : ℝ), Integrable (fun w : ℝ × ℝ =>
        c * (3 * w.1 ^ 2 + 3 * w.2 ^ 2 + 3) *
        Real.exp (-(1 / 2) * w.1 ^ 2) * Real.exp (-(1 / 2) * w.2 ^ 2))
        (volume.prod volume) := by
      intro c
      have hbase : Integrable (fun w : ℝ × ℝ =>
          3 * w.1 ^ 2 * Real.exp (-(1 / 2) * w.1 ^ 2) * Real.exp (-(1 / 2) * w.2 ^ 2) +
          3 * Real.exp (-(1 / 2) * w.1 ^ 2) * w.2 ^ 2 * Real.exp (-(1 / 2) * w.2 ^ 2) +
          3 * Real.exp (-(1 / 2) * w.1 ^ 2) * Real.exp (-(1 / 2) * w.2 ^ 2))
          (volume.prod volume) :=
        (((hg2.mul_prod hg0).const_mul 3).add
          ((hg0.mul_prod hg2).const_mul 3)).add
          ((hg0.mul_prod hg0).const_mul 3) |>.congr
          (ae_of_all _ fun w => by simp [Pi.add_apply]; ring)
      exact (hbase.const_mul c).congr (ae_of_all _ fun w => by ring)
    -- Integrability of each K-piece indicator integral on ℝ²
    -- (indicators bounded by 1, K bounded by Gaussian times polynomial)
    -- Helper: bound the trig part of each K-kernel
    -- |Kuu/Kvv trig| ≤ 3u²+3v²+3, |Kuv trig| ≤ u²+v²+1 ≤ 3u²+3v²+3
    -- Helper: exp factoring for all K-kernels
    have hexp_eq : ∀ u v : ℝ, Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) =
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := fun u v => by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hK_bound : ∀ (K : ℝ → ℝ → ℝ → ℝ → ℝ),
        (∀ u v : ℝ, |K x₁ u y₁ v| ≤
          Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
          Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2)) →
        ∀ (ind1 ind2 : ℝ), |ind1| ≤ 1 → |ind2| ≤ 1 →
        ∀ u v : ℝ, |ind1 * (ind2 * K x₁ u y₁ v)| ≤
          Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
          Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) :=
      fun K hKb ind1 ind2 h1 h2 u v => by
        have hKb_uv := hKb u v
        have hK_pos : 0 ≤ Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
          Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := by positivity
        calc |ind1 * (ind2 * K x₁ u y₁ v)|
            = |ind1| * |ind2 * K x₁ u y₁ v| := abs_mul ind1 _
          _ = |ind1| * (|ind2| * |K x₁ u y₁ v|) := by rw [abs_mul]
          _ ≤ 1 * (1 * _) := by
              apply mul_le_mul h1 (mul_le_mul h2 hKb_uv (abs_nonneg _) (by linarith)) _ (by linarith)
              exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
          _ = _ := by ring
    -- Trig bound for Kuu body
    have hKuu_trig : ∀ u v : ℝ,
        |(u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)| ≤ 3 * u ^ 2 + 3 * v ^ 2 + 3 :=
      fun u v => by
        have hs := Real.neg_one_le_sin (x₁ * y₁ + u * v)
        have hs' := Real.sin_le_one (x₁ * y₁ + u * v)
        have hc := Real.neg_one_le_cos (x₁ * y₁ + u * v)
        have hc' := Real.cos_le_one (x₁ * y₁ + u * v)
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v)]
        · nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v)]
    -- Trig bound for Kuv body
    have hKuv_trig : ∀ u v : ℝ,
        |(1 - u ^ 2 - v ^ 2) * Real.cos (x₁ * y₁ + u * v)| ≤ 3 * u ^ 2 + 3 * v ^ 2 + 3 :=
      fun u v => by
        have hc := Real.neg_one_le_cos (x₁ * y₁ + u * v)
        have hc' := Real.cos_le_one (x₁ * y₁ + u * v)
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg u, sq_nonneg v]
        · nlinarith [sq_nonneg u, sq_nonneg v]
    -- Trig bound for Kvv body
    have hKvv_trig : ∀ u v : ℝ,
        |(v ^ 2 - u ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
         2 * u * v * Real.cos (x₁ * y₁ + u * v)| ≤ 3 * u ^ 2 + 3 * v ^ 2 + 3 :=
      fun u v => by
        have hs := Real.neg_one_le_sin (x₁ * y₁ + u * v)
        have hs' := Real.sin_le_one (x₁ * y₁ + u * v)
        have hc := Real.neg_one_le_cos (x₁ * y₁ + u * v)
        have hc' := Real.cos_le_one (x₁ * y₁ + u * v)
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v)]
        · nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v)]
    -- Absolute bound on each K-kernel (without indicators)
    have hKuu_abs : ∀ u v : ℝ, |Kuu x₁ u y₁ v| ≤
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := fun u v => by
      simp only [Kuu]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
              |(u ^ 2 - v ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
               2 * u * v * Real.cos (x₁ * y₁ + u * v)|
          ≤ Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) :=
            mul_le_mul_of_nonneg_left (hKuu_trig u v) (Real.exp_nonneg _)
        _ = Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
            Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := by
            rw [hexp_eq]; ring
    have hKuv_abs : ∀ u v : ℝ, |Kuv x₁ u y₁ v| ≤
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := fun u v => by
      simp only [Kuv]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
              |(1 - u ^ 2 - v ^ 2) * Real.cos (x₁ * y₁ + u * v)|
          ≤ Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) :=
            mul_le_mul_of_nonneg_left (hKuv_trig u v) (Real.exp_nonneg _)
        _ = Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
            Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := by
            rw [hexp_eq]; ring
    have hKvv_abs : ∀ u v : ℝ, |Kvv x₁ u y₁ v| ≤
        Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
        Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := fun u v => by
      simp only [Kvv]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) *
              |(v ^ 2 - u ^ 2 - 1) * Real.sin (x₁ * y₁ + u * v) -
               2 * u * v * Real.cos (x₁ * y₁ + u * v)|
          ≤ Real.exp (-(x₁ ^ 2 + u ^ 2 + y₁ ^ 2 + v ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) :=
            mul_le_mul_of_nonneg_left (hKvv_trig u v) (Real.exp_nonneg _)
        _ = Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * (3 * u ^ 2 + 3 * v ^ 2 + 3) *
            Real.exp (-(1 / 2) * u ^ 2) * Real.exp (-(1 / 2) * v ^ 2) := by
            rw [hexp_eq]; ring
    -- AEStronglyMeasurable helpers for indicator-weighted K-kernels
    -- Shared: indicators are measurable
    have hind1_meas : Measurable (fun w : ℝ × ℝ => if 0 < w.1 then (1:ℝ) else 0) :=
      measurable_const.indicator measurableSet_Ioi |>.comp measurable_fst
    have hind2_meas : Measurable (fun w : ℝ × ℝ => if 0 < w.2 then (1:ℝ) else 0) :=
      measurable_const.indicator measurableSet_Ioi |>.comp measurable_snd
    -- Shared: Gaussian kernel (sin/cos combination) is continuous, hence measurable
    have hKuu_core_cont : Continuous (fun w : ℝ × ℝ =>
        Real.exp (-(x₁ ^ 2 + w.1 ^ 2 + y₁ ^ 2 + w.2 ^ 2) / 2) *
          ((w.1 ^ 2 - w.2 ^ 2 - 1) * Real.sin (x₁ * y₁ + w.1 * w.2) -
           2 * w.1 * w.2 * Real.cos (x₁ * y₁ + w.1 * w.2))) := by
      fun_prop
    have hKuv_core_cont : Continuous (fun w : ℝ × ℝ =>
        Real.exp (-(x₁ ^ 2 + w.1 ^ 2 + y₁ ^ 2 + w.2 ^ 2) / 2) *
          ((1 - w.1 ^ 2 - w.2 ^ 2) * Real.cos (x₁ * y₁ + w.1 * w.2))) := by
      fun_prop
    have hKvv_core_cont : Continuous (fun w : ℝ × ℝ =>
        Real.exp (-(x₁ ^ 2 + w.1 ^ 2 + y₁ ^ 2 + w.2 ^ 2) / 2) *
          ((w.2 ^ 2 - w.1 ^ 2 - 1) * Real.sin (x₁ * y₁ + w.1 * w.2) -
           2 * w.1 * w.2 * Real.cos (x₁ * y₁ + w.1 * w.2))) := by
      fun_prop
    have hKuu_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
        (if 0 < w.2 then (1:ℝ) else 0) *
        ((if 0 < w.1 then (1:ℝ) else 0) * Kuu x₁ w.1 y₁ w.2))
        (volume.prod volume) :=
      (hind2_meas.mul (hind1_meas.mul hKuu_core_cont.measurable)).aestronglyMeasurable
    have hKuv_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
        (if 0 < w.2 then (1:ℝ) else 0) *
        ((if 0 < w.1 then (1:ℝ) else 0) * Kuv x₁ w.1 y₁ w.2))
        (volume.prod volume) :=
      (hind2_meas.mul (hind1_meas.mul hKuv_core_cont.measurable)).aestronglyMeasurable
    have hKvv_meas : AEStronglyMeasurable (fun w : ℝ × ℝ =>
        (if 0 < w.1 then (1:ℝ) else 0) *
        ((if 0 < w.2 then (1:ℝ) else 0) * Kvv x₁ w.1 y₁ w.2))
        (volume.prod volume) :=
      (hind1_meas.mul (hind2_meas.mul hKvv_core_cont.measurable)).aestronglyMeasurable
    -- 2D integrability of indicator-weighted K-kernels
    have hKuu_int2D : Integrable (fun w : ℝ × ℝ =>
        (if 0 < w.2 then (1:ℝ) else 0) *
        ((if 0 < w.1 then (1:ℝ) else 0) * Kuu x₁ w.1 y₁ w.2))
        (volume.prod volume) := by
      refine (hdom2D (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2))).mono' hKuu_meas
        (ae_of_all _ fun w => ?_)
      simp only [Real.norm_eq_abs]
      have h1 : |(if 0 < w.2 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have h2 : |(if 0 < w.1 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      exact hK_bound Kuu hKuu_abs _ _ h1 h2 w.1 w.2
    have hKuv_int2D : Integrable (fun w : ℝ × ℝ =>
        (if 0 < w.2 then (1:ℝ) else 0) *
        ((if 0 < w.1 then (1:ℝ) else 0) * Kuv x₁ w.1 y₁ w.2))
        (volume.prod volume) := by
      refine (hdom2D (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2))).mono' hKuv_meas
        (ae_of_all _ fun w => ?_)
      simp only [Real.norm_eq_abs]
      have h1 : |(if 0 < w.2 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have h2 : |(if 0 < w.1 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      exact hK_bound Kuv hKuv_abs _ _ h1 h2 w.1 w.2
    have hKvv_int2D : Integrable (fun w : ℝ × ℝ =>
        (if 0 < w.1 then (1:ℝ) else 0) *
        ((if 0 < w.2 then (1:ℝ) else 0) * Kvv x₁ w.1 y₁ w.2))
        (volume.prod volume) := by
      refine (hdom2D (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2))).mono' hKvv_meas
        (ae_of_all _ fun w => ?_)
      simp only [Real.norm_eq_abs]
      have h1 : |(if 0 < w.1 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      have h2 : |(if 0 < w.2 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      exact hK_bound Kvv hKvv_abs _ _ h1 h2 w.1 w.2
    -- Integrability for integral_integral_swap (full-space with indicators)
    -- hKuu_int2D already gives integrability of ind(v>0)*(ind(u>0)*Kuu) on volume.prod volume
    have hKuu_piece : ∫ w : ℝ × ℝ, h5 x₁ ^ 2 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kuu x₁ w.1 y₁ w.2 =
        h5 x₁ ^ 2 * (-Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => h5 x₁ ^ 2 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          Kuu x₁ w.1 y₁ w.2) =
        fun w => h5 x₁ ^ 2 * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * Kuu x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hKuu_int2D]
      simp only []
      congr 1
      -- Swap u↔v via full-space integral_integral_swap, then factor indicators
      rw [MeasureTheory.integral_integral_swap hKuu_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * Kuu x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * Kuu x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]; simp only [Kuu]
      exact quadrant_integral_Kuu x₁ y₁
    have hKuv_piece : ∫ w : ℝ × ℝ, 2 * h5 x₁ * h5 y₁ *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kuv x₁ w.1 y₁ w.2 =
        2 * h5 x₁ * h5 y₁ * (Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.sin (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => 2 * h5 x₁ * h5 y₁ *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          Kuv x₁ w.1 y₁ w.2) =
        fun w => 2 * h5 x₁ * h5 y₁ * ((if 0 < w.2 then (1:ℝ) else 0) *
          ((if 0 < w.1 then (1:ℝ) else 0) * Kuv x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hKuv_int2D]
      simp only []
      congr 1
      -- Swap u↔v via full-space integral_integral_swap, then factor indicators
      rw [MeasureTheory.integral_integral_swap hKuv_int2D,
        show (fun y : ℝ => ∫ x, (if 0 < y then (1:ℝ) else 0) *
            ((if 0 < x then (1:ℝ) else 0) * Kuv x₁ x y₁ y)) =
          fun y => (if 0 < y then (1:ℝ) else 0) *
            ∫ x, (if 0 < x then (1:ℝ) else 0) * Kuv x₁ x y₁ y from
          funext fun y => MeasureTheory.integral_const_mul _ _,
        integral_if_pos]
      simp_rw [integral_if_pos]; simp only [Kuv]
      exact quadrant_integral_Kuv x₁ y₁
    have hKvv_piece : ∫ w : ℝ × ℝ, h5 y₁ ^ 2 *
        ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kvv x₁ w.1 y₁ w.2 =
        h5 y₁ ^ 2 * (-Real.exp (-(x₁ ^ 2 + y₁ ^ 2) / 2) * Real.cos (x₁ * y₁)) := by
      rw [show (fun w : ℝ × ℝ => h5 y₁ ^ 2 *
          ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
          Kvv x₁ w.1 y₁ w.2) =
        fun w => h5 y₁ ^ 2 * ((if 0 < w.1 then (1:ℝ) else 0) *
          ((if 0 < w.2 then (1:ℝ) else 0) * Kvv x₁ w.1 y₁ w.2)) from
        funext fun w => by ring,
        MeasureTheory.integral_const_mul, Measure.volume_eq_prod,
        MeasureTheory.integral_prod _ hKvv_int2D]
      simp only []
      congr 1
      rw [show (fun x : ℝ => ∫ (y : ℝ), (if 0 < x then (1:ℝ) else 0) *
            ((if 0 < y then (1:ℝ) else 0) * Kvv x₁ x y₁ y)) =
          fun x => (if 0 < x then (1:ℝ) else 0) *
            ∫ (y : ℝ), (if 0 < y then (1:ℝ) else 0) * Kvv x₁ x y₁ y from by
          ext x; rw [MeasureTheory.integral_const_mul]]
      rw [integral_if_pos]; simp_rw [integral_if_pos]
      simp only [Kvv]; exact quadrant_integral_Kvv x₁ y₁
    -- integral_add integrability: derive from hKuu_int2D, hKuv_int2D, hKvv_int2D
    have hKuu_w_int : Integrable (fun w : ℝ × ℝ =>
        h5 x₁ ^ 2 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kuu x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hKuu_int2D.const_mul (h5 x₁ ^ 2)).congr
        (ae_of_all _ fun w => by ring)
    have hKuv_w_int : Integrable (fun w : ℝ × ℝ =>
        2 * h5 x₁ * h5 y₁ * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kuv x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hKuv_int2D.const_mul (2 * h5 x₁ * h5 y₁)).congr
        (ae_of_all _ fun w => by ring)
    have hKvv_w_int : Integrable (fun w : ℝ × ℝ =>
        h5 y₁ ^ 2 * ((if 0 < w.1 then (1:ℝ) else 0) * if 0 < w.2 then (1:ℝ) else 0) *
        Kvv x₁ w.1 y₁ w.2) volume := by
      rw [Measure.volume_eq_prod]
      exact (hKvv_int2D.const_mul (h5 y₁ ^ 2)).congr
        (ae_of_all _ fun w => by ring)
    -- Split integral: ∫(A+B+C) = ∫A + ∫B + ∫C
    have h1 := MeasureTheory.integral_add (hKuu_w_int.add hKuv_w_int) hKvv_w_int
    simp only [Pi.add_apply] at h1
    have h2 := MeasureTheory.integral_add hKuu_w_int hKuv_w_int
    simp only [Pi.add_apply] at h2
    linarith [hKuu_piece, hKuv_piece, hKvv_piece]
  -- Step F: Use h_inner and integral_boundary_val_zero
  simp_rw [h_inner]
  exact integral_boundary_val_zero

/-- Direct proof that Φ''(0) = 0, using the integral representation and
the vanishing of the D2_val integral. -/
private lemma Phi_iteratedDeriv2_zero_direct :
    iteratedDeriv 2 Phi 0 = 0 := by
  rw [Phi_iteratedDeriv2_eq_integral]
  simp_rw [iteratedDeriv_Phi_integrand_eq]
  rw [MeasureTheory.integral_const_mul]
  simp_rw [iteratedDeriv2_Phi_smooth_eq]
  have h := integral_D2_val_zero
  linarith

private lemma integral_ind_iteratedDeriv2_smooth_zero :
    ∫ p : P44,
      (if 0 < p.1.2 then (1 : ℝ) else 0) *
      (if 0 < p.2.2 then (1 : ℝ) else 0) *
      iteratedDeriv 2 (Phi_smooth_part p) 0 = 0 := by
  have h := fun p => iteratedDeriv2_Phi_smooth_eq p
  simp_rw [h]
  exact integral_D2_val_zero

/-- The integral of the second-derivative integrand over P44 vanishes. -/
lemma integral_iteratedDeriv2_Phi_integrand_zero :
    ∫ p : P44, iteratedDeriv 2 (Phi_integrand · p) 0 = 0 := by
  have h1 : ∀ p : P44, iteratedDeriv 2 (Phi_integrand · p) 0 =
      4 * ((if 0 < p.1.2 then (1 : ℝ) else 0) *
      (if 0 < p.2.2 then (1 : ℝ) else 0) *
      iteratedDeriv 2 (Phi_smooth_part p) 0) :=
    fun p => iteratedDeriv_Phi_integrand_eq 2 p 0
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul, integral_ind_iteratedDeriv2_smooth_zero,
    mul_zero]

/-- **Φ''(0) = 0**: The second derivative of Φ at zero vanishes.

This is proved by showing the integral
  `∫ p, iteratedDeriv 2 (Phi_integrand · p) 0 = 0`
using the explicit formula for the second derivative (product + chain rule)
and evaluating the resulting Gaussian-Hermite integrals. -/
theorem Phi_iteratedDeriv2_at_zero : iteratedDeriv 2 Phi 0 = 0 := by
  rw [Phi_iteratedDeriv2_eq_integral]
  exact integral_iteratedDeriv2_Phi_integrand_zero

end Braverman
