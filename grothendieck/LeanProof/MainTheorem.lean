/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Rounding

/-!
# Theorem 1.1: KG < π/(2·log(1+√2))

The main theorem of Braverman-Makarychev-Makarychev-Naor (2011):
the Grothendieck constant KG is strictly less than the Krivine bound
π/(2·log(1+√2)) ≈ 1.7822.

## Definitions

We define the Grothendieck inequality predicate: `GrothendieckIneq K` says
that for all n×m real matrices A and all unit vectors x₁,...,xₙ, y₁,...,yₘ
in a Hilbert space,

  max_{ε,δ ∈ {±1}} ∑ aᵢⱼ εᵢ δⱼ ≥ (1/K) · ∑ aᵢⱼ ⟨xᵢ, yⱼ⟩

The Grothendieck constant is KG = inf{K : GrothendieckIneq K}.

## Strategy

1. From Theorem 5.1, get γ > log(1+√2) with the analytic inverse
2. Set K = π/(2γ)
3. K < π/(2·log(1+√2)) since γ > log(1+√2)
4. Show GrothendieckIneq K using the rounding scheme from Rounding.lean
-/

open Real Set

noncomputable section

namespace Braverman

/-! ### Grothendieck inequality predicate -/

/-- A constant K satisfies the Grothendieck inequality if for all finite
    bilinear forms defined by signs, the SDP relaxation ratio is at most K.

    Formally: for all n, m, matrix A, and unit vectors x, y in any
    real Hilbert space H,
      max_{ε,δ ∈ {±1}ⁿ×ᵐ} ∑ᵢⱼ aᵢⱼ εᵢ δⱼ ≥ (1/K) · ∑ᵢⱼ aᵢⱼ ⟨xᵢ, yⱼ⟩ -/
def GrothendieckIneq (K : ℝ) : Prop :=
  0 < K ∧
  ∀ (n m : ℕ) (A : Fin n → Fin m → ℝ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : Fin n → H) (y : Fin m → H)
    (_ : ∀ i, ‖x i‖ = 1) (_ : ∀ j, ‖y j‖ = 1),
    ∃ (ε : Fin n → ℝ) (δ : Fin m → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ j, δ j = 1 ∨ δ j = -1) ∧
      ∑ i, ∑ j, A i j * ε i * δ j ≥
        (1 / K) * ∑ i, ∑ j, A i j * @inner ℝ H _ (x i) (y j)

/-- The Krivine bound: π/(2·log(1+√2)). -/
def KrivineBound : ℝ := Real.pi / (2 * Real.log (1 + Real.sqrt 2))

/-- √2 > 0, used in positivity arguments for the Krivine bound. -/
private theorem sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos_of_pos (by norm_num)

/-- log(1 + √2) > 0, since 1 + √2 > 1. -/
theorem log_one_add_sqrt_two_pos : (0 : ℝ) < Real.log (1 + Real.sqrt 2) :=
  Real.log_pos (by linarith [sqrt_two_pos])

/-- The Krivine bound is positive: π > 0 and 2·log(1+√2) > 0. -/
theorem KrivineBound_pos : 0 < KrivineBound := by
  unfold KrivineBound
  exact div_pos Real.pi_pos (mul_pos (by norm_num) log_one_add_sqrt_two_pos)

/-! ### Rounding scheme implies Grothendieck inequality -/

/-- **Grothendieck inequality from rounding**: Given γ > 0 with the analytic
    inverse properties, π/(2γ) satisfies the Grothendieck inequality.

    This bridges `rounding_core_inequality` (which gives the (2γ/π) ratio)
    to the `GrothendieckIneq` predicate (which uses K = π/(2γ) and 1/K). -/
theorem grothendieck_ineq_of_rounding
    (γ : ℝ) (hγ_pos : γ > 0) (hγ_lt_one : γ < 1)
    (η p : ℝ) (hη : 0 < η) (hp : 0 < p)
    (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk γ))
    (hFi : ∀ z ∈ disk γ, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk γ, F_inv z ∈ S)
    (hSummable : summability_condition (taylor_coeff F_inv) γ) :
    GrothendieckIneq (Real.pi / (2 * γ)) := by
  constructor
  · -- Goal: 0 < π/(2γ)
    exact div_pos Real.pi_pos (mul_pos (by norm_num : (0:ℝ) < 2) hγ_pos)
  · -- Goal: the universal statement
    intro n m A H _ _ x y hx hy
    -- Get signs from the rounding core inequality
    obtain ⟨ε, δ, hε_sign, hδ_sign, hbound⟩ :=
      rounding_core_inequality γ hγ_pos hγ_lt_one η p hη hp
        F_inv hFa hFi hFS hSummable n m A H x y hx hy
    refine ⟨ε, δ, hε_sign, hδ_sign, ?_⟩
    -- Need: ∑ aᵢⱼ εᵢ δⱼ ≥ (1/K) · ∑ aᵢⱼ ⟨xᵢ,yⱼ⟩  where K = π/(2γ)
    -- From rounding_core_inequality: ∑ aᵢⱼ εᵢ δⱼ ≥ (2γ/π) · ∑ aᵢⱼ ⟨xᵢ,yⱼ⟩
    -- Since 1/K = 1/(π/(2γ)) = 2γ/π, these are the same.
    have hK_eq : 1 / (Real.pi / (2 * γ)) = 2 * γ / Real.pi := by
      rw [one_div, inv_div]
    rw [hK_eq]
    exact hbound

/-! ### Main theorem -/

/-- **Theorem 1.1** (Braverman-Makarychev-Makarychev-Naor, 2011):
    The Grothendieck constant KG is strictly less than the Krivine bound.

    Specifically, there exists K < π/(2·log(1+√2)) satisfying the
    Grothendieck inequality. -/
theorem theorem_1_1 :
    ∃ K : ℝ, K < KrivineBound ∧ GrothendieckIneq K := by
  -- Step 1: From Theorem 5.1, obtain γ > log(1+√2), γ < 1, and the analytic inverse F_p⁻¹
  obtain ⟨γ, hγ_bound, hγ_lt_one, η, p, F_inv, hη, hp, hSummable, hFa, hFi, hFS⟩ :=
    exists_good_gamma
  -- Step 2: Set K = π/(2γ). Since γ > log(1+√2) > 0, we have K < KrivineBound.
  refine ⟨Real.pi / (2 * γ), ?_, ?_⟩
  · -- Goal: π/(2γ) < π/(2·log(1+√2))
    -- Since π > 0 and 0 < 2·log(1+√2) < 2γ, this follows from div_lt_div_of_pos_left.
    unfold KrivineBound
    have hlog_pos := log_one_add_sqrt_two_pos
    apply div_lt_div_of_pos_left Real.pi_pos
    · -- 0 < 2 * log(1+√2)
      positivity
    · -- 2 * log(1+√2) < 2 * γ
      linarith
  · -- Goal: GrothendieckIneq (π/(2γ))
    -- Apply the rounding scheme from Rounding.lean.
    -- We need γ > 0 to use grothendieck_ineq_of_rounding.
    have hγ_pos : γ > 0 :=
      lt_trans (Real.log_pos (by linarith [sqrt_two_pos])) hγ_bound
    exact grothendieck_ineq_of_rounding γ hγ_pos hγ_lt_one η p hη hp
      F_inv hFa hFi hFS hSummable

/-- Corollary: The Grothendieck constant is strictly less than the Krivine bound. -/
theorem KG_lt_Krivine :
    ∃ K : ℝ, K < Real.pi / (2 * Real.log (1 + Real.sqrt 2)) ∧ GrothendieckIneq K :=
  theorem_1_1

end Braverman
