/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Core
import LeanProof.Theorem44Support
import LeanProof.Theorem44DirectValues
import LeanProof.Theorem44FourthDeriv
import LeanProof.Theorem44Regularity
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Order.Basic

/-!
# Theorem 4.4 Main assembly

Assembles the direct derivative values and regularity to prove
`Φ(η) > Φ(0)` for small positive η, and then derives the original
theorem statement.

## Key steps
1. Direct computation: Φ''(0) = 0, Φ''''(0) = 38400√2
2. Apply Taylor-Lagrange with n=3 on [0,η]
3. Use continuity of Φ'''' near 0 to ensure positivity of remainder
4. Convert back to the H_η(i)/i > log(1+√2) statement
-/

open Complex Set Real MeasureTheory

noncomputable section

namespace Braverman

/-! ## F. Derivative values (from Theorem44DirectValues) -/

-- Phi_iteratedDeriv2_at_zero : iteratedDeriv 2 Phi 0 = 0
-- Phi_iteratedDeriv4_at_zero : iteratedDeriv 4 Phi 0 = 75 * √2 / (8 * π)
-- Both imported from Theorem44DirectValues / Theorem44FourthDeriv.

/-! ## G. Final positivity by Taylor's theorem -/

/-- Φ''''(0) > 0. -/
theorem Phi_fourth_deriv_pos : iteratedDeriv 4 Phi 0 > 0 := by
  rw [Phi_iteratedDeriv4_at_zero]
  have h1 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  have h2 : Real.pi > 0 := Real.pi_pos
  positivity

/-- Φ(η) > Φ(0) for all sufficiently small positive η.
    By Taylor-Lagrange with n=3:
      Φ(η) - Φ(0) = Φ''''(ξ)·η⁴/24 for some ξ ∈ (0,η).
    Since Φ'(0) = Φ''(0) = Φ'''(0) = 0, the Taylor polynomial is just Φ(0).
    Since Φ''''(0) > 0, by continuity Φ''''(ξ) > 0 near 0. -/
-- Helper: if f is C^n, f(0) = f'(0) = ... = f^(n-1)(0) = 0, and f^(n)(0) > 0,
-- then f(t) > 0 for small positive t. Proved by n applications of MVT.
-- MVT step: if g is continuous on [0,t], has derivative g' on (0,t),
-- g(0)=0 and g'>0 on (0,t), then g(t)>0.
private lemma pos_of_deriv_pos {g g' : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hcont : ContinuousOn g (Icc 0 t))
    (hdiff : ∀ x ∈ Ioo 0 t, HasDerivAt g (g' x) x)
    (hg0 : g 0 = 0)
    (hpos : ∀ x ∈ Ioo 0 t, g' x > 0) :
    g t > 0 := by
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope g g' ht hcont hdiff
  have hc_pos := hpos c hc
  rw [heq, hg0, sub_zero] at hc_pos
  exact (div_pos_iff_of_pos_right (by linarith : (0:ℝ) < t - 0)).mp hc_pos

/-- HasDerivAt for iteratedDeriv from ContDiffAt. -/
private lemma contDiffAt_hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {k : ℕ} {x : ℝ}
    (h : ContDiffAt ℝ (↑(k + 1)) f x) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k f) x := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact DifferentiableAt.comp (𝕜 := ℝ) x
      (ContinuousLinearEquiv.differentiableAt
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.toContinuousLinearEquiv)
      (h.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_le le_rfl))
  rw [show iteratedDeriv (k + 1) f x = deriv (iteratedDeriv k f) x from
    congr_fun iteratedDeriv_succ x]
  exact hd.hasDerivAt

/-- ContinuousAt for iteratedDeriv from ContDiffAt. -/
private lemma contDiffAt_continuousAt_iteratedDeriv {f : ℝ → ℝ} {k : ℕ} {x : ℝ}
    (h : ContDiffAt ℝ (↑k) f x) :
    ContinuousAt (iteratedDeriv k f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact Continuous.continuousAt (ContinuousLinearEquiv.continuous
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.toContinuousLinearEquiv)
    |>.comp (h.continuousAt_iteratedFDeriv le_rfl)

/-- If f is C⁴ on [-r,r] with f(0)=f'(0)=f''(0)=f'''(0)=0 and f''''(0)>0,
    then f(t) > 0 for small positive t. Proof: cascade MVT 4 times. -/
private lemma pos_near_zero_of_deriv_pos {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hcd : ContDiffOn ℝ 4 f (Icc (-r) r))
    (hf0 : f 0 = 0)
    (hf1 : deriv f 0 = 0)
    (hf2 : iteratedDeriv 2 f 0 = 0)
    (hf3 : iteratedDeriv 3 f 0 = 0)
    (hf4 : iteratedDeriv 4 f 0 > 0) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → f t > 0 := by
  -- Helper: ContDiffAt at all points of Ioo(-r,r)
  have hcda : ∀ x, x ∈ Ioo (-r) r → ContDiffAt ℝ 4 f x :=
    fun x hx => hcd.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  -- HasDerivAt for layer k at interior points
  have hdiff : ∀ k ≤ 3, ∀ x ∈ Ioo (-r) r,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x :=
    fun k hk x hx => contDiffAt_hasDerivAt_iteratedDeriv
      ((hcda x hx).of_le (by exact_mod_cast (show k + 1 ≤ 4 by omega)))
  -- ContinuousOn for each layer on sub-intervals
  have hcont : ∀ k ≤ 4, ∀ a b, Icc a b ⊆ Ioo (-r) r →
      ContinuousOn (iteratedDeriv k f) (Icc a b) :=
    fun k hk a b hsub => ContinuousOn.mono
      (fun x hx => (contDiffAt_continuousAt_iteratedDeriv
        ((hcda x (hsub hx)).of_le (by exact_mod_cast hk))).continuousWithinAt) le_rfl
  -- Continuity of iteratedDeriv 4 f at 0 → find δ₀ where it's positive
  have hf4_cont_at : ContinuousAt (iteratedDeriv 4 f) 0 :=
    contDiffAt_continuousAt_iteratedDeriv (hcda 0 ⟨by linarith, by linarith⟩)
  obtain ⟨δ₀, hδ₀_pos, hf4_pos_on⟩ : ∃ δ₀ > 0, ∀ x, |x| < δ₀ →
      iteratedDeriv 4 f x > 0 := by
    rw [Metric.continuousAt_iff] at hf4_cont_at
    obtain ⟨ε, hε, hball⟩ := hf4_cont_at (iteratedDeriv 4 f 0 / 2) (by linarith)
    refine ⟨min ε (r / 2), by positivity, fun x hx => ?_⟩
    have hbd := hball (by rw [Real.dist_eq, sub_zero]; linarith [min_le_left ε (r / 2)])
    rw [Real.dist_eq] at hbd; linarith [abs_lt.mp hbd]
  set δ := min δ₀ (r / 2)
  refine ⟨δ, by positivity, fun t ht_pos ht_lt => ?_⟩
  have ht_r2 : t < r / 2 := lt_of_lt_of_le ht_lt (min_le_right _ _)
  have ht_δ₀ : t < δ₀ := lt_of_lt_of_le ht_lt (min_le_left _ _)
  -- [0, t] ⊂ Ioo(-r, r)
  have hsub : ∀ x, 0 ≤ x → x ≤ t → x ∈ Ioo (-r) r :=
    fun x hx0 hxt => ⟨by linarith, by linarith⟩
  have hsub_Icc : Icc 0 t ⊆ Ioo (-r) r := fun x hx => hsub x hx.1 hx.2
  -- Cascade MVT: layer 3 → 2 → 1 → 0
  -- ContinuousOn on [0,x] for any x ∈ [0,t]
  have hcont_sub : ∀ k ≤ 4, ∀ x, 0 < x → x ≤ t →
      ContinuousOn (iteratedDeriv k f) (Icc 0 x) :=
    fun k hk x hx0 hxt => hcont k hk 0 x (Icc_subset_Icc_right hxt |>.trans hsub_Icc)
  have h3 : ∀ x ∈ Ioo 0 t, iteratedDeriv 3 f x > 0 := by
    intro x ⟨hx0, hxt⟩
    exact pos_of_deriv_pos hx0 (hcont_sub 3 (by omega) x hx0 hxt.le)
      (fun y hy => hdiff 3 (by omega) y (hsub y hy.1.le (le_of_lt (lt_trans hy.2 hxt))))
      hf3 (fun y ⟨hy0, hyx⟩ => hf4_pos_on y (by rw [abs_of_pos (by linarith)]; linarith))
  have h2 : ∀ x ∈ Ioo 0 t, iteratedDeriv 2 f x > 0 := by
    intro x ⟨hx0, hxt⟩
    exact pos_of_deriv_pos hx0 (hcont_sub 2 (by omega) x hx0 hxt.le)
      (fun y hy => hdiff 2 (by omega) y (hsub y hy.1.le (le_of_lt (lt_trans hy.2 hxt))))
      hf2 (fun y ⟨hy0, hyx⟩ => h3 y ⟨hy0, lt_trans hyx hxt⟩)
  have h1 : ∀ x ∈ Ioo 0 t, iteratedDeriv 1 f x > 0 := by
    intro x ⟨hx0, hxt⟩
    exact pos_of_deriv_pos hx0 (hcont_sub 1 (by omega) x hx0 hxt.le)
      (fun y hy => hdiff 1 (by omega) y (hsub y hy.1.le (le_of_lt (lt_trans hy.2 hxt))))
      (by simp [iteratedDeriv_succ, iteratedDeriv_zero, hf1])
      (fun y ⟨hy0, hyx⟩ => h2 y ⟨hy0, lt_trans hyx hxt⟩)
  -- f(t) > 0
  exact pos_of_deriv_pos ht_pos (hcont_sub 0 (by omega) t ht_pos le_rfl)
    (fun y hy => by
      have := hdiff 0 (by omega) y (hsub y hy.1.le (le_of_lt hy.2))
      rwa [iteratedDeriv_zero] at this)
    hf0 (fun y ⟨hy0, hyt⟩ => by
      have hv := h1 y ⟨hy0, hyt⟩
      change iteratedDeriv (0 + 1) f y > 0
      simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hv)

theorem Phi_pos_near_zero :
    ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → Phi η > Phi 0 := by
  -- Apply pos_near_zero_of_deriv_pos to g(t) = Phi(t) - Phi(0)
  obtain ⟨r, hr, hcd⟩ := Phi_contDiffOn_order4
  set g := fun t => Phi t - Phi 0
  have hmem : Icc (-r) r ∈ nhds (0 : ℝ) := Icc_mem_nhds (by linarith) (by linarith)
  have hcda : ContDiffAt ℝ 4 Phi 0 := hcd.contDiffAt hmem
  have hg_cd : ContDiffOn ℝ 4 g (Icc (-r) r) := hcd.sub contDiffOn_const
  have hg0 : g 0 = 0 := by simp [g]
  have hPhi_diff : DifferentiableAt ℝ Phi 0 :=
    hcda.differentiableAt (by norm_num)
  have hg1 : deriv g 0 = 0 := by
    have : deriv g 0 = deriv Phi 0 - deriv (fun _ : ℝ => Phi 0) 0 :=
      deriv_sub hPhi_diff (differentiableAt_const _)
    rw [this, deriv_const, sub_zero, Phi_deriv_zero]
  have hg_iter : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → iteratedDeriv k g 0 = iteratedDeriv k Phi 0 := by
    intro k hk hk4
    have hfun : g = Phi - fun _ => Phi 0 := by ext; simp [g, Pi.sub_apply]
    rw [hfun, iteratedDeriv_sub (hcda.of_le (by exact_mod_cast hk4)) contDiffAt_const]
    simp [iteratedDeriv_const, show k ≠ 0 from by omega]
  have hg2 : iteratedDeriv 2 g 0 = 0 := by rw [hg_iter 2 (by omega) (by omega)]; exact Phi_iteratedDeriv2_at_zero
  have hg3 : iteratedDeriv 3 g 0 = 0 := by rw [hg_iter 3 (by omega) (by omega)]; exact Phi_iteratedDeriv3_zero
  have hg4 : iteratedDeriv 4 g 0 > 0 := by rw [hg_iter 4 (by omega) (by omega)]; exact Phi_fourth_deriv_pos
  obtain ⟨δ, hδ, hpos⟩ := pos_near_zero_of_deriv_pos hr hg_cd hg0 hg1 hg2 hg3 hg4
  exact ⟨δ, hδ, fun η hη_pos hη_lt => by linarith [hpos η hη_pos hη_lt]⟩

/-! ## The main theorem -/

/-- **Theorem 4.4**: H_η(i)/i > log(1+√2) for small η > 0. -/
theorem theorem_4_4' : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
    (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2) := by
  exact theorem_4_4_of_Phi_pos Phi_pos_near_zero

end Braverman
