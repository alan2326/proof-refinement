/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma42
import LeanProof.Lemma52
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Lemma 5.3: Existence of the analytic inverse F_p⁻¹

For every r ∈ (0, 1), there exists p_r > 0 such that for all p ∈ (0, p_r),
the function F_p is injective on a bounded open subset Ω_r ⊆ S,
F_p(Ω_r) = rD, and thus F_p⁻¹ is well-defined and analytic on rD.

## Strategy B: Analytic Inverse Function Theorem (avoiding Rouché)

Instead of Rouché's theorem (which is not in Mathlib), we use:
1. At p = 0, F₀ = H₀, which is injective on S with H₀(S) ⊇ D (Lemma 5.2).
2. F_p'(z) = (1-p)H₀'(z) + pH_η'(z). At p = 0, F₀' = H₀' ≠ 0 on S.
3. By continuity in p, F_p' ≠ 0 on compact subsets of S for small p.
4. The analytic IFT (`AnalyticAt.analyticAt_localInverse`) gives local inverses.
5. A connectedness argument extends the local inverse to all of rD.
-/

open Complex Set Metric

noncomputable section

namespace Braverman

/-- F_p is analytic on S (as a function of z, for fixed p and η). -/
theorem F_p_analyticOnNhd (η : ℝ) (p : ℝ) : AnalyticOnNhd ℂ (F_p η p) S := by
  have h1 := H0_analyticOnNhd
  have h2 := H_eta_analyticOnNhd η
  show AnalyticOnNhd ℂ (fun z => (1 - ↑p) * H0 z + ↑p * H_eta η z) S
  exact (analyticOnNhd_const.mul h1).add (analyticOnNhd_const.mul h2)

/-- F_p is differentiable on S. -/
theorem F_p_differentiableOn (η : ℝ) (p : ℝ) : DifferentiableOn ℂ (F_p η p) S :=
  (F_p_analyticOnNhd η p).differentiableOn

/-- The derivative of F_p with respect to z:
    F_p'(z) = (1-p) H₀'(z) + p H_η'(z). -/
theorem F_p_deriv (η : ℝ) (p : ℝ) (z : ℂ) (hz : z ∈ S) :
    deriv (F_p η p) z = (1 - ↑p) * deriv H0 z + ↑p * deriv (H_eta η) z := by
  have hS : IsOpen S := S_isOpen
  have hH0 : DifferentiableAt ℂ H0 z :=
    (H0_analyticOnNhd.differentiableOn.differentiableAt (hS.mem_nhds hz))
  have hHe : DifferentiableAt ℂ (H_eta η) z :=
    ((H_eta_analyticOnNhd η).differentiableOn.differentiableAt (hS.mem_nhds hz))
  have : deriv (F_p η p) z =
      deriv (fun z => (1 - ↑p) * H0 z) z + deriv (fun z => ↑p * H_eta η z) z := by
    change deriv (fun z => (1 - ↑p) * H0 z + ↑p * H_eta η z) z = _
    exact deriv_add (hH0.const_mul _) (hHe.const_mul _)
  rw [this, deriv_const_mul _ hH0, deriv_const_mul _ hHe]

/-- H₀' is nonzero on S (since H₀ = arcsin and arcsin' = 1/√(1-z²) ≠ 0). -/
theorem H0_deriv_ne_zero (z : ℂ) (hz : z ∈ S) : deriv H0 z ≠ 0 := by
  have h_diff_H0 : DifferentiableAt ℂ H0 z :=
    H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hz)
  have h_diff_sin : DifferentiableAt ℂ Complex.sin (H0 z) :=
    Complex.differentiable_sin.differentiableAt
  have h_evt : (Complex.sin ∘ H0) =ᶠ[nhds z] id :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨S, S_isOpen.mem_nhds hz, fun w hw => sin_H0_eq w hw⟩
  have h1 : deriv (Complex.sin ∘ H0) z = 1 := by
    rw [h_evt.deriv_eq, deriv_id']
  have h2 : deriv (Complex.sin ∘ H0) z = Complex.cos (H0 z) * deriv H0 z := by
    have := (Complex.hasDerivAt_sin (H0 z)).comp z h_diff_H0.hasDerivAt
    exact this.deriv
  rw [h2] at h1
  exact right_ne_zero_of_mul_eq_one h1

/-- At p = 0, the derivative F₀'(z) = H₀'(z) ≠ 0 for z ∈ S.
    This is because H₀' = 1/√(1-z²) and |Re z| < 1 implies 1-z² ≠ 0. -/
theorem F_p_deriv_ne_zero_at_zero (η : ℝ) (z : ℂ) (hz : z ∈ S) :
    deriv (F_p η 0) z ≠ 0 := by
  rw [F_p_deriv η 0 z hz]
  simp
  exact H0_deriv_ne_zero z hz

/-- For small enough p, F_p'(z) ≠ 0 on compact subsets of S.
    This is the key perturbation argument: F_p' is continuous in (p, z),
    F₀'(z) ≠ 0 on K, and a continuous nonvanishing function on a compact set
    has a positive minimum, so small perturbations preserve nonvanishing. -/
theorem F_p_deriv_ne_zero_small_p (η : ℝ) (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ p₀ > (0 : ℝ), ∀ p : ℝ, |p| < p₀ → ∀ z ∈ K, deriv (F_p η p) z ≠ 0 := by
  -- Handle the trivial case K = ∅
  by_cases hne : K.Nonempty
  · -- Step 1: deriv H0 is continuous on S, hence on K
    have hH0_cont : ContinuousOn (deriv H0) S :=
      H0_analyticOnNhd.deriv.continuousOn
    have hHe_cont : ContinuousOn (deriv (H_eta η)) S :=
      (H_eta_analyticOnNhd η).deriv.continuousOn
    -- Step 2: ‖deriv H0 ·‖ is continuous on K and attains its minimum
    obtain ⟨z₀, hz₀K, hz₀_min⟩ := hK.exists_isMinOn hne (hH0_cont.mono hKS).norm
    set δ := ‖deriv H0 z₀‖ with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def, norm_pos_iff]
      exact H0_deriv_ne_zero z₀ (hKS hz₀K)
    -- Step 3: bound on ‖deriv (H_eta η) - deriv H0‖ on K
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hHe_cont.mono hKS).sub (hH0_cont.mono hKS))
    -- M ≥ 0 since norms are nonneg
    have hM_nonneg : 0 ≤ M := by
      rcases hne with ⟨w, hw⟩
      exact le_trans (norm_nonneg _) (hM w hw)
    -- Step 4: Take p₀ = δ / (M + 1)
    refine ⟨δ / (M + 1), div_pos hδ_pos (by linarith), ?_⟩
    intro p hp z hzK
    -- Rewrite derivative
    rw [F_p_deriv η p z (hKS hzK)]
    -- Show (1 - p) * H0'(z) + p * He'(z) = H0'(z) + p * (He'(z) - H0'(z))
    have hrw : (1 - ↑p) * deriv H0 z + ↑p * deriv (H_eta η) z =
        deriv H0 z + ↑p * (deriv (H_eta η) z - deriv H0 z) := by ring
    rw [hrw]
    -- Prove nonvanishing via reverse triangle inequality
    intro h_eq
    -- From a + b = 0, get a = -b, hence ‖a‖ = ‖b‖
    have h_neg : deriv H0 z = -(↑p * (deriv (H_eta η) z - deriv H0 z)) :=
      eq_neg_of_add_eq_zero_left h_eq
    have h1 : ‖deriv H0 z‖ = ‖↑p * (deriv (H_eta η) z - deriv H0 z)‖ := by
      conv_lhs => rw [h_neg]; rw [norm_neg]
    -- ‖p * diff‖ = |p| * ‖diff‖
    have h2 : ‖↑p * (deriv (H_eta η) z - deriv H0 z)‖ =
        |p| * ‖deriv (H_eta η) z - deriv H0 z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    -- ‖diff‖ ≤ M
    have h3 : ‖deriv (H_eta η) z - deriv H0 z‖ ≤ M := hM z hzK
    -- δ ≤ ‖H₀'(z)‖
    have h5 : δ ≤ ‖deriv H0 z‖ := hz₀_min hzK
    -- Combine: δ ≤ ‖H₀'(z)‖ = |p| * ‖diff‖ ≤ |p| * M < δ/(M+1) * M < δ
    have h6 : |p| * ‖deriv (H_eta η) z - deriv H0 z‖ < δ := by
      have hM1_pos : (0 : ℝ) < M + 1 := by linarith
      have hpM1 : |p| * (M + 1) < δ := by
        have := mul_lt_mul_of_pos_right hp hM1_pos
        rwa [div_mul_cancel₀ _ (ne_of_gt hM1_pos)] at this
      calc |p| * ‖deriv (H_eta η) z - deriv H0 z‖
          ≤ |p| * M := mul_le_mul_of_nonneg_left h3 (abs_nonneg p)
        _ < δ := by nlinarith [abs_nonneg p]
    linarith [h1, h2]
  · push_neg at hne
    rw [hne]
    exact ⟨1, one_pos, fun _ _ z hz => absurd hz (notMem_empty z)⟩

/-!
## Helper lemmas for the inverse function

We decompose the proof of Lemma 5.3 into three main components:
1. Surjectivity: F_p(S) ⊇ disk(r) for small p (perturbation of H₀(S) ⊇ disk(1))
2. Injectivity: F_p is injective on the preimage of disk(r) within S
3. Analyticity: The pointwise inverse is analytic (local analytic IFT)

The full proof also needs the preimage of disk(r) to be contained in a compact
subset of S, so that F_p_deriv_ne_zero_small_p can be applied.
-/

/-! ### Auxiliary estimates for the three helper lemmas -/

/-- cos(H₀(z)) · H₀'(z) = 1 for z ∈ S, from differentiating sin(H₀(z)) = z. -/
private lemma cos_H0_mul_deriv_H0 (z : ℂ) (hz : z ∈ S) :
    Complex.cos (H0 z) * deriv H0 z = 1 := by
  have h_diff_H0 : DifferentiableAt ℂ H0 z :=
    H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hz)
  have h_evt : (Complex.sin ∘ H0) =ᶠ[nhds z] id :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨S, S_isOpen.mem_nhds hz, fun w hw => sin_H0_eq w hw⟩
  have h1 : deriv (Complex.sin ∘ H0) z = 1 := by
    rw [h_evt.deriv_eq, deriv_id']
  rw [← ((Complex.hasDerivAt_sin (H0 z)).comp z h_diff_H0.hasDerivAt).deriv, h1]

/-- The norm ‖φ'(z)/H₀'(z)‖ equals ‖ψ'(H₀(z))‖, where ψ(w) = H_η(sin w) - H₀(sin w).

    This is a chain rule computation: ψ'(H₀(z)) = φ'(sin(H₀(z))) · cos(H₀(z))
    = φ'(z) · cos(H₀(z)). Since cos(H₀(z)) · H₀'(z) = 1, we have
    cos(H₀(z)) = 1/H₀'(z), so ψ'(H₀(z)) = φ'(z)/H₀'(z). -/
private lemma ratio_norm_eq_psi_deriv_norm (η : ℝ) (z : ℂ) (hz : z ∈ S) :
    ‖deriv (phi η) z / deriv H0 z‖ =
    ‖deriv (fun w => H_eta η (Complex.sin w) - H0 (Complex.sin w)) (H0 z)‖ := by
  have h_cos_mul := cos_H0_mul_deriv_H0 z hz
  have h_cos_eq : Complex.cos (H0 z) = (deriv H0 z)⁻¹ :=
    eq_inv_of_mul_eq_one_left h_cos_mul
  have h_sinz : Complex.sin (H0 z) = z := sin_H0_eq z hz
  have h_eta_da : DifferentiableAt ℂ (H_eta η) (Complex.sin (H0 z)) := by
    rw [h_sinz]
    exact (H_eta_analyticOnNhd η).differentiableOn.differentiableAt (S_isOpen.mem_nhds hz)
  have h_H0_da : DifferentiableAt ℂ H0 (Complex.sin (H0 z)) := by
    rw [h_sinz]
    exact H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hz)
  have h_sub_hd : HasDerivAt (fun w => H_eta η (Complex.sin w) - H0 (Complex.sin w))
      (deriv (H_eta η) (Complex.sin (H0 z)) * Complex.cos (H0 z) -
       deriv H0 (Complex.sin (H0 z)) * Complex.cos (H0 z)) (H0 z) :=
    (h_eta_da.hasDerivAt.comp (H0 z) (Complex.hasDerivAt_sin (H0 z))).sub
    (h_H0_da.hasDerivAt.comp (H0 z) (Complex.hasDerivAt_sin (H0 z)))
  rw [h_sub_hd.deriv, h_sinz]
  have h_phi_deriv : deriv (phi η) z = deriv (H_eta η) z - deriv H0 z := by
    unfold phi; exact deriv_sub
      ((H_eta_analyticOnNhd η).differentiableOn.differentiableAt (S_isOpen.mem_nhds hz))
      (H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hz))
  have hrw : deriv (H_eta η) z * Complex.cos (H0 z) - deriv H0 z * Complex.cos (H0 z) =
      (deriv (H_eta η) z - deriv H0 z) * Complex.cos (H0 z) := by ring
  rw [hrw, h_cos_eq, ← h_phi_deriv]
  rw [norm_div, norm_mul, norm_inv, div_eq_mul_inv]


/-!
## Sorry-free inverse function (via bounded balls approach)

The sorry-free proof works with G_p(w) = F_p(sin(w)) on bounded closedBalls
instead of on the unbounded H₀(S), avoiding the need for global derivative
bounds and Lipschitz estimates on non-convex domains.
-/

/-! ## Reproduced private helpers from Lemma53.lean

These are private in Lemma53.lean so we must reproduce them here.
We use primed names to avoid conflicts. -/

/-- H_η(0) = 0, by oddness. -/
private lemma H_eta_zero' (η : ℝ) : H_eta η 0 = 0 := by
  have h := H_eta_odd η 0 zero_mem_S; simp only [neg_zero] at h
  have h2 : H_eta η 0 + H_eta η 0 = 0 := by linear_combination h
  have h3 : (2 : ℂ) * H_eta η 0 = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

/-- ψ = (H_η - H₀) ∘ sin is analytic on ball(0, 1).
    sin maps ball(0, 1) into S, and H_η - H₀ is analytic on S. -/
private lemma psi_analyticOnNhd' (η : ℝ) : AnalyticOnNhd ℂ
    (fun w => H_eta η (Complex.sin w) - H0 (Complex.sin w)) (ball (0 : ℂ) 1) := by
  have h_sin_an : AnalyticOnNhd ℂ Complex.sin (ball (0 : ℂ) 1) :=
    fun w _ => Complex.differentiable_sin.analyticAt w
  have h_sin_maps : MapsTo Complex.sin (ball (0 : ℂ) 1) S := by
    intro w hw; rw [Metric.mem_ball, dist_zero_right] at hw
    exact norm_sin_lt_one_of_norm_lt_one w hw
  exact ((H_eta_analyticOnNhd η).comp h_sin_an (fun w hw => h_sin_maps hw)).sub
    (H0_analyticOnNhd.comp h_sin_an (fun w hw => h_sin_maps hw))

/-- ψ is Lipschitz on closedBall(0, r') for r' < 1. -/
lemma psi_lipschitz_on_closedBall' (η : ℝ) (r' : ℝ) (hr'0 : 0 < r') (hr'1 : r' < 1) :
    ∃ L : NNReal, 0 < L ∧ LipschitzOnWith L
      (fun w : ℂ => H_eta η (Complex.sin w) - H0 (Complex.sin w))
      (closedBall (0 : ℂ) r') := by
  set ψ := fun w : ℂ => H_eta η (Complex.sin w) - H0 (Complex.sin w)
  have h_sub : closedBall (0 : ℂ) r' ⊆ ball (0 : ℂ) 1 := by
    intro w hw; rw [mem_closedBall, dist_zero_right] at hw; rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hw hr'1
  have h_an := psi_analyticOnNhd' η
  have h_diff : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := h_an.differentiableOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall 0 r').exists_bound_of_continuousOn
    (h_an.deriv.continuousOn.mono h_sub)
  have hM_nonneg : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM 0 (mem_closedBall.mpr (by simp [hr'0.le])))
  set C : NNReal := ⟨M + 1, by linarith⟩
  refine ⟨C, by simp only [C, ← NNReal.coe_lt_coe, NNReal.coe_zero, NNReal.coe_mk]; linarith, ?_⟩
  exact (convex_closedBall 0 r').lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (h_diff.differentiableAt
      (isOpen_ball.mem_nhds (h_sub hx))).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => by
      have hda := h_diff.differentiableAt (isOpen_ball.mem_nhds (h_sub hx))
      rw [hda.hasDerivAt.hasFDerivAt.fderiv]
      rw [ContinuousLinearMap.nnnorm_toSpanSingleton]
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
      linarith [norm_nonneg (deriv ψ x), hM x hx])

/-- G_p(w) = F_p(sin(w)) equals w + p·ψ(w) for w ∈ closedBall(0, r') with r' < 1. -/
lemma G_p_eq_add_psi' (η : ℝ) (p : ℝ) (w : ℂ) (r' : ℝ) (hr'1 : r' < 1)
    (hw : w ∈ closedBall (0 : ℂ) r') :
    F_p η p (Complex.sin w) =
      w + ↑p * (H_eta η (Complex.sin w) - H0 (Complex.sin w)) := by
  have hnorm : ‖w‖ ≤ r' := by rwa [mem_closedBall, dist_zero_right] at hw
  have hlt : ‖w‖ < 1 := lt_of_le_of_lt hnorm hr'1
  have hre : |w.re| < Real.pi / 2 := calc
    |w.re| ≤ ‖w‖ := abs_re_le_norm w
    _ < 1 := hlt
    _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rw [F_p_eq]
  have h := H0_sin_eq w hre (norm_sin_lt_one_of_norm_lt_one w hlt)
  unfold phi; rw [h]

/-- NonlinearRightInverse for the identity map. -/
private def id_nri' :
    ContinuousLinearMap.NonlinearRightInverse (ContinuousLinearMap.id ℂ ℂ) where
  toFun := id; nnnorm := 1
  bound' := fun y => by simp
  right_inv' := fun y => by simp

/-- G_p approximates the identity with constant |p|·L on closedBall(0, r'). -/
private lemma G_p_approx_id' (η : ℝ) (p : ℝ) (r' : ℝ) (hr'1 : r' < 1)
    (L : NNReal) (hL : LipschitzOnWith L
      (fun w : ℂ => H_eta η (Complex.sin w) - H0 (Complex.sin w))
      (closedBall (0 : ℂ) r')) :
    ApproximatesLinearOn (fun w => F_p η p (Complex.sin w))
      (ContinuousLinearMap.id ℂ ℂ) (closedBall (0 : ℂ) r')
      (⟨|p|, abs_nonneg p⟩ * L) := by
  intro x hx y hy
  simp only [ContinuousLinearMap.id_apply]
  rw [G_p_eq_add_psi' η p x r' hr'1 hx, G_p_eq_add_psi' η p y r' hr'1 hy]
  have hrw : x + ↑p * (H_eta η (Complex.sin x) - H0 (Complex.sin x)) -
    (y + ↑p * (H_eta η (Complex.sin y) - H0 (Complex.sin y))) - (x - y) =
    ↑p * ((H_eta η (Complex.sin x) - H0 (Complex.sin x)) -
           (H_eta η (Complex.sin y) - H0 (Complex.sin y))) := by ring
  rw [hrw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h_lip := hL.dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm] at h_lip
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  calc |p| * ‖(H_eta η (Complex.sin x) - H0 (Complex.sin x)) -
               (H_eta η (Complex.sin y) - H0 (Complex.sin y))‖
      ≤ |p| * (↑L * ‖x - y‖) := mul_le_mul_of_nonneg_left h_lip (abs_nonneg p)
    _ = ↑(⟨|p|, abs_nonneg p⟩ * L) * ‖x - y‖ := by
        simp [NNReal.coe_mul, NNReal.coe_mk]; ring

/-- Near-identity perturbation w ↦ w + p·ψ(w) is injective when |p|·Lip(ψ) < 1. -/
lemma near_identity_injOn' {A : Set ℂ} (ψ : ℂ → ℂ) (p : ℝ)
    (L : NNReal) (hL : LipschitzOnWith L ψ A) (hp : |p| * ↑L < 1) :
    InjOn (fun w => w + ↑p * ψ w) A := by
  intro w₁ hw₁ w₂ hw₂ h_eq; simp only at h_eq
  have h_diff : w₁ - w₂ = ↑p * (ψ w₂ - ψ w₁) := by linear_combination h_eq
  have h_norm : ‖w₁ - w₂‖ = |p| * ‖ψ w₁ - ψ w₂‖ := by
    rw [h_diff, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
  have h_lip := hL.dist_le_mul w₁ hw₁ w₂ hw₂
  rw [dist_eq_norm, dist_eq_norm] at h_lip
  have : ‖w₁ - w₂‖ ≤ |p| * ↑L * ‖w₁ - w₂‖ := by
    calc ‖w₁ - w₂‖ = |p| * ‖ψ w₁ - ψ w₂‖ := h_norm
      _ ≤ |p| * (↑L * ‖w₁ - w₂‖) := mul_le_mul_of_nonneg_left h_lip (abs_nonneg p)
      _ = |p| * ↑L * ‖w₁ - w₂‖ := by ring
  have : ‖w₁ - w₂‖ ≤ 0 := by nlinarith [norm_nonneg (w₁ - w₂)]
  rw [norm_le_zero_iff, sub_eq_zero] at this; exact this

/-- G_p surjectivity returning w-space preimages directly.
    For each z ∈ closedBall(0, r), there exists w ∈ closedBall(0, r₁)
    with F_p(sin(w)) = z. This is the key adaptation from Lemma53.lean's
    F_p_surj_on_closedBall: instead of returning sin(w) ∈ S, we return w. -/
private theorem G_p_surj_on_closedBall' (η : ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ p₁ > (0 : ℝ), ∀ p : ℝ, |p| < p₁ →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
        ∃ w ∈ closedBall (0 : ℂ) ((1 + r) / 2),
          F_p η p (Complex.sin w) = z := by
  set r' := (1 + r) / 2
  have hr'_lt : r' < 1 := by simp only [r']; linarith
  have hr'_pos : (0 : ℝ) < r' := by simp only [r']; linarith
  obtain ⟨L, hL_pos, hL_lip⟩ :=
    psi_lipschitz_on_closedBall' η r' hr'_pos hr'_lt
  refine ⟨(1 - r) / ((1 + r) * (↑L + 1)), div_pos (by linarith) (by positivity), ?_⟩
  intro p hp z hz
  have h_approx := G_p_approx_id' η p r' hr'_lt L hL_lip
  set c : NNReal := ⟨|p|, abs_nonneg p⟩ * L
  have hc_val : (c : ℝ) = |p| * ↑L := by simp [c, NNReal.coe_mul, NNReal.coe_mk]
  have hc_bound : (c : ℝ) < (1 - r) / (1 + r) := by
    rw [hc_val]
    calc |p| * ↑L < (1 - r) / ((1 + r) * (↑L + 1)) * ↑L :=
          mul_lt_mul_of_pos_right hp (by exact_mod_cast hL_pos)
      _ ≤ (1 - r) / (1 + r) := by
          have hL1 : (0 : ℝ) < ↑L + 1 := by positivity
          have hr1' : (0 : ℝ) < 1 + r := by linarith
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hr1' hL1) hr1']
          nlinarith [NNReal.coe_nonneg L]
  have hc_le_one : c ≤ 1 := by
    rw [← NNReal.coe_le_coe]; simp only [NNReal.coe_one]
    have : (1 - r) / (1 + r) ≤ 1 := div_le_one_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
    linarith
  -- Apply quantitative IFT
  have h_surj := h_approx.surjOn_closedBall_of_nonlinearRightInverse
    id_nri' (le_of_lt hr'_pos) (Subset.refl _)
  -- F_p(sin(0)) = 0
  have h_zero : F_p η p (Complex.sin 0) = 0 := by
    simp only [Complex.sin_zero]; rw [F_p_eq]; unfold phi
    rw [H0_zero, H_eta_zero' η]; ring
  -- Show z is in the surjective target closedBall(0, (1-c)·r')
  have hz_in_target : z ∈ closedBall (F_p η p (Complex.sin 0))
      (((↑id_nri'.nnnorm)⁻¹ - ↑c) * r') := by
    rw [h_zero, mem_closedBall, dist_zero_right]
    have h_nri : (↑id_nri'.nnnorm : ℝ)⁻¹ = 1 := by simp [id_nri']
    rw [h_nri]; simp only [r']
    have hz_norm := (mem_closedBall.mp hz); rw [dist_zero_right] at hz_norm
    have h_pos : (0 : ℝ) < 1 + r := by linarith
    have h1 : (c : ℝ) * (1 + r) < 1 - r := by
      have := mul_lt_mul_of_pos_right hc_bound h_pos
      rwa [div_mul_cancel₀ _ (ne_of_gt h_pos)] at this
    nlinarith
  -- Extract the preimage from the IFT
  obtain ⟨w, hw_ball, hw_eq⟩ := h_surj hz_in_target
  exact ⟨w, hw_ball, hw_eq⟩

/-- Surjectivity variant for disk(r) → closedBall preimages. -/
private theorem F_p_surj_on_closedBall' (η : ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ p₁ > (0 : ℝ), ∀ p : ℝ, |p| < p₁ →
      ∀ w ∈ Metric.closedBall (0 : ℂ) r, ∃ z ∈ S, F_p η p z = w := by
  obtain ⟨p₁, hp₁, hsurj⟩ := G_p_surj_on_closedBall' η r hr0 hr1
  refine ⟨p₁, hp₁, fun p hp w hw => ?_⟩
  obtain ⟨u, _, hu_eq⟩ := hsurj p hp w hw
  have hr'1 : (1 + r) / 2 < 1 := by linarith
  have hu_norm : ‖u‖ ≤ (1 + r) / 2 := by
    rwa [mem_closedBall, dist_zero_right] at *
  have hu_lt : ‖u‖ < 1 := lt_of_le_of_lt hu_norm hr'1
  exact ⟨Complex.sin u, norm_sin_lt_one_of_norm_lt_one u hu_lt, hu_eq⟩

/-! ## New bounded-ball theorems -/

/-- Generic lemma: if f is analytic+injective on ball(0, r₂) with nonzero
    derivative, and finv is a right inverse mapping disk(r) into closedBall(0, r₁)
    with r₁ < r₂, then finv is analytic on disk(r). -/
private theorem analytic_right_inverse_on_ball
    (f finv : ℂ → ℂ) (r r₁ r₂ : ℝ)
    (hr₁₂ : r₁ < r₂)
    (hf_an : AnalyticOnNhd ℂ f (ball (0 : ℂ) r₂))
    (hfinv_mem : ∀ z ∈ disk r, finv z ∈ closedBall (0 : ℂ) r₁)
    (hfinv_right : ∀ z ∈ disk r, f (finv z) = z)
    (hf_inj : InjOn f (ball (0 : ℂ) r₂))
    (hf_deriv : ∀ z ∈ ball (0 : ℂ) r₂, deriv f z ≠ 0) :
    AnalyticOnNhd ℂ finv (disk r) := by
  intro w hw
  set z₀ := finv w with hz₀
  have hz₀_closed : z₀ ∈ closedBall (0 : ℂ) r₁ := hfinv_mem w hw
  have hz₀_ball : z₀ ∈ ball (0 : ℂ) r₂ := by
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt
      (by rwa [mem_closedBall, dist_zero_right] at hz₀_closed)
      hr₁₂
  have hfz₀ : f z₀ = w := hfinv_right w hw
  have hf_an_at : AnalyticAt ℂ f z₀ := hf_an z₀ hz₀_ball
  have hf' : deriv f z₀ ≠ 0 := hf_deriv z₀ hz₀_ball
  -- Get local inverse via analytic IFT
  set g := hf_an_at.hasStrictDerivAt.localInverse _ _ _ hf' with hg
  have hg_an : AnalyticAt ℂ g w := by
    rw [← hfz₀]
    exact hf_an_at.analyticAt_localInverse hf'
  -- Show finv agrees with g near w
  have h_agree : finv =ᶠ[nhds w] g := by
    have h_right : ∀ᶠ x in nhds w, f (g x) = x := by
      rw [← hfz₀]
      exact HasStrictDerivAt.eventually_right_inverse hf_an_at.hasStrictDerivAt hf'
    have hg_cont : ContinuousAt g w := hg_an.continuousAt
    have hg_w : g w = z₀ := by
      rw [← hfz₀, hg]
      exact HasStrictFDerivAt.localInverse_apply_image _
    have hg_mem : ∀ᶠ x in nhds w, g x ∈ ball (0 : ℂ) r₂ :=
      hg_cont.eventually (isOpen_ball.mem_nhds (hg_w ▸ hz₀_ball))
    have h_disk_nhd : disk r ∈ nhds w :=
      IsOpen.mem_nhds (disk_isOpen r) hw
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨disk r ∩ {x | f (g x) = x} ∩ {x | g x ∈ ball (0 : ℂ) r₂}, ?_, ?_⟩
    · exact Filter.inter_mem (Filter.inter_mem h_disk_nhd h_right) hg_mem
    · intro x hx
      rcases hx with ⟨⟨hx_disk, hx_right⟩, hx_gball⟩
      have hx_finv : f (finv x) = x := hfinv_right x hx_disk
      have hx_finv_ball : finv x ∈ ball (0 : ℂ) r₂ := by
        have hmem := hfinv_mem x hx_disk
        rw [mem_ball, dist_zero_right]
        exact lt_of_le_of_lt
          (by rwa [mem_closedBall, dist_zero_right] at hmem)
          hr₁₂
      exact hf_inj hx_finv_ball hx_gball (hx_finv.trans hx_right.symm)
  exact hg_an.congr h_agree.symm

/-- G_p(w) = F_p(sin(w)) is analytic on ball(0, r₂) for r₂ < 1. -/
private theorem G_p_analyticOnNhd' (η : ℝ) (p : ℝ) (r₂ : ℝ) (hr₂1 : r₂ < 1) :
    AnalyticOnNhd ℂ (fun w : ℂ => F_p η p (Complex.sin w)) (ball (0 : ℂ) r₂) := by
  have h_sin_an : AnalyticOnNhd ℂ Complex.sin (ball (0 : ℂ) r₂) :=
    fun w _ => Complex.differentiable_sin.analyticAt w
  have h_sin_maps : MapsTo Complex.sin (ball (0 : ℂ) r₂) S := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    exact norm_sin_lt_one_of_norm_lt_one w (lt_trans hw hr₂1)
  exact (F_p_analyticOnNhd η p).comp h_sin_an (fun w hw => h_sin_maps hw)

/-- For small p, G_p is injective on ball(0, r₂). -/
theorem G_p_injOn_ball (η : ℝ) (r₂ : ℝ)
    (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1) :
    ∃ p₂ > (0 : ℝ), ∀ p : ℝ, |p| < p₂ →
      InjOn (fun w : ℂ => F_p η p (Complex.sin w)) (ball (0 : ℂ) r₂) := by
  obtain ⟨L, hL_pos, hL_lip⟩ := psi_lipschitz_on_closedBall' η r₂ hr₂0 hr₂1
  refine ⟨1 / (↑L + 1), by positivity, ?_⟩
  intro p hp w₁ hw₁ w₂ hw₂ hEq
  -- w₁, w₂ ∈ ball implies w₁, w₂ ∈ closedBall
  have hw₁n : ‖w₁‖ < r₂ := by rwa [mem_ball, dist_zero_right] at hw₁
  have hw₂n : ‖w₂‖ < r₂ := by rwa [mem_ball, dist_zero_right] at hw₂
  have hw₁c : w₁ ∈ closedBall (0 : ℂ) r₂ :=
    mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_lt hw₁n)
  have hw₂c : w₂ ∈ closedBall (0 : ℂ) r₂ :=
    mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_lt hw₂n)
  -- Rewrite G_p as id + p·ψ
  have h1 := G_p_eq_add_psi' η p w₁ r₂ hr₂1 hw₁c
  have h2 := G_p_eq_add_psi' η p w₂ r₂ hr₂1 hw₂c
  -- Use near_identity_injOn
  have hp_L : |p| * ↑L < 1 := by
    calc |p| * ↑L < 1 / (↑L + 1) * ↑L :=
          mul_lt_mul_of_pos_right hp (by exact_mod_cast hL_pos)
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one (by positivity : (0 : ℝ) < ↑L + 1)]
          nlinarith [NNReal.coe_nonneg L]
  have hInj := near_identity_injOn'
    (fun w : ℂ => H_eta η (Complex.sin w) - H0 (Complex.sin w))
    p L hL_lip hp_L
  -- hEq : (fun w => F_p η p (sin w)) w₁ = (fun w => F_p η p (sin w)) w₂
  -- which reduces to F_p η p (sin w₁) = F_p η p (sin w₂)
  have hEq' : F_p η p (Complex.sin w₁) = F_p η p (Complex.sin w₂) := hEq
  -- From h1 and h2: rewrite in terms of id + p·ψ
  have hGoal : w₁ + ↑p * (H_eta η (Complex.sin w₁) - H0 (Complex.sin w₁)) =
      w₂ + ↑p * (H_eta η (Complex.sin w₂) - H0 (Complex.sin w₂)) := by
    rw [← h1, ← h2]; exact hEq'
  exact hInj hw₁c hw₂c hGoal

/-- For small p, deriv G_p ≠ 0 on ball(0, r₂). -/
private theorem G_p_deriv_ne_zero_on_ball (η : ℝ) (r₂ : ℝ)
    (hr₂0 : 0 < r₂) (hr₂1 : r₂ < 1) :
    ∃ p₃ > (0 : ℝ), ∀ p : ℝ, |p| < p₃ →
      ∀ w ∈ ball (0 : ℂ) r₂, deriv (fun u : ℂ => F_p η p (Complex.sin u)) w ≠ 0 := by
  -- sin(closedBall(0, r₂)) is compact and ⊆ S
  let K : Set ℂ := Complex.sin '' closedBall (0 : ℂ) r₂
  have hK_compact : IsCompact K := (isCompact_closedBall _ _).image Complex.continuous_sin
  have hKS : K ⊆ S := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    rw [← hwz]
    have hw_norm : ‖w‖ ≤ r₂ := by rwa [mem_closedBall, dist_zero_right] at hw
    exact norm_sin_lt_one_of_norm_lt_one w (lt_of_le_of_lt hw_norm hr₂1)
  obtain ⟨p₃, hp₃, hFp⟩ := F_p_deriv_ne_zero_small_p η K hK_compact hKS
  refine ⟨p₃, hp₃, fun p hp w hw => ?_⟩
  -- deriv(F_p ∘ sin)(w) = F_p'(sin w) · cos w
  have hw_norm : ‖w‖ < r₂ := by rwa [mem_ball, dist_zero_right] at hw
  have hw_closed : w ∈ closedBall (0 : ℂ) r₂ :=
    mem_closedBall.mpr (by rw [dist_zero_right]; exact le_of_lt hw_norm)
  have hsinK : Complex.sin w ∈ K := ⟨w, hw_closed, rfl⟩
  have hsinS : Complex.sin w ∈ S := hKS hsinK
  have hFp' : deriv (F_p η p) (Complex.sin w) ≠ 0 := hFp p hp _ hsinK
  have hdiffF : DifferentiableAt ℂ (F_p η p) (Complex.sin w) :=
    (F_p_analyticOnNhd η p).differentiableOn.differentiableAt (S_isOpen.mem_nhds hsinS)
  -- Chain rule
  have hcomp : deriv (fun u => F_p η p (Complex.sin u)) w =
      deriv (F_p η p) (Complex.sin w) * Complex.cos w := by
    exact (hdiffF.hasDerivAt.comp w (Complex.hasDerivAt_sin w)).deriv
  rw [hcomp]
  -- cos w ≠ 0 because |Re w| < π/2
  have hw1 : ‖w‖ < 1 := lt_trans hw_norm hr₂1
  have hsinS' : Complex.sin w ∈ S := norm_sin_lt_one_of_norm_lt_one w hw1
  -- We need cos w ≠ 0. Use: cos(H₀(sin w)) · H₀'(sin w) = 1
  -- and H₀(sin w) = w (since |Re w| < π/2 and sin w ∈ S)
  have hwre : |w.re| < Real.pi / 2 := calc
    |w.re| ≤ ‖w‖ := abs_re_le_norm w
    _ < 1 := hw1
    _ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hH0sin : H0 (Complex.sin w) = w := H0_sin_eq w hwre hsinS'
  -- cos(H₀(sin w)) · H₀'(sin w) = 1, i.e., cos w · H₀'(sin w) = 1
  have h_diff_H0 : DifferentiableAt ℂ H0 (Complex.sin w) :=
    H0_analyticOnNhd.differentiableOn.differentiableAt (S_isOpen.mem_nhds hsinS')
  have h_evt : (Complex.sin ∘ H0) =ᶠ[nhds (Complex.sin w)] id :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨S, S_isOpen.mem_nhds hsinS', fun u hu => sin_H0_eq u hu⟩
  have h_chain : deriv (Complex.sin ∘ H0) (Complex.sin w) = 1 := by
    rw [h_evt.deriv_eq, deriv_id']
  have hcos_mul : Complex.cos (H0 (Complex.sin w)) * deriv H0 (Complex.sin w) = 1 := by
    rw [← ((Complex.hasDerivAt_sin (H0 (Complex.sin w))).comp (Complex.sin w)
      h_diff_H0.hasDerivAt).deriv, h_chain]
  rw [hH0sin] at hcos_mul
  -- cos w ≠ 0
  have hcos_ne : Complex.cos w ≠ 0 := by
    intro hzero; rw [hzero, zero_mul] at hcos_mul; exact zero_ne_one hcos_mul
  exact mul_ne_zero hFp' hcos_ne

/-! ## Main theorem -/

/-- Lemma 5.3 with W_inv exported.

Same as `lemma_5_3`, but additionally exports the `W_inv` witness and the
formula `F_inv z = sin(W_inv z)`, with `W_inv z ∈ closedBall 0 ((1+r)/2)`.

This is needed by `lemma_5_4_strong` to identify the contraction fixed point
with the actual analytic inverse value. -/
theorem lemma_5_3_with_W_inv (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ pr : ℝ, 0 < pr ∧
      ∀ p : ℝ, 0 < p → p < pr →
        ∃ (W_inv F_inv : ℂ → ℂ),
          AnalyticOnNhd ℂ W_inv (disk r) ∧
          AnalyticOnNhd ℂ F_inv (disk r) ∧
          (∀ z ∈ disk r, W_inv z ∈ closedBall (0 : ℂ) ((1 + r) / 2)) ∧
          (∀ z ∈ disk r, F_inv z = Complex.sin (W_inv z)) ∧
          (∀ z ∈ disk r, F_p η p (F_inv z) = z) ∧
          (∀ z ∈ disk r, F_inv z ∈ S) ∧
          F_inv 0 = 0 := by
  classical
  -- Set up nested radii: r < r₁ < r₂ < 1
  set r₁ : ℝ := (1 + r) / 2 with hr₁_def
  set r₂ : ℝ := (1 + r₁) / 2 with hr₂_def
  have hr₁0 : 0 < r₁ := by simp only [r₁]; linarith
  have hr₁1 : r₁ < 1 := by simp only [r₁]; linarith
  have hr_r₁ : r < r₁ := by simp only [r₁]; linarith
  have hr₁₂ : r₁ < r₂ := by simp only [r₁, r₂]; linarith
  have hr₂0 : 0 < r₂ := by simp only [r₂]; linarith
  have hr₂1 : r₂ < 1 := by simp only [r₁, r₂]; linarith
  -- Get the three quantitative bounds
  obtain ⟨p₁, hp₁, hsurj⟩ := G_p_surj_on_closedBall' η r hr0 hr1
  obtain ⟨p₂, hp₂, hinj⟩ := G_p_injOn_ball η r₂ hr₂0 hr₂1
  obtain ⟨p₃, hp₃, hderiv⟩ := G_p_deriv_ne_zero_on_ball η r₂ hr₂0 hr₂1
  -- Take pr = min(p₁, min(p₂, p₃))
  refine ⟨min p₁ (min p₂ p₃), lt_min hp₁ (lt_min hp₂ hp₃), ?_⟩
  intro p hp0 hplt
  have hp₁' : |p| < p₁ := by rw [abs_of_pos hp0]; exact lt_of_lt_of_le hplt (min_le_left _ _)
  have hp₂' : |p| < p₂ := by
    rw [abs_of_pos hp0]
    exact lt_of_lt_of_le hplt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp₃' : |p| < p₃ := by
    rw [abs_of_pos hp0]
    exact lt_of_lt_of_le hplt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- For each z ∈ disk(r), choose w ∈ closedBall(0, r₁) with G_p(w) = z
  have hchoose : ∀ z ∈ disk r, ∃ w ∈ closedBall (0 : ℂ) r₁,
      F_p η p (Complex.sin w) = z := by
    intro z hz
    rw [mem_disk_iff] at hz
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) r :=
      Metric.mem_closedBall.mpr (le_of_lt (by rwa [dist_zero_right]))
    exact hsurj p hp₁' z hz_closed
  -- Define W_inv and F_inv
  set W_inv : ℂ → ℂ := fun z =>
    if hz : z ∈ disk r then (hchoose z hz).choose
    else 0 with hW_inv_def
  set F_inv : ℂ → ℂ := fun z => Complex.sin (W_inv z) with hF_inv_def
  -- W_inv maps disk(r) into closedBall(0, r₁)
  have hW_inv_mem : ∀ z ∈ disk r, W_inv z ∈ closedBall (0 : ℂ) r₁ := by
    intro z hz; simp only [hW_inv_def, hz, dite_true]
    exact (hchoose z hz).choose_spec.1
  -- F_p(sin(W_inv(z))) = z
  have hGp_eq : ∀ z ∈ disk r, F_p η p (Complex.sin (W_inv z)) = z := by
    intro z hz; simp only [hW_inv_def, hz, dite_true]
    exact (hchoose z hz).choose_spec.2
  -- F_inv z = sin(W_inv z)
  have hF_inv_eq : ∀ z ∈ disk r, F_inv z = Complex.sin (W_inv z) := by
    intro z _; rfl
  -- F_p(F_inv(z)) = z
  have hF_inv_right : ∀ z ∈ disk r, F_p η p (F_inv z) = z := by
    intro z hz; exact hGp_eq z hz
  -- F_inv maps disk(r) into S
  have hF_inv_mem : ∀ z ∈ disk r, F_inv z ∈ S := by
    intro z hz
    simp only [hF_inv_def]
    have hw_mem := hW_inv_mem z hz
    have hw_norm : ‖W_inv z‖ ≤ r₁ := by rwa [mem_closedBall, dist_zero_right] at hw_mem
    have hw_lt : ‖W_inv z‖ < 1 := lt_of_le_of_lt hw_norm hr₁1
    exact norm_sin_lt_one_of_norm_lt_one (W_inv z) hw_lt
  -- W_inv is analytic
  have hW_inv_an : AnalyticOnNhd ℂ W_inv (disk r) := by
    exact analytic_right_inverse_on_ball
      (fun w => F_p η p (Complex.sin w)) W_inv r r₁ r₂
      hr₁₂
      (G_p_analyticOnNhd' η p r₂ hr₂1)
      hW_inv_mem
      (fun z hz => hGp_eq z hz)
      (hinj p hp₂')
      (hderiv p hp₃')
  -- F_inv = sin ∘ W_inv is analytic
  have hF_inv_an : AnalyticOnNhd ℂ F_inv (disk r) := by
    intro z hz
    have h_sin_an : AnalyticAt ℂ Complex.sin (W_inv z) :=
      Complex.differentiable_sin.analyticAt (W_inv z)
    exact h_sin_an.comp (hW_inv_an z hz)
  -- F_inv(0) = 0
  have hF_inv_zero : F_inv 0 = 0 := by
    have h0_disk : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
    have hW0_cb := hW_inv_mem 0 h0_disk
    have hW0_ball : W_inv 0 ∈ Metric.ball (0 : ℂ) r₂ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (by rwa [mem_closedBall, dist_zero_right] at hW0_cb) hr₁₂
    have hGp_W0 : F_p η p (Complex.sin (W_inv 0)) = 0 := hGp_eq 0 h0_disk
    have hGp_zero : F_p η p (Complex.sin 0) = 0 := by
      simp only [Complex.sin_zero]
      change (1 - ↑p) * H_eta 0 0 + ↑p * H_eta η 0 = 0
      have h1 : H_eta 0 0 = 0 := by
        have h := H_eta_odd 0 0 zero_mem_S; simp only [neg_zero] at h
        exact CharZero.eq_neg_self_iff.mp h
      have h2 : H_eta η 0 = 0 := by
        have h := H_eta_odd η 0 zero_mem_S; simp only [neg_zero] at h
        exact CharZero.eq_neg_self_iff.mp h
      rw [h1, h2]; ring
    have h0_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r₂ :=
      Metric.mem_ball_self hr₂0
    have hW0_eq : W_inv 0 = 0 := by
      have hGp_inj := hinj p hp₂'
      have heq : (fun w => F_p η p (Complex.sin w)) (W_inv 0) =
          (fun w => F_p η p (Complex.sin w)) 0 := by
        simp only; rw [hGp_W0, hGp_zero]
      exact hGp_inj hW0_ball h0_ball heq
    simp [hF_inv_def, hW0_eq, Complex.sin_zero]
  exact ⟨W_inv, F_inv, hW_inv_an, hF_inv_an, hW_inv_mem, hF_inv_eq,
         hF_inv_right, hF_inv_mem, hF_inv_zero⟩

/-- Lemma 5.3 (alternative proof via bounded balls).

For every r ∈ (0,1), there exists p_r > 0 such that for p ∈ (0, p_r),
F_p has a well-defined analytic inverse on rD, with values in S. -/
theorem lemma_5_3 (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ pr : ℝ, 0 < pr ∧
      ∀ p : ℝ, 0 < p → p < pr →
        ∃ (F_inv : ℂ → ℂ),
          AnalyticOnNhd ℂ F_inv (disk r) ∧
          (∀ z ∈ disk r, F_p η p (F_inv z) = z) ∧
          (∀ z ∈ disk r, F_inv z ∈ S) ∧
          F_inv 0 = 0 := by
  obtain ⟨pr, hpr, hspec⟩ := lemma_5_3_with_W_inv η r hr0 hr1
  refine ⟨pr, hpr, ?_⟩
  intro p hp hlt
  rcases hspec p hp hlt with
    ⟨W_inv, F_inv, _, hF_an, _, _, hRight, hMem, hZero⟩
  exact ⟨F_inv, hF_an, hRight, hMem, hZero⟩
