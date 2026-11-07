/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Lemma54
import LeanProof.Theorem44
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Theorem 5.1: Analytic inverse with coefficient radius γ > log(1+√2)

We establish the existence of parameters (η, p) and a radius γ > log(1+√2) such that
the Taylor coefficients aₖ of F_p⁻¹ satisfy ∑|aₖ|γᵏ = 1.

This is the key quantitative result that connects the strict improvement from
Theorem 4.4 to an explicit embedding that gives KG < Krivine bound.

## Strategy

1. From Theorem 4.4, choose η > 0 with H_η(i)/i > log(1+√2)
2. From Lemma 5.3, for r < 1, choose p small enough that F_p has analytic inverse on rD
3. From Lemma 5.4, get first-order expansion F_p⁻¹(z) = sin(z) + p·ψ(z) + O(p²)
4. Define γ via the summability radius: γ = sup{t : ∑|aₖ|tᵏ ≤ 1}
5. Show γ > log(1+√2) using Theorem 4.4 and coefficient estimates
-/

open Complex Set Metric Real

noncomputable section

namespace Braverman

/-! ### Taylor coefficients of F_p⁻¹ -/

/-- The Taylor coefficient aₖ of F_p⁻¹ at 0. Since F_p⁻¹ is analytic on disk(r),
    it has a convergent power series at 0 with these coefficients. -/
def taylor_coeff (F_inv : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k F_inv 0 / (Nat.factorial k : ℂ)

/-- F_p⁻¹ is odd (since F_p is odd), so even Taylor coefficients vanish. -/
theorem F_p_inv_odd (η : ℝ) (p r : ℝ) (F_inv : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F_inv (disk r))
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (hInj : InjOn (F_p η p) S)
    (hr : 0 < r) :
    ∀ k : ℕ, taylor_coeff F_inv (2 * k) = 0 := by
  -- Step 1: F_inv(-z) = -F_inv(z) for z ∈ disk r.
  have hF_p_odd : ∀ w : ℂ, w ∈ S → F_p η p (-w) = -F_p η p w := by
    intro w hw
    simp only [F_p]
    rw [H0_odd w hw, H_eta_odd η w hw]
    ring
  -- disk r is symmetric under negation
  have hdisk_neg : ∀ z ∈ disk r, -z ∈ disk r := by
    intro z hz
    rw [mem_disk_iff] at hz ⊢
    rwa [norm_neg]
  -- -w ∈ S whenever w ∈ S
  have hS_neg : ∀ w ∈ S, -w ∈ S := by
    intro w hw
    rw [mem_S_iff] at hw ⊢
    rwa [Complex.neg_re, abs_neg]
  -- F_inv is odd on disk r
  have hodd_disk : ∀ z ∈ disk r, F_inv (-z) = -F_inv z := by
    intro z hz
    have hnz : -z ∈ disk r := hdisk_neg z hz
    -- F_p(F_inv(-z)) = -z
    have h1 : F_p η p (F_inv (-z)) = -z := hFi (-z) hnz
    -- F_p(-F_inv(z)) = -F_p(F_inv(z)) = -z
    have h2 : F_p η p (-F_inv z) = -z := by
      rw [hF_p_odd (F_inv z) (hFS z hz), hFi z hz]
    -- Both F_inv(-z) and -F_inv(z) are in S
    have hm1 : F_inv (-z) ∈ S := hFS (-z) hnz
    have hm2 : -F_inv z ∈ S := hS_neg (F_inv z) (hFS z hz)
    -- By injectivity: F_inv(-z) = -F_inv(z)
    exact hInj hm1 hm2 (h1.trans h2.symm)
  -- Step 2: Use the identity theorem to extend oddness.
  -- g(z) = F_inv(-z) + F_inv(z) is analytic on disk r and vanishes there.
  -- Hence g ≡ 0, so all iterated derivatives of g at 0 vanish.
  -- This gives iteratedDeriv (2k) F_inv 0 = 0.
  --
  -- More directly: F_inv(-z) and -F_inv(z) are analytic at 0 and agree
  -- on disk r (neighborhood of 0). So they have the same iteratedDeriv at 0.
  have h0_mem : (0 : ℂ) ∈ disk r := zero_mem_disk r hr
  have hFeq : (fun z => F_inv (-z)) =ᶠ[nhds 0] (fun z => -F_inv z) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨disk r, (disk_isOpen r).mem_nhds h0_mem,
      fun z hz => hodd_disk z hz⟩
  intro k
  unfold taylor_coeff
  -- From the eventuallyEq, the iterated derivatives agree at 0
  have hdeq : iteratedDeriv (2 * k) (fun z => F_inv (-z)) 0 =
      iteratedDeriv (2 * k) (fun z => -F_inv z) 0 :=
    hFeq.iteratedDeriv_eq (2 * k)
  -- Use iteratedDeriv_comp_neg and iteratedDeriv_fun_neg
  have h1 := iteratedDeriv_comp_neg (2 * k) F_inv 0
  have h2 := iteratedDeriv_fun_neg (2 * k) F_inv 0
  -- h1: iteratedDeriv (2k) (F_inv ∘ (-·)) 0 = (-1)^(2k) • iteratedDeriv (2k) F_inv (-0)
  -- h2: iteratedDeriv (2k) (-F_inv) 0 = -(iteratedDeriv (2k) F_inv 0)
  rw [neg_zero, Even.neg_one_pow (even_two_mul k), one_smul] at h1
  -- h1: iteratedDeriv (2k) (F_inv ∘ (-·)) 0 = iteratedDeriv (2k) F_inv 0
  -- hdeq + h1 + h2: iteratedDeriv (2k) F_inv 0 = -(iteratedDeriv (2k) F_inv 0)
  rw [h1] at hdeq
  rw [h2] at hdeq
  -- hdeq: iteratedDeriv (2k) F_inv 0 = -(iteratedDeriv (2k) F_inv 0)
  have hzero : iteratedDeriv (2 * k) F_inv 0 = 0 :=
    CharZero.eq_neg_self_iff.mp hdeq
  rw [hzero, zero_div]

/-- The embedding weight for the k-th Taylor coefficient. -/
def embedding_weight (a : ℕ → ℂ) (γ : ℝ) (k : ℕ) : ℝ :=
  ‖a k‖ * γ ^ k

/-- The summability condition: ∑ₖ |aₖ| γᵏ = 1 ensures unit norm. -/
def summability_condition (a : ℕ → ℂ) (γ : ℝ) : Prop :=
  HasSum (fun k => embedding_weight a γ k) 1

/-- The summability function: s(t) = ∑ₖ |aₖ| · tᵏ for t ≥ 0.
    When F_inv is analytic on disk(r), this converges for t < r. -/
def summability_fn (F_inv : ℂ → ℂ) (t : ℝ) : ℝ :=
  ∑' k, ‖taylor_coeff F_inv k‖ * t ^ k

/-! ### Existence of summability radius γ -/

/-- At t = 0 we have s(0) = |a₀| = 0 (since F_p⁻¹(0) = 0). -/
theorem summability_fn_zero (F_inv : ℂ → ℂ) (h : F_inv 0 = 0) :
    summability_fn F_inv 0 = 0 := by
  simp only [summability_fn, taylor_coeff]
  convert tsum_zero with k
  rcases k with _ | k
  · simp [h]
  · simp [zero_pow (Nat.succ_ne_zero k)]

/-- Even Taylor coefficients of sin vanish (sin is odd). -/
private theorem taylor_coeff_sin_even (k : ℕ) :
    taylor_coeff Complex.sin (2 * k) = 0 := by
  unfold taylor_coeff
  -- sin is odd: sin(-z) = -sin(z)
  have hodd : ∀ z : ℂ, Complex.sin (-z) = -Complex.sin z :=
    Complex.sin_neg
  have h1 := iteratedDeriv_comp_neg (2 * k) Complex.sin (0 : ℂ)
  have h2 := iteratedDeriv_fun_neg (2 * k) Complex.sin (0 : ℂ)
  have heq : (fun x => Complex.sin (-x)) = (fun x => -Complex.sin x) := funext hodd
  rw [heq, neg_zero] at h1
  rw [h2] at h1
  rw [Even.neg_one_pow (even_two_mul k), one_smul] at h1
  rw [neg_eq_self.mp h1, zero_div]


/-- The (2k+1)-th iterated derivative of sin at 0 is (-1)^k. -/
private theorem iteratedDeriv_sin_odd_at_zero (k : ℕ) :
    iteratedDeriv (2 * k + 1) Complex.sin 0 = (-1) ^ k := by
  induction k with
  | zero =>
    rw [show 2 * 0 + 1 = 0 + 1 from by ring]
    rw [Complex.iteratedDeriv_add_one_sin]
    simp [Complex.cos_zero]
  | succ n ih =>
    -- 2*(n+1)+1 = (2*n+1+1) + 1 = (2*n+2) + 1
    -- iteratedDeriv ((2n+1+1)+1) sin = iteratedDeriv (2n+1+1) cos (by add_one_sin)
    --                                = -(iteratedDeriv (2n+1) sin)  (by add_one_cos)
    -- At 0: -(-1)^n = (-1)^(n+1)
    conv_lhs => rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 from by ring]
    rw [Complex.iteratedDeriv_add_one_sin,
        Complex.iteratedDeriv_add_one_cos]
    simp only [Pi.neg_apply]
    rw [ih]; ring

/-- The norm of the (2k+1)-th Taylor coefficient of sin is 1/(2k+1)!. -/
private theorem norm_taylor_coeff_sin_odd (k : ℕ) :
    ‖taylor_coeff Complex.sin (2 * k + 1)‖ = 1 / ((2 * k + 1).factorial : ℝ) := by
  unfold taylor_coeff
  rw [iteratedDeriv_sin_odd_at_zero k]
  rw [norm_div]
  congr 1
  · simp [norm_pow, norm_neg, norm_one]
  · rw [Complex.norm_natCast]

set_option maxHeartbeats 1600000 in
/-- The summability function of sin at t ≥ 0 equals sinh(t).
    ∑ ‖aₖ‖ tᵏ = ∑ t^(2k+1)/(2k+1)! = sinh(t).
    Not on the main proof path (Theorem 5.1 does not depend on this). -/
theorem summability_fn_sin_eq_sinh (t : ℝ) (ht : 0 ≤ t) :
    summability_fn Complex.sin t = Real.sinh t := by
  unfold summability_fn
  set f : ℕ → ℝ := fun k => ‖taylor_coeff Complex.sin k‖ * t ^ k with hf_def
  have heven_zero : ∀ k, f (2 * k) = 0 := fun k => by
    simp only [f, taylor_coeff_sin_even k, norm_zero, zero_mul]
  have heven_summable : Summable (fun k => f (2 * k)) := by
    rw [show (fun k => f (2 * k)) = fun _ => (0 : ℝ) from funext heven_zero]
    exact summable_zero
  have hodd_eq : ∀ k, f (2 * k + 1) =
      t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
    intro k; simp only [f, norm_taylor_coeff_sin_odd k]; ring
  have hodd_summable : Summable (fun k => f (2 * k + 1)) := by
    rw [show (fun k => f (2 * k + 1)) =
        fun k => t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) from funext hodd_eq]
    exact (Real.hasSum_sinh t).summable
  rw [← tsum_even_add_odd heven_summable hodd_summable]
  rw [show (fun k => f (2 * k)) = fun _ => (0 : ℝ) from funext heven_zero, tsum_zero, zero_add]
  rw [show (fun k => f (2 * k + 1)) =
      fun k => t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) from funext hodd_eq]
  exact (Real.hasSum_sinh t).tsum_eq

theorem sin_summability_at_log :
    summability_fn Complex.sin (Real.log (1 + Real.sqrt 2)) = 1 := by
  -- log(1+√2) ≥ 0
  have h_log_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  -- summability_fn sin (log(1+√2)) = sinh(log(1+√2))
  rw [summability_fn_sin_eq_sinh _ h_log_pos.le]
  -- sinh(log(1+√2)) = sinh(arsinh(1)) = 1
  have h_arsinh : Real.log (1 + Real.sqrt 2) = Real.arsinh 1 := by
    unfold Real.arsinh; norm_num
  rw [h_arsinh, Real.sinh_arsinh]

/-! ### Auxiliary lemmas for Theorem 5.1 -/

-- Key fact: log(1+√2) < 1, since 1+√2 < e
private theorem log_one_add_sqrt2_lt_one : Real.log (1 + Real.sqrt 2) < 1 := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  rw [Real.log_lt_iff_lt_exp (by linarith)]
  -- 1 + √2 < exp(1): √2 < 3/2 and exp(1) ≥ 5/2
  have h_sqrt2 := Real.sqrt_two_lt_three_halves
  have h_exp : 5 / 2 ≤ Real.exp 1 := by
    have := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 3
    simp [Finset.sum_range_succ] at this
    linarith
  linarith

/-- H_eta maps 0 to 0 (by oddness: H_eta(-0) = -H_eta(0), so H_eta(0) = -H_eta(0)). -/
private theorem H_eta_zero (η : ℝ) : H_eta η 0 = 0 := by
  have h := H_eta_odd η 0 zero_mem_S
  simp only [neg_zero] at h
  -- h : H_eta η 0 = -H_eta η 0, so H_eta η 0 = 0
  exact CharZero.eq_neg_self_iff.mp h

/-- F_p maps 0 to 0. -/
private theorem F_p_zero' (η : ℝ) (p : ℝ) : F_p η p 0 = 0 := by
  -- F_p η p 0 = (1 - p) * H0(0) + p * H_eta(η, 0) = 0
  -- Use H0 = H_eta 0, so H0(0) = H_eta(0, 0) = 0
  have h1 : H_eta 0 0 = 0 := H_eta_zero 0
  have h2 : H_eta η 0 = 0 := H_eta_zero η
  -- H0 is definitionally H_eta 0
  change (1 - ↑p) * H_eta 0 0 + ↑p * H_eta η 0 = 0
  rw [h1, h2]; ring

/-- If F_p ∘ F_inv = id on disk(r) and F_p is injective on S, then F_inv(0) = 0.
    Proof: F_p_inv_odd at k=0 gives taylor_coeff F_inv 0 = 0, i.e., F_inv(0) = 0. -/
private theorem F_inv_zero_of_right_inverse (η : ℝ) (p : ℝ) (r : ℝ) (hr : 0 < r)
    (F_inv : ℂ → ℂ)
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hInj : InjOn (F_p η p) S) :
    F_inv 0 = 0 := by
  have h := F_p_inv_odd η p r F_inv hFa hFi hFS hInj hr 0
  -- h : taylor_coeff F_inv (2 * 0) = 0, i.e., F_inv 0 = 0
  simp only [Nat.zero_eq, mul_zero] at h
  unfold taylor_coeff at h
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  exact h

/-- sinh(9/10) > 1. Follows from sinh being strictly increasing and
    arsinh(1) = log(1+√2) < 9/10. -/
theorem sinh_nine_tenths_gt_one : Real.sinh (9 / 10) > 1 := by
  -- Strategy: sinh(arsinh(1)) = 1, arsinh(1) = log(1+√2) < 9/10, sinh is strictly increasing
  rw [show (1 : ℝ) = Real.sinh (Real.arsinh 1) from (Real.sinh_arsinh 1).symm]
  apply Real.sinh_lt_sinh.mpr
  -- Need: arsinh(1) < 9/10, i.e., log(1+√2) < 9/10
  rw [show Real.arsinh 1 = Real.log (1 + Real.sqrt 2) from by unfold Real.arsinh; norm_num]
  -- log(1+√2) < 9/10 ↔ 1+√2 < exp(9/10)
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h_sqrt : Real.sqrt 2 < 142 / 100 := by
    rw [Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 142/100)]
    norm_num
  have h_exp : 588921 / 240000 ≤ Real.exp (9 / 10) := by
    have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 9/10 by norm_num) 5
    simp [Finset.sum_range_succ] at this
    linarith
  linarith

/-- **Cauchy coefficient perturbation bound** (paper equation 78).
    If two functions g, h are analytic on disk(r) and ‖g(z) - h(z)‖ ≤ δ on disk(r'),
    with 0 < r' < r, then their Taylor coefficients satisfy
    ‖taylor_coeff g k - taylor_coeff h k‖ ≤ δ / r'^k.

    This follows from the Cauchy estimate for derivatives:
    ‖iteratedDeriv n f c‖ ≤ n! * sup_{|z|=r'} ‖f(z)‖ / r'^n -/
private theorem taylor_coeff_sub_bound
    {g h : ℂ → ℂ} {r r' δ : ℝ}
    (hr' : 0 < r') (hr'r : r' < r)
    (hg : AnalyticOnNhd ℂ g (disk r))
    (hh : AnalyticOnNhd ℂ h (disk r))
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) r', ‖g z - h z‖ ≤ δ)
    (k : ℕ) :
    ‖taylor_coeff g k - taylor_coeff h k‖ ≤ δ / r' ^ k := by
  simp only [taylor_coeff, ← sub_div]
  have h0mem : (0 : ℂ) ∈ disk r := zero_mem_disk r (lt_trans hr' hr'r)
  have hga : ContDiffAt ℂ k g 0 := (hg 0 h0mem).contDiffAt.of_le le_top
  have hha : ContDiffAt ℂ k h 0 := (hh 0 h0mem).contDiffAt.of_le le_top
  rw [← iteratedDeriv_sub hga hha]
  -- DiffContOnCl for g - h on ball 0 r'
  have hclosed_sub : Metric.closedBall (0 : ℂ) r' ⊆ disk r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [mem_disk_iff]; linarith
  have hdiffOn : DifferentiableOn ℂ (g - h) (disk r) :=
    (hg.differentiableOn).sub (hh.differentiableOn)
  have hDCOC : DiffContOnCl ℂ (g - h) (Metric.ball (0 : ℂ) r') :=
    hdiffOn.diffContOnCl_ball hclosed_sub
  -- Bound on sphere (sphere ⊆ closedBall, so hbound applies)
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) r', ‖(g - h) z‖ ≤ δ := by
    intro z hz
    exact hbound z (Metric.sphere_subset_closedBall hz)
  -- Apply Cauchy estimate
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr' hDCOC hsphere
  -- hCauchy : ‖iteratedDeriv k (g - h) 0‖ ≤ k! * δ / r'^k
  -- Goal: ‖iteratedDeriv k (g - h) 0 / k!‖ ≤ δ / r'^k
  -- Goal: ‖iteratedDeriv k (g - h) 0 / k!‖ ≤ δ / r'^k
  -- hCauchy: ‖iteratedDeriv k (g - h) 0‖ ≤ k! * δ / r'^k
  rw [norm_div, Complex.norm_natCast]
  have hk_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
  exact div_le_div_of_nonneg_right hCauchy (le_of_lt hk_pos) |>.trans
    (by rw [mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hk_pos)])

/-- The summability function of F_inv exceeds 1 at t, given:
    - F_inv and sin are both analytic on disk(r)
    - Their Taylor coefficients differ by at most δ/r'^k (from Cauchy estimate on closedBall r')
    - t < r' (so the geometric series ∑(t/r')^k converges)
    - The error δ·t/(r'-t) is smaller than summability_fn sin t - 1

    This is the key estimate (paper equation 79). -/
theorem summability_fn_gt_one
    (F_inv : ℂ → ℂ) (r r' t : ℝ)
    (hr : 0 < r) (hr' : 0 < r') (ht : 0 < t) (htr' : t < r') (hr'r : r' < r)
    (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hsin : AnalyticOnNhd ℂ Complex.sin (disk r))
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) r', ‖F_inv z - Complex.sin z‖ ≤ δ)
    (hδ_nn : 0 ≤ δ)
    (hδ_small : summability_fn Complex.sin t - δ * r' / (r' - t) > 1) :
    summability_fn F_inv t > 1 := by
  -- Step 1: Coefficient bound from Cauchy estimate
  have hcoeff : ∀ k, ‖taylor_coeff F_inv k - taylor_coeff Complex.sin k‖ ≤ δ / r' ^ k :=
    taylor_coeff_sub_bound hr' hr'r hFa hsin hbound
  -- Step 2: Term-wise lower bound via reverse triangle inequality
  have hterm : ∀ k, ‖taylor_coeff F_inv k‖ * t ^ k ≥
      ‖taylor_coeff Complex.sin k‖ * t ^ k - δ / r' ^ k * t ^ k := by
    intro k
    have ht_nn : 0 ≤ t ^ k := pow_nonneg (le_of_lt ht) k
    have h_norm_ge : ‖taylor_coeff F_inv k‖ ≥ ‖taylor_coeff Complex.sin k‖ - δ / r' ^ k := by
      have h1 := norm_sub_norm_le (taylor_coeff Complex.sin k) (taylor_coeff F_inv k)
      rw [norm_sub_rev] at h1; linarith [hcoeff k]
    nlinarith
  -- Step 3: Summability prerequisites
  have htr'_ratio : t / r' < 1 := (div_lt_one (by linarith : 0 < r')).mpr htr'
  have htr'_nn : 0 ≤ t / r' := div_nonneg (le_of_lt ht) (le_of_lt hr')
  -- The error series ∑ δ/r'^k * t^k = δ * ∑ (t/r')^k is summable
  have herr_eq : ∀ k, δ / r' ^ k * t ^ k = δ * (t / r') ^ k := by
    intro k; rw [div_pow]; ring
  have herr_summable : Summable (fun k => δ / r' ^ k * t ^ k) := by
    rw [show (fun k => δ / r' ^ k * t ^ k) = (fun k => δ * (t / r') ^ k) from funext herr_eq]
    exact (summable_geometric_of_lt_one htr'_nn htr'_ratio).const_smul δ
  -- The sin series ∑ ‖a_k(sin)‖ * t^k is summable (sin is entire)
  have hsin_summable : Summable (fun k => ‖taylor_coeff Complex.sin k‖ * t ^ k) := by
    -- Dominated by exp(t): ‖taylor_coeff sin k‖ * t^k ≤ t^k / k!
    have hexp_summable : Summable (fun k : ℕ => t ^ k / ↑k.factorial) :=
      Real.summable_pow_div_factorial t
    apply Summable.of_nonneg_of_le (fun k => by positivity) _ hexp_summable
    intro k
    unfold taylor_coeff
    rw [norm_div, Complex.norm_natCast]
    have hsin_deriv : ‖iteratedDeriv k Complex.sin 0‖ ≤ 1 := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- even case: iteratedDeriv (2m) sin 0 = 0
        have h2m : k = 2 * m := by omega
        have := taylor_coeff_sin_even m
        unfold taylor_coeff at this
        have hfact_ne : (Nat.factorial (2 * m) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · rw [h2m, h]; simp
        · exact absurd h hfact_ne
      · -- odd case: iteratedDeriv (2m+1) sin 0 = (-1)^m, norm = 1
        rw [hm, iteratedDeriv_sin_odd_at_zero m]
        simp [norm_pow, norm_neg]
    calc ‖iteratedDeriv k Complex.sin 0‖ / ↑k.factorial * t ^ k
        ≤ 1 / ↑k.factorial * t ^ k := by
          apply mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hsin_deriv (by positivity)) (by positivity)
      _ = t ^ k / ↑k.factorial := by ring
  -- The F_inv series is summable (F_inv is analytic on disk(r), t < r)
  have hFinv_summable : Summable (fun k => ‖taylor_coeff F_inv k‖ * t ^ k) := by
    -- ‖a_k(F_inv)‖ ≤ ‖a_k(sin)‖ + δ/r'^k, so ‖a_k(F_inv)‖ * t^k ≤ (‖a_k(sin)‖ + δ/r'^k) * t^k
    -- Both sin and error series are summable, so the dominating series is summable
    apply Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by
        have := norm_sub_norm_le (taylor_coeff F_inv k) (taylor_coeff Complex.sin k)
        have hc := hcoeff k
        have ht_nn : 0 ≤ t ^ k := pow_nonneg (le_of_lt ht) k
        nlinarith)
      (hsin_summable.add herr_summable)
  -- The difference series is summable
  have hdiff_summable : Summable (fun k =>
      ‖taylor_coeff Complex.sin k‖ * t ^ k - δ / r' ^ k * t ^ k) :=
    hsin_summable.sub herr_summable
  -- Step 4: Apply tsum_le_tsum to get summability_fn F_inv t ≥ ∑(sin - error)
  have h_tsum_ge : summability_fn F_inv t ≥
      ∑' k, (‖taylor_coeff Complex.sin k‖ * t ^ k - δ / r' ^ k * t ^ k) := by
    apply le_of_eq_of_le _ (Summable.tsum_le_tsum (fun k => hterm k) hdiff_summable hFinv_summable)
    rfl
  -- Step 5: Split the tsum of differences
  have h_tsum_split : ∑' k, (‖taylor_coeff Complex.sin k‖ * t ^ k - δ / r' ^ k * t ^ k) =
      summability_fn Complex.sin t - ∑' k, δ / r' ^ k * t ^ k := by
    rw [hsin_summable.tsum_sub herr_summable]
    rfl
  -- Step 6: Evaluate the geometric error series
  have h_geom : ∑' k, δ / r' ^ k * t ^ k = δ * r' / (r' - t) := by
    rw [show (fun k => δ / r' ^ k * t ^ k) = (fun k => δ * (t / r') ^ k) from funext herr_eq]
    rw [tsum_mul_left, tsum_geometric_of_lt_one htr'_nn htr'_ratio]
    field_simp
  -- Step 7: Combine
  linarith [h_tsum_ge, h_tsum_split, h_geom]

/-- For an analytic function on disk(r), the series ∑ ‖taylor_coeff F_inv k‖ * t^k
    is summable when 0 ≤ t < r. Uses Cauchy coefficient bounds + geometric series. -/
theorem summable_weights_of_lt_radius
    (F_inv : ℂ → ℂ) (r t : ℝ)
    (hr : 0 < r) (ht0 : 0 ≤ t) (htr : t < r)
    (hF : AnalyticOnNhd ℂ F_inv (disk r)) :
    Summable (fun k => ‖taylor_coeff F_inv k‖ * t ^ k) := by
  -- Step 1: Choose R strictly between t and r
  set R := (t + r) / 2 with hR_def
  have hR_pos : 0 < R := by linarith
  have ht_lt_R : t < R := by linarith
  have hR_lt_r : R < r := by linarith
  -- Step 2: closedBall(0, R) ⊆ disk(r), and is compact
  have hclosed_sub : Metric.closedBall (0 : ℂ) R ⊆ disk r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [mem_disk_iff]; linarith
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) R) :=
    ProperSpace.isCompact_closedBall 0 R
  -- Step 3: F_inv is continuous on closedBall(0, R), so bounded there
  have hcont : ContinuousOn F_inv (Metric.closedBall (0 : ℂ) R) :=
    (hF.mono hclosed_sub).continuousOn
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  -- Step 4: The zero function is analytic on disk(r)
  have hzero_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (disk r) :=
    analyticOnNhd_const
  -- Step 5: ‖F_inv z - 0‖ ≤ M on closedBall(0, R)
  have hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖F_inv z - (fun _ => (0 : ℂ)) z‖ ≤ M := by
    intro z hz; simp only [sub_zero]; exact hM z hz
  -- Step 6: By Cauchy coefficient bound, ‖taylor_coeff F_inv k - taylor_coeff 0 k‖ ≤ M / R^k
  have hcoeff := taylor_coeff_sub_bound hR_pos hR_lt_r hF hzero_analytic hbound
  -- Step 7: taylor_coeff of zero function is 0
  have hzero_coeff : ∀ k, taylor_coeff (fun _ : ℂ => (0 : ℂ)) k = 0 := by
    intro k; unfold taylor_coeff
    simp
  -- Step 8: So ‖taylor_coeff F_inv k‖ ≤ M / R^k
  have hcoeff_bound : ∀ k, ‖taylor_coeff F_inv k‖ ≤ M / R ^ k := by
    intro k; specialize hcoeff k; rw [hzero_coeff k, sub_zero] at hcoeff; exact hcoeff
  -- Step 9: Dominate by geometric series M * (t/R)^k
  have htR_ratio : t / R < 1 := (div_lt_one hR_pos).mpr ht_lt_R
  have htR_nn : 0 ≤ t / R := div_nonneg ht0 (le_of_lt hR_pos)
  have hgeom : Summable (fun k => M * (t / R) ^ k) :=
    (summable_geometric_of_lt_one htR_nn htR_ratio).const_smul M
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg ht0 k))
    _ hgeom
  intro k
  have ht_nn : 0 ≤ t ^ k := pow_nonneg ht0 k
  have hR_pow_pos : (0 : ℝ) < R ^ k := pow_pos hR_pos k
  calc ‖taylor_coeff F_inv k‖ * t ^ k
      ≤ M / R ^ k * t ^ k :=
        mul_le_mul_of_nonneg_right (hcoeff_bound k) ht_nn
    _ = M * (t ^ k / R ^ k) := by
        rw [div_mul_comm, mul_comm]
    _ = M * (t / R) ^ k := by
        rw [← div_pow]

/-- The summability function is continuous on [0, r) when F_inv is analytic on disk(r). -/
private theorem summability_fn_continuousOn (F_inv : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F_inv (disk r)) :
    ContinuousOn (summability_fn F_inv) (Ico 0 r) := by
  -- Use continuousOn_of_locally_continuousOn: show continuity on Ico 0 r by showing
  -- continuity on Icc 0 r' for each r' < r (using continuousOn_tsum with dominator).
  apply continuousOn_of_locally_continuousOn
  intro t ht
  -- ht : t ∈ Ico 0 r, so 0 ≤ t and t < r
  -- Pick r' strictly between t and r
  set r' := (t + r) / 2 with hr'_def
  have hr'_pos : 0 < r' := by linarith [ht.1]
  have ht_lt_r' : t < r' := by linarith [ht.2]
  have hr'_lt_r : r' < r := by linarith [ht.2]
  -- The open interval (t - ε, r') ∩ Ico 0 r is a neighborhood of t in Ico 0 r
  refine ⟨Iio r', isOpen_Iio, by exact ht_lt_r', ?_⟩
  -- Show continuity on Ico 0 r ∩ Iio r' = Ico 0 r'
  have hss : Ico 0 r ∩ Iio r' ⊆ Icc 0 r' := by
    intro x ⟨⟨hx0, _⟩, hxr'⟩
    exact ⟨hx0, le_of_lt hxr'⟩
  apply ContinuousOn.mono _ hss
  -- Show continuity on Icc 0 r' using continuousOn_tsum
  unfold summability_fn
  -- Provide the dominator explicitly
  set u : ℕ → ℝ := fun k => ‖taylor_coeff F_inv k‖ * r' ^ k with hu_def
  apply continuousOn_tsum (u := u)
  · -- Each term is continuous
    intro k
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_pow k
  · -- Summable dominator: ∑ ‖coeff_k‖ * r'^k < ∞
    exact summable_weights_of_lt_radius F_inv r r' hr (by linarith [ht.1]) hr'_lt_r hF
  · -- Domination: for x ∈ Icc 0 r', ‖‖coeff_k‖ * x^k‖ ≤ ‖coeff_k‖ * r'^k
    intro k x hx
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hx.1 k))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact pow_le_pow_left₀ hx.1 hx.2 k

/-- By IVT: if summability_fn is 0 at 0 and > 1 at t₀, then there exists γ ∈ (0, t₀)
    with summability_fn = 1, giving the summability condition. -/
theorem exists_gamma_with_summability
    (F_inv : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F_inv (disk r))
    (hF0 : F_inv 0 = 0)
    (t₀ : ℝ) (ht₀_pos : 0 < t₀) (ht₀_lt_r : t₀ < r)
    (h_gt_one : summability_fn F_inv t₀ > 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < t₀ ∧
      summability_condition (taylor_coeff F_inv) γ := by
  -- summability_fn F_inv 0 = 0 and summability_fn F_inv t₀ > 1
  have h0 : summability_fn F_inv 0 = 0 := summability_fn_zero F_inv hF0
  -- Continuity on [0, r) ⊇ [0, t₀]
  have hcont := summability_fn_continuousOn F_inv r hr hF
  -- Restrict to [0, t₀] ⊆ [0, r)
  have hcont_sub : ContinuousOn (summability_fn F_inv) (Icc 0 t₀) :=
    hcont.mono (by intro x ⟨hx0, hxt⟩; exact ⟨hx0, lt_of_le_of_lt hxt ht₀_lt_r⟩)
  -- IVT: since f(0) = 0 < 1 < f(t₀), there exists γ ∈ [0, t₀] with f(γ) = 1
  have h1_mem : (1 : ℝ) ∈ Icc (summability_fn F_inv 0) (summability_fn F_inv t₀) := by
    rw [h0]; exact ⟨by linarith, le_of_lt h_gt_one⟩
  have ht₀_nn : (0 : ℝ) ≤ t₀ := le_of_lt ht₀_pos
  obtain ⟨γ, hγ_mem, hγ_val⟩ := intermediate_value_Icc ht₀_nn hcont_sub h1_mem
  -- γ ∈ [0, t₀] and summability_fn F_inv γ = 1
  refine ⟨γ, ?_, ?_, ?_⟩
  · -- γ > 0: if γ = 0 then summability_fn F_inv 0 = 0 ≠ 1
    by_contra h_le
    push_neg at h_le
    have : γ = 0 := le_antisymm h_le hγ_mem.1
    rw [this, h0] at hγ_val; linarith
  · -- γ < t₀: if γ = t₀ then summability_fn F_inv t₀ = 1, but we have > 1
    rcases lt_or_eq_of_le hγ_mem.2 with h | h
    · exact h
    · exfalso; rw [h] at hγ_val; linarith
  · -- summability_condition: HasSum (fun k => ‖coeff_k‖ * γ^k) 1
    -- hγ_val : summability_fn F_inv γ = 1, i.e., ∑' k, ‖coeff_k‖ * γ^k = 1
    unfold summability_condition embedding_weight
    -- Goal: HasSum (fun k => ‖taylor_coeff F_inv k‖ * γ^k) 1
    -- hγ_val : summability_fn F_inv γ = 1, i.e., ∑' k, ‖coeff_k‖ * γ^k = 1
    -- Need summability to convert tsum = 1 to HasSum
    -- Summability follows from γ < t₀ < r and F_inv analytic on disk(r)
    have hγ_lt_r : γ < r := lt_of_le_of_lt hγ_mem.2 ht₀_lt_r
    have hγ_sum := summable_weights_of_lt_radius F_inv r γ hr hγ_mem.1 hγ_lt_r hF
    rw [← hγ_val]
    exact hγ_sum.hasSum

/-! ### Conjugation symmetry -/

/-- H_eta preserves conjugation: H_eta(conj z) = conj(H_eta(z)).
    This follows from the integral definition: the integrand with conj(z) is the
    conjugate of the integrand with z (since f_eta is real-valued). -/
private theorem H_eta_conj (η : ℝ) (z : ℂ) :
    H_eta η (starRingEnd ℂ z) = starRingEnd ℂ (H_eta η z) := by
  simp only [H_eta]
  rw [← integral_conj]
  congr 1; ext p
  simp only [kernel_exponent, map_div₀, map_mul, map_sub, map_add, map_neg,
    map_pow, Complex.conj_ofReal, map_one, map_ofNat, ← Complex.exp_conj]

/-- F_p preserves conjugation: F_p(conj z) = conj(F_p(z)). -/
private theorem F_p_conj_eq (η : ℝ) (p : ℝ) (z : ℂ) :
    F_p η p (starRingEnd ℂ z) = starRingEnd ℂ (F_p η p z) := by
  simp only [F_p, H0]
  rw [H_eta_conj 0 z, H_eta_conj η z]
  simp [map_add, map_mul, map_sub, Complex.conj_ofReal]

/-- The imaginary unit I is in S. -/
private theorem I_mem_S : Complex.I ∈ S := by
  rw [mem_S_iff]; simp [Complex.I_re]

/-- varphi at 0 equals L₀: (H₀(I)/I).re = log(1+√2). -/
private theorem H0_I_div_I_re :
    (H0 Complex.I / Complex.I).re = Real.log (1 + Real.sqrt 2) := by
  have := varphi_zero
  simp only [varphi, H0] at this
  exact this

/-! ### Conjugation symmetry and purely imaginary property -/

/-- The function z ↦ conj(F_inv(conj z)) is analytic on disk(r).
    Proof: if F_inv(z) = ∑ aₙ zⁿ, then conj(F_inv(conj z)) = ∑ conj(aₙ) zⁿ,
    which has the same radius of convergence. -/
private theorem conj_F_inv_conj_analytic (η : ℝ) (p r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (F_inv : ℂ → ℂ) (hFa : AnalyticOnNhd ℂ F_inv (disk r)) :
    AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (F_inv (starRingEnd ℂ z))) (disk r) := by
  -- Strategy: show differentiability on the open disk, then use the complex-analytic theorem
  -- that complex-differentiable ⟹ analytic (DifferentiableOn.analyticOnNhd)
  have hopen : IsOpen (disk r) := Metric.isOpen_ball
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  have hcz_mem : starRingEnd ℂ z ∈ disk r := by
    simp only [disk, Metric.mem_ball, dist_zero_right] at hz ⊢
    rwa [Complex.norm_conj]
  -- F_inv is differentiable at conj(z) since conj(z) ∈ disk r
  have hd : DifferentiableAt ℂ F_inv (starRingEnd ℂ z) :=
    ((hFa _ hcz_mem) : AnalyticAt ℂ F_inv (starRingEnd ℂ z)).differentiableAt
  -- By DifferentiableAt.conj_conj: conj ∘ F_inv ∘ conj is differentiable at conj(conj(z)) = z
  have hcc := DifferentiableAt.conj_conj hd
  rw [starRingEnd_self_apply] at hcc
  exact DifferentiableAt.differentiableWithinAt hcc

/-- F_inv has conjugation symmetry: F_inv(conj z) = conj(F_inv z) for z ∈ disk(r).
    Proof: the function g(z) = conj(F_inv(conj z)) is analytic, satisfies
    F_p(g(z)) = z, maps into S, and g(0) = 0. By right_inverse_unique, g = F_inv. -/
private theorem F_inv_conj_symmetry (η : ℝ) (p r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hp : 0 < p)
    (F_inv : ℂ → ℂ) (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (hF0 : F_inv 0 = 0)
    (hFp_an : AnalyticAt ℂ (F_p η p) 0)
    (hFp_deriv : deriv (F_p η p) 0 ≠ 0) :
    ∀ z ∈ disk r, F_inv (starRingEnd ℂ z) = starRingEnd ℂ (F_inv z) := by
  set g := fun z => starRingEnd ℂ (F_inv (starRingEnd ℂ z))
  -- g is analytic on disk(r)
  have hga : AnalyticOnNhd ℂ g (disk r) := conj_F_inv_conj_analytic η p r hr0 hr1 F_inv hFa
  -- Helper: conj z ∈ disk r when z ∈ disk r
  have hconj_mem : ∀ z ∈ disk r, starRingEnd ℂ z ∈ disk r := by
    intro z hz; rw [mem_disk_iff] at hz ⊢; rwa [Complex.norm_conj]
  -- g is a right inverse of F_p
  have hgi : ∀ z ∈ disk r, F_p η p (g z) = z := by
    intro z hz
    show F_p η p (starRingEnd ℂ (F_inv (starRingEnd ℂ z))) = z
    rw [F_p_conj_eq, hFi _ (hconj_mem z hz)]; simp
  -- g maps into S (since conj(S) = S: Re(conj w) = Re w)
  have hgS : ∀ z ∈ disk r, g z ∈ S := by
    intro z hz
    show starRingEnd ℂ (F_inv (starRingEnd ℂ z)) ∈ S
    rw [mem_S_iff, Complex.conj_re]
    exact (mem_S_iff _).mp (hFS _ (hconj_mem z hz))
  -- g(0) = 0
  have hg0 : g 0 = 0 := by simp [g, hF0]
  -- By right_inverse_unique: g = F_inv on disk(r)
  have heq := right_inverse_unique η p r hr0 hr1 F_inv g hFa hga hFi hgi hFS hgS hF0 hg0
    hFp_an hFp_deriv
  -- heq : Set.EqOn F_inv g (disk r), meaning ∀ z ∈ disk r, F_inv z = g z
  -- We want: F_inv(conj z) = conj(F_inv z)
  -- Apply heq to conj z: F_inv(conj z) = g(conj z) = conj(F_inv(conj(conj z))) = conj(F_inv z)
  intro z hz
  have h := heq (hconj_mem z hz)  -- F_inv(conj z) = g(conj z)
  simp only [g, starRingEnd_self_apply] at h  -- F_inv(conj z) = conj(F_inv z)
  exact h

/-- F_inv is odd: F_inv(-z) = -F_inv(z) for z ∈ disk(r).
    Proof: h(z) = -F_inv(-z) is analytic on disk(r), satisfies F_p(h(z)) = z
    (using F_p(-w) = -F_p(w)), maps into S, and h(0) = 0.
    By right_inverse_unique, h = F_inv. -/
theorem F_inv_odd (η : ℝ) (p r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hp : 0 < p)
    (F_inv : ℂ → ℂ) (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (hF0 : F_inv 0 = 0)
    (hFp_an : AnalyticAt ℂ (F_p η p) 0)
    (hFp_deriv : deriv (F_p η p) 0 ≠ 0) :
    ∀ z ∈ disk r, F_inv (-z) = -F_inv z := by
  -- Helper: -z ∈ disk r when z ∈ disk r
  have hneg_mem : ∀ z ∈ disk r, -z ∈ disk r := by
    intro z hz; rw [mem_disk_iff] at hz ⊢; rwa [norm_neg]
  set g_odd := fun z => -F_inv (-z)
  -- g_odd is analytic on disk(r): composition of analytic maps
  have hga : AnalyticOnNhd ℂ g_odd (disk r) := by
    intro z hz
    show AnalyticAt ℂ (fun z => -F_inv (-z)) z
    exact ((hFa _ (hneg_mem z hz)).comp_of_eq (analyticAt_id.neg) (by simp)).neg
  -- g_odd is a right inverse of F_p
  have hgi : ∀ z ∈ disk r, F_p η p (g_odd z) = z := by
    intro z hz
    show F_p η p (-F_inv (-z)) = z
    have hFS' : F_inv (-z) ∈ S := hFS _ (hneg_mem z hz)
    rw [show F_p η p (-F_inv (-z)) = -(F_p η p (F_inv (-z))) from by
      simp only [F_p]; rw [H0_odd _ hFS', H_eta_odd _ _ hFS']; ring]
    rw [hFi _ (hneg_mem z hz), neg_neg]
  -- g_odd maps into S
  have hgS : ∀ z ∈ disk r, g_odd z ∈ S := by
    intro z hz
    show -F_inv (-z) ∈ S
    rw [mem_S_iff, Complex.neg_re, abs_neg]
    exact (mem_S_iff _).mp (hFS _ (hneg_mem z hz))
  -- g_odd(0) = 0
  have hg0 : g_odd 0 = 0 := by simp [g_odd, hF0]
  -- By right_inverse_unique: g_odd = F_inv on disk(r)
  have heq := right_inverse_unique η p r hr0 hr1 F_inv g_odd hFa hga hFi hgi hFS hgS hF0 hg0
    hFp_an hFp_deriv
  -- heq : F_inv z = g_odd z = -F_inv(-z) for z ∈ disk r
  -- Want: F_inv(-z) = -F_inv(z)
  -- Apply heq to -z: F_inv(-z) = g_odd(-z) = -F_inv(-(-z)) = -F_inv(z)
  intro z hz
  have h := heq (hneg_mem z hz)  -- F_inv(-z) = g_odd(-z)
  simp only [g_odd, neg_neg] at h  -- F_inv(-z) = -F_inv(z)
  exact h

/-- F_inv(γI) is purely imaginary when F_inv has conjugation symmetry and is odd.
    Proof: conj(γI) = -γI, so F_inv(conj(γI)) = F_inv(-γI) = -F_inv(γI) (oddness).
    Also F_inv(conj(γI)) = conj(F_inv(γI)) (conjugation). So conj(F_inv(γI)) = -F_inv(γI),
    meaning Re(F_inv(γI)) = 0. -/
private theorem F_inv_gammaI_re_eq_zero (η : ℝ) (p r γ : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hp : 0 < p) (hγ : 0 < γ) (hγr : γ < r)
    (F_inv : ℂ → ℂ) (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (hF0 : F_inv 0 = 0)
    (hFp_an : AnalyticAt ℂ (F_p η p) 0)
    (hFp_deriv : deriv (F_p η p) 0 ≠ 0)
    (hF_odd : ∀ z ∈ disk r, F_inv (-z) = -F_inv z) :
    (F_inv (↑γ * Complex.I)).re = 0 := by
  have hγI_mem : ↑γ * Complex.I ∈ disk r := by
    rw [mem_disk_iff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hγ]; exact hγr
  -- conj(γI) = -γI
  have hconj_γI : starRingEnd ℂ (↑γ * Complex.I) = -(↑γ * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  -- F_inv(conj(γI)) = conj(F_inv(γI)) (conjugation symmetry)
  have h1 := F_inv_conj_symmetry η p r hr0 hr1 hp F_inv hFa hFi hFS hF0 hFp_an hFp_deriv
    (↑γ * Complex.I) hγI_mem
  -- F_inv(-γI) = -F_inv(γI) (oddness)
  have h2 := hF_odd (↑γ * Complex.I) hγI_mem
  -- F_inv(conj(γI)) = F_inv(-γI) = -F_inv(γI)
  -- Also F_inv(conj(γI)) = conj(F_inv(γI))
  -- So conj(F_inv(γI)) = -F_inv(γI)
  have h3 : starRingEnd ℂ (F_inv (↑γ * Complex.I)) = -(F_inv (↑γ * Complex.I)) := by
    rw [← h1, hconj_γI, h2]
  -- conj(w) = -w implies Re(w) = 0
  have hre : (F_inv (↑γ * Complex.I)).re = -(F_inv (↑γ * Complex.I)).re := by
    have := congr_arg Complex.re h3
    simp only [Complex.conj_re, Complex.neg_re] at this
    exact this
  linarith

/-! ### The contradiction argument -/

/-- The summability radius γ satisfies γ > log(1+√2).
    Proof structure (paper eqs. 80-85):
    By contradiction, assume γ ≤ L₀. Then F_p(F_inv(γI)) = γI and F_inv(γI) ∈ S.
    Since F_inv(γI) is close to I (from hβ), the Lipschitz bound on F_p gives
    γ ≥ (1-p)L₀ + ph - L‖β‖ > L₀, contradiction.

    The heavy lifting (proving ‖F_inv(γI) - I‖ is small) is done at the call site
    using the sign-structure argument. This theorem just does the Lipschitz step. -/
private theorem summability_radius_gt_log
    (η : ℝ) (hη : 0 < η)
    (hη_bound : (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (F_inv : ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F_inv (disk r))
    (hFi : ∀ z ∈ disk r, F_p η p (F_inv z) = z)
    (hFS : ∀ z ∈ disk r, F_inv z ∈ S)
    (γ : ℝ) (hγ_pos : 0 < γ) (hγ_lt_r : γ < r)
    (hγ_sum : summability_condition (taylor_coeff F_inv) γ)
    -- Lipschitz of F_p on a ball around I
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ w, w ∈ S → ‖w - Complex.I‖ ≤ 1 / 2 →
        ‖F_p η p w - F_p η p Complex.I‖ ≤ L * ‖w - Complex.I‖)
    -- F_inv(γI) is close to I (the sign-structure bound)
    (hβ : ‖F_inv (↑γ * Complex.I) - Complex.I‖ <
        p * ((H_eta η Complex.I / Complex.I).re - Real.log (1 + Real.sqrt 2)) / (2 * L))
    (hβ_near : ‖F_inv (↑γ * Complex.I) - Complex.I‖ ≤ 1 / 2) :
    γ > Real.log (1 + Real.sqrt 2) := by
  by_contra hle
  push_neg at hle
  set L0 := Real.log (1 + Real.sqrt 2)
  set h := (H_eta η Complex.I / Complex.I).re
  set gap := h - L0
  have hgap : 0 < gap := by linarith
  -- w := F_inv(γI)
  set w := F_inv (↑γ * Complex.I)
  have hγI_mem : ↑γ * Complex.I ∈ disk r := by
    rw [mem_disk_iff, norm_mul, Complex.norm_real, Complex.norm_I,
        mul_one, Real.norm_eq_abs, abs_of_pos hγ_pos]; exact hγ_lt_r
  have hw_S : w ∈ S := hFS _ hγI_mem
  have hFp_eq : F_p η p w = ↑γ * Complex.I := hFi _ hγI_mem
  -- Key: (F_p(w)/I).re = γ
  have hγI_div : (↑γ * Complex.I / Complex.I).re = γ := by
    rw [mul_div_cancel_right₀ _ Complex.I_ne_zero, Complex.ofReal_re]
  -- (F_p(I)/I).re = (1-p)*L0 + p*h
  have hFpI_re : (F_p η p Complex.I / Complex.I).re = (1 - p) * L0 + p * h := by
    have hL0 : (H_eta 0 Complex.I / Complex.I).re = L0 := by
      have := H0_I_div_I_re; simp only [H0] at this; exact this
    have hfp : F_p η p Complex.I / Complex.I =
        ↑(1 - p) * (H_eta 0 Complex.I / Complex.I) +
        ↑p * (H_eta η Complex.I / Complex.I) := by
      simp only [F_p, H0]; push_cast; ring
    rw [hfp, Complex.add_re, Complex.mul_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im, hL0]
    simp only [zero_mul, sub_zero]; ring
  -- The Lipschitz bound gives: |γ - ((1-p)L0 + p*h)| ≤ L * ‖w - I‖
  have hFp_diff_re : |γ - ((1 - p) * L0 + p * h)| ≤ L * ‖w - Complex.I‖ := by
    have hdiff_re : |γ - ((1 - p) * L0 + p * h)| =
        |(F_p η p w / Complex.I - F_p η p Complex.I / Complex.I).re| := by
      congr 1; rw [Complex.sub_re]
      rw [show (F_p η p w / Complex.I).re = γ from by rw [hFp_eq, hγI_div]]
      rw [hFpI_re]
    have habs_le := Complex.abs_re_le_norm (F_p η p w / Complex.I - F_p η p Complex.I / Complex.I)
    rw [hdiff_re]
    calc |(F_p η p w / Complex.I - F_p η p Complex.I / Complex.I).re|
        ≤ ‖F_p η p w / Complex.I - F_p η p Complex.I / Complex.I‖ := habs_le
      _ = ‖(F_p η p w - F_p η p Complex.I) / Complex.I‖ := by
          congr 1; ring
      _ = ‖F_p η p w - F_p η p Complex.I‖ / ‖Complex.I‖ := norm_div _ _
      _ = ‖F_p η p w - F_p η p Complex.I‖ := by
          rw [Complex.norm_I, div_one]
      _ ≤ L * ‖w - Complex.I‖ := hLip w hw_S hβ_near
  -- Since γ ≤ L0: γ - ((1-p)L0 + p*h) = γ - L0 - p*gap ≤ -p*gap < 0
  have h_neg : γ - ((1 - p) * L0 + p * h) = (γ - L0) - p * gap := by ring
  have h_le_neg : γ - ((1 - p) * L0 + p * h) ≤ -p * gap := by linarith
  have h_abs_ge : p * gap ≤ |γ - ((1 - p) * L0 + p * h)| := by
    have := neg_abs_le (γ - ((1 - p) * L0 + p * h))
    linarith
  -- Chain: p*gap ≤ |...| ≤ L*‖w-I‖ < L*(p*gap/(2L)) = p*gap/2
  have hpg : 0 < p * gap := mul_pos hp hgap
  have hchain : p * gap ≤ L * ‖w - Complex.I‖ := le_trans h_abs_ge hFp_diff_re
  have hLβ : L * ‖w - Complex.I‖ < p * gap / 2 := by
    calc L * ‖w - Complex.I‖
        < L * (p * gap / (2 * L)) := mul_lt_mul_of_pos_left hβ hL
      _ = p * gap / 2 := by field_simp
  linarith

/-- The (2m+1)-th iterated derivative of sin at 0 equals (-1)^m. -/
private lemma sin_iteratedDeriv_odd (m : ℕ) :
    iteratedDeriv (2 * m + 1) Complex.sin 0 = ((-1 : ℂ) ^ m : ℂ) := by
  induction m with
  | zero =>
    simp only [Nat.zero_eq, mul_zero, zero_add, iteratedDeriv_one]
    rw [show deriv Complex.sin = Complex.cos from Complex.deriv_sin]
    exact Complex.cos_zero
  | succ k ih =>
    have h_eq : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [h_eq, iteratedDeriv_succ', Complex.deriv_sin, iteratedDeriv_succ',
      show deriv Complex.cos = fun z => -Complex.sin z from
        funext fun z => Complex.deriv_cos,
      show (fun z => -Complex.sin z) = (-1 : ℂ) • Complex.sin from by ext z; simp,
      iteratedDeriv_const_smul_field, smul_eq_mul, ih]
    push_cast; ring

/-- The norm of the (2m+1)-th Taylor coefficient of sin equals 1/(2m+1)!. -/
private lemma sin_taylor_coeff_norm (m : ℕ) :
    ‖taylor_coeff Complex.sin (2 * m + 1)‖ = 1 / ((2 * m + 1).factorial : ℝ) := by
  unfold taylor_coeff
  rw [sin_iteratedDeriv_odd m]; simp [norm_div, norm_pow, Complex.norm_natCast]

set_option maxHeartbeats 800000 in
/-- For small enough p, summability_fn(F_inv, log(1+√2)) < 1.
    This uses the sign-structure argument: the first-order correction to the
    summability function from the phi perturbation is negative (= -p·gap_η·cosh(L₀)),
    which dominates the O(p²) remainder for small p. -/
theorem summability_fn_at_log_lt_one
    (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hr9 : 9 / 10 < r)
    (hη_bound : (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2))
    (Cr : ℝ) (hCr : 0 < Cr) :
    ∃ p_β > 0, ∀ (p : ℝ), 0 < p → p < p_β →
      ∀ (F_inv : ℂ → ℂ),
        AnalyticOnNhd ℂ F_inv (disk r) →
        (∀ z ∈ disk r, F_inv (-z) = -F_inv z) →
        (∀ z ∈ disk r,
          ‖F_inv z - Complex.sin z -
            ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖ ≤ Cr * p ^ 2) →
        summability_fn F_inv (Real.log (1 + Real.sqrt 2)) < 1 := by
  set L₀ := Real.log (1 + Real.sqrt 2) with hL₀_def
  set gap := (H_eta η Complex.I / Complex.I).re - L₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith
  -- L₀ < 9/10 (from sinh argument)
  have hL₀_lt_9 : L₀ < 9 / 10 := by
    by_contra h; push_neg at h
    have h1 : Real.sinh L₀ = 1 := by
      rw [show L₀ = Real.arsinh 1 from by simp [L₀, Real.arsinh]; norm_num]
      exact Real.sinh_arsinh 1
    linarith [Real.sinh_le_sinh.mpr h, sinh_nine_tenths_gt_one]
  have hL₀_pos : 0 < L₀ := by
    apply Real.log_pos; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
  have hL₀_lt_r : L₀ < r := lt_trans hL₀_lt_9 hr9
  -- ρ between L₀ and r
  set ρ := (r + L₀) / 2 with hρ_def
  have hρ_pos : 0 < ρ := by linarith
  have hL₀_lt_ρ : L₀ < ρ := by linarith
  have hρ_lt_r : ρ < r := by linarith
  -- Key constants
  set cL₀ := Real.cosh L₀ with hcL₀_def
  have hcL₀_pos : 0 < cL₀ := Real.cosh_pos L₀
  -- Geometric series bound
  have hrat_lt_1 : L₀ / ρ < 1 := (div_lt_one hρ_pos).mpr hL₀_lt_ρ
  have hrat_nn : (0 : ℝ) ≤ L₀ / ρ := div_nonneg hL₀_pos.le hρ_pos.le
  set C_geom := ρ / (ρ - L₀) with hC_geom_def
  have hC_geom_pos : 0 < C_geom := div_pos hρ_pos (by linarith)
  -- phi(z) = (z - H_eta(η, sin z)) * cos z
  set phi_fn : ℂ → ℂ := fun z => (z - H_eta η (Complex.sin z)) * Complex.cos z with hphi_def
  -- phi is analytic on disk(r) (sin maps disk(r) into S, H_eta analytic on S)
  have h_phi_an : AnalyticOnNhd ℂ phi_fn (disk r) := by
    intro z hz
    have hz_lt := (mem_disk_iff z r).1 hz
    have hsinS : Complex.sin z ∈ S :=
      norm_sin_lt_one_of_norm_lt_one z (lt_trans hz_lt hr1)
    exact ((analyticAt_id.sub
      ((H_eta_analyticOnNhd η _ hsinS).comp_of_eq
        (Complex.differentiable_sin.analyticAt _) rfl)).mul
      (Complex.differentiable_cos.analyticAt _))
  -- The summability function of phi at L₀ converges
  have h_phi_summable := summable_weights_of_lt_radius phi_fn r L₀ hr0 hL₀_pos.le hL₀_lt_r h_phi_an
  -- Tail of phi summability series → 0 (from tendsto_sum_nat_add)
  have h_tail_bound : ∀ ε > 0, ∃ N : ℕ,
      ∑' k, ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N) < ε := by
    intro ε hε
    have htend := tendsto_sum_nat_add (fun k => ‖taylor_coeff phi_fn k‖ * L₀ ^ k)
    rw [show (0 : ℝ) = 0 from rfl] at htend
    obtain ⟨N, hN⟩ := ((tendsto_order.1 htend).2 ε hε).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨N, hN_tail⟩ := h_tail_bound (gap * cL₀ / 4) (by positivity)
  -- Compute sin(L₀ * I) = I
  have h_sinL₀I : Complex.sin (↑L₀ * Complex.I) = Complex.I := by
    rw [Complex.sin_mul_I]
    have h_sinh : Complex.sinh (↑L₀ : ℂ) = 1 := by
      rw [← Complex.ofReal_sinh]
      have : Real.sinh L₀ = 1 := by
        rw [show L₀ = Real.arsinh 1 from by simp [L₀, Real.arsinh]; norm_num]
        exact Real.sinh_arsinh 1
      simp [this]
    rw [h_sinh, one_mul]
  -- Compute cos(L₀ * I) = ↑cL₀
  have h_cosL₀I : Complex.cos (↑L₀ * Complex.I) = ↑cL₀ := by
    rw [Complex.cos_mul_I]
    simp [cL₀, Complex.ofReal_cosh]
  -- H_eta(η, I) is purely imaginary
  have h_HetaI_im : (H_eta η Complex.I).re = 0 := by
    -- conj(I) = -I, so H_eta(conj I) = H_eta(-I) = -H_eta(I) (oddness)
    -- Also H_eta(conj I) = conj(H_eta(I)) (conjugation symmetry)
    -- So conj(H_eta(I)) = -H_eta(I), meaning Re(H_eta(I)) = 0
    have h1 := H_eta_conj η Complex.I -- H_eta(conj I) = conj(H_eta I)
    have h2 := H_eta_odd η Complex.I I_mem_S -- H_eta(-I) = -H_eta I
    rw [Complex.conj_I] at h1 -- H_eta(-I) = conj(H_eta I)
    rw [h2] at h1 -- -H_eta I = conj(H_eta I)
    have h3 : (starRingEnd ℂ) (H_eta η Complex.I) = -(H_eta η Complex.I) := h1.symm
    have := congr_arg Complex.re h3
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  -- Compute phi(η, L₀I) = -I * gap * cL₀
  have h_phiL₀I : phi_fn (↑L₀ * Complex.I) = -(↑gap * ↑cL₀) * Complex.I := by
    simp only [phi_fn, h_sinL₀I, h_cosL₀I]
    -- Need: H_eta η I = ↑(gap + L₀) * I
    have him : (H_eta η Complex.I).im = gap + L₀ := by
      -- (w/I).re = w.im when w.re = 0
      have hre : (H_eta η Complex.I / Complex.I).re = gap + L₀ := by simp [gap]
      rw [Complex.div_re, Complex.I_re, Complex.I_im, Complex.normSq_I] at hre
      simp [h_HetaI_im] at hre
      linarith
    have h_HetaI : H_eta η Complex.I = ↑(gap + L₀) * Complex.I := by
      apply Complex.ext
      · simp [h_HetaI_im, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      · simp [him, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
    rw [h_HetaI]; push_cast; ring
  -- Sign-preservation constant: C_sign ≥ ‖c_{2m+1}‖ * (2m+1)! for each m ≤ N
  set C_sign := ∑ m ∈ Finset.range (N + 1),
      ‖taylor_coeff phi_fn (2 * m + 1)‖ * ↑((2 * m + 1).factorial) with hC_sign_def
  have hC_sign_nn : 0 ≤ C_sign := Finset.sum_nonneg (fun m _ => by positivity)
  -- p_β includes O(p²) threshold AND sign-preservation threshold
  set p_β_val := min 1 (min (gap * cL₀ / (4 * (Cr * C_geom + 1))) (1 / (C_sign + 1))) with hp_β_val
  refine ⟨p_β_val, by positivity, ?_⟩
  intro p hp_pos hp_lt_pβ F_inv hFa hF_odd hApprox
  -- Extract p thresholds
  have hp_lt1 : p < 1 := lt_of_lt_of_le hp_lt_pβ (min_le_left _ _)
  have hp_lt_geom : p < gap * cL₀ / (4 * (Cr * C_geom + 1)) :=
    lt_of_lt_of_le hp_lt_pβ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp_lt_sign : p < 1 / (C_sign + 1) :=
    lt_of_lt_of_le hp_lt_pβ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- Abbreviate h = sin + p*phi to keep expressions small for the elaborator
  set h_fn : ℂ → ℂ := fun z => Complex.sin z + ↑p * phi_fn z with hh_fn_def
  -- Cauchy coefficient bound on closedBall(0, ρ)
  have h_approx_cb : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ,
      ‖F_inv z - h_fn z‖ ≤ Cr * p ^ 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have := hApprox z ((mem_disk_iff z r).2 (lt_of_le_of_lt hz hρ_lt_r))
    rwa [show F_inv z - Complex.sin z - ↑p * phi_fn z =
      F_inv z - h_fn z from by simp [h_fn]; ring] at this
  -- h is analytic on disk(r)
  have h_h_an : AnalyticOnNhd ℂ h_fn (disk r) :=
    fun z hz => (Complex.differentiable_sin.analyticAt z).add
      ((analyticAt_const (v := (↑p : ℂ))).mul (h_phi_an z hz))
  -- Taylor coefficient bound: ‖a_k - h_k‖ ≤ Cr*p²/ρ^k
  have hcoeff : ∀ k, ‖taylor_coeff F_inv k - taylor_coeff h_fn k‖
      ≤ Cr * p ^ 2 / ρ ^ k :=
    fun k => taylor_coeff_sub_bound hρ_pos hρ_lt_r hFa h_h_an h_approx_cb k
  -- ASSEMBLY: summability_fn(F_inv, L₀) < 1
  -- Step A: summability_fn(F_inv, L₀) ≤ summability_fn(h, L₀) + Cr*p²*C_geom
  have stepA : summability_fn F_inv L₀ ≤
      summability_fn h_fn L₀ + Cr * p ^ 2 * C_geom := by
    -- Summabilities
    have hsumF := summable_weights_of_lt_radius F_inv r L₀ hr0 hL₀_pos.le hL₀_lt_r hFa
    have hsumH := summable_weights_of_lt_radius h_fn r L₀ hr0 hL₀_pos.le hL₀_lt_r h_h_an
    have hsumG : Summable fun k => Cr * p ^ 2 * (L₀ / ρ) ^ k :=
      (summable_geometric_of_lt_one hrat_nn hrat_lt_1).mul_left _
    -- Pointwise bound: ‖a_k‖ * L₀^k ≤ ‖h_k‖ * L₀^k + Cr*p²*(L₀/ρ)^k
    have hpt : ∀ k, ‖taylor_coeff F_inv k‖ * L₀ ^ k ≤
        ‖taylor_coeff h_fn k‖ * L₀ ^ k + Cr * p ^ 2 * (L₀ / ρ) ^ k := by
      intro k
      have h_nsn := norm_sub_norm_le (taylor_coeff F_inv k) (taylor_coeff h_fn k)
      have h_cb := hcoeff k
      have h1 : ‖taylor_coeff F_inv k‖ - ‖taylor_coeff h_fn k‖ ≤ Cr * p ^ 2 / ρ ^ k :=
        le_trans h_nsn h_cb
      have hL₀k : 0 ≤ L₀ ^ k := pow_nonneg hL₀_pos.le k
      have h_eq : Cr * p ^ 2 / ρ ^ k * L₀ ^ k = Cr * p ^ 2 * (L₀ / ρ) ^ k := by
        rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow]
      have h3 := mul_le_mul_of_nonneg_right h1 hL₀k
      rw [sub_mul] at h3; rw [h_eq] at h3; linarith
    -- Geometric series = C_geom
    have hgeom : ∑' k, Cr * p ^ 2 * (L₀ / ρ) ^ k = Cr * p ^ 2 * C_geom := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hrat_nn hrat_lt_1,
          one_sub_div hρ_pos.ne', inv_div]
    -- Combine using tsum comparison
    show summability_fn F_inv L₀ ≤ summability_fn h_fn L₀ + Cr * p ^ 2 * C_geom
    simp only [summability_fn]
    calc ∑' k, ‖taylor_coeff F_inv k‖ * L₀ ^ k
        ≤ ∑' k, (‖taylor_coeff h_fn k‖ * L₀ ^ k +
          Cr * p ^ 2 * (L₀ / ρ) ^ k) :=
          Summable.tsum_le_tsum hpt hsumF (hsumH.add hsumG)
      _ = (∑' k, ‖taylor_coeff h_fn k‖ * L₀ ^ k) +
          ∑' k, Cr * p ^ 2 * (L₀ / ρ) ^ k := hsumH.tsum_add hsumG
      _ = _ := by rw [hgeom]
  -- Step B: summability_fn(h, L₀) ≤ 1 - p*gap*cL₀/2 (sign-structure core)
  -- Uses: sign preservation for m ≤ N, phi tail bound, phi(L₀I) value
  have stepB : summability_fn h_fn L₀ ≤ 1 - p * gap * cL₀ / 2 := by
    -- SIGN-STRUCTURE ARGUMENT
    -- Key: summability_fn(h, L₀) ≤ (1 - p·gap·cL₀) + 2p·phi_tail(N) < 1 - p·gap·cL₀/2
    -- Step B.1: h_fn(L₀I) = (1 - p·gap·cL₀)·I
    have h_eval : h_fn (↑L₀ * I) = ↑(1 - p * gap * cL₀) * I := by
      simp only [h_fn]; rw [h_sinL₀I, h_phiL₀I]; push_cast; ring
    -- Step B.2: L₀I ∈ disk(r)
    have hL₀I_mem : ↑L₀ * I ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖↑L₀ * I‖ = ‖(↑L₀ : ℂ)‖ * ‖I‖ := norm_mul _ _
        _ = L₀ * 1 := by rw [Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hL₀_pos.le]
        _ = L₀ := mul_one _
        _ < r := hL₀_lt_r
    -- Step B.3: Power series ∑ taylor_coeff(h_fn, n) * (L₀I)^n = h_fn(L₀I)
    have h_series : ∑' n, taylor_coeff h_fn n * (↑L₀ * I) ^ n = h_fn (↑L₀ * I) := by
      have h1 := Complex.taylorSeries_eq_on_ball
        (h_h_an.differentiableOn : DifferentiableOn ℂ h_fn (Metric.ball 0 r)) hL₀I_mem
      simp only [sub_zero] at h1
      rw [← h1]; congr 1; ext n
      simp only [taylor_coeff, smul_eq_mul, div_eq_mul_inv]
      ac_rfl
    -- Step B.4: The signed sum value
    -- ∑ taylor_coeff(h_fn, n) * (L₀I)^n = (1 - p·gap·cL₀) * I
    have h_signed : ∑' n, taylor_coeff h_fn n * (↑L₀ * I) ^ n = ↑(1 - p * gap * cL₀) * I :=
      h_series.trans h_eval
    -- Step B.5: Taylor coefficients of h_fn are real (from conjugation symmetry)
    -- h_fn(conj z) = conj(h_fn z) since sin, phi_fn both preserve conjugation
    have h_real_coeff : ∀ k, (taylor_coeff h_fn k).im = 0 := by
      -- h_fn preserves conjugation on disk r
      have h_conj : ∀ z ∈ disk r, h_fn (starRingEnd ℂ z) = starRingEnd ℂ (h_fn z) := by
        intro z hz
        simp only [h_fn, phi_fn]
        rw [Complex.sin_conj, Complex.cos_conj, H_eta_conj η (Complex.sin z)]
        simp [map_add, map_mul, map_sub, Complex.conj_ofReal]
      -- By induction: iteratedDeriv k h_fn preserves conjugation on disk(r)
      have h_iter_conj : ∀ k, ∀ z ∈ disk r,
          (iteratedDeriv k h_fn) (starRingEnd ℂ z) =
          starRingEnd ℂ ((iteratedDeriv k h_fn) z) := by
        intro k; induction k with
        | zero => simp [iteratedDeriv_zero]; exact h_conj
        | succ n ih =>
          intro z hz
          have hf_diff : DifferentiableAt ℂ (iteratedDeriv n h_fn) z := by
            rw [iteratedDeriv_eq_iterate]; exact ((h_h_an z hz).iterated_deriv n).differentiableAt
          have hcz : starRingEnd ℂ z ∈ disk r := by
            rw [mem_disk_iff] at hz ⊢; rwa [Complex.norm_conj]
          have h_da := hf_diff.hasDerivAt.conj_conj
          have h_eq_f : ∀ w ∈ disk r, (starRingEnd ℂ ∘ iteratedDeriv n h_fn ∘ starRingEnd ℂ) w =
              iteratedDeriv n h_fn w := by
            intro w hw; simp only [Function.comp]
            rw [ih w hw, starRingEnd_self_apply]
          have h_ev : (starRingEnd ℂ ∘ iteratedDeriv n h_fn ∘ starRingEnd ℂ) =ᶠ[nhds (starRingEnd ℂ z)]
              (iteratedDeriv n h_fn) := by
            rw [Filter.eventuallyEq_iff_exists_mem]
            exact ⟨disk r, (disk_isOpen r).mem_nhds hcz, h_eq_f⟩
          rw [iteratedDeriv_succ]
          have h1 : deriv (starRingEnd ℂ ∘ iteratedDeriv n h_fn ∘ starRingEnd ℂ)
              (starRingEnd ℂ z) = starRingEnd ℂ (deriv (iteratedDeriv n h_fn) z) :=
            h_da.deriv
          have h2 : deriv (starRingEnd ℂ ∘ iteratedDeriv n h_fn ∘ starRingEnd ℂ)
              (starRingEnd ℂ z) = deriv (iteratedDeriv n h_fn) (starRingEnd ℂ z) :=
            h_ev.deriv_eq
          rw [← h2, h1]
      -- At z = 0: conj(iteratedDeriv k h_fn 0) = iteratedDeriv k h_fn 0
      have h_conj_eq : ∀ k, starRingEnd ℂ (iteratedDeriv k h_fn 0) = iteratedDeriv k h_fn 0 := by
        intro k
        have h0 : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
        have := h_iter_conj k 0 h0
        rw [map_zero] at this; exact this.symm
      -- Therefore (taylor_coeff h_fn k).im = 0
      intro k; unfold taylor_coeff
      have him : (iteratedDeriv k h_fn 0).im = 0 := Complex.conj_eq_iff_im.mp (h_conj_eq k)
      apply Complex.conj_eq_iff_im.mp
      rw [map_div₀, h_conj_eq k, map_natCast]
    -- Step B.6: h_fn is odd → even Taylor coefficients vanish
    have h_h_odd : ∀ z ∈ disk r, h_fn (-z) = -h_fn z := by
      intro z hz; simp only [h_fn]
      rw [Complex.sin_neg]
      have hz' := (mem_disk_iff z r).1 hz
      have : phi_fn (-z) = -phi_fn z := by
        simp only [phi_fn, Complex.sin_neg, Complex.cos_neg]
        have hsin_S : Complex.sin z ∈ S :=
          norm_sin_lt_one_of_norm_lt_one z (lt_trans hz' hr1)
        rw [H_eta_odd η (Complex.sin z) hsin_S]; ring
      rw [this]; ring
    have h_even_zero : ∀ k, taylor_coeff h_fn (2 * k) = 0 := by
      have h0_mem : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
      have hFeq : (fun z => h_fn (-z)) =ᶠ[nhds 0] (fun z => -h_fn z) :=
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨disk r, (disk_isOpen r).mem_nhds h0_mem, fun z hz => h_h_odd z hz⟩
      intro k; unfold taylor_coeff
      have hdeq := hFeq.iteratedDeriv_eq (2 * k)
      have h1 := iteratedDeriv_comp_neg (2 * k) h_fn 0
      have h2 := iteratedDeriv_fun_neg (2 * k) h_fn 0
      rw [neg_zero, Even.neg_one_pow (even_two_mul k), one_smul] at h1
      rw [h1] at hdeq; rw [h2] at hdeq
      rw [CharZero.eq_neg_self_iff.mp hdeq, zero_div]
    -- Step B.7: For odd n=2m+1, σ_n = b_n * (L₀I)^n is purely imaginary
    -- since b_n is real and (L₀I)^{2m+1} = (-1)^m * L₀^{2m+1} * I
    -- Step B.8: The signed sum ∑ Im(σ_n) = 1 - p*gap*cL₀
    -- From h_signed: ∑ σ_n = (1-p*gap*cL₀)*I, and each σ_n is imaginary
    -- Step B.9: Core bound via sign structure
    -- summability_fn h_fn L₀ ≤ (1 - p*gap*cL₀) + 2p * phi_tail(N) < 1 - p*gap*cL₀/2
    -- The first inequality uses:
    --   ∑ ‖b_n‖ L₀^n = ∑ Im(σ_n) + ∑ excess(n)
    --   where σ_n = b_n * (L₀I)^n, excess(n) = ‖σ_n‖ - Im(σ_n)
    --   ∑ Im(σ_n) = 1 - p*gap*cL₀ (from h_signed)
    --   For m ≤ N: excess = 0 (sign preserved)
    --   For m > N: excess ≤ 2p‖c_n‖ L₀^n
    --   Total excess ≤ 2p * phi_tail(N)
    -- Sin zero excess: ‖sin_n * (L₀I)^n‖ - Im(sin_n * (L₀I)^n) = 0 for all n
    have h_sin_excess : ∀ n, ‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖ -
        (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im = 0 := by
      have hL₀I_norm' : ‖(↑L₀ : ℂ) * I‖ = L₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL₀_pos.le, Complex.norm_I, mul_one]
      have h_sin_an_ball : AnalyticOnNhd ℂ Complex.sin (Metric.ball 0 (L₀ + 1)) :=
        fun w _ => Complex.differentiable_sin.analyticAt w
      have h_sin_ws := summable_weights_of_lt_radius Complex.sin (L₀ + 1) L₀
        (by linarith) hL₀_pos.le (by linarith) h_sin_an_ball
      have hσs_norm_eq : ∀ n, ‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖ =
          ‖taylor_coeff Complex.sin n‖ * L₀ ^ n := fun n => by
        rw [norm_mul, norm_pow, hL₀I_norm']
      have hσs_summable : Summable (fun n => taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n) :=
        Summable.of_norm (h_sin_ws.congr (fun n => (hσs_norm_eq n).symm))
      have h_sin_norm_sum : ∑' n, ‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖ = 1 := by
        rw [show (fun n => ‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖) =
            fun n => ‖taylor_coeff Complex.sin n‖ * L₀ ^ n from funext hσs_norm_eq]
        exact sin_summability_at_log
      have h_sin_sum_I : ∑' n, taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n = I := by
        have hzm : (↑L₀ : ℂ) * I ∈ Metric.ball (0 : ℂ) (L₀ + 1) := by
          rw [Metric.mem_ball, dist_zero_right, hL₀I_norm']; linarith
        have h1 := Complex.taylorSeries_eq_on_ball h_sin_an_ball.differentiableOn hzm
        simp only [sub_zero] at h1
        have h2 : ∑' n, taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n = Complex.sin ((↑L₀ : ℂ) * I) := by
          rw [← h1]; congr 1; ext n; simp only [taylor_coeff, smul_eq_mul, div_eq_mul_inv]; ac_rfl
        rw [h2, h_sinL₀I]
      have h_sin_im_summable : Summable (fun n => (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im) :=
        hσs_summable.map Complex.imCLM Complex.imCLM.continuous
      have h_sin_im_sum : ∑' n, (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im = 1 := by
        rw [← Complex.im_tsum hσs_summable, h_sin_sum_I]; simp
      have h_sin_excess_nn : ∀ n, 0 ≤ ‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖ -
          (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im := by
        intro n
        have := Complex.abs_im_le_norm (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n)
        linarith [le_abs_self (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im]
      have h_sin_excess_summable := hσs_summable.norm.sub h_sin_im_summable
      have h_sin_excess_zero : ∑' n, (‖taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n‖ -
          (taylor_coeff Complex.sin n * ((↑L₀ : ℂ) * I) ^ n).im) = 0 := by
        rw [hσs_summable.norm.tsum_sub h_sin_im_summable, h_sin_norm_sum, h_sin_im_sum, sub_self]
      intro n
      have h1 := h_sin_excess_summable.le_tsum n (fun j _ => h_sin_excess_nn j)
      linarith [h_sin_excess_nn n]
    have h_key : summability_fn h_fn L₀ ≤ (1 - p * gap * cL₀) +
        2 * p * (∑' k, ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N)) := by
      -- Proof: summability_fn(h, L₀) ≤ (1 - p*gap*cL₀) + 2p * phi_tail(N)
      --
      -- Key identity: summability_fn h L₀ = ∑ Im(b_n*(L₀I)^n) + ∑(‖b_n*(L₀I)^n‖ - Im(b_n*(L₀I)^n))
      -- where the first sum = 1 - p*gap*cL₀ and the second (excess) ≤ 2p * phi_tail
      --
      -- Step 1: σ_n = b_n*(L₀I)^n is summable
      have hσ_summable : Summable (fun n => taylor_coeff h_fn n * (↑L₀ * I) ^ n) :=
        Summable.of_norm ((summable_weights_of_lt_radius h_fn r L₀ hr0 hL₀_pos.le hL₀_lt_r h_h_an).congr fun n => by rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL₀_pos.le, Complex.norm_I, mul_one])
      -- Step 2: Im commutes with tsum: ∑ Im(σ_n) = 1 - p*gap*cL₀
      have h_im_summable : Summable (fun n => (taylor_coeff h_fn n * (↑L₀ * I) ^ n).im) :=
        hσ_summable.map Complex.imCLM Complex.imCLM.continuous
      have h_im_sum : ∑' n, (taylor_coeff h_fn n * (↑L₀ * I) ^ n).im = 1 - p * gap * cL₀ := by
        rw [← Complex.im_tsum hσ_summable, h_signed]
        simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      -- Step 3: ‖σ_n‖ = ‖b_n‖ * L₀^n
      have hL₀I_norm : ‖(↑L₀ : ℂ) * I‖ = L₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL₀_pos.le, Complex.norm_I, mul_one]
      have h_norm_eq : ∀ n, ‖taylor_coeff h_fn n‖ * L₀ ^ n =
          ‖taylor_coeff h_fn n * (↑L₀ * I) ^ n‖ := by
        intro n; rw [norm_mul, norm_pow, hL₀I_norm]
      -- Step 4: For each n, excess = ‖σ_n‖ - Im(σ_n) ≤ 2p * ‖c_n‖ * L₀^n
      -- (Uses: b_n real, sign analysis)
      have h_excess : ∀ n, ‖taylor_coeff h_fn n * (↑L₀ * I) ^ n‖ -
          (taylor_coeff h_fn n * (↑L₀ * I) ^ n).im ≤
          2 * p * (‖taylor_coeff phi_fn n‖ * L₀ ^ n) := by
        -- Step A: sin has zero excess at each term
        -- Proof: summability_fn sin L₀ = 1, ∑ Im(sin_n*(L₀I)^n) = 1,
        -- each excess ≥ 0, sum = 0 ⟹ each = 0
        set z := (↑L₀ : ℂ) * I with hz_def
        have h_sin_an_ball : AnalyticOnNhd ℂ Complex.sin (Metric.ball 0 (L₀ + 1)) :=
          fun w _ => Complex.differentiable_sin.analyticAt w
        have h_sin_ws := summable_weights_of_lt_radius Complex.sin (L₀ + 1) L₀
          (by linarith) hL₀_pos.le (by linarith) h_sin_an_ball
        have hσs_norm_eq : ∀ n, ‖taylor_coeff Complex.sin n * z ^ n‖ =
            ‖taylor_coeff Complex.sin n‖ * L₀ ^ n := by
          intro n; rw [norm_mul, norm_pow, hL₀I_norm]
        have hσs_summable : Summable (fun n => taylor_coeff Complex.sin n * z ^ n) :=
          Summable.of_norm (h_sin_ws.congr (fun n => (hσs_norm_eq n).symm))
        -- ∑ ‖sin_n * z^n‖ = 1
        have h_sin_norm_sum : ∑' n, ‖taylor_coeff Complex.sin n * z ^ n‖ = 1 := by
          rw [show (fun n => ‖taylor_coeff Complex.sin n * z ^ n‖) =
              fun n => ‖taylor_coeff Complex.sin n‖ * L₀ ^ n from funext hσs_norm_eq]
          exact sin_summability_at_log
        -- ∑ sin_n * z^n = sin(z) = I
        have h_sin_sum_I : ∑' n, taylor_coeff Complex.sin n * z ^ n = I := by
          have hzm : z ∈ Metric.ball (0 : ℂ) (L₀ + 1) := by
            rw [Metric.mem_ball, dist_zero_right, hL₀I_norm]; linarith
          have h1 := Complex.taylorSeries_eq_on_ball
            (h_sin_an_ball.differentiableOn) hzm
          simp only [sub_zero] at h1
          have h2 : ∑' n, taylor_coeff Complex.sin n * z ^ n = Complex.sin z := by
            rw [← h1]; congr 1; ext n
            simp only [taylor_coeff, smul_eq_mul, div_eq_mul_inv]; ac_rfl
          rw [h2, hz_def, h_sinL₀I]
        -- ∑ Im(sin_n * z^n) = 1
        have h_sin_im_summable : Summable (fun n => (taylor_coeff Complex.sin n * z ^ n).im) :=
          hσs_summable.map Complex.imCLM Complex.imCLM.continuous
        have h_sin_im_sum : ∑' n, (taylor_coeff Complex.sin n * z ^ n).im = 1 := by
          rw [← Complex.im_tsum hσs_summable, h_sin_sum_I]; simp
        -- Each sin excess ≥ 0
        have h_sin_excess_nn : ∀ n, 0 ≤ ‖taylor_coeff Complex.sin n * z ^ n‖ -
            (taylor_coeff Complex.sin n * z ^ n).im := by
          intro n
          linarith [le_trans (le_abs_self (taylor_coeff Complex.sin n * z ^ n).im)
            (Complex.abs_im_le_norm (taylor_coeff Complex.sin n * z ^ n))]
        -- Sum of sin excesses = 0
        have h_sin_excess_summable : Summable (fun n => ‖taylor_coeff Complex.sin n * z ^ n‖ -
            (taylor_coeff Complex.sin n * z ^ n).im) :=
          hσs_summable.norm.sub h_sin_im_summable
        have h_sin_excess_zero : ∑' n, (‖taylor_coeff Complex.sin n * z ^ n‖ -
            (taylor_coeff Complex.sin n * z ^ n).im) = 0 := by
          rw [hσs_summable.norm.tsum_sub h_sin_im_summable, h_sin_norm_sum, h_sin_im_sum, sub_self]
        -- Each sin excess = 0
        have h_sin_excess : ∀ n, ‖taylor_coeff Complex.sin n * z ^ n‖ -
            (taylor_coeff Complex.sin n * z ^ n).im = 0 := by
          intro n
          have h1 : ‖taylor_coeff Complex.sin n * z ^ n‖ -
              (taylor_coeff Complex.sin n * z ^ n).im ≤
              ∑' i, (‖taylor_coeff Complex.sin i * z ^ i‖ -
              (taylor_coeff Complex.sin i * z ^ i).im) :=
            h_sin_excess_summable.le_tsum n (fun j _ => h_sin_excess_nn j)
          linarith [h_sin_excess_nn n]
        -- Step B: Decompose taylor_coeff h_fn n
        have h0_mem : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
        have h_decomp : ∀ n, taylor_coeff h_fn n =
            taylor_coeff Complex.sin n + ↑p * taylor_coeff phi_fn n := by
          intro n; unfold taylor_coeff
          have h_sin_an : AnalyticAt ℂ Complex.sin 0 := Complex.differentiable_sin.analyticAt 0
          have h_phi_an0 : AnalyticAt ℂ phi_fn 0 := h_phi_an 0 h0_mem
          have h_pp : AnalyticAt ℂ (fun z => (↑p : ℂ) * phi_fn z) 0 :=
            analyticAt_const.mul h_phi_an0
          have hsum : iteratedDeriv n (fun z => Complex.sin z + ↑p * phi_fn z) 0 =
              iteratedDeriv n Complex.sin 0 +
              iteratedDeriv n (fun z => (↑p : ℂ) * phi_fn z) 0 :=
            iteratedDeriv_add h_sin_an.contDiffAt h_pp.contDiffAt
          have hsmul : iteratedDeriv n (fun z => (↑p : ℂ) * phi_fn z) 0 =
              (↑p : ℂ) * iteratedDeriv n phi_fn 0 := by
            have : (fun z => (↑p : ℂ) * phi_fn z) = (↑p : ℂ) • phi_fn := by
              ext w; simp [Pi.smul_apply, smul_eq_mul]
            rw [this, iteratedDeriv_const_smul_field, smul_eq_mul]
          show iteratedDeriv n h_fn 0 / ↑n.factorial =
            iteratedDeriv n Complex.sin 0 / ↑n.factorial +
            ↑p * (iteratedDeriv n phi_fn 0 / ↑n.factorial)
          rw [show iteratedDeriv n h_fn 0 = iteratedDeriv n
              (fun z => Complex.sin z + ↑p * phi_fn z) 0 from rfl,
              hsum, hsmul]
          ring
        -- Step C: For each n, bound excess using triangle inequality
        intro n
        set a := taylor_coeff Complex.sin n * z ^ n
        set b := (↑p : ℂ) * taylor_coeff phi_fn n * z ^ n
        -- h_n * z^n = a + b
        have hab : taylor_coeff h_fn n * z ^ n = a + b := by
          rw [h_decomp n]; ring
        rw [hab]
        -- ‖a + b‖ - Im(a + b) ≤ 2 * ‖b‖
        have h_tri : ‖a + b‖ - (a + b).im ≤ 2 * ‖b‖ := by
          have ha_im : a.im = ‖a‖ := by linarith [h_sin_excess n]
          have him : (a + b).im = a.im + b.im := by simp [Complex.add_im]
          rw [him, ha_im]
          have h1 : ‖a + b‖ - ‖a‖ ≤ ‖b‖ := by linarith [norm_add_le a b]
          have h2 : -b.im ≤ ‖b‖ := by
            linarith [Complex.abs_im_le_norm b, neg_abs_le b.im]
          linarith
        -- ‖b‖ = p * (‖phi_n‖ * L₀^n)
        have hb_norm : ‖b‖ = p * (‖taylor_coeff phi_fn n‖ * L₀ ^ n) := by
          simp only [b, norm_mul, norm_pow, hL₀I_norm, Complex.norm_real,
            Real.norm_of_nonneg hp_pos.le]
          ring
        linarith
      -- Step 5: Sum the excess using tsum_le_tsum
      have h_norm_summable := hσ_summable.norm
      have h_phi_norm_summable : Summable (fun n => 2 * p * (‖taylor_coeff phi_fn n‖ * L₀ ^ n)) :=
        h_phi_summable.mul_left _
      -- ∑ ‖σ_n‖ ≤ ∑ Im(σ_n) + ∑ 2p * ‖c_n‖ * L₀^n
      have h_sum_bound : ∑' n, ‖taylor_coeff h_fn n‖ * L₀ ^ n ≤
          (1 - p * gap * cL₀) + 2 * p * (∑' n, ‖taylor_coeff phi_fn n‖ * L₀ ^ n) := by
        have h1 : ∀ n, ‖taylor_coeff h_fn n * (↑L₀ * I) ^ n‖ ≤
            (taylor_coeff h_fn n * (↑L₀ * I) ^ n).im +
            2 * p * (‖taylor_coeff phi_fn n‖ * L₀ ^ n) := by
          intro n; linarith [h_excess n]
        have h2 := Summable.tsum_le_tsum h1 h_norm_summable (h_im_summable.add h_phi_norm_summable)
        rw [Summable.tsum_add h_im_summable h_phi_norm_summable, h_im_sum, tsum_mul_left] at h2
        show ∑' n, ‖taylor_coeff h_fn n‖ * L₀ ^ n ≤
          1 - p * gap * cL₀ + 2 * p * ∑' n, ‖taylor_coeff phi_fn n‖ * L₀ ^ n
        convert h2 using 1
        congr 1; ext n; exact h_norm_eq n
      -- Step 6: sign preservation for n < N gives tail bound
      -- Define excess function
      set z := (↑L₀ : ℂ) * I with hz_def
      set excess := fun n => ‖taylor_coeff h_fn n * z ^ n‖ -
          (taylor_coeff h_fn n * z ^ n).im with hexcess_def
      -- Excess is nonneg
      have h_excess_nn : ∀ n, 0 ≤ excess n := fun n => by
        simp only [hexcess_def]
        linarith [Complex.abs_im_le_norm (taylor_coeff h_fn n * z ^ n),
                  le_abs_self (taylor_coeff h_fn n * z ^ n).im]
      -- Excess is summable
      have h_excess_summable : Summable excess := by
        show Summable (fun n => ‖taylor_coeff h_fn n * z ^ n‖ -
            (taylor_coeff h_fn n * z ^ n).im)
        exact h_norm_summable.sub h_im_summable
      -- summability_fn = im_sum + excess_sum
      have h_sf_decomp : summability_fn h_fn L₀ =
          (1 - p * gap * cL₀) + ∑' n, excess n := by
        have h1 : summability_fn h_fn L₀ = ∑' n, ‖taylor_coeff h_fn n * z ^ n‖ := by
          show ∑' n, ‖taylor_coeff h_fn n‖ * L₀ ^ n = _
          congr 1; ext n; exact h_norm_eq n
        have h2 : (fun n => ‖taylor_coeff h_fn n * z ^ n‖) =
            fun n => (taylor_coeff h_fn n * z ^ n).im + excess n := by
          ext n; simp only [hexcess_def]; ring
        rw [h1, h2, h_im_summable.tsum_add h_excess_summable, h_im_sum]
      -- Re-derive h_decomp (needed for sign preservation)
      have h0_mem : (0 : ℂ) ∈ disk r := zero_mem_disk r hr0
      have h_decomp : ∀ n, taylor_coeff h_fn n =
          taylor_coeff Complex.sin n + ↑p * taylor_coeff phi_fn n := by
        intro n; unfold taylor_coeff
        have h_sin_an : AnalyticAt ℂ Complex.sin 0 := Complex.differentiable_sin.analyticAt 0
        have h_phi_an0 : AnalyticAt ℂ phi_fn 0 := h_phi_an 0 h0_mem
        have h_pp : AnalyticAt ℂ (fun z => (↑p : ℂ) * phi_fn z) 0 :=
          analyticAt_const.mul h_phi_an0
        have hsum : iteratedDeriv n (fun z => Complex.sin z + ↑p * phi_fn z) 0 =
            iteratedDeriv n Complex.sin 0 +
            iteratedDeriv n (fun z => (↑p : ℂ) * phi_fn z) 0 :=
          iteratedDeriv_add h_sin_an.contDiffAt h_pp.contDiffAt
        have hsmul : iteratedDeriv n (fun z => (↑p : ℂ) * phi_fn z) 0 =
            (↑p : ℂ) * iteratedDeriv n phi_fn 0 := by
          have : (fun z => (↑p : ℂ) * phi_fn z) = (↑p : ℂ) • phi_fn := by
            ext w; simp [Pi.smul_apply, smul_eq_mul]
          rw [this, iteratedDeriv_const_smul_field, smul_eq_mul]
        show iteratedDeriv n h_fn 0 / ↑n.factorial =
          iteratedDeriv n Complex.sin 0 / ↑n.factorial +
          ↑p * (iteratedDeriv n phi_fn 0 / ↑n.factorial)
        rw [show iteratedDeriv n h_fn 0 = iteratedDeriv n
            (fun z => Complex.sin z + ↑p * phi_fn z) 0 from rfl,
            hsum, hsmul]
        ring
      -- Key: (L₀*I)^(2m+1) = (-1)^m * L₀^(2m+1) * I
      have hzpow_odd : ∀ m : ℕ, z ^ (2 * m + 1) =
          ((-1 : ℂ) ^ m * ↑(L₀ ^ (2 * m + 1))) * I := by
        intro m; induction m with
        | zero => simp [hz_def]
        | succ k ih =>
          rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega,
              pow_add, ih]
          have : z ^ 2 = -(↑(L₀ ^ 2)) := by
            rw [hz_def, mul_pow, ofReal_pow]; simp [I_sq]
          rw [this]; push_cast; ring
      -- For odd n = 2m+1 with m ≤ N: excess = 0 (sign preservation)
      have h_sign_pres : ∀ m : ℕ, m ≤ N →
          excess (2 * m + 1) = 0 := by
        intro m hm
        set n := 2 * m + 1 with hn_def
        set b := taylor_coeff h_fn n with hb_def
        set s := taylor_coeff Complex.sin n with hs_def
        set c := taylor_coeff phi_fn n with hc_def
        -- b = s + p * c
        have hbc : b = s + ↑p * c := h_decomp n
        -- b is real
        have hb_im : b.im = 0 := h_real_coeff n
        -- s = (-1)^m / (2m+1)!  (as complex)
        have hs_val : s = ↑((-1 : ℝ) ^ m / ↑n.factorial) := by
          simp only [hs_def, taylor_coeff, hn_def]
          rw [sin_iteratedDeriv_odd m]
          push_cast; rfl
        -- s.re * (-1)^m = 1/(2m+1)!
        have hs_re_sign : s.re * (-1 : ℝ) ^ m = 1 / ↑n.factorial := by
          rw [hs_val, Complex.ofReal_re, div_mul_eq_mul_div, ← pow_add]
          norm_num
        -- p * ‖c‖ < 1/n!   (from hp_lt_sign)
        have hc_bound : p * ‖c‖ < 1 / ↑n.factorial := by
          have hm_mem : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
          have h1 : ‖c‖ * ↑n.factorial ≤ C_sign := by
            show ‖taylor_coeff phi_fn (2 * m + 1)‖ * ↑(2 * m + 1).factorial ≤ C_sign
            rw [hC_sign_def]
            apply Finset.single_le_sum _ hm_mem
            intro i _
            exact mul_nonneg (norm_nonneg _) (Nat.cast_nonneg' _)
          have h2 : p * (C_sign + 1) < 1 := by
            rwa [lt_div_iff₀ (by positivity : (0:ℝ) < C_sign + 1)] at hp_lt_sign
          have hn_fact_pos : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr n.factorial_pos
          rw [lt_div_iff₀ hn_fact_pos]
          calc p * ‖c‖ * ↑n.factorial
              = p * (‖c‖ * ↑n.factorial) := by ring
            _ ≤ p * C_sign := by nlinarith
            _ < p * (C_sign + 1) := by nlinarith [hp_pos]
            _ < 1 := h2
        -- b.re * (-1)^m > 0
        have hb_re_pos : b.re * (-1 : ℝ) ^ m > 0 := by
          have hbre : b.re = s.re + p * c.re := by
            rw [hbc]; simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          rw [hbre, show (s.re + p * c.re) * (-1 : ℝ) ^ m =
              s.re * (-1 : ℝ) ^ m + p * (c.re * (-1 : ℝ) ^ m) from by ring,
              hs_re_sign]
          have h_abs : |c.re * (-1 : ℝ) ^ m| ≤ ‖c‖ := by
            calc |c.re * (-1 : ℝ) ^ m|
                = |c.re| * |(-1 : ℝ) ^ m| := abs_mul _ _
              _ = |c.re| * 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
              _ = |c.re| := mul_one _
              _ ≤ ‖c‖ := Complex.abs_re_le_norm c
          have h_neg : -(p * ‖c‖) ≤ p * (c.re * (-1 : ℝ) ^ m) := by
            have := neg_abs_le (c.re * (-1 : ℝ) ^ m)
            nlinarith [hp_pos.le]
          linarith
        -- σ_n = ↑(b.re * (-1)^m * L₀^n) * I
        have hσ_form : taylor_coeff h_fn n * z ^ n =
            ↑(b.re * (-1 : ℝ) ^ m * L₀ ^ n) * I := by
          show b * z ^ n = _
          rw [hzpow_odd m, show n = 2 * m + 1 from rfl]
          have hb_eq : b = ↑b.re := Complex.ext (by simp) (by simp [hb_im])
          conv_lhs => rw [hb_eq]
          simp only [ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one]; ring
        -- excess = ‖↑r * I‖ - (↑r * I).im = 0 for r ≥ 0
        simp only [hexcess_def, hσ_form]
        set rv := b.re * (-1 : ℝ) ^ m * L₀ ^ n with hrv_def
        have hr_nn : (0 : ℝ) ≤ rv :=
          mul_nonneg (le_of_lt hb_re_pos) (pow_nonneg hL₀_pos.le _)
        simp [Complex.norm_real, Real.norm_of_nonneg hr_nn, Complex.norm_I,
              Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      -- Even terms have excess 0
      have h_excess_even_zero : ∀ k : ℕ, excess (2 * k) = 0 := by
        intro k; simp only [hexcess_def, h_even_zero k, zero_mul, norm_zero,
          Complex.zero_im, sub_self]
      -- All excess for n < 2*(N+1) is zero
      have h_excess_zero_small : ∀ n, n < 2 * (N + 1) → excess n = 0 := by
        intro n hn
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨m, hm⟩
        · have : n = 2 * k := by omega
          rw [this]; exact h_excess_even_zero k
        · rw [show n = 2 * m + 1 from by omega]; exact h_sign_pres m (by omega)
      -- Tail bound: ∑ excess ≤ 2p * ∑_{n≥N} ‖c_n‖ * L₀^n
      -- First: ∑ excess = ∑_{n≥2(N+1)} excess (head is zero)
      have h_excess_tail_eq : ∑' n, excess n =
          ∑' k, excess (k + 2 * (N + 1)) := by
        rw [← h_excess_summable.sum_add_tsum_nat_add (2 * (N + 1))]
        have : ∑ i ∈ Finset.range (2 * (N + 1)), excess i = 0 :=
          Finset.sum_eq_zero (fun i hi =>
            h_excess_zero_small i (Finset.mem_range.mp hi))
        linarith
      -- Each tail excess term ≤ 2p * ‖c_n‖ * L₀^n
      have h_excess_tail_bound : ∀ k, excess (k + 2 * (N + 1)) ≤
          2 * p * (‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
            L₀ ^ (k + 2 * (N + 1))) :=
        fun k => h_excess (k + 2 * (N + 1))
      -- ∑_{n≥2(N+1)} ‖c_n‖ * L₀^n ≤ ∑_{n≥N} ‖c_n‖ * L₀^n (subtail ≤ tail)
      have h_subtail : ∑' k, ‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
          L₀ ^ (k + 2 * (N + 1)) ≤
          ∑' k, ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N) := by
        have hf_nn : ∀ n, 0 ≤ ‖taylor_coeff phi_fn n‖ * L₀ ^ n := fun n =>
          mul_nonneg (norm_nonneg _) (pow_nonneg hL₀_pos.le _)
        have hfN : Summable (fun k => ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N)) :=
          h_phi_summable.comp_injective (fun a b h => by omega)
        have hkey : (fun k => ‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
            L₀ ^ (k + 2 * (N + 1))) =
            fun k => (fun k => ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N))
              (k + (2 * (N + 1) - N)) := by
          ext k; simp only [show k + (2 * (N + 1) - N) + N = k + 2 * (N + 1) from by omega]
        rw [hkey, ← hfN.sum_add_tsum_nat_add (2 * (N + 1) - N)]
        linarith [Finset.sum_nonneg (s := Finset.range (2 * (N + 1) - N))
          (fun i _ => hf_nn (i + N))]
      -- Combine everything
      rw [h_sf_decomp, h_excess_tail_eq]
      have h_tail_sum_bound : ∑' k, excess (k + 2 * (N + 1)) ≤
          2 * p * ∑' k, ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N) := by
        have h_rhs_summable : Summable (fun k =>
            2 * p * (‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
              L₀ ^ (k + 2 * (N + 1)))) :=
          (h_phi_summable.comp_injective (fun a b h => by omega)).mul_left _
        calc ∑' k, excess (k + 2 * (N + 1))
            ≤ ∑' k, 2 * p * (‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
                L₀ ^ (k + 2 * (N + 1))) := by
              apply Summable.tsum_le_tsum h_excess_tail_bound
              · exact h_excess_summable.comp_injective (fun a b h => by omega)
              · exact h_rhs_summable
          _ = 2 * p * ∑' k, ‖taylor_coeff phi_fn (k + 2 * (N + 1))‖ *
                L₀ ^ (k + 2 * (N + 1)) := tsum_mul_left
          _ ≤ 2 * p * ∑' k, ‖taylor_coeff phi_fn (k + N)‖ * L₀ ^ (k + N) := by
              apply mul_le_mul_of_nonneg_left h_subtail (by positivity)
      linarith
    have h2p : (0 : ℝ) < 2 * p := by positivity
    have h_tail_bound := mul_lt_mul_of_pos_left hN_tail h2p
    linarith
  -- Step C: Cr*p²*C_geom < p*gap*cL₀/4 (from threshold)
  have stepC : Cr * p ^ 2 * C_geom < p * gap * cL₀ / 4 := by
    have hden : 0 < 4 * (Cr * C_geom + 1) := by positivity
    have h1 : p * (4 * (Cr * C_geom + 1)) < gap * cL₀ :=
      by rwa [lt_div_iff₀ hden] at hp_lt_geom
    have h2 : Cr * C_geom * p < gap * cL₀ / 4 := by nlinarith
    have h3 : p ^ 2 ≤ p := by nlinarith [hp_lt1]
    nlinarith [hCr, hC_geom_pos]
  -- Combine: summability_fn < 1
  have hpgc : 0 < p * gap * cL₀ := by positivity
  linarith

/-! ### Main theorem -/

/-- **Theorem 5.1** (Braverman et al. 2011): There exist η, p, γ with
    γ > log(1+√2) such that F_p has an analytic inverse on disk(γ) with
    F_p⁻¹ mapping disk(γ) into S, and the Taylor coefficients satisfy
    the summability condition ∑|aₖ|γᵏ = 1.

    The proof follows the paper:
    1. Theorem 4.4 gives η with H_η(i)/i > log(1+√2)
    2. Lemma 5.3 gives analytic inverse on disk(r) for r < 1
    3. Lemma 5.4 gives F_inv ≈ sin + O(p), so summability_fn ≈ sinh > 1 at 9/10
    4. IVT gives γ with ∑|aₖ|γᵏ = 1
    5. Contradiction argument shows γ > log(1+√2) -/
theorem theorem_5_1 : ∃ (η : ℝ) (p : ℝ) (γ : ℝ),
    0 < η ∧ 0 < p ∧ γ > Real.log (1 + Real.sqrt 2) ∧ γ < 1 ∧
    ∃ (F_inv : ℂ → ℂ),
      AnalyticOnNhd ℂ F_inv (disk γ) ∧
      (∀ z ∈ disk γ, F_p η p (F_inv z) = z) ∧
      (∀ z ∈ disk γ, F_inv z ∈ S) ∧
      summability_condition (taylor_coeff F_inv) γ := by
  -- Step 1: Get η from Theorem 4.4
  obtain ⟨η, hη_pos, hη_improvement⟩ := exists_eta_strict_improvement
  -- Step 2: Choose r close to 1 (with r > 9/10 for the sinh argument)
  set r : ℝ := 19 / 20 with hr_def
  have hr_pos : 0 < r := by norm_num
  have hr_lt_1 : r < 1 := by norm_num
  have hr9 : 9 / 10 < r := by norm_num
  -- Step 3: From Lemma 5.4 (strong), get the approximation bound with ∃ F_inv
  obtain ⟨Cr, pr₀, hCr, hpr₀, h54⟩ := lemma_5_4_strong η r hr_pos hr_lt_1
  -- Step 4: Bound on φ(z) on closedBall(0, r)
  have h_phi_cont : ContinuousOn (fun z => (z - H_eta η (Complex.sin z)) * Complex.cos z)
      (closedBall (0 : ℂ) r) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.sub ((H_eta_analyticOnNhd η).continuousOn.comp
        Complex.continuous_sin.continuousOn (fun z hz => by
          rw [mem_S_iff]; exact norm_sin_lt_one_of_norm_lt_one z (lt_of_le_of_lt
            (by rwa [mem_closedBall, dist_zero_right] at hz) hr_lt_1)))
    · exact Complex.continuous_cos.continuousOn
  obtain ⟨B_phi, hB_phi⟩ :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn h_phi_cont
  -- Step 5: Set up comparison parameters
  set r_mid : ℝ := 37 / 40  -- between 9/10 and r=19/20
  have hr_mid_pos : 0 < r_mid := by norm_num
  have hr_mid_lt_r : r_mid < r := by norm_num
  have h9_lt_r_mid : (9 : ℝ) / 10 < r_mid := by norm_num
  set B_total := |B_phi| + Cr + 1
  have hB_total_pos : 0 < B_total := by positivity
  set ratio := r_mid / (r_mid - 9 / 10)
  have hratio_pos : 0 < ratio := by positivity
  set gap := Real.sinh (9 / 10) - 1
  have hgap_pos : 0 < gap := by linarith [sinh_nine_tenths_gt_one]
  -- gap_η = improvement from Theorem 4.4
  set gap_η := (H_eta η Complex.I / Complex.I).re - Real.log (1 + Real.sqrt 2)
  have hgap_η_pos : 0 < gap_η := by linarith
  -- Derivative threshold: F_p has nonzero derivative at 0 for small p
  obtain ⟨p_deriv, hp_deriv_pos, hp_deriv_cond⟩ := F_p_deriv_ne_zero_small_p η {0}
    isCompact_singleton (Set.singleton_subset_iff.mpr (by rw [mem_S_iff]; simp))
  -- Sign-structure threshold: summability_fn(F_inv, L₀) < 1 for small p
  obtain ⟨p_β, hp_β_pos, h_sf_lt⟩ :=
    summability_fn_at_log_lt_one η r hr_pos hr_lt_1 hr9 hη_improvement Cr hCr
  -- Step 6: Choose p small enough for everything
  set p_thresh := min pr₀ (min 1 (min (gap / (2 * B_total * ratio))
    (min (1 / (2 * gap_η)) (min p_deriv p_β))))
  have hp_thresh_pos : 0 < p_thresh := by
    apply lt_min hpr₀; apply lt_min one_pos; apply lt_min
    · exact div_pos hgap_pos (by positivity)
    · exact lt_min (div_pos one_pos (by positivity)) (lt_min hp_deriv_pos hp_β_pos)
  -- p := p_thresh / 2 < p_thresh
  have hp_val : p_thresh / 2 > 0 := by linarith
  have hp_lt_thresh : p_thresh / 2 < p_thresh := by linarith
  set p := p_thresh / 2 with hp_def
  have hp_pos : 0 < p := hp_val
  have hp_lt_pr₀ : p < pr₀ := lt_of_lt_of_le hp_lt_thresh (min_le_left _ _)
  have hp_lt1 : p < 1 := lt_of_lt_of_le hp_lt_thresh
    (le_trans (min_le_right _ _) (min_le_left _ _))
  -- Step 7: Get F_inv from lemma_5_4_strong
  obtain ⟨F_inv, hFa, hFi, hFS, hF0, hApprox⟩ := h54 p hp_pos hp_lt_pr₀
  -- Step 8: Bound ‖F_inv z - sin z‖ on closedBall(0, r_mid)
  set δ := p * B_total
  have hδ_nn : 0 ≤ δ := by positivity
  have h_bound : ∀ z ∈ Metric.closedBall (0 : ℂ) r_mid,
      ‖F_inv z - Complex.sin z‖ ≤ δ := by
    intro z hz
    have hz_disk : z ∈ disk r := by
      rw [mem_disk_iff]; rw [mem_closedBall, dist_zero_right] at hz; linarith
    have hz_cb : z ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right]; rw [mem_closedBall, dist_zero_right] at hz; linarith
    have hphi := hB_phi z hz_cb
    have hap := hApprox z hz_disk
    -- ‖F_inv z - sin z‖ ≤ ‖p*φ(z)‖ + Cr*p² ≤ p*|B_phi| + Cr*p ≤ p*B_total = δ
    set a := F_inv z - Complex.sin z - ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)
    set b := ↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)
    have hab : F_inv z - Complex.sin z = a + b := by simp only [a, b]; ring
    have hb : ‖b‖ ≤ p * |B_phi| := by
      simp only [b]
      calc ‖↑p * ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
          = ‖(↑p : ℂ)‖ * ‖(z - H_eta η (Complex.sin z)) * Complex.cos z‖ := norm_mul _ _
        _ = p * ‖(z - H_eta η (Complex.sin z)) * Complex.cos z‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp_pos]
        _ ≤ p * |B_phi| := by gcongr; exact le_trans hphi (le_abs_self _)
    calc ‖F_inv z - Complex.sin z‖ = ‖a + b‖ := by rw [hab]
      _ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
      _ ≤ Cr * p ^ 2 + p * |B_phi| := by linarith [hap]
      _ ≤ Cr * p + p * |B_phi| := by
          have : p ^ 2 ≤ p := by nlinarith [hp_lt1]
          nlinarith
      _ = p * (|B_phi| + Cr) := by ring
      _ ≤ p * B_total := by gcongr; linarith
  -- Step 9: Apply summability_fn_gt_one
  have hsin_an : AnalyticOnNhd ℂ Complex.sin (disk r) := fun z _ =>
    Complex.differentiable_sin.analyticAt z
  have hδ_small : summability_fn Complex.sin (9 / 10) - δ * r_mid / (r_mid - 9 / 10) > 1 := by
    -- δ * ratio < gap = sinh(9/10) - 1
    have hp_bound : p < gap / (2 * B_total * ratio) :=
      lt_of_lt_of_le hp_lt_thresh (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hδ_ratio : δ * ratio < gap := by
      calc δ * ratio = p * B_total * ratio := by simp only [δ]
        _ < gap / (2 * B_total * ratio) * B_total * ratio := by nlinarith
        _ = gap / 2 := by field_simp
        _ < gap := by linarith
    -- summability_fn sin (9/10) = sinh(9/10) (by definition + absolute convergence)
    -- This requires unfolding, but for now:
    -- δ * r_mid / (r_mid - 9/10) = δ * ratio, and gap = sinh(9/10) - 1
    -- summability_fn sin (9/10) ≥ sinh(9/10) (actually equal by absolute convergence of sin)
    -- So summability_fn sin (9/10) - δ*ratio ≥ sinh(9/10) - gap = 1 + (gap - δ*ratio) > 1
    rw [summability_fn_sin_eq_sinh (9 / 10) (by norm_num)]
    -- goal: sinh(9/10) - δ * r_mid / (r_mid - 9/10) > 1
    -- = sinh(9/10) - δ * (37/40) / (1/40) > 1
    -- = sinh(9/10) - δ * 37 > 1
    have h_ratio_eq : δ * r_mid / (r_mid - 9 / 10) = δ * ratio := by
      simp only [ratio]; ring
    rw [h_ratio_eq]
    -- Now: sinh(9/10) - δ * ratio > 1, i.e., gap > δ * ratio
    simp only [gap] at hδ_ratio; linarith
  have h_gt_one := summability_fn_gt_one F_inv r r_mid (9 / 10) hr_pos hr_mid_pos
    (by norm_num) h9_lt_r_mid hr_mid_lt_r hFa hsin_an h_bound hδ_nn hδ_small
  -- Step 10: IVT gives γ
  obtain ⟨γ, hγ_pos, hγ_lt, hγ_sum⟩ := exists_gamma_with_summability F_inv r hr_pos hFa hF0
    (9 / 10) (by norm_num) (by norm_num) h_gt_one
  -- Step 11: γ > log(1+√2) by summability function comparison
  -- For small p, summability_fn(F_inv, L₀) < 1 (sign-structure argument).
  -- Since summability_fn(F_inv, γ) = 1 and the function is monotone increasing, γ > L₀.
  have hγ_lt_r : γ < r := lt_trans hγ_lt (by norm_num : (9:ℝ)/10 < r)
  -- F_inv is odd (via right_inverse_unique)
  have hFp_an : AnalyticAt ℂ (F_p η p) 0 :=
    F_p_analyticOnNhd η p 0 (by rw [mem_S_iff]; simp)
  have hFp_deriv : deriv (F_p η p) 0 ≠ 0 := by
    have hp_lt_pd : p < p_deriv :=
      lt_of_lt_of_le hp_lt_thresh (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))))
    have hp_abs : |p| < p_deriv := by rwa [abs_of_pos hp_pos]
    exact hp_deriv_cond p hp_abs 0 (Set.mem_singleton _)
  have hF_odd := F_inv_odd η p r hr_pos hr_lt_1 hp_pos F_inv hFa hFi hFS hF0 hFp_an hFp_deriv
  -- p < p_β (sign-structure threshold)
  have hp_lt_pβ : p < p_β :=
    lt_of_lt_of_le hp_lt_thresh (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))))
  -- summability_fn F_inv L₀ < 1 from the sign-structure lemma
  have h_sf_lt_one := h_sf_lt p hp_pos hp_lt_pβ F_inv hFa hF_odd hApprox
  -- γ > L₀ by monotonicity of summability_fn
  set L₀ := Real.log (1 + Real.sqrt 2) with hL₀_def
  have hL₀_pos : 0 < L₀ := by
    apply Real.log_pos; linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]
  have hL₀_lt_9 : L₀ < 9 / 10 := by
    -- sinh(L₀) = 1 < sinh(9/10), so L₀ < 9/10 by strict monotonicity
    by_contra h; push_neg at h
    have h1 : Real.sinh L₀ = 1 := by
      rw [show L₀ = Real.arsinh 1 from by simp [L₀, Real.arsinh]; norm_num]
      exact Real.sinh_arsinh 1
    have h2 := sinh_nine_tenths_gt_one
    linarith [Real.sinh_le_sinh.mpr h]
  have hL₀_lt_r : L₀ < r := lt_trans hL₀_lt_9 hr9
  have hγ_gt_log : γ > L₀ := by
    by_contra hle
    push_neg at hle
    -- If γ ≤ L₀: summability_fn(γ) ≤ summability_fn(L₀) (monotone, nonneg coefficients)
    have h_sum_γ := summable_weights_of_lt_radius F_inv r γ hr_pos hγ_pos.le hγ_lt_r hFa
    have h_sum_L₀ := summable_weights_of_lt_radius F_inv r L₀ hr_pos hL₀_pos.le hL₀_lt_r hFa
    have h_le : summability_fn F_inv γ ≤ summability_fn F_inv L₀ := by
      simp only [summability_fn]
      exact h_sum_γ.tsum_mono h_sum_L₀ (fun k => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hγ_pos.le hle k) (norm_nonneg _))
    -- But summability_fn(γ) = 1 > summability_fn(L₀), contradiction
    have h_eq_one : summability_fn F_inv γ = 1 := by
      simp only [summability_fn, summability_condition, embedding_weight] at hγ_sum ⊢
      exact hγ_sum.tsum_eq
    linarith
  -- Step 12: Package
  refine ⟨η, p, γ, hη_pos, hp_pos, hγ_gt_log, ?_, F_inv, ?_, ?_, ?_, hγ_sum⟩
  · linarith  -- γ < 1 from γ < 9/10 < 1
  · exact hFa.mono (Metric.ball_subset_ball (le_of_lt hγ_lt_r))
  · exact fun z hz => hFi z (Metric.ball_subset_ball (le_of_lt hγ_lt_r) hz)
  · exact fun z hz => hFS z (Metric.ball_subset_ball (le_of_lt hγ_lt_r) hz)

/-! ### Corollary: existence of good embedding parameters -/

/-- The key consequence: we can find an embedding that gives a
    strictly better Grothendieck constant. -/
theorem exists_good_gamma :
    ∃ γ : ℝ, γ > Real.log (1 + Real.sqrt 2) ∧ γ < 1 ∧
    ∃ (η p : ℝ) (F_inv : ℂ → ℂ),
      0 < η ∧ 0 < p ∧
      summability_condition (taylor_coeff F_inv) γ ∧
      AnalyticOnNhd ℂ F_inv (disk γ) ∧
      (∀ z ∈ disk γ, F_p η p (F_inv z) = z) ∧
      (∀ z ∈ disk γ, F_inv z ∈ S) := by
  obtain ⟨η, p, γ, hη, hp, hγ, hγ1, F_inv, hFa, hFi, hFS, hSum⟩ := theorem_5_1
  exact ⟨γ, hγ, hγ1, η, p, F_inv, hη, hp, hSum, hFa, hFi, hFS⟩

end Braverman
