/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54_Paper.lean — paper-faithful proof of Lemma 5.4

A formalization of Braverman et al. §5 Lemma 5.4 following the paper's
strategy:

  1. Apply Lemma 5.3 at the outer radius `r₁ = (1+r)/2` so that `F_inv`
     is analytic on `disk r₁` (one step larger than the target).
  2. Bound `‖F_inv z‖ ≤ R := sinh r₂` for `z ∈ disk r₁`, where
     `r₂ = (3+r)/4 = (1+r₁)/2` is the W_inv radius.
  3. Apply Cauchy's estimate to `F_inv` recentred at `z₀ ∈ disk r`,
     yielding closed-form bounds on the first and second z-derivatives.
  4. Differentiate the identity `F_p(F_inv p z) = z` in `p` to get
     identity (75): `∂_p F_inv = -(H_η - H_0)(F_inv) / F_p'(F_inv)`.
  5. Differentiate identity (75) once more in `p`, bounding each piece
     by the certified sup-norm hypotheses, to get an explicit bound on
     `‖∂²_p F_inv‖`.
  6. Apply the Lagrange form of Taylor's theorem to the function
     `p ↦ F_inv p z - sin z - p · ψ(z)` to obtain the
     `‖…‖ ≤ Cr_paper · p²` conclusion.

Steps 1+2 are obtained from `Braverman.lemma_5_3_with_W_inv` separately for
each `p`. The paper-faithful proof requires *joint* regularity of the
family `(p, z) ↦ F_inv p z` in both parameters (so identity (75) makes
sense via the chain rule). That joint regularity is supplied here as a
trusted analytic input (the implicit function theorem applied to
`(p, w) ↦ F_p η p w` near `(0, sin z)` — a standard textbook fact).

The rest of the proof — Cauchy bounds, identity (75), the second-`p`
derivative bound, and the Lagrange Taylor remainder — is fully proved
in Lean from the axioms below and Mathlib.
-/

import LeanProof.Lemma54
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Cauchy

open Complex Set Metric Real

noncomputable section

namespace Braverman.Paper

/-! ## Section 1 — Nested radii `r < r₁ < r₂ < 1`

We use three radii throughout:
* `r`: the target — Taylor bound is stated on `disk r`.
* `r₁ := (1+r)/2`: outer disk where `F_inv` is analytic. Cauchy uses
  the gap `r₁ - r = (1-r)/2`.
* `r₂ := (3+r)/4 = (1+r₁)/2`: W_inv radius. `‖F_inv z‖ ≤ sinh r₂`.
-/

/-- Outer-disk radius — `F_inv` is analytic here. -/
def r1 (r : ℝ) : ℝ := (1 + r) / 2

/-- W_inv radius — bounds `‖F_inv z‖` via `sin`. -/
def r2 (r : ℝ) : ℝ := (3 + r) / 4

theorem r1_pos {r : ℝ} (hr0 : 0 < r) : 0 < r1 r := by unfold r1; linarith

theorem r1_lt_one {r : ℝ} (hr1 : r < 1) : r1 r < 1 := by unfold r1; linarith

theorem r_lt_r1 {r : ℝ} (hr1 : r < 1) : r < r1 r := by unfold r1; linarith

theorem r2_pos {r : ℝ} (hr0 : 0 < r) : 0 < r2 r := by unfold r2; linarith

theorem r2_lt_one {r : ℝ} (hr1 : r < 1) : r2 r < 1 := by unfold r2; linarith

theorem r1_lt_r2 {r : ℝ} (hr1 : r < 1) : r1 r < r2 r := by unfold r1 r2; linarith

theorem disk_subset_disk_r1 {r : ℝ} (hr1 : r < 1) :
    disk r ⊆ disk (r1 r) := by
  intro z hz
  rw [mem_disk_iff] at hz ⊢
  exact lt_trans hz (r_lt_r1 hr1)

/-! ## Section 2 — `‖sin z‖ ≤ sinh ‖z‖` and the `R`-bound

The sharp bound for `‖Complex.sin z‖` over `closedBall 0 r` is
`Real.sinh r`, achieved on the imaginary axis (`z = i·r`). Combined
with `lemma_5_3_with_W_inv` (which puts `W_inv z` in `closedBall 0 r₂`),
we get `‖F_inv z‖ ≤ sinh r₂` for `z ∈ disk r₁`.
-/

/-- `sinh²(x) - sinh²(y) = sinh(x+y) · sinh(x-y)`. -/
theorem sinh_sq_sub_sinh_sq (x y : ℝ) :
    Real.sinh x ^ 2 - Real.sinh y ^ 2 = Real.sinh (x + y) * Real.sinh (x - y) := by
  rw [Real.sinh_add, Real.sinh_sub]
  have h1 : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := Real.cosh_sq' y
  have h2 : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := Real.cosh_sq' x
  nlinarith [h1, h2]

/-- For `0 ≤ y ≤ x`, `x² - y² ≤ sinh²(x) - sinh²(y)`. -/
theorem sinh_sq_sub_sinh_sq_ge {x y : ℝ}
    (hxy : y ≤ x) (hy : 0 ≤ y) :
    x ^ 2 - y ^ 2 ≤ Real.sinh x ^ 2 - Real.sinh y ^ 2 := by
  rw [sinh_sq_sub_sinh_sq]
  have hxy_sum_nn : 0 ≤ x + y := by linarith
  have hxy_diff_nn : 0 ≤ x - y := by linarith
  have h1 : x + y ≤ Real.sinh (x + y) := Real.self_le_sinh_iff.mpr hxy_sum_nn
  have h2 : x - y ≤ Real.sinh (x - y) := Real.self_le_sinh_iff.mpr hxy_diff_nn
  have h3 : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  rw [h3]
  exact mul_le_mul h1 h2 hxy_diff_nn (le_trans hxy_sum_nn h1)

/-- The paper's tight R-bound: `‖Complex.sin z‖ ≤ Real.sinh ‖z‖`. -/
theorem norm_sin_le_sinh_norm (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  have hkey : ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
    have h := Braverman.norm_sq_sin_add_mul_I z.re z.im
    rw [Complex.re_add_im z] at h
    rw [h]
    have hpyt : Real.sin z.re ^ 2 + Real.cos z.re ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq z.re
    have hcsd : Real.cosh z.im ^ 2 - Real.sinh z.im ^ 2 = 1 :=
      Real.cosh_sq_sub_sinh_sq z.im
    nlinarith [hpyt, hcsd, sq_nonneg (Real.sin z.re), sq_nonneg (Real.cos z.re),
               sq_nonneg (Real.sinh z.im), sq_nonneg (Real.cosh z.im)]
  have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h_sin_le : Real.sin z.re ^ 2 ≤ z.re ^ 2 := by
    have h1 : |Real.sin z.re| ≤ |z.re| := Real.abs_sin_le_abs
    have h2 : |Real.sin z.re| ^ 2 ≤ |z.re| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs, sq_abs] at h2
  have h_im_le : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h_norm_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have h_abs_im_nn : 0 ≤ |z.im| := abs_nonneg _
  have h_sinh_diff :
      ‖z‖ ^ 2 - |z.im| ^ 2 ≤ Real.sinh ‖z‖ ^ 2 - Real.sinh |z.im| ^ 2 :=
    sinh_sq_sub_sinh_sq_ge h_im_le h_abs_im_nn
  have h_im_abs_sq : |z.im| ^ 2 = z.im ^ 2 := sq_abs z.im
  have h_sinh_im_abs : Real.sinh |z.im| ^ 2 = Real.sinh z.im ^ 2 := by
    by_cases hb : 0 ≤ z.im
    · rw [abs_of_nonneg hb]
    · push_neg at hb
      rw [abs_of_neg hb, Real.sinh_neg, neg_sq]
  have h_sq_bound : ‖Complex.sin z‖ ^ 2 ≤ Real.sinh ‖z‖ ^ 2 := by
    rw [hkey]
    have hsh : ‖z‖ ^ 2 - z.im ^ 2 ≤ Real.sinh ‖z‖ ^ 2 - Real.sinh z.im ^ 2 := by
      rw [← h_im_abs_sq, ← h_sinh_im_abs]; exact h_sinh_diff
    have hre_sq : z.re ^ 2 = ‖z‖ ^ 2 - z.im ^ 2 := by rw [h_norm_sq]; ring
    linarith [h_sin_le.trans_eq hre_sq]
  have h_norm_sin_nn : 0 ≤ ‖Complex.sin z‖ := norm_nonneg _
  have h_sinh_nn : 0 ≤ Real.sinh ‖z‖ := Real.sinh_nonneg_iff.mpr h_norm_nn
  nlinarith [h_sq_bound, h_norm_sin_nn, h_sinh_nn,
             sq_nonneg (‖Complex.sin z‖ - Real.sinh ‖z‖),
             sq_nonneg (‖Complex.sin z‖ + Real.sinh ‖z‖)]

/-- `‖sin z‖ ≤ sinh R` on `closedBall 0 R`. -/
theorem norm_sin_le_sinh_of_mem_closedBall {R : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) R) : ‖Complex.sin z‖ ≤ Real.sinh R := by
  have hz_norm : ‖z‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hz
  calc ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := norm_sin_le_sinh_norm z
    _ ≤ Real.sinh R := Real.sinh_le_sinh.mpr hz_norm

/-- The paper's R-bound: `R_val_paper r := sinh r₂ = sinh ((3+r)/4)`. -/
def R_val_paper (r : ℝ) : ℝ := Real.sinh (r2 r)

theorem R_val_paper_pos {r : ℝ} (hr0 : 0 < r) : 0 < R_val_paper r := by
  unfold R_val_paper
  exact Real.sinh_pos_iff.mpr (r2_pos hr0)

theorem R_val_paper_nonneg {r : ℝ} (hr0 : 0 < r) : 0 ≤ R_val_paper r :=
  le_of_lt (R_val_paper_pos hr0)

/-! ## Section 3 — F_inv on the outer disk (Steps 1+2 combined)

Wraps `lemma_5_3_with_W_inv` at radius `r₁`. Adds the closed-form
`R := sinh r₂` bound on `‖F_inv z‖` via `‖sin (W_inv z)‖ ≤ sinh r₂`.

This is the *non-joint* version: for each `p` separately, we get an
analytic right-inverse on `disk r₁`. Joint regularity in `(p, z)` is
provided independently below. -/

/-- **Step 1+2.** For each `p` separately, an analytic right-inverse
exists on `disk r₁`, with `‖F_inv z‖ ≤ R_val_paper r`. -/
theorem F_inv_R_bound (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ pr_paper > 0, ∀ p : ℝ, 0 < p → p < pr_paper →
      ∃ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (disk (r1 r)) ∧
        (∀ z ∈ disk (r1 r), F_p η p (F_inv z) = z) ∧
        (∀ z ∈ disk (r1 r), F_inv z ∈ S) ∧
        F_inv 0 = 0 ∧
        (∀ z ∈ disk (r1 r), ‖F_inv z‖ ≤ R_val_paper r) := by
  obtain ⟨pr, hpr_pos, hspec⟩ :=
    Braverman.lemma_5_3_with_W_inv η (r1 r) (r1_pos hr0) (r1_lt_one hr1)
  refine ⟨pr, hpr_pos, ?_⟩
  intro p hp0 hppr
  obtain ⟨W_inv, F_inv, _hW_an, hF_an, hW_mem, hF_eq, hF_inv_right, hF_mem, hF_zero⟩ :=
    hspec p hp0 hppr
  refine ⟨F_inv, hF_an, hF_inv_right, hF_mem, hF_zero, ?_⟩
  intro z hz
  have hr2_eq : (1 + r1 r) / 2 = r2 r := by unfold r1 r2; ring
  rw [hF_eq z hz]
  have hWmem : W_inv z ∈ closedBall (0 : ℂ) ((1 + r1 r) / 2) := hW_mem z hz
  rw [hr2_eq] at hWmem
  exact norm_sin_le_sinh_of_mem_closedBall hWmem

/-! ## Section 3b — Joint-regular `F_inv_paper : ℝ → ℂ → ℂ`

The paper's argument differentiates `p ↦ F_inv p z` at fixed `z`. That
requires a *joint*-regular family in `(p, z)`. The implicit function
theorem applied to `G(p, w) := F_p η p w - z` near `(0, sin z)` produces
such a family — this is a textbook fact (every grad student would accept
it on sight) but its Lean formalization requires non-trivial real-vs-
complex differentiability bridging via Mathlib's IFT API.

We *axiomatize* the existence of such a joint-regular family. The axioms
below assert exactly what the IFT delivers: a `C²`-in-`p`, analytic-in-`z`
family with `F_p η p (F_inv_paper p z) = z`, `F_inv_paper 0 z = sin z`,
the analytic image control `‖F_inv_paper p z‖ ≤ R_val_paper r`, and the
correct first-`p`-derivative at `p = 0`.

The remaining steps (3, 4, 5, 6) and the top-level theorem are
**fully proved** Lean theorems, with no further axioms.
-/

/-- The paper's joint-regular threshold (axiomatized — supplied by IFT). -/
axiom pr_paper (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : ℝ

axiom pr_paper_pos (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    0 < pr_paper η r hr0 hr1

/-- `pr_paper ≤ 1`. We need this so that `p ∈ Ioo 0 pr_paper ⊆ Icc 0 1`,
giving access to the `M_pp` hypothesis on `F_p η p` for `p ∈ Icc 0 1`. -/
axiom pr_paper_le_one (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    pr_paper η r hr0 hr1 ≤ 1

/-- The paper's joint-regular analytic right-inverse `F_inv_paper : ℝ → ℂ → ℂ`
(axiomatized — supplied by the analytic implicit function theorem applied to
`(p, w) ↦ F_p η p w` near `(0, sin z)`). -/
axiom F_inv_paper (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : ℝ → ℂ → ℂ

/-- Right-inverse identity: `F_p η p (F_inv_paper p z) = z` for
`p ∈ [0, pr_paper)` and `z ∈ disk r₁`. -/
axiom F_inv_paper_eq (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ p ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1),
    ∀ z ∈ disk (r1 r), F_p η p (F_inv_paper η r hr0 hr1 p z) = z

/-- The image lies in `S` (so `H_0`, `H_eta` are differentiable there). -/
axiom F_inv_paper_mem_S (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ p ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1),
    ∀ z ∈ disk (r1 r), F_inv_paper η r hr0 hr1 p z ∈ S

/-- At `p = 0`, the family is `sin` (since `F_p η 0 = H0 = arcsin`).
**Proved** from `F_inv_paper_eq` + `Braverman.H0_injective` (Lemma 5.2) +
`Braverman.H0_sin_eq` + `F_inv_paper_mem_S`. (Was an axiom prior to
sprint 010; promoted to a theorem because the supporting infrastructure
in `LeanProof/Lemma52.lean` already provides `H0_injective` and
`H0_sin_eq` as non-axiomatic Lean theorems, making the IFT's
branch-pinning at `p = 0` derivable.) -/
theorem F_inv_paper_zero (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z ∈ disk (r1 r), F_inv_paper η r hr0 hr1 0 z = Complex.sin z := by
  intro z hz
  -- Step 1: F_p η 0 (F_inv_paper 0 z) = z (from axiom F_inv_paper_eq at p = 0).
  have h0_in_Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1) :=
    Set.mem_Ico.mpr ⟨le_refl 0, pr_paper_pos η r hr0 hr1⟩
  have h_eq : F_p η 0 (F_inv_paper η r hr0 hr1 0 z) = z :=
    F_inv_paper_eq η r hr0 hr1 0 h0_in_Ico z hz
  -- Step 2: F_p η 0 = H0 (algebraic, from F_p definition).
  have h_F_p_0 : ∀ w, F_p η 0 w = Braverman.H0 w := by
    intro w; unfold F_p; simp
  rw [h_F_p_0] at h_eq
  -- Now h_eq : H0 (F_inv_paper 0 z) = z.
  -- Step 3: |z.re| < π/2 (since |z| < r1 r ≤ 1 < π/2).
  have h_z_norm : ‖z‖ < r1 r := (mem_disk_iff z (r1 r)).mp hz
  have hr1_le_one : r1 r ≤ 1 := by unfold r1; linarith
  have h_re_bound : |z.re| < Real.pi / 2 := by
    have h_pi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hzre_le_norm : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    linarith
  -- Step 4: sin z ∈ S (using `norm_sin_lt_one_of_norm_lt_one`).
  have h_z_norm_lt_one : ‖z‖ < 1 := lt_of_lt_of_le h_z_norm hr1_le_one
  have h_sin_z_S : Complex.sin z ∈ S := by
    rw [mem_S_iff]
    exact Braverman.norm_sin_lt_one_of_norm_lt_one z h_z_norm_lt_one
  -- Step 5: H0 (sin z) = z (apply Braverman.H0_sin_eq from Lemma52.lean).
  have h_H0_sin : Braverman.H0 (Complex.sin z) = z :=
    Braverman.H0_sin_eq z h_re_bound h_sin_z_S
  -- Step 6: F_inv_paper 0 z ∈ S (axiom F_inv_paper_mem_S).
  have h_F_inv_S : F_inv_paper η r hr0 hr1 0 z ∈ S :=
    F_inv_paper_mem_S η r hr0 hr1 0 h0_in_Ico z hz
  -- Step 7: H0_injective concludes (both points in S map to same z).
  exact Braverman.H0_injective h_F_inv_S h_sin_z_S (h_eq.trans h_H0_sin.symm)

/-- The image is bounded by `R_val_paper r` (Step 1+2 of the paper). -/
axiom F_inv_paper_R_bound (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ p ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1),
    ∀ z ∈ disk (r1 r), ‖F_inv_paper η r hr0 hr1 p z‖ ≤ R_val_paper r

/-- For each fixed `p ∈ (0, pr_paper)`, the section `F_inv_paper p` is
analytic on `disk r₁`. (This is what the IFT's `OpenPartialHomeomorph.analyticAt_symm`
delivers.) -/
axiom F_inv_paper_analytic (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ p ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1),
    AnalyticOnNhd ℂ (F_inv_paper η r hr0 hr1 p) (disk (r1 r))

/-- The family is `C²` in `p` on `[0, pr_paper)`, uniformly over `z ∈ disk r`.
(This is what `IsContDiffImplicitAt.implicitFunction` delivers, up to the
real-vs-complex bridging needed to pull `C²` regularity from the joint
implicit function back to a single section.) -/
axiom F_inv_paper_contdiff (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z ∈ disk r,
      ContDiffOn ℝ 2 (fun q : ℝ => F_inv_paper η r hr0 hr1 q z)
        (Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1))

/-- The family fixes the origin: `F_inv_paper p 0 = 0` for `p ∈ [0, pr_paper)`.

This follows from `F_p η p (F_inv_paper p z) = z` at `z = 0` (which gives
`F_p η p (F_inv_paper p 0) = 0`) plus local invertibility of `F_p η p` near
0 (with `F_p η p 0 = 0` since `H_0(0) = H_eta(0) = 0`). The IFT delivers
this branch automatically; we axiomatize it. -/
axiom F_inv_paper_at_origin (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ p ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1),
      F_inv_paper η r hr0 hr1 p 0 = 0

/-- The `p`-derivative of the family at `p = 0` is the paper's `ψ(z)`:
specifically, `(z - H_eta η (sin z)) · cos z`.

This follows from identity (75) at `p = 0`: `∂_p F_inv |_0 = -(H_η - H_0)(sin z) / H_0'(sin z)`,
with `H_0(sin z) = z`, `H_0'(sin z) = 1/cos z`, so
`∂_p F_inv |_0 = -(H_η(sin z) - z) · cos z = (z - H_η(sin z)) · cos z`. -/
axiom F_inv_paper_first_deriv_zero (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ z ∈ disk r,
      HasDerivWithinAt (fun q : ℝ => F_inv_paper η r hr0 hr1 q z)
        ((z - H_eta η (Complex.sin z)) * Complex.cos z)
        (Set.Ici (0 : ℝ)) 0

/-! ## Section 4 — The F_inv-image envelope

Sup-norm hypotheses live on this set. By `F_inv_paper_R_bound` and
`F_inv_paper_mem_S`, the actual image is contained here. -/

/-- Envelope `closedBall 0 R ∩ S` containing the F_inv image. The
sup-norm hypotheses for `Cr_paper` are stated on this set. -/
def F_inv_envelope (r : ℝ) : Set ℂ := closedBall (0 : ℂ) (R_val_paper r) ∩ S

theorem F_inv_image_subset_envelope {η p r : ℝ} (hr1 : r < 1)
    {F_inv : ℂ → ℂ} (hF_S : ∀ z ∈ disk (r1 r), F_inv z ∈ S)
    (hF_R : ∀ z ∈ disk (r1 r), ‖F_inv z‖ ≤ R_val_paper r) :
    ∀ z ∈ disk (r1 r), F_inv z ∈ F_inv_envelope r := by
  intro z hz
  refine ⟨?_, hF_S z hz⟩
  rw [mem_closedBall, dist_zero_right]
  exact hF_R z hz

/-! ## Section 5 — Two `Cr` formulas

Two different `Cr` constants live side-by-side, both in terms of `r, R` and
sup-norm hypotheses on the F_inv-image envelope:

1. **`Cr_paper` (literal, paper-faithful).** The exact formula from
   Braverman et al. (2011) p.23:
   ```
   Cr_paper r M R := 8·M²·R/(1-r)² · (1 + 16·R/(1-r)³)
   ```
   where `M ≥ max{|H_0|, |H_η|, |H_0'|, |H_η'|}` on the F_inv envelope.
   `M_pp` does *not* appear — the paper bounds `d²/dz² F⁻¹_p` directly via
   Cauchy on the `(1+r)/2`-disk (giving `16R/(1-r)³`).

2. **`Cr_refined` (tighter, used internally by `lemma_5_4_refined`).**
   Uses *differences* and an explicit `M_pp` bound on `F_p''`:
   ```
   Cr_refined r M_diff M_diffp M_pp R
     := M_diff·M_diffp·invFp² + M_pp·M_diff²·invFp³/2,
        invFp := 2R/(1-r).
   ```
   Substituting `M_diff, M_diffp = O(η)` makes the leading term `O(η²)`,
   producing a much tighter bound at small `η`. -/

/-! ### `Cr_paper` — the paper-faithful (literal) formula -/

/-- **Braverman et al.'s literal `Cr` from Lemma 5.4 (p.23).**
    `Cr_paper r M R := 8·M²·R/(1-r)² · (1 + 16·R/(1-r)³)`. -/
def Cr_paper (r M R : ℝ) : ℝ :=
  8 * M ^ 2 * R / (1 - r) ^ 2 * (1 + 16 * R / (1 - r) ^ 3)

theorem Cr_paper_nonneg {r M R : ℝ}
    (hr1 : r < 1) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    0 ≤ Cr_paper r M R := by
  unfold Cr_paper
  have h1mr_pos : 0 < 1 - r := by linarith
  have h1mr_sq_pos : 0 < (1 - r) ^ 2 := by positivity
  have h1mr_cu_pos : 0 < (1 - r) ^ 3 := by positivity
  have hbig_nn : 0 ≤ 16 * R / (1 - r) ^ 3 := by positivity
  have hsum_nn : 0 ≤ 1 + 16 * R / (1 - r) ^ 3 := by linarith
  have hlead_nn : 0 ≤ 8 * M ^ 2 * R / (1 - r) ^ 2 := by positivity
  exact mul_nonneg hlead_nn hsum_nn

/-! ### `Cr_tight` — the constant the paper's Step-5 derivation actually
establishes (before the loose `(2R+1)(1-r)³ ≤ 16R` algebraic step)

`F_inv_p_second_deriv_bound_paper` produces, immediately before its
`alg_step_paper` invocation, the literal bound

    ‖∂²_p F_inv‖ ≤ 32 M² R (R + 1) / (1 - r)²,

which the paper-faithful proof then weakens to `2 · Cr_paper r M R`
via the (loose) algebraic inequality `(2R+1)(1-r)³ ≤ 16R`. At the
candidate's parameters `(r = 23/25, M = 432, R = sinh(24/25))` the
algebraic step inflates the constant by ≈ 10870×, propagating to an
≈ 8340× loss on `Cr`. Defining `Cr_tight := 16 M² R (R+1) / (1-r)²`
exposes the constant the proof actually establishes (so the Lagrange
remainder absorbs the `1/2!` factor against `2 · Cr_tight`, matching
the role `2 · Cr_paper` plays today). -/
def Cr_tight (r M R : ℝ) : ℝ := 16 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2

theorem Cr_tight_nonneg {r M R : ℝ}
    (hr1 : r < 1) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    0 ≤ Cr_tight r M R := by
  -- `hM` is in the signature for parity with `Cr_paper_nonneg`; `positivity`
  -- closes the goal via `M ^ 2 ≥ 0` without consulting it.
  let _ := hM
  unfold Cr_tight
  have h1mr_pos : 0 < 1 - r := by linarith
  positivity

/-! ### `Cr_refined` — the tighter formula used by `lemma_5_4_refined` -/

/-- The refined `Cr`, structured as follows:
* `invFp := 2 R / (1 - r)` — upper bound on `‖1/F_p'(F_inv z)‖` (Step 3).
* First chunk `M_diff · M_diffp · invFp²` — from
  `(H_η' - H_0')(F_inv) · ∂_p F_inv / F_p'(F_inv)`.
* Second chunk `(M_pp · M_diff² · invFp³) / 2` — from
  `(H_η - H_0)(F_inv) · F_p''(F_inv) · ∂_p F_inv / F_p'(F_inv)²`.

Both chunks already absorb the Lagrange `1/2` factor. -/
def Cr_refined (r M_diff M_diffp M_pp R : ℝ) : ℝ :=
  let invFp := 2 * R / (1 - r)
  M_diff * M_diffp * invFp ^ 2 + M_pp * M_diff ^ 2 * invFp ^ 3 / 2

theorem Cr_refined_nonneg {r M_diff M_diffp M_pp R : ℝ}
    (hr1 : r < 1) (hMdiff : 0 ≤ M_diff) (hMdiffp : 0 ≤ M_diffp)
    (hMpp : 0 ≤ M_pp) (hR : 0 ≤ R) :
    0 ≤ Cr_refined r M_diff M_diffp M_pp R := by
  unfold Cr_refined
  have h1mr_pos : 0 < 1 - r := by linarith
  have hinvFp_nn : 0 ≤ 2 * R / (1 - r) := by positivity
  positivity

/-! ### `Cr_phi` — η-aware constant consuming `M_phi`, `M_phi_prime` only

Hybrid form between `Cr_tight` (single-`M`, with the triangle bound `‖Φ‖, ‖Φ'‖ ≤ 2M`)
and `Cr_refined` (consuming all three proposal_001 oracles): keeps the direct
Cauchy step `‖u_zz‖ ≤ 8R/(1-r)²` (avoiding the implicit-function chain through
`M_pp`), but tightens the two triangle bounds via the η-aware sup norms
`M_phi ≥ ‖H_η - H_0‖` and `M_phi_prime ≥ ‖H_η' - H_0'‖`.

The structure is:
* `invFp := 2 R / (1 - r)` — upper bound on `‖1/F_p'(F_inv z)‖` (Step 3).
* First chunk `M_phi · M_phi_prime · invFp²` — from
  `(H_η' - H_0')(F_inv) · ∂_p F_inv / F_p'(F_inv)` (was `2M · 2M · invFp²`
  in `Cr_tight`).
* Second chunk `(4R/(1-r)²) · M_phi²` — from
  `(H_η - H_0)(F_inv)² · ∂²_z F_inv / 2!` (was `(8R/(1-r)²) · (2M)² / 2`
  in `Cr_tight`; the `/ 2` came from absorbing the Lagrange factor, now
  rolled into the `4R` numerator instead of `8R`).

Both chunks already absorb the Lagrange `1/2` factor, so
`‖∂²_p F_inv‖ ≤ 2 · Cr_phi r M_phi M_phi_prime R`. -/
def Cr_phi (r M_phi M_phi_prime R : ℝ) : ℝ :=
  let invFp := 2 * R / (1 - r)
  M_phi * M_phi_prime * invFp ^ 2 + (4 * R / (1 - r) ^ 2) * M_phi ^ 2

theorem Cr_phi_nonneg {r M_phi M_phi_prime R : ℝ}
    (hr1 : r < 1) (hMphi : 0 ≤ M_phi) (hMphip : 0 ≤ M_phi_prime)
    (hR : 0 ≤ R) :
    0 ≤ Cr_phi r M_phi M_phi_prime R := by
  unfold Cr_phi
  have h1mr_pos : 0 < 1 - r := by linarith
  have hinvFp_nn : 0 ≤ 2 * R / (1 - r) := by positivity
  positivity

/-! ### `Cr_phi_invD` — η-aware Cr formula taking an arb-certified `1/‖D‖` bound

Same shape as `Cr_phi`, but the `invFp = 2R/(1−r)` "paper-worst-case" bound on
`1/‖∂_z F_p‖` is replaced by an *abstract* `inv_F_p_z` parameter, supplied at
the candidate level by an arb-certified oracle (≈ 2 at the V9 parameters,
versus the paper bound ≈ 28.75). This is a 14× tightening of `invFp` and
hence ~196× tightening of `invFp²` — a structural win sourced entirely from
the term-1 of `Cr_phi` (the `M_phi · M_phi_prime · invFp²` chunk). The
term-2 (Cauchy on `u_zz`) is unchanged. -/
def Cr_phi_invD (r M_phi M_phi_prime R inv_F_p_z : ℝ) : ℝ :=
  M_phi * M_phi_prime * inv_F_p_z ^ 2 + (4 * R / (1 - r) ^ 2) * M_phi ^ 2

theorem Cr_phi_invD_nonneg {r M_phi M_phi_prime R inv_F_p_z : ℝ}
    (hr1 : r < 1) (hMphi : 0 ≤ M_phi) (hMphip : 0 ≤ M_phi_prime)
    (hR : 0 ≤ R) (hinv : 0 ≤ inv_F_p_z) :
    0 ≤ Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z := by
  unfold Cr_phi_invD
  have h1mr_pos : 0 < 1 - r := by linarith
  positivity

/-! ### `Cr_phi_uzz` — η-aware Cr formula taking arb-certified `1/‖D‖` and `‖DD‖` bounds

Same shape as `Cr_phi_invD`, but the second-term Cauchy bound on `‖u_zz‖`
(`‖u_zz‖ ≤ 8R/(1-r)²` via `F_inv_second_deriv_bound_core`) is replaced
by an aux-z-identity-driven bound `‖u_zz‖ ≤ M_pp · inv_F_p_z³` derived
from the identity `DD · h² + D · u_zz = 0` together with the certified
sup-norm bounds `‖DD‖ ≤ M_pp` and `1/‖D‖ ≤ inv_F_p_z`.

The `r` and `R` arguments are no longer needed in the formula proper
(they are absent from the second term), but they remain in the
signature for API parity with `Cr_phi`/`Cr_phi_invD`. -/
def Cr_phi_uzz (r M_phi M_phi_prime inv_F_p_z M_pp : ℝ) : ℝ :=
  M_phi * M_phi_prime * inv_F_p_z ^ 2
    + (1 / 2) * M_pp * inv_F_p_z ^ 3 * M_phi ^ 2

theorem Cr_phi_uzz_nonneg {r M_phi M_phi_prime inv_F_p_z M_pp : ℝ}
    (hMphi : 0 ≤ M_phi) (hMphip : 0 ≤ M_phi_prime)
    (hinv : 0 ≤ inv_F_p_z) (hMpp : 0 ≤ M_pp) :
    0 ≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp := by
  unfold Cr_phi_uzz
  positivity

end Braverman.Paper
