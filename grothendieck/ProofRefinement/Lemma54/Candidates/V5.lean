/-
  Candidates/V5.lean — bound `R_val_paper(23/25) = sinh(49/50)` directly via
  `Real.exp_bound`, dropping `Cr_val` from `1231718400` to `1153569600`.

  -- @parent Candidates/V4.lean
  -- @sprint Sprint_Contracts/sprint_007.md

  V4 used the loose two-step chain
  `sinh(49/50) ≤ sinh(1) ≤ 6/5` (via `Real.sinh_le_sinh` then
  `Real.exp_one_lt_d9`). The first step is the dominant slack: the actual
  `sinh(49/50) ≈ 1.14457` lives ≈ 0.011 below `sinh(1) ≈ 1.17520`,
  costing ≈ 6% on `R(R+1)`. V5 bounds `sinh(49/50)` *directly* using
  `Real.exp_bound` on the depth-10 Taylor truncation at `x = ±49/50`,
  capturing that slack. This is distinct from sprint_006's "R-rationalisation"
  axis: that one tightened the `sinh(1) → rational` step; this one removes
  the unnecessary `sinh(49/50) ≤ sinh(1)` step entirely.

  Score: `Cr_val = 1153569600` exactly
  (= `16 · 432² · (23/20) · (43/20) / (2/25)²`), a 1.0677× reduction
  vs V4's `1231718400` (≈ 6.34% off the V4 baseline).

  Direct-bound numerics (computed exactly via `Fraction` in
  `Scratch/V5_verify_taylor.py` and in `Scratch/planner_007_pick_R.py`):
    - Depth-10 Taylor sum
        S+ := Σ_{m<10} (49/50)^m / m! ≈ 2.66445599...
        S- := Σ_{m<10} (-49/50)^m / m! ≈ 0.37531089...
    - Tolerance per side: |x|^10 · 11 / (10! · 10) ≈ 2.477·10⁻⁷.
    - Worst case e^x − e^(−x) ≤ (S+ − S-) + 2·tol ≈ 2.28914560,
      well below 23/10 = 2.3 (margin ≈ 0.01085).
    - Hence sinh(49/50) ≤ 23/20.

  Trust base (unchanged from V1/V2/V3/V4):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  No new axioms are introduced; the tightening only invokes existing
  Mathlib facts about `Real.sinh`, `Real.exp_bound`, and `Real.exp_bound'`.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, unchanged from V1/V2/V3/V4) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`.
Set to `432`, the integer ceiling of the certified
`compute_M_bound_tight ≈ 431.81`. -/
def M_val : ℝ := 432

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. -/
def delta_val : ℝ := 163 / 1000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. -/
def B_val : ℝ := 1115 / 1000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-! ## Section 2: Score (literal rational `Cr_val`, dominating `Cr_tight`) -/

/-- `Cr_val := 1153569600`, a literal rational equal to
`16 · M_val² · (23/20) · (23/20 + 1) / (1 − r_val)²`
(with `M_val = 432`, `r_val = 23/25`, so `1 − r_val = 2/25`):
`16 · 186624 · (23/20) · (43/20) / (4/625)
   = 16 · 186624 · (989/400) · (625/4)
   = 186624 · 6181.25
   = 1153569600`.
The score gate's `_eval_rational` evaluates `Cr_val` directly without
touching `Real.sinh`. The sink theorem closes via
`Cr_tight r M (R_val_paper r) ≤ Cr_val`, justified by
`R_val_paper (23/25) ≤ 23/20`. -/
def Cr_val : ℝ := 1153569600

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25` -/

/-- `R_val_paper (23/25) = sinh (49/50) ≤ 23/20`. Proved by directly
    bounding the two exponentials in `sinh(49/50) = (exp(49/50) − exp(−49/50))/2`
    via `Real.exp_bound` / `Real.exp_bound'` at depth `n = 10` (Taylor
    truncation tolerance ≈ `2.48·10⁻⁷` on each side, sum ≈ `5·10⁻⁷`,
    safely below the ≈ `0.011` nlinarith margin against `2.3`). -/
theorem R_val_paper_le_twentythree_twentieths :
    Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 23 / 20 := by
  -- Reduce to `sinh ((3 + 23/25)/4) ≤ 23/20`, i.e. `sinh (49/50) ≤ 23/20`.
  unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
  have h_arg : (3 + (23 : ℝ) / 25) / 4 = 49 / 50 := by norm_num
  rw [h_arg]
  -- Step 1: rewrite `sinh (49/50)` as `(exp(49/50) − exp(−49/50)) / 2`.
  have h_sinh : Real.sinh (49 / 50 : ℝ) =
      (Real.exp (49 / 50) - Real.exp (-(49 / 50))) / 2 := Real.sinh_eq _
  rw [h_sinh]
  -- Step 2: upper-bound `Real.exp (49/50)` via `Real.exp_bound'` at `n = 10`.
  have hx_nn : (0 : ℝ) ≤ 49 / 50 := by norm_num
  have hx_le_one : (49 : ℝ) / 50 ≤ 1 := by norm_num
  have h_upper :
      Real.exp (49 / 50 : ℝ) ≤
        (Finset.range 10).sum (fun m => (49 / 50 : ℝ) ^ m / m.factorial)
          + (49 / 50 : ℝ) ^ 10 * (10 + 1 : ℝ) / ((Nat.factorial 10 : ℝ) * 10) :=
    Real.exp_bound' hx_nn hx_le_one (by decide : 0 < 10)
  -- Step 3: lower-bound `Real.exp (-(49/50))` via `Real.exp_bound` at `n = 10`.
  have h_abs_le_one : |(-(49 / 50) : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hx_nn]; exact hx_le_one
  have h_bound_neg :
      |Real.exp (-(49 / 50 : ℝ)) -
         (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial)|
        ≤ |(-(49 / 50) : ℝ)| ^ 10 *
            (Nat.succ 10 / ((Nat.factorial 10 : ℝ) * 10)) :=
    Real.exp_bound h_abs_le_one (by decide : 0 < 10)
  have h_abs_eq : |(-(49 / 50) : ℝ)| = 49 / 50 := by
    rw [abs_neg, abs_of_nonneg hx_nn]
  rw [h_abs_eq] at h_bound_neg
  -- Step 4: evaluate the two Taylor sums to literal rationals.
  have h_S_plus :
      (Finset.range 10).sum (fun m => (49 / 50 : ℝ) ^ m / m.factorial) =
        269776169487175721557 / 101250000000000000000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
               Nat.factorial, Nat.cast_one, Nat.cast_mul,
               pow_zero, pow_succ]
    norm_num
  have h_S_minus :
      (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial) =
        38000227837801227143 / 101250000000000000000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
               Nat.factorial, Nat.cast_one, Nat.cast_mul,
               pow_zero, pow_succ]
    norm_num
  rw [h_S_plus] at h_upper
  -- Convert the absolute-value bound on `exp(-49/50)` to a one-sided lower bound.
  have h_lower : Real.exp (-(49 / 50 : ℝ)) ≥
      (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial)
        - (49 / 50 : ℝ) ^ 10 *
            (Nat.succ 10 / ((Nat.factorial 10 : ℝ) * 10)) := by
    have := abs_sub_le_iff.mp h_bound_neg
    linarith [this.1, this.2]
  rw [h_S_minus] at h_lower
  -- Step 5: replace `Nat.factorial 10` and `Nat.succ 10` with their numeric values.
  have h_fact : (Nat.factorial 10 : ℝ) = 3628800 := by simp [Nat.factorial]
  rw [h_fact] at h_upper
  have h_lower' : Real.exp (-(49 / 50 : ℝ)) ≥
      38000227837801227143 / 101250000000000000000
        - (49 / 50 : ℝ) ^ 10 * (11 / (3628800 * 10)) := by
    have hsucc : (Nat.succ 10 : ℝ) = 11 := by norm_num
    rw [hsucc, h_fact] at h_lower
    exact h_lower
  -- Step 6: `(exp(49/50) - exp(-49/50)) / 2 ≤ 23/20` iff
  --         `exp(49/50) - exp(-49/50) ≤ 23/10`.
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  -- Combine `h_upper` (S+ + tol upper bound) and `h_lower'` (S- − tol lower bound):
  --   exp(49/50) − exp(−49/50) ≤ (S+ − S-) + 2·tol ≈ 2.28914560 < 23/10.
  nlinarith [h_upper, h_lower']

/-! ## Section 3: Oracle rectangle (the M-bound domain, unchanged from V1/V2/V3/V4) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, unchanged from V1/V2/V3/V4) -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Certified single-`M` sup-norm bound: `|H_0|, |H_η|, |H_0'|,
|H_η'| ≤ M_val` on the tight rectangle `Ω(163/1000, 1115/1000)`. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V2/V3/V4; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_tight` to
obtain `≤ Cr_tight r M (R_val_paper r) * p^2`, then absorbing into
the literal rational `Cr_val = 1153569600` via the monotonicity
`Cr_tight r M (R_val_paper r) ≤ Cr_val` (driven by
`R_val_paper r ≤ 23/20`). The conclusion's `Cr_val` is a rational that
the per-candidate Evaluator scores directly, yielding the 1.0677×
reduction vs V4 (≈ 6.34%). -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  obtain ⟨pr, hpr_pos, h_main⟩ :=
    Braverman.Paper.lemma_5_4_paper_on_domain_tight
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_tight r M (R_val_paper r) * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  have hR_le :
      Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 23 / 20 :=
    R_val_paper_le_twentythree_twentieths
  have hR_nn :
      (0 : ℝ) ≤ Braverman.Paper.R_val_paper Braverman.SearchConfig.r :=
    Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos
  -- Monotonicity step: `Cr_tight r M R ≤ Cr_val` for our parameters.
  have h_Cr_le :
      Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)
        ≤ Cr_val := by
    -- Re-express `hR_le`/`hR_nn` against the literal `23/25` so that they
    -- match the goal after `unfold ... SearchConfig.r`.
    have hR_le' :
        Braverman.Paper.R_val_paper (23 / 25 : ℝ) ≤ 23 / 20 := by
      have := hR_le
      unfold Braverman.SearchConfig.r at this
      exact this
    have hR_nn' :
        (0 : ℝ) ≤ Braverman.Paper.R_val_paper (23 / 25 : ℝ) := by
      have := hR_nn
      unfold Braverman.SearchConfig.r at this
      exact this
    unfold Braverman.Paper.Cr_tight Cr_val M_val Braverman.SearchConfig.r
    -- After unfolds the goal reads (modulo norm_num on (1 - 23/25)):
    --   16 * 432^2 * R * (R + 1) / (1 - 23/25)^2 ≤ 1153569600
    -- where R = R_val_paper (23/25). Replace `1 - 23/25` by `2/25`.
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (2 / 25) ^ 2)]
    -- Goal: 16 * 432^2 * R * (R + 1) ≤ 1153569600 * (2/25)^2
    -- 1153569600 * (2/25)^2 = 1153569600 * 4/625 = 7382845.44
    --                       = 184571136/25.
    -- And 16 * 432^2 * (23/20) * (43/20) = 16·186624·989/400
    --                                    = 184571136/25.
    -- So suffices: R·(R+1) ≤ (23/20)·(43/20) = 989/400 = 2.4725, given 0 ≤ R ≤ 23/20.
    nlinarith [hR_le', hR_nn', sq_nonneg (R - 23/20), sq_nonneg R,
               mul_nonneg hR_nn' hR_nn']
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r) * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
