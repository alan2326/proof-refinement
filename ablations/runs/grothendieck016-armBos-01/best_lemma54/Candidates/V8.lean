/-
  Candidates/V8.lean — promote `F_inv_paper_zero` from `axiom` to `theorem`
  in shared infrastructure (`Proof/Lib/Lemma54_Paper.lean`); literals are
  byte-identical to V7.

  -- @parent Candidates/V7.lean
  -- @sprint Sprint_Contracts/sprint_010.md

  V8 is byte-identical to V7 except for this header comment. The substantive
  change is **out-of-file**: `Proof/Lib/Lemma54_Paper.lean` now provides
  `F_inv_paper_zero` as a derived `theorem` (proved from `F_inv_paper_eq` +
  `Braverman.H0_injective` (from `LeanProof/Lemma52.lean`) +
  `Braverman.H0_sin_eq` + `F_inv_paper_mem_S`) rather than as a 12th
  trusted analytic axiom.

  Score: `Cr_val = 1132310000` exactly — unchanged from V7. The win is
  the audited axiom count: V7's 12 trusted analytic axioms drop to 11
  (specifically, `Braverman.Paper.F_inv_paper_zero` no longer appears
  in `axioms_used` because it's now a theorem). Trust base shrinks from
  3 + 12 + 2 = 17 to 3 + 11 + 2 = 16.

  Sprints 005, 006, 007, 008, 009 were all parameter-tweak axes
  (R-axis, sinh-direct, M-precision, rectangle-delta). Sprint 010 is
  the first axiom-prove move (Bulletin's "Current priority" direction
  1, per the 2026-04-30 REGIME SHIFT note). The motivating insight:
  `F_inv_paper_zero` is the unique axiom in the 12-axiom IFT package
  that follows from non-axiomatic infrastructure already present at
  the candidate's import chain (`Lemma52.lean`'s `H0_injective` and
  `H0_sin_eq` are fully proved Lean theorems; the IFT's branch-
  pinning at `p = 0` is therefore redundant).

  Trust base (one fewer axiom than V7):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper`
      family) — specifically `pr_paper`, `pr_paper_pos`,
      `pr_paper_le_one`, `F_inv_paper`, `F_inv_paper_eq`,
      `F_inv_paper_mem_S`, `F_inv_paper_R_bound`,
      `F_inv_paper_analytic`, `F_inv_paper_contdiff`,
      `F_inv_paper_at_origin`, `F_inv_paper_first_deriv_zero`.
      `F_inv_paper_zero` is NOT in this list — it is now a
      derived theorem.
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on
      `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, δ pushed to Rouché floor) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Set to `428`, the integer ceiling of the precision-bumped certified
`compute_M_bound_tight ≈ 855827/2000 ≈ 427.9135` (with
`n_per_edge=8192, prec=600, safety_rel=1e-5`). The certified arb ball
at the new rectangle is `[427.711 ± 0.198]`, so `428` is comfortably
above. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle, pushed to its Rouché-margin floor at fixed `B_val = 1115/1000`.
Sprint 009 found that `δ = 1635/10000 = 0.1635` is the largest rational
≤ 0.164 keeping the Rouché margin certified positive
(≈ 1.10·10⁻⁴ at the chosen precision); `δ ≥ 1636/10000` collapses
the margin. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. -/
def B_val : ℝ := 1115 / 1000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-! ## Section 2: Score (literal rational `Cr_val`, dominating `Cr_tight`) -/

/-- `Cr_val := 1132310000`, a literal rational dominating
`16 · M_val² · (23/20) · (23/20 + 1) / (1 − r_val)²`
(with `M_val = 428`, `r_val = 23/25`, so `1 − r_val = 2/25`):
    Cr_min = 16 · 428² · (23/20) · (43/20) · (625/4)
           = 16 · 183184 · (989/400) · (625/4)
           = 1132306100
and `Cr_val = 1132310000` is the next clean multiple of `10⁴` above
`Cr_min`, leaving the nlinarith margin
`Cr_val·(2/25)² − 16·428²·(23/20)·(43/20) = 624/25 = 24.96 > 0`. The
score gate's `_eval_rational` evaluates `Cr_val` directly; the sink
theorem closes via `Cr_tight r M (R_val_paper r) ≤ Cr_val`, justified by
`R_val_paper (23/25) ≤ 23/20`. -/
def Cr_val : ℝ := 1132310000

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25`
    (verbatim from V5/V6/V7; the R axis is not the focus of this sprint). -/

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

/-! ## Section 3: Oracle rectangle (the M-bound domain, δ pushed to floor) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, signatures unchanged) -/

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
|H_η'| ≤ M_val` on the tight rectangle `Ω(1635/10000, 1115/1000)`. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V2/V3/V4/V5/V6/V7;
proved by delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_tight`
to obtain `≤ Cr_tight r M (R_val_paper r) * p^2`, then absorbing into
the literal rational `Cr_val = 1132310000` via the monotonicity
`Cr_tight r M (R_val_paper r) ≤ Cr_val` (driven by
`R_val_paper r ≤ 23/20` and `M_val = 428`). The conclusion's `Cr_val`
is a rational that the per-candidate Evaluator scores directly,
yielding the same score as V7 (the win in V8 is on the audited axiom
count, not on `Cr_val`). -/
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
    --   16 * 428^2 * R * (R + 1) / (1 - 23/25)^2 ≤ 1132310000
    -- where R = R_val_paper (23/25). Replace `1 - 23/25` by `2/25`.
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (2 / 25) ^ 2)]
    -- Goal: 16 * 428^2 * R * (R + 1) ≤ 1132310000 * (2/25)^2
    -- 1132310000 * (2/25)^2 = 1132310000 * 4/625 = 7246784.00.
    -- And 16 * 428^2 * (23/20) * (43/20) = 16·183184·989/400
    --                                    = 181168976/25 ≈ 7246759.04.
    -- Margin: 624/25 = 24.96 > 0. So suffices: R·(R+1) ≤ (23/20)·(43/20) = 989/400,
    -- given 0 ≤ R ≤ 23/20.
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
