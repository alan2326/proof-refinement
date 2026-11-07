/-
  Candidates/V6.lean — switch axes from R to M: tighten the oracle's
  internal precision, drop `M_val` from `432` to `431`, dropping `Cr_val`
  from `1153569600` to `1148240000`.

  -- @parent Candidates/V5.lean
  -- @sprint Sprint_Contracts/sprint_008.md

  Sprints 005, 006, and 007 were all R-axis work (Cr-formula structure,
  R-as-rational, direct sinh bound). The R lever is now near its analytic
  floor: `sinh(49/50) ≈ 1.14457` vs the V5 bound `R_rat = 23/20 = 1.15`,
  leaving only ≈ 0.5% room. This sprint switches to the M lever, last
  visited in sprint 003 (M dropped 4000 → 432 via the Rouché-tightened
  rectangle `Ω(163/1000, 1115/1000)`). V6 retargets only the *internal
  precision* of `compute_M_bound_tight`:
      `n_per_edge`: 1024 → 4096
      `prec`     :  200 → 400
      `safety_rel`: 1e-3 → 1e-4
      `max_denom`: 10000 (unchanged)
      `δ`, `B`    : unchanged.
  At the earlier precision the certified rational bound was
  `4318113/10000 ≈ 431.81`; at the new precision it tightens to
  `215309/500 ≈ 430.62`, well below the integer `431`. The function
  signature, the rectangle, and the Rouché certification are all
  unchanged — this is a *retarget* of internal precision, not a new
  oracle. R remains at the V5 bound `23/20`.

  Score: `Cr_val = 1148240000` exactly
  (= `⌈16·431²·(23/20)·(43/20)/(2/25)² ⌉` rounded up to a clean multiple
  of `10000`), a 1.00465× reduction vs V5's `1153569600` (≈ 0.462% off
  the V5 baseline).

  Arithmetic identity (verified exactly via `Fraction` in
  `Scratch/sprint_008_verify.py`):
      Cr_min = 16·431²·(23/20)·(43/20)·(625/4)
             = 4592940725/4
             = 1148235181.25
      Cr_val = 1148240000  ≥  Cr_min   (margin 4818.75)
      LHS_max = 16·431²·(23/20)·(43/20)            = 183717629/25 ≈ 7348705.16
      RHS     = 1148240000 · (2/25)²              =        7348736
      nlinarith margin = RHS − LHS_max            = 771/25       = 30.84
  This margin is comfortable (compare V5's much tighter margin), so the
  same nlinarith hints from V5 close the polynomial step unchanged.

  Trust base (unchanged from V1/V2/V3/V4/V5):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  No new axioms; only `M_val`, `Cr_val`, and the literal `1153569600` in
  the Cr-monotonicity step move.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, unchanged from V1–V5) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`.
Set to `431`, the integer ceiling of the precision-bumped certified
`compute_M_bound_tight ≈ 215309/500 ≈ 430.62` (with
`n_per_edge=4096, prec=400, safety_rel=1e-4`). The earlier
low-precision bound (`n_per_edge=1024, prec=200`) was `≈ 431.81`,
hence V5's `432`; the precision retarget reveals that the underlying
arb ball is `≈ [430.18 ± ε]`, so `431` is comfortably above. -/
def M_val : ℝ := 431

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

/-- `Cr_val := 1148240000`, a literal rational dominating
`16 · M_val² · (23/20) · (23/20 + 1) / (1 − r_val)²`
(with `M_val = 431`, `r_val = 23/25`, so `1 − r_val = 2/25`):
    Cr_min = 16 · 431² · (23/20) · (43/20) · (625/4)
           = 16 · 185761 · (989/400) · (625/4)
           = 4592940725/4
           = 1148235181.25
and `Cr_val = 1148240000` is the next clean multiple of `10⁴` above
`Cr_min`, leaving a generous nlinarith margin
`Cr_val·(2/25)² − 16·431²·(23/20)·(43/20) = 30.84 > 0`. The score gate's
`_eval_rational` evaluates `Cr_val` directly; the sink theorem closes via
`Cr_tight r M (R_val_paper r) ≤ Cr_val`, justified by
`R_val_paper (23/25) ≤ 23/20`. -/
def Cr_val : ℝ := 1148240000

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25`
    (verbatim from V5; the R axis is not the focus of this sprint). -/

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

/-! ## Section 3: Oracle rectangle (the M-bound domain, unchanged from V1–V5) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, unchanged from V1–V5) -/

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

/-- **The candidate's sink theorem.** Same shape as V2/V3/V4/V5; proved
by delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_tight` to
obtain `≤ Cr_tight r M (R_val_paper r) * p^2`, then absorbing into
the literal rational `Cr_val = 1148240000` via the monotonicity
`Cr_tight r M (R_val_paper r) ≤ Cr_val` (driven by
`R_val_paper r ≤ 23/20` and `M_val = 431`). The conclusion's `Cr_val`
is a rational that the per-candidate Evaluator scores directly,
yielding the 1.00465× reduction vs V5 (≈ 0.462%). -/
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
    --   16 * 431^2 * R * (R + 1) / (1 - 23/25)^2 ≤ 1148240000
    -- where R = R_val_paper (23/25). Replace `1 - 23/25` by `2/25`.
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (2 / 25) ^ 2)]
    -- Goal: 16 * 431^2 * R * (R + 1) ≤ 1148240000 * (2/25)^2
    -- 1148240000 * (2/25)^2 = 1148240000 * 4/625 = 7348736.00.
    -- And 16 * 431^2 * (23/20) * (43/20) = 16·185761·989/400
    --                                    = 183717629/25 ≈ 7348705.16.
    -- Margin: 30.84 > 0. So suffices: R·(R+1) ≤ (23/20)·(43/20) = 989/400,
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
