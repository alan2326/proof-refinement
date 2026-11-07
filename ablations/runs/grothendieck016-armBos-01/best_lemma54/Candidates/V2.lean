/-
  Candidates/V2.lean — switch `Cr_val` from `Cr_paper` to `Cr_tight`,
  eliminating the loose `(2R+1)(1-r)³ ≤ 16R` algebraic-step slack.

  -- @parent Candidates/V1.lean
  -- @sprint Sprint_Contracts/sprint_004.md

  V2 inherits V1's tight Rouché-certified rectangle `Ω(163/1000, 1115/1000)`
  and `M_val := 432`, but replaces V1's `Cr_val := Cr_paper r M (R_val_paper r)`
  by `Cr_val := Cr_tight r M (R_val_paper r) = 16 M² R (R+1) / (1-r)²`.

  `Cr_tight` is the constant the paper-faithful proof of
  `F_inv_p_second_deriv_bound_paper` (in `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`,
  the line containing `h_arith` simplification) literally establishes
  *before* the loose algebraic step `(2R+1)(1-r)³ ≤ 16R` weakens it to
  `2 · Cr_paper r M R`. At our parameters
  `(r = 23/25, M = 432, R = sinh(24/25))`, the algebraic step inflates
  the constant by ≈ 10870×, propagating to an ≈ 8340× loss.

  Switching to `Cr_tight` exposes the proof's actual Step-5 output. The
  Lagrange Taylor step `taylor_remainder_p` is `Cr`-polymorphic, so this
  substitution requires no new analysis: a parallel proof chain
  `Cr_tight` / `F_inv_p_second_deriv_bound_tight` /
  `lemma_5_4_paper_on_domain_tight` lives alongside the paper-faithful
  chain in `Proof/Lib/Lemma54_Paper*.lean`.

  Score: `Cr_val ≈ 1.145·10⁹` — an ≈ 8340× reduction vs V1's ≈ 9.55·10¹².

  Trust base (unchanged from V1):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  No new axioms are introduced; `Cr_tight`,
  `F_inv_p_second_deriv_bound_tight`, and `lemma_5_4_paper_on_domain_tight`
  are all `def`/`theorem` declarations proved from the existing axiom set.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle, unchanged from V1) -/

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

/-! ## Section 2: Score (paper's `Cr_tight` formula at the chosen tuple) -/

/-- `Cr_val := Cr_tight r M_val (R_val_paper r)`. The constant the paper's
Step-5 derivation literally establishes (before the loose `(2R+1)(1-r)³ ≤ 16R`
algebraic step). With `M_val = 432` (from V1) and the algebraic-step slack
removed, this evaluates to ≈ 1.145·10⁹ — an ≈ 8340× reduction vs V1. -/
def Cr_val : ℝ :=
  Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val
    (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)

theorem Cr_val_nn : 0 ≤ Cr_val :=
  Braverman.Paper.Cr_tight_nonneg
    Braverman.SearchConfig.r_lt_one
    M_val_nn
    (Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos)

/-! ## Section 3: Oracle rectangle (the M-bound domain, unchanged from V1) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed, unchanged from V1) -/

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

/-- **The candidate's sink theorem.** Same shape as V1; proved by direct
delegation to `Braverman.Paper.lemma_5_4_paper_on_domain_tight` (parallel
to V1's `lemma_5_4_paper_on_domain`). The conclusion's `Cr_val` factor
is `Cr_tight` rather than `Cr_paper`, yielding the ≈ 8340× score
reduction. -/
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
            ≤ Cr_val * p ^ 2 :=
  Braverman.Paper.lemma_5_4_paper_on_domain_tight
    Braverman.SearchConfig.eta Braverman.SearchConfig.r
    Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
    M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle

end Braverman.PaperV0
