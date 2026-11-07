/-
  Candidates/V13.lean — tighten V12's four η-aware oracle ceilings to
  their exact certified rational values, dropping `Cr_val` from
  `1/32 = 0.03125` to `1/300 ≈ 0.003333` (a 9.375× reduction).

  -- @parent Candidates/V12.lean
  -- @sprint Sprint_Contracts/sprint_018.md

  The substantive change: V13 is byte-identical to V12 in *shape* — same
  trust base (3 Lean primitives + 9 `F_inv_paper` seeds +
  `h_oracle_domain_contains_image` + 4 oracles
  `h_M_phi`/`h_M_phi_prime`/`h_inv_F_p_z`/`h_u_zz`), same structural
  chain (`Cr_phi_uzz_direct` formula, `_phi_uzz_direct` core lemma,
  `lemma_5_4_paper_on_domain_phi_uzz_direct` wrapper). Only the four
  numerical literals (and the resulting `Cr_val`) move:

    M_phi_val       :  239/5000   →  61/2500     (= 0.0244, certified)
    M_phi_prime_val :  543/10000  →  59/2000     (= 0.0295, certified)
    inv_F_p_z_val   :  2          →  3407/2000   (= 1.7035, certified)
    u_zz_bound_val  :  2          →  15519/10000 (= 1.5519, certified)
    Cr_val          :  1/32       →  1/300       (≈ 0.003333)

  The certified rationals are exactly what
  `Numerical_Library.compute_M_phi_bound`, `compute_M_phi_prime_bound`,
  `compute_inv_F_p_z_bound`, and `compute_u_zz_bound` return at
  production-grade precision; V12's prior literals were integer/round-
  rational *ceilings* above these for `norm_num`/`nlinarith` ergonomics
  in earlier sprints, leaving 1.96×, 1.84×, 1.17×, 1.29× of slack
  respectively (compounding to a ~12.25× literal-side overhead in
  `Cr_phi_uzz_direct` vs the literal `Cr_val`).

  At V13 parameters:
    Cr_phi_uzz_direct r_val M_phi M_phi_prime inv_F_p_z u_zz_bound
      = (61/2500)·(59/2000)·(3407/2000)² + (1/2)·(15519/10000)·(61/2500)²
      = 51015320591 / 20000000000000
      ≈ 0.0025507660.
  Setting `Cr_val := 1/300 ≈ 0.0033333` leaves margin ≈ 0.000783
  (23.48% of RHS) — comfortably above any `norm_num` numerical-tolerance
  threshold for pure rational arithmetic.

  Mathematical insight: the integer-ceiling pattern that V9/V10/V11/V12
  used (e.g., `M_phi_val := 239/5000` rather than `61/2500`,
  `inv_F_p_z_val := 2` rather than `3407/2000`) was a transient ergonomic
  choice in earlier sprints — the certified rationals are themselves
  clean enough for `norm_num` to handle the closing inequality directly,
  so dropping each literal to its certified value is honest and the
  slack vanishes. No structural change to the formula
  `Cr_phi_uzz_direct`, the four oracle axioms' content, or the proof
  chain in `Lemma54_Paper_Pderiv_Single.lean` /
  `Lemma54_Paper_Main.lean` — only the literals declared here.

  Trust base (byte-identical in shape to V12, only declared values move):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity).
    - `Braverman.PaperV0.h_M_phi_oracle` (declared bound now `61/2500`).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (declared bound now `59/2000`).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (declared bound now `3407/2000`).
    - `Braverman.PaperV0.h_u_zz_oracle` (declared bound now `15519/10000`).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V12 literals tightened to certified rationals) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V12 byte-identical for parity. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V12. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V12. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `61/2500 = 0.0244`, the exact certified rational returned by
`Numerical_Library.compute_M_phi_bound` at production-grade precision.
TIGHTENED in sprint_018 from V12's `239/5000` (1.96× slack removed). -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. Set to `59/2000 = 0.0295`, the exact certified rational
returned by `Numerical_Library.compute_M_phi_prime_bound` at production-
grade precision. TIGHTENED in sprint_018 from V12's `543/10000` (1.84×
slack removed). -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `3407/2000 = 1.7035`, the
exact certified rational returned by
`Numerical_Library.compute_inv_F_p_z_bound` at production-grade
precision. TIGHTENED in sprint_018 from V12's integer ceiling `2` (1.17×
slack removed). -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on
`‖∂²_z F_p(η, p, w)‖ / ‖∂_z F_p(η, p, w)‖³`. Equivalently, by the aux-z
identity, this is a direct upper bound on `‖u_zz‖`. Set to
`15519/10000 = 1.5519`, the exact certified rational returned by
`Numerical_Library.compute_u_zz_bound` at production-grade precision.
TIGHTENED in sprint_018 from V12's integer ceiling `2` (1.29× slack
removed). -/
def u_zz_bound_val : ℝ := 15519 / 10000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

theorem M_phi_val_pos : 0 < M_phi_val := by unfold M_phi_val; norm_num
theorem M_phi_val_nn : 0 ≤ M_phi_val := le_of_lt M_phi_val_pos
theorem M_phi_prime_val_pos : 0 < M_phi_prime_val := by
  unfold M_phi_prime_val; norm_num
theorem M_phi_prime_val_nn : 0 ≤ M_phi_prime_val :=
  le_of_lt M_phi_prime_val_pos

theorem inv_F_p_z_val_pos : 0 < inv_F_p_z_val := by
  unfold inv_F_p_z_val; norm_num
theorem inv_F_p_z_val_nn : 0 ≤ inv_F_p_z_val := le_of_lt inv_F_p_z_val_pos

theorem u_zz_bound_val_pos : 0 < u_zz_bound_val := by
  unfold u_zz_bound_val; norm_num
theorem u_zz_bound_val_nn : 0 ≤ u_zz_bound_val := le_of_lt u_zz_bound_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 1/300`) -/

/-- `Cr_val := 1/300`, dominating the literal rational
`Cr_phi_uzz_direct r_val M_phi_val M_phi_prime_val inv_F_p_z_val u_zz_bound_val`:
    Cr_phi_uzz_direct = 51015320591 / 20000000000000 ≈ 0.002551.
Margin to `Cr_val = 1/300 ≈ 0.003333` is ≈ 0.000783 (23.48% of RHS),
comfortably above the `norm_num` tolerance for pure rational
arithmetic. -/
def Cr_val : ℝ := 1 / 300

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

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
|H_η'| ≤ M_val` on the tight rectangle. Carried over from V12 for
parity; the `_phi_uzz_direct` wrapper does not consume this oracle (it
should not appear in the transitive axiom set of the sink, but it's
declared here so the per-candidate audit captures the same numerical-
witness surface that V12 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Declared bound `M_phi_val`
tightened from V12's `239/5000` to the certified `61/2500` in
sprint_018. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Declared bound
`M_phi_prime_val` tightened from V12's `543/10000` to the certified
`59/2000` in sprint_018. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Declared
bound `inv_F_p_z_val` tightened from V12's integer ceiling `2` to the
certified `3407/2000` in sprint_018. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on the analytic quotient
`‖∂²_z F_p / (∂_z F_p)³‖`: for every `p ∈ Ioo 0 pr_paper` and every
`w ∈ oracle_domain`,
  `‖∂²_z F_p(η, p, w)‖ ≤ ‖∂_z F_p(η, p, w)‖³ · u_zz_bound_val`.
Equivalently, `‖DD‖/‖D‖³ ≤ u_zz_bound_val` on the rectangle.

Runner-witnessed by `Numerical_Library.compute_u_zz_bound`, which
returns a certified rational `15519/10000 ≈ 1.5519`. Declared bound
`u_zz_bound_val` tightened from V12's integer ceiling `2` to the
certified `15519/10000` in sprint_018 (now exact-equal to the certified
output rather than a 1.29× ceiling above it). -/
axiom h_u_zz_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 3
              * u_zz_bound_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V12; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct`
(the η-aware wrapper introduced in sprint_016), threading the four
oracles with their tightened declared bounds. The conclusion's bound
`Cr_phi_uzz_direct r_val M_phi_val M_phi_prime_val inv_F_p_z_val u_zz_bound_val`
is then absorbed into the literal `Cr_val * p^2 = (1/300) * p^2` via
the monotonicity step
`Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound ≤ 1/300`,
justified by direct rational arithmetic on the literal constants. -/
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_prime_val M_phi_val_nn M_phi_prime_val_nn
      inv_F_p_z_val inv_F_p_z_val_nn
      u_zz_bound_val u_zz_bound_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle h_inv_F_p_z_oracle h_u_zz_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step:
  -- `Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz_direct Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val u_zz_bound_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz_direct Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val u_zz_bound_val
    -- LHS = (61/2500)·(59/2000)·(3407/2000)² + (1/2)·(15519/10000)·(61/2500)²
    --     = 51015320591 / 20000000000000
    --     ≈ 0.0025507660
    -- ≤ 1/300 ≈ 0.0033333  (margin ≈ 0.000783, 23.48% of RHS)
    show 61 / 2500 * (59 / 2000) * (3407 / 2000 : ℝ) ^ 2 +
        1 / 2 * (15519 / 10000 : ℝ) * (61 / 2500) ^ 2 ≤ 1 / 300
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz_direct Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val u_zz_bound_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
