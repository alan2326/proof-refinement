/-
  Candidates/V12.lean — replace V11's loose triangle product
  `‖u_zz‖ ≤ M_pp · inv_F_p_z³ ≈ 449` by a single direct inline oracle on
  the analytic quotient `‖∂²_z F_p / (∂_z F_p)³‖ ≤ 2`. Drops `Cr_val`
  from V11's `1` to `1/32` (a 32× reduction).

  -- @parent Candidates/V11.lean
  -- @sprint Sprint_Contracts/sprint_016.md

  The substantive change: V12 declares a NEW oracle axiom `h_u_zz_oracle`
  (runner-witnessed by `Numerical_Library.compute_u_zz_bound`, which
  certifies the joint sup `sup_{p,w} ‖DD/D³‖ ≤ 15519/10000 ≈ 1.5519`) and
  consumes it via the new core lemma `F_inv_p_second_deriv_bound_phi_uzz_direct`
  in `Lemma54_Paper_Pderiv_Single.lean`, together with the new wrapper
  `lemma_5_4_paper_on_domain_phi_uzz_direct` in `Lemma54_Paper_Main.lean`.
  V12 DROPS the now-unused `M_pp_val` definition and `h_M_pp_oracle` axiom
  — the new chain bypasses them entirely.

  At V12 parameters (V11 minus M_pp + the new u_zz_bound):
    r_val           = 23/25
    M_phi_val       = 239/5000
    M_phi_prime_val = 543/10000
    inv_F_p_z_val   = 2
    u_zz_bound_val  = 2     (NEW; certified ≈ 1.5519, integer ceiling)
  Then
    Cr_phi_uzz_direct r_val M_phi M_phi_prime inv_F_p_z u_zz_bound
      = (239/5000)·(543/10000)·4 + (1/2)·2·(239/5000)²
      = 519108/50000000 + 114242/50000000
      = 633350/50000000
      ≈ 0.01267.
  Setting `Cr_val := 1/32 = 0.03125` leaves margin ≈ 0.01858 — comfortable
  for `norm_num` on literal rationals.

  Mathematical insight: by the auxiliary z-identity `DD · h² + D · u_zz = 0`
  combined with `‖h‖ = 1/‖D‖`, we have `‖u_zz‖ = ‖DD‖/‖D‖³` exactly. V11
  bounded this loosely by `(sup ‖DD‖) · (sup 1/‖D‖)³ = M_pp · inv_F_p_z³`,
  but at p=0 the closed-form arcsin derivatives give the remarkable
  identity `H_0''(w)/H_0'(w)³ = w` exactly, so `g(0,w) = |w|` over the
  rectangle — a single direct sup of the analytic quotient is
  fundamentally tighter than the product of two independent sups.

  Trust base (one new oracle replacing V11's M_pp):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity).
    - `Braverman.PaperV0.h_M_phi_oracle` (V11 carried).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (V11 carried).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (V11 carried).
    - `Braverman.PaperV0.h_u_zz_oracle` (NEW; sprint_016) —
      `‖DD‖ ≤ ‖D‖³ · u_zz_bound_val` for every `p ∈ Ioo 0 pr_paper` and
      `w ∈ oracle_domain`. Runner-witnessed by
      `Numerical_Library.compute_u_zz_bound`, which returns a certified
      rational `15519/10000 ≈ 1.5519`, comfortably below
      `u_zz_bound_val := 2`.
    - `h_M_pp_oracle` is NO LONGER USED — dropped from the V12 trust set.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V11 - M_pp + the new u_zz_bound) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V11 byte-identical for parity. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `239/5000 = 0.0478`. Carried over from V11. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. Set to `543/10000 = 0.0543`. Carried over from V11. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `2`. Carried over from V11. -/
def inv_F_p_z_val : ℝ := 2

/-- η-aware uniform-in-p direct upper bound on
`‖∂²_z F_p(η, p, w)‖ / ‖∂_z F_p(η, p, w)‖³`. Equivalently, by the aux-z
identity, this is a direct upper bound on `‖u_zz‖`. Set to `2`, the
integer ceiling of the certified `compute_u_zz_bound = 15519/10000 ≈
1.5519` at production-grade precision (the arb pipeline returns a
certified ball ≈ [1.55017 ± 1.3·10⁻²⁰]). NEW in sprint_016 — replaces
V11's loose product `M_pp · inv_F_p_z³ ≈ 449`. -/
def u_zz_bound_val : ℝ := 2

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/32`) -/

/-- `Cr_val := 1/32`, dominating the literal rational
`Cr_phi_uzz_direct r_val M_phi_val M_phi_prime_val inv_F_p_z_val u_zz_bound_val`:
    Cr_phi_uzz_direct ≈ 0.01267.
Margin to `Cr_val = 1/32 = 0.03125` is ≈ 0.01858, comfortably above the
`norm_num` tolerance. -/
def Cr_val : ℝ := 1 / 32

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
|H_η'| ≤ M_val` on the tight rectangle. Carried over from V11 for
parity; the `_phi_uzz_direct` wrapper does not consume this oracle (it
should not appear in the transitive axiom set of the sink, but it's
declared here so the per-candidate audit captures the same numerical-
witness surface that V11 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V11. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V11. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V11. -/
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
returns a certified rational `15519/10000 ≈ 1.5519` — comfortably below
`u_zz_bound_val := 2`.

NEW in sprint_016. Replaces V11's loose triangle product
`‖u_zz‖ ≤ M_pp · inv_F_p_z³ ≈ 449` by a single direct sup of the
analytic quotient ≈ 1.55 — a 289× tightening. The bound's
multiplicative form `‖DD‖ ≤ ‖D‖³ · u_zz_bound_val` (rather than the
divisional form `‖DD‖/‖D‖³ ≤ u_zz_bound_val`) avoids requiring a
`‖D‖ > 0` hypothesis at the axiom level; the `_Pderiv_Single` proof
internally re-establishes `‖D‖ > 0` from the paper Cauchy bound and
divides through. -/
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

/-- **The candidate's sink theorem.** Same shape as V0–V11; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct`
(the new η-aware wrapper introduced in this sprint), threading the new
`h_u_zz_oracle` together with V11's other oracles (minus
`h_M_pp_oracle`). The conclusion's bound
`Cr_phi_uzz_direct r_val M_phi_val M_phi_prime_val inv_F_p_z_val u_zz_bound_val * p^2`
is then absorbed into the literal `Cr_val * p^2 = (1/32) * p^2` via the
monotonicity step
`Cr_phi_uzz_direct r M_phi M_phi_prime inv_F_p_z u_zz_bound ≤ 1/32`,
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
    -- LHS = (239/5000)·(543/10000)·4 + (1/2)·2·(239/5000)²
    --     = 519108/50000000 + 114242/50000000
    --     = 633350/50000000
    --     ≈ 0.01267
    -- ≤ 1/32 = 0.03125  (margin ≈ 0.01858)
    show 239 / 5000 * (543 / 10000) * (2 : ℝ) ^ 2 +
        1 / 2 * (2 : ℝ) * (239 / 5000) ^ 2 ≤ 1 / 32
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
