/-
  Candidates/V15.lean — replace V14's term-2 triangle product
  `u_zz_bound · M_phi²` with a single direct arb-certified oracle on
  the joint analytic quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`,
  dropping `Cr_val` from `1/1300 ≈ 7.692·10⁻⁴` to `1/2600 ≈ 3.846·10⁻⁴`
  (a 2× reduction).

  -- @parent Candidates/V14.lean
  -- @sprint Sprint_Contracts/sprint_020.md

  The substantive change: V15 introduces a NEW sixth oracle
  `h_uzz_phi_sq_oracle` certifying
    sup_{p ∈ [0, pr_paper], w ∈ Ω(δ_val, B_val)}
        ‖DD(p, w) · Phi(w)² / D(p, w)³‖  ≤  uzz_phi_sq_val
  via the new arb pipeline `compute_uzz_phi_sq_bound`. The certified
  rational at production parameters is `153/1000000 ≈ 1.53·10⁻⁴`,
  versus V14's triangle product `u_zz_bound · M_phi² ≈ 9.24·10⁻⁴`.
  The ~6× shrink in term-2 unlocks `Cr_val := 1/2600`.

  V15 keeps `M_val`, `delta_val`, `B_val`, `M_phi_val`,
  `M_phi_prime_val`, `inv_F_p_z_val`, `u_zz_bound_val`, and
  `joint_phi_phip_invD2_val` byte-identical to V14 (the V14 oracles
  remain declared for parity), but the new sink only consumes
  `h_joint_phi_phip_invD2_oracle`, `h_uzz_phi_sq_oracle`, and
  `h_oracle_domain_contains_image`. Five V14 oracles
  (`h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`,
  `h_inv_F_p_z_oracle`, `h_u_zz_oracle`) are now orphaned by the new
  sink — strict improvement.

  At V15 parameters:
    Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq
      = (3/10000) + (1/2)·(153/1000000)
      = 753/2000000
      ≈ 0.0003765.
  Setting `Cr_val := 1/2600 ≈ 0.0003846` leaves margin ≈ 8.12·10⁻⁶
  (~2.2% of RHS), which `norm_num` handles as pure rational arithmetic.

  Mathematical insight: the V14 term-2 was the dominant slack. The
  triangle bound `u_zz_bound · M_phi²` superimposes the *worst-case*
  (p, w) for `‖u_zz‖ = ‖DD‖/‖D‖³` and the *worst-case* w for `‖Φ‖²`,
  even though these need not bind together. The arb-certified joint
  scan binds them at a single (p, w) — the result `1.53·10⁻⁴` is
  ~6× smaller than the triangle product.

  Trust base (V14's plus one new entry):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V15 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V15 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V15 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V15 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V15 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (consumed by V15 sink).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (NEW; consumed by V15 sink).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle. Carried over from V14 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V14. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V14. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V14: `61/2500 = 0.0244`. NOT consumed by the new
V15 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V14
for parity; NOT consumed by the new V15 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V14 for parity; NOT consumed by the new V15 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V14: `15519/10000 = 1.5519`.
NOT consumed by the new V15 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Carried over from V14: `3/10000`.
Consumed by the V15 sink for term-1. -/
def joint_phi_phip_invD2_val : ℝ := 3 / 10000

/-- **NEW IN V15.** η-aware uniform-in-p direct upper bound on the
*joint* analytic quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖` over
`(p, w) ∈ [0, pr_paper] × Ω(δ_val, B_val)`. Set to `153/1000000 ≈
1.53·10⁻⁴`, the certified rational returned by
`Numerical_Library.compute_uzz_phi_sq_bound` at production-grade
precision (the actual arb sup is ≈ 1.5251·10⁻⁴). Consumed by the
V15 sink for term-2. -/
def uzz_phi_sq_val : ℝ := 153 / 1000000

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

theorem joint_phi_phip_invD2_val_pos : 0 < joint_phi_phip_invD2_val := by
  unfold joint_phi_phip_invD2_val; norm_num
theorem joint_phi_phip_invD2_val_nn : 0 ≤ joint_phi_phip_invD2_val :=
  le_of_lt joint_phi_phip_invD2_val_pos

theorem uzz_phi_sq_val_pos : 0 < uzz_phi_sq_val := by
  unfold uzz_phi_sq_val; norm_num
theorem uzz_phi_sq_val_nn : 0 ≤ uzz_phi_sq_val :=
  le_of_lt uzz_phi_sq_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 1/2600`) -/

/-- `Cr_val := 1/2600`, dominating the literal rational
`Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val`:
    LHS = (3/10000) + (1/2)·(153/1000000)
        = 753/2000000
        ≈ 0.0003765.
Margin to `Cr_val = 1/2600 ≈ 0.0003846` is ≈ 8.12·10⁻⁶ (~2.2% of RHS),
comfortably handled by `norm_num` for pure rational arithmetic. -/
def Cr_val : ℝ := 1 / 2600

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle -/

/-- The tight Step-1/Rouché-certified rectangle `Ω(delta_val, B_val)`. -/
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

/-- Certified single-`M` sup-norm bound. Carried over from V14 for
parity; not consumed by the new V15 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V14 for
parity; NOT consumed by the new V15 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V14 for
parity; NOT consumed by the new V15 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V14 for parity; NOT consumed by the new V15 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V14 for parity; NOT consumed by the new V15 sink. -/
axiom h_u_zz_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 3
              * u_zz_bound_val

/-- η-aware uniform-in-p direct upper bound on the joint analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Carried over from V14:
backed by `compute_joint_phi_phip_invD2_bound`. Consumed by the V15
sink for term-1. -/
axiom h_joint_phi_phip_invD2_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖(Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
            * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                - deriv Braverman.H0 w)‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 2
              * joint_phi_phip_invD2_val

/-- **NEW IN V15**: η-aware uniform-in-p direct upper bound on the
joint analytic quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`: for every
`p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
  `‖DD(p, w) · Phi(w)²‖ ≤ ‖∂_z F_p(η, p, w)‖³ · uzz_phi_sq_val`.

Runner-witnessed by `Numerical_Library.compute_uzz_phi_sq_bound`,
which returns a certified rational `153/1000000 ≈ 1.53·10⁻⁴` at
production parameters. -/
axiom h_uzz_phi_sq_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w
            * (Braverman.H_eta Braverman.SearchConfig.eta w
                - Braverman.H0 w) ^ 2‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 3
              * uzz_phi_sq_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V14; proved by
delegating to
`Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` (the
new wrapper introduced in sprint_020), threading the joint oracles
for both term-1 (`h_joint_phi_phip_invD2_oracle`) and term-2
(`h_uzz_phi_sq_oracle`). -/
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint2
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      joint_phi_phip_invD2_val joint_phi_phip_invD2_val_nn
      uzz_phi_sq_val uzz_phi_sq_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_joint_phi_phip_invD2_oracle h_uzz_phi_sq_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step:
  -- `Cr_phi_uzz_direct_joint2 joint uzz_phi_sq ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz_direct_joint2
          joint_phi_phip_invD2_val uzz_phi_sq_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz_direct_joint2 Cr_val
           joint_phi_phip_invD2_val uzz_phi_sq_val
    -- LHS = (3/10000) + (1/2)·(153/1000000)
    --     = 753/2000000
    --     ≈ 0.0003765
    -- ≤ 1/2600 ≈ 0.0003846  (margin ≈ 8.12·10⁻⁶, 2.2% of RHS).
    show (3 / 10000 : ℝ) + 1 / 2 * (153 / 1000000 : ℝ) ≤ 1 / 2600
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz_direct_joint2
          joint_phi_phip_invD2_val uzz_phi_sq_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
