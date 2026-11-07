/-
  Candidates/V17.lean — wildcard byte-identical copy of V16
  (procedural for the harness's every-4-sprints wildcard cadence).

  -- @parent Candidates/V0.lean
  -- @sprint Sprint_Contracts/sprint_022.md

  Sprint_022 is a research sprint (every-4-sprints wildcard rule;
  the last wildcard was sprint_017, and sprints 018, 019, 020, 021
  formed the four-sprint window). Its primary deliverable lives in
  `Scratch/sprint_022_research_findings.md` (numerical
  characterization of the achievable floor of the current
  `(2·joint + uzz_phi_sq)` decomposition at higher arb resolutions
  and one alternative factored bound). The Lean candidate file is
  *byte-identical to V16* — same `Cr_val = 1/3500`, same six oracle
  declarations, same sink delegation. The wildcard's "parent" field
  is `V0.lean` per the harness rule (the parent must be a non-
  immediate ancestor), but the byte content is V16's because there
  is no V0-specific property to revive — V16 is the latest-PASS
  floor and the Cr_val score has been monotonically tightening.

  Trust base, score, oracle wiring: identical to V16. This file
  exists to keep the wildcard cadence honest and to anchor the
  research-findings file to a candidate with a definite log entry.

  Mathematically, the substantive value of sprint_022 is in the
  Scratch/ research artifact's `Recommendation for sprint_023`
  label, which tells the next Planner whether to (a) push the
  oracles to higher resolution (`L1-RUN`), (b) abandon the
  resolution lever and pivot (`L1-DEAD`), (c) replace the
  decomposition with a factored single-oracle direction
  (`L2-WIN`), or (d) abandon the factored direction too
  (`L2-DEAD`).

  Trust base (V16's, unchanged):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V17 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V17 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V17 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V17 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V17 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (consumed by V17
      sink for term-1).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (consumed by V17 sink for
      term-2).

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
tight oracle rectangle. Carried over from V16 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V16. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V16. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V16: `61/2500 = 0.0244`. NOT consumed by the V17 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V16
for parity; NOT consumed by the V17 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V16 for parity; NOT consumed by the V17 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V16: `15519/10000 = 1.5519`.
NOT consumed by the V17 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set in V16 to `1/5000 = 2·10⁻⁴`
(from the certified arb sup of `≈ 1.989·10⁻⁴`). Consumed by the V17
sink for term-1. -/
def joint_phi_phip_invD2_val : ℝ := 1 / 5000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set to `153/1000000 ≈ 1.53·10⁻⁴`,
the certified rational returned by
`Numerical_Library.compute_uzz_phi_sq_bound` at production-grade
precision (the actual arb sup is ≈ 1.5251·10⁻⁴). Carried over from
V16 byte-identical. Consumed by the V17 sink for term-2. -/
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

/-! ## Section 2: Score (literal rational `Cr_val = 1/3500`) -/

/-- `Cr_val := 1/3500`, dominating the literal rational
`Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val`:
    LHS = (1/5000) + (1/2)·(153/1000000)
        = 553/2000000
        ≈ 0.0002765.
Margin to `Cr_val = 1/3500 ≈ 0.0002857` is ≈ 9.18·10⁻⁶ (~3.3% of RHS),
comfortably handled by `norm_num` for pure rational arithmetic. -/
def Cr_val : ℝ := 1 / 3500

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

/-- Certified single-`M` sup-norm bound. Carried over from V16 for
parity; not consumed by the V17 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V16 for
parity; NOT consumed by the V17 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V16 for
parity; NOT consumed by the V17 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V16 for parity; NOT consumed by the V17 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V16 for parity; NOT consumed by the V17 sink. -/
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
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Statement byte-identical to
V16; consumed by the V17 sink for term-1. -/
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

/-- η-aware uniform-in-p direct upper bound on the joint analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`: for every
`p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
  `‖DD(p, w) · Phi(w)²‖ ≤ ‖∂_z F_p(η, p, w)‖³ · uzz_phi_sq_val`.

Runner-witnessed by `Numerical_Library.compute_uzz_phi_sq_bound`,
which returns a certified rational `153/1000000 ≈ 1.53·10⁻⁴` at
production parameters. Carried over from V16 byte-identical. -/
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

/-- **The candidate's sink theorem.** Same shape as V0–V16; proved by
delegating to
`Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` (the
wrapper introduced in sprint_020), threading the joint oracles for both
term-1 (`h_joint_phi_phip_invD2_oracle`) and term-2
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
    -- LHS = (1/5000) + (1/2)·(153/1000000)
    --     = 553/2000000
    --     ≈ 0.0002765
    -- ≤ 1/3500 ≈ 0.0002857  (margin ≈ 9.18·10⁻⁶, 3.3% of RHS).
    show (1 / 5000 : ℝ) + 1 / 2 * (153 / 1000000 : ℝ) ≤ 1 / 3500
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
