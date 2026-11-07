/-
  Candidates/V22.lean — linear successor to V21 along the
  `oracle-resolution-tightening` axis: bump `n_per_edge` default
  from `16384` to `32768` in both `compute_joint_phi_phip_invD2_bound`
  and `compute_uzz_phi_sq_bound`, retarget the two consumed-oracle
  ceilings to the tighter rationals returned by the planner's fresh
  scans at the V21 rationaliser settings (`safety_abs=1e-8`,
  `max_denom=10⁷`), and drop `Cr_val` from `1/71900` (V21) to
  `1/124000` (V22).

  -- @parent Candidates/V21.lean
  -- @sprint Sprint_Contracts/sprint_027.md

  Sprint_027 is a *linear* sprint: V21 is the latest-PASS at
  `Cr_val = 1/71900`. The mechanism here is purely in the
  ball_value (the underlying arb supremum): halving the boundary
  cell width via `n_per_edge=16384 → 32768` narrows each per-cell
  acb interval, shrinking the certified supremum on both joint
  oracles by ~41-48%. The rationaliser's tightening parameters are
  unchanged from V21 (sprint_026 already exhausted ~95% of the
  rationalisation slack on the V21 ball values; the new V22 ball
  values have 0.74%/3.57% slack, so a future sprint along
  `oracle-ceiling-tightening` could squeeze the uzz ceiling further).

  The planner's `Scratch/sprint_027_planner_run_n32768.py` ran both
  oracles end-to-end at `n_per_edge=32768` with the V21 rationaliser
  settings and recorded:

    - joint quotient `‖Phi · Phi'/D²‖`: ball_value `≈ 6.452·10⁻⁶`,
      rationalised `13/2000000 = 6.50·10⁻⁶` (slack 0.74%) in 33.9s.
    - uzz quotient   `‖DD · Phi²/D³‖`:  ball_value `≈ 2.993·10⁻⁶`,
      rationalised `31/10000000 = 3.10·10⁻⁶` (slack 3.57%) in 46.3s.

  Per-doubling reduction history on these oracles has been
  monotonically decreasing (2048→4096: −68.6%/−71.9%; 4096→8192:
  −61.6%/−65.0%; 8192→16384: −50.0%/−60.0%; 16384→32768: −41.2%/
  −48.2%), confirming the bound is genuinely interval-width-
  dominated rather than true-value-dominated.

  The new triangle bound
    `joint + (1/2)·uzz_phi_sq = 13/2000000 + (1/2)·31/10000000
                              = 65/10000000 + 31/20000000
                              = 130/20000000 + 31/20000000
                              = 161/20000000
                              = 8.05·10⁻⁶`
  is dominated by `Cr_val = 1/124000 ≈ 8.065·10⁻⁶` with comfortable
  integer margin `20000000 − 124000·161 = 36000` (rational margin
  `36000/(124000·2·10⁷) ≈ 1.45·10⁻⁸`), giving a `1.724×` win over
  V21's `Cr_val = 1/71900` and a cumulative `~1.018·10²⁰×`
  reduction over V0.

  The structural form of `Cr_phi_uzz_direct_joint2 joint uzz =
  joint + (1/2)·uzz` (Proof/Lib/Lemma54_Paper.lean:567) is unchanged.
  The proof body of `lemma_5_4_search` is byte-identical to V21
  modulo the three numeric literals and the `show` line in the
  monotonicity step.

  Trust base (V21's, unchanged):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V22 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V22 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V22 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V22 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V22 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (consumed by V22
      sink for term-1).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (consumed by V22 sink for
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
tight oracle rectangle. Carried over from V21 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V21. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V21. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V21: `61/2500 = 0.0244`. NOT consumed by the V22 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V21
for parity; NOT consumed by the V22 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V21 for parity; NOT consumed by the V22 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V21: `15519/10000 = 1.5519`.
NOT consumed by the V22 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set in V22 to
`13/2000000 = 6.50·10⁻⁶`, the certified rational returned by
`Numerical_Library.compute_joint_phi_phip_invD2_bound` at production
parameters (n_per_edge=32768, prec=200, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 6.452·10⁻⁶` (slack 0.74%).
Consumed by the V22 sink for term-1. -/
def joint_phi_phip_invD2_val : ℝ := 13 / 2000000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set in V22 to
`31/10000000 = 3.10·10⁻⁶`, the certified rational returned by
`Numerical_Library.compute_uzz_phi_sq_bound` at production parameters
(n_per_edge=32768, prec=200, safety_abs=1e-8, max_denom=10⁷); the
actual arb sup is `≈ 2.993·10⁻⁶` (slack 3.57%). Consumed by the V22
sink for term-2. -/
def uzz_phi_sq_val : ℝ := 31 / 10000000

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/124000`) -/

/-- `Cr_val := 1/124000`, dominating the literal rational
`Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val`:
    LHS = (13/2000000) + (1/2)·(31/10000000)
        = 65/10000000 + 31/20000000
        = 130/20000000 + 31/20000000
        = 161/20000000
        = 8.05·10⁻⁶.
Margin to `Cr_val = 1/124000 ≈ 8.065·10⁻⁶` is the integer margin
`20000000 − 124000·161 = 20000000 − 19964000 = 36000` (rational margin
`36000/(124000·2·10⁷) ≈ 1.45·10⁻⁸`), comfortably handled by
`norm_num` for pure rational arithmetic. The mechanical rational
check `1/124000 ≥ 161/20000000 ⇔ 20000000 ≥ 124000·161 = 19964000`.
Cumulative win `~1.018·10²⁰×` over V0 (V0 was `≈ 8.196·10¹⁴`, V22 is
`1/124000 ≈ 8.065·10⁻⁶`, ratio `8.196·10¹⁴ / 8.065·10⁻⁶ ≈ 1.016·10²⁰`). -/
def Cr_val : ℝ := 1 / 124000

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

/-- Certified single-`M` sup-norm bound. Carried over from V21 for
parity; not consumed by the V22 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V21 for
parity; NOT consumed by the V22 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V21 for
parity; NOT consumed by the V22 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V21 for parity; NOT consumed by the V22 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V21 for parity; NOT consumed by the V22 sink. -/
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
V21; consumed by the V22 sink for term-1. The declared bound
`joint_phi_phip_invD2_val = 13/2000000` dominates the certified arb sup
`≈ 6.452·10⁻⁶` at n_per_edge=32768 with safety_abs=1e-8/max_denom=10⁷
(slack 0.74%). -/
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
which returns a certified rational `31/10000000 ≈ 3.10·10⁻⁶` at
production parameters (n_per_edge=32768, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 2.993·10⁻⁶` (slack 3.57%).
Consumed by the V22 sink for term-2. -/
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

/-- **The candidate's sink theorem.** Same shape as V0–V21; proved by
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
    -- LHS = (13/2000000) + (1/2)·(31/10000000)
    --     = 65/10000000 + 31/20000000
    --     = 130/20000000 + 31/20000000
    --     = 161/20000000
    --     = 8.05·10⁻⁶
    -- ≤ 1/124000 ≈ 8.065·10⁻⁶
    -- (integer margin 36000;
    --  the rational check is 20000000 ≥ 124000·161 = 19964000).
    show (13 / 2000000 : ℝ) + 1 / 2 * (31 / 10000000 : ℝ) ≤ 1 / 124000
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
