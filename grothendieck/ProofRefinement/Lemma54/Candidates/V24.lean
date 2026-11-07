/-
  Candidates/V24.lean — linear successor to V23 along the
  `research+proposal-filing` axis. V24 is **byte-identical to V23**
  modulo this header comment block: every numeric literal, every
  oracle declaration, every supporting lemma, and the entire body
  of `lemma_5_4_search` are unchanged. `Cr_val` stays at `1/169000`
  and the score does not move this sprint.

  -- @parent Candidates/V23.lean
  -- @sprint Sprint_Contracts/sprint_029.md

  Sprint_029 is a *research-and-proposal-filing* sprint: it exists to
  keep the loop running per `Bulletin.md` "Keeping the loop running"
  guidance, while gathering numerical data to inform sprint_030's
  mandatory wildcard pivot. No proof body is changed.

  ## Research deliverables (sprint_029)

  Three Python research probes were executed (results live in
  `Scratch/sprint_029_*` and are synthesised in
  `Scratch/sprint_029_research_summary.md`):

    1. **3-way decomposition probe**
       (`Scratch/sprint_029_planner_three_way_decomp.py`):
       Tested whether splitting term-2 of `Cr_phi_uzz_direct_joint2`
       as `|DD · Phi² / D³| ≤ sup(|DD/D|) · sup(|Phi/D|)²` beats the
       joint cubic oracle. Result at n_per_edge=4096: product of
       separate sups = `1.99·10⁻⁴`, **84× larger** than the joint
       ball value `2.37·10⁻⁶`. Verdict: DEAD.

    2. **Merged-numerator probe at high resolution**
       (`Scratch/sprint_029_planner_merged_n65536.py`): Re-tested
       sprint_026's "merged dead" verdict at n ∈ {16384, 32768, 65536}.
       Ratio merged/triangle drops `1.61 → 1.40 → 1.20` monotonically
       (sprint_026's n=8192 measurement was 1.78). Linear extrapolation
       in `log(n)` crosses 1.0 around `n = 2^17 - 2^18`. Verdict:
       INCONCLUSIVE (trending toward viable; one or two more doublings
       could turn this into a sprint_030 win).

    3. **Per-edge sup-dominance probe**
       (`Scratch/sprint_029_planner_per_edge_sup.py`): Recorded the
       per-edge max of joint and uzz quotients separately. Right
       (`Re=+(1-δ)`) and Left (`Re=-(1-δ)`) tie for dominance
       (symmetric in `Re z`); Top (`Im=+B`) is ~30% smaller;
       **Bottom (`Im=-B`) is 10-18× smaller**. Verdict: INCONCLUSIVE
       for a sub-region oracle pivot, but suggests a 25% scan-cost
       optimisation by skipping the Bottom edge.

  ## Proposal_003 (async, filed by Planner)

  The Planner authored `Proposals/proposal_003_wider_analyticity_domain.md`
  in the same invocation as queueing this contract. Status: pending.
  Type: new-axiom. Requests `F_inv_paper_analytic_wider` over
  `disk((3+r)/4)` (vs the existing `disk((1+r)/2)`); approval would
  revive the sprint_013-blocked contour-change axis (Cauchy contour
  radius lift `(1-r)/2 → (3-r)/4`, shrinking every n-th derivative
  bound by `1.5ⁿ`). Direct V23-chain win estimate: `1.0×-1.5×` plus
  structural unblocking. The Generator does not consume this in V24
  — proposal_003 is queued for human review.

  ## Recommended direction for sprint_030 (mandatory wildcard)

  Priority order: (1) `merged-numerator-revive` at `n ∈ {2^17, 2^18}`
  to cross the ratio-1.0 threshold; (2) `oracle-resolution-tightening-n131072`
  (no-3-in-a-row cap reset after sprint_029's research axis);
  (3) `wider-analyticity-domain-pending` if proposal_003 is approved
  by then. 3-way decomposition and sub-region oracle are dead.

  ## Numerical witnesses (unchanged from V23)

  V23's joint oracles, scanned at `n_per_edge=65536` with the
  sprint_026 rationaliser (`safety_abs=1e-8`, `max_denom=10⁷`),
  yielded:

    - joint quotient `‖Phi · Phi'/D²‖`: ball_value `≈ 4.622·10⁻⁶`,
      rationalised `47/10000000 = 4.70·10⁻⁶` (slack 1.70%).
    - uzz quotient   `‖DD · Phi²/D³‖`:  ball_value `≈ 2.368·10⁻⁶`,
      rationalised `3/1250000 = 2.40·10⁻⁶` (slack 1.33%).

  V24 inherits these literals byte-identical.

  ## Triangle bound (unchanged from V23)

    `joint + (1/2)·uzz_phi_sq = 47/10000000 + (1/2)·3/1250000
                              = 47/10000000 + 12/10000000
                              = 59/10000000
                              = 5.90·10⁻⁶`
  is dominated by `Cr_val = 1/169000 ≈ 5.917·10⁻⁶` with integer margin
  `10000000 − 169000·59 = 29000`. Cumulative win `~1.387·10²⁰×` over
  V0 (V0 was `≈ 8.196·10¹⁴`, V24 is `1/169000 ≈ 5.917·10⁻⁶`).

  Trust base (V23's, unchanged):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V24 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V24 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V24 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V24 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V24 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (consumed by V24
      sink for term-1).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (consumed by V24 sink for
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
tight oracle rectangle. Carried over from V22 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V22. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V22. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V22: `61/2500 = 0.0244`. NOT consumed by the V23 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V22
for parity; NOT consumed by the V23 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V22 for parity; NOT consumed by the V23 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V22: `15519/10000 = 1.5519`.
NOT consumed by the V23 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set in V23 to
`47/10000000 = 4.70·10⁻⁶`, the certified rational returned by
`Numerical_Library.compute_joint_phi_phip_invD2_bound` at production
parameters (n_per_edge=65536, prec=200, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 4.622·10⁻⁶` (slack 1.70%).
Consumed by the V23 sink for term-1. -/
def joint_phi_phip_invD2_val : ℝ := 47 / 10000000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Set in V23 to
`3/1250000 = 2.40·10⁻⁶`, the certified rational returned by
`Numerical_Library.compute_uzz_phi_sq_bound` at production parameters
(n_per_edge=65536, prec=200, safety_abs=1e-8, max_denom=10⁷); the
actual arb sup is `≈ 2.368·10⁻⁶` (slack 1.33%). Consumed by the V23
sink for term-2. -/
def uzz_phi_sq_val : ℝ := 3 / 1250000

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/169000`) -/

/-- `Cr_val := 1/169000`, dominating the literal rational
`Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val`:
    LHS = (47/10000000) + (1/2)·(3/1250000)
        = 47/10000000 + 12/10000000
        = 59/10000000
        = 5.90·10⁻⁶.
Margin to `Cr_val = 1/169000 ≈ 5.917·10⁻⁶` is the integer margin
`10000000 − 169000·59 = 10000000 − 9971000 = 29000` (rational margin
`29000/(169000·10⁷) ≈ 1.72·10⁻⁸`), comfortably handled by
`norm_num` for pure rational arithmetic. The mechanical rational
check `1/169000 ≥ 59/10000000 ⇔ 10000000 ≥ 169000·59 = 9971000`.
Cumulative win `~1.387·10²⁰×` over V0 (V0 was `≈ 8.196·10¹⁴`, V23 is
`1/169000 ≈ 5.917·10⁻⁶`, ratio `8.196·10¹⁴ / 5.917·10⁻⁶ ≈ 1.385·10²⁰`). -/
def Cr_val : ℝ := 1 / 169000

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

/-- Certified single-`M` sup-norm bound. Carried over from V22 for
parity; not consumed by the V23 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V22 for
parity; NOT consumed by the V23 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V22 for
parity; NOT consumed by the V23 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V22 for parity; NOT consumed by the V23 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V22 for parity; NOT consumed by the V23 sink. -/
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
V22; consumed by the V23 sink for term-1. The declared bound
`joint_phi_phip_invD2_val = 47/10000000` dominates the certified arb sup
`≈ 4.622·10⁻⁶` at n_per_edge=65536 with safety_abs=1e-8/max_denom=10⁷
(slack 1.70%). -/
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
which returns a certified rational `3/1250000 ≈ 2.40·10⁻⁶` at
production parameters (n_per_edge=65536, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 2.368·10⁻⁶` (slack 1.33%).
Consumed by the V23 sink for term-2. -/
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

/-- **The candidate's sink theorem.** Same shape as V0–V22; proved by
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
    -- LHS = (47/10000000) + (1/2)·(3/1250000)
    --     = 47/10000000 + 12/10000000
    --     = 59/10000000
    --     = 5.90·10⁻⁶
    -- ≤ 1/169000 ≈ 5.917·10⁻⁶
    -- (integer margin 29000;
    --  the rational check is 10000000 ≥ 169000·59 = 9971000).
    show (47 / 10000000 : ℝ) + 1 / 2 * (3 / 1250000 : ℝ) ≤ 1 / 169000
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
