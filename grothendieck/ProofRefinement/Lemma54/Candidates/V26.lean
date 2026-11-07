/-
  Candidates/V26.lean — sprint_031 oracle-resolution-tightening on the
  merged_uderiv oracle: doubles the boundary partition resolution from
  V25's `n_per_edge=262144` to `n_per_edge=524288`, re-runs
  `compute_merged_uderiv_bound`, and rationalises the new (tighter)
  certified `merged_uderiv_val` at the locked rationaliser settings
  (`safety_abs=1e-8, max_denom=10⁷`). The mathematical content is
  byte-identical to V25 — same form-A identity, same merged-numerator
  oracle signature, same proof skeleton — only the *numerical* declared
  values tighten because the per-cell `acb` interval slack on the
  merged-numerator destructive-interference cancellation tightens with
  the finer boundary discretisation.

  -- @parent Candidates/V25.lean
  -- @sprint Sprint_Contracts/sprint_031.md

  Sprint_031 is a regular linear-chain sprint (no wildcard; previous
  wildcard was sprint_030 at V23 → V25, next wildcard is sprint_034).
  Direction: `oracle-resolution-tightening` on the merged_uderiv
  oracle. The no-3-in-a-row rule is satisfied (sprints 028/029/030
  used three different axes [oracle-resolution-tightening on legacy
  joint+uzz, research+proposal, formula-change/merged-numerator];
  sprint_031 returns to oracle-resolution-tightening on the *new*
  merged oracle, which is fresh on this axis).

  Verification probe at `n_per_edge=524288`
  (`Scratch/sprint_031_verify_n524288.txt`) measured:
    - merged_sup = 7.3095e-6  (vs V25's 8.0865e-6 at n=262144)
    - per-doubling absolute drop on merged_sup: 9.6%
    - rationalised at safety_abs=1e-8, max_denom=10⁷: 37/5000000 ≈ 7.40e-6
      (slack ~1.2%)
    - halved: 37/10000000 ≈ 3.70e-6
    - Strictly beats V25's `Cr_val = 1/240000 ≈ 4.167e-6`.

  Note on the planner's `1/280000` target: the projected per-doubling
  decrement (~17%) was higher than the actual measurement (9.6%),
  so the ball value 7.31e-6 sits above the `1/140000 = 7.143e-6`
  threshold required to reach `Cr_val ≤ 1/280000`. The decision-rule
  cond_a is therefore not met, but cond_b — the actual win-over-V25
  criterion — clears cleanly. We commit V26 with the smaller-but-
  robust win at `Cr_val = 1/268000` (1.117× over V25).

  V26's `Cr_val := 1/268000 ≈ 3.731e-6` dominates
  `Cr_phi_uzz_merged merged_uderiv_val = (1/2)·(37/5000000) =
  37/10000000 ≈ 3.700e-6`. The integer dominance check is:
    `37/10000000 ≤ 1/268000  ⇔  37·268000 ≤ 10000000
                            ⇔  9916000 ≤ 10000000` ✓ (margin 84000).

  Win over V25: `(1/240000) / (1/268000) = 268000/240000 ≈ 1.117×`.
  Win over V23: `1.420 × 1.117 ≈ 1.586×`.
  Cumulative: V0 → V26 ≈ `8.196·10¹⁴ / (1/268000) ≈ 2.197·10²⁰×`.

  Trust base (V25's, byte-identical):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V26 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V26 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V26 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V26 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V26 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (carried over
      for parity, NOT consumed by V26 sink).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (carried over for parity,
      NOT consumed by V26 sink).
    - `Braverman.PaperV0.h_merged_uderiv_oracle` (consumed by V26 sink
      as the single direct bound on the exact `|u''|` quotient; same
      axiom signature as V25, only its declared rational tightens).

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
tight oracle rectangle. Carried over from V25 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V25. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V25. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V25: `61/2500 = 0.0244`. NOT consumed by the V26 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V25
for parity; NOT consumed by the V26 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V25 for parity; NOT consumed by the V26 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V25: `15519/10000 = 1.5519`.
NOT consumed by the V26 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
def joint_phi_phip_invD2_val : ℝ := 47 / 10000000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
def uzz_phi_sq_val : ℝ := 3 / 1250000

/-- η-aware uniform-in-p direct upper bound on the *merged-numerator*
analytic quotient `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. By the form-A identity combined
with `u' = -Phi/D`, this quotient equals `‖u''‖` exactly, so the
single oracle replaces V23's triangle-decomposition product
`2·joint + uzz_phi_sq`.

V26 tightens the V25 declaration `41/5000000` to `37/5000000` by
doubling the boundary discretisation `n_per_edge` from 262144 to
524288. The certified arb sup at the new resolution is `≈ 7.310·10⁻⁶`
(vs V25's `≈ 8.087·10⁻⁶` — a 9.6% absolute drop), and its
rationalisation at the locked `safety_abs=1e-8, max_denom=10⁷` is
`37/5000000 = 7.40·10⁻⁶` (slack ~1.2%). Source:
`Numerical_Library.compute_merged_uderiv_bound` with default
n_per_edge=524288.

Consumed by the V26 sink. -/
def merged_uderiv_val : ℝ := 37 / 5000000

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

theorem merged_uderiv_val_pos : 0 < merged_uderiv_val := by
  unfold merged_uderiv_val; norm_num
theorem merged_uderiv_val_nn : 0 ≤ merged_uderiv_val :=
  le_of_lt merged_uderiv_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 1/268000`) -/

/-- `Cr_val := 1/268000`, dominating the literal rational
`Cr_phi_uzz_merged merged_uderiv_val = (1/2) · (37/5000000) =
37/10000000`.

The integer dominance check: `37/10000000 ≤ 1/268000 ⇔
10000000 ≥ 268000·37 = 9916000` ✓ (integer margin 84000;
relative margin `84000/10000000 = 0.84%`), comfortably handled
by `norm_num` for pure rational arithmetic.

Win over V25: `(1/240000) / (1/268000) = 268000/240000 ≈ 1.117×`.
Cumulative win `~2.197·10²⁰×` over V0 (V0 was `≈ 8.196·10¹⁴`,
V26 is `1/268000 ≈ 3.731·10⁻⁶`, ratio `8.196·10¹⁴ / 3.731·10⁻⁶ ≈
2.197·10²⁰`).

Note: `1/268000` is the densest cleanly-margined denominator
under the locked rationaliser settings (`safety_abs=1e-8,
max_denom=10⁷`); larger denominators (e.g. `1/270000`) bring
the relative margin below `0.5%`, which we keep as our cushion
for `norm_num`. -/
def Cr_val : ℝ := 1 / 268000

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

/-- Certified single-`M` sup-norm bound. Carried over from V25 for
parity; not consumed by the V26 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V25 for parity; NOT consumed by the V26 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V25 for parity; NOT consumed by the V26 sink. -/
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
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
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
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`. Carried over from V25 for
parity; NOT consumed by the V26 sink. -/
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

/-- η-aware uniform-in-p direct upper bound on the *merged-numerator*
analytic quotient `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³` for every
`p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`:

  `‖2·Φ·Φ'·D − DD·Φ²‖ ≤ ‖D‖³ · merged_uderiv_val`.

By the form-A identity (`F_inv_p_second_deriv_form_A` in
`Lemma54_Paper_Pderiv_Single.lean`) combined with `u' = -Φ/D`, the
LHS / `‖D‖³` equals `‖u''‖` exactly. Captures the destructive
interference between `2·Φ·Φ'·D` and `DD·Φ²` (which have opposite
signs at our `(η, r)`) inside one acb interval per cell.

Runner-witnessed by `Numerical_Library.compute_merged_uderiv_bound`,
which at sprint_031's bumped default (`n_per_edge=524288`) returns
the certified rational `37/5000000 ≈ 7.40·10⁻⁶`; the actual arb sup
is `≈ 7.310·10⁻⁶` (slack ~1.2%). Same axiom signature as V25 — only
the certified-rational value tightens. Consumed by the V26 sink. -/
axiom h_merged_uderiv_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖2 * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
            * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                - deriv Braverman.H0 w)
            * deriv (Braverman.F_p Braverman.SearchConfig.eta p) w
          - iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w
              * (Braverman.H_eta Braverman.SearchConfig.eta w
                  - Braverman.H0 w) ^ 2‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 3
              * merged_uderiv_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V25; proved by
delegating to
`Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_merged` (the merged-
numerator wrapper introduced in sprint_030), threading the merged
oracle for the exact `|u''|` quotient with the V26-tightened bound. -/
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_merged
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      merged_uderiv_val merged_uderiv_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_merged_uderiv_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step:
  -- `Cr_phi_uzz_merged merged_uderiv_val ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz_merged merged_uderiv_val ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz_merged Cr_val merged_uderiv_val
    -- LHS = (1/2)·(37/5000000) = 37/10000000 ≈ 3.700·10⁻⁶
    -- ≤ 1/268000 ≈ 3.731·10⁻⁶
    -- (integer margin 84000;
    --  the rational check is 10000000 ≥ 268000·37 = 9916000).
    show (1 / 2 : ℝ) * (37 / 5000000 : ℝ) ≤ 1 / 268000
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz_merged merged_uderiv_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
