/-
  Candidates/V25.lean — wildcard structural pivot from V23 along the
  `formula-change: merged-numerator inline oracle` axis: replace V23's
  triangle-decomposition `2·joint_phi_phip_invD2 + uzz_phi_sq` active
  bound on `‖u''‖` with a single merged oracle on the *exact* `|u''|`
  quotient `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³`. By the form-A identity
  combined with `u' = -Phi/D`, this quotient equals `‖u''‖` exactly,
  capturing the destructive interference between the two summands
  (which have opposite signs at our `(η, r) = (1/100, 23/25)`) inside
  one acb interval per cell — savings the triangle bound discards.

  -- @parent Candidates/V23.lean
  -- @sprint Sprint_Contracts/sprint_030.md

  Sprint_030 is the mandatory wildcard per the 4-sprint cadence
  (sprint_026 was the previous wildcard at V18 → V21). V24 was a
  research-only sprint that was byte-identical to V23, so V23 is the
  latest-content predecessor. The mechanism here is *structural*: the
  triangle inequality on the merged numerator
  `2·Phi·Phi'·D − DD·Phi²` (a difference, not a sum, because
  `u' = -Phi/D`) gives `‖u''‖ ≤ 2·‖Phi·Phi'/D²‖ + ‖DD·Phi²/D³‖ =
  2·joint + uzz_phi_sq` — strictly looser than the merged sup
  `‖2·Phi·Phi'·D − DD·Phi²‖/‖D‖³` whenever the two summands cancel
  pointwise. At our (η, r), they do.

  The Generator's verification probe at `n_per_edge=262144`
  (Scratch/sprint_030_verify_n262144.txt) measured:
    - merged_sup ≈ 8.0865e-6
    - naive_sum  ≈ 9.2851e-6 (= 2·joint + uzz_phi_sq at the same resolution)
    - ratio = 0.870917 < 1.0 — viable.

  The new oracle `compute_merged_uderiv_bound` returns rational
  `41/5000000 ≈ 8.20e-6` at `n_per_edge=262144, safety_abs=1e-8,
  max_denom=10⁷` (slack ~1.4%). Halved this is `41/10000000 ≈ 4.10e-6`,
  comfortably below V23's `Cr_val = 1/169000 ≈ 5.917e-6`.

  V25's `Cr_val := 1/240000 ≈ 4.167e-6` dominates
  `Cr_phi_uzz_merged merged_uderiv_val = (1/2)·(41/5000000) =
  41/10000000`. The integer dominance check is:
    `41/10000000 ≤ 1/240000  ⇔  41·240000 ≤ 10000000
                            ⇔  9840000 ≤ 10000000` ✓ (margin 160000).

  Win over V23: `(1/169000) / (1/240000) = 240000/169000 ≈ 1.420×`.
  Cumulative `8.196·10¹⁴ / (1/240000) ≈ 1.967·10²⁰×` over V0.

  Trust base (V23's, with one new oracle):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`.
    - `Braverman.PaperV0.h_M_oracle` (carried over for parity, NOT
      consumed by V25 sink).
    - `Braverman.PaperV0.h_M_phi_oracle` (carried over for parity, NOT
      consumed by V25 sink).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` (carried over for parity,
      NOT consumed by V25 sink).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (carried over for parity,
      NOT consumed by V25 sink).
    - `Braverman.PaperV0.h_u_zz_oracle` (carried over for parity, NOT
      consumed by V25 sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (carried over
      for parity, NOT consumed by V25 sink).
    - `Braverman.PaperV0.h_uzz_phi_sq_oracle` (carried over for parity,
      NOT consumed by V25 sink).
    - `Braverman.PaperV0.h_merged_uderiv_oracle` (NEW; consumed by V25
      sink as the single direct bound on the exact `|u''|` quotient).

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
tight oracle rectangle. Carried over from V23 byte-identical. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V23. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V23. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Carried over from V23: `61/2500 = 0.0244`. NOT consumed by the V25 sink. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖`. Carried over from V23
for parity; NOT consumed by the V25 sink. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V23 for parity; NOT consumed by the V25 sink. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-p direct upper bound on `‖∂²_z F_p / (∂_z F_p)³‖`,
equivalently `‖u_zz‖`. Carried over from V23: `15519/10000 = 1.5519`.
NOT consumed by the V25 sink. -/
def u_zz_bound_val : ℝ := 15519 / 10000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
def joint_phi_phip_invD2_val : ℝ := 47 / 10000000

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
def uzz_phi_sq_val : ℝ := 3 / 1250000

/-- η-aware uniform-in-p direct upper bound on the *merged-numerator*
analytic quotient `‖2·Phi·Phi'·D − DD·Phi²‖ / ‖D‖³` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. By the form-A identity combined
with `u' = -Phi/D`, this quotient equals `‖u''‖` exactly, so the
single oracle replaces V23's triangle-decomposition product
`2·joint + uzz_phi_sq`.

Set in V25 to `41/5000000 = 8.20·10⁻⁶`, the certified rational
returned by `Numerical_Library.compute_merged_uderiv_bound` at
production parameters (n_per_edge=262144, prec=200, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 8.087·10⁻⁶` (slack ~1.4%).

Consumed by the V25 sink. -/
def merged_uderiv_val : ℝ := 41 / 5000000

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/240000`) -/

/-- `Cr_val := 1/240000`, dominating the literal rational
`Cr_phi_uzz_merged merged_uderiv_val = (1/2) · (41/5000000) =
41/10000000`.

Margin to `Cr_val = 1/240000 ≈ 4.167·10⁻⁶` is the integer margin
`10000000 − 240000·41 = 10000000 − 9840000 = 160000` (rational margin
`160000/(240000·10⁷) ≈ 6.67·10⁻⁸`), comfortably handled by `norm_num`
for pure rational arithmetic. The mechanical rational check
`1/240000 ≥ 41/10000000 ⇔ 10000000 ≥ 240000·41 = 9840000`.

Win over V23: `(1/169000) / (1/240000) = 240000/169000 ≈ 1.420×`.
Cumulative win `~1.967·10²⁰×` over V0 (V0 was `≈ 8.196·10¹⁴`, V25 is
`1/240000 ≈ 4.167·10⁻⁶`, ratio `8.196·10¹⁴ / 4.167·10⁻⁶ ≈
1.967·10²⁰`). -/
def Cr_val : ℝ := 1 / 240000

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

/-- Certified single-`M` sup-norm bound. Carried over from V23 for
parity; not consumed by the V25 sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`. Carried
over from V23 for parity; NOT consumed by the V25 sink. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Carried
over from V23 for parity; NOT consumed by the V25 sink. -/
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
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
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
quotient `‖DD(p, w) · Phi(w)² / D(p, w)³‖`. Carried over from V23 for
parity; NOT consumed by the V25 sink. -/
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
which returns the certified rational `41/5000000 ≈ 8.20·10⁻⁶` at
production parameters (n_per_edge=262144, safety_abs=1e-8,
max_denom=10⁷); the actual arb sup is `≈ 8.087·10⁻⁶` (slack ~1.4%).
Consumed by the V25 sink. -/
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

/-- **The candidate's sink theorem.** Same shape as V0–V23; proved by
delegating to
`Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_merged` (the merged-
numerator wrapper introduced in sprint_030), threading the new merged
oracle for the exact `|u''|` quotient. -/
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
    -- LHS = (1/2)·(41/5000000) = 41/10000000 = 4.10·10⁻⁶
    -- ≤ 1/240000 ≈ 4.167·10⁻⁶
    -- (integer margin 160000;
    --  the rational check is 10000000 ≥ 240000·41 = 9840000).
    show (1 / 2 : ℝ) * (41 / 5000000 : ℝ) ≤ 1 / 240000
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz_merged merged_uderiv_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
