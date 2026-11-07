/-
  Candidates/V11.lean — consume the proposal_001-approved `h_M_pp_oracle`
  (registered in `lemma.toml` since proposal_001 but unused in V9/V10) to
  replace V10's recentred-Cauchy `‖u_zz‖ ≤ 8R/(1-r)²` step with an
  aux-z-identity-driven `‖u_zz‖ ≤ M_pp · inv_F_p_z³` bound, dropping
  `Cr_val` from V10's `2` to `1` (a 2× reduction).

  -- @parent Candidates/V10.lean
  -- @sprint Sprint_Contracts/sprint_015.md

  The substantive change is the new sink delegation: V11 calls
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (added to
  `Proof/Lib/Lemma54_Paper_Main.lean` in this sprint), which uses the new
  `F_inv_p_second_deriv_bound_phi_uzz` (added to
  `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`) and the new `Cr_phi_uzz`
  formula (added to `Proof/Lib/Lemma54_Paper.lean`):
      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  At V11 parameters (same as V10 + the new M_pp):
    r_val           = 23/25
    M_phi_val       = 239/5000
    M_phi_prime_val = 543/10000
    inv_F_p_z_val   = 2
    M_pp_val        = 5608/100      (NEW; certified ≈ 35048/625 ≈ 56.077)
  Then
    Cr_phi_uzz r_val M_phi M_phi_prime inv_F_p_z M_pp
      ≤ (239/5000)·(543/10000)·4
        + (1/2)·(5608/100)·8·(239/5000)²
      ≈ 0.0104 + 0.5126 ≈ 0.5230.
  Setting `Cr_val := 1` leaves margin ≈ 0.477 — comfortable for
  `nlinarith` on the literal rational arithmetic.

  The key mathematical insight is the auxiliary z-identity
  `DD · h² + D · u_zz = 0` (already proved in
  `Lemma54_Paper_Pderiv_Single.lean` as `F_inv_aux_z_identity`), which
  yields
      ‖u_zz‖ = ‖DD‖ · ‖h‖² / ‖D‖ = ‖DD‖ · (1/‖D‖)³
             ≤ M_pp · inv_F_p_z³
  via the certified bounds `‖DD‖ ≤ M_pp` and `1/‖D‖ ≤ inv_F_p_z`. At the
  V10 parameters this gives `‖u_zz‖ ≤ 56.08 · 8 = 448.6`, vs the paper
  Cauchy `8R/(1-r)² ≈ 1393` — a 3.1× tightening of the dominant term-2
  coefficient.

  Trust base (one new oracle on top of V10's six):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper`
      family — same as V10).
    - `Braverman.PaperV0.h_M_oracle` (single-`M` sup bound on
      `Ω(δ, B)`; carried over from V10 byte-identical for parity).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).
    - `Braverman.PaperV0.h_M_phi_oracle` — ‖H_η(w) - H_0(w)‖ ≤ M_phi_val
      on the oracle rectangle (proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` — ‖H_η'(w) - H_0'(w)‖
      ≤ M_phi_prime_val on the oracle rectangle (proposal_001).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` — for every
      `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`.
    - `Braverman.PaperV0.h_M_pp_oracle` (NEW; was registered in
      `lemma.toml` since proposal_001 but unused in V9/V10) — for every
      `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `‖∂²_z F_p(η, p, w)‖ ≤ M_pp_val`. Runner-witnessed by
      `Numerical_Library.compute_M_pp_bound`, which returns a certified
      rational `35048/625 ≈ 56.077`, comfortably below
      `M_pp_val := 5608/100 = 56.08`.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V10 + the M_pp addition) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V10 byte-identical for parity. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V10. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V10. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `239/5000 = 0.0478`, the rational ceiling of the certified
`compute_M_phi_bound ≈ 0.0476` at proposal_001 production-grade
precision. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. Set to `543/10000 = 0.0543`, the rational ceiling of the
certified `compute_M_phi_prime_bound ≈ 0.0541` at proposal_001
production-grade precision. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `2`, the integer ceiling
of the certified `compute_inv_F_p_z_bound ≈ 1.7035`. -/
def inv_F_p_z_val : ℝ := 2

/-- η-aware uniform-in-p upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `5608/100 = 56.08`, the
rational ceiling of the certified `compute_M_pp_bound = 35048/625
≈ 56.077` at production-grade precision (the arb pipeline returns a
certified ball ≈ [56.0207 ± 2.6·10⁻¹⁹]). -/
def M_pp_val : ℝ := 5608 / 100

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

theorem M_pp_val_pos : 0 < M_pp_val := by unfold M_pp_val; norm_num
theorem M_pp_val_nn : 0 ≤ M_pp_val := le_of_lt M_pp_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 1`) -/

/-- `Cr_val := 1`, dominating the literal rational
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val`:
    Cr_phi_uzz ≤ 0.0104 + 0.5126 ≈ 0.5230.
Margin to `Cr_val = 1` is ≈ 0.477, comfortably above the `nlinarith`
tolerance. -/
def Cr_val : ℝ := 1

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25`

Even though `Cr_phi_uzz` does NOT depend on `R`, the proof body of
`lemma_5_4_paper_on_domain_phi_uzz` still routes through
`F_p_deriv_lower_bound_at_F_inv` (Step 3, Cauchy first-deriv on the
F-side) to establish `D ≠ 0`, and so `R_val_paper r` is implicit in the
proof; this helper is unused at the candidate level (the closing
`nlinarith` does not consume it), but kept for future-proofing in case
a downstream change reintroduces R into `Cr_phi_uzz`. -/
theorem R_val_paper_le_twentythree_twentieths :
    Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 23 / 20 := by
  unfold Braverman.Paper.R_val_paper Braverman.Paper.r2 Braverman.SearchConfig.r
  have h_arg : (3 + (23 : ℝ) / 25) / 4 = 49 / 50 := by norm_num
  rw [h_arg]
  have h_sinh : Real.sinh (49 / 50 : ℝ) =
      (Real.exp (49 / 50) - Real.exp (-(49 / 50))) / 2 := Real.sinh_eq _
  rw [h_sinh]
  have hx_nn : (0 : ℝ) ≤ 49 / 50 := by norm_num
  have hx_le_one : (49 : ℝ) / 50 ≤ 1 := by norm_num
  have h_upper :
      Real.exp (49 / 50 : ℝ) ≤
        (Finset.range 10).sum (fun m => (49 / 50 : ℝ) ^ m / m.factorial)
          + (49 / 50 : ℝ) ^ 10 * (10 + 1 : ℝ) / ((Nat.factorial 10 : ℝ) * 10) :=
    Real.exp_bound' hx_nn hx_le_one (by decide : 0 < 10)
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
  have h_lower : Real.exp (-(49 / 50 : ℝ)) ≥
      (Finset.range 10).sum (fun m => (-(49 / 50) : ℝ) ^ m / m.factorial)
        - (49 / 50 : ℝ) ^ 10 *
            (Nat.succ 10 / ((Nat.factorial 10 : ℝ) * 10)) := by
    have := abs_sub_le_iff.mp h_bound_neg
    linarith [this.1, this.2]
  rw [h_S_minus] at h_lower
  have h_fact : (Nat.factorial 10 : ℝ) = 3628800 := by simp [Nat.factorial]
  rw [h_fact] at h_upper
  have h_lower' : Real.exp (-(49 / 50 : ℝ)) ≥
      38000227837801227143 / 101250000000000000000
        - (49 / 50 : ℝ) ^ 10 * (11 / (3628800 * 10)) := by
    have hsucc : (Nat.succ 10 : ℝ) = 11 := by norm_num
    rw [hsucc, h_fact] at h_lower
    exact h_lower
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [h_upper, h_lower']

/-! ## Section 3: Oracle rectangle (the M-bound domain, δ pushed to floor) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed; V10's six + the new
                  `h_M_pp_oracle`) -/

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
|H_η'| ≤ M_val` on the tight rectangle `Ω(1635/10000, 1115/1000)`.
Carried over from V10 for parity; the `_phi_uzz` wrapper does not consume
this oracle (it should not appear in the transitive axiom set of the
sink, but it's declared here so the per-candidate audit/log captures
the same numerical-witness surface that V10 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`: `‖H_η(w) - H_0(w)‖ ≤ M_phi_val`
on the oracle rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_bound`. (Approved as part of
proposal_001.) -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`:
`‖deriv (H_η)(w) - deriv (H_0)(w)‖ ≤ M_phi_prime_val` on the oracle
rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_prime_bound`. (Approved as part of
proposal_001.) -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound`. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-p upper bound on `‖∂²_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`‖∂²_z F_p(η, p, w)‖ ≤ M_pp_val`. Runner-witnessed by
`Numerical_Library.compute_M_pp_bound`, which returns a certified
rational `35048/625 ≈ 56.077` — comfortably below
`M_pp_val := 5608/100 = 56.08`.

This axiom was registered in `lemma.toml`'s `[[oracles]]` table as part
of proposal_001 (alongside `h_M_phi_oracle` and
`h_M_phi_prime_oracle`) but was deliberately UNUSED in V9/V10 because
at the time `inv_F_p_z` was still 28.75 (paper Cauchy), making
`M_pp · inv_F_p_z³ ≫ 8R/(1-r)²`. With V10's
`inv_F_p_z_val = 2`, the inequality flips:
`M_pp · 8 ≈ 449 < 1393 ≈ 8R/(1-r)²`, so the M_pp oracle now becomes
the better bound on `‖u_zz‖`. -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V10; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (the
new η-aware wrapper introduced in this sprint), threading the new
`h_M_pp_oracle` together with the V10 oracles. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val * p^2`
is then absorbed into the literal `Cr_val * p^2 = 1 * p^2` via the
monotonicity step
`Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ 1`,
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_prime_val M_phi_val_nn M_phi_prime_val_nn
      inv_F_p_z_val inv_F_p_z_val_nn
      M_pp_val M_pp_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle h_inv_F_p_z_oracle h_M_pp_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_val
    -- LHS = (239/5000)·(543/10000)·4 + (1/2)·(5608/100)·8·(239/5000)²
    --     = 519108/50000000 + (5608·8/200)·(57121/25000000)
    --     = 519108/50000000 + (44864/200)·(57121/25000000)
    --     ≈ 0.01038 + 0.51257
    --     ≈ 0.5230 ≤ 1
    show 239 / 5000 * (543 / 10000) * (2 : ℝ) ^ 2 +
        1 / 2 * (5608 / 100) * (2 : ℝ) ^ 3 * (239 / 5000) ^ 2 ≤ 1
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
