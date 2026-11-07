/-
  Candidates/V27.lean — first post-K_max-patch PASS: re-baseline V11's
  `Cr_phi_uzz` proof body onto the truncation-free `round3` oracle suite.

  -- @parent Candidates/V11.lean
  -- @sprint Sprint_Contracts/sprint_033.md

  ## Background — the K_max-truncation regression (PATCH_NOTES.md, 2026-05-03)

  Every numerical oracle that backed V9–V26's `Cr_val` was non-rigorous
  because the underlying `eval_H_eta_at_acb` truncates the φ-series at
  `K_max = 80` with no rigorous tail bound. PATCH_NOTES.md §3's audit
  table re-evaluates each candidate's `Cr_phi_*` formula with the
  truncation-free post-patch oracles and ranks V11 as the structural
  sweet spot: `Cr_patched(V11) = 0.32551` is the lowest patched value
  among V9..V26 except for V14 (0.281), which uses a different oracle
  set (`joint_phi_phip_invD2`) the V11 proof chain doesn't consume.

  V27 reuses V11's exact Lean proof structure (same sink delegation to
  `lemma_5_4_paper_on_domain_phi_uzz`, same six oracle axioms, same
  numerical-witness surface) but retargets the four scalar η-aware
  oracle ceilings to the truncation-free round3 rationalised values:

      Oracle          | V11 (K_max-truncated)    | V27 (round3 truncfree)
      ----------------|--------------------------|------------------------
      M_phi_val       | 239 / 5000 ≈ 0.04780     | 231143 / 10000000 ≈ 0.02311
      M_phi_prime_val | 543 / 10000 ≈ 0.05430    | 905139 / 2500000 ≈ 0.36206
      inv_F_p_z_val   | 2                        | 1424571 / 400000 ≈ 3.56143
      M_pp_val        | 5608 / 100 ≈ 56.08000    | 185260647 / 10000000 ≈ 18.52606

  The four new literals are the rationalised outputs of
  `Numerical_Library.truncfree.round3().as_oracle_result(name,
  safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7)`, verified
  byte-faithful by `Scratch/sprint_033_verify_round3.py` (the
  `DECISION: viable` block in `Scratch/sprint_033_verify_round3.txt`
  records the asserted Fraction equality and the formula value).

  AUDIT-driven score:

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        = M_phi · M_phi_prime · inv_F_p_z²
            + (1/2) · M_pp · inv_F_p_z³ · M_phi²
        = (231143/10⁷) · (905139/2.5·10⁶) · (1424571/4·10⁵)²
            + (1/2) · (185260647/10⁷) · (1424571/4·10⁵)³ · (231143/10⁷)²
        ≈ 0.10615 + 0.22356
        ≈ 0.32970

  Setting `Cr_val := 1/3 ≈ 0.33333` leaves margin
      1/3 − Cr_phi_uzz ≈ 3.63·10⁻³  (≈ +1.09 %)
  against the formula and margin
      1/3 − Cr_patched(V11) ≈ 7.82·10⁻³  (≈ +2.40 %)
  against the round3 audit floor for V11. (V27 reuses V11's
  `Cr_phi_uzz` formula, so its `Cr_patched` is the V11 row of
  `audit_naive_results.json`.)

  Trust base (byte-identical to V11; no new axioms):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper`
      family — same as V11).
    - `Braverman.PaperV0.h_M_oracle` (single-`M` sup bound on
      `Ω(δ, B)`; carried over from V11 byte-identical for parity).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).
    - `Braverman.PaperV0.h_M_phi_oracle` — ‖H_η(w) - H_0(w)‖ ≤ M_phi_val
      on the oracle rectangle (proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` — ‖H_η'(w) - H_0'(w)‖
      ≤ M_phi_prime_val on the oracle rectangle (proposal_001).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` — for every
      `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`.
    - `Braverman.PaperV0.h_M_pp_oracle` (proposal_001) — for every
      `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `‖∂²_z F_p(η, p, w)‖ ≤ M_pp_val`.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.

  AUDIT: Cr_phi_uzz(M_phi, M_phi_prime, inv_F_p_z, M_pp) ≤ Cr_val
         under PATCH_NOTES rules.
  Source chunks: Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json
  Source audit:  Cache/Backups/2026-05-03_subdivision/audit_naive_results.json
  Cr_patched(this candidate) = 0.32551055319967653
    (= V11 row of audit_naive_results.json; same Cr_phi_uzz formula)
  Cr_val = 1/3 ≈ 0.33333  (margin +2.40% over Cr_patched)
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V11 surface, truncation-free literals) -/

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
Set to `231143/10000000 ≈ 0.02311`, the rationalised ceiling of the
truncation-free `compute_M_phi_truncfree_bound(source="round3")` at
`safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7`. -/
def M_phi_val : ℝ := 231143 / 10000000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. Set to `905139/2500000 ≈ 0.36206`, the rationalised ceiling
of `compute_M_phi_prime_truncfree_bound(source="round3")` at the same
rationaliser settings. -/
def M_phi_prime_val : ℝ := 905139 / 2500000

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `1424571/400000 ≈ 3.56143`,
the rationalised ceiling of
`compute_inv_F_p_z_truncfree_bound(source="round3")`. -/
def inv_F_p_z_val : ℝ := 1424571 / 400000

/-- η-aware uniform-in-p upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `185260647/10000000
≈ 18.52606`, the rationalised ceiling of
`compute_M_pp_truncfree_bound(source="round3")`. -/
def M_pp_val : ℝ := 185260647 / 10000000

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/3`) -/

/-- `Cr_val := 1/3`, dominating the literal rational
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val`:
    Cr_phi_uzz ≈ 0.10615 + 0.22356 ≈ 0.32970.
Margin to `Cr_val = 1/3 ≈ 0.33333` is ≈ 3.63·10⁻³ (≈ +1.09 %). -/
def Cr_val : ℝ := 1 / 3

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

/-! ## Section 4: Oracle axioms (V11's six; numerical literals updated) -/

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
Carried over from V11 for parity; the `_phi_uzz` wrapper does not consume
this oracle (it should not appear in the transitive axiom set of the
sink, but it's declared here so the per-candidate audit/log captures
the same numerical-witness surface that V11 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`: `‖H_η(w) - H_0(w)‖ ≤ M_phi_val`
on the oracle rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_truncfree_bound` (round3 source). -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`:
`‖deriv (H_η)(w) - deriv (H_0)(w)‖ ≤ M_phi_prime_val` on the oracle
rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_prime_truncfree_bound` (round3 source). -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-p upper bound on `1/‖∂_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_truncfree_bound` (round3 source). -/
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
`Numerical_Library.compute_M_pp_truncfree_bound` (round3 source). -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V11; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (the
η-aware wrapper introduced in sprint_015), threading the V11 oracle
six-pack with truncation-free numerical literals. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val * p^2`
is then absorbed into the literal `Cr_val * p^2 = (1/3) * p^2` via the
monotonicity step
`Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ 1/3`,
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
    -- LHS ≈ 0.10615 + 0.22356 ≈ 0.32970 ≤ 1/3 ≈ 0.33333
    show 231143 / 10000000 * (905139 / 2500000)
            * ((1424571 : ℝ) / 400000) ^ 2 +
        1 / 2 * (185260647 / 10000000)
            * ((1424571 : ℝ) / 400000) ^ 3
            * (231143 / 10000000) ^ 2 ≤ 1 / 3
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
