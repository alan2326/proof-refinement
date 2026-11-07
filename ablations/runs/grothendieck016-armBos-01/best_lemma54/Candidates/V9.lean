/-
  Candidates/V9.lean — consume η-aware proposal_001 oracles
  (`h_M_phi_oracle`, `h_M_phi_prime_oracle`) to drop `Cr_val` from
  V8's `1132310000` to `5` (a 2.26·10⁸× reduction). The `M_pp` oracle
  is intentionally NOT consumed — at the candidate's parameters, the
  implicit-function chain `M_pp · invFp³` would be worse than the
  retained Cauchy step `‖u_zz‖ ≤ 8R/(1-r)²`.

  -- @parent Candidates/V8.lean
  -- @sprint Sprint_Contracts/sprint_012.md

  The substantive change is the new sink delegation: V9 calls
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi` (added to
  `Proof/Lib/Lemma54_Paper_Main.lean` in this sprint), which uses the
  new `F_inv_p_second_deriv_bound_phi` (added to
  `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`) and the new `Cr_phi`
  formula (added to `Proof/Lib/Lemma54_Paper.lean`):
      Cr_phi r M_phi M_phi_prime R
        := M_phi · M_phi_prime · invFp²
             + (4R/(1-r)²) · M_phi²,    invFp = 2R/(1-r).

  At V9 parameters:
    r_val           = 23/25
    M_phi_val       = 239/5000      (oracle bound; smoke ≈ 0.0476)
    M_phi_prime_val = 543/10000     (oracle bound; smoke ≈ 0.0541)
    R_val_paper r   ≤ 23/20         (already proved as
                                     `R_val_paper_le_twentythree_twentieths`)
  Then
    Cr_phi r M_phi M_phi_prime R ≤ 121203353/32000000 ≈ 3.7876.
  Setting `Cr_val := 5` leaves margin ≈ 1.21 — comfortable for
  `nlinarith` on the literal rational arithmetic.

  Trust base (two new oracles, retains the structural axiom):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper`
      family — same as V8; `F_inv_paper_zero` remains a derived theorem).
    - `Braverman.PaperV0.h_M_oracle` (single-`M` sup bound on
      `Ω(δ, B)`; still threaded through the structural pipeline,
      since the abstract domain `E` is shared with the unchanged
      Step 1/Step 2 plumbing). NOTE: V9 keeps M_val/h_M_oracle
      byte-identical to V8 *only because* the on_domain_phi wrapper
      doesn't actually need them on its proof path; the M_val + M_oracle
      are still declared for parity with V8 / future audits but the
      sink delegates to `_phi`, not `_tight`. They will appear in the
      transitive axiom set only if `lemma_5_4_paper_on_domain_phi`
      transitively depends on them — which it doesn't, by design.
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).
    - `Braverman.PaperV0.h_M_phi_oracle` — ‖H_η(w) - H_0(w)‖ ≤ M_phi_val
      on the oracle rectangle (proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle` — ‖H_η'(w) - H_0'(w)‖
      ≤ M_phi_prime_val on the oracle rectangle (proposal_001).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V8 + the η-aware additions) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V8 byte-identical for parity (and so the runner can
still cross-check on-rectangle precision); the `_phi` wrapper does not
consume `h_M_oracle`. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V8. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V8. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `239/5000 = 0.0478`, the rational ceiling of the certified
`compute_M_phi_bound ≈ 0.0476` at proposal_001 production-grade
precision (`n_per_edge=512, prec=200, K_max=80`). -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. Set to `543/10000 = 0.0543`, the rational ceiling of the
certified `compute_M_phi_prime_bound ≈ 0.0541` at proposal_001
production-grade precision. -/
def M_phi_prime_val : ℝ := 543 / 10000

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

/-! ## Section 2: Score (literal rational `Cr_val = 5`) -/

/-- `Cr_val := 5`, dominating the literal rational
`Cr_phi r_val M_phi_val M_phi_prime_val (R_val_paper r_val)`:
    Cr_phi ≤ 121203353/32000000 ≈ 3.7876
(using `R_val_paper r_val ≤ 23/20`). Margin to `Cr_val = 5` is
≈ 1.21, comfortably above the `nlinarith` tolerance. -/
def Cr_val : ℝ := 5

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25`
    (verbatim from V5/V6/V7/V8; the R axis is not the focus of this sprint). -/

/-- `R_val_paper (23/25) = sinh (49/50) ≤ 23/20`. Same proof as V8. -/
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

/-! ## Section 4: Oracle axioms (runner-witnessed, signatures unchanged) -/

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
Carried over from V8 for parity; the `_phi` wrapper does not consume
this oracle (it should not appear in the transitive axiom set of the
sink, but it's declared here so the per-candidate audit/log captures
the same numerical-witness surface that V8 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`: `‖H_η(w) - H_0(w)‖ ≤ M_phi_val`
on the oracle rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_bound`, which returns a certified arb
ball ≈ 0.0476 at `(n_per_edge=512, prec=200, K_max=80)` —
comfortably below `M_phi_val = 239/5000 = 0.0478`. (Approved as part
of proposal_001.) -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`:
`‖deriv (H_η)(w) - deriv (H_0)(w)‖ ≤ M_phi_prime_val` on the oracle
rectangle. Runner-witnessed by
`Numerical_Library.compute_M_phi_prime_bound`, which returns a
certified arb ball ≈ 0.0541 at `(n_per_edge=512, prec=200, K_max=80)` —
comfortably below `M_phi_prime_val = 543/10000 = 0.0543`. (Approved
as part of proposal_001.) -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V8; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi` (the new
η-aware wrapper introduced in this sprint), threading the two new
proposal_001 oracles `h_M_phi_oracle` and `h_M_phi_prime_oracle`. The
conclusion's bound `Cr_phi r_val M_phi_val M_phi_prime_val
(R_val_paper r_val) * p^2` is then absorbed into the literal
`Cr_val * p^2 = 5 * p^2` via the monotonicity step
`Cr_phi r M_phi M_phi_prime (R_val_paper r) ≤ 5`, justified by
`R_val_paper r ≤ 23/20` plus rational arithmetic on the literal
constants `M_phi_val = 239/5000`, `M_phi_prime_val = 543/10000`. -/
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_prime_val M_phi_val_nn M_phi_prime_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_phi r M_phi M_phi_prime (R_val_paper r) * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  have hR_le :
      Braverman.Paper.R_val_paper Braverman.SearchConfig.r ≤ 23 / 20 :=
    R_val_paper_le_twentythree_twentieths
  have hR_nn :
      (0 : ℝ) ≤ Braverman.Paper.R_val_paper Braverman.SearchConfig.r :=
    Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos
  -- Monotonicity step: `Cr_phi r M_phi M_phi_prime R ≤ Cr_val` for our parameters.
  have h_Cr_le :
      Braverman.Paper.Cr_phi Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)
        ≤ Cr_val := by
    have hR_le' :
        Braverman.Paper.R_val_paper (23 / 25 : ℝ) ≤ 23 / 20 := by
      have := hR_le
      unfold Braverman.SearchConfig.r at this
      exact this
    have hR_nn' :
        (0 : ℝ) ≤ Braverman.Paper.R_val_paper (23 / 25 : ℝ) := by
      have := hR_nn
      unfold Braverman.SearchConfig.r at this
      exact this
    unfold Braverman.Paper.Cr_phi Cr_val M_phi_val M_phi_prime_val
           Braverman.SearchConfig.r
    set R := Braverman.Paper.R_val_paper (23 / 25 : ℝ) with hR_def
    -- The unfold leaves a `let invFp`. Beta-reduce by showing the body explicitly.
    show 239 / 5000 * (543 / 10000) * (2 * R / (1 - 23 / 25)) ^ 2 +
        4 * R / (1 - 23 / 25) ^ 2 * (239 / 5000) ^ 2 ≤ 5
    have h_1m : (1 : ℝ) - 23 / 25 = 2 / 25 := by norm_num
    rw [h_1m]
    -- Clear the divisions by hand. The LHS is:
    --   (239/5000) · (543/10000) · (2R/(2/25))^2
    --     + (4R/(2/25)^2) · (239/5000)^2
    --   = (239 · 543 / 5·10^7) · 625·R^2
    --     + (4R · 625 / 4) · (239^2 / 5000^2)
    --   = (239 · 543 · 625 / 5·10^7) · R^2 + 625 · R · (57121 / 25000000)
    --   = (129777 · 625 / 50000000) · R^2 + (625 · 57121 / 25000000) · R
    --   = (81110625 / 50000000) · R^2 + (35700625 / 25000000) · R
    -- We rewrite the goal in this clean polynomial form, then nlinarith.
    have h_lhs_eq :
        239 / 5000 * (543 / 10000) * (2 * R / (2 / 25)) ^ 2 +
            4 * R / (2 / 25) ^ 2 * (239 / 5000) ^ 2 =
          (81110625 / 50000000) * R ^ 2 + (35700625 / 25000000) * R := by
      field_simp
      ring
    rw [h_lhs_eq]
    -- Goal: (81110625/50000000) R^2 + (35700625/25000000) R ≤ 5
    -- At R = 23/20: 0.027 + 0.001 ... wait let me re-check.
    -- 81110625/50000000 ≈ 1.6222125; · R^2 at R^2 ≤ (23/20)^2 = 529/400 = 1.3225;
    --   gives 1.6222 · 1.3225 ≈ 2.1454.
    -- 35700625/25000000 = 1.42825; · R at R ≤ 23/20 = 1.15;
    --   gives 1.42825 · 1.15 = 1.64249.
    -- Sum ≈ 3.78787 ≤ 5. Margin ≈ 1.21.
    have hR2_le : R ^ 2 ≤ (23 / 20) ^ 2 := by
      have := sq_le_sq' (by linarith [hR_nn'] : -(23/20) ≤ R) hR_le'
      simpa using this
    nlinarith [hR_le', hR_nn', hR2_le, sq_nonneg R]
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val
          (Braverman.Paper.R_val_paper Braverman.SearchConfig.r) * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
