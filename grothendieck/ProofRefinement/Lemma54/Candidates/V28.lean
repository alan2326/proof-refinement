/-
  Candidates/V28.lean — V14-formula re-baseline onto truncation-free
  oracles: drop V27's `Cr_phi_uzz` four-scalar-product formula in
  favour of V14's `Cr_phi_uzz_direct_joint = joint + (1/2)·u_zz·M_phi²`,
  the structurally tightest `Cr_phi_*` formula at round-3 chunks
  (PATCH_NOTES §3, audit_naive_results.json V14 row).

  -- @parent Candidates/V11.lean
  -- @sprint Sprint_Contracts/sprint_034.md

  V28 is cloned from V27.lean for the proof-scaffolding boilerplate
  (`oracle_domain`, `M_val`, `R_val_paper_le_twentythree_twentieths`,
  the `h_M_oracle` and `h_oracle_domain_contains_image` axioms) but
  swaps the V11/V27 sink delegation
  `lemma_5_4_paper_on_domain_phi_uzz` for V14's
  `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`. The four-scalar
  oracle pack `(M_phi, M_phi_prime, inv_F_p_z, M_pp)` consumed by
  V27 is replaced with the three-oracle pack
  `(M_phi, joint_phi_phip_invD2, u_zz_bound)` consumed by V14, with
  the *literals retargeted to the truncation-free round-3 ceilings*
  (V14's K_max-era literals would all be wrong for the truncfree
  pipeline — `u_zz_bound` jumps from `15519/10000 ≈ 1.55` to
  `8342848479/10000000 ≈ 834.28`).

  ## Background — the K_max-truncation regression (PATCH_NOTES.md, 2026-05-03)

  Every numerical oracle that backed V9–V26's `Cr_val` was
  non-rigorous because the underlying `eval_H_eta_at_acb` truncates
  the φ-series at `K_max = 80` with no rigorous tail bound. PATCH_NOTES
  §3's audit table re-evaluates each candidate's `Cr_phi_*` formula
  with the truncation-free post-patch oracles. V14's formula —
  `joint_phi_phip_invD2 + (1/2)·u_zz_bound·M_phi²` — has the smallest
  `Cr_patched = 0.28103` of any V0..V26 candidate, ~14% below V11's
  `Cr_patched = 0.32551`. V28 takes that structural win as the next
  audit-floor-moving sprint after V27 (which only tightened V11's
  literal against V11's audit floor of 0.3255).

  ## Numerical retargeting (round-3 truncfree rationaliser ceilings)

      Oracle                | V14 (K_max-era)            | V28 (round3 truncfree)
      ----------------------|----------------------------|--------------------------
      M_phi_val             | 61 / 2500 ≈ 0.02440        | 231143 / 10000000 ≈ 0.02311
      joint_phi_phip_invD2_val| 3 / 10000 = 0.00030       | 609061 / 10000000 ≈ 0.06091
      u_zz_bound_val        | 15519 / 10000 ≈ 1.55190    | 8342848479 / 10000000 ≈ 834.28485

  The three new literals are the rationalised outputs of
  `Numerical_Library.truncfree.round3().as_oracle_result(name,
  safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7)`, verified
  byte-faithful by `Scratch/sprint_034_verify_v14.py` (the
  `DECISION: viable` block in `Scratch/sprint_034_verify_v14.txt`
  records the asserted Fraction equality and the formula value).
  Note `M_phi` is the SAME literal as in V27 (same oracle, same
  bundle, same rationaliser settings).

  AUDIT-driven score:

      Cr_phi_uzz_direct_joint r M_phi joint u_zz
        = joint + (1/2) · u_zz · M_phi²
        = 609061/10⁷ + (1/2) · (8342848479/10⁷) · (231143/10⁷)²
        = 567546286918441161071 / 2000000000000000000000
        ≈ 0.283773

  Setting `Cr_val := 2/7 ≈ 0.285714` leaves margin
      2/7 − Cr_phi_uzz_direct_joint
        = 27175991570911872503 / 14000000000000000000000
        ≈ 1.94·10⁻³  (≈ +0.68 %)
  against the formula and margin
      2/7 − Cr_patched(V14) = 2/7 − 0.28102580431097141
        ≈ 4.69·10⁻³  (≈ +1.66 %)
  against the round-3 audit floor for V14. (V28 reuses V14's
  `Cr_phi_uzz_direct_joint` formula, so its `Cr_patched` is the
  V14 row of `audit_naive_results.json`.)

  Reduction over V27: `Cr_val(V27) / Cr_val(V28) = (1/3) / (2/7)
  = 7/6 ≈ 1.167×` (≈ 16.7 % tighter). This is the first post-patch
  sprint that lowers the audit floor (V27 only tightened the literal
  against V11's audit floor of 0.3255; V28 swaps to V14's audit floor
  of 0.28103).

  Trust base (different oracle constellation than V27; no new free-floating axioms):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper`
      family — same as V11/V14/V27).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).
    - `Braverman.PaperV0.h_M_oracle` (single-`M` sup bound on
      `Ω(δ, B)`; carried over from V11 byte-identical for parity;
      not consumed by the V14-formula sink).
    - `Braverman.PaperV0.h_M_phi_oracle` — ‖H_η(w) - H_0(w)‖ ≤ M_phi_val
      on the oracle rectangle (proposal_001; consumed by sink).
    - `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` (sprint_019)
      — for every `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `‖(H_η - H_0)(w) · (H_η' - H_0')(w)‖ ≤ ‖∂_z F_p‖² · joint_val`.
    - `Braverman.PaperV0.h_u_zz_oracle` (sprint_016) — for every
      `p ∈ Ioo 0 pr_paper` and every `w ∈ Ω(δ, B)`,
      `‖∂²_z F_p‖ ≤ ‖∂_z F_p‖³ · u_zz_bound_val`.

  Both `h_joint_phi_phip_invD2_oracle` and `h_u_zz_oracle` are
  registered in `lemma.toml`'s `[[oracles]]` table; sprint_034
  rewires their `oracle_fn` strings to
  `compute_joint_phi_phip_invD2_truncfree_bound` and
  `compute_u_zz_bound_truncfree_bound` respectively (both already
  re-exported through `Numerical_Library/__init__.py`).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.

  AUDIT: Cr_phi_uzz_direct_joint(M_phi, joint_phi_phip_invD2, u_zz_bound)
         ≤ Cr_val under PATCH_NOTES rules.
  Source chunks: Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json
  Source audit:  Cache/Backups/2026-05-03_subdivision/audit_naive_results.json
  Cr_patched(this candidate) = 0.28102580431097141
    (= V14 row of audit_naive_results.json; same Cr_phi_uzz_direct_joint formula)
  Cr_val = 2/7 ≈ 0.28571  (margin +1.66% over Cr_patched)
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (V14 oracle constellation, truncfree literals) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V11/V27 byte-identical for parity (not consumed by
the V14-formula sink). -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Carried over from V27. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Carried over from V27. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `231143/10000000 ≈ 0.02311`, the rationalised ceiling of the
truncation-free `compute_M_phi_truncfree_bound(source="round3")` at
`safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7`. Same literal as V27
(same oracle, same bundle, same rationaliser settings). -/
def M_phi_val : ℝ := 231143 / 10000000

/-- η-aware uniform-in-(p,w) upper bound on the joint analytic quotient
`‖Phi(w) · Phi'(w) / D(p, w)²‖`. Set to `609061/10000000 ≈ 0.06091`,
the rationalised ceiling of
`compute_joint_phi_phip_invD2_truncfree_bound(source="round3")` at
the same rationaliser settings. NEW IN V28 (vs V27); replaces the
four-scalar product `M_phi · M_phi_prime · inv_F_p_z²` with a single
joint sup. -/
def joint_phi_phip_invD2_val : ℝ := 609061 / 10000000

/-- η-aware uniform-in-(p,w) upper bound on `‖∂²_z F_p / (∂_z F_p)³‖
= ‖u_zz‖`. Set to `8342848479/10000000 ≈ 834.28485`, the rationalised
ceiling of `compute_u_zz_bound_truncfree_bound(source="round3")` at
the same rationaliser settings. NEW IN V28 (vs V27); the truncation-
free bound is ≈ 540× larger than V14's K_max-era literal `15519/10000`
because the K_max truncation hid most of the actual `u_zz` magnitude
on the oracle rectangle, but the V14 formula still wins because
`joint`'s ~0.061 dominates the saved term-1 cost. -/
def u_zz_bound_val : ℝ := 8342848479 / 10000000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

theorem M_phi_val_pos : 0 < M_phi_val := by unfold M_phi_val; norm_num
theorem M_phi_val_nn : 0 ≤ M_phi_val := le_of_lt M_phi_val_pos

theorem joint_phi_phip_invD2_val_pos : 0 < joint_phi_phip_invD2_val := by
  unfold joint_phi_phip_invD2_val; norm_num
theorem joint_phi_phip_invD2_val_nn : 0 ≤ joint_phi_phip_invD2_val :=
  le_of_lt joint_phi_phip_invD2_val_pos

theorem u_zz_bound_val_pos : 0 < u_zz_bound_val := by
  unfold u_zz_bound_val; norm_num
theorem u_zz_bound_val_nn : 0 ≤ u_zz_bound_val :=
  le_of_lt u_zz_bound_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 2/7`) -/

/-- `Cr_val := 2/7`, dominating the literal rational
`Cr_phi_uzz_direct_joint r_val M_phi joint u_zz`:
    LHS = 609061/10⁷ + (1/2)·(8342848479/10⁷)·(231143/10⁷)²
        = 567546286918441161071 / 2·10²¹
        ≈ 0.283773.
Margin to `Cr_val = 2/7 ≈ 0.285714` is ≈ 1.94·10⁻³ (≈ +0.68 % of RHS),
comfortably handled by `norm_num` for pure rational arithmetic. -/
def Cr_val : ℝ := 2 / 7

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ### Helper: a tight rational upper bound on `R_val_paper` at `r = 23/25`

Even though `Cr_phi_uzz_direct_joint` does NOT depend on `R`, the proof
body of `lemma_5_4_paper_on_domain_phi_uzz_direct_joint` still routes
through `F_p_deriv_lower_bound_at_F_inv` (Step 3, Cauchy first-deriv on
the F-side) to establish `D ≠ 0`, and so `R_val_paper r` is implicit
in the proof; this helper is unused at the candidate level (the closing
`norm_num` does not consume it), but kept for future-proofing in case
a downstream change reintroduces R into `Cr_phi_uzz_direct_joint`. -/
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

/-! ## Section 4: Oracle axioms (V14's three; literals retargeted to round-3 truncfree) -/

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
Carried over from V11/V27 for parity; the
`_phi_uzz_direct_joint` wrapper does not consume this oracle (it
should not appear in the transitive axiom set of the sink, but it's
declared here so the per-candidate audit/log captures the same
numerical-witness surface that V14 had). -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`:
`‖H_η(w) - H_0(w)‖ ≤ M_phi_val` on the oracle rectangle.
Runner-witnessed by
`Numerical_Library.compute_M_phi_truncfree_bound` (round3 source).
Consumed by the V14-formula sink for the term-2 chunk. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware uniform-in-p direct upper bound on the *joint* analytic
quotient `‖Phi(w) · Phi'(w) / D(p, w)²‖` over `(p, w) ∈
[0, pr_paper] × Ω(δ_val, B_val)`. Signature matches
`lemma_5_4_paper_on_domain_phi_uzz_direct_joint`'s
`h_joint_oracle_dom` hypothesis verbatim
(`Proof/Lib/Lemma54_Paper_Main.lean:1005-1008`). Runner-witnessed
by `Numerical_Library.compute_joint_phi_phip_invD2_truncfree_bound`
(round3 source). -/
axiom h_joint_phi_phip_invD2_oracle :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖(Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
            * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                - deriv Braverman.H0 w)‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta q) w‖ ^ 2
              * joint_phi_phip_invD2_val

/-- η-aware uniform-in-p direct upper bound on `‖DD‖/‖D‖³`. Signature
matches `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`'s
`h_u_zz_oracle_dom` hypothesis verbatim
(`Proof/Lib/Lemma54_Paper_Main.lean:1009-1012`). Runner-witnessed
by `Numerical_Library.compute_u_zz_bound_truncfree_bound`
(round3 source). -/
axiom h_u_zz_oracle :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta q) w‖
          ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta q) w‖ ^ 3
              * u_zz_bound_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V27; proved by
delegating to
`Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint` (the
joint-formula wrapper introduced in sprint_019), threading the
joint oracle for term-1 and `h_u_zz_oracle`/`h_M_phi_oracle` for
term-2. The conclusion's bound
`Cr_phi_uzz_direct_joint r_val M_phi_val joint_val u_zz_bound_val * p^2`
is then absorbed into the literal `Cr_val * p^2 = (2/7) * p^2` via
the monotonicity step
`Cr_phi_uzz_direct_joint r M_phi joint u_zz ≤ 2/7`,
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
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_val_nn
      joint_phi_phip_invD2_val joint_phi_phip_invD2_val_nn
      u_zz_bound_val u_zz_bound_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_joint_phi_phip_invD2_oracle h_u_zz_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step:
  -- `Cr_phi_uzz_direct_joint r M_phi joint u_zz ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz_direct_joint Braverman.SearchConfig.r
          M_phi_val joint_phi_phip_invD2_val u_zz_bound_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz_direct_joint Cr_val M_phi_val
           joint_phi_phip_invD2_val u_zz_bound_val
    -- LHS = 609061/10⁷ + (1/2)·(8342848479/10⁷)·(231143/10⁷)²
    --     = 567546286918441161071 / 2·10²¹
    --     ≈ 0.283773
    -- ≤ 2/7 ≈ 0.285714  (margin ≈ 1.94·10⁻³, +0.68% of RHS).
    show (609061 / 10000000 : ℝ)
            + 1 / 2 * (8342848479 / 10000000)
                * ((231143 : ℝ) / 10000000) ^ 2 ≤ 2 / 7
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz_direct_joint Braverman.SearchConfig.r
          M_phi_val joint_phi_phip_invD2_val u_zz_bound_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
