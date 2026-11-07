/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma54Effective.lean — Effective companion of Lemma 5.4 (paper-faithful)

Specializes `Braverman.Paper.lemma_5_4_paper` (the paper-faithful existential
form with the closed-form `Cr_paper r M R = 8·M²·R/(1-r)² · (1+16·R/(1-r)³)`
constant) to a concrete tuple of rationals
`(eta_val, r_val, delta_val, B_val, M_val)` supplied by the certified-arb
oracle. The resulting `Cr_val` is a transparent rational expression, readable
directly from the theorem statement.

The effective companion now factors through a concrete oracle rectangle
`Ω(delta_val, B_val)` rather than the legacy `F_inv_envelope`. This matches
the intended trust boundary: the Python side certifies that exact rectangle,
while Lean only assumes two oracle facts about it:

* the relevant `F_inv_paper` image lands in that domain;
* `M_val` bounds `|H_0|, |H_η|, |H_0'|, |H_η'|` on that domain.

The proof-graph runner re-verifies the currently exposed numerical part
(`M_oracle ≤ M_val`) on every `--all` invocation and refuses to certify a
trajectory in which the bound fails.

The current witness `M_val = 4000` is deliberately round and conservative.
The Python pipeline can tighten it further (e.g. via `compute_M_rigorous`).
-/

import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main

open Complex Set Metric Real

noncomputable section

namespace Braverman.Effective

/-! ## Concrete numerical values -/

/-- Perturbation parameter for the Krivine improvement (Theorem 4.4). -/
def eta_val : ℝ := 1 / 100

/-- Target disk radius (matches `ProofRefinement.Lemma54.Proof.SearchConfig.r`). -/
def r_val : ℝ := 23 / 25

/-- Real-width parameter for the explicit Step 1/Step 2 rectangle
`Ω(delta_val, B_val)`. -/
def delta_val : ℝ := 57 / 1000

/-- Imaginary-height parameter for the explicit Step 1/Step 2 rectangle
`Ω(delta_val, B_val)`. -/
def B_val : ℝ := 293 / 250

/-- Single-`M` sup-norm bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
explicit oracle rectangle. Set to `4000` to dominate the certified
`compute_M_rigorous` output on `Ω(delta_val, B_val)` (≈ 3600 at the current
rectangle); the dominant term is the Cauchy
bound on `|H_η'|` evaluated on the inflated rectangle `Ω(δ - δ/4, B + δ/4)`
divided by `δ/4`. -/
def M_val : ℝ := 4000

/-- `Cr_paper` evaluated at the concrete rationals (the paper-faithful
single-`M` constant). -/
def Cr_val : ℝ :=
  Braverman.Paper.Cr_paper r_val M_val
    (Braverman.Paper.R_val_paper r_val)

/-! ## Positivity / non-negativity facts -/

theorem eta_val_pos : 0 < eta_val := by unfold eta_val; norm_num
theorem r_val_pos : 0 < r_val := by unfold r_val; norm_num
theorem r_val_lt_one : r_val < 1 := by unfold r_val; norm_num
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem delta_val_lt_one : delta_val < 1 := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num
theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos

theorem Cr_val_nn : 0 ≤ Cr_val :=
  Braverman.Paper.Cr_paper_nonneg r_val_lt_one M_val_nn
    (Braverman.Paper.R_val_paper_nonneg r_val_pos)

/-! ## Oracle-backed numerical domain and bounds

`oracle_domain` is the exact rectangle certified by the Step 1 / Step 2
numerics for `(eta_val, r_val)`. The oracle must certify containment of the
`F_inv_paper` image in this set, and the single-`M` sup-norm bound on this
same set.

Substituting a tighter `M_val` preserves the proof; a larger one loosens
`Cr_val`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper eta_val r_val r_val_pos r_val_lt_one),
      ∀ z ∈ Braverman.disk r_val,
        Braverman.Paper.F_inv_paper eta_val r_val r_val_pos r_val_lt_one q z
          ∈ oracle_domain

axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta eta_val w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta eta_val) w‖ ≤ M_val

/-! ## Effective Lemma 5.4 -/

/-- **Effective Lemma 5.4 (paper-faithful).** Specializes `lemma_5_4_paper`
to the concrete rationals `r_val`, `eta_val`, `delta_val`, `B_val`, and
`M_val` from the oracle.
The Taylor remainder bound is `Cr_val · p²` with `Cr_val` the paper's literal
closed-form constant `8·M²·R/(1-r)² · (1+16·R/(1-r)³)`. -/
theorem lemma_5_4_effective :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk r_val,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p eta_val p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z - Braverman.H_eta eta_val (Complex.sin z)) * Complex.cos z)‖
            ≤ Cr_val * p ^ 2 := by
  exact Braverman.Paper.lemma_5_4_paper_on_domain
    eta_val r_val r_val_pos r_val_lt_one
    M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle

end Braverman.Effective
