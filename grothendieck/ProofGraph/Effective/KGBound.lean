/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# KGBound.lean — Effective KG < Krivine bound

Sink of the proof graph. Defines a concrete `KG_upper_val := π / (2 · γ_val)`
where `γ_val` is the witness extracted from `theorem_5_1` (effective form),
and proves both:

  * `KG_upper_val < KrivineBound` — strict improvement over Krivine,
  * `∃ K = KG_upper_val, KG_upper_val satisfies the Grothendieck inequality`.

The proof routes through `Braverman.theorem_1_1`. As a consequence,
`KG_lt_Krivine_effective` inherits `sorryAx` from `Rounding.lean`, where
two non-quantitative steps in the rounding scheme remain unfinished. This
is the documented limitation of the current LeanProof; see
`LeanProof/Rounding.lean:160,189`. All quantitative content (the explicit
constant `Cr_paper`, the strict inequality `γ_val > log(1+√2)`, the chain
to a numerical KG bound) is `sorry`-free.
-/

import LeanProof.MainTheorem
import ProofGraph.Effective.Theorem51Effective

open Complex

noncomputable section

namespace Braverman.Effective

/-! ## The effective Grothendieck-constant upper bound -/

/-- The concrete upper bound on `KG`: `π / (2 · gamma_explicit)`, where
`gamma_explicit` is the Theorem 5.1 witness. This is the analogue of
Krivine's `π / (2 · log(1+√2))` with the strictly improved
`gamma_explicit > log(1+√2)` in the denominator. -/
def KG_upper_val : ℝ := Real.pi / (2 * gamma_explicit)

theorem KG_upper_val_pos : 0 < KG_upper_val := by
  unfold KG_upper_val
  have hγ : 0 < gamma_explicit := gamma_explicit_pos
  positivity

/-! ## KG_upper_val < KrivineBound

This is the strict-improvement step. It uses only the inequality
`gamma_explicit > log(1+√2)` (no oracle axioms beyond what `theorem_5_1`
already needed). -/

theorem KG_upper_val_lt_krivine : KG_upper_val < Braverman.KrivineBound := by
  unfold KG_upper_val Braverman.KrivineBound
  have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) :=
    Braverman.log_one_add_sqrt_two_pos
  have hγ_lower : Real.log (1 + Real.sqrt 2) < gamma_explicit := gamma_explicit_gt_log
  apply div_lt_div_of_pos_left Real.pi_pos
  · positivity
  · linarith

/-! ## Concrete rational-sandwich KG bound

The sandwich `gamma_lo_rat < gamma_explicit < gamma_hi_rat` from
`Theorem51Effective.lean` lets us replace the transcendental denominator
`gamma_explicit` by the rational lower endpoint `gamma_lo_rat`, giving a
concrete rational-derived upper bound on `KG`. -/

/-- Concrete rational-derived upper bound on `KG`: `π / (2 · gamma_lo_rat)`.
This is the certificate-side numerical witness behind the explicit
Grothendieck constant bound. -/
def KG_upper_val_rat : ℝ := Real.pi / (2 * (gamma_lo_rat : ℝ))

theorem KG_upper_val_lt_rat_bound : KG_upper_val < KG_upper_val_rat := by
  unfold KG_upper_val KG_upper_val_rat
  have hγ_gt_lo : ((gamma_lo_rat : ℚ) : ℝ) < gamma_explicit :=
    gamma_explicit_gt_lo_rat
  have h_lo_pos : (0 : ℝ) < ((gamma_lo_rat : ℚ) : ℝ) := by
    show (0 : ℝ) < (gamma_lo_rat : ℝ)
    unfold gamma_lo_rat
    push_cast
    norm_num
  apply div_lt_div_of_pos_left Real.pi_pos
  · linarith
  · linarith

/-! ## Effective KG_lt_Krivine

We re-derive `Braverman.theorem_1_1` (which gives an existential over `K`)
into a packaged form using `KG_upper_val` as the named witness. -/

/-- **Effective Theorem 1.1.** The specific upper bound `KG_upper_val =
π / (2 · gamma_explicit)` strictly improves over Krivine's
`π / (2 · log(1+√2))` and over the rational sandwich's
`π / (2 · gamma_lo_rat)`, and satisfies the Grothendieck inequality. -/
theorem KG_lt_Krivine_effective :
    KG_upper_val < Braverman.KrivineBound ∧
    KG_upper_val < KG_upper_val_rat ∧
    Braverman.GrothendieckIneq KG_upper_val := by
  refine ⟨KG_upper_val_lt_krivine, KG_upper_val_lt_rat_bound, ?_⟩
  -- Apply grothendieck_ineq_of_rounding using gamma_explicit and Theorem 5.1's witnesses.
  obtain ⟨F_inv, hFa, hFi, hFS, hSum⟩ :=
    theorem_5_1_effective.2.2.2.2
  exact Braverman.grothendieck_ineq_of_rounding
    gamma_explicit gamma_explicit_pos gamma_explicit_lt_one
    eta_val_5_1 p_val_5_1 eta_val_5_1_pos p_val_5_1_pos
    F_inv hFa hFi hFS hSum

end Braverman.Effective
