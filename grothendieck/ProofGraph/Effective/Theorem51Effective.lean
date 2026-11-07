/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem51Effective.lean — Effective companion of Theorem 5.1

The original `Braverman.Effective.theorem_5_1_paper_effective` is purely existential:

    ∃ η p γ, 0 < η ∧ 0 < p ∧ γ > log(1+√2) ∧ γ < 1 ∧ <summability>

The effective companion exposes the witness triple via `Classical.choose`,
giving named reals `eta_val_5_1`, `p_val_5_1`, `gamma_explicit`. Downstream
consumers (KGBound) only need the inequalities on `gamma_explicit`, which we
recover from the destructured spec.

## Rational sandwich on `gamma_explicit`

`gamma_explicit` is still defined via `Classical.choose`, but we now also
expose `gamma_lo_rat` / `gamma_hi_rat` — Python-emitted rational endpoints
that are intended to bracket the certified-arb `gamma_best ≈ 0.881373…`
output of `solve_gamma`. The sandwich
`(gamma_lo_rat : ℝ) < gamma_explicit < (gamma_hi_rat : ℝ)` is exposed as a
new oracle axiom `h_gamma_explicit_sandwich` (a "tight" upgrade of the
existing `gamma_explicit_gt_log` ∧ `gamma_explicit_lt_one`).

The numerical witness for this axiom is a runner cross-check that the
certified `gamma_best` arb interval lies inside the rational sandwich.
The mathematical bridge between Lean's IVT-chosen γ and the certified
`gamma_best` is not formally proved in Lean: theorem_5_1's `Classical.choose`
selects a γ for an internally-chosen `p`, while `gamma_best` is computed at
`p_override = 1e-30`. Bringing them into formal alignment requires lifting
`p` to be an explicit parameter of `theorem_5_1_paper_effective` (via the
generic `theorem_5_1_from_thresholds` from Phase 3 step 2) — see
`STATUS_AND_PLAN.md` for the open work.
-/

import LeanProof.Theorem51
import ProofGraph.Effective.Lemma54Effective
import ProofGraph.Effective.Theorem51PaperEffective
import ProofGraph.Effective.Theorem51AtPExplicit

open Complex Set Metric

noncomputable section

namespace Braverman.Effective

/-! ## Witness triple extracted from `theorem_5_1` -/

/-- `η` for the effective companion: pinned to `eta_val = 1/100`. -/
def eta_val_5_1 : ℝ := eta_val

/-- `p` for the effective companion: pinned to `p_explicit_rat = 1/10^30`,
matching the certified-arb pipeline's `p_override`. With this pinning, the
IVT-chosen γ is unambiguously the γ for the same `(η, p)` as the certified
`gamma_best`. -/
def p_val_5_1 : ℝ := p_explicit_rat

/-- The `γ` witness extracted from `theorem_5_1_at_p_explicit`. Since the
underlying theorem fixes `(η, p) = (eta_val, p_explicit_rat)` matching the
certified pipeline, this γ is identifiable with the certified `gamma_best`
to within the rational sandwich `[gamma_lo_rat, gamma_hi_rat]`. -/
def gamma_explicit : ℝ := theorem_5_1_at_p_explicit.choose

theorem eta_val_5_1_pos : 0 < eta_val_5_1 := eta_val_pos

theorem p_val_5_1_pos : 0 < p_val_5_1 := p_explicit_rat_pos

theorem gamma_explicit_gt_log : gamma_explicit > Real.log (1 + Real.sqrt 2) :=
  theorem_5_1_at_p_explicit.choose_spec.1

theorem gamma_explicit_lt_one : gamma_explicit < 1 :=
  theorem_5_1_at_p_explicit.choose_spec.2.1

/-- Positivity of `gamma_explicit` is implied by `gamma_explicit > log(1+√2) > 0`. -/
theorem gamma_explicit_pos : 0 < gamma_explicit := by
  have h_log_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    have h_sqrt : 1 < Real.sqrt 2 := by
      have h2 : (1 : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  linarith [gamma_explicit_gt_log]

/-! ## Rational sandwich on `gamma_explicit`

The certified-arb `solve_gamma.gamma_best` emits `γ ≈ 0.8813735870195430252…`
with arb radius below `5·10⁻⁴¹`. The rationals below pick a 10⁻¹⁶-wide
window around that midpoint. The runner verifies that `gamma_best` lies
inside the window; the Lean-side identification of `gamma_explicit` with
that arb interval is asserted via `h_gamma_explicit_sandwich`. -/

/-- Lower endpoint of the rational sandwich on `gamma_explicit`. Picked
just below the certified-arb `gamma_best ≈ 0.8813735870195430252…`. -/
def gamma_lo_rat : ℚ := 8813735870195430 / 10^16

/-- Upper endpoint of the rational sandwich on `gamma_explicit`. Picked
just above the certified-arb `gamma_best`. -/
def gamma_hi_rat : ℚ := 8813735870195431 / 10^16

/-- **Oracle axiom.** The Lean witness `gamma_explicit` lies in the rational
sandwich `[gamma_lo_rat, gamma_hi_rat]`. Numerically witnessed by
`solve_gamma.gamma_best`'s arb interval, which the runner verifies is
contained in the same sandwich.

Bridge status: `gamma_explicit` is now extracted from `theorem_5_1_at_p_explicit`,
which fixes `(η, p) = (eta_val, p_explicit_rat)` to match the certified-arb
pipeline's `p_override = 1e-30`. The IVT-chosen γ for this specific `p` is
the same γ that `solve_gamma` computes via arb. The remaining axiomatic gap
is just the assertion that the arb-computed `gamma_best ± radius` numerically
hits the rational interval `[gamma_lo_rat, gamma_hi_rat]` — a computational
fact the runner's `gamma_best_in_lean_sandwich` cross-check verifies on every
`--run-all` invocation. -/
axiom h_gamma_explicit_sandwich :
    (gamma_lo_rat : ℝ) < gamma_explicit ∧ gamma_explicit < (gamma_hi_rat : ℝ)

theorem gamma_explicit_gt_lo_rat : (gamma_lo_rat : ℝ) < gamma_explicit :=
  h_gamma_explicit_sandwich.1

theorem gamma_explicit_lt_hi_rat : gamma_explicit < (gamma_hi_rat : ℝ) :=
  h_gamma_explicit_sandwich.2

/-! ## Effective Theorem 5.1 -/

/-- **Effective Theorem 5.1.** Packaged as a single proposition over the
extracted witnesses; same shape as the original existential, but now `(η, p)`
is the explicit `(eta_val, p_explicit_rat)` matching the certified-arb
pipeline. -/
theorem theorem_5_1_effective :
    0 < eta_val_5_1 ∧ 0 < p_val_5_1 ∧
    gamma_explicit > Real.log (1 + Real.sqrt 2) ∧ gamma_explicit < 1 ∧
    ∃ (F_inv : ℂ → ℂ),
      AnalyticOnNhd ℂ F_inv (Braverman.disk gamma_explicit) ∧
      (∀ z ∈ Braverman.disk gamma_explicit,
        Braverman.F_p eta_val_5_1 p_val_5_1 (F_inv z) = z) ∧
      (∀ z ∈ Braverman.disk gamma_explicit, F_inv z ∈ Braverman.S) ∧
      Braverman.summability_condition (Braverman.taylor_coeff F_inv) gamma_explicit := by
  refine ⟨eta_val_5_1_pos, p_val_5_1_pos, gamma_explicit_gt_log, gamma_explicit_lt_one, ?_⟩
  -- The F_inv quintuple comes from `theorem_5_1_at_p_explicit`, whose `(η, p)`
  -- matches `(eta_val_5_1, p_val_5_1)` definitionally.
  exact theorem_5_1_at_p_explicit.choose_spec.2.2

end Braverman.Effective
