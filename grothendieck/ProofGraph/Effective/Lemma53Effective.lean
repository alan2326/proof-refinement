/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma53Effective.lean — Effective companion of Lemma 5.3

A trivial specialization of `Braverman.lemma_5_3` to the concrete tuple
`(eta_val, r_val) = (1/100, 23/25)`. The threshold `pr_val_53` is extracted
via `Classical.choose`; downstream consumers only need it to be positive
(no rational lower bound is required for the chain to `theorem_5_1`).
-/

import LeanProof.Lemma53
import ProofGraph.Effective.Lemma54Effective

open Complex Set Metric

noncomputable section

namespace Braverman.Effective

/-- The (opaque) `pr` extracted from `lemma_5_3` at `(eta_val, r_val)`. -/
def pr_val_53 : ℝ :=
  (Braverman.lemma_5_3 eta_val r_val r_val_pos r_val_lt_one).choose

theorem pr_val_53_pos : 0 < pr_val_53 :=
  (Braverman.lemma_5_3 eta_val r_val r_val_pos r_val_lt_one).choose_spec.1

/-- **Effective Lemma 5.3.** For every `p ∈ (0, pr_val_53)` there is an
analytic right-inverse `F_inv` of `F_p eta_val p` on `disk r_val`,
mapping into `S` and fixing `0`. -/
theorem lemma_5_3_effective :
    0 < pr_val_53 ∧ ∀ (p : ℝ), 0 < p → p < pr_val_53 →
      ∃ (F_inv : ℂ → ℂ),
        AnalyticOnNhd ℂ F_inv (Braverman.disk r_val) ∧
        (∀ z ∈ Braverman.disk r_val, Braverman.F_p eta_val p (F_inv z) = z) ∧
        (∀ z ∈ Braverman.disk r_val, F_inv z ∈ Braverman.S) ∧
        F_inv 0 = 0 := by
  refine ⟨pr_val_53_pos, ?_⟩
  intro p hp_pos hp_lt
  exact (Braverman.lemma_5_3 eta_val r_val r_val_pos r_val_lt_one).choose_spec.2
    p hp_pos hp_lt

end Braverman.Effective
