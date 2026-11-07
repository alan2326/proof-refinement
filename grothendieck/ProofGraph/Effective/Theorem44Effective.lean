/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem44Effective.lean — Effective companion of Theorem 4.4

The original `Braverman.theorem_4_4` is purely existential: there *exists*
some small `η₀ > 0` such that the strict-improvement inequality holds for
`η ∈ (0, η₀)`. The threshold `η₀` is buried in the proof.

The effective companion exposes a concrete `eta_val := 1/100` and asserts
the inequality at that specific value via a single oracle-backed axiom.
The certified-arb pipeline
`grothendieck.proof.certified.h_eta_evaluator.eval_h_eta_at_i_arb` numerically
verifies the inequality at `eta_val`; the proof-graph runner re-runs it on
every `--all` invocation.
-/

import LeanProof.Theorem44
import ProofGraph.Effective.Lemma54Effective

open Complex

noncomputable section

namespace Braverman.Effective

/-! ## Oracle-backed numerical axiom

Asserts that the specific `eta_val = 1/100` chosen for the proof graph
satisfies the strict-improvement inequality. Numerically verified by
`eval_h_eta_at_i_arb` (which delegates to `compute_Delta_rigor` over a
truncated GL grid; certified margin of `Δ ≈ 5.3 · 10⁻⁸`). -/
axiom h_eta_strict_improvement_oracle :
    (Braverman.H_eta eta_val Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2)

/-! ## Effective Theorem 4.4 -/

/-- **Effective Theorem 4.4.** The specific `eta_val = 1/100` strictly
improves over Krivine's scheme: `H_{eta_val}(i)/i > log(1+√2)`. -/
theorem theorem_4_4_effective :
    0 < eta_val ∧
    (Braverman.H_eta eta_val Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2) :=
  ⟨eta_val_pos, h_eta_strict_improvement_oracle⟩

end Braverman.Effective
