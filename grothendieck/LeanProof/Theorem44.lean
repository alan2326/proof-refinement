/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanProof.Theorem44Main

/-!
# Theorem 4.4: Strict improvement over Krivine's scheme

We prove that H_η(i)/i > log(1+√2) for small η > 0.

This is THE key result showing that the partition f_η gives a strict improvement
over the identity (Krivine's scheme), and is the reason the Grothendieck constant
is strictly less than the Krivine bound π/(2·log(1+√2)).

The proof is assembled in `Theorem44Main.lean` from:
- `Theorem44Core.lean`: Phi definition, F44, partial derivatives
- `Theorem44Regularity.lean`: C⁴ regularity, differentiation under integral
- `Theorem44Support.lean`: Gaussian/Hermite transform lemmas
- `Theorem44DirectValues.lean`: Φ''(0) = 0
- `Theorem44FourthDeriv.lean`: Φ''''(0) = 75√2/(8π) > 0
- `Theorem44Main.lean`: Taylor assembly → Φ(η) > Φ(0) near 0
-/

noncomputable section

namespace Braverman

/-- **Theorem 4.4**: H_η(i)/i > log(1+√2) for small η > 0.

    Equivalently, φ(η) > φ(0) for small η > 0. This follows from
    the Taylor expansion: φ(η) = φ(0) + φ⁴(0)/24 · η⁴ + O(η⁵),
    with φ⁴(0) > 0 and lower-order terms vanishing. -/
theorem theorem_4_4 : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
    (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2) :=
  theorem_4_4'

/-- Corollary: there exists η > 0 such that H_η(i)/i > log(1+√2). -/
theorem exists_eta_strict_improvement :
    ∃ η : ℝ, 0 < η ∧ (H_eta η Complex.I / Complex.I).re > Real.log (1 + Real.sqrt 2) := by
  obtain ⟨η₀, hη₀_pos, hη₀⟩ := theorem_4_4
  exact ⟨η₀ / 2, by linarith, hη₀ _ (by linarith) (by linarith)⟩

end Braverman
