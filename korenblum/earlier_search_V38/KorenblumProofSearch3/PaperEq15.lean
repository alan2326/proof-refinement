import Mathlib

open MeasureTheory

noncomputable section

namespace Korenblum

/-- Integrand for branch 1 of Wang's equation (15):
`12 ρ^3 (ρ^2 - c^2) / (c^6 Λ(ρ))`. -/
def scalarIntegrand1 (c : ℝ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  12 * ρ ^ 3 * (ρ ^ 2 - c ^ 2) / (c ^ 6 * Λ ρ)

/-- Integrand for branch 2 of Wang's equation (15):
`4 ρ^3 / (c^4 Λ(ρ))`. -/
def scalarIntegrand2 (c : ℝ) (Λ : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  4 * ρ ^ 3 / (c ^ 4 * Λ ρ)

/-- Wang's scalar criterion from equation (15). -/
def scalarCriterion (c : ℝ) (Λ : ℝ → ℝ) : ℝ :=
  let split := c * Real.sqrt (4 / 3)
  (∫ ρ in c..split, scalarIntegrand1 c Λ ρ) +
    ∫ ρ in split..1, scalarIntegrand2 c Λ ρ

end Korenblum
