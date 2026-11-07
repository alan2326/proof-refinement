import Mathlib

/-!
# Korenblum maximum principle — Bergman A² candidate contract (noPF arm)

This file holds the entire mathematical content of the candidate contract for
the no-partial-formalization ablation arm. Unlike the sibling `korenblum/`
workspace, this file contains **no** coefficient-level intermediate, **no**
Wang Section 2 hypothesis bundle, and **no** equation chain — only the
function-level Korenblum max principle stated against Mathlib.

The agent's task in this arm is to prove `ValidKorenblumBound c` for the
largest rational `c ∈ (0,1)` it can.
-/

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum

/-- The open complex unit disk. -/
def UnitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- Squared Bergman A² seminorm: `∫_𝔻 |f(z)|² dA(z)`. -/
noncomputable def bergmanNormSq (f : ℂ → ℂ) : ℝ :=
  ∫ z in UnitDisk, ‖f z‖ ^ 2 ∂(volume : Measure ℂ)

/--
Korenblum maximum principle at radius `c`.

A real number `c ∈ (0,1)` is a valid Korenblum lower bound if, for every pair
of analytic, A²-integrable functions `f, g : ℂ → ℂ` on the open unit disk
such that `‖f(z)‖ ≤ ‖g(z)‖` whenever `c < ‖z‖ < 1`, the Bergman A² norm
inequality `‖f‖_{A²} ≤ ‖g‖_{A²}` holds.

This is the function-level Korenblum statement. There is no intermediate
coefficient-level reduction here.
-/
def ValidKorenblumBound (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk →
      AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      bergmanNormSq f ≤ bergmanNormSq g

end ProofRefinement.Korenblum
