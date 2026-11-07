-- Sprint 097: hoist shim. The mathematical content of this file has
-- been moved to `ProofRefinement/Korenblum/Proof/Integrability.lean`
-- (under the namespace `ProofRefinement.Korenblum.Proof.Integrability`)
-- for shared reuse across V63-V68 and any future candidate that needs
-- the parametric `IntervalIntegrable` of `ModeBridge.scalarIntegrand`
-- (and its two-window consolidation shape). This file is preserved as
-- a thin re-export shim under the original per-candidate namespace
-- `ProofRefinement.Korenblum.Candidates.V63.Integrability`, so V63's
-- existing imports and qualified references continue to work
-- byte-for-byte without further edits to V63.lean.
--
-- Each of the two original top-level theorems is exposed as a
-- `theorem` alias whose proof is the corresponding hoisted theorem
-- under the new `Proof.Integrability` namespace. No `axiom`s. No
-- `sorry`s. No new mathematical content.

import ProofRefinement.Korenblum.Proof.Integrability

open scoped BigOperators Topology
open Filter Finset MeasureTheory Set

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V63.Integrability

open KorenblumPaper

/-- Re-export shim for the hoisted
`Proof.Integrability.modeScalarIntegrand_intervalIntegrable`. -/
theorem modeScalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ} {j : ℕ}
    (hj : 1 ≤ j)
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
      volume a b :=
  ProofRefinement.Korenblum.Proof.Integrability.modeScalarIntegrand_intervalIntegrable
    hj hc hab hca hb1 hPaperK

/-- Re-export shim for the hoisted
`Proof.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable`. -/
theorem mode_two_and_one_scalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ}
    (hc : 0 < c)
    (hcStart₁ : c ≤ ρStart₁)
    (hStart₁LeStop₁ : ρStart₁ ≤ ρStop₁)
    (hStart₂LeStop₂ : ρStart₂ ≤ ρStop₂)
    (hStop₁_le_Start₂ : ρStop₁ ≤ ρStart₂)
    (hStop₂_le_one : ρStop₂ ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 2 (WangOuter.paperLambda K c) ρ)
      volume ρStart₁ ρStop₁ ∧
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 1 (WangOuter.paperLambda K c) ρ)
      volume ρStart₂ ρStop₂ :=
  ProofRefinement.Korenblum.Proof.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
    hc hcStart₁ hStart₁LeStop₁ hStart₂LeStop₂ hStop₁_le_Start₂ hStop₂_le_one hPaperK

end ProofRefinement.Korenblum.Candidates.V63.Integrability
