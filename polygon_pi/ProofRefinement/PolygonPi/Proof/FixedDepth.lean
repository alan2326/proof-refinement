/-
# The pinned benchmark interval

TRUSTED SURFACE — read-only to every agent in the refinement loop.

`certified_polygon_interval` is the theorem the artifact reports. It is a
trusted corollary of the contract, so no candidate can weaken it: whatever a
candidate proves, the evaluator type-checks this corollary applied to it, and
the reported interval is therefore always

    P₁₀ + lambda / 4 ^ 10  <  π  <  P₁₀ + kappa / 4 ^ 10

with `P₁₀` the half-perimeter of the inscribed regular 4096-gon and width
exactly `(kappa - lambda) / 4 ^ 10`.
-/
import ProofRefinement.PolygonPi.Proof.CandidateContract

open scoped Real

namespace ProofRefinement.PolygonPi

open PolygonCore

/-- The reported interval at the frozen benchmark depth. -/
theorem certified_polygon_interval {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    polygonLower benchmarkDepth + lam / 4 ^ benchmarkDepth < Real.pi ∧
    Real.pi < polygonLower benchmarkDepth + kap / 4 ^ benchmarkDepth :=
  h.2.2 benchmarkDepth

/-- The width of the reported interval is `(kap - lam) / 4 ^ benchmarkDepth`.

Stated so the artifact's headline number is a theorem rather than arithmetic
done in prose. -/
theorem certified_polygon_interval_width (lam kap : ℝ) :
    (polygonLower benchmarkDepth + kap / 4 ^ benchmarkDepth) -
      (polygonLower benchmarkDepth + lam / 4 ^ benchmarkDepth) =
    (kap - lam) / 4 ^ benchmarkDepth := by
  ring

end ProofRefinement.PolygonPi
