/-
# The scored contract

TRUSTED SURFACE — read-only to every agent in the refinement loop.

A candidate ships two rational literals `lambda` and `kappa` together with a
proof of `ValidPolygonBound lambda kappa`. The score is the width coefficient
`kappa - lambda`, minimized. Improving means lowering `kappa`, raising `lambda`,
or both.

The obligation is quantified over **all** depths `n`, not just the benchmark
depth. Freezing the depth inside the obligation would let a candidate win by
brute-force numerics at a single point. The benchmark depth enters only in the
*reported* interval (`Proof/FixedDepth.lean`).
-/
import ProofRefinement.PolygonPi.Proof.Surface

open scoped Real

namespace ProofRefinement.PolygonPi

open PolygonCore

/-- The scored contract: uniform-in-`n` two-sided error coefficients.

`0 ≤ lam` rather than `0 < lam`, so the baseline `lambda = 0` sits inside the
contract instead of being a special case; at `lam = 0` the lower conjunct
reduces to the trusted `polygonLower_lt_pi`. -/
def ValidPolygonBound (lam kap : ℝ) : Prop :=
  0 ≤ lam ∧ 0 < kap ∧
    ∀ n : ℕ,
      polygonLower n + lam / 4 ^ n < Real.pi ∧
      Real.pi < polygonLower n + kap / 4 ^ n

/-- The optional secondary contract at one frozen depth `d`.

Logged as a second frontier, never a substitute for `ValidPolygonBound`. A
candidate that declares it is claiming a bound it could not establish uniformly
in `n`. -/
def ValidPolygonBoundAt (d : ℕ) (lam kap : ℝ) : Prop :=
  0 ≤ lam ∧ 0 < kap ∧
    polygonLower d + lam / 4 ^ d < Real.pi ∧
    Real.pi < polygonLower d + kap / 4 ^ d

end ProofRefinement.PolygonPi
