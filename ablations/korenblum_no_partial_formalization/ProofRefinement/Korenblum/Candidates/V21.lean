-- @parent V20
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct
import ProofRefinement.Korenblum.Proof.CirclePolynomialParseval
import ProofRefinement.Korenblum.Proof.AnalyticParseval
import ProofRefinement.Korenblum.Proof.CircleMeanRadial
import ProofRefinement.Korenblum.Proof.BergmanParseval
import ProofRefinement.Korenblum.Proof.PolarIntegrability
import ProofRefinement.Korenblum.Proof.RadialIntegrability
import ProofRefinement.Korenblum.Proof.CleanConditional
import ProofRefinement.Korenblum.Proof.InnerRadialReduction
import ProofRefinement.Korenblum.Proof.AnnulusBergmanParseval
import ProofRefinement.Korenblum.Proof.CircleMeanLogConvex
import ProofRefinement.Korenblum.Proof.CauchyL2Estimate
import ProofRefinement.Korenblum.Proof.SubMeanValue
import ProofRefinement.Korenblum.Proof.CircleMeanContinuous
import ProofRefinement.Korenblum.Proof.MobiusDisk
import ProofRefinement.Korenblum.Proof.MobiusDeriv

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V21

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V20. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input.

Wang (2025) proved the Korenblum maximum principle holds at radius
`c = 0.3554` at the Bergman A² level. This single axiom asserts the entire
Wang theorem at this radius.

V21 adds the new module `Proof/MobiusDeriv.lean` to the build graph. That
module pins the analytic derivative of the unit-disk Möbius automorphism
`φ_a(z) = (a - z) / (1 - conj(a) z)` plus its modulus identity (the
positive real Jacobian factor that appears in any Bergman A²
change-of-variables on the disk under `φ_a`):

* `hasDerivAt_mobiusDisk` — pointwise derivative formula
  `(mobiusDisk a)'(z) = -(1 - conj(a) * a) / (1 - conj(a) z)^2`,
* `norm_sq_deriv_mobiusDisk` — modulus identity
  `‖(mobiusDisk a)'(z)‖² = (1 - ‖a‖²)² / ‖1 - conj(a) z‖^4`,
* `deriv_mobiusDisk` — same as (1) packaged for `deriv`.

These are the missing analytic link between sprint 020's Möbius algebra
primitives and a future Bergman A² conformal-invariance result. The score
`c_value = 3554/10000` is unchanged from V20; this sprint is
scaffolding-only and exercises the new module via import.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V21 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V20; this sprint is scaffolding-only and
adds the Möbius unit-disk automorphism's derivative plus its Jacobian-
modulus identity in `Proof/MobiusDeriv.lean`, exercised by the build via
import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V21
