-- @parent V19
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V20

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V19. -/
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

V20 adds the new module `Proof/MobiusDisk.lean` to the build graph. That
module pins five core algebraic / analytic primitives for the unit-disk
Möbius automorphism `φ_a(z) = (a - z) / (1 - conj(a) · z)`:

* `mobiusDisk_denom_ne_zero` — denominator non-vanishing on the closed
  unit disk for `a ∈ UnitDisk`,
* `mobiusDisk_one_sub_normSq` — the Schwarz–Pick algebraic identity
  `1 - ‖φ_a z‖² = (1 - ‖a‖²)(1 - ‖z‖²) / ‖1 - conj(a)·z‖²`,
* `mobiusDisk_mapsTo` — `φ_a` is a self-map of `UnitDisk`,
* `mobiusDisk_involution` — `φ_a ∘ φ_a = id` on `UnitDisk`,
* `mobiusDisk_analyticOn` — `φ_a` is analytic on `UnitDisk`.

These are the algebraic / analytic primitives every downstream Schwarz–Pick,
pseudohyperbolic-distance, or Bergman-A² conformal-invariance argument
factors through. The score `c_value = 3554/10000` is unchanged from V19;
this sprint is scaffolding-only and exercises the new module via import.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V20 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V19; this sprint is scaffolding-only and
adds the Möbius unit-disk automorphism's algebraic / analytic primitives
in `Proof/MobiusDisk.lean`, exercised by the build via import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V20
