-- @parent V17
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V18

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V17. -/
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

V18 adds the Bergman A² sub-mean-value inequality at the origin (sprint
018) in `Proof/SubMeanValue.lean`. One new public theorem is exposed:

* `normSq_zero_le_bergmanNormSq_div_pi` — sub-mean-value inequality at the
  origin. For `f` analytic and A²-integrable on `UnitDisk`,
  `π · ‖f(0)‖² ≤ bergmanNormSq f`. Proved by single-summand
  `Summable.le_tsum` extraction on sprint 011's whole-disk Bergman
  Parseval identity, with the `a₀ = f(0)` identification via
  `HasFPowerSeriesAt.coeff_zero`.

This is the "outer→pointwise transport" primitive: it gives a pointwise
upper bound on `‖f(z)‖²` from an integrated bound on `‖f‖²` over a disk
centered at `z`. The general-interior-point form (theorem (2) in the
sprint contract) is deferred to a follow-up sprint per Fallback A; see
`Experience.md` for the deferral note.

The score `c_value = 3554/10000` is unchanged from V17.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V18 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V17; this sprint is scaffolding-only and
adds the Bergman A² sub-mean-value inequality at the origin in
`Proof/SubMeanValue.lean`, exercised by the build via import.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V18
