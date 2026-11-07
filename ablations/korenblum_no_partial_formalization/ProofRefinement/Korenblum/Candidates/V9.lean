-- @parent V8
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

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V9

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V8. -/
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

V9 imports `Proof.AnalyticParseval` so that the new analytic Bergman-Parseval
circle-mean identity — `circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖p.coeff k‖²`
for `f` analytic with formal power series `p` on a ball `0 ≤ r < R`, plus
its disk-shape consumer for `AnalyticOn ℂ f UnitDisk` and `0 ≤ r < 1` —
compiles as part of V9's build graph. This is the analytic-to-coefficient
bridge that any future Korenblum c-push must consume.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V9 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V8; this sprint is scaffolding-only and
adds the analytic Bergman-Parseval identity in `Proof/AnalyticParseval.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V9
