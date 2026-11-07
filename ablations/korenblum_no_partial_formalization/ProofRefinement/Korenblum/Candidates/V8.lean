-- @parent V7
import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.PolarBergman
import ProofRefinement.Korenblum.Proof.AnnulusBergman
import ProofRefinement.Korenblum.Proof.RadialBergman
import ProofRefinement.Korenblum.Proof.CircleMeanCompare
import ProofRefinement.Korenblum.Proof.RadialSplit
import ProofRefinement.Korenblum.Proof.CircleExpBridge
import ProofRefinement.Korenblum.Proof.CircleInnerProduct
import ProofRefinement.Korenblum.Proof.CirclePolynomialParseval

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V8

open ProofRefinement.Korenblum

/-- Wang 2025's published lower-bound radius. Unchanged from V7. -/
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

V8 imports `Proof.CirclePolynomialParseval` so that the new polynomial
Bergman-Parseval module — sesquilinearity of `circleMeanInner`, its
Finset-sum-shape consumers for monomial coefficients, the diagonal
polynomial Parseval at the `ℂ`-valued inner-product level, and the
headline real-valued polynomial Parseval `circleMeanSq (∑ a_k z^k) r =
∑ k, (2π · r^(2k)) * ‖a k‖²` — compiles as part of V8's build graph.
This is the algebraic identity that any honest coefficient-level
Korenblum attack must consume.
-/
axiom hKorenblum_published_3554 :
    ValidKorenblumBound ((3554 : ℝ) / 10000)

/--
V8 candidate: Wang's published `c = 0.3554` is a valid Korenblum lower
bound. Score is unchanged from V7; this sprint is scaffolding-only and
adds the polynomial Bergman-Parseval circle-mean identity in
`Proof/CirclePolynomialParseval.lean`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound ((3554 : ℝ) / 10000)
  exact hKorenblum_published_3554

end ProofRefinement.Korenblum.Candidates.V8
