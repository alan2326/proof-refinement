import ProofRefinement.Korenblum.Proof.ProblemAxioms

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum

open ProblemAxioms

/--
A candidate proves that `c` is a valid Korenblum lower bound if:

1. `0 < c < 1`, and
2. for every paper Section 2 instance at radius `c`, the inner disk excess is
   dominated by the outer annulus excess.
-/
def ValidKorenblumBound (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c),
        diskExcess paper.circleGap c ≤ annulusExcess paper.circleGap c

end ProofRefinement.Korenblum
