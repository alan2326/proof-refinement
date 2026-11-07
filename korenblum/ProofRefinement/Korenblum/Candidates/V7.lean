-- @parent V6
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V7

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3/V4/V5/V6 —
sprint 007 ships the *single-`Z` collapse* of sprint 003's two-`Z` disk-side
upper bound on the branch-split sub-regime `(c, branchSplit c]`, but the
sink theorem is still discharged via `valid_of_eq15` so the score does not
regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3/V4/V5/V6, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 007 side lemma: exercise the new single-`Z` collapsed disk-side upper
bound at the seed `c_value` against an abstract `ρ` constrained by the
branch-split inequality `3·ρ² ≤ 4·c²`. This materialises the new chain
`diskExcess ≤ (c⁶/6)/(ρ²−c²)·Z_ρ` (a single-`Z` upper bound — the first of
its kind in the workspace). The side lemma is not `axiom`-ed and does not
call the seed axiom; it exists purely to verify that the new bound
typechecks at the seed `c_value`.
-/
theorem v7_diskExcess_collapsed_single_Z_chain_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    {ρ : ℝ}
    (hcρ : c_value < ρ)
    (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c_value ^ 2)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
        * PaperAxioms.sigmaZeroMinus a b ρ :=
  diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
    paper c_value_pos hcρ hρ_branch hρ1 hInt

/--
Sprint 007 numeric witness lemma: the branch-split sub-regime
`(c_value, branchSplit c_value]` is non-empty at the seed `c_value`. We pick
`ρ = 41/100 = 0.41`, which satisfies `c_value = 0.3554 < 0.41` and
`3·(0.41)² = 0.5043 ≤ 4·(0.3554)² ≈ 0.50523664`. This confirms that the new
bound has a non-trivial domain of applicability at the seed `c_value`. The
witness is local to V7 and is not used elsewhere.
-/
theorem v7_branch_split_witness_at_seed :
    c_value < 41 / 100 ∧ 3 * (41 / 100 : ℝ) ^ 2 ≤ 4 * c_value ^ 2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [c_value]

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new single-`Z` collapsed disk-side
upper bound is materialised above in
`v7_diskExcess_collapsed_single_Z_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V7
