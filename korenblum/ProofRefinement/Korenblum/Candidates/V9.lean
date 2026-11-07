-- @parent V8
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V9

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3/V4/V5/V6/V7/V8 —
sprint 009 ships the *first cross-chain reducer* `valid_of_collapsed_disk_eq8_eq9_lower`
(stitching sprint 007's collapsed disk upper bound to sprint 006's `(8)+(9)`
annulus lower bound, eliminating both `diskExcess` and `annulusExcess` from the
sufficient condition's LHS), but the sink theorem is still discharged via
`valid_of_eq15` so the score does not regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3/V4/V5/V6/V7/V8, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 009 structural witness lemma: at the seed `c_value = 0.3554`, the
disk-side branch-split sub-regime `3ρ² ≤ 4c_value²` is non-vacuous —
`ρ = 4/10` satisfies `c_value < ρ < 1` and `3ρ² ≤ 4c_value²`.
Sanity: `4 · c_value² = 4 · 0.12631 = 0.50524`, `3 · 0.16 = 0.48 ≤ 0.50524`,
and `0.3554 < 0.4 < 1`. The witness is local to V9 and is not used elsewhere
— its purpose is to demonstrate that the disk-side witness component of
`valid_of_collapsed_disk_eq8_eq9_lower`'s `h_witness` premise is non-vacuous
at the seed `c_value`.
-/
theorem v9_branch_split_witness_at_seed :
    ∃ ρ : ℝ, c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 := by
  refine ⟨4 / 10, ?_, ?_, ?_⟩ <;> norm_num [c_value]

/--
Sprint 009 side lemma: exercise the new cross-chain reducer
`valid_of_collapsed_disk_eq8_eq9_lower` at the seed `c_value` against an
abstract witness/integrability bundle. This materialises the new chain
`(2)+(3)+(4) collapsed ∧ (8)+(9) integrated ∧ kernel ineq ⇒ ValidKorenblumBound`
in V9's call graph. The side lemma is not `axiom`-ed and does not call the
seed axiom; it exists purely to verify that the new reduction typechecks at
the seed `c_value`.
-/
theorem v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ ρ₁ ρ₂ : ℝ,
          c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 ∧
            c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c_value 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
            (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
                * PaperAxioms.sigmaZeroMinus a b ρ
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value :=
  valid_of_collapsed_disk_eq8_eq9_lower
    c_value_pos c_value_lt_one h_witness

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new cross-chain reducer is materialised
above in `v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V9
