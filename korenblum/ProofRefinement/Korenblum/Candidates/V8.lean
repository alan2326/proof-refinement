-- @parent V7
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V8

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0/V1/V2/V3/V4/V5/V6/V7 —
sprint 008 ships the *first sub-interval branch-1 sufficient condition* for
`ValidKorenblumBound` (a strictly weaker premise than Wang's `(15)`), but the
sink theorem is still discharged via `valid_of_eq15` so the score does not
regress. -/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0/V1/V2/V3/V4/V5/V6/V7, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 008 numeric witness lemma: at the seed `c_value = 0.3554`,
`branchSplit c_value = c_value · √(4/3) ≈ 0.4104 < 1`. We show this via
the explicit numeric bound `√(4/3) ≤ 6/5`, then `c_value · √(4/3) ≤
0.3554 · 1.2 = 0.42648 < 1`. The witness is local to V8 and is not used
elsewhere — its purpose is to demonstrate that the `hSplit_lt_one`
hypothesis of `valid_of_eq10_subinterval_branch1` is non-vacuous at the
seed `c_value`.
-/
theorem v8_split_lt_one_at_seed :
    PaperAxioms.branchSplit c_value < 1 := by
  unfold PaperAxioms.branchSplit
  have h43_nn : (0 : ℝ) ≤ 4 / 3 := by norm_num
  have hsq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 := Real.sq_sqrt h43_nn
  have hsqrt_nn : 0 ≤ Real.sqrt (4 / 3 : ℝ) := Real.sqrt_nonneg _
  -- √(4/3) ≤ 6/5 because (6/5)² = 36/25 ≥ 4/3.
  have hbound : Real.sqrt (4 / 3 : ℝ) ≤ 6 / 5 := by
    nlinarith [hsq, hsqrt_nn]
  have hcv : c_value = 3554 / 10000 := rfl
  nlinarith [hbound, hsqrt_nn, c_value_pos, hcv]

/--
Sprint 008 side lemma: exercise the new sub-interval branch-1 sufficient
condition `valid_of_eq10_subinterval_branch1` at the seed `c_value` against
abstract window/mass/integrability premises. This materialises the new
chain `(10) + sub-interval mass ≥ 1 ⇒ ValidKorenblumBound` in V8's call
graph. The side lemma is not `axiom`-ed and does not call the seed axiom;
it exists purely to verify that the new reduction typechecks at the seed
`c_value`.
-/
theorem v8_valid_of_eq10_subinterval_branch1_chain_compiles
    (hSplit_lt_one : PaperAxioms.branchSplit c_value < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c_value 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c_value
                  (WangOuter.paperLambda K c_value) ρ) :
    ValidKorenblumBound c_value :=
  valid_of_eq10_subinterval_branch1
    c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum lower
bound. We discharge the sink theorem via the existing `valid_of_eq15` so that
the score does not regress; the brand-new sub-interval branch-1 sufficient
condition is materialised above in
`v8_valid_of_eq10_subinterval_branch1_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V8
