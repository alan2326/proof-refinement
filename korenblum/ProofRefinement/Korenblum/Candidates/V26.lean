-- @parent V25
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V26

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V25 — sprint 026 ships
the workspace's **first integrated disk bound with paper-axiom signature
`{eq4}` only** (vs sprint 013's `{eq3, eq4}`), the **first paper-internal
cross-validation that sprint 013's `diskExcess ≤ c⁴ · sigmaZeroMinus c` bound
is derivable through a strictly smaller paper-axiom signature**, and **sprint
025's first downstream consumer**. The new generic theorem
`diskExcess_upper_bound_via_circleGapSeries_eq4_only` integrates sprint 025's
pointwise series-side bound `circleGap r ≤ sigmaPlus r` against the polar
Jacobian `2r` over `[0, c]`, after pointwise compression via
`paper.eq4_sigmaPlus_bound`. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V25, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 026 side lemma: exercise the brand-new full-disk integrated upper bound
`diskExcess_upper_bound_via_circleGapSeries_eq4_only` at the seed
`c = c_value`. The signature exhibits the new lemma's hypothesis shape — the
abstract `Section2Assumptions` instance, the universal-over-`Ioo 0 c` series
summability premise, and the integrability of `2r·circleGap` on `[0, c]`. The
proof body is a single application of the new generic lemma. Not `axiom`-ed
and does not call the seed axiom.
-/
theorem v26_disk_bound_via_circleGapSeries_eq4_only_compiles
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
  diskExcess_upper_bound_via_circleGapSeries_eq4_only
    paper c_value_pos c_value_lt_one hSummable hInt

/--
Sprint 026 structural witness lemma: the closed-form RHS coefficient of the
new bound at the seed `c_value^4 = (1777/5000)^4` is positive. Confirms that
the bound is non-vacuous when `sigmaZeroMinus a b c_value > 0`. Not `axiom`-ed
and does not call the seed axiom.
-/
theorem v26_disk_bound_rhs_coefficient_at_seed :
    (0 : ℝ) < c_value ^ 4 := by
  unfold c_value
  norm_num

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new full-disk integrated upper
bound is materialised above in `v26_disk_bound_via_circleGapSeries_eq4_only_compiles`
and `v26_disk_bound_rhs_coefficient_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V26
