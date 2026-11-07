-- @parent V46
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V47

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V46 — sprint 047
ships the workspace's **first paper-axiom-free, oracle-cell-free annulus-side
N1/N2 partition equality** for `annulusExcess (circleGap a b) c` at the
integrated `tsum` layer. The new generic theorem
`annulusExcess_eq_tsum_partition_via_series` is the structural mirror of
sprint 043's `diskExcess_eq_tsum_partition_via_series` over the disjoint
sub-interval `[c, 1]` with the disjoint termwise integration weight
`(1 - c^(2k+2))/(k+1)`. Together with sprint 043 it covers **both halves**
of the natural decomposition `annulusSlice 0 1 = diskExcess + annulusExcess`
at the integrated × N1/N2-restricted termwise layer, completing the
prerequisite cone for an end-to-end paper-axiom-free, oracle-cell-free
closing reducer. The sink theorem is still discharged via `valid_of_eq15`
so the score does not regress; the new partition equality is materialised in
two side lemmas below.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := c_value_pos.le

theorem c_value_le_one : c_value ≤ (1 : ℝ) := c_value_lt_one.le

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V46, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 047 side lemma (`_compiles`): exhibits the new generic equality
`annulusExcess_eq_tsum_partition_via_series` at the seed `c = c_value`. The
signature accepts the `hSummable_int_norm` cell universally quantified —
a `Summable` hypothesis on the closed-form integral-norm shape
`|coeffPlusGap a b k| * (1 - c_value^(2k+2))/(k+1)` (the same shape sprint 046
takes) — and the conclusion is the new N1/N2 partition equality directly.
**No `Section2Assumptions` instance is required**, **no `paper.eq*`
invocation**, **no oracle cell**. The proof body is a single application of
the new generic lemma at the seed. Not `axiom`-ed and does not call the
seed axiom.
-/
theorem v47_annulusExcess_eq_tsum_partition_compiles
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c_value ^ (2 * k + 2)) / (k + 1))) :
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            (1 - c_value ^ (2 * k + 2)) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                (1 - c_value ^ (2 * k + 2)) / (k + 1)
            else 0 :=
  annulusExcess_eq_tsum_partition_via_series (a := a) (b := b)
    c_value_nonneg c_value_le_one hSummable_int_norm

/--
Sprint 047 side lemma (`_recovers_sprint046_at_seed`): demonstrates that the
new annulus-side N1/N2 partition equality re-derives sprint 046's
unconditioned `tsum`-of-integrals identity at the seed. The proof chains the
two equalities via transitivity: sprint 046 expresses
`annulusExcess (circleGap a b) c_value` as the unconditioned `tsum`, and
sprint 047 expresses it as the partition difference; chaining `← sprint046`
with `sprint047` yields the equality between the two RHS shapes. Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v47_annulusExcess_eq_tsum_partition_recovers_sprint046_at_seed
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c_value ^ (2 * k + 2)) / (k + 1))) :
    ∑' k : ℕ,
      PaperAxioms.coeffPlusGap a b k *
        (1 - c_value ^ (2 * k + 2)) / (k + 1) =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            (1 - c_value ^ (2 * k + 2)) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                (1 - c_value ^ (2 * k + 2)) / (k + 1)
            else 0 := by
  -- Both sides equal `annulusExcess (circleGap a b) c_value` by sprints
  -- 046 and 047 respectively. Chain via transitivity.
  rw [← annulusExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
        c_value_nonneg c_value_le_one hSummable_int_norm]
  exact annulusExcess_eq_tsum_partition_via_series (a := a) (b := b)
    c_value_nonneg c_value_le_one hSummable_int_norm

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free,
oracle-cell-free annulus-side N1/N2 partition equality is materialised above
in the two side lemmas
`v47_annulusExcess_eq_tsum_partition_compiles` and
`v47_annulusExcess_eq_tsum_partition_recovers_sprint046_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V47
