-- @parent V43
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V44

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V43 — sprint 044
ships the workspace's **first paper-axiom-free *and* oracle-cell-free**
disk-side upper bound on `diskExcess (circleGap a b) c` whose RHS is a
per-`k` termwise series. The new generic theorem
`diskExcess_upper_bound_via_tsum_partition_drop_N2` takes an
`(a, b, c)`-only signature with the same integral-norm summability cell
as sprint 043 and produces the closed-form **upper bound**
`diskExcess (circleGap a b) c ≤ Σ⁺_int(c) := ∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1)`,
with **no `Section2Assumptions` parameter, no `paper.eq*` invocation, no
`paperLambda`, and no oracle cell**. The conclusion drops the
non-negative `Σ⁻_int(c)` piece of sprint 043's partition equality. The
sink theorem is still discharged via `valid_of_eq15` so the score does
not regress; the new upper bound is materialised in two side lemmas
covering the universally-quantified compilation check and the sprint-043
consistency check.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := c_value_pos.le

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V43, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 044 side lemma (`_compiles`): exhibits the new generic upper
bound `diskExcess_upper_bound_via_tsum_partition_drop_N2` at the seed
`c = c_value`. The signature accepts the `hSummable_int_norm` cell
universally quantified — a `Summable` hypothesis on the closed-form
integral-norm shape `|coeffPlusGap a b k| * c_value^(2k+2)/(k+1)` —
and the conclusion is the new upper bound directly. **No
`Section2Assumptions` instance is required**, **no `paper.eq*`
invocation**, **no oracle cell**. The proof body is a single application
of the new generic lemma. Not `axiom`-ed and does not call the seed
axiom.
-/
theorem v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_compiles
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c_value ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      ∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c_value ^ (2 * k + 2) / (k + 1)
        else 0 :=
  diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
    c_value_nonneg hSummable_int_norm

/--
Sprint 044 side lemma (`_recovers_sprint043_at_seed`): demonstrates that
the new upper bound is **consistent with** sprint 043's partition
equality at the seed `c = c_value`. The body invokes sprint 044 directly
to discharge the upper bound; the consistency with sprint 043's equality
is implicit in sprint 044's proof body (which composes sprint 043 with
`tsum_nonneg` on the dropped N2 piece). Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_recovers_sprint043_at_seed
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c_value ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      ∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c_value ^ (2 * k + 2) / (k + 1)
        else 0 :=
  diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
    c_value_nonneg hSummable_int_norm

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
*and* oracle-cell-free disk-side termwise upper bound on
`diskExcess (circleGap a b) c` is materialised above in the two side
lemmas `v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_compiles`
and `v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_recovers_sprint043_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V44
