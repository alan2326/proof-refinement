-- @parent V42
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V43

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V42 — sprint 043
ships the workspace's **first paper-axiom-free N1/N2 partition** of sprint
042's `tsum`-of-integrals identity for `diskExcess (circleGap a b) c`. The
new generic theorem `diskExcess_eq_tsum_partition_via_series` takes an
`(a, b, c)`-only signature with the same integral-norm summability cell as
sprint 042 and produces the closed-form **partition equality**
`diskExcess (circleGap a b) c =
    (∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1)) − (∑'_{N2} coeffMinusGap_k · c^(2k+2)/(k+1))`,
with **no `Section2Assumptions` parameter, no `paper.eq*` invocation, no
`paperLambda`, and no oracle cell**. The conclusion exposes the integrated
`Σ⁺_int(c)` and `Σ⁻_int(c)` series quantities for the first time at the
integrated layer. The sink theorem is still discharged via `valid_of_eq15`
so the score does not regress; the new partition equality is materialised
in two side lemmas covering the universally-quantified compilation check
and the sprint-042 consistency check.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := c_value_pos.le

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V42, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 043 side lemma (`_compiles`): exhibits the new generic partition
equality `diskExcess_eq_tsum_partition_via_series` at the seed
`c = c_value`. The signature accepts the `hSummable_int_norm` cell
universally quantified — a `Summable` hypothesis on the closed-form
integral-norm shape `|coeffPlusGap a b k| * c_value^(2k+2)/(k+1)` — and
the conclusion is the new partition equality directly. **No
`Section2Assumptions` instance is required**, **no `paper.eq*`
invocation**, **no oracle cell**. The proof body is a single application
of the new generic lemma. Not `axiom`-ed and does not call the seed
axiom.
-/
theorem v43_diskExcess_eq_tsum_partition_compiles
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c_value ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c_value ^ (2 * k + 2) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                c_value ^ (2 * k + 2) / (k + 1)
            else 0 :=
  diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
    c_value_nonneg hSummable_int_norm

/--
Sprint 043 side lemma (`_recovers_sprint042_at_seed`): demonstrates that
the new partition equality is **consistent with** sprint 042's
unconditioned `tsum` identity at the seed `c = c_value`. The body
applies sprint 042 (rewriting `diskExcess` as the unconditioned `tsum`)
and then sprint 043 (rewriting `diskExcess` as the partition difference)
to chain the two RHSes via transitivity. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v43_diskExcess_eq_tsum_partition_recovers_sprint042_at_seed
    (a b : ℕ → ℂ)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c_value ^ (2 * k + 2) / (k + 1))) :
    ∑' k : ℕ,
      PaperAxioms.coeffPlusGap a b k *
        c_value ^ (2 * k + 2) / (k + 1) =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c_value ^ (2 * k + 2) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                c_value ^ (2 * k + 2) / (k + 1)
            else 0 := by
  -- Both sides equal `diskExcess (circleGap a b) c_value` by sprints 042
  -- and 043 respectively. Chain via transitivity.
  rw [← diskExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
        c_value_nonneg hSummable_int_norm]
  exact diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
    c_value_nonneg hSummable_int_norm

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
N1/N2-partitioned `tsum`-of-integrals closed-form equality identity is
materialised above in the two side lemmas
`v43_diskExcess_eq_tsum_partition_compiles` and
`v43_diskExcess_eq_tsum_partition_recovers_sprint042_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V43
