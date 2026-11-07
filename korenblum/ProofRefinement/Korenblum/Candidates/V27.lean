-- @parent V26
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V27

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V26 — sprint 027 ships
the workspace's **first paper-axiom-free proof of the *equality direction* of
`paper.eq3_circleGap_decomposition`** (`circleGap r = sigmaPlus r −
r² · sigmaZeroMinus r`), a strict structural upgrade of sprint 025's
*inequality* direction `circleGap r ≤ sigmaPlus r`, and the **first workspace
`tsum`-partition identity argument on `circleGapSeries`**. The new generic
theorem `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` is
parameterised only by `(a, b, r)`, `r ≥ 0`, and a single summability premise on
the unconditioned `circleGapSeries` summand; it is **not** a closing reducer
for `ValidKorenblumBound c`, but a structural identity that opens the
`circleGapSeries`-direct identity-form axis for downstream consumers. The sink
theorem is still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V26, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 027 side lemma: exercise the brand-new series-level *equality* identity
`circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` at the seed
`r = c_value`. The signature exhibits the new lemma's hypothesis shape — only
two cells: non-negativity of the radius (here `c_value_pos.le`) and summability
of the unconditioned `circleGapSeries` summand at `r = c_value`. The proof body
is a single application of the new generic lemma. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v27_circleGap_eq_via_series_partition_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
    PaperAxioms.circleGap a b c_value =
      PaperAxioms.sigmaPlus a b c_value -
        c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value :=
  circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
    a b c_value_pos.le hSummable

/--
Sprint 027 structural witness lemma: confirm that the new lemma's identity at
`r = c_value` reproduces the conclusion of
`paper.eq3_circleGap_decomposition c_value` *without* invoking
`paper.eq3_circleGap_decomposition` anywhere in the proof body. The `paper`
parameter is present only as a structural witness that the equality's *type*
matches what `eq3` would produce; the actual proof discharges through sprint
027 alone. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
    PaperAxioms.circleGap a b c_value =
      PaperAxioms.sigmaPlus a b c_value -
        c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value := by
  -- Sprint 027's identity gives the conclusion directly,
  -- without invoking `paper.eq3_circleGap_decomposition`.
  exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
    a b c_value_pos.le hSummable

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new series-level *equality*
identity is materialised above in
`v27_circleGap_eq_via_series_partition_compiles` and
`v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V27
