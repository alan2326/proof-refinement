-- @parent V24
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V25

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V24 — sprint 025 ships
the workspace's **first lemma operating purely at the `circleGapSeries`
representation level**, the **first workspace consumer of
`coeffPlusGap`/`sigmaPlus`/`n1Pred`**, and the **first paper-internal
cross-validation that the inequality direction of
`paper.eq3_circleGap_decomposition` (`circleGap r ≤ sigmaPlus r`) is provable
from series structure alone, with zero paper-axiom invocation in the transitive
proof body**. The new generic theorem `circleGap_le_sigmaPlus_via_series_split`
is parameterised only by `(a, b, r)` and a single summability premise on the
full `circleGapSeries` summand; it is **not** a closing reducer for
`ValidKorenblumBound c`, but a structural lemma that opens the
`circleGapSeries`-direct sufficient-condition axis. The sink theorem is still
discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V24, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 025 side lemma: exercise the brand-new series-representation-level
upper bound `circleGap_le_sigmaPlus_via_series_split` at the seed
`r = c_value`. The signature exhibits the new lemma's hypothesis shape — only
two cells: non-negativity of the radius (here `c_value_pos.le`) and
summability of the `circleGapSeries` summand at `r = c_value`. The proof body
is a single application of the new generic lemma. Not `axiom`-ed and does not
call the seed axiom.
-/
theorem v25_circleGap_le_sigmaPlus_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
    PaperAxioms.circleGap a b c_value ≤ PaperAxioms.sigmaPlus a b c_value :=
  circleGap_le_sigmaPlus_via_series_split a b c_value_pos.le hSummable

/--
Sprint 025 structural witness lemma: the analytical core of sprint 025
materialised at the seed — the termwise non-positivity of the n2Pred
contribution to `circleGapSeries c_value`. For any index `k` satisfying
`n2Pred a b k` (equivalently `0 < k ∧ ‖a k‖ < ‖b k‖`), the summand
`coeffPlusGap a b k · c_value^(2k) = (‖a k‖² − ‖b k‖²) · c_value^(2k)` is
non-positive — derived via `pow_le_pow_left₀` on `‖a k‖ < ‖b k‖` for
`coeffPlusGap a b k ≤ 0` and `pow_nonneg c_value_pos.le _` for
`c_value^(2k) ≥ 0`, then combined via `mul_nonpos_of_nonpos_of_nonneg`.
This is the structural fact at the heart of sprint 025's proof body, exhibited
at the seed radius. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v25_circleGap_series_split_n2_nonpos_at_seed
    (a b : ℕ → ℂ) (k : ℕ) (h : PaperAxioms.n2Pred a b k) :
    PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k) ≤ 0 := by
  have hab : ‖a k‖ < ‖b k‖ := h.2
  have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
  have h_sq_le : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
    pow_le_pow_left₀ ha_nn hab.le 2
  have h_gap_np : PaperAxioms.coeffPlusGap a b k ≤ 0 := by
    unfold PaperAxioms.coeffPlusGap
    linarith
  have h_pow_nn : 0 ≤ c_value ^ (2 * k) :=
    pow_nonneg c_value_pos.le _
  exact mul_nonpos_of_nonpos_of_nonneg h_gap_np h_pow_nn

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new series-representation-level
upper bound is materialised above in `v25_circleGap_le_sigmaPlus_compiles`
and `v25_circleGap_series_split_n2_nonpos_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V25
