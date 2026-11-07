-- Sprint 070, Phase A: per-candidate derived-theorem file shipping the
-- series-level bridge connecting Wang's per-`k` lift identity (V54) to the
-- workspace's `tsum`-level circle-gap object.
--
-- This file ships LIFT_SERIES_BRIDGE as a Lean theorem (no axiom, no
-- oracle, no edit to `KorenblumPaper/`). The natural composition of:
--
--   * `Candidates.V54.LiftIdentity.lift_identity_per_k` (sprint 069),
--   * `Mathlib.Topology.Algebra.InfiniteSum.*` (`Summable.tsum_sub`,
--     `Summable.div_const`, `tsum_div_const`),
--   * the `def`-level unfolding of `liftGapSeries` and `circleGapSeries`
--     from `KorenblumPaper.PaperAxioms`.
--
-- ### Sign / orientation note
--
-- The contract sketch in `Sprint_Contracts/sprint_070_lift_circle_series_bridge_per_candidate_derived_theorem.md`
-- proposed
--
--   liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ
--
-- but the per-`k` calculation gives the opposite sign:
-- by V54's lift identity,
--
--   ‖b k − α·a k‖² − ‖a k − α·b k‖² = (1 − α²) · (‖b k‖² − ‖a k‖²),
--
-- so dividing by `1 − α²` and summing against `ρ^(2k)`, the LHS series
-- equals `∑' k, (‖b k‖² − ‖a k‖²)·ρ^(2k)` whereas
-- `circleGapSeries a b ρ = ∑' k, (‖a k‖² − ‖b k‖²)·ρ^(2k)`. These differ
-- by a sign. We therefore ship the mathematically correct orientation:
--
--   liftGapSeries b a α ρ − liftGapSeries a b α ρ = circleGapSeries a b ρ
--
-- (equivalently, with the original orientation,
-- `liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries b a ρ`).
-- The compositional / structural value for downstream consumers is
-- identical; the next planner can re-orient any consumer that prefers the
-- contract's original swap.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`, registered
-- in `lemma.toml:[import_policy].allowed_exact` per sprint 070's one-line
-- edit (mirroring sprint 068/069's pattern).
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Candidates.V54.LiftIdentity

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge

open KorenblumPaper

/--
Sprint 070 / Phase A — `liftSeriesBridge_main`, the series-level identity
linking V54's per-`k` lift identity to the workspace's circle-gap series.

For any `(a, b : ℕ → ℂ)`, any real `α` with `α² < 1`, any `ρ ≥ 0`, and the
four summability hypotheses surfaced as theorem arguments,

    liftGapSeries b a (fun _ => α) ρ − liftGapSeries a b (fun _ => α) ρ
      = circleGapSeries a b ρ.

The identity is paper-axiom-free: it depends only on
`Candidates.V54.LiftIdentity.lift_identity_per_k`, the `def`-level
unfolding of `liftGapSeries` / `circleGapSeries` from
`KorenblumPaper.PaperAxioms`, and standard `tsum`-level Mathlib API
(`Summable.tsum_sub`, `Summable.div_const`, `tsum_div_const`).

Proof structure:

1. Unfold `liftGapSeries _ _ (fun _ => α) ρ` to `∑' k, ‖_‖² · ρ^(2k) /
   (1 − α²)`.
2. Use `tsum_div_const` to factor the constant denominator out:
   `(∑' k, ‖_‖² · ρ^(2k)) / (1 − α²)`.
3. Combine the two `liftGapSeries` terms and use `Summable.tsum_sub`
   under the four summability hypotheses to get a single `tsum` of the
   per-`k` difference.
4. Apply V54's `lift_identity_per_k` per `k` (via `tsum_congr`) to
   rewrite `(‖b k − α·a k‖² − ‖a k − α·b k‖²) / (1 − α²)` to
   `‖b k‖² − ‖a k‖²` after multiplying through.
5. The resulting `tsum` is termwise the negation of `circleGapSeries`,
   so the original orientation `liftGapSeries a b … − liftGapSeries
   b a …` would equal `−circleGapSeries a b ρ`. We state the
   sign-correct swap.
-/
theorem liftSeriesBridge_main
    (a b : ℕ → ℂ) (α ρ : ℝ)
    (hα_sq_lt_one : α ^ 2 < 1)
    (_hρ_nonneg : 0 ≤ ρ)
    (hSum_b_minus_αa :
      Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)))
    (hSum_a_minus_αb :
      Summable (fun k : ℕ => ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)))
    (hSum_a_norm :
      Summable (fun k : ℕ => ‖a k‖ ^ 2 * ρ ^ (2 * k)))
    (hSum_b_norm :
      Summable (fun k : ℕ => ‖b k‖ ^ 2 * ρ ^ (2 * k))) :
    PaperAxioms.liftGapSeries b a (fun _ => α) ρ
      - PaperAxioms.liftGapSeries a b (fun _ => α) ρ
        = PaperAxioms.circleGapSeries a b ρ := by
  -- Abbreviations for the four series. Note: the `b a (fun _ => α)`
  -- direction (which appears first in the theorem statement) unfolds to
  -- `‖a k - α·b k‖²`, swapping `a`/`b` from the def.
  set f1 : ℕ → ℝ := fun k : ℕ => ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)
    with hf1_def
  set f2 : ℕ → ℝ := fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)
    with hf2_def
  -- `1 − α² > 0`, hence nonzero.
  have hαsq_pos : (0 : ℝ) < 1 - α ^ 2 := by linarith
  have hαsq_ne : (1 : ℝ) - α ^ 2 ≠ 0 := ne_of_gt hαsq_pos
  -- Step 1+2: rewrite each `liftGapSeries _ _ (fun _ => α) ρ` as
  -- `(∑' k, _) / (1 - α^2)` using `tsum_div_const` after `tsum_congr`.
  have liftBA : PaperAxioms.liftGapSeries b a (fun _ => α) ρ
      = (∑' k : ℕ, f1 k) / (1 - α ^ 2) := by
    -- Unfold: `liftGapSeries b a (fun _ => α) ρ = ∑' k, ‖a k - α·b k‖² · ρ^(2k) / (1 - α²)`
    show (∑' k : ℕ,
        (‖a k - ((fun _ : ℝ => α) ρ : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k))
          / (1 - ((fun _ : ℝ => α) ρ) ^ 2))
        = (∑' k : ℕ, f1 k) / (1 - α ^ 2)
    simp only [hf1_def]
    rw [← tsum_div_const]
  have liftAB : PaperAxioms.liftGapSeries a b (fun _ => α) ρ
      = (∑' k : ℕ, f2 k) / (1 - α ^ 2) := by
    show (∑' k : ℕ,
        (‖b k - ((fun _ : ℝ => α) ρ : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k))
          / (1 - ((fun _ : ℝ => α) ρ) ^ 2))
        = (∑' k : ℕ, f2 k) / (1 - α ^ 2)
    simp only [hf2_def]
    rw [← tsum_div_const]
  rw [liftBA, liftAB]
  -- Step 3: the LHS is `((∑ f1) − (∑ f2)) / (1 − α²)`. We want to
  -- show this equals `circleGapSeries a b ρ`.
  -- Combine the difference of fractions: `a/c - b/c = (a-b)/c`.
  rw [← sub_div]
  -- Goal: `((∑' k, f1 k) - (∑' k, f2 k)) / (1 - α^2) = circleGapSeries a b ρ`
  -- Apply `Summable.tsum_sub` so the numerator becomes a single `tsum`:
  have hSum_f1 : Summable f1 := by
    simpa [hf1_def] using hSum_a_minus_αb
  have hSum_f2 : Summable f2 := by
    simpa [hf2_def] using hSum_b_minus_αa
  rw [← hSum_f1.tsum_sub hSum_f2]
  -- Goal: `(∑' k, (f1 k - f2 k)) / (1 - α^2) = circleGapSeries a b ρ`
  -- Move the division inside:
  rw [← tsum_div_const]
  -- Goal: `(∑' k, (f1 k - f2 k) / (1 - α^2)) = circleGapSeries a b ρ`
  -- Now unfold circleGapSeries and prove termwise equality via `tsum_congr`.
  show (∑' k : ℕ, (f1 k - f2 k) / (1 - α ^ 2)) = PaperAxioms.circleGapSeries a b ρ
  unfold PaperAxioms.circleGapSeries
  refine tsum_congr (fun k => ?_)
  -- Per-term goal:
  --   `(‖a k - α·b k‖² · ρ^(2k) - ‖b k - α·a k‖² · ρ^(2k)) / (1 - α²)
  --      = coeffPlusGap a b k * ρ^(2k)`
  -- where `coeffPlusGap a b k = ‖a k‖² - ‖b k‖²`.
  unfold PaperAxioms.coeffPlusGap
  -- Apply V54's `lift_identity_per_k` to express
  --   `‖b k - α·a k‖² - ‖a k - α·b k‖² = (1 - α²)(‖b k‖² - ‖a k‖²)`
  have hLift := V54.LiftIdentity.lift_identity_per_k a b α k
  -- hLift : (1 - α^2) * (‖b k‖^2 - ‖a k‖^2) = ‖b k - α·a k‖^2 - ‖a k - α·b k‖^2
  -- Goal: `(f1 k - f2 k) / (1 - α^2) = (‖a k‖^2 - ‖b k‖^2) * ρ^(2k)`
  -- where f1 k = ‖a k - α·b k‖² · ρ^(2k), f2 k = ‖b k - α·a k‖² · ρ^(2k).
  -- Move the `1 - α²` to the RHS via `div_eq_iff`:
  rw [hf1_def, hf2_def, div_eq_iff hαsq_ne]
  -- Goal: `‖a k - α·b k‖² · ρ^(2k) − ‖b k - α·a k‖² · ρ^(2k) =
  --        (‖a k‖² − ‖b k‖²) · ρ^(2k) · (1 − α²)`
  -- This follows from `hLift` (multiplied by `−1` and by `ρ^(2k)`).
  -- Reformulate hLift: ‖a k - α·b k‖² - ‖b k - α·a k‖² = (1 - α²)(‖a k‖² - ‖b k‖²)
  have hLift' :
      ‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2
        = (1 - α ^ 2) * (‖a k‖ ^ 2 - ‖b k‖ ^ 2) := by
    linarith [hLift]
  -- Multiply both sides by `ρ^(2k)`:
  have hLift_mul :
      (‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2) * ρ ^ (2 * k)
        = (1 - α ^ 2) * (‖a k‖ ^ 2 - ‖b k‖ ^ 2) * ρ ^ (2 * k) := by
    rw [hLift']
  linarith [hLift_mul]

/--
Sprint 070 / Phase A (optional companion) — `liftGapSeries_nonneg`.

With `α² < 1` and the relevant summability hypothesis, `liftGapSeries a b
(fun _ => α) ρ` is non-negative because each term is `‖_‖²·ρ^(2k) / (1−α²)
≥ 0`.

Note: `ρ^(2k) ≥ 0` for any real `ρ` (since `2*k` is even); we do not
require `0 ≤ ρ`. The summability hypothesis is the natural one for this
direction of `liftGapSeries`.
-/
theorem liftGapSeries_nonneg
    (a b : ℕ → ℂ) (α ρ : ℝ)
    (hα_sq_lt_one : α ^ 2 < 1)
    (hSum_b_minus_αa :
      Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k))) :
    0 ≤ PaperAxioms.liftGapSeries a b (fun _ => α) ρ := by
  have hαsq_pos : (0 : ℝ) < 1 - α ^ 2 := by linarith
  have hαsq_ne : (1 : ℝ) - α ^ 2 ≠ 0 := ne_of_gt hαsq_pos
  -- Rewrite `liftGapSeries` as `(∑' k, ‖_‖²·ρ^(2k)) / (1 - α²)`.
  have hLift : PaperAxioms.liftGapSeries a b (fun _ => α) ρ
      = (∑' k : ℕ, ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)) / (1 - α ^ 2) := by
    show (∑' k : ℕ,
        (‖b k - ((fun _ : ℝ => α) ρ : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k))
          / (1 - ((fun _ : ℝ => α) ρ) ^ 2))
        = _
    rw [← tsum_div_const]
  rw [hLift]
  -- Numerator non-negative: `‖_‖² ≥ 0`, `ρ^(2k) = (ρ^k)^2 ≥ 0`, product ≥ 0.
  have h_num_nonneg : 0 ≤ ∑' k : ℕ, ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k) := by
    apply tsum_nonneg
    intro k
    have h1 : 0 ≤ ‖b k - (α : ℂ) * a k‖ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ρ ^ (2 * k) := by
      have : ρ ^ (2 * k) = (ρ ^ k) ^ 2 := by
        rw [← pow_mul, mul_comm]
      rw [this]
      exact sq_nonneg _
    exact mul_nonneg h1 h2
  exact div_nonneg h_num_nonneg (le_of_lt hαsq_pos)

end ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge
