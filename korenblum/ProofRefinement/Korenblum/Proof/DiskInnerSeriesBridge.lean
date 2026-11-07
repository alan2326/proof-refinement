-- Sprint 096: hoisted from `Candidates/V63/DiskInnerSeriesBridge.lean`
-- (originally Sprint 082, Phase A) for shared reuse across V62, V64-V68,
-- and any future candidate that needs the
-- `diskExcess (circleGap a b) c = innerSeriesExcess a b c` bridge.
--
-- The hoist is structural and score-neutral: the file's mathematical
-- content (five `theorem`s, no `axiom`s, no `sorry`s) is preserved
-- byte-for-byte modulo namespace and import-line rewrites. The trust
-- surface is unchanged conjunct-for-conjunct: the module remains
-- paper-axiom-free, drawing only on `KorenblumPaper.PaperAxioms`,
-- `KorenblumPaper.OneModePaperBridge` (transitively pulling in
-- `OneModeSeries`), `ProofRefinement.Korenblum.Proof.Reduction`
-- (sprint 042's `diskExcess_eq_tsum_via_termwise_integration`), and
-- Mathlib. The original V63 per-candidate file at
-- `Candidates/V63/DiskInnerSeriesBridge.lean` is reduced to a thin
-- re-export shim under the same per-candidate namespace
-- `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`,
-- which preserves backward compatibility for V63's existing imports.
--
-- This file ships five target theorems (no `axiom`s, no `sorry`s):
--
--   1. `coeffPlusGap_eq_plusSeq_sub_minusSeq` — per-`k` algebraic
--      identity `coeffPlusGap a b k = plusSeq a b k − minusSeq a b k`,
--      proved by a three-case `by_cases` on `n1Pred`/`n2Pred`.
--   2. `coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted`
--      — termwise multiplication of theorem 1 by the disk weight
--      `c^(2k+2) / (k+1)`.
--   3. `summable_coeffPlusGap_weighted_of_summable_components` and the
--      absolute-value variant
--      `summable_abs_coeffPlusGap_weighted_of_summable_components` —
--      summability corollaries lifting sprint 081's two summability
--      shapes to the gap-weighted series. The absolute-value variant
--      discharges sprint 042's `Summable_int_norm` hypothesis on
--      `diskExcess_eq_tsum_via_termwise_integration`.
--   4. `diskExcess_eq_innerSeriesExcess` — the bridge equality
--      `diskExcess (circleGap a b) c = innerSeriesExcess a b c`,
--      composing sprint 042's identity with theorem 2 + `tsum_sub` +
--      definitional unfold of `diskWeightedSeq` and `innerSeriesExcess`.
--   5. `diskExcess_le_innerSeriesExcess` — the `≤` corollary in the
--      exact `h_witness`-cell shape consumed by the reducer.
--
-- ### The bridge's analytic content
--
-- The chain of equalities (paper-axiom-free):
--
--   diskExcess (circleGap a b) c
--     = ∑' k, coeffPlusGap a b k * c^(2k+2) / (k+1)        [sprint 042]
--     = ∑' k, (plusSeq − minusSeq) a b k * c^(2k+2) / (k+1) [theorem 1]
--     = ∑' k, plusSeq * w − ∑' k, minusSeq * w              [tsum_sub]
--     = diskWeightedSeq (plusSeq a b) c −
--         diskWeightedSeq (minusSeq a b) c
--     = innerSeriesExcess a b c                             [unfold]
--
-- ### Why the per-`k` identity holds
--
-- For each `k`, exactly one of three cases applies:
--   * `k = 0`: `n1Pred` holds (left disjunct `k = 0`); `n2Pred` fails
--     (`0 < 0` is false). `plusSeq a b 0 = coeffPlusGap a b 0`,
--     `minusSeq a b 0 = 0`.
--   * `k ≥ 1` and `‖a k‖ ≥ ‖b k‖`: `n1Pred` holds via right disjunct;
--     `n2Pred` fails (`‖a k‖ < ‖b k‖` is false). `plusSeq = coeffPlusGap`,
--     `minusSeq = 0`.
--   * `k ≥ 1` and `‖a k‖ < ‖b k‖`: `n1Pred` fails (both disjuncts fail);
--     `n2Pred` holds. `plusSeq = 0`, `minusSeq = coeffMinusGap =
--     -coeffPlusGap`.
--
-- In every case `coeffPlusGap a b k = plusSeq a b k − minusSeq a b k`.
--
-- ### Hypothesis envelope
--
-- The proofs draw only on:
--
--   * `KorenblumPaper.PaperAxioms` (definitions of `n1Pred`, `n2Pred`,
--     `coeffPlusGap`, `coeffMinusGap`, `diskExcess`, `circleGap`),
--   * `KorenblumPaper.OneModePaperBridge` (definitions of `plusSeq`,
--     `minusSeq`, `innerSeriesExcess`),
--   * `KorenblumPaper.OneModeSeries` (definition of `diskWeightedSeq`,
--     transitively pulled in by `OneModePaperBridge`),
--   * `ProofRefinement.Korenblum.Proof.Reduction` (sprint 042's
--     `diskExcess_eq_tsum_via_termwise_integration`),
--   * Mathlib's `Summable.sub`, `Summable.congr`,
--     `Summable.tsum_sub`, `tsum_congr`, `Summable.of_norm_bounded` API.
--
-- No new `axiom`s. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`, which is
-- already covered by the existing `[import_policy].allowed_prefixes`
-- entry `ProofRefinement.Korenblum.Proof` (lemma.toml line 54-55).

import Mathlib
import KorenblumPaper.PaperAxioms
import KorenblumPaper.OneModePaperBridge
import ProofRefinement.Korenblum.Proof.Reduction

open scoped BigOperators

noncomputable section

namespace ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge

open KorenblumPaper

/-!
### Theorem 1 — per-`k` algebraic identity

`coeffPlusGap a b k = plusSeq a b k − minusSeq a b k` for all `k : ℕ`,
proved by a three-case `by_cases` on `n1Pred`/`n2Pred`. This is the
load-bearing per-`k` identity underneath the `tsum`-level bridge.
-/

/-- Per-`k` algebraic identity:
`coeffPlusGap a b k = plusSeq a b k − minusSeq a b k`.

Proof structure: three-case `by_cases`.
  * `k = 0`: `n1Pred` holds (left disjunct `k = 0`), `n2Pred` fails.
  * `k ≥ 1, ‖a k‖ ≥ ‖b k‖`: `n1Pred` holds (right disjunct), `n2Pred`
    fails.
  * `k ≥ 1, ‖a k‖ < ‖b k‖`: `n1Pred` fails (both disjuncts fail),
    `n2Pred` holds. Closes via `coeffMinusGap = -coeffPlusGap`. -/
theorem coeffPlusGap_eq_plusSeq_sub_minusSeq
    (a b : ℕ → ℂ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k =
      OneModePaperBridge.plusSeq a b k -
        OneModePaperBridge.minusSeq a b k := by
  classical
  by_cases hk0 : k = 0
  · -- Case 1: k = 0. n1Pred holds via left disjunct, n2Pred fails.
    subst hk0
    have hN1 : PaperAxioms.n1Pred a b 0 := Or.inl rfl
    have hN2_neg : ¬ PaperAxioms.n2Pred a b 0 := by
      rintro ⟨h, _⟩
      exact absurd h (lt_irrefl 0)
    simp [OneModePaperBridge.plusSeq, OneModePaperBridge.minusSeq,
      if_pos hN1, if_neg hN2_neg]
  · -- Case 2 or 3: k ≥ 1.
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hba : ‖b k‖ ≤ ‖a k‖
    · -- Case 2: ‖a k‖ ≥ ‖b k‖. n1Pred holds via right disjunct,
      -- n2Pred fails.
      have hN1 : PaperAxioms.n1Pred a b k := Or.inr hba
      have hN2_neg : ¬ PaperAxioms.n2Pred a b k := by
        rintro ⟨_, hlt⟩
        exact absurd hlt (not_lt.mpr hba)
      simp [OneModePaperBridge.plusSeq, OneModePaperBridge.minusSeq,
        if_pos hN1, if_neg hN2_neg]
    · -- Case 3: ‖a k‖ < ‖b k‖. n1Pred fails (both disjuncts fail),
      -- n2Pred holds.
      push_neg at hba
      have hN1_neg : ¬ PaperAxioms.n1Pred a b k := by
        rintro (h | h)
        · exact hk0 h
        · exact absurd hba (not_lt.mpr h)
      have hN2 : PaperAxioms.n2Pred a b k := ⟨hk_pos, hba⟩
      simp only [OneModePaperBridge.plusSeq, OneModePaperBridge.minusSeq,
        if_neg hN1_neg, if_pos hN2]
      -- Goal: coeffPlusGap a b k = 0 - coeffMinusGap a b k.
      unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
      ring

/-!
### Theorem 2 — termwise weighted identity

Multiplying theorem 1 by the disk weight `c^(2k+2) / (k+1)` gives the
per-`k` identity in the exact shape consumed by `tsum_congr` in the
bridge proof.
-/

/-- Termwise weighted identity:
`coeffPlusGap a b k * c^(2k+2) / (k+1) =
  plusSeq * w − minusSeq * w`.

Direct multiplication of theorem 1 by `c^(2k+2) / (k+1)`. -/
theorem coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted
    (a b : ℕ → ℂ) (c : ℝ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1) =
      OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) -
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) := by
  have h := coeffPlusGap_eq_plusSeq_sub_minusSeq a b k
  rw [h]
  ring

/-!
### Theorem 3 — summability corollaries

The summability of the gap-weighted series follows from the summability
of the two component series via `Summable.sub` plus `Summable.congr`
through theorem 2's per-`k` identity.

The absolute-value variant — required by sprint 042's
`diskExcess_eq_tsum_via_termwise_integration` — follows from the
pointwise bound `|coeffPlusGap| ≤ |plusSeq| + |minusSeq|` plus the
two component summabilities, via `Summable.of_norm_bounded`.
-/

/-- Summability of the gap-weighted series, derived from the two
component summabilities via theorem 2's per-`k` identity. -/
theorem summable_coeffPlusGap_weighted_of_summable_components
    {a b : ℕ → ℂ} {c : ℝ}
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    Summable (fun k : ℕ =>
      PaperAxioms.coeffPlusGap a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
  -- (plusSeq * w) - (minusSeq * w) is summable.
  have hSub : Summable (fun k : ℕ =>
      OneModePaperBridge.plusSeq a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1) -
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
    hPlusDisk.sub hMinusDisk
  -- And it equals coeffPlusGap * w pointwise.
  refine hSub.congr ?_
  intro k
  symm
  exact coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted a b c k

/-- Pointwise bound on the absolute coefficient gap by the absolute
component sequences. -/
private lemma abs_coeffPlusGap_le_abs_plusSeq_add_abs_minusSeq
    (a b : ℕ → ℂ) (k : ℕ) :
    |PaperAxioms.coeffPlusGap a b k| ≤
      |OneModePaperBridge.plusSeq a b k| +
        |OneModePaperBridge.minusSeq a b k| := by
  have h := coeffPlusGap_eq_plusSeq_sub_minusSeq a b k
  rw [h]
  calc |OneModePaperBridge.plusSeq a b k -
            OneModePaperBridge.minusSeq a b k|
      ≤ |OneModePaperBridge.plusSeq a b k| +
          |OneModePaperBridge.minusSeq a b k| := abs_sub _ _

/-- Summability of the **absolute-value** gap-weighted series, derived
from the two component summabilities via the pointwise bound
`|coeffPlusGap| ≤ |plusSeq| + |minusSeq|`. This shape is required by
sprint 042's `diskExcess_eq_tsum_via_termwise_integration`. -/
theorem summable_abs_coeffPlusGap_weighted_of_summable_components
    {a b : ℕ → ℂ} {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    Summable (fun k : ℕ =>
      |PaperAxioms.coeffPlusGap a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
  -- Build summable envelope (|plusSeq| + |minusSeq|) * c^(2k+2)/(k+1).
  -- Strategy: hPlusDisk.abs is `Summable (fun k => |plusSeq * w|)`; show
  -- this equals `|plusSeq| * w` pointwise via Summable.congr, since w
  -- is nonneg.
  have hAbsEqPlus : ∀ k : ℕ,
      |OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)| =
        |OneModePaperBridge.plusSeq a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) := by
    intro k
    have hpow_nonneg : 0 ≤ c ^ (2 * k + 2) := pow_nonneg hc_nonneg _
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hwnonneg : 0 ≤ c ^ (2 * k + 2) / ((k : ℝ) + 1) :=
      div_nonneg hpow_nonneg hk1_pos.le
    have hReassoc :
        OneModePaperBridge.plusSeq a b k * c ^ (2 * k + 2) /
            ((k : ℝ) + 1) =
          OneModePaperBridge.plusSeq a b k *
            (c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by ring
    rw [hReassoc, abs_mul, abs_of_nonneg hwnonneg, mul_div_assoc]
  have hAbsEqMinus : ∀ k : ℕ,
      |OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)| =
        |OneModePaperBridge.minusSeq a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) := by
    intro k
    have hpow_nonneg : 0 ≤ c ^ (2 * k + 2) := pow_nonneg hc_nonneg _
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hwnonneg : 0 ≤ c ^ (2 * k + 2) / ((k : ℝ) + 1) :=
      div_nonneg hpow_nonneg hk1_pos.le
    have hReassoc :
        OneModePaperBridge.minusSeq a b k * c ^ (2 * k + 2) /
            ((k : ℝ) + 1) =
          OneModePaperBridge.minusSeq a b k *
            (c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by ring
    rw [hReassoc, abs_mul, abs_of_nonneg hwnonneg, mul_div_assoc]
  have hAbsPlus : Summable (fun k : ℕ =>
      |OneModePaperBridge.plusSeq a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
    hPlusDisk.abs.congr hAbsEqPlus
  have hAbsMinus : Summable (fun k : ℕ =>
      |OneModePaperBridge.minusSeq a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
    hMinusDisk.abs.congr hAbsEqMinus
  have hEnvelope : Summable (fun k : ℕ =>
      (|OneModePaperBridge.plusSeq a b k| +
          |OneModePaperBridge.minusSeq a b k|) *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
    -- Equal to hAbsPlus + hAbsMinus pointwise.
    have hSum : Summable (fun k : ℕ =>
        |OneModePaperBridge.plusSeq a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) +
          |OneModePaperBridge.minusSeq a b k| *
            c ^ (2 * k + 2) / ((k : ℝ) + 1)) := hAbsPlus.add hAbsMinus
    refine hSum.congr ?_
    intro k
    ring
  refine Summable.of_norm_bounded
    (g := fun k : ℕ =>
      (|OneModePaperBridge.plusSeq a b k| +
          |OneModePaperBridge.minusSeq a b k|) *
        c ^ (2 * k + 2) / ((k : ℝ) + 1))
    hEnvelope ?_
  intro k
  -- Norm bound.
  simp only []  -- beta-reduce the lambda in the RHS goal
  have hpow_nonneg : 0 ≤ c ^ (2 * k + 2) := pow_nonneg hc_nonneg _
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hk1_nonneg : 0 ≤ (k : ℝ) + 1 := hk1_pos.le
  have hWeight_nonneg : 0 ≤ c ^ (2 * k + 2) / ((k : ℝ) + 1) :=
    div_nonneg hpow_nonneg hk1_nonneg
  have hAbsBound :
      |PaperAxioms.coeffPlusGap a b k| ≤
        |OneModePaperBridge.plusSeq a b k| +
          |OneModePaperBridge.minusSeq a b k| :=
    abs_coeffPlusGap_le_abs_plusSeq_add_abs_minusSeq a b k
  have hAbsCoef_nonneg : 0 ≤ |PaperAxioms.coeffPlusGap a b k| := abs_nonneg _
  -- The `Summable.of_norm_bounded` goal is
  -- `‖|coeffPlusGap k| * w‖ ≤ envelope k * w`.
  -- Reassociate division and apply mul_le_mul_of_nonneg_right.
  have hLHS_eq :
      |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) /
          ((k : ℝ) + 1) =
        |PaperAxioms.coeffPlusGap a b k| *
          (c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
    ring
  have hRHS_eq :
      (|OneModePaperBridge.plusSeq a b k| +
          |OneModePaperBridge.minusSeq a b k|) *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) =
        (|OneModePaperBridge.plusSeq a b k| +
            |OneModePaperBridge.minusSeq a b k|) *
          (c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
    ring
  have hLHS_nonneg :
      0 ≤ |PaperAxioms.coeffPlusGap a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1) := by
    rw [hLHS_eq]
    exact mul_nonneg hAbsCoef_nonneg hWeight_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hLHS_nonneg, hLHS_eq, hRHS_eq]
  exact mul_le_mul_of_nonneg_right hAbsBound hWeight_nonneg

/-!
### Theorem 4 — the bridge equality

The bridge `diskExcess (circleGap a b) c = innerSeriesExcess a b c`,
composed via:
  1. sprint 042's `diskExcess_eq_tsum_via_termwise_integration` (LHS
     unfolds to `∑' k, coeffPlusGap * w`),
  2. theorem 2 lifted by `tsum_congr` (per-`k` rewrite to
     `∑' k, plusSeq * w − minusSeq * w`),
  3. `Summable.tsum_sub` (RHS splits into the two `tsum`'s),
  4. definitional unfold of `diskWeightedSeq` and `innerSeriesExcess`.
-/

/-- The bridge equality: `diskExcess (circleGap a b) c =
innerSeriesExcess a b c`.

The hypotheses `hPlusDisk` and `hMinusDisk` are sprint 081's first and
third summability shapes; `hAbsSummable` is sprint 042's
`Summable_int_norm` hypothesis. -/
theorem diskExcess_eq_innerSeriesExcess
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      OneModePaperBridge.innerSeriesExcess a b c := by
  -- Step 1: rewrite LHS via sprint 042.
  have hStep1 :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) /
            ((k : ℝ) + 1) := by
    have hAbs' : Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
      -- The forms `((k : ℝ) + 1)` and `(k + 1 : ℝ)` are defeq; the
      -- congr step simply re-indexes pointwise.
      refine hAbsSummable.congr ?_
      intro k
      ring
    have h := ProofRefinement.Korenblum.diskExcess_eq_tsum_via_termwise_integration
      a b (c := c) hc_nonneg ?_
    · -- The form `(k + 1)` and `((k : ℝ) + 1)` are defeq; `exact h`
      -- discharges directly modulo defeq.
      exact h
    · -- Discharge the absSummable hypothesis at the form sprint 042 wants.
      refine hAbs'.congr ?_
      intro k
      ring
  rw [hStep1]
  -- Step 2: rewrite per-k body via theorem 2 (in the form
  -- `coeffPlusGap*w = plusSeq*w - minusSeq*w`).
  have hStep2 :
      ∑' k : ℕ,
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) /
            ((k : ℝ) + 1) =
        ∑' k : ℕ,
          (OneModePaperBridge.plusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1) -
            OneModePaperBridge.minusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1)) := by
    apply tsum_congr
    intro k
    exact coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted a b c k
  rw [hStep2]
  -- Step 3: apply Summable.tsum_sub.
  have hStep3 :
      ∑' k : ℕ,
          (OneModePaperBridge.plusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1) -
            OneModePaperBridge.minusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1)) =
        (∑' k : ℕ,
            OneModePaperBridge.plusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1)) -
          ∑' k : ℕ,
            OneModePaperBridge.minusSeq a b k *
              c ^ (2 * k + 2) / ((k : ℝ) + 1) :=
    hPlusDisk.tsum_sub hMinusDisk
  rw [hStep3]
  -- Step 4: identify the two tsums with diskWeightedSeq invocations
  -- and unfold innerSeriesExcess.
  unfold OneModePaperBridge.innerSeriesExcess
  -- diskWeightedSeq u c := ∑' n, u n * c^(2n+2) / (n + 1 : ℝ).
  -- The (k + 1 : ℝ) vs ((k : ℝ) + 1) shape is defeq via push_cast.
  have hPlusEq :
      ∑' k : ℕ,
          OneModePaperBridge.plusSeq a b k *
            c ^ (2 * k + 2) / ((k : ℝ) + 1) =
        OneModeSeries.diskWeightedSeq
          (OneModePaperBridge.plusSeq a b) c := by
    unfold OneModeSeries.diskWeightedSeq
    apply tsum_congr
    intro k
    ring
  have hMinusEq :
      ∑' k : ℕ,
          OneModePaperBridge.minusSeq a b k *
            c ^ (2 * k + 2) / ((k : ℝ) + 1) =
        OneModeSeries.diskWeightedSeq
          (OneModePaperBridge.minusSeq a b) c := by
    unfold OneModeSeries.diskWeightedSeq
    apply tsum_congr
    intro k
    ring
  rw [hPlusEq, hMinusEq]

/-!
### Theorem 5 — the `≤` corollary

One-line corollary of theorem 4 — the equality's `le_of_eq` form.
Signature **byte-exactly matches** the
`diskExcess ≤ innerSeriesExcess` cell inside
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
predicate at `Proof/Reduction.lean:7820-7821`.
-/

/-- The `≤` corollary in the exact `h_witness`-cell shape consumed by
the `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer at
`Proof/Reduction.lean:7820-7821`. -/
theorem diskExcess_le_innerSeriesExcess
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk :
      Summable (fun k : ℕ =>
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      OneModePaperBridge.innerSeriesExcess a b c :=
  le_of_eq
    (diskExcess_eq_innerSeriesExcess hc_nonneg hPlusDisk hMinusDisk hAbsSummable)

end ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge
