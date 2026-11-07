-- Sprint 096: hoist shim. The mathematical content of this file has
-- been moved to `ProofRefinement/Korenblum/Proof/DiskInnerSeriesBridge.lean`
-- (under the namespace `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`)
-- for shared reuse across V62, V64-V68, and any future candidate
-- needing the `diskExcess (circleGap a b) c = innerSeriesExcess a b c`
-- bridge. This file is preserved as a thin re-export shim under the
-- original per-candidate namespace
-- `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`,
-- so V63's existing imports and qualified references continue to work
-- byte-for-byte without further edits to V63.lean.
--
-- Each of the five original theorems is exposed as a `theorem` alias
-- whose proof is the corresponding hoisted theorem under the new
-- `Proof.DiskInnerSeriesBridge` namespace. No `axiom`s. No `sorry`s.
-- No new mathematical content.

import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge

open scoped BigOperators

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge

open KorenblumPaper

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.coeffPlusGap_eq_plusSeq_sub_minusSeq`. -/
theorem coeffPlusGap_eq_plusSeq_sub_minusSeq
    (a b : ℕ → ℂ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k =
      OneModePaperBridge.plusSeq a b k -
        OneModePaperBridge.minusSeq a b k :=
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.coeffPlusGap_eq_plusSeq_sub_minusSeq
    a b k

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted`. -/
theorem coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted
    (a b : ℕ → ℂ) (c : ℝ) (k : ℕ) :
    PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / ((k : ℝ) + 1) =
      OneModePaperBridge.plusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) -
        OneModePaperBridge.minusSeq a b k *
          c ^ (2 * k + 2) / ((k : ℝ) + 1) :=
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.coeffPlusGap_weighted_eq_plusSeq_weighted_sub_minusSeq_weighted
    a b c k

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.summable_coeffPlusGap_weighted_of_summable_components`. -/
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
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.summable_coeffPlusGap_weighted_of_summable_components
    hPlusDisk hMinusDisk

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components`. -/
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
        c ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components
    hc_nonneg hPlusDisk hMinusDisk

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.diskExcess_eq_innerSeriesExcess`. -/
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
      OneModePaperBridge.innerSeriesExcess a b c :=
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.diskExcess_eq_innerSeriesExcess
    hc_nonneg hPlusDisk hMinusDisk hAbsSummable

/-- Re-export shim for the hoisted
`Proof.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess`. -/
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
  ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
    hc_nonneg hPlusDisk hMinusDisk hAbsSummable

end ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
