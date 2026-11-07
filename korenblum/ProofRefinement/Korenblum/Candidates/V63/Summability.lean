-- Sprint 098: hoist shim. The mathematical content of this file has
-- been moved to `ProofRefinement/Korenblum/Proof/Summability.lean`
-- (under the namespace `ProofRefinement.Korenblum.Proof.Summability`)
-- for shared reuse across V63-V68 and any future candidate that needs
-- the H²-to-six-shapes summability transfer kit. This file is preserved
-- as a thin re-export shim under the original per-candidate namespace
-- `ProofRefinement.Korenblum.Candidates.V63.Summability`, so V63's
-- existing imports and qualified references continue to work
-- byte-for-byte without further edits to V63.lean. Completes the V63
-- derived-theorem trio after sprint 096 (`DiskInnerSeriesBridge`) and
-- sprint 097 (`Integrability`).
--
-- Each of the seven original top-level theorems is exposed as a
-- `theorem` alias whose proof is the corresponding hoisted theorem
-- under the new `Proof.Summability` namespace. The nine helper
-- `lemma`s in the original file are referenced only inside the
-- top-level theorems' proof bodies (verified by `grep` across V64-V68
-- before the hoist) — they do not need shim aliases. No `axiom`s. No
-- `sorry`s. No new mathematical content.

import ProofRefinement.Korenblum.Proof.Summability

open scoped BigOperators

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V63.Summability

open KorenblumPaper

/-- Re-export shim for the hoisted
`Proof.Summability.summable_plus_disk_weight`. -/
theorem summable_plus_disk_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_plus_disk_weight
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.summable_plus_sigma_at_c`. -/
theorem summable_plus_sigma_at_c
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_plus_sigma_at_c
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.summable_minus_disk_weight`. -/
theorem summable_minus_disk_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_minus_disk_weight
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.summable_minus_sigma_at_c`. -/
theorem summable_minus_sigma_at_c
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_minus_sigma_at_c
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.summable_minus_kernel_weight`. -/
theorem summable_minus_kernel_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_minus_kernel_weight
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.summable_minus_sigma_uniform_on_open`. -/
theorem summable_minus_sigma_uniform_on_open
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)) :=
  ProofRefinement.Korenblum.Proof.Summability.summable_minus_sigma_uniform_on_open
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Re-export shim for the hoisted
`Proof.Summability.six_summability_shapes_from_h2`. -/
theorem six_summability_shapes_from_h2
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) ∧
    (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) :=
  ProofRefinement.Korenblum.Proof.Summability.six_summability_shapes_from_h2
    hH2_a hH2_b hc_nonneg hc_lt_one

end ProofRefinement.Korenblum.Candidates.V63.Summability
