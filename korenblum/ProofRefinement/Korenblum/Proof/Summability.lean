-- Sprint 098: hoisted from `Candidates/V63/Summability.lean`
-- (originally Sprint 081, Phase A) for shared reuse across V63-V68
-- and any future candidate that needs the H²-to-six-shapes summability
-- transfer kit. Completes the V63 derived-theorem trio after sprint 096
-- (`DiskInnerSeriesBridge`) and sprint 097 (`Integrability`).
--
-- The hoist is structural and score-neutral: the file's mathematical
-- content (seven top-level `theorem`s + nine helper `lemma`s, no
-- `axiom`s, no `sorry`s) is preserved byte-for-byte modulo namespace
-- and import-line rewrites. The trust surface is unchanged
-- conjunct-for-conjunct: the module remains paper-axiom-free, drawing
-- only on `Mathlib`, `KorenblumPaper.PaperAxioms`,
-- `KorenblumPaper.OneModePaperBridge`, all pinned in
-- `lemma.toml:[workspace_import_policy]`. The original V63 per-candidate
-- file at `Candidates/V63/Summability.lean` is reduced to a thin
-- re-export shim under the same per-candidate namespace
-- `ProofRefinement.Korenblum.Candidates.V63.Summability`, which
-- preserves backward compatibility for V63's existing imports.
--
-- This file ships **six summability transfer theorems** plus one
-- consolidation theorem (no `axiom`s, no `sorry`s). Each transfer
-- theorem takes as input a Wang H²-style hypothesis on `(a, b)`:
--
--   `hH2_a : Summable (fun n => ‖a n‖^2)`
--   `hH2_b : Summable (fun n => ‖b n‖^2)`
--
-- together with `0 ≤ c < 1`, and produces one of the six summability
-- shapes the reducer's `h_witness` predicate requires.
--
-- ### The six target shapes (Proof/Reduction.lean:7787-7803)
--
--   1. `Summable (fun n => plusSeq a b n * c^(2n+2) / (n+1))`
--   2. `Summable (fun n => plusSeq a b n * c^(2n))`
--   3. `Summable (fun n => minusSeq a b n * c^(2n+2) / (n+1))`
--   4. `Summable (fun n => minusSeq a b n * c^(2n))`
--   5. `Summable (fun n => minusSeq a b n * OneModeKernel.weight c n)`
--   6. `∀ ρ, c < ρ → ρ < 1 →
--           Summable (fun n => minusSeq a b n * ρ^(2n))`
--
-- ### Why the H² hypothesis cannot be derived from `Section2Assumptions`
--
-- The bundled `Section2Assumptions` structure does NOT carry coefficient-
-- level summability data — it states pointwise paper-faithful identities
-- and bounds (eq3, eq4, eq8, eq9, etc.) but does not assert
-- `Summable (‖a n‖^2)` / `Summable (‖b n‖^2)` (i.e. boundary-L²
-- finiteness of `f, g`). Wang's Section 2 setup implicitly assumes this
-- (the boundary functions live in H²) but it is not encoded as a field.
-- Hence the kit's transfers take H² as an INPUT hypothesis, not derive
-- it from `paper`. The V64+ c-push will need to either carry
-- `(hH2_a, hH2_b)` as candidate-side hypotheses (free axiom, expanding
-- the seed envelope by two axioms) or file proposal_004 to add H²
-- fields to `Section2Assumptions`.
--
-- ### Proof strategy per transfer (canonical template)
--
-- 1. Build `Summable (fun n => ‖a n‖^2 + ‖b n‖^2)` via `Summable.add`.
-- 2. Bound `|coeffPlusGap a b n| = | ‖a n‖^2 - ‖b n‖^2 | ≤
--    ‖a n‖^2 + ‖b n‖^2` (and similarly for `coeffMinusGap`); hence
--    `|plusSeq a b n| ≤ ‖a n‖^2 + ‖b n‖^2` and
--    `|minusSeq a b n| ≤ ‖a n‖^2 + ‖b n‖^2` (the indicator-restriction
--    only makes the LHS smaller).
-- 3. Apply the geometric / factorial weighting bound:
--    `c^(2n) ≤ 1`, `c^(2n+2)/(n+1) ≤ 1`,
--    `OneModeKernel.weight c n = (n/(n+1)) c^(2n+2) ≤ 1`,
--    `ρ^(2n) ≤ 1` for `ρ ≤ 1` — all under `0 ≤ c, ρ ≤ 1`.
-- 4. Close via `Summable.of_norm_bounded` against the H² envelope.
--
-- ### Hypothesis envelope
--
-- The proofs draw only on:
--
--   * `KorenblumPaper.PaperAxioms` (definitions of `coeffPlusGap`,
--     `coeffMinusGap`, `n1Pred`, `n2Pred`),
--   * `KorenblumPaper.OneModePaperBridge` (definitions of `plusSeq`,
--     `minusSeq` as if-then-else over the predicates above),
--   * `KorenblumPaper.OneModeKernel` (definition of `weight`),
--   * Mathlib's `Summable.of_norm_bounded`, `Summable.add`,
--     `pow_le_one₀`, `abs_*` API.
--
-- No new `axiom`s. No oracle. No edit to `KorenblumPaper/`. The file
-- lives under `ProofRefinement.Korenblum.Proof.Summability`, which is
-- allowed by the existing `[workspace_import_policy]`
-- `ProofRefinement.Korenblum.*` prefix entry; no candidate-side
-- `[import_policy]` change is needed because the new path is already
-- covered by the existing `allowed_prefixes` entry
-- `ProofRefinement.Korenblum.Proof`.
import Mathlib
import KorenblumPaper.PaperAxioms
import KorenblumPaper.OneModePaperBridge

open scoped BigOperators

noncomputable section

namespace ProofRefinement.Korenblum.Proof.Summability

open KorenblumPaper

/-!
### Common helper bounds

These lemmas factor out the shared structure of the six transfer
theorems' proofs.
-/

/-- Pointwise bound: the coefficient gap is sandwiched by the H² envelope
`‖a n‖^2 + ‖b n‖^2`. -/
lemma abs_coeffPlusGap_le_envelope (a b : ℕ → ℂ) (n : ℕ) :
    |PaperAxioms.coeffPlusGap a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := by
  unfold PaperAxioms.coeffPlusGap
  have ha : 0 ≤ ‖a n‖ ^ 2 := sq_nonneg _
  have hb : 0 ≤ ‖b n‖ ^ 2 := sq_nonneg _
  rcases le_total (‖a n‖ ^ 2) (‖b n‖ ^ 2) with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Pointwise bound: the negative coefficient gap is sandwiched by the
H² envelope `‖a n‖^2 + ‖b n‖^2`. -/
lemma abs_coeffMinusGap_le_envelope (a b : ℕ → ℂ) (n : ℕ) :
    |PaperAxioms.coeffMinusGap a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := by
  unfold PaperAxioms.coeffMinusGap
  have ha : 0 ≤ ‖a n‖ ^ 2 := sq_nonneg _
  have hb : 0 ≤ ‖b n‖ ^ 2 := sq_nonneg _
  rcases le_total (‖b n‖ ^ 2) (‖a n‖ ^ 2) with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Pointwise bound: `|plusSeq a b n| ≤ ‖a n‖^2 + ‖b n‖^2`. The
indicator restriction only makes the left side smaller (or zero). -/
lemma abs_plusSeq_le_envelope (a b : ℕ → ℂ) (n : ℕ) :
    |OneModePaperBridge.plusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := by
  classical
  unfold OneModePaperBridge.plusSeq
  by_cases hk : PaperAxioms.n1Pred a b n
  · simp only [if_pos hk]
    exact abs_coeffPlusGap_le_envelope a b n
  · simp only [if_neg hk, abs_zero]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Pointwise bound: `|minusSeq a b n| ≤ ‖a n‖^2 + ‖b n‖^2`. The
indicator restriction only makes the left side smaller (or zero). -/
lemma abs_minusSeq_le_envelope (a b : ℕ → ℂ) (n : ℕ) :
    |OneModePaperBridge.minusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := by
  classical
  unfold OneModePaperBridge.minusSeq
  by_cases hk : PaperAxioms.n2Pred a b n
  · simp only [if_pos hk]
    exact abs_coeffMinusGap_le_envelope a b n
  · simp only [if_neg hk, abs_zero]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The H² envelope `n ↦ ‖a n‖^2 + ‖b n‖^2` is summable when both
component sequences are individually summable. -/
lemma summable_h2_envelope
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2)) :
    Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
  hH2_a.add hH2_b

/-- Geometric tail bound: for `0 ≤ ρ ≤ 1` and any `n`, `ρ^(2n) ≤ 1`. -/
lemma pow_two_n_le_one
    {ρ : ℝ} (hρ_nonneg : 0 ≤ ρ) (hρ_le_one : ρ ≤ 1) (n : ℕ) :
    ρ ^ (2 * n) ≤ 1 :=
  pow_le_one₀ hρ_nonneg hρ_le_one

/-- Geometric tail bound: for `0 ≤ c ≤ 1`, `c^(2n+2) ≤ 1`. -/
lemma pow_two_n_plus_two_le_one
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) (n : ℕ) :
    c ^ (2 * n + 2) ≤ 1 :=
  pow_le_one₀ hc_nonneg hc_le_one

/-- Disk-weighted bound: for `0 ≤ c ≤ 1`,
`c^(2n+2) / (n+1 : ℝ) ≤ 1`. -/
lemma disk_weight_le_one
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) (n : ℕ) :
    c ^ (2 * n + 2) / ((n : ℝ) + 1) ≤ 1 := by
  have hpow_le_one : c ^ (2 * n + 2) ≤ 1 :=
    pow_two_n_plus_two_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n + 2) := pow_nonneg hc_nonneg _
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hn1_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- Direct: c^(2n+2) / (n+1) ≤ 1 / 1 = 1 since numerator ≤ 1 and
  -- denominator ≥ 1.
  rw [div_le_one hn1_pos]
  linarith

/-- `OneModeKernel.weight c n ≤ 1` for `0 ≤ c ≤ 1`.

`OneModeKernel.weight c n = (n / (n+1)) · c^(2n+2)` and both factors lie
in `[0, 1]` under `0 ≤ c ≤ 1`. -/
lemma weight_le_one
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) (n : ℕ) :
    OneModeKernel.weight c n ≤ 1 := by
  unfold OneModeKernel.weight
  have hpow_le_one : c ^ (2 * n + 2) ≤ 1 :=
    pow_two_n_plus_two_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n + 2) := pow_nonneg hc_nonneg _
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hratio_nonneg : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) :=
    div_nonneg hn_nonneg hn1_pos.le
  have hratio_le_one : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1_pos]
    linarith
  calc (n : ℝ) / ((n : ℝ) + 1) * c ^ (2 * n + 2)
      ≤ 1 * c ^ (2 * n + 2) := by
        exact mul_le_mul_of_nonneg_right hratio_le_one hpow_nonneg
    _ = c ^ (2 * n + 2) := by ring
    _ ≤ 1 := hpow_le_one

/-- `OneModeKernel.weight c n ≥ 0` for `0 ≤ c`. -/
lemma weight_nonneg
    {c : ℝ} (hc_nonneg : 0 ≤ c) (n : ℕ) :
    0 ≤ OneModeKernel.weight c n := by
  unfold OneModeKernel.weight
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hratio_nonneg : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) :=
    div_nonneg hn_nonneg hn1_pos.le
  have hpow_nonneg : 0 ≤ c ^ (2 * n + 2) := pow_nonneg hc_nonneg _
  exact mul_nonneg hratio_nonneg hpow_nonneg

/-!
### The six summability transfer theorems

Each takes `(hH2_a, hH2_b, hc_nonneg, hc_lt_one)` and produces one of
the six shapes from `Proof/Reduction.lean:7787-7803`.
-/

/-- Transfer 1: `plusSeq a b n * c^(2n+2) / (n+1)` is summable. -/
theorem summable_plus_disk_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) := by
  have hc_le_one : c ≤ 1 := hc_lt_one.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  -- ‖plusSeq a b n * c^(2n+2)/(n+1)‖ ≤ ‖a n‖^2 + ‖b n‖^2.
  have hWeight_le_one : c ^ (2 * n + 2) / ((n : ℝ) + 1) ≤ 1 :=
    disk_weight_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n + 2) := pow_nonneg hc_nonneg _
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hWeight_nonneg : 0 ≤ c ^ (2 * n + 2) / ((n : ℝ) + 1) :=
    div_nonneg hpow_nonneg hn1_pos.le
  have hAbsPlus : |OneModePaperBridge.plusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_plusSeq_le_envelope a b n
  have hAbsPlus_nonneg : 0 ≤ |OneModePaperBridge.plusSeq a b n| := abs_nonneg _
  have hEnv_nonneg : 0 ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  -- Compute the norm.
  have hRewrite :
      ‖OneModePaperBridge.plusSeq a b n *
          c ^ (2 * n + 2) / ((n : ℝ) + 1)‖ =
        |OneModePaperBridge.plusSeq a b n| *
          (c ^ (2 * n + 2) / ((n : ℝ) + 1)) := by
    rw [mul_div_assoc, Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_of_nonneg hc_nonneg, abs_of_nonneg hn1_pos.le]
  rw [hRewrite]
  calc |OneModePaperBridge.plusSeq a b n| *
          (c ^ (2 * n + 2) / ((n : ℝ) + 1))
      ≤ |OneModePaperBridge.plusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hWeight_le_one hAbsPlus_nonneg
    _ = |OneModePaperBridge.plusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsPlus

/-- Transfer 2: `plusSeq a b n * c^(2n)` is summable. -/
theorem summable_plus_sigma_at_c
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) := by
  have hc_le_one : c ≤ 1 := hc_lt_one.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  have hpow_le_one : c ^ (2 * n) ≤ 1 := pow_two_n_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n) := pow_nonneg hc_nonneg _
  have hAbsPlus : |OneModePaperBridge.plusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_plusSeq_le_envelope a b n
  have hAbsPlus_nonneg : 0 ≤ |OneModePaperBridge.plusSeq a b n| := abs_nonneg _
  have hRewrite :
      ‖OneModePaperBridge.plusSeq a b n * c ^ (2 * n)‖ =
        |OneModePaperBridge.plusSeq a b n| * c ^ (2 * n) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc_nonneg]
  rw [hRewrite]
  calc |OneModePaperBridge.plusSeq a b n| * c ^ (2 * n)
      ≤ |OneModePaperBridge.plusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hpow_le_one hAbsPlus_nonneg
    _ = |OneModePaperBridge.plusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsPlus

/-- Transfer 3: `minusSeq a b n * c^(2n+2) / (n+1)` is summable. -/
theorem summable_minus_disk_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) := by
  have hc_le_one : c ≤ 1 := hc_lt_one.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  have hWeight_le_one : c ^ (2 * n + 2) / ((n : ℝ) + 1) ≤ 1 :=
    disk_weight_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n + 2) := pow_nonneg hc_nonneg _
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hWeight_nonneg : 0 ≤ c ^ (2 * n + 2) / ((n : ℝ) + 1) :=
    div_nonneg hpow_nonneg hn1_pos.le
  have hAbsMinus : |OneModePaperBridge.minusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_minusSeq_le_envelope a b n
  have hAbsMinus_nonneg : 0 ≤ |OneModePaperBridge.minusSeq a b n| := abs_nonneg _
  have hRewrite :
      ‖OneModePaperBridge.minusSeq a b n *
          c ^ (2 * n + 2) / ((n : ℝ) + 1)‖ =
        |OneModePaperBridge.minusSeq a b n| *
          (c ^ (2 * n + 2) / ((n : ℝ) + 1)) := by
    rw [mul_div_assoc, Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_of_nonneg hc_nonneg, abs_of_nonneg hn1_pos.le]
  rw [hRewrite]
  calc |OneModePaperBridge.minusSeq a b n| *
          (c ^ (2 * n + 2) / ((n : ℝ) + 1))
      ≤ |OneModePaperBridge.minusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hWeight_le_one hAbsMinus_nonneg
    _ = |OneModePaperBridge.minusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsMinus

/-- Transfer 4: `minusSeq a b n * c^(2n)` is summable. -/
theorem summable_minus_sigma_at_c
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) := by
  have hc_le_one : c ≤ 1 := hc_lt_one.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  have hpow_le_one : c ^ (2 * n) ≤ 1 := pow_two_n_le_one hc_nonneg hc_le_one n
  have hpow_nonneg : 0 ≤ c ^ (2 * n) := pow_nonneg hc_nonneg _
  have hAbsMinus : |OneModePaperBridge.minusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_minusSeq_le_envelope a b n
  have hAbsMinus_nonneg : 0 ≤ |OneModePaperBridge.minusSeq a b n| := abs_nonneg _
  have hRewrite :
      ‖OneModePaperBridge.minusSeq a b n * c ^ (2 * n)‖ =
        |OneModePaperBridge.minusSeq a b n| * c ^ (2 * n) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc_nonneg]
  rw [hRewrite]
  calc |OneModePaperBridge.minusSeq a b n| * c ^ (2 * n)
      ≤ |OneModePaperBridge.minusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hpow_le_one hAbsMinus_nonneg
    _ = |OneModePaperBridge.minusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsMinus

/-- Transfer 5: `minusSeq a b n * OneModeKernel.weight c n` is summable.

`OneModeKernel.weight c n = (n/(n+1)) · c^(2n+2)` is bounded by `1`
under `0 ≤ c ≤ 1`. -/
theorem summable_minus_kernel_weight
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) := by
  have hc_le_one : c ≤ 1 := hc_lt_one.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  have hWeight_le_one : OneModeKernel.weight c n ≤ 1 :=
    weight_le_one hc_nonneg hc_le_one n
  have hWeight_nonneg : 0 ≤ OneModeKernel.weight c n :=
    weight_nonneg hc_nonneg n
  have hAbsMinus : |OneModePaperBridge.minusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_minusSeq_le_envelope a b n
  have hAbsMinus_nonneg : 0 ≤ |OneModePaperBridge.minusSeq a b n| := abs_nonneg _
  have hRewrite :
      ‖OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n‖ =
        |OneModePaperBridge.minusSeq a b n| * OneModeKernel.weight c n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWeight_nonneg]
  rw [hRewrite]
  calc |OneModePaperBridge.minusSeq a b n| * OneModeKernel.weight c n
      ≤ |OneModePaperBridge.minusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hWeight_le_one hAbsMinus_nonneg
    _ = |OneModePaperBridge.minusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsMinus

/-- Transfer 6: `ρ`-uniform shape — for any `ρ ∈ (c, 1)`,
`minusSeq a b n * ρ^(2n)` is summable.

The proof generalises `summable_minus_sigma_at_c` to arbitrary `ρ < 1`:
the geometric domination `ρ^(2n) ≤ 1` holds at any `0 ≤ ρ ≤ 1`. The
bound on `ρ` from below by `c` is not used — we only need `0 ≤ ρ` and
`ρ ≤ 1`, which follow from `0 ≤ c < ρ` and `ρ < 1`. -/
theorem summable_minus_sigma_uniform_on_open
    {a b : ℕ → ℂ}
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (_hc_lt_one : c < 1) :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)) := by
  intro ρ hcρ hρ1
  have hρ_nonneg : 0 ≤ ρ := le_of_lt (lt_of_le_of_lt hc_nonneg hcρ)
  have hρ_le_one : ρ ≤ 1 := hρ1.le
  have hEnv : Summable (fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) :=
    summable_h2_envelope hH2_a hH2_b
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖a n‖ ^ 2 + ‖b n‖ ^ 2) hEnv ?_
  intro n
  have hpow_le_one : ρ ^ (2 * n) ≤ 1 := pow_two_n_le_one hρ_nonneg hρ_le_one n
  have hpow_nonneg : 0 ≤ ρ ^ (2 * n) := pow_nonneg hρ_nonneg _
  have hAbsMinus : |OneModePaperBridge.minusSeq a b n| ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 :=
    abs_minusSeq_le_envelope a b n
  have hAbsMinus_nonneg : 0 ≤ |OneModePaperBridge.minusSeq a b n| := abs_nonneg _
  have hRewrite :
      ‖OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)‖ =
        |OneModePaperBridge.minusSeq a b n| * ρ ^ (2 * n) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ_nonneg]
  rw [hRewrite]
  calc |OneModePaperBridge.minusSeq a b n| * ρ ^ (2 * n)
      ≤ |OneModePaperBridge.minusSeq a b n| * 1 := by
        exact mul_le_mul_of_nonneg_left hpow_le_one hAbsMinus_nonneg
    _ = |OneModePaperBridge.minusSeq a b n| := by ring
    _ ≤ ‖a n‖ ^ 2 + ‖b n‖ ^ 2 := hAbsMinus

/-!
### Consolidation theorem

Bundles the six transfers into a single theorem whose conclusion's
shape **byte-exactly matches** the six summability conjuncts inside
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
predicate at `Proof/Reduction.lean:7787-7803`. The V64+ c-push sprint's
`obtain` pattern can consume this directly without re-ordering or
adapter shims.
-/

/-- Six summability shapes from the H² hypothesis pair. The output
shape matches `Proof/Reduction.lean:7787-7803` byte-exactly:

```
Summable (fun n => plusSeq a b n * c^(2n+2) / (n+1)) ∧
Summable (fun n => plusSeq a b n * c^(2n)) ∧
Summable (fun n => minusSeq a b n * c^(2n+2) / (n+1)) ∧
Summable (fun n => minusSeq a b n * c^(2n)) ∧
Summable (fun n => minusSeq a b n * OneModeKernel.weight c n) ∧
∀ ρ, c < ρ → ρ < 1 →
  Summable (fun n => minusSeq a b n * ρ^(2n))
```
-/
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
  ⟨summable_plus_disk_weight hH2_a hH2_b hc_nonneg hc_lt_one,
   summable_plus_sigma_at_c hH2_a hH2_b hc_nonneg hc_lt_one,
   summable_minus_disk_weight hH2_a hH2_b hc_nonneg hc_lt_one,
   summable_minus_sigma_at_c hH2_a hH2_b hc_nonneg hc_lt_one,
   summable_minus_kernel_weight hH2_a hH2_b hc_nonneg hc_lt_one,
   summable_minus_sigma_uniform_on_open hH2_a hH2_b hc_nonneg hc_lt_one⟩

end ProofRefinement.Korenblum.Proof.Summability
