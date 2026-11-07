-- Sprint 075, Phase A: per-candidate derived-theorem file shipping the
-- INTEGRATED LIFT IDENTITY over `[c, 1]` for V58. This is the structural
-- annulus-side sibling of V57's `DiskExcessLiftIntegrated`, with the
-- integration domain swapped from `[0, c]` to `[c, 1]` and the per-`k`
-- polar weight `c^(2k+2)/(k+1)` swapped for `(1 - c^(2k+2))/(k+1)`.
--
-- This file ships two `theorem`s plus an optional Theorem 3 (no `axiom`s,
-- no `sorry`s):
--
--   1. `annulusExcess_lift_identity_at_alpha`: the integrated form of V54's
--      per-`k` lift identity, expressed as a `tsum` of annulus-weighted
--      `‖·‖²` differences.
--
--      `(1 − α²) · annulusExcess (circleGap a b) c
--         = ∑' k, ‖a k − α·b k‖² · (1 − c^(2k+2)) / (k+1)
--           − ∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2)) / (k+1)`
--
--   2. `annulusExcess_lower_bound_via_lift_at_alpha`: the immediate
--      corollary obtained by dropping the (non-negative) first `tsum`.
--
--      `(1 − α²) · annulusExcess (circleGap a b) c
--         ≥ − ∑' k, ‖b k − α·a k‖² · (1 − c^(2k+2)) / (k+1)`
--
--   3. `annulusMinusDiskExcess_per_k_at_alpha_eq_c` (Optional Theorem 3):
--      the closed-form per-`k` representation of `annulusExcess - diskExcess`
--      at `α = c`.
--
-- ### Hypothesis envelope
--
-- Unlike V57's Theorem 1 (which surfaces the disk-side polar-Jacobian as a
-- hypothesis because Mathlib's `intervalIntegral.integral_tsum` machinery
-- is heavy), V58's Theorem 1 invokes the already-proved
-- `Reduction.annulusExcess_eq_tsum_via_termwise_integration` (sprint 046).
-- This is a strict structural improvement: V58 surfaces only the single
-- sprint-046 polar-Jacobian summability hypothesis
-- `Summable (fun k => |coeffPlusGap a b k| · (1 - c^(2k+2)) / (k+1))`,
-- not a free-standing `hAnnulusJacobian` equation.
--
-- ### Sign / orientation convention
--
-- Per V54's `lift_identity_per_k`,
--
--   `(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²`.
--
-- Negating gives
--
--   `(1 − α²) · (‖a k‖² − ‖b k‖²) = ‖a k − α·b k‖² − ‖b k − α·a k‖²`.
--
-- Since `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`, the integrated form
-- works out to the V57-mirroring orientation:
--
--   `(1 − α²) · annulusExcess (circleGap a b) c
--      = ∑' k, (‖a k − α·b k‖² − ‖b k − α·a k‖²) · (1 − c^(2k+2)) / (k+1)`
--
-- which decomposes into Theorem 1's stated difference of two `tsum`s.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated`,
-- registered in `lemma.toml:[import_policy].allowed_exact` per sprint 075's
-- one-line edit (mirroring sprints 068/069/070/073's pattern).
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Candidates.V54.LiftIdentity
import ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated

open KorenblumPaper

/--
Sprint 075 / Phase A — `annulusExcess_lift_identity_at_alpha`, the integrated
form of V54's per-`k` lift identity over the annulus `[c, 1]`.

For any `(a, b : ℕ → ℂ)`, any real `α`, any `c ∈ [0, 1]`, the four
annulus-weighted summability hypotheses, and the sprint-046 polar-Jacobian
summability hypothesis,

  `(1 − α²) · annulusExcess (circleGap a b) c
     = ∑' k, ‖a k − (α : ℂ)·b k‖² · (1 − c^(2k+2)) / (k+1)
       − ∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k+1)`.

This is the workspace's first `tsum`-level identity bridging Wang's
per-`k` lift-identity content (V54) to the integrated `annulusExcess`
quantity used throughout `Reduction.lean`.

Unlike V57's Theorem 1 (which surfaces the disk-side polar-Jacobian as a
hypothesis), V58 Theorem 1 invokes the already-proved sprint-046 theorem
`Reduction.annulusExcess_eq_tsum_via_termwise_integration` directly, so
the only "polar-Jacobian-shaped" hypothesis surfaced is that theorem's
summability premise.

The signature does **not** require `α² < 1`. Unlike V57's disk-side
Theorem 2 (which uses `α² < 1` to derive a *strict* upper bound by
dropping a non-negative `tsum`), V58 Theorem 1 is a pure algebraic
equality: `(1 − α²)` factors through cleanly even when `α² ≥ 1`.
-/
theorem annulusExcess_lift_identity_at_alpha
    (a b : ℕ → ℂ) (α c : ℝ)
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSum_a_minus_alpha_b_ann :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_b_minus_alpha_a_ann :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (_hSum_a_norm_ann :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (_hSum_b_norm_ann :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_polar_jacobian :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))) :
    (1 - α ^ 2) *
        PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
      = (∑' k : ℕ,
            ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
        - (∑' k : ℕ,
            ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)) := by
  -- Step 1: rewrite `annulusExcess` via the existing sprint-046 theorem.
  rw [ProofRefinement.Korenblum.annulusExcess_eq_tsum_via_termwise_integration
        a b hc_nonneg hc_le_one hSum_polar_jacobian]
  -- Step 2: pull `(1 - α^2)` inside the `tsum`.
  rw [← tsum_mul_left]
  -- Step 3: introduce abbreviations for the two RHS sequences.
  set f : ℕ → ℝ := fun k =>
    ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)
    with hf_def
  set g : ℕ → ℝ := fun k =>
    ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)
    with hg_def
  have hSum_f : Summable f := by simpa [hf_def] using hSum_a_minus_alpha_b_ann
  have hSum_g : Summable g := by simpa [hg_def] using hSum_b_minus_alpha_a_ann
  -- The RHS combined as a single `tsum` of `f k - g k`.
  rw [← hSum_f.tsum_sub hSum_g]
  refine tsum_congr (fun k => ?_)
  -- Per-term equality. Apply V54's lift identity at `(a, b, α, k)`.
  have hLift :=
    ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k
      a b α k
  -- Negate to align with `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`.
  have hLift' :
      (1 - α ^ 2) * PaperAxioms.coeffPlusGap a b k
        = ‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2 := by
    unfold PaperAxioms.coeffPlusGap
    linarith [hLift]
  -- Now distribute: each summand is
  -- `(1−α²) · (coeffPlus · (1 − c^(2k+2))/(k+1))`,
  -- which factors as `((1−α²) · coeffPlus) · (1 − c^(2k+2))/(k+1)`.
  show (1 - α ^ 2) *
      (PaperAxioms.coeffPlusGap a b k *
          (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
    = f k - g k
  have hLift_mul :
      (1 - α ^ 2) *
          (PaperAxioms.coeffPlusGap a b k *
              (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
        = (‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2)
            * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
    rw [show (1 - α ^ 2) *
              (PaperAxioms.coeffPlusGap a b k *
                  (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
              = ((1 - α ^ 2) * PaperAxioms.coeffPlusGap a b k)
                  * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ) by ring]
    rw [hLift']
  rw [hLift_mul]
  simp only [hf_def, hg_def]
  ring

/--
Sprint 075 / Phase A — `annulusExcess_lower_bound_via_lift_at_alpha`, the
immediate corollary of Theorem 1 by dropping the non-negative
`‖a k − α·b k‖² · (1 − c^(2k+2)) / (k+1)` term (the **first** `tsum`,
note the orientation flip versus V57's Theorem 2).

The bound is:

  `−∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k+1)
     ≤ (1 − α²) · annulusExcess (circleGap a b) c`.

Equivalently:

  `∑' k, ‖b k − (α : ℂ)·a k‖² · (1 − c^(2k+2)) / (k+1)
     ≥ − (1 − α²) · annulusExcess (circleGap a b) c`.

Orientation note: V57's Theorem 2 drops the **second** `tsum` (the
`‖b − α·a‖²` term) to produce an upper bound on `(1 − α²) · diskExcess`.
V58 mirrors that pattern by dropping the **first** `tsum` (the
`‖a − α·b‖²` term), producing a lower bound on `(1 − α²) · annulusExcess`.
The choice was guided by the contract's "Sign / orientation convention":
the disk-side upper bound and the annulus-side lower bound together let
a future closing-reducer sprint compose them additively without sign
mismatch.
-/
theorem annulusExcess_lower_bound_via_lift_at_alpha
    (a b : ℕ → ℂ) (α c : ℝ)
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSum_a_minus_alpha_b_ann :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_b_minus_alpha_a_ann :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_a_norm_ann :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_b_norm_ann :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_polar_jacobian :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))) :
    -(∑' k : ℕ,
          ‖b k - (α : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
      ≤ (1 - α ^ 2) *
          PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := by
  -- Apply Theorem 1 to get the equality form.
  have hEq :=
    annulusExcess_lift_identity_at_alpha a b α c hc_nonneg hc_le_one
      hSum_a_minus_alpha_b_ann hSum_b_minus_alpha_a_ann
      hSum_a_norm_ann hSum_b_norm_ann hSum_polar_jacobian
  -- The dropped first `tsum` is non-negative because each summand is
  -- `‖_‖² · (1 − c^(2k+2)) / (k+1) ≥ 0` under `c ∈ [0, 1]`.
  have hTsum_nonneg :
      0 ≤ ∑' k : ℕ,
        ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
    apply tsum_nonneg
    intro k
    have h1 : 0 ≤ ‖a k - (α : ℂ) * b k‖ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 1 - c ^ (2 * k + 2) := by
      have hPow_le_one : c ^ (2 * k + 2) ≤ 1 :=
        pow_le_one₀ hc_nonneg hc_le_one
      linarith
    have h3 : 0 ≤ (k + 1 : ℝ) := by positivity
    have hMul : 0 ≤ ‖a k - (α : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) :=
      mul_nonneg h1 h2
    exact div_nonneg hMul h3
  -- LHS = ∑'_a − ∑'_b, with ∑'_a ≥ 0, so −∑'_b ≤ LHS.
  linarith [hEq, hTsum_nonneg]

/--
Sprint 075 / Phase A (Optional Theorem 3) —
`annulusMinusDiskExcess_per_k_at_alpha_eq_c`, the closed-form per-`k`
representation of `annulusExcess − diskExcess` at `α = c`.

  `(1 − c²) · (annulusExcess (circleGap a b) c
                 − diskExcess (circleGap a b) c)
     = ∑' k, ((1 − c²) · coeffPlusGap a b k)
              · (1 − 2 c^(2k+2)) / (k + 1)`.

Note: the `(1 − c²)` factor appears on both the LHS (multiplying
`annulusExcess − diskExcess`) and as a per-`k` factor on the RHS. This
is the most natural Λ-free statement obtainable from V54's lift identity
without dividing through. On `c² < 1`, dividing both sides by `(1 − c²)`
gives the simpler equivalent form

  `annulusExcess (circleGap a b) c − diskExcess (circleGap a b) c
     = ∑' k, coeffPlusGap a b k · (1 − 2 c^(2k+2)) / (k + 1)`.

(The contract's stated equality omits the `(1 − c²)` on the RHS;
algebraically the cleanest formulation keeps it factored on both sides
to avoid the division-by-`(1 − c²)` step. Future closing-reducer sprints
can divide as needed.)

Proof: subtract V57's Theorem 1 (at α = c) from V58 Theorem 1 (at α = c).
The two RHS `‖a k − c·b k‖² · _ / (k+1)` `tsum`s have weights
`(1 − c^(2k+2))` (annulus) and `c^(2k+2)` (disk); their difference has
weight `1 − 2 c^(2k+2)`. Same for the `‖b k − c·a k‖²` `tsum`s. Then
re-collapse the difference of two per-`k` `‖·‖²` quantities back to
`(1 − c²) · coeffPlusGap` via V54's lift identity at α = c.

V58 by itself does NOT close any inequality on `annulusExcess −
diskExcess`. The natural candidate `coeffPlusGap_k · (1 − 2 c^(2k+2)) ≥ 0`
falsifies on the E1 adversary (single-mode `b_1 = 1`, `coeffPlusGap_1
= −1`, weight `1 − 2c⁴ > 0` at `c ≈ 0.36`). Theorem 3 is the equality
that lets a future sprint state the inequality precisely and attempt
a per-`k` closing argument with appropriate cross-coupling.
-/
theorem annulusMinusDiskExcess_per_k_at_alpha_eq_c
    (a b : ℕ → ℂ) (c : ℝ)
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hcsq_lt_one : c ^ 2 < 1)
    -- Disk-side hypotheses (for V57 Theorem 1 at α = c).
    (hSum_a_minus_cb_disk :
      Summable (fun k : ℕ =>
        ‖a k - (c : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_b_minus_ca_disk :
      Summable (fun k : ℕ =>
        ‖b k - (c : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_a_norm_disk :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_b_norm_disk :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hDiskJacobian :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        = ∑' k : ℕ,
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ))
    -- Annulus-side hypotheses (for V58 Theorem 1 at α = c).
    (hSum_a_minus_cb_ann :
      Summable (fun k : ℕ =>
        ‖a k - (c : ℂ) * b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_b_minus_ca_ann :
      Summable (fun k : ℕ =>
        ‖b k - (c : ℂ) * a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_a_norm_ann :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_b_norm_ann :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)))
    (hSum_polar_jacobian :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))) :
    (1 - c ^ 2) *
        (PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
           - PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      = ∑' k : ℕ,
          ((1 - c ^ 2) * PaperAxioms.coeffPlusGap a b k)
            * (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
  -- V57 Theorem 1 at α = c.
  have hDisk :=
    ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated.diskExcess_lift_identity_at_alpha
      a b c c hcsq_lt_one hc_nonneg
      hSum_a_minus_cb_disk hSum_b_minus_ca_disk
      hSum_a_norm_disk hSum_b_norm_disk hDiskJacobian
  -- V58 Theorem 1 at α = c.
  have hAnn :=
    annulusExcess_lift_identity_at_alpha a b c c hc_nonneg hc_le_one
      hSum_a_minus_cb_ann hSum_b_minus_ca_ann
      hSum_a_norm_ann hSum_b_norm_ann hSum_polar_jacobian
  -- Step A: collapse the two `‖a − cb‖²` paired tsums into a single tsum
  -- with combined weight `1 − 2c^(2k+2)`.
  have hCombined_a_eq :
      (∑' k : ℕ,
            ‖a k - (c : ℂ) * b k‖ ^ 2 *
              (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
        - (∑' k : ℕ,
              ‖a k - (c : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ))
        = ∑' k : ℕ,
            ‖a k - (c : ℂ) * b k‖ ^ 2 *
              (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
    rw [← hSum_a_minus_cb_ann.tsum_sub hSum_a_minus_cb_disk]
    refine tsum_congr (fun k => ?_)
    ring
  -- Step B: collapse the two `‖b − ca‖²` paired tsums.
  have hCombined_b_eq :
      (∑' k : ℕ,
            ‖b k - (c : ℂ) * a k‖ ^ 2 *
              (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ))
        - (∑' k : ℕ,
              ‖b k - (c : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ))
        = ∑' k : ℕ,
            ‖b k - (c : ℂ) * a k‖ ^ 2 *
              (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
    rw [← hSum_b_minus_ca_ann.tsum_sub hSum_b_minus_ca_disk]
    refine tsum_congr (fun k => ?_)
    ring
  -- Step C: derive summability of the combined-weight functions from the
  -- pair-difference identity (so we can apply tsum_sub once more).
  have hSum_combined_a :
      Summable (fun k : ℕ =>
        ‖a k - (c : ℂ) * b k‖ ^ 2 *
          (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ)) := by
    have hEq_fun :
        (fun k : ℕ =>
            ‖a k - (c : ℂ) * b k‖ ^ 2 *
              (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ))
          = (fun k : ℕ =>
              ‖a k - (c : ℂ) * b k‖ ^ 2 *
                  (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)
                - ‖a k - (c : ℂ) * b k‖ ^ 2 *
                    c ^ (2 * k + 2) / (k + 1 : ℝ)) := by
      funext k; ring
    rw [hEq_fun]
    exact hSum_a_minus_cb_ann.sub hSum_a_minus_cb_disk
  have hSum_combined_b :
      Summable (fun k : ℕ =>
        ‖b k - (c : ℂ) * a k‖ ^ 2 *
          (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ)) := by
    have hEq_fun :
        (fun k : ℕ =>
            ‖b k - (c : ℂ) * a k‖ ^ 2 *
              (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ))
          = (fun k : ℕ =>
              ‖b k - (c : ℂ) * a k‖ ^ 2 *
                  (1 - c ^ (2 * k + 2)) / (k + 1 : ℝ)
                - ‖b k - (c : ℂ) * a k‖ ^ 2 *
                    c ^ (2 * k + 2) / (k + 1 : ℝ)) := by
      funext k; ring
    rw [hEq_fun]
    exact hSum_b_minus_ca_ann.sub hSum_b_minus_ca_disk
  -- Step D: combine the two combined-weight tsums into a single tsum on
  -- `(‖a − cb‖² − ‖b − ca‖²) · (1 − 2c^(2k+2)) / (k+1)`.
  have hCombined_diff_eq :
      (∑' k : ℕ,
            ‖a k - (c : ℂ) * b k‖ ^ 2 *
              (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ))
        - (∑' k : ℕ,
              ‖b k - (c : ℂ) * a k‖ ^ 2 *
                (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ))
        = ∑' k : ℕ,
            (‖a k - (c : ℂ) * b k‖ ^ 2 - ‖b k - (c : ℂ) * a k‖ ^ 2)
              * (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ) := by
    rw [← hSum_combined_a.tsum_sub hSum_combined_b]
    refine tsum_congr (fun k => ?_)
    ring
  -- Step E: rewrite (1 − c²) · (annulusExcess − diskExcess) using hAnn − hDisk.
  have hSubtract :
      (1 - c ^ 2) *
          (PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
             - PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
        = (∑' k : ℕ,
              ‖a k - (c : ℂ) * b k‖ ^ 2 *
                (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ))
          - (∑' k : ℕ,
                ‖b k - (c : ℂ) * a k‖ ^ 2 *
                  (1 - 2 * c ^ (2 * k + 2)) / (k + 1 : ℝ)) := by
    have hExpand :
        (1 - c ^ 2) *
            (PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
               - PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
          = (1 - c ^ 2) *
                PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
            - (1 - c ^ 2) *
                PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
      ring
    rw [hExpand, hAnn, hDisk]
    have hRearr :
        ∀ X Y Z W : ℝ, (X - Y) - (Z - W) = (X - Z) - (Y - W) := by
      intros X Y Z W; ring
    rw [hRearr]
    rw [hCombined_a_eq, hCombined_b_eq]
  -- Step F: substitute and apply V54's lift identity per-`k`.
  rw [hSubtract, hCombined_diff_eq]
  refine tsum_congr (fun k => ?_)
  -- Goal: `(‖a − cb‖² − ‖b − ca‖²) · (1 − 2c^(2k+2)) / (k+1)
  --        = ((1 − c²) · coeffPlusGap a b k) · (1 − 2c^(2k+2)) / (k+1)`
  -- By V54: (1 − c²) · (‖b‖² − ‖a‖²) = ‖b − ca‖² − ‖a − cb‖².
  -- Negating: (1 − c²) · (‖a‖² − ‖b‖²) = ‖a − cb‖² − ‖b − ca‖².
  -- Since coeffPlusGap a b k = ‖a‖² − ‖b‖²:
  --   ‖a − cb‖² − ‖b − ca‖² = (1 − c²) · coeffPlusGap a b k
  have hLift :=
    ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k
      a b c k
  have hLift' :
      ‖a k - (c : ℂ) * b k‖ ^ 2 - ‖b k - (c : ℂ) * a k‖ ^ 2
        = (1 - c ^ 2) * PaperAxioms.coeffPlusGap a b k := by
    unfold PaperAxioms.coeffPlusGap
    linarith [hLift]
  rw [hLift']

end ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated
