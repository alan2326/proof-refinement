-- Sprint 073, Phase A: per-candidate derived-theorem file shipping the
-- INTEGRATED LIFT IDENTITY over `[0, c]` for V57.
--
-- This file ships two `theorem`s (no `axiom`s, no `sorry`s):
--
--   1. `diskExcess_lift_identity_at_alpha`: the integrated form of V54's
--      per-`k` lift identity, expressed as a `tsum` of disk-weighted
--      `‖·‖²` differences.
--
--      `(1 − α²) · diskExcess (circleGap a b) c
--         = ∑' k, ‖a k − α·b k‖² · c^(2k+2) / (k+1)
--           − ∑' k, ‖b k − α·a k‖² · c^(2k+2) / (k+1)`
--
--   2. `diskExcess_upper_bound_via_lift_at_alpha`: the immediate
--      corollary obtained by dropping the (non-negative) second `tsum`.
--
--      `(1 − α²) · diskExcess (circleGap a b) c
--         ≤ ∑' k, ‖a k − α·b k‖² · c^(2k+2) / (k+1)`
--
--   3. `diskExcess_le_simple_at_alpha_eq_c` (Optional Theorem 3): the
--      Cauchy/triangle-bound specialisation at `α = c`, producing a
--      closed-form upper bound in terms of `diskWeightedSeq (‖a·‖²) c`
--      and `diskWeightedSeq (‖b·‖²) c`.
--
-- ### Hypothesis envelope
--
-- The per-`k` algebraic identity (V54 `lift_identity_per_k`) is paper-
-- axiom-free. The series-level rearrangement (combining V54 per-`k`
-- with `tsum` arithmetic) is paper-axiom-free. The remaining piece is
-- the **polar-Jacobian disk-integral identity**:
--
--   `diskExcess (circleGap a b) c
--      = ∑' k, coeffPlusGap a b k · c^(2k+2) / (k+1)`
--
-- which is the termwise integration of `2ρ · ρ^(2k)` over `[0, c]`.
-- Per Mathlib v4.28.0 and the contract's stop-conditions, the cleanest
-- way to ship this without a heavy `intervalIntegral.integral_tsum`
-- detour is to surface it as a hypothesis in Theorem 1's signature —
-- the analogous strategy V53/V54/V55 already use for their own
-- structural side-conditions (e.g. V53/ThetaStep takes `0 ≤ c` as a
-- hypothesis to satisfy `paper.eq3_circleGap_decomposition`'s
-- precondition; V55/LiftSeriesBridge takes four summability
-- hypotheses).
--
-- Surfacing the polar-Jacobian identity as a hypothesis is consistent
-- with the contract's BLOCKED-on-summability stop-condition guidance:
-- the V57 side-lemma `v57_lift_integrated_compiles_at_seed_witness`
-- exercises Theorem 1's signature against arbitrary `(a, b, α, c)`
-- without instantiating the polar-Jacobian or summability hypotheses
-- (statement-level non-vacuity check, mirroring V55's pattern). The
-- per-`k` algebraic content of the integrated lift identity is what
-- this sprint ships; the polar-Jacobian step is a separate piece that
-- a future sprint (or a future Mathlib-API-heavy formalisation) can
-- discharge cleanly.
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
-- works out to
--
--   `(1 − α²) · diskExcess (circleGap a b) c
--      = ∑' k, (‖a k − α·b k‖² − ‖b k − α·a k‖²) · c^(2k+2) / (k+1)`
--
-- which decomposes into Theorem 1's stated difference of two `tsum`s
-- under the natural disk-weighted summability hypotheses.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated`,
-- registered in `lemma.toml:[import_policy].allowed_exact` per sprint
-- 073's one-line edit (mirroring sprints 068/069/070's pattern).
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Candidates.V54.LiftIdentity
import ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated

open KorenblumPaper

/--
Sprint 073 / Phase A — `diskExcess_lift_identity_at_alpha`, the integrated
form of V54's per-`k` lift identity over the disk `[0, c]`.

For any `(a, b : ℕ → ℂ)`, any real `α` with `α² < 1`, any `c ≥ 0`, the
disk-weighted summability hypotheses, and the polar-Jacobian disk-integral
bridge identity (a structural assumption that
`diskExcess (circleGap a b) c = ∑' k, coeffPlusGap a b k · c^(2k+2)/(k+1)`,
the termwise integration of `2ρ · circleGapSeries`),

  `(1 − α²) · diskExcess (circleGap a b) c
     = ∑' k, ‖a k − (α : ℂ)·b k‖² · c^(2k+2) / (k+1)
       − ∑' k, ‖b k − (α : ℂ)·a k‖² · c^(2k+2) / (k+1)`.

This is the workspace's first `tsum`-level identity bridging Wang's
per-`k` lift-identity content (V54) to the integrated `diskExcess`
quantity used throughout `Reduction.lean`. The proof outline:

1. Apply the polar-Jacobian disk-integral hypothesis to rewrite
   `diskExcess (circleGap a b) c` as
   `∑' k, coeffPlusGap a b k · c^(2k+2)/(k+1)`.
2. Multiply by `(1 − α²)` and pull the constant inside the `tsum` via
   `Summable.tsum_mul_left`.
3. Apply V54's `lift_identity_per_k` per-`k` to express
   `(1 − α²)·(‖a k‖² − ‖b k‖²)
       = ‖a k − α·b k‖² − ‖b k − α·a k‖²`.
4. Distribute the `· c^(2k+2)/(k+1)` factor through the difference and
   split the resulting `tsum` of differences into the difference of two
   `tsum`s using `Summable.tsum_sub` under the four disk-weighted
   summability hypotheses.
-/
theorem diskExcess_lift_identity_at_alpha
    (a b : ℕ → ℂ) (α c : ℝ)
    (_hα_sq_lt_one : α ^ 2 < 1)
    (_hc_nonneg : 0 ≤ c)
    (hSum_a_minus_αb_disk :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_b_minus_αa_disk :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (_hSum_a_norm_disk :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (_hSum_b_norm_disk :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hDiskJacobian :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        = ∑' k : ℕ,
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ)) :
    (1 - α ^ 2) *
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      = (∑' k : ℕ,
            ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ))
        - (∑' k : ℕ,
            ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)) := by
  -- Step 1: rewrite `diskExcess` via the polar-Jacobian hypothesis.
  rw [hDiskJacobian]
  -- Step 2: pull `(1 - α^2)` inside the `tsum`.
  --   `(1 - α²) · ∑' k, X k = ∑' k, (1 - α²) · X k`
  -- where `X k = coeffPlusGap a b k · c^(2k+2) / (k+1)`.
  -- We avoid `Summable.tsum_mul_left` to dodge the summability
  -- precondition (it is implied by the four hypotheses but takes a few
  -- rewrites to extract); instead, use `tsum_mul_left` (the unconditional
  -- form for `T2Space` real-valued tsums).
  rw [← tsum_mul_left]
  -- Goal:
  --   `∑' k, (1 - α²) · (coeffPlusGap a b k · c^(2k+2) / (k+1))
  --      = (∑' k, ‖a k − α·b k‖² · c^(2k+2)/(k+1))
  --        − (∑' k, ‖b k − α·a k‖² · c^(2k+2)/(k+1))`
  -- Step 3: use V54's per-`k` lift identity to rewrite each summand.
  -- Define abbreviations for the two RHS sequences for readability.
  set f : ℕ → ℝ := fun k =>
    ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)
    with hf_def
  set g : ℕ → ℝ := fun k =>
    ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)
    with hg_def
  -- Need both `f` and `g` summable.
  have hSum_f : Summable f := by simpa [hf_def] using hSum_a_minus_αb_disk
  have hSum_g : Summable g := by simpa [hg_def] using hSum_b_minus_αa_disk
  -- The RHS combined as a single `tsum` of `f k - g k`.
  rw [← hSum_f.tsum_sub hSum_g]
  -- Goal: `∑' k, (1 − α²) · (coeffPlusGap a b k · c^(2k+2)/(k+1))
  --        = ∑' k, (f k − g k)`
  refine tsum_congr (fun k => ?_)
  -- Per-term equality. Apply V54's lift identity at `(a, b, α, k)`:
  --   `(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − α·a k‖² − ‖a k − α·b k‖²`
  have hLift := V54.LiftIdentity.lift_identity_per_k a b α k
  -- Negate to align with `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`:
  have hLift' :
      (1 - α ^ 2) * PaperAxioms.coeffPlusGap a b k
        = ‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2 := by
    unfold PaperAxioms.coeffPlusGap
    -- `(1 − α²) · (‖a k‖² − ‖b k‖²) = ‖a k − α·b k‖² − ‖b k − α·a k‖²`
    -- follows from `hLift` by negation.
    linarith [hLift]
  -- Now distribute: each summand is `(1−α²) · (coeffPlus · c^(2k+2)/(k+1))`,
  -- which factors as `((1−α²) · coeffPlus) · c^(2k+2)/(k+1)`.
  show (1 - α ^ 2) *
      (PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ))
    = f k - g k
  -- Multiply hLift' by `c^(2k+2)/(k+1)` (a real-valued nonzero or
  -- otherwise constant factor — we don't need a sign condition for
  -- this rewriting, just `ring`-level distribution).
  have hLift_mul :
      (1 - α ^ 2) *
          (PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ))
        = (‖a k - (α : ℂ) * b k‖ ^ 2 - ‖b k - (α : ℂ) * a k‖ ^ 2)
            * c ^ (2 * k + 2) / (k + 1 : ℝ) := by
    have := hLift'
    -- `LHS = ((1 − α²) · coeffPlus) · c^(2k+2)/(k+1)`.
    -- Substitute hLift' on the inner `(1−α²) · coeffPlus`.
    rw [show (1 - α ^ 2) *
              (PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ))
              = ((1 - α ^ 2) * PaperAxioms.coeffPlusGap a b k)
                  * c ^ (2 * k + 2) / (k + 1 : ℝ) by ring]
    rw [hLift']
  rw [hLift_mul]
  -- Goal: `(‖a k − α·b k‖² − ‖b k − α·a k‖²) · c^(2k+2)/(k+1) = f k − g k`
  -- with `f k = ‖a k − α·b k‖² · c^(2k+2)/(k+1)` and similarly `g`.
  simp only [hf_def, hg_def]
  ring

/--
Sprint 073 / Phase A — `diskExcess_upper_bound_via_lift_at_alpha`, the
immediate corollary of Theorem 1 by dropping the non-negative
`‖b k − α·a k‖² · c^(2k+2) / (k+1)` term.

Hypotheses inherit from Theorem 1, plus `0 < 1 − α²` (i.e. `α² < 1`
strictly). The bound is:

  `(1 − α²) · diskExcess (circleGap a b) c
     ≤ ∑' k, ‖a k − (α : ℂ)·b k‖² · c^(2k+2) / (k+1)`.

This is the workspace's first **Λ-free** disk-side upper bound on
`diskExcess` integrated over `[0, c]`. It does not divide by
`paperLambda K c ρ` anywhere — the factor `(1 − α²)` is the only
denominator-shaped quantity, and it does not depend on a radial
parameter ρ at all. Future closing-reducer sprints can compose this
bound with annulus-side machinery on a chain that does not pay the
Λ-suppression that has falsified every closed-form `(a, b)`-independent
kernel since sprint 048.
-/
theorem diskExcess_upper_bound_via_lift_at_alpha
    (a b : ℕ → ℂ) (α c : ℝ)
    (hα_sq_lt_one : α ^ 2 < 1)
    (hc_nonneg : 0 ≤ c)
    (hSum_a_minus_αb_disk :
      Summable (fun k : ℕ =>
        ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_b_minus_αa_disk :
      Summable (fun k : ℕ =>
        ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_a_norm_disk :
      Summable (fun k : ℕ =>
        ‖a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hSum_b_norm_disk :
      Summable (fun k : ℕ =>
        ‖b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hDiskJacobian :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        = ∑' k : ℕ,
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ)) :
    (1 - α ^ 2) *
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      ≤ ∑' k : ℕ,
          ‖a k - (α : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ) := by
  -- Apply Theorem 1 to get the equality form, then drop the non-negative
  -- second `tsum`.
  have hEq :=
    diskExcess_lift_identity_at_alpha a b α c hα_sq_lt_one hc_nonneg
      hSum_a_minus_αb_disk hSum_b_minus_αa_disk
      hSum_a_norm_disk hSum_b_norm_disk hDiskJacobian
  -- The dropped `tsum` is non-negative because each summand is
  -- `‖_‖² · c^(2k+2)/(k+1) ≥ 0` under `c ≥ 0`.
  have hTsum_nonneg :
      0 ≤ ∑' k : ℕ,
        ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ) := by
    apply tsum_nonneg
    intro k
    -- Each term: `(‖_‖² · c^(2k+2)) / (k+1)`. Numerator ≥ 0, denominator ≥ 0.
    have h1 : 0 ≤ ‖b k - (α : ℂ) * a k‖ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ c ^ (2 * k + 2) := by
      have hPow : c ^ (2 * k + 2) = (c ^ (k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      rw [hPow]
      exact sq_nonneg _
    have h3 : 0 ≤ (k + 1 : ℝ) := by positivity
    have hMul : 0 ≤ ‖b k - (α : ℂ) * a k‖ ^ 2 * c ^ (2 * k + 2) :=
      mul_nonneg h1 h2
    exact div_nonneg hMul h3
  -- LHS = RHS_minus_TSum_nonneg ≤ RHS = ∑' k, ‖a k − α·b k‖² · c^(2k+2)/(k+1).
  linarith [hEq, hTsum_nonneg]

/--
Sprint 073 / Phase A (Optional Theorem 3) —
`diskExcess_le_simple_at_alpha_eq_c`.

Specialise Theorem 2 to `α = c` (so `α² = c² < 1` for `c ∈ (0, 1)`),
and apply the elementary triangle bound `‖a k − c·b k‖² ≤ 2(‖a k‖² +
c²·‖b k‖²)` per-`k`, summed against `c^(2k+2)/(k+1)`:

  `diskExcess (circleGap a b) c
     ≤ (2 / (1 − c²)) · ∑' k, (‖a k‖² + c² · ‖b k‖²) · c^(2k+2) / (k+1)`.

This is a **closed-form upper bound** on `diskExcess` purely in terms
of `Σ⁰⁺(c)`-style coefficient sums (the `‖a k‖²` and `‖b k‖²`
disk-weighted sums). It is the structural sibling of Wang's eq (5)/(6)
but routes through the lift identity at the `c = ρ` anchor rather than
through the eq (3)/(4) chain.

The triangle bound `‖a k − c·b k‖² ≤ 2·(‖a k‖² + c²·‖b k‖²)` follows
from `(x − y)² ≤ 2(x² + y²)` (a special case of the elementary
inequality `2xy ≤ x² + y²`), applied to `x = ‖a k‖`, `y = c · ‖b k‖`,
plus the operator inequality `‖a k − c·b k‖ ≤ ‖a k‖ + c·‖b k‖` (the
triangle inequality).
-/
theorem diskExcess_le_simple_at_alpha_eq_c
    (a b : ℕ → ℂ) (c : ℝ)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
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
    (hSum_combined_disk :
      Summable (fun k : ℕ =>
        2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) *
          c ^ (2 * k + 2) / (k + 1 : ℝ)))
    (hDiskJacobian :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
        = ∑' k : ℕ,
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1 : ℝ)) :
    (1 - c ^ 2) *
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
      ≤ ∑' k : ℕ,
          2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) *
            c ^ (2 * k + 2) / (k + 1 : ℝ) := by
  -- `c^2 < 1` from `0 < c < 1`.
  have hcsq_lt_one : c ^ 2 < 1 := by
    have : c ^ 2 ≤ c := by nlinarith [hc_pos.le, hc_lt_one]
    linarith
  -- `c ≥ 0`.
  have hc_nonneg : 0 ≤ c := hc_pos.le
  -- Apply Theorem 2 at `α = c`.
  have hTheorem2 :=
    diskExcess_upper_bound_via_lift_at_alpha a b c c hcsq_lt_one hc_nonneg
      hSum_a_minus_cb_disk hSum_b_minus_ca_disk
      hSum_a_norm_disk hSum_b_norm_disk hDiskJacobian
  -- Now bound the RHS termwise using the triangle/Cauchy bound:
  --   `‖a k − c·b k‖² ≤ 2·(‖a k‖² + c²·‖b k‖²)`.
  have hPerK_bound : ∀ k : ℕ,
      ‖a k - (c : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)
        ≤ 2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) *
            c ^ (2 * k + 2) / (k + 1 : ℝ) := by
    intro k
    -- Triangle inequality: `‖a k − c·b k‖ ≤ ‖a k‖ + c·‖b k‖`.
    have hTri : ‖a k - (c : ℂ) * b k‖ ≤ ‖a k‖ + c * ‖b k‖ := by
      have h1 : ‖a k - (c : ℂ) * b k‖ ≤ ‖a k‖ + ‖(c : ℂ) * b k‖ :=
        norm_sub_le _ _
      have h2 : ‖(c : ℂ) * b k‖ = c * ‖b k‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_nonneg]
      linarith
    -- Square both sides: need both nonneg.
    have hLHS_nonneg : 0 ≤ ‖a k - (c : ℂ) * b k‖ := norm_nonneg _
    have hRHS_nonneg : 0 ≤ ‖a k‖ + c * ‖b k‖ := by
      have ha : 0 ≤ ‖a k‖ := norm_nonneg _
      have hb : 0 ≤ ‖b k‖ := norm_nonneg _
      have hcb : 0 ≤ c * ‖b k‖ := mul_nonneg hc_nonneg hb
      linarith
    have hSq_le : ‖a k - (c : ℂ) * b k‖ ^ 2 ≤ (‖a k‖ + c * ‖b k‖) ^ 2 := by
      exact pow_le_pow_left₀ hLHS_nonneg hTri 2
    -- And `(‖a k‖ + c·‖b k‖)^2 ≤ 2·(‖a k‖² + c²·‖b k‖²)` follows from
    -- `2xy ≤ x² + y²` with `x = ‖a k‖`, `y = c·‖b k‖`.
    have hCauchy : (‖a k‖ + c * ‖b k‖) ^ 2
        ≤ 2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) := by
      have ha : 0 ≤ ‖a k‖ := norm_nonneg _
      have hb : 0 ≤ ‖b k‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a k‖ - c * ‖b k‖), sq_nonneg c, ha, hb]
    -- Combined: `‖a k − c·b k‖² ≤ 2·(‖a k‖² + c²·‖b k‖²)`.
    have hCombined : ‖a k - (c : ℂ) * b k‖ ^ 2
        ≤ 2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) := le_trans hSq_le hCauchy
    -- Multiply both sides by `c^(2k+2)/(k+1) ≥ 0`.
    have hPow_nonneg : 0 ≤ c ^ (2 * k + 2) := by
      have : c ^ (2 * k + 2) = (c ^ (k + 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      rw [this]
      exact sq_nonneg _
    have hKp1_pos : 0 < (k + 1 : ℝ) := by positivity
    have hWeight_nonneg : 0 ≤ c ^ (2 * k + 2) / (k + 1 : ℝ) :=
      div_nonneg hPow_nonneg hKp1_pos.le
    -- Multiply through.
    have hScaled :
        ‖a k - (c : ℂ) * b k‖ ^ 2 * (c ^ (2 * k + 2) / (k + 1 : ℝ))
          ≤ 2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2)
              * (c ^ (2 * k + 2) / (k + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCombined hWeight_nonneg
    -- Re-associate to match the goal's `... · c^(2k+2) / (k+1)` shape.
    have hLHS_assoc :
        ‖a k - (c : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ)
          = ‖a k - (c : ℂ) * b k‖ ^ 2 * (c ^ (2 * k + 2) / (k + 1 : ℝ)) := by
      ring
    have hRHS_assoc :
        2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) *
            c ^ (2 * k + 2) / (k + 1 : ℝ)
          = 2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2)
              * (c ^ (2 * k + 2) / (k + 1 : ℝ)) := by
      ring
    rw [hLHS_assoc, hRHS_assoc]
    exact hScaled
  -- Sum the per-`k` bound termwise.
  have hTsum_le :
      (∑' k : ℕ,
          ‖a k - (c : ℂ) * b k‖ ^ 2 * c ^ (2 * k + 2) / (k + 1 : ℝ))
        ≤ ∑' k : ℕ,
            2 * (‖a k‖ ^ 2 + c ^ 2 * ‖b k‖ ^ 2) *
              c ^ (2 * k + 2) / (k + 1 : ℝ) :=
    hSum_a_minus_cb_disk.tsum_le_tsum hPerK_bound hSum_combined_disk
  -- Chain Theorem 2 with the triangle bound to close.
  exact le_trans hTheorem2 hTsum_le

end ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated
