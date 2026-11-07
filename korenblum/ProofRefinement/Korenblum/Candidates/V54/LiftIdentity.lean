-- Sprint 069, Phase A: per-candidate derived-theorem file shipping
-- Wang's per-`k` lift identity for V54.
--
-- This file ships LIFT_IDENTITY as a Lean theorem (no axiom, no oracle):
--
--   `(1 - α^2) · (‖b k‖^2 - ‖a k‖^2) =
--      ‖b k - (α : ℂ) * a k‖^2 - ‖a k - (α : ℂ) * b k‖^2`
--
-- valid for every `(a, b : ℕ → ℂ)`, every real `α`, and every `k : ℕ`.
--
-- The identity is purely algebraic on `ℂ`-valued sequences. The proof
-- expands `‖z‖^2` via `Complex.sq_norm` / `Complex.normSq_apply` to the
-- real-component form `z.re^2 + z.im^2`, then closes by `ring` after
-- distributing the `(α : ℂ) * _` coercion via `Complex.re_ofReal_mul`,
-- `Complex.im_ofReal_mul`, `Complex.sub_re`, `Complex.sub_im`.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V54.LiftIdentity`, which is
-- registered in `lemma.toml:[import_policy].allowed_exact` per sprint 069's
-- one-line edit (mirroring sprint 068's `Candidates.V53.ThetaStep` row).
import Mathlib.Analysis.Complex.Norm

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V54.LiftIdentity

open Complex

/--
Sprint 069 / Phase A — `lift_identity_per_k_re_im`, the literal real-component
form of Wang's per-`k` lift identity.

This is the "ring form" of the identity, with both sides written explicitly
in the real and imaginary parts of `a k` and `b k`. It closes by `ring`
without any analysis-side rewrites.

For any real-valued `α` and any complex `a k, b k`,

    (1 − α²)·((b k).re² + (b k).im² − (a k).re² − (a k).im²)
      =  ((b k).re − α·(a k).re)² + ((b k).im − α·(a k).im)²
       − ((a k).re − α·(b k).re)² − ((a k).im − α·(b k).im)².

This is the algebraic kernel of `lift_identity_per_k`; the latter is
obtained by reading off `‖z‖² = z.re² + z.im²` on each side via
`Complex.sq_norm` plus `Complex.normSq_apply`.
-/
theorem lift_identity_per_k_re_im
    (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
    (1 - α ^ 2) *
        ( ((b k).re ^ 2 + (b k).im ^ 2)
          - ((a k).re ^ 2 + (a k).im ^ 2) )
      = ( ((b k).re - α * (a k).re) ^ 2
          + ((b k).im - α * (a k).im) ^ 2 )
        - ( ((a k).re - α * (b k).re) ^ 2
            + ((a k).im - α * (b k).im) ^ 2 ) := by
  ring

/--
Sprint 069 / Phase A — `lift_identity_per_k`, Wang's per-`k` lift identity
in its native `‖·‖²` form.

For any sequences `a, b : ℕ → ℂ`, any real scalar `α`, and any index `k`,

    (1 − α²) · (‖b k‖² − ‖a k‖²)
      = ‖b k − (α : ℂ) · a k‖² − ‖a k − (α : ℂ) · b k‖².

This is the algebraic backbone of Wang's per-`k` cross-coupling step. It
is paper-axiom-free: it does not depend on any `Section2Assumptions`
field, on any oracle, or on any `KorenblumPaper.*` content. It is a pure
identity on the structure `(ℕ → ℂ) × (ℕ → ℂ) × ℝ × ℕ`.

Proof outline:

1. Convert each `‖·‖²` to `Complex.normSq` via `Complex.sq_norm`.
2. Unfold each `Complex.normSq` to the real-component sum
   `re² + im²` via `Complex.normSq_apply`.
3. Compute `(b k - (α : ℂ) * a k).re = (b k).re - α * (a k).re` (and the
   imaginary analogue), using `Complex.sub_re`/`sub_im`,
   `Complex.re_ofReal_mul`/`im_ofReal_mul` to handle the coercion
   `(α : ℝ) → (α : ℂ)`.
4. Reduce both sides to the same real-component polynomial form and
   close by `lift_identity_per_k_re_im` (a `ring`-level identity).
-/
theorem lift_identity_per_k
    (a b : ℕ → ℂ) (α : ℝ) (k : ℕ) :
    (1 - α ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
      = ‖b k - (α : ℂ) * a k‖ ^ 2 - ‖a k - (α : ℂ) * b k‖ ^ 2 := by
  -- Step 1 + 2: rewrite `‖z‖²` as `z.re^2 + z.im^2` via the
  -- `Complex.sq_norm` / `Complex.normSq_apply` chain. We use
  -- `mul_self`-form first then convert to `_^2` via `← sq`.
  have hSq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]
  -- Apply `hSq` to all four norms.
  rw [hSq (b k), hSq (a k), hSq (b k - (α : ℂ) * a k),
      hSq (a k - (α : ℂ) * b k)]
  -- Step 3: distribute the subtraction and `(α : ℂ) * _` over `re`/`im`.
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul]
  -- Step 4: close by `ring`.
  ring

/--
Sprint 069 / Phase A — `lift_identity_per_k_rearranged`, a contraction-regime
rearrangement of `lift_identity_per_k`.

When `α^2 < 1` (Wang's contraction-lift regime), the cross-multiplied
factor `1 − α²` is nonzero, so dividing yields

    ‖b k‖² − ‖a k‖² =
      (‖b k − (α : ℂ)·a k‖² − ‖a k − (α : ℂ)·b k‖²) / (1 − α²).

This optional companion is included for downstream consumability:
future per-`k` cross-coupling derivations that consume the lift identity
typically read off `‖b k‖² − ‖a k‖²` (the per-`k` boundary `L²` excess)
in terms of the right-hand side via this rearrangement.
-/
theorem lift_identity_per_k_rearranged
    (a b : ℕ → ℂ) (α : ℝ) (hα : α ^ 2 < 1) (k : ℕ) :
    ‖b k‖ ^ 2 - ‖a k‖ ^ 2
      = (‖b k - (α : ℂ) * a k‖ ^ 2 - ‖a k - (α : ℂ) * b k‖ ^ 2)
          / (1 - α ^ 2) := by
  have h1 : (1 : ℝ) - α ^ 2 ≠ 0 := by
    have : (0 : ℝ) < 1 - α ^ 2 := by linarith
    exact ne_of_gt this
  have hraw := lift_identity_per_k a b α k
  -- Goal: `‖b k‖^2 - ‖a k‖^2 = (... - ...) / (1 - α^2)`. Multiply both
  -- sides by `(1 - α^2)` via `eq_div_iff` and conclude from `hraw`.
  rw [eq_div_iff h1]
  linarith [hraw]

end ProofRefinement.Korenblum.Candidates.V54.LiftIdentity
