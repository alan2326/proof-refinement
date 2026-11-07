-- Sprint 077, Phase B: per-candidate derived-theorem file shipping the
-- α-varying generalisation of V54's per-`k` lift identity from `α : ℝ`
-- to `α : ℕ → ℝ` (per-mode α(·)).
--
-- This file is a one-line wrapper of V54's `lift_identity_per_k`. The
-- algebraic content is V54's; sprint 077's structural contribution at the
-- candidate level is to (a) freeze the α-varying signature into the
-- workspace's import graph for sprint 078's downstream use, and (b) make
-- the next planner's task — consuming this signature and shipping a
-- c-push (GO branch) or pivoting (NO-GO branch) — a one-import affair.
--
-- The Phase 0 mpmath sweep
-- (`Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.py`) returned GO
-- for the per-`k` α-varying kernel above c = 7129/20000, with the
-- structural caveat that the witness's α-vector includes |α(k)| > 1
-- entries (specifically α(k) = 1.01 for k ≥ 1 in the
-- `all_over(α0=0.10,α_h=1.01)` family, exiting V54's
-- `lift_identity_per_k_rearranged` contraction regime). Sprint 078's
-- planner consumes the witness with the explicit warning recorded in
-- `Scratch/sprint_077_witness.txt`.
--
-- No new axioms. No oracle. No edit to `KorenblumPaper/`. No edit to
-- `Reduction.lean`. The file lives under
-- `ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity`,
-- registered in `lemma.toml:[import_policy].allowed_exact` per sprint
-- 077's one-line edit (mirroring sprints 068/069/070/073/075's pattern).
import Mathlib.Analysis.Complex.Norm
import ProofRefinement.Korenblum.Candidates.V54.LiftIdentity

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity

/--
Sprint 077 / Phase B — `lift_identity_per_k_alpha_varying`, the trivial
α-varying generalisation of V54's `lift_identity_per_k`.

For any sequences `a, b : ℕ → ℂ`, any sequence `α : ℕ → ℝ`, and any
index `k`,

    (1 − α(k)²) · (‖b k‖² − ‖a k‖²)
       = ‖b k − (α k : ℂ) · a k‖² − ‖a k − (α k : ℂ) · b k‖².

This is the SAME identity as V54's `lift_identity_per_k`, applied at
`α := α k` for each `k` independently. The proof is a one-line
delegation: V54's identity is universal in the real-scalar α, so
specialising at α := α(k) is a no-op.

The α-varying signature is the workspace's first per-candidate
derived-theorem file ranging over `α : ℕ → ℝ` rather than `α : ℝ`.
Sprint 078 (GO branch, gated by `Scratch/sprint_077_witness.txt`)
consumes this signature when building the α-varying integrated lift
identity (analogous to V57.Theorem 1 / V58.Theorem 1 with α swapped
for α(k) per-mode).
-/
theorem lift_identity_per_k_alpha_varying
    (a b : ℕ → ℂ) (α : ℕ → ℝ) (k : ℕ) :
    (1 - (α k) ^ 2) * (‖b k‖ ^ 2 - ‖a k‖ ^ 2)
      = ‖b k - ((α k) : ℂ) * a k‖ ^ 2
          - ‖a k - ((α k) : ℂ) * b k‖ ^ 2 :=
  ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k
    a b (α k) k

/--
Sprint 077 / Phase B — `lift_identity_per_k_alpha_varying_rearranged`,
the contraction-regime rearrangement of `lift_identity_per_k_alpha_varying`.

When `α(k)² < 1` for every `k` (the per-mode contraction-lift regime),
the cross-multiplied factor `1 − α(k)²` is nonzero per-`k`, so dividing
yields

    ‖b k‖² − ‖a k‖² =
      (‖b k − (α k : ℂ)·a k‖² − ‖a k − (α k : ℂ)·b k‖²) / (1 − α(k)²).

Note: per-`k` `α(k)² < 1` is the natural domain for V58.Theorem 3-style
closed-form readouts of the per-`k` cross-coupling at α := α(k).
Sprint 077's witness search detected NO contraction-regime witness
(`max_k |α(k)| < 1` with kernel ≥ 0 on every canonical extremal at any
c > 7129/20000); see `Scratch/sprint_077_witness.txt`'s structural
caveat for details. This rearrangement is shipped for completeness so
that sprint 078's planner has both the unrearranged and rearranged
forms available.
-/
theorem lift_identity_per_k_alpha_varying_rearranged
    (a b : ℕ → ℂ) (α : ℕ → ℝ)
    (hα : ∀ k, (α k) ^ 2 < 1) (k : ℕ) :
    ‖b k‖ ^ 2 - ‖a k‖ ^ 2
      = (‖b k - ((α k) : ℂ) * a k‖ ^ 2
            - ‖a k - ((α k) : ℂ) * b k‖ ^ 2)
          / (1 - (α k) ^ 2) :=
  ProofRefinement.Korenblum.Candidates.V54.LiftIdentity.lift_identity_per_k_rearranged
    a b (α k) (hα k) k

end ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity
