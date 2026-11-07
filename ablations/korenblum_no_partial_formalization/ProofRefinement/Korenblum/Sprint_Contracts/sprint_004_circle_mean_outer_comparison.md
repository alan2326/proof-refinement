# Sprint 004: `circleMeanSq` outer-annulus comparison + radial-form outer monotonicity

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V3.lean`
**Target file**: `Candidates/V4.lean`
**Direction**: section2-proof (Bergman scaffolding — radial comparison API)

## Goal

Lift the outer-annulus comparison hypothesis `‖f z‖ ≤ ‖g z‖ on c < ‖z‖ < 1`
into the radial / circle-mean world by proving:

1. `circleMeanSq_le_of_outerAnnulus_dom` — at every fixed radius
   `r ∈ Ioo c 1`, the pointwise outer-annulus dominance hypothesis implies
   `circleMeanSq f r ≤ circleMeanSq g r`;
2. `outerAnnulus_norm_sq_mono_via_radial` — a parallel proof of the existing
   `outerAnnulus_norm_sq_mono`, this time routed through the radial polar
   form (`outerAnnulus_norm_sq_polar` + the new circle-mean comparison
   lemma + integral monotonicity in `r`).

Both lemmas live in a new file `Proof/CircleMeanCompare.lean`. V4 is
**scaffolding-only**: `c_value = 3554/10000` is unchanged and the only
seed axiom is still `hKorenblum_published_3554`. The contribution is the
new derived module, which is the canonical bridge from
"pointwise dominance on outerAnnulus" to "radial-form dominance of the
outer Bergman integral."

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- The existing `outerAnnulus_norm_sq_mono` (in `Proof/AnnulusBergman.lean`)
  already gives the outer-half comparison via direct 2D integral
  monotonicity. That proof lives in the `Set ℂ` world. **Every honest
  attempt to push `c > 0.3554` requires an analytic argument on the
  *inner* half**, and every plausible inner-half tool — circle-mean
  monotonicity in `r`, Bergman-monomial Parseval, Cauchy-formula
  coefficient bounds, mean-value bounds via `Real.circleAverage` — works
  on the radial circle-mean function `r ↦ circleMeanSq f r`, not on the
  2D set-integral. Before any inner-half attack can even compose with
  the existing outer-half result, we need the outer comparison **stated
  in `circleMeanSq` form**. This sprint produces that statement.
- The lemma is single-session-sized. The proof of (1) is mechanical: at
  fixed `r ∈ Ioo c 1` and any `θ ∈ Ioo (-π) π`,
  `polarCoord.symm (r, θ) ∈ outerAnnulus c` (the membership argument is
  already coded inside `outerAnnulus_norm_sq_polar`'s step 4 in
  `Proof/RadialBergman.lean`), so the hypothesis hands us
  `‖f(symm(r,θ))‖ ≤ ‖g(symm(r,θ))‖` pointwise; squaring (monotone on
  non-negatives via `pow_le_pow_left₀`) preserves the inequality; and
  `setIntegral_mono_on` over `θ ∈ Ioo (-π) π` closes the goal. The proof
  of (2) is a single application of `setIntegral_mono_on` on
  `r ∈ Ioo c 1` against the inequality `circleMeanSq f r * r ≤
  circleMeanSq g r * r` (multiply (1) by `r ≥ 0`), then chain through
  `outerAnnulus_norm_sq_polar` on each side.
- After this sprint, the inner-half attack has a clean statement to
  drive toward: `circleMeanSq f r ≤ circleMeanSq g r` for `r ∈ Ioc 0 c`,
  derivable from analyticity of `f, g` plus the outer comparison via
  some monotonicity / mean-value tool. Without sprint 4's lemma, that
  inner-half statement would have to be re-derived in every candidate.
- The proofs sit comfortably in the generator's declared scope:
  `setIntegral_mono_on`, `pow_le_pow_left₀`, the membership-in-`outerAnnulus`
  unfold reused from `outerAnnulus_norm_sq_polar` step 4, plus `mul_le_mul`
  on a non-negative scalar. No new Mathlib API surface is touched.
- Falsifiable bottleneck: if `setIntegral_mono_on` cannot be applied
  (e.g. because the integrability side hypotheses on `circleMeanSq`'s
  `θ`-integrand cannot be threaded through to it), the `STATUS=BLOCKED`
  log will record exactly which Mathlib API is missing for the radial
  comparison form. That same bottleneck would block any future inner-
  half attack, so the failure mode is informative either way.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleMeanCompare.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,
  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.AnnulusBergman`,
    `Proof.RadialBergman` (and **only** those workspace-side imports),
  - exposes lemma (1): roughly

    ```lean
    theorem circleMeanSq_le_of_outerAnnulus_dom
        (f g : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c)
        (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖)
        {r : ℝ} (hr : r ∈ Set.Ioo c 1)
        (hf_int : IntegrableOn
            (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
            (Set.Ioo (-Real.pi) Real.pi) volume)
        (hg_int : IntegrableOn
            (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
            (Set.Ioo (-Real.pi) Real.pi) volume) :
        circleMeanSq f r ≤ circleMeanSq g r
    ```

    Proof outline: unfold `circleMeanSq` on both sides;
    `setIntegral_mono_on` on `Ioo (-π) π`; for the pointwise step at
    `θ ∈ Ioo (-π) π`, derive `polarCoord.symm (r, θ) ∈ outerAnnulus c`
    from `r ∈ Ioo c 1` (mirror the step-4 unfold from
    `outerAnnulus_norm_sq_polar` in `Proof/RadialBergman.lean`); apply
    `h` and `pow_le_pow_left₀ (norm_nonneg _) _ 2`.
  - exposes lemma (2): roughly

    ```lean
    theorem outerAnnulus_norm_sq_mono_via_radial
        (f g : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
        (hf_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        (hg_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        (hf_circle : ∀ r ∈ Set.Ioo c 1,
            IntegrableOn
              (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
              (Set.Ioo (-Real.pi) Real.pi) volume)
        (hg_circle : ∀ r ∈ Set.Ioo c 1,
            IntegrableOn
              (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
              (Set.Ioo (-Real.pi) Real.pi) volume)
        (hfg_radial_int :
            IntegrableOn (fun r => circleMeanSq f r * r)
                         (Set.Ioo c 1) volume)
        (hg_radial_int :
            IntegrableOn (fun r => circleMeanSq g r * r)
                         (Set.Ioo c 1) volume)
        (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
        (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
          ≤ (∫ z in outerAnnulus c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ))
    ```

    Proof outline: `rw [outerAnnulus_norm_sq_polar f c hc hc1 hf_polar,
    outerAnnulus_norm_sq_polar g c hc hc1 hg_polar]`; then
    `setIntegral_mono_on` on `r ∈ Ioo c 1` against the pointwise
    inequality `circleMeanSq f r * r ≤ circleMeanSq g r * r`; the pointwise
    inequality follows from `circleMeanSq_le_of_outerAnnulus_dom` plus
    `mul_le_mul_of_nonneg_right` (or `mul_le_mul`) using `0 ≤ r` from
    `hc ≤ r`.
  - The integrability hypotheses (`hf_circle`, `hg_circle`,
    `hfg_radial_int`, `hg_radial_int`) are threaded through; the generator
    is free to tighten or weaken their exact shape (e.g. consolidate to
    a single `IntegrableOn` of the polar product on the box, plus Fubini)
    as long as the lemma's conclusion type is unchanged.
  - Both lemmas are `theorem`/`lemma`, never `axiom`. No `sorry`.
- `ProofRefinement/Korenblum/Candidates/V4.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V4`, marked
  `-- @parent V3`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V3),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V3,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`, and the new
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare` so that the new
    module is part of V4's compile graph and is exercised by the build.
    No structural use of the new lemmas is required in V4 itself.
- No edits to `lemma.toml`. No edits to V0/V1/V2/V3 or to the existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V4` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V4.lean` succeeds (the evaluator
   accepts V4 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V3; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/CircleMeanCompare.lean`
   contains:
   - one `theorem` (or `lemma`) named `circleMeanSq_le_of_outerAnnulus_dom`
     (or equivalently named) whose conclusion is `circleMeanSq f r ≤
     circleMeanSq g r` for any `r ∈ Set.Ioo c 1`, given the pointwise
     outer-annulus dominance hypothesis;
   - one `theorem` (or `lemma`) named
     `outerAnnulus_norm_sq_mono_via_radial` (or equivalently named)
     whose conclusion is the same outer-annulus integral inequality
     proved by `outerAnnulus_norm_sq_mono` in `Proof/AnnulusBergman.lean`,
     but whose proof is routed through `outerAnnulus_norm_sq_polar` and
     `circleMeanSq_le_of_outerAnnulus_dom` (the proof must call both;
     i.e. the new lemma is a *radial* re-derivation, not a re-export of
     `outerAnnulus_norm_sq_mono`).
   Both must be `theorem` / `lemma`, never `axiom`, with no `sorry`.
4. The new module `Proof.CircleMeanCompare` must be **used**, even
   trivially, somewhere in V4's transitive compile graph (importing
   `Proof.CircleMeanCompare` from V4 is sufficient — it forces the
   module to compile as part of V4's build).

## Out of scope

- Edit older candidates (`V0.lean`, `V1.lean`, `V2.lean`, `V3.lean`) or
  the existing `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the generator finds either lemma genuinely
  blocked on a missing Mathlib API, it must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize the lemma.
- Attempt the inner half. The inner-half comparison
  (`circleMeanSq f r ≤ circleMeanSq g r` for `r ∈ Ioc 0 c`) is genuinely
  hard and requires either a circle-mean monotonicity-in-radius argument
  (subharmonicity of `|f|²`, Cauchy / Bergman Parseval, or
  `Real.circleAverage`-based mean-value tooling) or an entirely
  different analytical chain. Those are deferred to follow-up sprints
  so this one is single-session-sized.
- Bridge `circleMeanSq` to Mathlib's `Real.circleAverage` (which uses
  the `circleMap` parametrisation `r * Complex.exp (θ * I)` rather than
  `polarCoord.symm`). That bridge is its own follow-up sprint.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).
- Subharmonicity of `circleMeanSq f`, `r`-monotonicity of
  `circleMeanSq f`, Bergman monomial Parseval, Cauchy circle
  representation, or any other ingredient that closes the *inner* half
  of the Korenblum split.
- Push `c_value` above `3554/10000`. That is a follow-up sprint, built
  on top of this one.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `setIntegral_mono_on` cannot be applied
  to the radial integrand because the generator hits an integrability
  shape mismatch that cannot be repaired by re-stating the hypotheses,
  or the membership-in-`outerAnnulus` unfold for `polarCoord.symm (r, θ)`
  with `r ∈ Ioo c 1` cannot be replicated outside `Proof/RadialBergman.lean`):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (e.g. whether the generator tried to lift `outerAnnulus_norm_sq_polar`
  itself rather than re-derive its step 4, whether the integrability
  hypotheses were consolidated or left split, whether
  `setIntegral_mono_on` versus `integral_mono_on` versus
  `MeasureTheory.integral_mono` was used).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
