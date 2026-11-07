# Sprint 002: Annulus split + outer-annulus monotonicity for `bergmanNormSq`

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V1.lean`
**Target file**: `Candidates/V2.lean`
**Direction**: section2-proof (Bergman scaffolding)

## Goal

Build the **annulus decomposition** of `bergmanNormSq` and the **outer-annulus
monotonicity** corollary as derived theorems against Mathlib in a new
`ProofRefinement/Korenblum/Proof/AnnulusBergman.lean`, then re-prove
`ValidKorenblumBound c_value` at the seed `c = 3554/10000` in
`Candidates/V2.lean` using the existing seed axiom.

The two intended scaffolding lemmas are, schematically:

```lean
/-- Outer annulus `c < ‖z‖ < 1` (open). -/
def outerAnnulus (c : ℝ) : Set ℂ := {z : ℂ | c < ‖z‖ ∧ ‖z‖ < 1}

/-- Inner closed disk `‖z‖ ≤ c`, intersected with the unit disk. -/
def innerDisk (c : ℝ) : Set ℂ := {z : ℂ | ‖z‖ ≤ c} ∩ UnitDisk

/-- Splitting the Bergman A² norm at radius `c`. -/
theorem bergmanNormSq_split (f : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf : Integrable (fun z => ‖f z‖ ^ 2)
            ((volume : Measure ℂ).restrict UnitDisk)) :
    bergmanNormSq f
      = (∫ z in innerDisk c, ‖f z‖ ^ 2)
        + (∫ z in outerAnnulus c, ‖f z‖ ^ 2) := ...

/-- Outer-annulus monotonicity: pointwise `‖f‖ ≤ ‖g‖` on the open
outer annulus implies the outer-annulus integrals are ordered. -/
theorem outerAnnulus_norm_sq_mono
    (f g : ℂ → ℂ) (c : ℝ)
    (hf : IntegrableOn (fun z => ‖f z‖ ^ 2) (outerAnnulus c))
    (hg : IntegrableOn (fun z => ‖g z‖ ^ 2) (outerAnnulus c))
    (h : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2)
      ≤ (∫ z in outerAnnulus c, ‖g z‖ ^ 2) := ...
```

(The exact set names, set definitions, hypothesis shape, and any
ae-strongly-measurable side conditions can be tightened by the generator.
Acceptable variants include using `Metric.closedBall (0:ℂ) c ∩ UnitDisk` for
the inner disk, `Metric.ball (0:ℂ) 1 \ Metric.closedBall (0:ℂ) c` for the
outer annulus, or splitting via `setIntegral_union` versus
`integral_indicator_add`. What matters is that the two headline lemmas
hold and are useful.)

This sprint is **scaffolding-only**: `c_value` does not increase. V2 ships
with the same `c = 3554/10000` and the same `hKorenblum_published_3554`
axiom as V1. The contribution is the new derived module: every plausible
Korenblum-style improvement past `0.3554` factors through the
inner-vs-outer annulus split with the outer side handled by the
hypothesis-driven monotonicity, so this is the next-smallest reusable
Bergman scaffolding piece after the polar decomposition.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- The `ValidKorenblumBound` hypothesis says `‖f‖ ≤ ‖g‖` on the *outer*
  annulus `c < ‖z‖ < 1`, and asks us to compare `∫_𝔻 ‖f‖² ≤ ∫_𝔻 ‖g‖²` on
  the *whole* disk. The standard structural move is
  `‖f‖²_{A²} = inner_part + outer_part`, with the outer part dominated by
  the corresponding `g`-integral by direct monotonicity of integrals. The
  inner part is the genuinely hard half (it's where Korenblum's argument
  bites). This sprint isolates and cleanly proves the easy half, leaving
  the inner part as the explicit obstruction for follow-up sprints.
- Both lemmas are tight against Mathlib's existing API:
  - `bergmanNormSq_split` is `setIntegral_union` with the disk split as
    `UnitDisk = innerDisk c ∪ outerAnnulus c`, modulo measurability of the
    annulus and disjointness up to a measure-zero sphere.
  - `outerAnnulus_norm_sq_mono` is `setIntegral_mono_on` (or the
    a.e. variant) applied to the squared-norm functions, which are
    non-negative and measurable.
  Both proofs sit comfortably in the generator's declared scope (Lebesgue
  monotonicity, `setIntegral_union`, `MeasurableSet` for `Metric.ball`).
- Without these handles, every later sprint that compares `f` and `g`
  on the outer annulus must re-derive the split inline. Pinning the
  decomposition lemma in `Proof/` (admitted by
  `lemma.toml:[import_policy]` via the `ProofRefinement.Korenblum.Proof`
  prefix) makes it reusable across all future candidates without any
  trust changes.
- This sprint also produces a falsifiable data point about the no-PF
  arm: if `setIntegral_union` and `setIntegral_mono_on` cannot close the
  decomposition cleanly in one session, the obstruction is structural,
  not capability — and the `STATUS=BLOCKED` log will record exactly
  which Mathlib lemma was the bottleneck.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/AnnulusBergman.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace, containing
  - definitions for `outerAnnulus c` and `innerDisk c` (or chosen Mathlib
    set forms — see Goal),
  - measurability lemmas (`MeasurableSet (outerAnnulus c)`,
    `MeasurableSet (innerDisk c)`) — these should be one-liners using
    `Metric.isOpen_ball.measurableSet`, `IsClosed.measurableSet`, etc.,
  - a disjoint-union lemma showing the open unit disk is the disjoint
    union of `innerDisk c` and `outerAnnulus c` up to the measure-zero
    sphere `‖z‖ = c` (use `MeasurableSet.union`, ae-disjointness via the
    sphere having Lebesgue measure zero in `ℂ ≃ ℝ²`),
  - the headline lemma `bergmanNormSq_split` (or equivalent shape — see
    Goal),
  - the headline lemma `outerAnnulus_norm_sq_mono` (or equivalent shape
    — see Goal).
  - The proofs should call `MeasureTheory.setIntegral_union` (and/or
    `integral_indicator_add` / `setIntegral_indicator`) for the split,
    and `MeasureTheory.setIntegral_mono_on` (or `setIntegral_mono_ae`)
    for the monotonicity. No appeal to `bergmanNormSq_polar` is needed
    or expected; the two scaffolding modules are independent.
- `ProofRefinement/Korenblum/Candidates/V2.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V2`, marked
  `-- @parent V1`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V1),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V1,
  - imports both `ProofRefinement.Korenblum.Proof.PolarBergman` and
    `ProofRefinement.Korenblum.Proof.AnnulusBergman` so that the new
    module is part of V2's compile graph and is exercised by the build.
    No structural use of the new lemmas is required in V2 itself.
- No edits to `lemma.toml`. No edits to V0/V1. No new axioms beyond the
  already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V2` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V2.lean` succeeds (the evaluator
   accepts V2 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V1; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/AnnulusBergman.lean`
   contains two `theorem`s (or `lemma`s) — names may differ, but their
   *content* must:
   - one rewrites `bergmanNormSq f` (or, equivalently, the integral of
     `‖f z‖^2` over the unit disk under the appropriate integrability
     hypothesis on `f`) as a sum of an inner-disk integral
     (`{z : ‖z‖ ≤ c} ∩ UnitDisk` or its open variant) and an
     outer-annulus integral (`{z : c < ‖z‖ < 1}`),
   - the other concludes `∫_{outer} ‖f‖² ≤ ∫_{outer} ‖g‖²` from the
     pointwise hypothesis `∀ z ∈ outer, ‖f z‖ ≤ ‖g z‖` (with
     appropriate integrability side hypotheses on `f` and `g`).
   Both must be `theorem`/`lemma`, not `axiom`, with no `sorry`.
4. The new module `Proof.AnnulusBergman` must be **used**, even
   trivially, somewhere in V2's transitive compile graph (importing
   `Proof.AnnulusBergman` from V2 is sufficient — it forces the module
   to compile as part of V2's build).

## Out of scope

- Edit older candidates (`V0.lean`, `V1.lean`) or `Proof/PolarBergman.lean`.
- Change the final theorem statement.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the generator finds either lemma genuinely
  blocked on a missing Mathlib API, it must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize the lemma.
- Attempt to push `c_value` above `3554/10000`. That is a follow-up
  sprint, built on top of this one and the polar module.
- Inner-disk monotonicity, circle-mean monotonicity, subharmonicity of
  `|f|²`, Bergman monomial Parseval, or any other ingredient that
  closes the *inner* half of the Korenblum split. Those are deliberately
  deferred to follow-up sprints so this one is single-session-sized.
- Edit `lemma.toml` (no policy expansion needed; the `Proof.` prefix is
  already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `setIntegral_union` not directly applicable
  due to the sphere `‖z‖ = c` boundary, ae-disjointness handling fails,
  `setIntegral_mono_on` requires a hypothesis shape we cannot supply):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (`setIntegral_union` vs `integral_indicator_add` vs
  `setIntegral_indicator`, ae-restriction handling, integrability
  hypothesis shape, sphere-measure-zero argument).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
