# Sprint 001: Polar-coordinate decomposition of `bergmanNormSq`

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V0.lean`
**Target file**: `Candidates/V1.lean`
**Direction**: section2-proof (Bergman scaffolding)

## Goal

Build the polar-coordinate decomposition of `bergmanNormSq` as a derived
theorem in `ProofRefinement/Korenblum/Proof/PolarBergman.lean` against
Mathlib, and re-prove `ValidKorenblumBound c_value` at the seed
`c = 3554/10000` in `Candidates/V1.lean` using the existing seed axiom.

The intended scaffolding lemma is, schematically:

```
theorem bergmanNormSq_polar (f : ℂ → ℂ)
    (hf_meas : Measurable f) :
    bergmanNormSq f =
      ∫ r in Set.Ioo (0 : ℝ) 1,
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖f (r * (Real.cos θ + Real.sin θ * Complex.I))‖ ^ 2 * r) := by
  ...
```

(The exact statement, hypotheses on `f`, and the inner-integral measure can
be tightened by the generator. Acceptable variants include using
`Complex.exp (θ * Complex.I)`, expressing the inner integral as
`circleIntegral`, or threading `Integrable` / `AEStronglyMeasurable` side
hypotheses. What matters is that the lemma rewrites
`∫_{UnitDisk} ‖f z‖² ∂volume` as a polar `r • ...` repeated integral over
`r ∈ (0,1)`.)

This sprint is **scaffolding-only**: `c_value` does not increase. V1 ships
with the same `c = 3554/10000` and the same `hKorenblum_published_3554`
axiom as V0. The contribution is the new derived module, which is required
by every plausible non-trivial route that pushes `c_value` above
`0.3554` in this no-PF arm.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- This is the first generator session in the workspace, with no prior
  attempts on record. Every honest route to a higher `c` (annulus integral
  comparison, subharmonic circle-mean monotonicity, Bergman monomial
  Parseval, pseudohyperbolic / Korenblum extremal arguments) needs to
  decompose `∫_{UnitDisk} ‖f‖² dA` into a radial integral against circle
  integrals. Without that bridge, no later sprint can avoid re-deriving it
  inline.
- Mathlib has the right primitive: `Complex.integral_comp_polarCoord_symm`
  in `Mathlib.Analysis.SpecialFunctions.PolarCoord` rewrites
  `∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) = ∫ p, f p`, with
  `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`. Restricting to
  `UnitDisk = Metric.ball 0 1` reduces `r > 0` to `r ∈ (0,1)`. So the
  derivation is short in principle and lives entirely inside Mathlib's
  measure-theory and special-functions APIs — well within the generator's
  declared scope.
- Pinning the lemma in `Proof/` (admitted by `lemma.toml:[import_policy]`
  via the `ProofRefinement.Korenblum.Proof` prefix) makes it reusable by
  all subsequent candidate versions without further trust changes.
- This sprint also produces an honest baseline data point: a
  scaffolding-only V1 confirms whether the Bergman polar bridge is
  derivable against Mathlib in one session, or whether the obstruction is
  structural (in which case we learn something about the cost of the no-PF
  ablation).

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/PolarBergman.lean`: **new file**, in the
  `ProofRefinement.Korenblum` namespace, containing
  - any helper lemmas (e.g. `‖Complex.polarCoord.symm (r, θ)‖ = |r|`,
    membership of `polarCoord.symm (r, θ)` in `UnitDisk` for
    `r ∈ Ioo 0 1`, `θ ∈ Ioo (-π) π`),
  - a measurability / integrability lemma sufficient for the rewrite,
  - the headline lemma `bergmanNormSq_polar` (or an equivalent shape — see
    Goal), expressing `bergmanNormSq f` as a repeated integral
    `∫ r in Ioo 0 1, ∫ θ in Ioo (-π) π, ‖f (polarCoord.symm (r,θ))‖^2 * r`
    (with the obvious volume measures).
  - The proof should call `Complex.integral_comp_polarCoord_symm` (or
    `Complex.lintegral_comp_polarCoord_symm`) and Fubini
    (`MeasureTheory.integral_prod` / `setIntegral_prod`) to peel the inner
    integral.
- `ProofRefinement/Korenblum/Candidates/V1.lean`: **new file** in namespace
  `ProofRefinement.Korenblum.Candidates.V1`, marked `-- @parent V0`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V0),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V0,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman` so that the new
    module is part of V1's compile graph and is exercised by the build.
    No structural use of `bergmanNormSq_polar` is required in V1 itself.
- No edits to `lemma.toml`. No edits to V0. No new axioms beyond the
  already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V1` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V1.lean` succeeds (the evaluator
   accepts V1 as a well-formed candidate). The score `c_value = 3554/10000`
   is **unchanged** from V0; this is expected and not a failure of the
   sprint, but it must be reported truthfully in the run.
3. The file `ProofRefinement/Korenblum/Proof/PolarBergman.lean` contains a
   theorem (named `bergmanNormSq_polar` or as renamed by the generator)
   that rewrites `bergmanNormSq f` as a repeated polar integral over
   `r ∈ Ioo 0 1`, `θ ∈ Ioo (-π) π`, with the `r` Jacobian factor present.
   The theorem must be `theorem`, not `axiom`, with no `sorry`.
4. The polar lemma must be **used**, even trivially, somewhere in V1's
   transitive compile graph (importing `Proof.PolarBergman` from V1 is
   sufficient — it forces the module to compile as part of V1's build).

## Out of scope

- Edit older candidates (`V0.lean`).
- Change the final theorem statement.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the generator finds the polar lemma genuinely
  blocked on a missing Mathlib API, it must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize the polar lemma.
- Attempt to push `c_value` above `3554/10000`. That is the next sprint,
  built on top of this one.
- Write circle-mean monotonicity, subharmonicity, or Parseval-style
  lemmas. Those are deliberately deferred to follow-up sprints so this
  one is single-session-sized.
- Edit `lemma.toml` (no policy expansion needed; the `Proof.` prefix is
  already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. polar lemma not closable against current
  Mathlib without a missing API): `STATUS=BLOCKED` with a precise note in
  `Experience.md` recording which Mathlib lemma was the obstruction and
  which approaches were tried (Fubini direction, lintegral-vs-integral
  variant, ae-restriction handling, integrability hypothesis shape).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
