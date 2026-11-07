# Sprint 012: polar-integrability bridge from contract `Integrable` hypothesis

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V11.lean`
**Target file**: `Candidates/V12.lean`
**Direction**: section2-proof (Bergman scaffolding — derive the polar-pullback
integrability hypothesis used by every existing scaffolding consumer from the
contract-level `Integrable (‖f z‖²) (volume.restrict UnitDisk)` hypothesis)

## Goal

Close the integrability gap between the **`ValidKorenblumBound` contract
hypothesis**

```lean
Integrable (fun z => ‖f z‖ ^ 2)
  ((volume : Measure ℂ).restrict UnitDisk)
```

and the **polar-pullback integrability hypothesis** that every existing
Bergman / radial scaffolding consumer takes (`bergmanNormSq_polar`,
`bergmanNormSq_radial_polar`, `outerAnnulus_norm_sq_polar`,
`innerDisk_norm_sq_polar`, `validKorenblum_of_innerCircleMean_dom`,
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
`bergmanNormSq_termwise_mono`):

```lean
IntegrableOn
  (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
  (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
  ((volume : Measure ℝ).prod volume)
```

In a new file `Proof/PolarIntegrability.lean`, expose:

1. `polar_integrableOn_of_bergmanIntegrable` — *the headline bridge*. For any
   `f : ℂ → ℂ` (no analyticity required, only measurability) with
   `Integrable (fun z => ‖f z‖²) (volume.restrict UnitDisk)`, the polar
   pullback `(r, θ) ↦ r · ‖f (polarCoord.symm (r,θ))‖²` is `IntegrableOn`
   the polar rectangle `Ioo 0 1 ×ˢ Ioo (-π) π` with respect to `volume.prod
   volume`.

   *Statement (or equivalent)*:

   ```lean
   theorem polar_integrableOn_of_bergmanIntegrable
       {f : ℂ → ℂ}
       (hf_meas : AEStronglyMeasurable f volume)
       (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                   ((volume : Measure ℂ).restrict UnitDisk)) :
       IntegrableOn
         (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
         (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
         ((volume : Measure ℝ).prod volume)
   ```

   The measurability hypothesis is taken either as
   `AEStronglyMeasurable f volume` (the canonical Mathlib measurability
   class) or as `Measurable f`, depending on which is cleanest at the
   `polarCoord.symm` composition step. The generator picks whichever
   composes cleanly and records the choice in `Experience.md`. For
   downstream consumers (analytic `f`), measurability is automatic from
   `Continuous f`, so the form of measurability hypothesis is not the
   bottleneck.

   *Implementation sketch* (the generator picks the cleanest path):

   - **Path 1 — via `Complex.lintegral_comp_polarCoord_symm`.** Mathlib's
     `Complex.lintegral_comp_polarCoord_symm` is the `lintegral` form of
     the polar substitution: for measurable `g : ℂ → ℝ≥0∞`,
     `∫⁻ z, g z = ∫⁻ p in polarCoord.target, p.1 • g (polarCoord.symm p)`.
     Apply with `g z := UnitDisk.indicator (‖f z‖²) z` cast to `ℝ≥0∞`
     via `ENNReal.ofReal`. The LHS is `∫⁻ z in UnitDisk, ‖f z‖² ∂volume`,
     finite by `hf_int`; the RHS is `∫⁻ p in polarCoord.target ∩
     polar-preimage of UnitDisk, p.1 · ‖f (polarCoord.symm p)‖²`, which
     equals the polar-rectangle `lintegral` over `Ioo 0 1 ×ˢ Ioo (-π) π`
     by `polarTarget_inter_unitDisk_eq` (sprint 001) up to a measure-zero
     set. Finiteness of the RHS then implies `IntegrableOn` via
     `MeasureTheory.integrableOn_iff_lintegral_lt_top` (or the closely-
     named variant `MeasureTheory.HasFiniteIntegral.integrable_of_aestronglyMeasurable`).

   - **Path 2 — via the direct measurePreserving form.** Mathlib has
     `Complex.measurableEquivPolarCoord` or the
     `MeasureTheory.MeasurePreserving` form of `Complex.polarCoord`. The
     statement is that, modulo Jacobian,
     `Complex.polarCoord.symm` is measure-preserving from
     `(volume.prod volume).withDensity (fun p => p.1)` on
     `Ioo 0 ∞ ×ˢ Ioo (-π) π` to `volume` on `ℂ \ {0}`. Then
     `IntegrableOn` transfers via `MeasurePreserving.integrableOn_image`.

   - **Path 3 — manual: reduce to `lintegral` and apply Tonelli +
     polar substitution by hand.** Cast `‖f z‖²` to `ℝ≥0∞` via
     `ENNReal.ofReal`, apply `Complex.lintegral_comp_polarCoord_symm`
     directly, then bound the polar `lintegral` by the unit-disk
     `lintegral` (which is finite). Finally use
     `MeasureTheory.integrableOn_of_aestronglyMeasurable_of_hasFiniteIntegral`
     (or `Integrable.mk` style). This is the longest but most direct
     route; the generator may prefer it if Path 1 / Path 2 do not unify
     cleanly.

   The generator may consume `polarTarget_inter_unitDisk_eq` (sprint 001)
   to identify the polar target intersected with the unit-disk preimage
   with `Ioo 0 1 ×ˢ Ioo (-π) π` modulo the boundary `r = 1` (which has
   measure zero in the radial direction).

2. `polar_integrableOn_of_continuous_of_bergmanIntegrable` — *the analytic-
   `f` specialisation*. For `f : ℂ → ℂ` with `Continuous f` (or the strictly
   weaker `AnalyticOn ℂ f UnitDisk`) and `Integrable (‖f z‖²)
   (volume.restrict UnitDisk)`, the polar-pullback integrability follows.
   This is just `polar_integrableOn_of_bergmanIntegrable` with the
   measurability hypothesis discharged via `Continuous.aestronglyMeasurable`
   or `AnalyticOn.aestronglyMeasurable` (Mathlib name to investigate). The
   generator may inline this directly into (1) if it compiles cleanly; if
   not, expose it as a separate convenience wrapper.

   *Statement (or equivalent)*:

   ```lean
   theorem polar_integrableOn_of_analyticOn_of_bergmanIntegrable
       {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
       (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                   ((volume : Measure ℂ).restrict UnitDisk)) :
       IntegrableOn
         (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
         (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
         ((volume : Measure ℝ).prod volume)
   ```

   *Implementation sketch*: from `AnalyticOn ℂ f UnitDisk` derive
   `ContinuousOn f UnitDisk` via `AnalyticOn.continuousOn`. Lift to a
   continuous extension or, more cleanly, take measurability from
   `AnalyticOn.aestronglyMeasurable` (or from `MeasurableOn`) on
   `UnitDisk`, then use the contract-side `volume.restrict UnitDisk`
   integrability and (1).

   *Note for the generator*: the contract hypothesis is on the *restricted*
   measure; conversion to a global `AEStronglyMeasurable f volume` may
   require a `Set.indicator` reformulation. The cleanest path is to
   apply (1) directly with measurability sourced from the polar
   composition `f ∘ polarCoord.symm`, since that composition is what the
   final integrand actually evaluates to.

V12 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V11
and the only seed axiom is still `hKorenblum_published_3554`. The
contribution is the new derived module that pins, in Lean, the gateway
between the contract hypothesis and every existing scaffolding consumer.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

- **It is the literal blocking glue between the contract hypothesis and
  every analytic Bergman lemma in the workspace.** Sprints 001–011 built
  eleven Bergman-scaffolding modules — polar pull-back, annulus split,
  radial decomposition, polynomial Parseval, analytic-`tsum` Parseval,
  radial monotonicity, full Bergman A² Parseval — but every single
  consumer (`bergmanNormSq_polar`, `bergmanNormSq_radial_polar`,
  `validKorenblum_of_innerCircleMean_dom`,
  `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
  `bergmanNormSq_termwise_mono`) takes the polar-pullback integrability
  `IntegrableOn (fun (r,θ) => r · ‖f (polarCoord.symm (r,θ))‖²) (Ioo 0 1
  ×ˢ Ioo (-π) π)` as an *opaque hypothesis*. The contract gives instead
  `Integrable (fun z => ‖f z‖²) (volume.restrict UnitDisk)`. Without a
  bridge between the two, no future c-push attempt can compose the
  contract with any of the existing scaffolding without either (a)
  re-deriving this glue ad hoc inside the c-push proof or (b) leaving
  `STATUS=BLOCKED` on integrability bookkeeping that *should not* be the
  bottleneck.

- **It is the smallest sprint that materially advances the science.**
  Every sprint past V11 will need this bridge. Doing it as a standalone
  scaffolding sprint (rather than inline inside a future c-push)
  isolates the polar-substitution / lintegral / change-of-variables
  bookkeeping into a single derived theorem that all downstream
  consumers can chain through. This is exactly the same pattern as
  sprints 001–011 (each one isolated a single Bergman building block);
  sprint 012 closes the only remaining gap between *contract* and
  *scaffolding* on the integrability axis.

- **Three Mathlib paths, all bounded.** As above. The `lintegral` form
  via `Complex.lintegral_comp_polarCoord_symm` is the most direct; the
  measurePreserving form via `Complex.measurableEquivPolarCoord` is the
  cleanest *if* that exact spelling exists in Mathlib v4.28; the manual
  Tonelli + polar substitution is the longest fallback. The generator
  records in `Experience.md` which path was tried and why it was the
  cleanest.

- **Falsifiable in one Generator session.** Each path above is one
  Mathlib lemma chase. The genuinely-uncertain step is whether the
  Mathlib `polarCoord` API exposes a measure-preserving / lintegral
  identity that unifies with the *bare* `volume.prod volume` measure on
  `Ioo 0 1 ×ˢ Ioo (-π) π` (rather than the `withDensity (· · r)`
  measure on `Ioi 0 ×ˢ Ioo (-π) π`); if not, the generator must thread
  the `r`-Jacobian explicitly. This bookkeeping is exactly the kind of
  thing the generator's declared scope covers (*"Lebesgue-integral
  monotonicity on annulus regions"*, *"`nlinarith` / `polyrith` /
  `field_simp` / `ring` chains hundreds of lines long"*).

- **Why not push c.** Pushing `c` past `0.3554` requires *new analytical
  content* (subharmonic mean-value, Cauchy coefficient bound from
  boundary sup-norm, pseudohyperbolic / Möbius-distance arguments, or
  Hayman–Korenblum-style maximum-principle chain). Each of those is at
  minimum one full sprint of mathematical content (and likely more).
  Without the polar-integrability bridge, *none* of those c-push
  attempts can chain to the existing Bergman scaffolding without
  re-deriving sprint 012's content first. The bridge is the
  prerequisite, not the inverse.

- **Why not pursue analytical scaffolding instead.** The two natural
  analytical-scaffolding follow-ups to sprint 011 are (a) a Cauchy
  coefficient bound `‖a_k‖ ≤ M(r)/r^k` from the boundary sup-norm
  `M(r) := sup_{‖z‖=r} ‖f(z)‖`, and (b) right-continuity / strict
  monotonicity of `r ↦ circleMeanSq f r` for analytic `f`. Both are
  honest mathematical content, but both are *strictly downstream* of
  the polar-integrability bridge: any proof of (a) consumed by a
  c-push needs to thread the contract hypothesis through to a
  Bergman-A² inequality, which routes through the polar form. Sprint
  012 is the shortest path to unblocking either.

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"Lebesgue-integral monotonicity on annulus regions"*, *"bridging
  pointwise modulus inequalities to boundary integrals"*, and the
  generator has already exercised `Complex.integral_comp_polarCoord_symm`
  / `Complex.lintegral_comp_polarCoord_symm` / `polarTarget_inter_unitDisk_eq`
  in sprints 001–003. The polar-integrability bridge is exactly one
  composition layer above what is already in the build graph.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/PolarIntegrability.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, and `Proof.PolarBergman`
    (the latter for `polarCoord_symm_mem_unitDisk_iff` and the
    polar-target bookkeeping already proved in sprint 001),

  - exposes (1) `polar_integrableOn_of_bergmanIntegrable` (or equivalent
    name), with statement as above. The measurability hypothesis is at
    the generator's discretion (`AEStronglyMeasurable f volume`,
    `Measurable f`, or the polar-composition form
    `AEStronglyMeasurable (f ∘ polarCoord.symm)
       ((volume.prod volume).restrict (Ioo 0 1 ×ˢ Ioo (-π) π))`);
    pick whichever composes cleanly through Mathlib's polar lemma.

  - exposes (2) `polar_integrableOn_of_analyticOn_of_bergmanIntegrable`
    (or equivalent name), the analytic-`f` specialisation. Discharges
    the measurability hypothesis from `AnalyticOn ℂ f UnitDisk`. May
    be inlined into (1) if cleaner.

  - all theorems must be `theorem`/`lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as long
    as the conclusion is unchanged.

- `ProofRefinement/Korenblum/Candidates/V12.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V12`, marked
  `-- @parent V11`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V11),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V11,
  - imports the same module set as V11 plus
    `ProofRefinement.Korenblum.Proof.PolarIntegrability` so that the
    new module is part of V12's compile graph and is exercised by the
    build. No structural use of the new lemma in V12 itself is
    required.

- No edits to `lemma.toml`. No edits to V0/.../V11 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V12` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V12.lean` succeeds (the evaluator
   accepts V12 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V11; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.

3. The file `ProofRefinement/Korenblum/Proof/PolarIntegrability.lean`
   contains:
   - one `theorem` (or `lemma`) named
     `polar_integrableOn_of_bergmanIntegrable` (or equivalently named)
     whose conclusion is the polar-pullback `IntegrableOn` form, with a
     hypothesis equivalent to (or strictly stronger than) the contract's
     `Integrable (fun z => ‖f z‖²) (volume.restrict UnitDisk)` plus a
     measurability hypothesis on `f`;
   - one `theorem` (or `lemma`) named
     `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (or
     equivalently named) whose conclusion is the polar-pullback
     `IntegrableOn` form for `f` analytic on `UnitDisk` and Bergman-A²
     integrable. May be inlined into the first if cleaner.
   All theorems must be `theorem` / `lemma`, never `axiom`, with no
   `sorry`. The proof must genuinely *use* a Mathlib polar-substitution
   lemma (one of `Complex.lintegral_comp_polarCoord_symm`,
   `Complex.integral_comp_polarCoord_symm`, the `MeasureTheory.MeasurePreserving`
   form of `Complex.polarCoord`, or a closely-named variant) — not
   bypass via a parallel non-polar argument.

4. The new module `Proof.PolarIntegrability` must be **used**, even
   trivially, somewhere in V12's transitive compile graph (importing it
   from V12 is sufficient — it forces the module to compile as part of
   V12's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V11.lean`) or the existing
  `Proof/*.lean` files. Threading the new bridge through the existing
  consumers (e.g., updating `validKorenblum_of_innerCircleMean_dom` to
  derive `hf_polar` internally from a Bergman-integrability hypothesis)
  is the *next* sprint's job, not this one's. The downstream rewiring
  is a separate, larger refactor; this sprint pins the bridge as a
  standalone derived theorem that future sprints may consume.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the polar-substitution chain is genuinely
  blocked on a missing Mathlib API, the generator must `STATUS=BLOCKED`
  with the precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the polar-integrability bridge that any
  future c-push consumer must consume.

- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`

- Blocked within scope (e.g. `Complex.lintegral_comp_polarCoord_symm` is
  not the exact Mathlib name in v4.28 and the closely-named variant
  has a different measure shape that does not unify with
  `volume.prod volume` on `Ioo 0 1 ×ˢ Ioo (-π) π`; or the polar target
  intersection lemma `polarTarget_inter_unitDisk_eq` (sprint 001) does
  not unify with the polar `lintegral` form's underlying domain;
  or the conversion between `Integrable (volume.restrict UnitDisk)` and
  a global `IntegrableOn UnitDisk` introduces a measurability
  obstruction that does not discharge cleanly):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (Path 1 / Path 2 / Path 3 from the Why section above; whether
  the measurability hypothesis was tried as `AEStronglyMeasurable f
  volume`, `Measurable f`, or the polar-composition form;
  whether `Complex.lintegral_comp_polarCoord_symm` was found at the
  expected name or under a different name, e.g. with the underscore
  removed or with a different argument order; whether the polar
  Jacobian was threaded explicitly via `Measure.withDensity` or
  implicitly via a measure-preserving lemma).

  **Fallback form** (if the polar-pullback integrability is too brittle
  in any direct form): the generator may instead expose only a *weaker*
  conclusion that suffices for downstream consumers — for example, the
  integrability of `(r, θ) ↦ ‖f (polarCoord.symm (r,θ))‖²` (without the
  `r`-Jacobian factor) on `Ioo 0 1 ×ˢ Ioo (-π) π`, plus a separate
  trivial bound `r ≤ 1` on `Ioo 0 1` to recover the
  `r · ‖...‖²` form via `Integrable.mul_const` or
  `Integrable.bdd_mul`. This is strictly weaker but still enough for
  every existing scaffolding consumer that only uses the polar-pullback
  integrability as an opaque hypothesis. The fallback is acceptable if
  and only if the generator records in `Experience.md` why the
  stronger form was infeasible.

- Needs human trust expansion (e.g. a genuinely missing Mathlib polar-
  substitution lemma that justifies a new axiom or import-policy
  change): `STATUS=BLOCKED_NEEDS_HUMAN`.
