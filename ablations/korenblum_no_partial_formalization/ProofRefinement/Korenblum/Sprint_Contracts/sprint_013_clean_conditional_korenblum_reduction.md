# Sprint 013: clean conditional Korenblum reduction with contract-shaped hypotheses

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V12.lean`
**Target file**: `Candidates/V13.lean`
**Direction**: section2-proof (Bergman scaffolding — derive the six remaining
radial / circle integrability hypotheses of
`validKorenblum_of_innerCircleMean_dom` from the contract's bare
`Integrable (‖f z‖²) (volume.restrict UnitDisk)` plus `AnalyticOn ℂ f UnitDisk`,
and expose a clean conditional Korenblum reduction whose hypotheses are
exactly `ValidKorenblumBound`-contract-shaped + `h_inner` + `h_outer`)

## Goal

Close the **last remaining plumbing gap** between the
`ValidKorenblumBound c` contract and the existing conditional Korenblum
reduction `validKorenblum_of_innerCircleMean_dom` (sprint 005, in
`Proof/RadialSplit.lean`).

Sprint 012 built the polar-pullback bridge
`polar_integrableOn_of_analyticOn_of_bergmanIntegrable`, but the conditional
reduction `validKorenblum_of_innerCircleMean_dom` takes **eight** integrability
hypotheses, only **two** of which (`hf_polar`, `hg_polar`) are direct outputs
of the polar bridge. The remaining six are radial / circle integrability:

```lean
-- Radial-form integrability of `circleMeanSq · r` on each half:
hf_inner_int : IntegrableOn (fun r => circleMeanSq f r * r) (Ioc 0 c) volume
hf_outer_int : IntegrableOn (fun r => circleMeanSq f r * r) (Ioo c 1) volume
hg_inner_int : IntegrableOn (fun r => circleMeanSq g r * r) (Ioc 0 c) volume
hg_outer_int : IntegrableOn (fun r => circleMeanSq g r * r) (Ioo c 1) volume

-- Per-radius θ-integrability for outer-half slices:
hf_circle : ∀ r ∈ Ioo c 1, IntegrableOn
              (fun θ => ‖f (polarCoord.symm (r, θ))‖²) (Ioo (-π) π) volume
hg_circle : ∀ r ∈ Ioo c 1, IntegrableOn
              (fun θ => ‖g (polarCoord.symm (r, θ))‖²) (Ioo (-π) π) volume
```

In a new file `Proof/RadialIntegrability.lean`, derive these six hypotheses
from the polar-pullback `IntegrableOn` hypothesis (the output of sprint
012's bridge) via Fubini-Tonelli on the product measure, plus product-measure
restriction lemmas. Then in a new file `Proof/CleanConditional.lean`, expose
the headline composed theorem:

```lean
theorem validKorenblum_of_inner_outer_dom_of_analyticOn
    (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk))
    (hg_int : Integrable (fun z => ‖g z‖ ^ 2)
                ((volume : Measure ℂ).restrict UnitDisk))
    (h_inner : ∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r)
    (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
    bergmanNormSq f ≤ bergmanNormSq g
```

This is the **clean** conditional Korenblum reduction. With it in place, a
future c-push consumer can compose against `ValidKorenblumBound c'`'s
contract hypotheses (`AnalyticOn`, `Integrable (‖·‖²) (volume.restrict UnitDisk)`,
plus an outer-annulus pointwise dominance) without threading any radial /
circle integrability bookkeeping. The single remaining mathematical content
of any future c-push is `h_inner` — the inner-half radial dominance — which
is the genuine Korenblum content.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

V13 ships with `c_value = 3554/10000` unchanged from V12; this is
scaffolding-only. The contribution is the new derived modules that finally
close the contract → conditional plumbing chain. After this sprint, every
remaining gap to a c-push attempt is *mathematical content*, not Lean
plumbing.

## Why

- **It is the literal blocking glue between sprint 012 (polar-bridge) and
  sprint 005 (conditional reduction).** Sprint 012 lifted the contract's
  Bergman integrability to a polar-pullback `IntegrableOn` over
  `Ioo 0 1 ×ˢ Ioo (-π) π`. Sprint 005's conditional reduction takes the
  polar-pullback as one of its eight hypotheses but additionally takes six
  more radial / per-θ integrability hypotheses, none of which are direct
  outputs of the polar-bridge. Those six are derivable from the polar-
  bridge output via Fubini-Tonelli, but until that derivation is pinned in
  Lean, no future c-push can compose these two scaffolding pieces without
  re-deriving the integrability bookkeeping ad hoc inside the c-push proof.

- **It is the smallest sprint that materially advances the science past
  V12.** Every alternative scaffolding direction (Cauchy coefficient
  bounds, polynomial-density approximation, subharmonicity-based mean-
  value chains) is *strictly downstream* of having the conditional
  Korenblum reduction in contract-shaped form. Whatever genuine c-push
  attempt comes next must consume some clean conditional, and this is
  the cleanest one available given the existing scaffolding tower.

- **Concrete Mathlib path.** The six derivations all route through the
  same family of Mathlib lemmas:

  - Fubini's theorem on `volume.prod volume` over a product set:
    `MeasureTheory.Integrable.integral_prod_left` /
    `MeasureTheory.IntegrableOn.integral_prod_left` (the `IntegrableOn`
    consumer; or alternatively through `setIntegral_prod` + Fubini-Tonelli).
  - Per-slice integrability: `MeasureTheory.Integrable.integrable_prod_left`
    / `Integrable.prod_left_ae` (each slice is integrable for almost every
    radius).
  - Set-restriction monotonicity: `IntegrableOn.mono_set` from
    `Ioc 0 c ⊆ Ioo 0 1` (with the boundary `r = 0` and `r = c`
    handled appropriately) and `Ioo c 1 ⊆ Ioo 0 1`.
  - Promotion from "almost-every" radial slice integrability to "every"
    radial slice integrability via the per-θ `circleMeanSq` definition
    being absolutely continuous against the polar-pullback's
    Fubini-restricted `r`-marginal.

  Each of these is one Mathlib lemma chase bounded under the generator's
  declared scope (*"Lebesgue-integral monotonicity on annulus regions"*,
  *"Cauchy–Schwarz on boundary integrals"*, *"`nlinarith` / `polyrith` /
  `field_simp` / `ring` chains hundreds of lines long"*).

- **Falsifiable in one Generator session.** The six derivations are all
  variations on the same Fubini-Tonelli pattern; the genuine bookkeeping
  is whether Mathlib's `Integrable.prod_left_ae` / `integral_prod_left`
  expose the per-slice integrability cleanly enough to discharge `hf_circle`
  /  `hg_circle` for *every* radius `r ∈ Ioo c 1` (rather than almost-every).
  The fallback if Mathlib only gives almost-every is to weaken the
  conditional theorem's hypothesis to almost-every (matching what the
  scaffolding actually consumes via `setIntegral_congr_ae`); the conditional
  reduction's downstream consumers can be patched accordingly.

- **Why not push c.** Pushing `c` past `0.3554` requires *new analytical
  content* — specifically the inner-circle-mean dominance hypothesis
  `h_inner` of `validKorenblum_of_innerCircleMean_dom`. There is no
  cheap or short path to this content from Mathlib; the Korenblum /
  Hayman / Wang chain is genuinely several pages of extremal-function
  arguments. Until the conditional reduction is in clean contract-shaped
  form, every c-push attempt has to re-derive the integrability plumbing
  *before* attempting the genuine analytical content. Sprint 013 is the
  prerequisite, not the inverse.

- **Why not pursue Cauchy coefficient bounds, polynomial-density
  approximation, or subharmonic mean-value scaffolding.** All three are
  legitimate analytical scaffolding, but none of them compose against
  `ValidKorenblumBound c'` cleanly without first having the conditional
  reduction in contract-shaped form. Sprint 013 is the unique path that
  unblocks all three downstream directions simultaneously.

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"termwise summability and `tsum`-level rearrangements"*,
  *"Lebesgue-integral monotonicity on annulus regions"*, and the generator
  has already exercised `Integrable.integral_prod_left`,
  `Measure.prod_restrict`, `setIntegral_mono_on`, `setIntegral_prod` in
  sprints 001–012. The radial-integrability bridge is exactly one
  composition layer above what is already in the build graph.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/RadialIntegrability.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.AnnulusBergman`, `Proof.RadialBergman`, and
    `Proof.PolarIntegrability` (the latter for the polar-bridge output
    that this file's six derivations all start from),

  - exposes the six radial / per-θ integrability handles, each derived
    from the polar-pullback `IntegrableOn` hypothesis. The exact names
    and statement shapes are at the generator's discretion, but the
    conclusion forms must match the consumers in
    `validKorenblum_of_innerCircleMean_dom`. Suggested names (the
    generator may rename for clarity):

    ```lean
    theorem radial_integrableOn_circleMeanSq_mul_r_Ioc
        {f : ℂ → ℂ}
        (hf_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
        IntegrableOn (fun r => circleMeanSq f r * r)
                     (Set.Ioc 0 c) volume

    theorem radial_integrableOn_circleMeanSq_mul_r_Ioo
        ... -- same shape, on Ioo c 1

    theorem circle_integrableOn_normSq_polar
        {f : ℂ → ℂ}
        (hf_polar : ...)
        {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
        ∀ᵐ r ∂(volume.restrict (Set.Ioo c 1)),
          IntegrableOn (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
                       (Set.Ioo (-Real.pi) Real.pi) volume
    ```

    The `circle_integrableOn_normSq_polar` form may be `∀ᵐ` rather than
    `∀` if the latter does not discharge cleanly from
    `Integrable.prod_left_ae`. If so, the conditional reduction's
    downstream call to `circleMeanSq_le_of_outerAnnulus_dom` (which
    consumes per-radius `hf_circle`) will need to be re-routed through
    a pointwise-`ae`-converted form. The generator picks whichever form
    composes cleanly and records the choice in `Experience.md`.

  - all theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. Names are guidelines.

- `ProofRefinement/Korenblum/Proof/CleanConditional.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.AnnulusBergman`,
    `Proof.RadialBergman`, `Proof.RadialSplit`, `Proof.PolarIntegrability`,
    `Proof.RadialIntegrability` (and any others needed for the composition),

  - exposes the headline clean conditional Korenblum reduction:

    ```lean
    theorem validKorenblum_of_inner_outer_dom_of_analyticOn
        (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
        (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
        (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                    ((volume : Measure ℂ).restrict UnitDisk))
        (hg_int : Integrable (fun z => ‖g z‖ ^ 2)
                    ((volume : Measure ℂ).restrict UnitDisk))
        (h_inner : ∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r)
        (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
        bergmanNormSq f ≤ bergmanNormSq g
    ```

    *Implementation sketch*: apply `polar_integrableOn_of_analyticOn_of_bergmanIntegrable`
    to `f` and to `g` to obtain `hf_polar` and `hg_polar`. Apply the
    six radial / circle integrability bridges from
    `Proof/RadialIntegrability.lean` to each polar-pullback. Then apply
    `validKorenblum_of_innerCircleMean_dom` (sprint 005) with all eight
    hypotheses now derived from the contract.

  - if the per-radius circle-integrability `hf_circle` / `hg_circle` is only
    available in `∀ᵐ` form, the generator may need to expose an
    intermediate form `validKorenblum_of_innerCircleMean_dom_ae` in
    `Proof/RadialSplit.lean` *as a separate theorem* (not an edit to the
    existing one — the existing form remains as-is) or as a private helper
    in `Proof/CleanConditional.lean`. The generator's choice; either is
    acceptable as long as the headline `validKorenblum_of_inner_outer_dom_of_analyticOn`
    has the contract-shaped statement above.

  - all theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`.

- `ProofRefinement/Korenblum/Candidates/V13.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V13`, marked
  `-- @parent V12`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V12),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V12,
  - imports the same module set as V12 plus
    `ProofRefinement.Korenblum.Proof.RadialIntegrability` and
    `ProofRefinement.Korenblum.Proof.CleanConditional`, so that both new
    modules are part of V13's compile graph and exercised by the build.
    No structural use of the new lemmas in V13 itself is required.

- No edits to `lemma.toml`. No edits to V0/.../V12 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V13` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V13.lean` succeeds (the evaluator
   accepts V13 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V12; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.

3. The file `ProofRefinement/Korenblum/Proof/RadialIntegrability.lean`
   contains theorems (or lemmas) deriving each of the six radial /
   per-θ integrability conclusions used by
   `validKorenblum_of_innerCircleMean_dom`, with hypothesis being the
   polar-pullback `IntegrableOn` of `(r,θ) ↦ r · ‖f (polarCoord.symm
   (r,θ))‖²` on `Ioo 0 1 ×ˢ Ioo (-π) π` (and analogously for `g`).
   The two `circle_integrable*` per-radius forms may be either
   per-radius (`∀ r ∈ Ioo c 1`) or almost-every-radius (`∀ᵐ r`).
   All theorems must be `theorem` / `lemma`, never `axiom`, with no
   `sorry`. The proofs must genuinely route through Mathlib's
   Fubini-Tonelli machinery
   (`Integrable.integral_prod_left`, `Integrable.prod_left_ae`,
   `Measure.prod_restrict`, `setIntegral_prod`, `MeasureTheory.IntegrableOn.mono_set`,
   or closely-named variants).

4. The file `ProofRefinement/Korenblum/Proof/CleanConditional.lean`
   contains a `theorem` (or `lemma`) named
   `validKorenblum_of_inner_outer_dom_of_analyticOn` (or equivalently
   named) whose statement is the contract-shaped clean conditional
   Korenblum reduction above. The proof must compose
   `polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (sprint 012),
   the six radial / circle integrability bridges (this sprint), and
   `validKorenblum_of_innerCircleMean_dom` (sprint 005). It must not
   re-derive any of those three pieces inline; it is genuinely a
   composition.

5. Both new modules `Proof.RadialIntegrability` and
   `Proof.CleanConditional` must be **used**, even trivially, somewhere
   in V13's transitive compile graph (importing them from V13 is
   sufficient — it forces both modules to compile as part of V13's
   build).

## Out of scope

- Edit older candidates (`V0.lean` through `V12.lean`) or the existing
  `Proof/*.lean` files. In particular, do **not** edit
  `Proof/RadialSplit.lean` to change the existing
  `validKorenblum_of_innerCircleMean_dom`; if a variant form (`_ae` or
  with stripped hypotheses) is needed for the clean composition, expose
  it as a *new* theorem in `Proof/CleanConditional.lean` (or as a
  private helper there).

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the Fubini-Tonelli chain is genuinely blocked
  on a missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the contract → conditional plumbing bridge
  that any future c-push consumer must consume.

- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

- Attempt the genuine inner-circle-mean dominance content (the
  Korenblum/Hayman/Wang extremal-function chain). That is the *next*
  sprint's job, conditional on this sprint's clean conditional being
  in place.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`

- Blocked within scope (e.g.
  `MeasureTheory.Integrable.prod_left_ae` is not the exact Mathlib name
  in v4.28 and the closely-named variant `Integrable.integral_prod_left`
  produces only the `r`-marginal integrability, not the per-slice
  θ-integrability; or `setIntegral_prod` does not unify with the polar-
  pullback's `volume.prod volume` measure; or the `Ioc 0 c ⊆ Ioo 0 1`
  set-restriction loses the boundary `r = c` measurability needed by
  `IntegrableOn.mono_set` and the workaround through
  `MeasureTheory.IntegrableOn.restrict` introduces a circular
  measurability obligation; or the per-radius `hf_circle` is genuinely
  only derivable in `∀ᵐ` form and the existing
  `validKorenblum_of_innerCircleMean_dom` cannot be directly fed by an
  `∀ᵐ` form without a re-statement):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (`Integrable.integral_prod_left` vs `IntegrableOn.integral_prod_left`
  vs `setIntegral_prod` vs `Measure.prod_restrict` vs manual
  `lintegral`-Tonelli; whether the per-radius `hf_circle` was derived
  pointwise or `∀ᵐ`; whether the `Ioc 0 c → Ioo 0 1` set-restriction was
  done via `IntegrableOn.mono_set` or via boundary-handling on `r = c`).

  **Fallback form** (if the per-radius circle-integrability is only
  available in `∀ᵐ` form): the generator may instead expose the clean
  conditional with `∀ᵐ` hypotheses. The fallback theorem's statement
  becomes:

  ```lean
  theorem validKorenblum_of_inner_outer_dom_of_analyticOn_ae
      (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
      (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
      (hf_int : Integrable (fun z => ‖f z‖ ^ 2)
                  ((volume : Measure ℂ).restrict UnitDisk))
      (hg_int : Integrable (fun z => ‖g z‖ ^ 2)
                  ((volume : Measure ℂ).restrict UnitDisk))
      (h_inner : ∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r)
      (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
      bergmanNormSq f ≤ bergmanNormSq g
  ```

  with the proof routing through a private helper
  `validKorenblum_of_innerCircleMean_dom_ae` that is a pointwise-`∀ᵐ`
  variant of `validKorenblum_of_innerCircleMean_dom`, derived in
  `Proof/CleanConditional.lean` (not by edit to `Proof/RadialSplit.lean`).
  The fallback is acceptable if and only if the generator records in
  `Experience.md` why the stronger pointwise form was infeasible.

- Needs human trust expansion (e.g. a genuinely missing Mathlib Fubini-
  Tonelli lemma that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
