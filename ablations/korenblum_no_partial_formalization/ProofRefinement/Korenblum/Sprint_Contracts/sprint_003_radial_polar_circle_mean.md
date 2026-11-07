# Sprint 003: Radial polar form of the annulus split + `circleMean` abstraction

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V2.lean`
**Target file**: `Candidates/V3.lean`
**Direction**: section2-proof (Bergman scaffolding)

## Goal

Bridge the two existing scaffolding modules (`Proof.PolarBergman` and
`Proof.AnnulusBergman`) by deriving the **radial polar form** of the
annulus split. Introduce the canonical `circleMean` abstraction that every
subsequent subharmonic / monotone-mean argument must consume.

The three intended scaffolding lemmas are, schematically:

```lean
/-- Squared-norm circle mean of `f` at radius `r`. -/
noncomputable def circleMeanSq (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2

/-- Polar form of the inner-disk integral: integrate the squared circle
mean against `r dr` over `r ∈ (0, c]`. -/
theorem innerDisk_norm_sq_polar
    (f : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ r in Set.Ioc (0 : ℝ) c, circleMeanSq f r * r := ...

/-- Polar form of the outer-annulus integral: integrate the squared circle
mean against `r dr` over `r ∈ (c, 1)`. -/
theorem outerAnnulus_norm_sq_polar
    (f : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf_polar : ...) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∫ r in Set.Ioo c 1, circleMeanSq f r * r := ...
```

(Exact set choices — `Set.Ioc 0 c` vs `Set.Ioo 0 c` for the inner half,
the integrability hypothesis shape, whether to ship a single
`bergmanNormSq_radial_polar f = ∫_{r∈(0,1)} circleMeanSq f r · r` and
derive the two halves from it via `setIntegral_subset` plus a sphere
`{r = c}` measure-zero argument, or to prove each half directly — are at
the generator's discretion. What matters is that the three named pieces
(`circleMeanSq` definition, inner half, outer half) hold and together
span the full radial integral.)

This sprint is **scaffolding-only**: `c_value` does not increase. V3 ships
with the same `c = 3554/10000` and the same `hKorenblum_published_3554`
axiom as V2. The contribution is the new derived module: the radial
polar form is the unique missing bridge between
`bergmanNormSq_polar` (polar pull-back of the whole disk) and
`bergmanNormSq_split` (the inner/outer set-integral split). Without this
bridge no subsequent argument can attack the inner-disk piece via
circle-mean monotonicity, since circle-mean monotonicity lives in the
radial coordinate.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- The inner half of the Korenblum split is the genuinely hard half. Every
  honest route past `0.3554` factors through some monotone-mean argument
  on `r ↦ circleMeanSq f r` — most directly, the subharmonicity-driven
  fact that `r ↦ circleMeanSq f r` is non-decreasing in `r ∈ [0, 1)` for
  `f` analytic on the unit disk. That argument cannot even be *stated*
  without a fixed `circleMeanSq` definition and a polar form of the
  inner-disk integral. This sprint pins both.
- Mathlib has the right primitives. `bergmanNormSq_polar` (this
  workspace's own derived theorem) already gives
  `bergmanNormSq f = ∫_{r∈(0,1)} ∫_{θ∈(-π,π)} ‖f(symm(r,θ))‖² · r`. The
  inner / outer halves come from the same Fubini argument restricted to
  `Set.Ioc 0 c` and `Set.Ioo c 1` respectively, modulo a polar-region
  rewrite. The polar pull-back of `innerDisk c \ {0}` is exactly
  `Set.Ioc 0 c ×ˢ Set.Ioo (-π) π` (up to a θ-axis null set), and the
  pull-back of `outerAnnulus c` is `Set.Ioo c 1 ×ˢ Set.Ioo (-π) π`. So
  each half is a polar substitution + Fubini, in the same style as
  sprint 001 and well within the generator's scope.
- The proofs sit comfortably in the generator's declared scope:
  `Complex.integral_comp_polarCoord_symm`, `setIntegral_prod`,
  `setIntegral_eq_of_subset_of_forall_diff_eq_zero` (the same family of
  Mathlib API used in sprint 001), plus a single norm-on-polarCoord-symm
  case split for the inner-disk membership.
- This sprint also produces a falsifiable data point: if the inner-half
  rewrite cannot be closed against current Mathlib (e.g. because the
  natural sphere `‖z‖ = c` boundary handling forces an ae-disjointness
  branch the generator cannot dispatch), the `STATUS=BLOCKED` log will
  record exactly which Mathlib lemma was the bottleneck — and that
  bottleneck is the same one any future inner-disk Korenblum argument
  would have to face.
- Without these handles, every later sprint that compares circle means
  must re-derive the radial form inline. Pinning the three scaffolding
  pieces in `Proof/RadialBergman.lean` (admitted by
  `lemma.toml:[import_policy]` via the `ProofRefinement.Korenblum.Proof`
  prefix) makes them reusable across all future candidates without any
  trust changes.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/RadialBergman.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace, containing
  - the definition `circleMeanSq f r` (squared-norm circle integral over
    `θ ∈ Ioo (-π) π` of `‖f (polarCoord.symm (r, θ))‖²`, with no `1/(2π)`
    normalisation — the bare integral is the natural quantity for the
    radial form of `bergmanNormSq`),
  - a polar-region rewrite for the open outer annulus
    (`outerAnnulus c = polarCoord.symm '' (Ioo c 1 ×ˢ Ioo (-π) π)` up to
    the negative-real axis, or a direct subset+null argument analogous to
    the `polarTarget_inter_unitDisk_eq` style in `PolarBergman.lean`),
  - `outerAnnulus_norm_sq_polar` (or equivalently named) — the headline
    radial form of the outer integral,
  - `innerDisk_norm_sq_polar` (or equivalently named) — the headline
    radial form of the inner integral. The closure-vs-open boundary
    handling at `r = c` is a single sphere-null-set argument; the
    generator may choose `Set.Ioc 0 c` or `Set.Ioo 0 c` to avoid it.
  - The proofs should mirror `bergmanNormSq_polar`'s six-step shape:
    indicator rewrite, polar pull-back, domain shrinkage to the
    appropriate `r`-interval via
    `setIntegral_eq_of_subset_of_forall_diff_eq_zero`, indicator unfold,
    Fubini, and a final `circleMeanSq` re-folding step. The two halves
    are independent and do not need to call each other.
  - Optional but recommended: a single
    `bergmanNormSq_radial_polar` lemma stating
    `bergmanNormSq f = ∫ r in Ioo 0 1, circleMeanSq f r * r`, derived
    from `bergmanNormSq_polar` plus a simple `setIntegral_congr_fun` /
    `integral_congr_ae` to fold the inner integral into `circleMeanSq`.
    This is the natural top-level statement the inner / outer halves
    decompose.
- `ProofRefinement/Korenblum/Candidates/V3.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V3`, marked
  `-- @parent V2`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V2),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V2,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`, and the new
    `ProofRefinement.Korenblum.Proof.RadialBergman` so that the new
    module is part of V3's compile graph and is exercised by the build.
    No structural use of the new lemmas is required in V3 itself.
- No edits to `lemma.toml`. No edits to V0/V1/V2. No new axioms beyond
  the already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V3` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V3.lean` succeeds (the evaluator
   accepts V3 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V2; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/RadialBergman.lean`
   contains:
   - a `noncomputable def` (named `circleMeanSq` or as renamed by the
     generator) of type `(ℂ → ℂ) → ℝ → ℝ` whose definition is the
     `θ`-integral of `‖f (polarCoord.symm (r, θ))‖²` over `Ioo (-π) π`
     against `volume`;
   - one `theorem` (or `lemma`) rewriting `∫ z in outerAnnulus c, ‖f z‖²`
     as a single `r`-integral over an interval ending at `1` of
     `circleMeanSq f r * r` (with appropriate polar integrability
     side hypotheses on `f`);
   - one `theorem` (or `lemma`) rewriting `∫ z in innerDisk c, ‖f z‖²`
     as a single `r`-integral over an interval starting at `0` and
     ending at `c` (open or half-open, generator's choice) of
     `circleMeanSq f r * r` (with the same integrability shape).
   All three must be `def`/`theorem`/`lemma`, not `axiom`, with no
   `sorry`.
4. The new module `Proof.RadialBergman` must be **used**, even
   trivially, somewhere in V3's transitive compile graph (importing
   `Proof.RadialBergman` from V3 is sufficient — it forces the module
   to compile as part of V3's build).

## Out of scope

- Edit older candidates (`V0.lean`, `V1.lean`, `V2.lean`) or
  `Proof/PolarBergman.lean` / `Proof/AnnulusBergman.lean`.
- Change the final theorem statement.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the generator finds either radial half
  genuinely blocked on a missing Mathlib API, it must `STATUS=BLOCKED`
  with the precise obstruction, **not** axiomatize the lemma.
- Attempt to push `c_value` above `3554/10000`. That is a follow-up
  sprint, built on top of this one.
- Subharmonicity of `circleMeanSq f`, `r`-monotonicity of
  `circleMeanSq f`, Bergman monomial Parseval, Cauchy circle
  representation, or any other ingredient that closes the *inner* half
  of the Korenblum split. Those are deliberately deferred to follow-up
  sprints so this one is single-session-sized.
- A `1/(2π)` normalisation on `circleMeanSq`. The bare integral is the
  natural quantity for the radial form of `bergmanNormSq` (no `2π`
  bookkeeping), and any future normalised version can be hoisted later.
- Edit `lemma.toml` (no policy expansion needed; the `Proof.` prefix is
  already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `setIntegral_eq_of_subset_of_forall_diff_eq_zero`
  cannot be applied because the polar pull-back of `innerDisk c` requires
  a non-trivial null-set on the negative-real axis or `r = c` sphere
  handling; or `circleMeanSq` cannot be folded back from the Fubini
  inner integral because the generator hits an ae-vs-restricted-volume
  mismatch): `STATUS=BLOCKED` with a precise note in `Experience.md`
  recording which Mathlib lemma was the obstruction and which approaches
  were tried (closed `Ioc` vs open `Ioo` for the inner radial domain,
  whether the generator tried to derive the two halves directly versus
  via a top-level `bergmanNormSq_radial_polar` plus a split, integrability
  hypothesis shape).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
