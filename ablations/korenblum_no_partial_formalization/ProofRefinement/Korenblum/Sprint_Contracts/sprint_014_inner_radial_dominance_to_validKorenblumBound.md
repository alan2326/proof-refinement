# Sprint 014: contract-shaped reduction `ValidKorenblumBound c` from universal inner-half radial dominance

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V13.lean`
**Target file**: `Candidates/V14.lean`
**Direction**: section2-proof / trust-reduction-prep (Lean-derive the
*final* composition layer above sprint 013's clean conditional: from the
universal inner-half radial dominance hypothesis quantified over `(f, g)`,
derive the contract-shaped `ValidKorenblumBound c`. This is the single
remaining Lean-side composition step before a future sprint can replace
the seed axiom `hKorenblum_published_3554` with a strictly smaller leaf
that asserts only the inner-half radial dominance — Wang's intermediate
conclusion — rather than the full function-level Korenblum implication.)

## Goal

Lift sprint 013's clean conditional Korenblum reduction
`validKorenblum_of_inner_outer_dom_of_analyticOn` (which is *per-pair*
`(f, g)`) to the **contract-shaped** universal form

```lean
theorem validKorenblumBound_of_inner_radial_dominance
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_inner_universal : ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      ∀ r ∈ Set.Ioc (0 : ℝ) c, circleMeanSq f r ≤ circleMeanSq g r) :
    ValidKorenblumBound c
```

In a new file `Proof/InnerRadialReduction.lean`. The proof is a direct
composition: unfold `ValidKorenblumBound`, fix `(f, g)` and the
five hypotheses, instantiate `h_inner_universal` to obtain the inner-half
radial dominance, then apply
`validKorenblum_of_inner_outer_dom_of_analyticOn` (sprint 013) with this
inner-half hypothesis and the contract's outer-half pointwise dominance.
The only non-trivial detail is the bridge between
`∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖` (contract shape) and
`∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖` (sprint-013-clean-conditional shape),
which is one `simp [outerAnnulus]` plus `mem_setOf` rewrite.

V14 ships with `c_value = 3554/10000` unchanged from V13 and the same seed
axiom `hKorenblum_published_3554`. The new theorem is included in V14's
build graph via import, and a follow-up sprint (post-proposal) will
replace the seed axiom with a strictly smaller leaf
`hWang_inner_radial_dominance_3554` and use this theorem to derive
`ValidKorenblumBound (3554/10000)` from that smaller leaf.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

- **It is the smallest sprint that materially advances goal #3 of
  AGENT_BRIEF** ("Replace the seed axiom `hKorenblum_published_3554` with
  a Lean theorem that derives the conclusion at `c = 0.3554` from a
  smaller set of axioms"). Goal #3 is explicitly listed and the only one
  achievable in a single bounded Generator session at this scaffolding
  height. Goal #1 ("prove a larger valid `c` directly") requires several
  pages of Korenblum/Hayman extremal-function content not in Mathlib.
  Goal #2 ("self-contained per-candidate partial formalization") is what
  sprints 001–013 have *already* been doing across the function-level
  contract; sprint 014 is the *capstone* of that scaffolding tower.

- **It is the explicit follow-up to sprint 013.** Sprint 013's
  `validKorenblum_of_inner_outer_dom_of_analyticOn` takes a *per-pair*
  `h_inner` and `h_outer` plus integrability hypotheses, and concludes
  `bergmanNormSq f ≤ bergmanNormSq g`. The contract `ValidKorenblumBound c`
  is the *universal* form, quantifying over all `(f, g)`. The lift from
  per-pair to universal is one `intro` plus an inner-hypothesis
  instantiation. Without this lift, every future trust-reduction sprint
  must re-derive the lift inline, which would defeat the point of having
  sprint 013's clean conditional pinned.

- **The trust-reduction pathway it enables.** Once
  `validKorenblumBound_of_inner_radial_dominance` is pinned in Lean, the
  axiom `hKorenblum_published_3554` (currently asserting the full
  function-level Korenblum implication at `c = 0.3554`) can be replaced
  with a strictly smaller axiom

  ```lean
  axiom hWang_inner_radial_dominance_3554 :
    ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, (3554 / 10000 : ℝ) < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      ∀ r ∈ Set.Ioc (0 : ℝ) (3554 / 10000), circleMeanSq f r ≤ circleMeanSq g r
  ```

  which asserts only Wang 2025's *intermediate* inner-radial-dominance
  conclusion — a sub-claim of the published proof, not the headline
  conclusion. Wang's paper proves this intermediate explicitly (it is the
  L²-mean comparison along the inner half, derived from the
  extremal-function chain), and it is strictly weaker than asserting
  `ValidKorenblumBound (3554/10000)` directly: the function-level
  Korenblum implication follows from this intermediate via the *outer-half*
  scaffolding (sprints 001–013) which is *already Lean-formalized* in this
  workspace. Trust is genuinely reduced because Lean now bears the
  outer-half + integrability + radial-split argument, leaving only the
  inner-half extremal content as an axiom. **The replacement is the next
  sprint's job**, not this one's; this sprint pins the Lean-side
  composition that the replacement requires.

- **The sprint is runnable immediately, without the proposal being
  approved.** The new theorem
  `validKorenblumBound_of_inner_radial_dominance` is a pure Lean
  derivation (no new axiom, no `lemma.toml` edit). V14's
  `korenblum_constant_search` continues to use the existing seed axiom
  `hKorenblum_published_3554`, exactly as V13's does — the new theorem
  is included in the V14 build graph via import to ensure it compiles,
  but is not used in `korenblum_constant_search`'s proof. The proposal
  for the smaller-leaf axiom is filed separately as
  `proposal_001_replace_seed_with_inner_radial_dominance.md` and does
  not gate the sprint.

- **Falsifiable in one Generator session.** The proof is one `intro`
  cascade plus a direct application of
  `validKorenblum_of_inner_outer_dom_of_analyticOn` (sprint 013) with
  the contract's hypotheses re-routed. The genuinely uncertain step is
  the bridge between
  `∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖` (contract shape) and
  `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖` (sprint-013 shape). The bridge
  is one `simp only [outerAnnulus, Set.mem_setOf_eq]` plus a destructure;
  the `outerAnnulus c = {z | c < ‖z‖ ∧ ‖z‖ < 1}` definition (in
  `Proof/AnnulusBergman.lean`) makes the two forms equivalent up to
  `‖z‖ < 1 ↔ z ∈ UnitDisk` (which is `Metric.mem_ball_zero_iff` plus
  norm = `dist · 0`).

- **Why not pursue Hardy's convexity (log-convexity of `circleMeanSq f r`
  in `log r`) as the next sprint.** Hardy's convexity is a useful tool
  downstream of sprint 011's Bergman Parseval identity, but it does not
  directly contribute to the inner-half radial dominance *bridge* (since
  the inner-radial dominance requires *cross-function* comparison
  `circleMeanSq f r ≤ circleMeanSq g r`, not a single-function
  log-convexity bound). Hardy's convexity is plausibly a follow-up
  sprint after this one, especially if the trust-reduction sprint
  (sprint 015) is gated on the proposal's approval.

- **Why not attempt a c-push directly.** Pushing `c` past `0.3554`
  requires a *new analytical chain* — specifically an extremal-function
  argument that proves a higher-radius inner-radial dominance. This
  chain is Korenblum 1991 / Hayman–Korenblum 1995 / Wang 2025 territory,
  several pages long, with no obvious Mathlib API. A direct c-push
  attempt at this scaffolding height would either need to import the
  full Wang machinery (which the no-PF arm explicitly excludes) or
  attempt the chain from scratch (which is several sprints of work,
  not one). The most rational next step is to lift the *existing*
  `c = 0.3554` proof to a smaller-leaf axiom form first — both because
  it is achievable in one sprint and because it pins the Lean-side
  composition that any future c-push will *also* need to consume.

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"bridging pointwise modulus inequalities to boundary integrals"*,
  *"Lebesgue-integral monotonicity on annulus regions"*, and the
  generator has already exercised
  `validKorenblum_of_inner_outer_dom_of_analyticOn` in sprint 013. The
  new theorem is one `intro`-and-apply layer above what is already in
  the build graph — strictly the smallest bounded-Generator-session
  sprint that materially advances the science.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/InnerRadialReduction.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.AnnulusBergman`,
    `Proof.RadialBergman`, `Proof.CleanConditional` (and **only** those
    workspace-side imports — the file is a thin composition layer above
    sprint 013's `validKorenblum_of_inner_outer_dom_of_analyticOn`, and
    pulling in further Bergman-Parseval / circle-mean modules would just
    bloat the build graph),

  - exposes `validKorenblumBound_of_inner_radial_dominance`. Statement:

    ```lean
    theorem validKorenblumBound_of_inner_radial_dominance
        {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
        (h_inner_universal : ∀ (f g : ℂ → ℂ),
          AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
          Integrable (fun z => ‖f z‖ ^ 2)
            ((volume : Measure ℂ).restrict UnitDisk) →
          Integrable (fun z => ‖g z‖ ^ 2)
            ((volume : Measure ℂ).restrict UnitDisk) →
          (∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
          ∀ r ∈ Set.Ioc (0 : ℝ) c,
            circleMeanSq f r ≤ circleMeanSq g r) :
        ValidKorenblumBound c
    ```

    *Implementation sketch*: unfold `ValidKorenblumBound`. Provide the
    `0 < c` and `c < 1` parts directly. For the universal Bergman
    inequality, `intro f g hf_an hg_an hf_int hg_int h_outer_contract`.
    Construct
    `h_inner : ∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`
    by applying `h_inner_universal f g hf_an hg_an hf_int hg_int
    h_outer_contract`. Construct
    `h_outer_clean : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖`
    by `intro z hz; simp only [outerAnnulus, Set.mem_setOf_eq] at hz;
       exact h_outer_contract z (mem_unitDisk_of_norm_lt_one hz.2) hz.1`
    (with a small bridge `mem_unitDisk_of_norm_lt_one : ‖z‖ < 1 →
    z ∈ UnitDisk`, which is one line via `Metric.mem_ball_zero_iff` plus
    `Complex.norm_eq_abs` / `dist_zero_right`). Finally apply
    `validKorenblum_of_inner_outer_dom_of_analyticOn f g c hc hc1
    hf_an hg_an hf_int hg_int h_inner h_outer_clean`.

  - if the bridge `‖z‖ < 1 → z ∈ UnitDisk` is more than one line in
    Lean, the generator may add a `private theorem
    mem_unitDisk_iff_norm_lt_one : z ∈ UnitDisk ↔ ‖z‖ < 1` as a helper
    in the same file. The `UnitDisk = Metric.ball (0 : ℂ) 1` definition
    gives this via `Metric.mem_ball_zero_iff` plus `dist_zero_right`
    plus `Complex.norm_eq_abs` (the `‖·‖` on `ℂ` is `Complex.abs`).

  - the theorem must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proof must be a *direct composition* —
    `validKorenblum_of_inner_outer_dom_of_analyticOn` must be called
    exactly once, and `h_inner_universal` instantiated exactly once
    per pair — not bypass via re-derivation of sprint 013's chain.

- `ProofRefinement/Korenblum/Candidates/V14.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V14`, marked
  `-- @parent V13`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V13),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V13,
  - imports the same module set as V13 plus
    `ProofRefinement.Korenblum.Proof.InnerRadialReduction`, so that the
    new module is part of V14's compile graph and is exercised by the
    build. No structural use of the new theorem in V14 itself is
    required.

- `ProofRefinement/Korenblum/Proposals/proposal_001_replace_seed_with_inner_radial_dominance.md`:
  **new file**, status `pending`. Documents the eventual trust-reduction
  axiom replacement (substitute `hKorenblum_published_3554` with
  `hWang_inner_radial_dominance_3554` in `lemma.toml:[seed_axioms].allowed`,
  and ship a V15 candidate that uses
  `validKorenblumBound_of_inner_radial_dominance` to derive
  `ValidKorenblumBound (3554/10000)` from the smaller leaf). The
  proposal does *not* gate this sprint; it documents the next step.

- No edits to `lemma.toml`. No edits to V0/.../V13 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V14` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V14.lean` succeeds (the evaluator
   accepts V14 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V13; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/InnerRadialReduction.lean`
   contains a `theorem` (or `lemma`) named
   `validKorenblumBound_of_inner_radial_dominance` (or equivalently
   named) whose conclusion is `ValidKorenblumBound c` and whose only
   non-routine hypothesis is the universal inner-half radial dominance
   statement quantified over `(f, g)` plus the analyticity, integrability,
   and outer-annulus pointwise dominance hypotheses (as in the contract
   shape of `ValidKorenblumBound`). The theorem must be `theorem` /
   `lemma`, never `axiom`, with no `sorry`. The proof must genuinely call
   `validKorenblum_of_inner_outer_dom_of_analyticOn` (sprint 013) — *not*
   bypass via direct re-derivation of sprint 013's chain.
4. The new module `Proof.InnerRadialReduction` must be **used**, even
   trivially, somewhere in V14's transitive compile graph (importing
   it from V14 is sufficient — it forces the module to compile as part
   of V14's build).
5. The file
   `ProofRefinement/Korenblum/Proposals/proposal_001_replace_seed_with_inner_radial_dominance.md`
   exists with status `pending`, contains a clear statement of the
   axiom replacement, and references this sprint's
   `validKorenblumBound_of_inner_radial_dominance` as the consumer
   that makes the replacement possible. The proposal **does not gate**
   the sprint — V14 is shippable independent of the proposal's
   approval status.

## Out of scope

- Edit older candidates (`V0.lean` through `V13.lean`) or the existing
  `Proof/*.lean` files.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms — including the eventual
  `hWang_inner_radial_dominance_3554`, which is gated on the proposal's
  approval and is the *next* sprint's job, not this one's). If the
  composition path is genuinely blocked on a missing Mathlib API or on
  a hypothesis-shape mismatch, the generator must `STATUS=BLOCKED` with
  the precise obstruction, **not** axiomatize.
- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the contract-shape composition above
  sprint 013's clean conditional that any future trust-reduction or
  c-push consumer must consume.
- Edit `lemma.toml` (no policy expansion in this sprint; the policy
  edit would be part of the post-proposal V15 sprint).
- Attempt any inner-half radial dominance derivation. This sprint is
  *parametric* over the inner-half hypothesis — it does not attempt to
  prove or instantiate it.

## Time budget

≤ 45 minutes runtime. (This is a thin composition sprint, materially
shorter than sprints 011–013.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`

- Blocked within scope (e.g. the contract-shape outer-annulus hypothesis
  bridge `∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖` to
  `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖` requires a Mathlib lemma the
  generator cannot find — most likely a `mem_unitDisk_iff_norm_lt_one`
  variant via `Metric.mem_ball_zero_iff` plus `dist_zero_right`; or
  the `‖z‖ < 1` projection from `outerAnnulus c` membership requires a
  pattern match the generator cannot discharge cleanly through `simp
  [outerAnnulus]`):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (`Metric.mem_ball_zero_iff` vs `Complex.mem_ball` vs manual
  `dist_zero_right` + `Complex.norm_eq_abs` vs `simp [UnitDisk,
  Metric.ball]`).

  **Fallback form** (if the contract-shape outer-annulus bridge is
  awkward in Lean): the generator may instead expose the theorem with
  the *clean conditional shape* directly, accepting
  `h_outer_clean : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖` as a separate
  hypothesis instead of deriving it inline. The fallback theorem's
  statement becomes:

  ```lean
  theorem validKorenblumBound_of_inner_radial_dominance_outerAnnulus
      {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
      (h_inner_universal : ∀ (f g : ℂ → ℂ),
        AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
        Integrable (fun z => ‖f z‖ ^ 2)
          ((volume : Measure ℂ).restrict UnitDisk) →
        Integrable (fun z => ‖g z‖ ^ 2)
          ((volume : Measure ℂ).restrict UnitDisk) →
        (∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) →
        ∀ r ∈ Set.Ioc (0 : ℝ) c,
          circleMeanSq f r ≤ circleMeanSq g r) :
      ValidKorenblumBound c
  ```

  In this fallback form the bridge `UnitDisk → outerAnnulus c` is
  pushed *into* the inner-radial hypothesis statement, so the theorem
  consumer (the future trust-reduction axiom
  `hWang_inner_radial_dominance_3554`) just needs to be stated in the
  `outerAnnulus`-flavored form. The fallback is acceptable if and only
  if the generator records in `Experience.md` why the contract-shape
  form was infeasible, and updates the proposal
  `proposal_001_replace_seed_with_inner_radial_dominance.md` to use
  the matching `outerAnnulus`-flavored axiom statement.

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
