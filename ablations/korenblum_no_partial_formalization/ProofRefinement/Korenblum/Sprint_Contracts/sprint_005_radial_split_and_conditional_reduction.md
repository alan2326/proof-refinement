# Sprint 005: radial split of `bergmanNormSq` + conditional Korenblum reduction

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V4.lean`
**Target file**: `Candidates/V5.lean`
**Direction**: section2-proof (Bergman scaffolding — radial reduction of the Korenblum target to a single radial inequality)

## Goal

Reduce the entire function-level Korenblum maximum principle to a **single
radial inequality on the inner half** by formalizing two lemmas:

1. `radialIntegral_split` — the radial-form splitting

   ```
   ∫ r in Ioo (0:ℝ) 1, circleMeanSq f r * r
     = (∫ r in Ioc 0 c, circleMeanSq f r * r)
       + (∫ r in Ioo c 1, circleMeanSq f r * r)
   ```

   for any `c ∈ Ioo 0 1` (with appropriate radial integrability hypotheses).

2. `validKorenblum_of_innerCircleMean_dom` — a conditional reduction: given
   the inner-half radial dominance hypothesis

   ```
   ∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r
   ```

   plus the (already-derivable) outer-half radial dominance from
   `circleMeanSq_le_of_outerAnnulus_dom`, the conclusion
   `bergmanNormSq f ≤ bergmanNormSq g` follows by composing the two halves
   along `radialIntegral_split`. Stated against the same integrability
   shape as `bergmanNormSq_radial_polar` / `outerAnnulus_norm_sq_polar` /
   `innerDisk_norm_sq_polar`, this lemma is the canonical *conditional*
   form of the Korenblum implication: it isolates the inner-half radial
   inequality as the **only** remaining mathematical obstruction.

Both lemmas live in a new file `Proof/RadialSplit.lean`. V5 is
**scaffolding-only**: `c_value = 3554/10000` is unchanged and the only
seed axiom is still `hKorenblum_published_3554`. The contribution is the
new derived module, which formalizes the reduction "Korenblum at `c` ⇔
inner-half radial dominance for `r ∈ Ioc 0 c`" as a Lean theorem.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- After sprints 001–004 the Bergman scaffolding contains: polar
  pull-back of the whole disk (`bergmanNormSq_polar`,
  `bergmanNormSq_radial_polar`), the inner / outer disjoint-union split
  on `Set ℂ` (`bergmanNormSq_split`), the radial polar form of each half
  (`outerAnnulus_norm_sq_polar`, `innerDisk_norm_sq_polar`), and the
  radial-form outer-annulus comparison
  (`circleMeanSq_le_of_outerAnnulus_dom`,
  `outerAnnulus_norm_sq_mono_via_radial`). What is **missing** is the one
  bookkeeping lemma that lets these compose: the radial integral on
  `Ioo 0 1` is the sum of the radial integrals on `Ioc 0 c` and `Ioo c 1`.
  Without `radialIntegral_split`, the inner and outer halves cannot be
  recombined in the radial world; without
  `validKorenblum_of_innerCircleMean_dom`, every future inner-half attack
  has to redo the recombination from scratch.
- The conditional reduction lemma is the *natural* statement of "what
  remains after the outer-half is closed". Once it is in place, every
  follow-up sprint targeting `c > 0.3554` has a single clean target:
  prove `∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r` for some
  `c > 0.3554` from analyticity plus the outer-annulus dominance
  hypothesis. This focuses all future analytical work onto a single
  radial inequality and removes the 2D set-integral bookkeeping from
  every subsequent attempt.
- Both lemmas sit comfortably in the generator's declared scope:
  `setIntegral_union` on the disjoint decomposition `Ioo (0:ℝ) 1
  = Ioc 0 c ∪ Ioo c 1` (using `c < 1` and `0 < c`); `IntegrableOn.union`
  / `integrableOn_union` to thread integrability; `add_le_add` to
  combine the two halves; and the already-proven
  `bergmanNormSq_radial_polar`, `outerAnnulus_norm_sq_polar`,
  `innerDisk_norm_sq_polar`, `circleMeanSq_le_of_outerAnnulus_dom` for
  the conditional reduction. No new Mathlib API surface is touched.
- Sanity check on the disjoint decomposition: `Ioo (0:ℝ) 1 = Ioc 0 c ∪
  Ioo c 1` whenever `0 < c < 1`. The endpoints are handled by `Ioc 0 c`
  capturing `r ∈ (0, c]` (closed at `c`) and `Ioo c 1` capturing
  `r ∈ (c, 1)` (open at `c`); the singleton `{c}` lies in `Ioc 0 c`,
  not in `Ioo c 1`, so the two are genuinely disjoint and union to
  `Ioo 0 1`. This is the same boundary convention used by
  `outerAnnulus_norm_sq_polar` / `innerDisk_norm_sq_polar`, so the
  composition is mechanical.
- Falsifiable bottleneck: if `setIntegral_union` cannot be applied
  cleanly to the radial integrand on the disjoint decomposition (e.g.
  because the integrability shape on `Ioc 0 c ∪ Ioo c 1` does not match
  the shape on `Ioo 0 1`, or because `IntegrableOn.union` requires a
  measurability-of-set hypothesis the generator cannot discharge), the
  `STATUS=BLOCKED` log will record exactly which Mathlib API is the
  obstruction. This is the same kind of plumbing obstruction that any
  inner-half attack would face, so the failure is informative.
- Why this sprint and not a numerical-budget push at higher `c`: the
  workspace currently has zero radial-form composition lemmas. Without
  one, no honest attack on the inner half can compile against the
  outer-half scaffolding without rebuilding the composition from
  scratch. Filing a "push `c` from 0.3554 to 0.36 via direct Mathlib
  argument" sprint at this stage would be premature — the radial
  reduction is the prerequisite, not the inverse.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/RadialSplit.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,
  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.AnnulusBergman`,
    `Proof.PolarBergman`, `Proof.RadialBergman`, `Proof.CircleMeanCompare`
    (and **only** those workspace-side imports),
  - exposes lemma (1): roughly

    ```lean
    theorem radialIntegral_split
        (f : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
        (hf_inner_int :
            IntegrableOn (fun r => circleMeanSq f r * r)
                         (Set.Ioc 0 c) volume)
        (hf_outer_int :
            IntegrableOn (fun r => circleMeanSq f r * r)
                         (Set.Ioo c 1) volume) :
        (∫ r in Set.Ioo (0 : ℝ) 1, circleMeanSq f r * r)
          = (∫ r in Set.Ioc 0 c, circleMeanSq f r * r)
            + (∫ r in Set.Ioo c 1, circleMeanSq f r * r)
    ```

    Proof outline: rewrite `Set.Ioo (0:ℝ) 1 = Set.Ioc 0 c ∪ Set.Ioo c 1`
    (a one-line set equality from `0 < c < 1`); apply `setIntegral_union`
    on the disjoint decomposition (disjointness: `r ∈ Ioc 0 c` forces
    `r ≤ c`, `r ∈ Ioo c 1` forces `c < r`; measurability of `Ioo c 1`
    via `measurableSet_Ioo`); thread integrability through.
  - exposes lemma (2): roughly

    ```lean
    theorem validKorenblum_of_innerCircleMean_dom
        (f g : ℂ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
        -- polar integrability for `f`, `g` on the full polar box
        (hf_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        (hg_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        -- radial-form integrability for both halves of both functions
        (hf_inner_int :
            IntegrableOn (fun r => circleMeanSq f r * r)
                         (Set.Ioc 0 c) volume)
        (hf_outer_int :
            IntegrableOn (fun r => circleMeanSq f r * r)
                         (Set.Ioo c 1) volume)
        (hg_inner_int :
            IntegrableOn (fun r => circleMeanSq g r * r)
                         (Set.Ioc 0 c) volume)
        (hg_outer_int :
            IntegrableOn (fun r => circleMeanSq g r * r)
                         (Set.Ioo c 1) volume)
        -- inner-half radial dominance hypothesis (the genuine remaining
        -- mathematical content; not closed in this sprint)
        (h_inner : ∀ r ∈ Set.Ioc 0 c,
            circleMeanSq f r ≤ circleMeanSq g r)
        -- outer-half pointwise dominance hypothesis (this sprint closes
        -- the outer half via `circleMeanSq_le_of_outerAnnulus_dom`)
        (hf_circle : ∀ r ∈ Set.Ioo c 1,
            IntegrableOn
              (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
              (Set.Ioo (-Real.pi) Real.pi) volume)
        (hg_circle : ∀ r ∈ Set.Ioo c 1,
            IntegrableOn
              (fun θ => ‖g (Complex.polarCoord.symm (r, θ))‖ ^ 2)
              (Set.Ioo (-Real.pi) Real.pi) volume)
        (h_outer : ∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖) :
        bergmanNormSq f ≤ bergmanNormSq g
    ```

    Proof outline:
    - rewrite both sides via `bergmanNormSq_radial_polar` (using
      `hf_polar`, `hg_polar`),
    - apply `radialIntegral_split` to both sides at `c`,
    - the goal becomes
      `(∫_{Ioc 0 c} cM f * r) + (∫_{Ioo c 1} cM f * r)
         ≤ (∫_{Ioc 0 c} cM g * r) + (∫_{Ioo c 1} cM g * r)`;
      apply `add_le_add`,
    - inner half: `setIntegral_mono_on` on `Ioc 0 c` against
      `circleMeanSq f r * r ≤ circleMeanSq g r * r`, where the pointwise
      inequality follows from `h_inner` plus `mul_le_mul_of_nonneg_right`
      with `0 ≤ r` (from `r ∈ Ioc 0 c` ⇒ `0 < r`),
    - outer half: identical to the proof of
      `outerAnnulus_norm_sq_mono_via_radial` (modulo the
      `outerAnnulus_norm_sq_polar` rewrite which is no longer needed —
      we are already in radial form), routed through
      `circleMeanSq_le_of_outerAnnulus_dom` plus `setIntegral_mono_on`
      on `Ioo c 1`.
  - The signature shapes above are guidelines. The generator is free to
    consolidate or weaken hypotheses (e.g. derive `hf_circle` /
    `hg_circle` from `hf_polar` / `hg_polar` via Fubini if cleaner, or
    derive `hf_inner_int` / `hf_outer_int` from a single radial
    `IntegrableOn` hypothesis on `Ioo 0 1` plus monotonicity), as long
    as the statement of the **conclusion** of each lemma is exactly as
    above and the lemmas are **theorems** (no `axiom`, no `sorry`).
- `ProofRefinement/Korenblum/Candidates/V5.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V5`, marked
  `-- @parent V4`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V4),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V4,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`, and the new
    `ProofRefinement.Korenblum.Proof.RadialSplit` so that the new
    module is part of V5's compile graph and is exercised by the build.
    No structural use of the new lemmas is required in V5 itself.
- No edits to `lemma.toml`. No edits to V0/V1/V2/V3/V4 or to the
  existing `Proof/*.lean` files. No new axioms beyond the
  already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V5` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V5.lean` succeeds (the evaluator
   accepts V5 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V4; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/RadialSplit.lean` contains:
   - one `theorem` (or `lemma`) named `radialIntegral_split` (or
     equivalently named) whose conclusion is the radial integral split

     ```
     ∫ r in Ioo (0:ℝ) 1, circleMeanSq f r * r
       = (∫ r in Ioc 0 c, circleMeanSq f r * r)
         + (∫ r in Ioo c 1, circleMeanSq f r * r)
     ```

     for any `c` with `0 < c < 1` (and integrability hypotheses on the
     two halves);
   - one `theorem` (or `lemma`) named
     `validKorenblum_of_innerCircleMean_dom` (or equivalently named)
     whose conclusion is `bergmanNormSq f ≤ bergmanNormSq g`, taking as
     hypotheses:
       1. analyticity / integrability hypotheses sufficient to invoke
          `bergmanNormSq_radial_polar`,
       2. an inner-half radial dominance hypothesis of the form
          `∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`,
       3. an outer-half pointwise dominance hypothesis of the form
          `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖`.
     The proof must call `radialIntegral_split` (so that the radial
     splitting is genuinely *used*, not bypassed); it must close the
     outer half via `circleMeanSq_le_of_outerAnnulus_dom` (or directly
     via `outerAnnulus_norm_sq_mono_via_radial`); and it must close the
     inner half via `setIntegral_mono_on` (or equivalent) on the inner
     radial integral against the inner-half radial dominance hypothesis.
   Both must be `theorem` / `lemma`, never `axiom`, with no `sorry`.
4. The new module `Proof.RadialSplit` must be **used**, even
   trivially, somewhere in V5's transitive compile graph (importing
   `Proof.RadialSplit` from V5 is sufficient — it forces the module
   to compile as part of V5's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V4.lean`) or the existing
  `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`, `Proof/CircleMeanCompare.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If the generator finds either lemma genuinely
  blocked on a missing Mathlib API, it must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize the lemma.
- **Attempt the inner half** — i.e., do not try to prove
  `∀ r ∈ Set.Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r` in this
  sprint. The whole point of `validKorenblum_of_innerCircleMean_dom` is
  to *take that as a hypothesis*. Discharging it requires an
  analyticity-driven argument (Hardy-style monotonicity, Bergman
  monomial Parseval, Cauchy / Poisson kernel bounds, or an entirely
  different chain) and is genuinely hard — that is the next sprint's
  job, not this one's. Any partial attempt to discharge it inline
  inflates the sprint past one Generator session.
- Bridge `circleMeanSq` to Mathlib's `Real.circleAverage` (which uses
  the `circleMap` parametrisation `r * Complex.exp (θ * I)` rather
  than `polarCoord.symm`). That bridge is its own follow-up sprint and
  is not required for the radial split or the conditional reduction.
- Push `c_value` above `3554/10000`. That is a follow-up sprint, built
  on top of this one's conditional reduction.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `setIntegral_union` cannot be applied to
  the radial integrand on `Ioo 0 1 = Ioc 0 c ∪ Ioo c 1` because of an
  integrability-hypothesis shape mismatch that cannot be repaired by
  re-stating the hypotheses, or the disjoint-union set equality
  `Ioo 0 1 = Ioc 0 c ∪ Ioo c 1` cannot be discharged by `Set.ext`+
  `simp [Set.mem_Ioo, Set.mem_Ioc, Set.mem_union]` plus order
  arithmetic): `STATUS=BLOCKED` with a precise note in `Experience.md`
  recording which Mathlib lemma was the obstruction and which approaches
  were tried (e.g. whether the generator tried `setIntegral_union`
  versus `MeasureTheory.integral_union_ae` versus an `indicator`-based
  decomposition; whether the disjoint-union set equality was attacked
  via `Set.ext` versus `Set.Ioo_eq_union_Ioc_Ioo` lookup; whether
  integrability was consolidated to a single `Ioo 0 1` hypothesis or
  left split).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
