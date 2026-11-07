# Proposal 001: replace `hKorenblum_published_3554` with `hWang_inner_radial_dominance_3554`

**Created**: 2026-05-07 by Planner
**Status**: pending
**Type**: new-axiom (replaces an existing seed axiom with a strictly smaller leaf)

## What's needed

- **File(s):**
  - `ProofRefinement/Korenblum/lemma.toml` — replace
    `hKorenblum_published_3554` in `[seed_axioms].allowed` with
    `hWang_inner_radial_dominance_3554`.
  - `ProofRefinement/Korenblum/Candidates/V15.lean` — new candidate, parent
    `V14`, that re-declares the seed axiom in the new (smaller) shape and
    proves `korenblum_constant_search` via
    `validKorenblumBound_of_inner_radial_dominance` (sprint 014, in
    `Proof/InnerRadialReduction.lean`).
- **Lean surface:** the new axiom

  ```lean
  axiom hWang_inner_radial_dominance_3554 :
    ∀ (f g : ℂ → ℂ),
      AnalyticOn ℂ f UnitDisk → AnalyticOn ℂ g UnitDisk →
      Integrable (fun z => ‖f z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      Integrable (fun z => ‖g z‖ ^ 2)
        ((volume : Measure ℂ).restrict UnitDisk) →
      (∀ z ∈ UnitDisk, (3554 / 10000 : ℝ) < ‖z‖ → ‖f z‖ ≤ ‖g z‖) →
      ∀ r ∈ Set.Ioc (0 : ℝ) (3554 / 10000),
        circleMeanSq f r ≤ circleMeanSq g r
  ```

  V15's `korenblum_constant_search` proof becomes a direct application of
  `validKorenblumBound_of_inner_radial_dominance` to
  `hWang_inner_radial_dominance_3554` (with `c = 3554/10000`,
  `0 < c` and `c < 1` discharged by `norm_num`).

- **Config changes:**
  - `lemma.toml:[seed_axioms].allowed`: remove
    `hKorenblum_published_3554`, add `hWang_inner_radial_dominance_3554`.

## Mathematical content

`hWang_inner_radial_dominance_3554` asserts only the **inner-half radial
dominance** sub-claim of Wang (2025) at `c = 0.3554`: that whenever `f, g`
are analytic, A²-integrable on the unit disk, and `‖f‖ ≤ ‖g‖` on the
outer annulus, the inner-half circle-means satisfy
`circleMeanSq f r ≤ circleMeanSq g r` for every `r ∈ Ioc 0 (3554/10000)`.

Wang's published proof derives this intermediate explicitly via the
extremal-function chain on the outer annulus pulled back to inner radii;
it is the natural intermediate conclusion before bridging to the full
Bergman A² inequality `bergmanNormSq f ≤ bergmanNormSq g`. The bridge
itself — the radial split, polar pullback, per-θ integrability, and the
outer-half pointwise comparison — is **already Lean-formalized** in this
workspace (sprints 001–013) and is consumed by sprint 014's
`validKorenblumBound_of_inner_radial_dominance`
(`Proof/InnerRadialReduction.lean`). Wang's intermediate is strictly
weaker than asserting `ValidKorenblumBound (3554/10000)` directly: the
function-level Korenblum implication follows from the intermediate via
the outer-half + radial-split scaffolding which Lean now bears.

## Win unlocked

- **Trust reduction at the same `c_value`.** The seed axiom shrinks from
  the full function-level Korenblum max principle at `c = 0.3554` to
  Wang's inner-half radial dominance intermediate. The numerical bound
  `c_value = 3554/10000` is preserved; only the trust leaf shrinks.
- **Scaffolding for c-push.** A future c-push attempt may find it easier
  to derive the inner-half radial dominance at higher `c` (extremal-
  function content) than to re-derive the entire Korenblum max principle
  at higher `c`. Pinning the contract-shape composition above sprint
  013's clean conditional means the c-push attempt only needs to
  axiomatize / prove the inner-half radial dominance at the new `c`.

## Risk / trust cost

The new axiom asserts a sub-claim of Wang (2025) — strictly less than
the existing seed axiom. No new mathematical content is being trusted
that was not already implicit in `hKorenblum_published_3554`; the
proposal is a strict trust contraction.

The proposal does **not** introduce any new Mathlib import or
import-policy expansion: `validKorenblumBound_of_inner_radial_dominance`
already compiles inside the workspace as part of V14's build graph.

## Follow-up sprint outline

Sprint 015 (post-approval):

1. Edit `lemma.toml`: replace `hKorenblum_published_3554` with
   `hWang_inner_radial_dominance_3554` in `[seed_axioms].allowed`.
2. Create `Candidates/V15.lean`, parent `V14`. Imports the same module
   set as V14. Defines `c_value := 3554 / 10000` (unchanged). Declares
   the new `axiom hWang_inner_radial_dominance_3554` (in the universal
   shape above). Proves `korenblum_constant_search :
   ValidKorenblumBound c_value` by
   `validKorenblumBound_of_inner_radial_dominance c_value_pos c_value_lt_one
   hWang_inner_radial_dominance_3554` (with the `change` to align
   `c_value` with `3554/10000`).
3. Run `lake build ProofRefinement.Korenblum.Candidates.V15` and
   `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V15.lean` to verify the
   evaluator accepts the new candidate. Score is unchanged from V14
   (`c_value = 3554/10000`); the win is the trust contraction, which
   is recorded in the run log.

## Status log

- 2026-05-07 created by Planner (alongside sprint 014).
