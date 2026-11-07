# Sprint 010: radial monotonicity of `circleMeanSq` for analytic functions

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V9.lean`
**Target file**: `Candidates/V10.lean`
**Direction**: section2-proof (Bergman scaffolding — analytic-to-`tsum` Parseval consumer
exposing radial monotonicity, the canonical follow-up of sprint 009)

## Goal

Lift sprint 009's analytic-to-`tsum` Parseval identity

```
circleMeanSq f r = ∑' k, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
```

to a **radial-monotonicity** statement: for any analytic `f` on the open unit
disk, the map `r ↦ circleMeanSq f r` is non-decreasing on `[0, 1)`.

In a new file `Proof/CircleMeanRadial.lean`, expose:

1. `circleMeanSq_radial_mono` — *the headline identity*. For any
   `f : ℂ → ℂ` with `AnalyticOn ℂ f UnitDisk` and any `r₁, r₂ : ℝ` with
   `0 ≤ r₁ ≤ r₂ < 1`,

   ```lean
   circleMeanSq f r₁ ≤ circleMeanSq f r₂
   ```

   The proof passes through sprint 009's
   `circleMeanSq_eq_tsum_of_analyticOn_unitDisk`: extract a coefficient
   sequence `a` valid simultaneously at `r₁` and at `r₂` (use the same `a`
   for both — sprint 009's existential is `cauchyPowerSeries f 0 R` for any
   suitable `R`, so the witness is *independent* of the chosen radius), then
   compare the two `tsum`s termwise.

2. `circleMeanSq_termwise_mono` — *the coefficient-level consumer*. For
   `f, g : ℂ → ℂ` analytic on `UnitDisk` and `0 ≤ r < 1`, if there exist
   coefficient sequences `a, b : ℕ → ℂ` and a common-witness Parseval
   identity (i.e. `circleMeanSq f r = ∑' k, (2π · r^(2k)) ‖a k‖²` and
   similarly for `g, b`) such that `‖a k‖ ≤ ‖b k‖` for every `k`, then

   ```lean
   circleMeanSq f r ≤ circleMeanSq g r
   ```

   This is a strict `tsum` lemma over non-negatives — Mathlib
   `tsum_le_tsum` on the per-term inequality
   `(2π · r^(2k)) ‖a k‖² ≤ (2π · r^(2k)) ‖b k‖²`, with summability on
   both sides supplied by sprint 009's Parseval identity (each side is a
   real number, hence the implicit `Summable`).

3. `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
   *the canonicalised disk-shape consumer*. Strengthen sprint 009's existential
   `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` to a `theorem` with a
   **canonical witness**: for `f : ℂ → ℂ` analytic on `UnitDisk` and any
   `0 ≤ r < 1`,

   ```lean
   circleMeanSq f r
     = ∑' k, (2 * Real.pi * r ^ (2 * k))
              * ‖(cauchyPowerSeries f 0 1).coeff k‖ ^ 2
   ```

   (Or, if the cleaner form is to expose it as `(cauchyPowerSeries f 0 R)` for
   any suitable `R`, the generator may pick whichever variant compiles
   cleanly — but the witness *must* be a Mathlib-named, deterministic
   function of `f`, not a `Classical.choose`-extracted existential.) This is
   the indispensable building block for (1): without a *canonical, radius-
   independent* coefficient sequence, the radial-monotonicity proof in (1)
   would have to compare two unrelated existentials.

V10 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V9 and
the only seed axiom is still `hKorenblum_published_3554`. The contribution
is the new derived module that finally pins, in Lean, the **monotonicity
half** of the Bergman-A² Parseval theory: every analytic `f` has a
non-decreasing radial circle-mean, witnessed at the coefficient level by
the canonical Cauchy power series. Without this lemma the conditional
reduction `validKorenblum_of_innerCircleMean_dom` (sprint 005) cannot be
attacked at the coefficient level, because there is no Lean-side guarantee
that the `tsum` form supplied by sprint 009 is the *same* `tsum` form one
would obtain at a neighbouring radius.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

- **It is the canonical follow-up of sprint 009.** Sprint 009 shipped the
  analytic-to-`tsum` bridge `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` as
  an *existential* statement (`∃ a, …`). That form is unusable for any
  inequality-shaped attack: comparing `circleMeanSq f r` at two different
  radii through the existential would require either (a) showing the two
  existentially-witnessed sequences agree, or (b) producing a deterministic
  witness. Sprint 010 (3) supplies (b) via Mathlib's `cauchyPowerSeries`,
  which sprint 009's proof of (2) already uses internally — the existential
  was a stylistic choice, not a mathematical necessity. With (3) in place,
  (1) and (2) drop out as one-line `tsum` arithmetic.
- **It is a strict prerequisite for any inner-half c-push, not a parallel
  direction.** The conditional reduction
  `validKorenblum_of_innerCircleMean_dom` (sprint 005) requires
  `∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`. In coefficient form
  this is `∀ r ∈ Ioc 0 c, ∑' k, (2π · r^(2k)) ‖a k‖² ≤ ∑' k, …`. The
  termwise-comparison lemma (2) reduces this to `∀ k, ‖a k‖ ≤ ‖b k‖`, which
  is a *coefficient-level* statement on `f, g`. The
  radial-monotonicity lemma (1) is the orthogonal direction: it lets the
  generator transport circle-mean information across radii (e.g. from
  `r = c` boundary to `r ≤ c` interior). Both are needed.
- **The proof outline is bounded.** Each step is one Mathlib rewrite:
  - **(3)** From `AnalyticOn ℂ f UnitDisk` plus `0 ≤ r < 1`, extract
    `HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R` for some
    `R > r`, exactly as sprint 009 did internally. The body of sprint 009's
    `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` literally constructs this
    witness; the only change is exposing the witness as the headline
    statement instead of an existential. The **subtle step** is that the
    coefficients `cauchyPowerSeries f 0 R` depend on `R` syntactically;
    however, the Mathlib lemma `cauchyPowerSeries_def` (or
    `cauchyPowerSeries_apply` plus iteratedFDeriv-locality) shows
    `cauchyPowerSeries f 0 R = cauchyPowerSeries f 0 R'` whenever the
    derivatives at `0` are well-defined, which follows from analyticity at
    `0`. The generator may instead phrase (3) directly with a generic
    `R : ℝ≥0` such that `(R : ℝ) ∈ (r, 1)`, and quantify over `R` in the
    statement — the `cauchyPowerSeries` coefficient is then defined via
    that `R` and the equality holds for any such `R`. The cleanest form is
    at the generator's discretion as long as the witness is canonical
    (not via `Classical.choose`).
  - **(1)** Apply (3) at both `r₁` and `r₂` with a common `R` (e.g.
    `R := (r₂ + 1) / 2`, which satisfies `r₁ ≤ r₂ < R < 1`). The two
    `tsum`s share the same coefficient sequence
    `(cauchyPowerSeries f 0 R).coeff`. Apply termwise comparison
    `(2π · r₁^(2k)) ‖a k‖² ≤ (2π · r₂^(2k)) ‖a k‖²` (per-term, via
    `pow_le_pow_left` / `mul_le_mul_of_nonneg_right`), then `tsum_le_tsum`
    on the non-negative summable sequences.
  - **(2)** Direct `tsum_le_tsum` of `(2π · r^(2k)) ‖a k‖² ≤ (2π · r^(2k))
    ‖b k‖²` from `‖a k‖ ≤ ‖b k‖`, with summability on both sides
    inherited from the Parseval `HasSum` / `Summable` data.
- **Falsifiable in one Generator session.** Each step above is one Mathlib
  lemma. The genuinely uncertain step is the canonicalisation of (3): does
  Mathlib expose `cauchyPowerSeries_eq_of_analyticOn` (or equivalent
  radius-independence)? If not, the generator may instead `let
  p := cauchyPowerSeries f 0 R` *inside* the proofs of (1) and (2) without
  exposing it in the theorem statement, and quantify over the existential
  pair `(p, R)` instead of fixing the witness. That is a strictly weaker
  but still-useful form, and the planner accepts it as a fallback (see
  *Stop conditions*).
- **The `r₁ = 0` corner.** At `r₁ = 0`, `circleMeanSq f 0 = 2π · ‖f 0‖²`
  by `circleMeanSq_const` (sprint 006) applied to the constant function
  `f 0`, *or* by the `tsum` collapse where `r^(2k) = 0` for `k ≥ 1`.
  This is a `by_cases r₁ = 0` corner that costs one short branch using
  `pow_zero` plus `tsum_eq_single 0`. Not a blocker.
- **Why not also attempt the inner-half dominance.** As sprint 009's *Out
  of scope* paragraph explicitly says, the inner-half radial dominance
  is the actual mathematical content of Korenblum and requires a
  weighted-extremal-disk argument (Wang's 30 pages). Bundling it with
  this sprint would tie pass criteria to an as-yet-unwritten coefficient-
  level inequality. Pinning radial monotonicity + termwise comparison +
  canonical-witness Parseval as scaffolding-only isolates the limit-
  passing content cleanly and keeps the sprint acceptance criterion
  falsifiable in one Generator session.
- **Why not bundle into a numerical-budget push.** The workspace
  currently has zero radial transport lemmas for `circleMeanSq`. Without
  them, no honest attack on the inner half can compose against the
  Parseval identity from sprint 009. A "push c from 0.3554 to 0.36 via
  direct Mathlib argument" sprint at this stage would be premature —
  radial monotonicity is the prerequisite, not the inverse.
- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Parseval
  / boundary L² expansions on analytic functions"*, *"termwise summability
  and `tsum`-level rearrangements"*, and *"subharmonicity / mean-value
  arguments for `|f|²`"* as in scope. Radial monotonicity is the
  Bergman-side avatar of sub-mean-value / `tsum`-monotonicity, applied at
  radius `r < 1`.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleMeanRadial.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.RadialBergman`,
    `Proof.CircleExpBridge`, `Proof.CircleInnerProduct`,
    `Proof.CirclePolynomialParseval`, `Proof.AnalyticParseval` (and
    **only** those workspace-side imports),

  - exposes (3) `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`.
    Statement (or equivalent — the exact form of the canonical witness is
    at the generator's discretion as long as the witness is a deterministic
    Mathlib function of `f` and the conclusion is unchanged):

    ```lean
    theorem circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
        {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < (R : ℝ)) :
        circleMeanSq f r
          = ∑' k : ℕ,
              (2 * Real.pi * r ^ (2 * k))
                * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
    ```

    Proof outline: identical to the body of sprint 009's
    `circleMeanSq_eq_tsum_of_analyticOn_unitDisk`, but fixing the
    intermediate `R : ℝ≥0` as an explicit hypothesis instead of a
    `set R := …` inside the proof. The hypothesis chain
    `closedBall 0 R ⊆ ball 0 1 = UnitDisk → DifferentiableOn ℂ f
    (closedBall 0 R) → HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0
    R → circleMeanSq_hasFPowerSeriesOnBall …` runs unchanged. The
    generator may copy-and-adapt the body of sprint 009's existential
    proof, replacing the `set R := (r + 1) / 2` step with the explicit
    `R` hypothesis.

  - exposes (2) `circleMeanSq_termwise_mono`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_termwise_mono
        {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        (hg : AnalyticOn ℂ g UnitDisk)
        {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
        {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < (R : ℝ))
        (h_coeff : ∀ k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖
              ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
        circleMeanSq f r ≤ circleMeanSq g r
    ```

    Proof outline: rewrite both sides via (3); apply `tsum_le_tsum` on the
    per-term inequality `(2π · r^(2k)) ‖a k‖² ≤ (2π · r^(2k)) ‖b k‖²`,
    where `a := (cauchyPowerSeries f 0 R).coeff` and similarly `b`.
    Per-term summability and the term-level inequality are direct from
    `mul_le_mul_of_nonneg_left` (squaring is monotone on nonneg, then
    multiply by the nonneg constant `2π · r^(2k)`).

  - exposes (1) `circleMeanSq_radial_mono`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_radial_mono
        {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        {r₁ r₂ : ℝ} (hr₁_nonneg : 0 ≤ r₁) (hr_le : r₁ ≤ r₂) (hr₂_lt : r₂ < 1) :
        circleMeanSq f r₁ ≤ circleMeanSq f r₂
    ```

    Proof outline: pick `R : ℝ≥0` with `r₂ < R < 1` (e.g. `R := ⟨(r₂ + 1)/2,
    by linarith⟩`). Apply (3) at both `r₁` and `r₂` with this common `R`.
    Both sides are then `∑' k, (2π · r^(2k)) ‖(cauchyPowerSeries f 0 R).coeff
    k‖²` for `r ∈ {r₁, r₂}`. Apply `tsum_le_tsum` on the per-term
    inequality `(2π · r₁^(2k)) c ≤ (2π · r₂^(2k)) c` where `c := ‖… ‖² ≥ 0`,
    using `pow_le_pow_left` (the `r₁ ≤ r₂` hypothesis on nonneg) plus
    `mul_le_mul_of_nonneg_right`.

  - All three items must be `theorem`/`lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as long
    as the conclusion is unchanged and the witness in (3) is a deterministic
    Mathlib function of `f` (not a `Classical.choose` of an existential).

- `ProofRefinement/Korenblum/Candidates/V10.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V10`, marked
  `-- @parent V9`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V9),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V9,
  - imports `ProofRefinement.Korenblum.Proof.CandidateContract`,
    `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`,
    `ProofRefinement.Korenblum.Proof.CircleExpBridge`,
    `ProofRefinement.Korenblum.Proof.CircleInnerProduct`,
    `ProofRefinement.Korenblum.Proof.CirclePolynomialParseval`,
    `ProofRefinement.Korenblum.Proof.AnalyticParseval`,
    and the new
    `ProofRefinement.Korenblum.Proof.CircleMeanRadial` so that the new
    module is part of V10's compile graph and is exercised by the build.
    No structural use of the new lemmas in V10 itself is required.
- No edits to `lemma.toml`. No edits to V0/.../V9 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V10` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V10.lean` succeeds (the evaluator
   accepts V10 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V9; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/CircleMeanRadial.lean`
   contains:
   - one `theorem` (or `lemma`) named
     `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
     (or equivalently named) whose conclusion is the canonical-witness
     Parseval identity
     `circleMeanSq f r = ∑' k, (2π · r^(2k)) * ‖(cauchyPowerSeries f 0 R).coeff k‖²`
     for `f` analytic on `UnitDisk` and `0 ≤ r < (R : ℝ) < 1`;
   - one `theorem` (or `lemma`) named `circleMeanSq_termwise_mono`
     (or equivalently named) whose conclusion is
     `circleMeanSq f r ≤ circleMeanSq g r` from `‖a k‖ ≤ ‖b k‖`
     pointwise on the canonical Cauchy-power-series coefficients;
   - one `theorem` (or `lemma`) named `circleMeanSq_radial_mono`
     (or equivalently named) whose conclusion is
     `circleMeanSq f r₁ ≤ circleMeanSq f r₂` for `f` analytic on
     `UnitDisk` and `0 ≤ r₁ ≤ r₂ < 1`.
   All three must be `theorem` / `lemma`, never `axiom`, with no `sorry`.
   The proof of (1) (radial monotonicity) must genuinely *use* (3)
   (canonical-witness Parseval) at both radii — not bypass via
   `circleMeanSq_eq_tsum_of_analyticOn_unitDisk`'s existential or via a
   parallel direct argument — so that the chain through canonical Cauchy
   power series is the one actually exercised by the build. Equivalently,
   if the generator chooses to inline the canonicalisation of (3) inside
   the proof of (1) rather than expose it as a separate theorem, the
   inlining must still produce a *deterministic* coefficient witness
   (i.e. a `let p := cauchyPowerSeries f 0 R` rather than an
   `obtain ⟨a, ha⟩ := circleMeanSq_eq_tsum_of_analyticOn_unitDisk …`).
4. The new module `Proof.CircleMeanRadial` must be **used**, even
   trivially, somewhere in V10's transitive compile graph (importing it
   from V10 is sufficient — it forces the module to compile as part of
   V10's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V9.lean`) or the existing
  `Proof/*.lean` files. The canonicalisation of the existential in
  sprint 009's `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` is **not** an
  edit to `Proof/AnalyticParseval.lean`; it is a new theorem in
  `Proof/CircleMeanRadial.lean` that re-derives the same content with a
  fixed witness. Sprint 009's theorem stays unchanged.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If any of the three lemmas is genuinely blocked
  on a missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- **Attempt the inner-half radial dominance** at the `tsum` level, i.e.
  do not try to prove `∀ r ∈ Ioc 0 c, ∑' k, ‖a k‖² · r^(2k) ≤
  ∑' k, ‖b k‖² · r^(2k)` from outer-annulus dominance in this sprint.
  That is the actual mathematical content of Korenblum and requires a
  weighted-extremal-disk argument; it is at least one full follow-up
  sprint (more likely several).
- Prove the **full Bergman Parseval identity**
  `bergmanNormSq f = ∑' k, π / (k + 1) * ‖a k‖²` (a single radial
  integration `∫_0^1 r · circleMeanSq f r dr` against the radial measure).
  Useful as the next sprint after this one, but not required by the three
  items above.
- Bridge `circleMeanSq` to Mathlib's `Real.circleAverage` /
  `Complex.circleIntegral`. Useful long-term but not required here.
- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the radial-monotonicity tool that any future
  c-push must consume.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `cauchyPowerSeries f 0 R` does not unify with
  the formal series produced by sprint 009's
  `DifferentiableOn.hasFPowerSeriesOnBall`-route under the chosen `R`, or
  Mathlib's `tsum_le_tsum` over `ℝ` requires summability hypotheses that
  cannot be discharged from the Parseval `HasSum` data without unfolding,
  or `pow_le_pow_left₀` does not apply to the `r₁ ≤ r₂` term-level
  comparison because the exponent `2 * k` requires a separate
  `pow_le_pow_left_of_le_one`-vs-`pow_le_pow_left` split, or the
  canonicalisation of (3) requires a Mathlib `cauchyPowerSeries`
  radius-independence lemma that turns out to live under a different name
  than the generator can find): `STATUS=BLOCKED` with a precise note in
  `Experience.md` recording which Mathlib lemma was the obstruction and
  which approaches were tried (e.g. whether the generator tried
  `tsum_le_tsum` versus `Summable.tsum_mono`, whether the radius bound
  went through `cauchyPowerSeries_def`-style equality versus a fresh
  `HasFPowerSeriesOnBall` extraction at each `R`, whether the
  termwise-comparison in (2) went through `tsum_le_tsum` directly versus
  a `HasSum.le` route).

  **Fallback form** (if the canonical-witness `cauchyPowerSeries`
  formulation in (3) is too brittle): the generator may instead expose
  (3) as

  ```lean
  theorem circleMeanSq_eq_tsum_witness_of_analyticOn_unitDisk
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1) :
      ∃ a : ℕ → ℂ, ∀ {r : ℝ}, 0 ≤ r → r < (R : ℝ) →
        circleMeanSq f r = ∑' k, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
  ```

  with the existential **outside** the radius `r` quantifier. This is
  weaker than the canonical witness but strong enough for (1) and (2)
  to drop out: a single `obtain ⟨a, ha⟩` at the top of (1) gives a
  common witness for both `r₁` and `r₂`. The fallback is acceptable
  if and only if the generator records in `Experience.md` why the
  canonical-witness form was infeasible.
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
