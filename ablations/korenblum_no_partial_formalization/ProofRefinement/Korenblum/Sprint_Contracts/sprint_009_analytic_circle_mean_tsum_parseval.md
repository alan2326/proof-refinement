# Sprint 009: analytic `circleMeanSq` is the `tsum` of the polynomial Parseval terms

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V8.lean`
**Target file**: `Candidates/V9.lean`
**Direction**: section2-proof (Bergman scaffolding — analytic-to-`tsum` Parseval bridge,
the explicitly-named follow-up of sprint 008)

## Goal

Lift sprint 008's polynomial Parseval identity

```
circleMeanSq (fun z => ∑ k ∈ Finset.range N, a k * z ^ k) r
  = ∑ k ∈ Finset.range N, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
```

to the **analytic / power-series** case. In a new file
`Proof/AnalyticParseval.lean`, expose:

1. `circleMeanSq_hasFPowerSeriesOnBall` — *the headline identity*. For any
   analytic `f : ℂ → ℂ` represented by a formal power series `p` on the
   open ball `ball 0 R` (i.e. `HasFPowerSeriesOnBall f p 0 R` with
   `R : ℝ≥0∞`), and any radius `r : ℝ` with `0 ≤ r` and `(r : ℝ≥0∞) < R`,

   ```lean
   circleMeanSq f r
     = ∑' k : ℕ, (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2
   ```

   The series on the RHS is summable; its `tsum` equals the
   circle-mean.

2. `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` — *the disk-shape consumer*.
   For any `f : ℂ → ℂ` with `AnalyticOn ℂ f UnitDisk` and any `r : ℝ` with
   `0 ≤ r` and `r < 1`, there exists a sequence `a : ℕ → ℂ` such that

   ```lean
   circleMeanSq f r = ∑' k : ℕ, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
   ```

   This is the form actually consumed by any future Korenblum-style
   coefficient-level argument inside `UnitDisk`. It follows from (1) by
   producing the `HasFPowerSeriesOnBall` data on `ball 0 1` from
   `AnalyticOn ℂ f UnitDisk` (Mathlib: `AnalyticOn.hasFPowerSeriesOnBall`
   on a ball, or the local `AnalyticAt.hasFPowerSeriesAt` plus a
   radius-of-convergence bound; the generator may use whichever Mathlib
   handle is cleanest as long as the conclusion is unchanged).

V9 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V8 and
the only seed axiom is still `hKorenblum_published_3554`. The contribution
is the new derived module that finally bridges the *analytic* function-level
Korenblum hypothesis space (which is what `ValidKorenblumBound` actually
quantifies over) to the *coefficient-level* Parseval `tsum` form. Without
this bridge the polynomial Parseval of sprint 008 is unusable in any honest
c-push: the contract admits arbitrary analytic `f, g`, not polynomials.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

- **This is the explicitly named follow-up.** Sprint 008's *Out of scope*
  paragraph says: *"Prove the `tsum`-level Parseval identity for analytic
  `f` on the open unit disk, i.e. `circleMeanSq f r = 2π · ∑' k, ‖a k‖² ·
  r^(2k)` for `f` with formal power series `(a, R)`. This is the next
  sprint, built on top of (1)–(4) plus a Mathlib bridge through
  `HasFPowerSeriesOnBall` and a dominated-convergence-on-θ argument."*
  Sprint 009 is exactly that next sprint.
- **It is a strict prerequisite for any c-push, not a parallel direction.**
  `ValidKorenblumBound c` quantifies over **arbitrary** `AnalyticOn ℂ f
  UnitDisk` `f, g`, not polynomials. Sprint 008's polynomial Parseval is
  therefore the limit-target, not the consumed form. Until the analytic
  case is reduced to the `tsum` form, the inner-half radial dominance
  hypothesis of sprint 005 (`validKorenblum_of_innerCircleMean_dom`) cannot
  be discharged for the actual contract: the generator would have nothing
  to compute against. With the `tsum` form in place, the next sprint can
  attempt the inner-half radial dominance as a `tsum` inequality

  ```
  ∀ r ∈ Ioc 0 c, ∑' k, ‖a k‖² · r^(2k) ≤ ∑' k, ‖b k‖² · r^(2k)
  ```

  which, while still hard, is at least concretely formulated and admits
  Cauchy–Schwarz / extremal-disk attacks.
- **The proof outline is bounded.** Mathlib provides every piece:
  - `HasFPowerSeriesOnBall.tendstoUniformlyOn` (from
    `Mathlib.Analysis.Analytic.Basic`): partial sums of `p` converge
    uniformly to `f` on `closedBall 0 r'` for any `r' : ℝ≥0` with
    `(r' : ℝ≥0∞) < R`.
  - `Complex.norm_polarCoord_symm` plus `polarCoord_symm_eq_exp` (sprint 006):
    `polarCoord.symm (r, θ)` lies in `Metric.closedBall 0 r` (for `0 ≤ r`)
    by `‖polarCoord.symm (r, θ)‖ = r`.
  - The composition with `polarCoord.symm` of a uniform limit on
    `closedBall 0 r` is again a uniform limit on `Ioo (-π) π`
    (uniformly-on-the-image), via `TendstoUniformlyOn.comp`.
  - Squaring the norm preserves uniform convergence on a bounded image
    (`Continuous.tendstoUniformlyOn` on `‖·‖²`, or
    `TendstoUniformlyOn.norm.sq` via `(·)^2`'s uniform continuity on
    bounded sets).
  - `MeasureTheory.tendsto_setIntegral_of_tendstoUniformlyOn` (or its
    Bochner variant) on `Ioo (-π) π` (a bounded measurable set) closes the
    integral-of-limit = limit-of-integrals step.
  - The polynomial Parseval (sprint 008) gives the partial-sum identity.
  - Adding back the `r` factor and pushing through `tsum` is one
    `Filter.Tendsto.add` / `HasSum.tsum_eq` step.
- **Falsifiable in one Generator session.** Each step above is one Mathlib
  rewrite. The genuinely uncertain step is which of Mathlib's three
  uniform-convergence-of-power-series API surfaces is the cleanest:
  - `HasFPowerSeriesOnBall.tendstoUniformlyOn` (uniform-on-`closedBall`
    convergence of the `partialSum`),
  - `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv_smul`,
  - `Asymptotics.IsBigO.partialSum_tsum`-shaped bound.
  If the cleanest API turns out to be one we have not anticipated, the
  generator records it in `Experience.md` and the sprint is informative
  even if it `STATUS=BLOCKED`.
- **The `r = 0` corner.** At `r = 0`, `circleMeanSq f 0 = 2π · ‖f 0‖² =
  2π · ‖p.coeff 0‖²` and `r^(2k) = 0` for `k ≥ 1`, so the `tsum` collapses
  to the `k = 0` term. This is a `by_cases r = 0` corner that costs one
  short branch using `Real.zero_pow_eq` / `pow_zero`. Not a blocker.
- **Why not also push c.** The polynomial-level inner-half radial
  dominance is genuinely false in general (Korenblum is not pointwise on
  circle-means; the proof requires a weighted argument that is the actual
  content of the theorem). Bundling a c-push with this scaffolding would
  tie pass criteria to an as-yet-unwritten coefficient-level inequality
  whose mathematical content Wang's paper itself takes 30+ pages to
  assemble. Pinning the analytic-to-`tsum` bridge as scaffolding-only
  isolates the limit-passing content cleanly and keeps the sprint
  acceptance criterion falsifiable in one Generator session.
- **Why not bundle into a numerical-budget push.** The workspace currently
  has zero analytic-to-coefficient bridges. Without one, no honest attack
  on the inner half can compile against the polynomial-Parseval scaffolding
  without rebuilding the bridge from scratch. Filing a "push c from 0.3554
  to 0.36 via direct Mathlib argument" sprint at this stage would be
  premature — the analytic-to-`tsum` Parseval bridge is the prerequisite,
  not the inverse.
- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Parseval
  / boundary L² expansions on analytic functions"*, *"termwise summability
  and `tsum`-level rearrangements"*, and *"bridging pointwise modulus
  inequalities to boundary integrals"* as in scope. This sprint is exactly
  one such bridge, applied at radius `r < 1` instead of at the boundary.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/AnalyticParseval.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.RadialBergman`,
    `Proof.CircleExpBridge`, `Proof.CircleInnerProduct`,
    `Proof.CirclePolynomialParseval` (and **only** those workspace-side
    imports),

  - exposes (1) `circleMeanSq_hasFPowerSeriesOnBall`. Statement (or
    equivalent — the exact integrability hypotheses on the partial-sum
    convergence are at the generator's discretion as long as the
    conclusion is unchanged):

    ```lean
    theorem circleMeanSq_hasFPowerSeriesOnBall
        {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ≥0∞}
        (hf : HasFPowerSeriesOnBall f p 0 R)
        {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : (r : ℝ≥0∞) < R) :
        circleMeanSq f r
          = ∑' k : ℕ,
              (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2
    ```

    Proof outline:

    - **Step 1** — Pin `aₖ := p.coeff k : ℂ`. (Mathlib name:
      `FormalMultilinearSeries.coeff`.)

    - **Step 2** — Reduce to uniform convergence on the closed circle of
      radius `r`. Use `HasFPowerSeriesOnBall.tendstoUniformlyOn` (or
      `HasFPowerSeriesOnBall.tendstoUniformlyOn_of_lt_radius`) to obtain

      ```
      TendstoUniformlyOn
        (fun N z => ∑ k ∈ Finset.range N, p.coeff k * z ^ k)
        f atTop (Metric.closedBall 0 r)
      ```

      (or its `Asymptotics.IsBigO`-shaped Mathlib equivalent).

    - **Step 3** — Compose with `polarCoord.symm`. The image of
      `Ioo (-π) π` under `θ ↦ polarCoord.symm (r, θ)` lies in
      `Metric.closedBall 0 r` because
      `‖polarCoord.symm (r, θ)‖ = |r| = r` (using `0 ≤ r`). Apply
      `TendstoUniformlyOn.comp` (or pull back the uniform-convergence
      witness via `Set.MapsTo`) to get

      ```
      TendstoUniformlyOn
        (fun N θ => ∑ k ∈ Finset.range N,
            p.coeff k * (Complex.polarCoord.symm (r, θ)) ^ k)
        (fun θ => f (Complex.polarCoord.symm (r, θ)))
        atTop (Set.Ioo (-Real.pi) Real.pi)
      ```

    - **Step 4** — Square the norm. The map `z ↦ ‖z‖²` is uniformly
      continuous on the bounded set `Metric.closedBall 0 r` (continuous
      on a compact set), so `TendstoUniformlyOn.comp_continuous` (or
      a manual `TendstoUniformlyOn.norm.sq`) gives

      ```
      TendstoUniformlyOn
        (fun N θ =>
          ‖∑ k ∈ Finset.range N,
              p.coeff k * (Complex.polarCoord.symm (r, θ)) ^ k‖ ^ 2)
        (fun θ => ‖f (Complex.polarCoord.symm (r, θ))‖ ^ 2)
        atTop (Set.Ioo (-Real.pi) Real.pi)
      ```

    - **Step 5** — Pass the limit through the integral. Apply
      `MeasureTheory.tendsto_setIntegral_of_tendstoUniformlyOn` (or its
      Bochner variant on the bounded measurable set `Ioo (-π) π`,
      which has finite volume) to commute `Filter.Tendsto` with the
      `setIntegral`. Each partial-sum integrand is continuous in θ, so
      its `IntegrableOn (Ioo (-π) π) volume` is automatic via
      `Continuous.integrableOn_Ioc.mono_set Ioo_subset_Ioc_self`
      (the same pattern sprint 008 uses).

    - **Step 6** — Apply sprint 008's polynomial Parseval to each
      partial sum:

      ```
      ∫ θ in Ioo (-π) π,
          ‖∑ k ∈ Finset.range N, p.coeff k *
              (Complex.polarCoord.symm (r, θ)) ^ k‖ ^ 2
        = circleMeanSq (fun z => ∑ k ∈ Finset.range N, p.coeff k * z ^ k) r
        = ∑ k ∈ Finset.range N,
            (2 * Real.pi * r ^ (2 * k)) * ‖p.coeff k‖ ^ 2
      ```

      via `circleMeanSq` unfolding (matching the integrand shape) plus
      `circleMeanSq_polynomial` (sprint 008).

    - **Step 7** — Assemble. The `Filter.Tendsto` of the partial-sum
      identities (a `Finset.range N` finite sum over `k`) to a `tsum` is
      the definition of `HasSum`. Apply `HasSum.tsum_eq` (or
      `Summable.tsum_eq_of_tendsto_finset_sum`) to identify the limit
      as `∑' k, (2π · r^(2k)) * ‖p.coeff k‖²`.

    The generator is free to consolidate steps or to use a different
    Mathlib path (e.g. `HasFPowerSeriesOnBall.hasSum` plus an
    integral-of-`HasSum` argument) as long as the conclusion is
    unchanged and the proof is a `theorem` (no `axiom`, no `sorry`).

  - exposes (2) `circleMeanSq_eq_tsum_of_analyticOn_unitDisk`. Statement
    (or equivalent):

    ```lean
    theorem circleMeanSq_eq_tsum_of_analyticOn_unitDisk
        {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < 1) :
        ∃ a : ℕ → ℂ,
          circleMeanSq f r
            = ∑' k : ℕ, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
    ```

    Proof outline:

    - From `AnalyticOn ℂ f UnitDisk` (i.e. `AnalyticOn ℂ f
      (Metric.ball 0 1)`), extract `HasFPowerSeriesOnBall f p 0 R` for
      some `p : FormalMultilinearSeries ℂ ℂ ℂ` and some
      `R : ℝ≥0∞` with `R ≥ 1` (i.e. `(1 : ℝ≥0∞) ≤ R`). Mathlib handle:
      `AnalyticAt.hasFPowerSeriesAt` at `0 ∈ ball 0 1` gives
      `HasFPowerSeriesAt f p 0` for some `p`; then upgrade to
      `HasFPowerSeriesOnBall` with radius equal to the formal-series
      radius `p.radius`, and observe `p.radius ≥ 1` because `f` is
      analytic on the entire ball of radius 1.

      An alternative cleaner handle if available:
      `AnalyticOn.hasFPowerSeriesOnBall` (or
      `AnalyticOnNhd.hasFPowerSeriesOnBall`) directly producing
      `HasFPowerSeriesOnBall f p 0 1` from
      `AnalyticOn ℂ f (Metric.ball 0 1)`. The generator should pick
      whichever Mathlib name is exposed.

    - Take `a k := p.coeff k`.

    - Apply (1) at this `p` and the chosen radius bound. Need
      `(r : ℝ≥0∞) < R`; derive from `r < 1 ≤ R` via
      `ENNReal.coe_lt_coe.mpr` plus the radius bound.

  - Both items must be `theorem`/`lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as
    long as the conclusion is unchanged.

- `ProofRefinement/Korenblum/Candidates/V9.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V9`, marked
  `-- @parent V8`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V8),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V8,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`,
    `ProofRefinement.Korenblum.Proof.CircleExpBridge`,
    `ProofRefinement.Korenblum.Proof.CircleInnerProduct`,
    `ProofRefinement.Korenblum.Proof.CirclePolynomialParseval`,
    and the new
    `ProofRefinement.Korenblum.Proof.AnalyticParseval` so that the new
    module is part of V9's compile graph and is exercised by the build.
    No structural use of the new lemmas in V9 itself is required.
- No edits to `lemma.toml`. No edits to V0/.../V8 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V9` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V9.lean` succeeds (the evaluator
   accepts V9 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V8; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/AnalyticParseval.lean`
   contains:
   - one `theorem` (or `lemma`) named
     `circleMeanSq_hasFPowerSeriesOnBall` (or equivalently named) whose
     conclusion is `circleMeanSq f r = ∑' k, (2 * Real.pi * r^(2k)) *
     ‖p.coeff k‖²` for `f` having a formal power series `p` on a ball of
     radius `R > (r : ℝ≥0∞)`;
   - one `theorem` (or `lemma`) named
     `circleMeanSq_eq_tsum_of_analyticOn_unitDisk` (or equivalently
     named) whose conclusion is the existence of `a : ℕ → ℂ` such that
     `circleMeanSq f r = ∑' k, (2 * Real.pi * r^(2k)) * ‖a k‖²` for
     `AnalyticOn ℂ f UnitDisk` and `0 ≤ r < 1`.
   Both must be `theorem` / `lemma`, never `axiom`, with no `sorry`.
   The proof of (1) must genuinely *use* `circleMeanSq_polynomial`
   (sprint 008) — not bypass it via a parallel direct argument — so that
   the chain from polynomial Parseval to analytic Parseval is the one
   actually exercised by the build.
4. The new module `Proof.AnalyticParseval` must be **used**, even
   trivially, somewhere in V9's transitive compile graph (importing it
   from V9 is sufficient — it forces the module to compile as part of
   V9's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V8.lean`) or the existing
  `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`, `Proof/CircleMeanCompare.lean`,
  `Proof/RadialSplit.lean`, `Proof/CircleExpBridge.lean`,
  `Proof/CircleInnerProduct.lean`,
  `Proof/CirclePolynomialParseval.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If either lemma is genuinely blocked on a
  missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- **Attempt the inner-half radial dominance** at the `tsum` level, i.e.
  do not try to prove `∀ r ∈ Ioc 0 c, ∑' k, ‖a k‖² · r^(2k) ≤
  ∑' k, ‖b k‖² · r^(2k)` from outer-annulus dominance in this sprint.
  That is the actual mathematical content of Korenblum and requires a
  weighted-extremal-disk argument; it is at least one full follow-up
  sprint (more likely several).
- Bridge `circleMeanSq` to Mathlib's `Real.circleAverage` /
  `Complex.circleIntegral`. Useful long-term but not required by the
  two items above.
- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the analytic-to-coefficient bridge that
  any future c-push must consume.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. the cleanest Mathlib uniform-convergence-of-
  power-series API surface is not `HasFPowerSeriesOnBall.tendstoUniformlyOn`
  but a different name and the alternative path is brittle, or
  `MeasureTheory.tendsto_setIntegral_of_tendstoUniformlyOn` does not exist
  under that exact name and the generator cannot find the Bochner-integral
  variant, or `TendstoUniformlyOn.comp_continuous` for squaring the norm
  does not lift cleanly through `polarCoord.symm`'s parametrisation, or
  the radius-bound chain `(r : ℝ≥0∞) < R` requires a coercion the
  generator cannot discharge cleanly, or `AnalyticOn.hasFPowerSeriesOnBall`
  on `Metric.ball 0 1` is not the available Mathlib name and the
  alternative `AnalyticAt.hasFPowerSeriesAt` plus radius-upgrade chain is
  too brittle to discharge in one session): `STATUS=BLOCKED` with a
  precise note in `Experience.md` recording which Mathlib lemma was the
  obstruction and which approaches were tried (e.g. whether the
  generator tried `HasFPowerSeriesOnBall.tendstoUniformlyOn` versus
  `FormalMultilinearSeries.hasSum` plus a manual `tsum`-of-uniform-limit
  argument; whether the integral-limit step was attacked via
  `tendsto_setIntegral_of_tendstoUniformlyOn` versus
  `tendsto_integral_of_dominated_convergence`; whether the radius
  upgrade went through `AnalyticOn.hasFPowerSeriesOnBall` versus
  `AnalyticAt.hasFPowerSeriesAt` plus a radius-bound argument).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
