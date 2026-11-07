# Sprint 037: Pointwise outer (annulus-side) lower bound on `circleGap a b ρ` with **paper-axiom-free body** modulo a single explicit `Λ`-bridge hypothesis cell — the workspace's **first paper-axiom-free annulus-side bound** of any kind, the **annulus-side mirror of sprint 036**, the **first hypothesis-cell lift on the annulus side of the proof** (parallel to but independent of `hSigmaCmp` on the disk side), and the **first lemma to fuse sprint 005 + sprint 027 with an explicit `hLambdaBridge` cell into a single pointwise annulus chain**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V36.lean`
**Target file**: `Candidates/V37.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hLambdaBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
    2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
        / WangOuter.paperLambda K c ρ
      ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
```

The statement and conclusion are **byte-for-byte identical** to sprint
005's `circleGap_outer_lower_bound_of_eq8_eq9`. The **only** signature
change is:

| Sprint | Annulus-bridge inputs              |
|--------|--------------------------------------|
| 005    | `paper : Section2Assumptions a b K c` (body invokes `paper.eq8_sigma_to_liftGap` and `paper.eq9_liftGap_to_circleGap` via `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`) |
| **NEW: 037** | **explicit `hLambdaBridge : sigmaMinus a b ρ ≤ paperLambda K c ρ · circleGap a b ρ`** |

Sprint 037 is the **annulus-side mirror of sprint 036**:

- Sprint 036 lifted the **disk-side** unique series-non-derivable
  conjunct `Σ⁺(c) ≤ Σ⁻(c)` to a hypothesis cell `hSigmaCmp`, giving a
  paper-axiom-free pointwise inner bound on `circleGap a b r` for
  `r < c`.
- Sprint 037 lifts the **annulus-side** unique series-non-derivable
  conjunct (the post-substitution form of `(8)+(9)`,
  `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap ρ`) to a hypothesis cell
  `hLambdaBridge`, giving a paper-axiom-free pointwise outer bound on
  `circleGap a b ρ` for `ρ > c`.

After sprint 037 lands, the workspace has **paper-axiom-free pointwise
bounds on both the inner-disk and outer-annulus sides modulo two
clean hypothesis cells**, isolating the precise oracle/proposal targets
on each side of the closing-reducer cone.

The body of sprint 037 invokes:

| Analytical step inside body                                  | Provider |
|--------------------------------------------------------------|----------|
| `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap ρ`                              | **explicit hypothesis `hLambdaBridge`** |
| `Σ⁻(ρ) = ρ² · Z_ρ`                                            | sprint 005 (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`) |
| `0 < Λ(c, ρ)`                                                 | `WangPaperSideConditions.paperLambda_pos` (already used by sprint 005's body line 534-535; standalone theorem, not a paper-axiom field projection) |
| Divide through by `Λ(c, ρ) > 0`, multiply by `2ρ ≥ 0`, algebraic clean-up | sprint 005's body verbatim (lines 534-559) |

The proof body invokes **zero `paper.eq*` field projections** and
**zero `Section2Assumptions`-bound names**. The `K : ℝ → ℝ → ℝ`
parameter is required only because `paperLambda` takes a `K`, but
nothing about `K` is used beyond passing it through to
`paperLambda` — there is no `paper : Section2Assumptions` instance and
no `paper.K_*` invocation anywhere.

Then ship a `Candidates/V37.lean` at the same `c = 0.3554` that
compiles, scores `≥ V36 = 1777/5000`, and **materialises** the new
theorem in side lemmas
`v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_compiles`
and
`v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_recovers_via_eq8_eq9_at_seed` side lemma demonstrates that the
`hLambdaBridge` hypothesis can be discharged from
`paper.eq8_sigma_to_liftGap` + `paper.eq9_liftGap_to_circleGap` via
`eq8eq9_sigma_to_circleBridge_of_eq8_eq9` at the seed — exactly mirroring
V34/V36's `_recovers_via_eq4_at_seed` pattern. This confirms the new
theorem is a **strict generalisation of sprint 005**: any consumer with
`paper.eq8`/`paper.eq9` access can recover sprint 005's exact conclusion
through the new chain.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 037 ships:

1. **The workspace's first paper-axiom-free annulus-side bound of any
   kind.** Every prior annulus-side bound in `Reduction.lean` (sprint
   005's `circleGap_outer_lower_bound_of_eq8_eq9`, sprint 006's
   `annulusExcess_lower_bound_of_eq8_eq9`, and the annulus halves of
   every closing reducer in the workspace) invokes the
   `paper.eq8_sigma_to_liftGap` + `paper.eq9_liftGap_to_circleGap`
   pair, either directly or through
   `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`. The descending paper-axiom
   signature exercise that the disk side has gone through (sprints
   013, 026, 029, 030, 031, 034, 036) has **not been started on the
   annulus side**. Sprint 037 opens this axis with the smallest
   possible structural first: the pointwise outer lower bound at the
   layer of sprint 005.

2. **Annulus-side mirror of sprint 036 — completes the disk/annulus
   symmetry on the pointwise paper-axiom-free axis.** Sprint 036
   ships the **inner-disk** (`r < c`) pointwise paper-axiom-free
   two-`Z` upper bound on `circleGap a b r` modulo `hSigmaCmp`.
   Sprint 037 ships the **outer-annulus** (`ρ > c`) pointwise
   paper-axiom-free single-`Z` lower bound on `circleGap a b ρ`
   modulo `hLambdaBridge`. Together they form the full
   pointwise/inner/outer × upper/lower matrix on the paper-axiom-free
   axis:

   | Side / Direction        | Paper-axiom-free pointwise bound | Lifted cell |
   |-------------------------|----------------------------------|-------------|
   | Inner disk, upper bound | sprint 036 (two-`Z`)             | `hSigmaCmp` |
   | Outer annulus, lower bound | **NEW sprint 037** (single-`Z`) | `hLambdaBridge` |

   Sprint 037 is the **missing** outer-annulus corner. Together with
   sprint 036 the workspace toolkit covers both sides of the
   `diskExcess + annulusExcess` decomposition paper-axiom-free modulo
   two independent hypothesis cells.

3. **First hypothesis-cell lift on the annulus side — independent of
   `hSigmaCmp`.** The disk-side `hSigmaCmp` cell appears in sprints
   034, 035, 036; the annulus-side `hLambdaBridge` cell would be the
   **first** of its kind. The two cells are **structurally
   independent**:

   * `hSigmaCmp : sigmaPlus a b c ≤ sigmaMinus a b c` is a
     **comparison between two series at the same radius `c`** — a
     statement about how `coeffPlusGap` and `coeffMinusGap` relate
     when both are evaluated on their respective indicator
     restrictions to the disk anchor `c`.
   * `hLambdaBridge : sigmaMinus a b ρ ≤ Λ(c, ρ) · circleGap a b ρ`
     is a **bridge inequality** relating two structurally distinct
     quantities (the indicator-restricted `sigmaMinus` series and the
     unconditioned `circleGapSeries`) at the **outer** anchor `ρ`,
     scaled by the geometric factor `Λ(c, ρ)`.

   A future closing reducer that lifts **both** cells into the
   witness existential would have a paper-axiom-free body modulo
   exactly these two hypothesis cells — the workspace's first reducer
   with **two independent oracle/proposal targets** clearly labelled.

4. **First lemma to fuse sprint 005 with an explicit `hLambdaBridge`
   cell.** Sprint 005's body invokes the `(8)+(9)` bridge (lines
   525-529 of `Reduction.lean`), then sprint 005's own series
   identity, then the `paperLambda_pos` standalone theorem, then
   does the algebraic chain. Sprint 037 retains all of those
   ingredients **except** the `(8)+(9)` bridge invocation, which is
   replaced by direct consumption of the explicit `hLambdaBridge`
   hypothesis. This is a precise structural ablation: sprint 037 =
   sprint 005 minus `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, plus
   `hLambdaBridge`.

5. **Structural prerequisite for paper-axiom-free annulus-side
   downstream sprints.** Once sprint 037 ships, the following
   downstream sprints become available (each queueable as a separate
   sprint after the analytical groundwork sprint 037 lays):

   * A future annulus-side integrated bound
     `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
     (sprint 006's analog, paper-axiom-free modulo a window-uniform
     `hLambdaBridge` family) — would integrate sprint 037's pointwise
     bound over `[ρ₁, ρ₂] ⊂ (c, 1)` and produce a paper-axiom-free
     annulus-side integrated lower bound. The `hLambdaBridge`
     hypothesis would naturally upgrade to a window-uniform form
     (`∀ ρ ∈ Icc ρ₁ ρ₂, hLambdaBridge`).
   * A future closing reducer
     `valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window`
     fusing sprint 035's disk side with the future annulus-side
     integrated bound, achieving **paper-axiom signature `{}` modulo
     two independent hypothesis cells** (`hSigmaCmp` + window-uniform
     `hLambdaBridge`) — the workspace's first end-to-end closing
     reducer with empty paper-axiom signature.
   * Various branch-1/branch-2 paper-axiom-free closing reducer
     variants mirroring sprints 014/017/023 patterns but with
     paper-axiom-free annulus-side body.

   Sprint 037 is the **single bottleneck** for this entire annulus-side
   downstream cone. Without it, every annulus-side bound necessarily
   passes through `paper.eq8`/`paper.eq9`, and every downstream
   annulus-side integrated / closing-reducer sprint inherits this
   dependency.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V37 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form pointwise lower
  bound on `circleGap a b ρ` with the same RHS shape as sprint 005.

Why this is **not** "the same chain" as sprint 005:

* **Different paper-axiom signature.** Sprint 005's body invokes
  `paper.eq8_sigma_to_liftGap` and `paper.eq9_liftGap_to_circleGap`
  via `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (line 528-529 of
  `Reduction.lean`); sprint 037's body invokes **zero** `paper.eq*`
  field projections. The chain through which the same RHS is reached
  is distinct: sprint 005 delegates `Σ⁻(ρ) ≤ Λ(c,ρ) · circleGap ρ` to
  a single `(8)+(9)` bridge invocation; sprint 037 lifts this single
  inequality to an explicit hypothesis cell.
* **Different signature shape.** Sprint 005 has 4 cells (`paper`,
  `hc_pos`, `hcρ`, `hρ1`); sprint 037 has 4 (no `paper` parameter;
  same three geometric cells; new `hLambdaBridge` and `K` as an
  implicit parameter). The structural change: drop `paper`, add
  `hLambdaBridge`, expose `K` as a top-level implicit.
* **Different downstream consumer pattern.** Sprint 005 cannot be
  consumed without `paper.eq8`/`paper.eq9`; sprint 037 *can* be
  consumed without those (e.g., via a future oracle on
  `Σ⁻(ρ) ≤ Λ(c,ρ) · circleGap ρ`, or via a numerical certificate).
  This is the structural distinction.

Why this is **not** "the same chain" as sprint 036:

* **Different side of the proof.** Sprint 036 bounds `circleGap a b r`
  from **above** for `r < c` (inner-disk regime); sprint 037 bounds
  `circleGap a b ρ` from **below** for `ρ > c` (outer-annulus
  regime). The two bounds are not comparable as statements: they
  apply to disjoint radial regimes and have opposite directions.
* **Different lifted hypothesis cell.** Sprint 036 lifts
  `sigmaPlus a b c ≤ sigmaMinus a b c` (a series-vs-series
  comparison at the disk anchor `c`); sprint 037 lifts
  `sigmaMinus a b ρ ≤ Λ(c, ρ) · circleGap a b ρ` (a series-vs-`circleGap`
  bridge at the annulus anchor `ρ` scaled by `Λ`). The two cells
  involve disjoint analytical content: `hSigmaCmp` is a coefficient
  comparison between the N1 and N2 partitions of the same
  `coeffPlusGap`/`coeffMinusGap` family at one radius; `hLambdaBridge`
  is the post-substitution form of the lift-gap bridge that connects
  the outer-annulus mode-restricted series to the unconditioned
  `circleGap` series at a different radius.
* **Different proof body.** Sprint 036 fuses sprints 005, 027, 028,
  032 (a five-element fusion at the pointwise inner-disk layer);
  sprint 037 invokes only sprint 005's series identity (a one-element
  workspace lemma fusion at the pointwise outer-annulus layer) plus
  the standalone `paperLambda_pos`. The two proof bodies share
  **only** sprint 005's identity; the rest of the body is disjoint.

Why this is **not** "the same chain" as sprint 027 alone:

* Sprint 027 is the *identity* `circleGap a b r = sigmaPlus a b r −
  r² · sigmaZeroMinus a b r`. Sprint 037 does **not** consume sprint
  027 directly in its body — sprint 037 stays in the
  `sigmaMinus`/`circleGap` representation throughout (it does not
  decompose `circleGap` into `sigmaPlus` and `sigmaMinus`). The
  annulus-side proof never needs the `sigmaPlus` half of the
  decomposition. (A future variant could consume sprint 027 to give
  a stronger lower bound, but that is out of sprint 037's scope.)

Why this is **not** "the same chain" as sprints 034/035:

* **Sprint 034 is integrated, disk-side, single-`Z`**; sprint 037 is
  pointwise, annulus-side, single-`Z`. The shapes are qualitatively
  different (different layer, different side).
* **Sprint 035 is a closing reducer**; sprint 037 is a pointwise
  bound that would feed a future annulus-side integrated bound and
  then a future closing reducer. The two are at different layers.
* **Sprints 034/035 lift `hSigmaCmp`**; sprint 037 lifts
  `hLambdaBridge`. Different cells, different sides.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~10 lines (sprint 005's signature is ~10
  lines; sprint 037 differs by dropping `paper` and adding
  `hLambdaBridge`).
* The proof body is ~25–30 lines — sprint 005's body (~46 lines,
  lines 514–559 of `Reduction.lean`) modified by:
  - replace lines 525–529 (the `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`
    invocation) with `have hBridge := hLambdaBridge`,
  - drop the `paper` parameter,
  - keep the rest of sprint 005's body byte-for-byte identical
    (lines 530–559: invoke sprint 005's series identity, divide by
    `Λ(c, ρ) > 0` via `paperLambda_pos`, multiply by `2ρ ≥ 0`,
    algebraic clean-up via `field_simp`).
* All Lean idioms used (`mul_le_mul_of_nonneg_left`, `linarith`,
  `field_simp`, `div_le_iff₀`, `simpa`) are verbatim from sprint
  005's body. No new idioms required.
* Estimate: ~25–30 lines for the new theorem. Candidate side lemmas
  ~25 lines each. Total V37 size: ≤ 150 lines.

### Note on the choice to lift `hLambdaBridge` to a hypothesis

Identical in spirit to sprint 034/036's choice to lift `hSigmaCmp`.
An alternative shape would be to **derive** `hLambdaBridge` from
`paper.eq8_sigma_to_liftGap` + `paper.eq9_liftGap_to_circleGap`
internally and bake `paper : Section2Assumptions a b K c` into the
new theorem's signature, eliminating the `hLambdaBridge` hypothesis.
This would **not** achieve sprint 037's structural goal: the body
would still invoke `paper.eq8`/`paper.eq9` and the paper-axiom
signature would remain non-empty. The chosen shape (lift
`hLambdaBridge` to the signature, drop the `paper` parameter
entirely) is what enables structural firsts (#1, #3, #5 above) and
isolates the unique annulus-side oracle target. This deliberate
parallelism with sprint 036 ensures consumers can pair a `hSigmaCmp`
cell (sprint 036) with a `hLambdaBridge` cell (sprint 037) to obtain
a fully-paper-axiom-free pointwise pair on the disk and annulus
sides.

### Note on the discharge of `hLambdaBridge` at the seed

V37's `_recovers_via_eq8_eq9_at_seed` side lemma exhibits the
**discharge route via `paper.eq8_sigma_to_liftGap` and
`paper.eq9_liftGap_to_circleGap`**: given a
`Section2Assumptions a b K c_value` instance, the lemma invokes
`PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ1`
to produce an inhabitant of
`sigmaMinus a b ρ ≤ paperLambda K c ρ · circleGap a b ρ`,
then plugs this into the new generic theorem along with the
geometric cells. The resulting conclusion is byte-for-byte identical
to sprint 005's at the seed — recovering sprint 005's exact bound
through sprint 037's chain.

This side lemma serves **two roles**: (a) confirms the new theorem
is a strict generalisation of sprint 005 (any consumer with
`paper.eq8`/`paper.eq9` access can recover sprint 005's bound from
sprint 037); (b) demonstrates the precise discharge route that a
future oracle-bearing consumer would substitute (replace the
`paper.eq8`/`paper.eq9` invocations with the oracle's witness — every
other cell remains identical).

### Note on the `K` parameter

Sprint 037's signature must keep `K : ℝ → ℝ → ℝ` as an implicit
parameter because the conclusion contains `paperLambda K c ρ`, which
takes `K` as a parameter. However, **nothing in sprint 037's body
uses any property of `K` beyond passing it through to `paperLambda`**.
There is no `paper : Section2Assumptions a b K c` instance, no
`paper.K_*` invocation, no `K`-specific hypothesis. The `K`
parameter is purely syntactic, present only because `paperLambda`'s
type signature requires it. (`paperLambda_pos` is also parametrised
by `K` but is a standalone theorem with no `paper` premise.)

### Note on hypothesis-count and analytical structure

Sprint 005 has 4 cells (`paper`, `hc_pos`, `hcρ`, `hρ1`). Sprint 037
has 4 cells (paper-axiom-free; no `paper` parameter; same three
geometric cells; new `hLambdaBridge`). The hypothesis-count delta is
0 (drop `paper`, add `hLambdaBridge`). Net: hypothesis count
identical; paper-axiom signature on the body shrinks from
`{eq8, eq9}` to `{}` modulo the explicit `hLambdaBridge`.

### Note on the witness at the seed

V37's `_recovers_via_eq8_eq9_at_seed` side lemma should exhibit the
discharge of the new theorem at the seed `c = c_value = 3554/10000`,
with `hLambdaBridge` discharged by `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`
applied to `paper.eq8_sigma_to_liftGap` and
`paper.eq9_liftGap_to_circleGap`. The other hypotheses are
discharged via existing seed scaffolding patterns. The structural-marker
`ρ` value should be a concrete rational larger than `c_value` (e.g.,
`ρ := 1/2` mirroring sprint 022's witness, well above the seed
`c_value ≈ 0.3554`).

The `_compiles` side lemma should exhibit the new theorem's
hypothesis shape with concrete `c = c_value`, `ρ := 1/2`,
`K := fun _ _ => 1` (or any concrete `K` that satisfies
`paperLambda_pos`'s side conditions implicitly — `paperLambda_pos`
is `K`-uniform). The `hLambdaBridge` hypothesis is taken as a
universally-quantified Lean hypothesis on the side lemma.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
      {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ : ℝ}
      (hc_pos : 0 < c)
      (hcρ : c < ρ)
      (hρ1 : ρ < 1)
      (hLambdaBridge :
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
      2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ
        ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
  ```
  Estimated location: append after sprint 036's
  `circleGap_inner_bound_via_series_only_modulo_sigma_compare`
  (at the current end of `Reduction.lean`). Estimated ~25–30 lines.

  The proof body is structurally **sprint 005's body verbatim**
  (lines 514–559 of `Reduction.lean`) with the following targeted
  substitution at lines 525–529:

  Replace
  ```lean
  -- (8)+(9) bridge: sigmaMinus ρ ≤ Λ(c, ρ) · circleGap ρ.
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
      paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ1
  ```
  with
  ```lean
  -- Explicit hypothesis: `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap ρ`.
  -- This replaces sprint 005's invocation of
  -- `eq8eq9_sigma_to_circleBridge_of_eq8_eq9 paper.eq8_* paper.eq9_*`,
  -- making the body paper-axiom-free.
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    hLambdaBridge
  ```

  Drop the `paper : Section2Assumptions a b K c` parameter. Keep the
  rest of sprint 005's body (lines 530–559: invoke sprint 005's
  series identity `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, derive
  `0 < paperLambda K c ρ` via `WangPaperSideConditions.paperLambda_pos`,
  divide through, multiply by `2ρ ≥ 0`, algebraic clean-up via
  `field_simp`) **byte-for-byte identical** to sprint 005.

- `ProofRefinement/Korenblum/Candidates/V37.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V36),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V36),
  4. Adds two side lemmas
     `v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_compiles`
     and
     `v37_circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`
     exercising the new generic theorem:
     - `_compiles` exhibits the new theorem's hypothesis shape — four
       cells: `hc_pos`, `hcρ`, `hρ1`, `hLambdaBridge`. Concrete
       witness: instantiate at `c = c_value = 3554/10000`,
       `ρ := 1/2`, `K := fun _ _ => 1` (or any concrete `K`). The
       `hLambdaBridge` hypothesis is taken as a universally-quantified
       Lean hypothesis on the side lemma; this side lemma does **not**
       use a `paper` instance.
     - `_recovers_via_eq8_eq9_at_seed` takes a `Section2Assumptions a b K
       c_value` instance, discharges `hLambdaBridge` from
       `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
       paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ
       hρ1`, and applies the new theorem to recover sprint 005's exact
       conclusion at the seed (`2ρ³·Z_ρ/Λ(c,ρ) ≤ 2ρ·circleGap a b ρ`
       with `ρ := 1/2`).
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V36).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V37` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V37.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V37 ties V36 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V37.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V37.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — the body is paper-axiom-free.
   Greppable check: in the body of
   `circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`,
   the count of `paper.eq` substrings is **0**. (The lemma's signature
   also does not include a `paper : Section2Assumptions ...`
   parameter.)
7. The proof body **does not invoke**
   `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` — that bridge constructor
   is the workspace marker for `eq8`+`eq9` chains and its absence
   confirms the lifted-cell chain. Greppable check: count of
   `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` in the body of the new
   theorem is **0**.
8. The proof body invokes `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
   (sprint 005's series identity) at least once. Greppable check:
   count of `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` substrings in
   the body of the new theorem is ≥ 1.
9. The proof body invokes `WangPaperSideConditions.paperLambda_pos`
   (or its `paperLambda_pos`-equivalent unqualified form) at least
   once. Greppable check: count of `paperLambda_pos` substrings in
   the body of the new theorem is ≥ 1.
10. The new theorem's signature includes the explicit
    `hLambdaBridge : PaperAxioms.sigmaMinus a b ρ ≤
    WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ`
    hypothesis. Greppable check: the substring `hLambdaBridge`
    appears in the signature line region of the new theorem.
11. The V37 `_recovers_via_eq8_eq9_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` exactly once,
    in the proof body (greppable: count of
    `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` in the body of
    `v37_..._recovers_via_eq8_eq9_at_seed` is exactly 1). This
    confirms the new theorem **strictly generalises** sprint 005
    (any consumer with `paper.eq8`/`paper.eq9` access can recover
    sprint 005's conclusion through the new chain).
12. The proof body of the new theorem **does not invoke**
    `circleGap_outer_lower_bound_of_eq8_eq9` (sprint 005's outer
    lower bound) — the structural marker that sprint 037 is a
    fresh chain, not a wrapper around sprint 005. Greppable check:
    count of `circleGap_outer_lower_bound_of_eq8_eq9` in the body
    of the new theorem is 0.
13. The new theorem's conclusion is **byte-for-byte identical** to
    sprint 005's `circleGap_outer_lower_bound_of_eq8_eq9` conclusion
    (modulo whitespace): both produce
    `2 * ρ ^ 3 * sigmaZeroMinus a b ρ / paperLambda K c ρ ≤
    2 * ρ * circleGap a b ρ`.

## Out of scope

- Edit older candidates V0–V36.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V37 is the
  same `hEq15_seed_3554` that V0–V36 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land an oracle/proposal for `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap ρ`. Sprint
  037 isolates this as a type-level hypothesis but does not itself
  discharge it via an oracle. A future planner may file
  `Proposals/proposal_<NNN>_*.md` for a numerical or analytical
  oracle on the lambda-bridge inequality if motivated; sprint 037 is
  decoupled from that proposal.
- Materialise sprint 037 in a downstream chain (i.e., do not
  re-derive sprint 006's `annulusExcess_lower_bound_of_eq8_eq9` or
  any closing reducer using sprint 037 yet — those are second-order
  follow-up sprints). Sprint 037 ships only the new pointwise outer
  bound plus its V37 side-lemma materialisations.
- Land an integrated annulus-side bound paper-axiom-free modulo
  `hLambdaBridge` (the natural "sprint 038" — sprint 006's analog).
  This requires a window-uniform `hLambdaBridge` family
  (`∀ ρ ∈ Icc ρ₁ ρ₂, hLambdaBridge`) and the corresponding
  integrability/measurability machinery; queueable as a separate
  sprint.
- Land a closing reducer paper-axiom-free modulo both `hSigmaCmp`
  and a window-uniform `hLambdaBridge` (the natural "sprint 039" —
  fusion of sprint 035 with the future "sprint 038"). Requires the
  intermediate annulus-side integrated bound; queueable separately.
- Land a paper-axiom-free outer lower bound through any *other*
  chain (e.g., via sprint 027's equality decomposition of `circleGap`
  followed by separate bounds on `sigmaPlus ρ` and `sigmaMinus ρ`).
  The single-`hLambdaBridge`-cell chain is the unique chain we ship
  in sprint 037.
- Series-derive any disk-side bound. The disk-side paper-axiom
  signature is unchanged by sprint 037; sprints 034/036 already
  cover it.

## Time budget

≤ 45 minutes runtime. (Sprint 005's body is ~46 lines; sprint 037's
body is sprint 005's body with one targeted replacement of ~6 lines
at the `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` invocation, dropping
the `paper` parameter. V37 candidate adds ~25–30 lines per side lemma.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
