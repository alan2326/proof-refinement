# Sprint 033: Series-level cross-radius **upper** bound on `sigmaPlus` via N1 termwise convexity — the workspace's **first paper-axiom-free convexity lemma on `sigmaPlus`**, the **N1-side dual of sprint 028's N2-side `sigmaZeroMinus` convexity**, and the **closure of the convexity-vs-monotonicity matrix on the N1 partition** opened by sprint 032

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V32.lean`
**Target file**: `Candidates/V33.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem sigmaPlus_upper_via_series_convexity
    (a b : ℕ → ℂ) {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt_c : r < c)
    (hc_lt_ρ : c < ρ)
    (hSummable_r :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
        else 0))
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b c ≤
      ((ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b r +
        ((c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b ρ
```

This is the **N1-side termwise-convexity dual of sprint 028's
`sigmaZeroMinus_lower_via_series_convexity`** (`Reduction.lean:4047-`).
Where sprint 028 proves the N2-restricted partial-sum **lower** bound
`Z_r ≥ μ₁ Z_c − μ₂ Z_ρ` from non-negativity of `coeffMinusGap a b k` on
N2 and convexity of `t ↦ t^(k-1)`, sprint 033 proves the N1-restricted
partial-sum **upper** bound `Σ⁺(c) ≤ μ₁ Σ⁺(r) + μ₂ Σ⁺(ρ)` from
non-negativity of `coeffPlusGap a b k` on N1 (positive-`k` portion) and
convexity of `t ↦ t^k` (no `−1` shift), with the `k = 0` summand handled
by termwise equality (`coeffPlusGap a b 0 = μ₁·coeffPlusGap a b 0 +
μ₂·coeffPlusGap a b 0` since `μ₁ + μ₂ = 1`).

The proof body parallels sprint 028's body line-for-line with the four
substitutions:

* `n2Pred a b k` → `n1Pred a b k`
* `coeffMinusGap a b k` → `coeffPlusGap a b k`
* `s ^ (2 * k - 2)` → `s ^ (2 * k)` (no `−2` exponent shift)
* `sigmaZeroMinus a b _` → `sigmaPlus a b _`

The structurally-novel step compared to sprint 028 is the `k = 0`
sub-case in the termwise convexity inequality. Sprint 028's N2-side
argument has `n2Pred a b 0 = (0 < 0 ∧ _) = False`, so the `k = 0`
summand is trivially zero. Sprint 033's N1-side argument has
`n1Pred a b 0 = True`, so the `k = 0` summand is `coeffPlusGap a b 0 *
r^0 = coeffPlusGap a b 0` on **all three** of `r`, `c`, `ρ`. Termwise
convexity at `k = 0` reduces to
`coeffPlusGap a b 0 ≤ μ₁·coeffPlusGap a b 0 + μ₂·coeffPlusGap a b 0`,
which since `μ₁ + μ₂ = 1` collapses to `le_refl _` — irrespective of the
sign of `coeffPlusGap a b 0` (which can be negative when `‖a 0‖ < ‖b 0‖`).

The summability transfer follows sprint 028's existing two-summability
pattern: take `Summable` at *both* lower-radius `r` and upper-radius `ρ`
as hypotheses, then derive `Summable` at `c` via the workspace's existing
`sigmaPlus`-side summability transfer (or via `Summable.add` of bounded
sandwich) — the natural mirror of sprint 028's two-summability anchor
shape (sprint 028 takes `Summable` at upper-`ρ` and uses sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` to derive at `c` and `r`;
sprint 033 cannot use sprint 012 because that lemma is N2-side, so we
take both `r` and `ρ` summability premises and derive `c` summability
in-house via `Summable.of_nonneg_of_le` applied to the convex-combination
upper bound).

Then ship a `Candidates/V33.lean` at the same `c = 0.3554` that
compiles, scores `≥ V32 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v33_sigmaPlus_upper_via_series_convexity_compiles` and
`v33_sigmaPlus_upper_via_series_convexity_witness_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 033 is the **first paper-axiom-free convexity lemma on
`sigmaPlus`**, on the previously-untouched N1-side of the
convexity-vs-monotonicity matrix:

| Axis | N1 partition (`sigmaPlus`) | N2 partition (`sigmaZeroMinus`) |
|------|-----------------------------|----------------------------------|
| Monotonicity (two-radius, `t ↦ t^k`) | sprint 032 | sprint 011 |
| Convexity (three-radius, `t ↦ t^k`/`t^(k-1)`) | **NEW: sprint 033** | sprint 028 |
| Summability transfer | (in-house in 033) | sprint 012 |

After sprint 033 lands, the workspace has a **complete 2×2
convexity-vs-monotonicity matrix on both partitions**. This matrix is
the structural prerequisite for any future series-level argument that
needs to bridge `Σ⁺(r), Σ⁺(c), Σ⁺(ρ)` across multiple radii — for
instance, a series-level upper bound on `Σ⁺(c)` via `Σ⁺(r₁), Σ⁺(r₂)`
at convex combinations of `r₁², r₂²`, which is the natural
**series-side cross-validation skeleton** for paper-internal-derivation
attempts on the second conjunct of `paper.eq4_sigmaPlus_bound`
(`Σ⁺(c) ≤ Σ⁻(c)`) — sprint 026's "candidate K" analysis flagged that
conjunct as not directly series-derivable, but the sharpest known route
to a series-side *upper* bound on `Σ⁺(c)` is precisely a convex
combination of `Σ⁺` evaluated at flanking radii. Sprint 033 provides
exactly that ingredient.

The structural firsts:

1. **First paper-axiom-free convexity lemma on `sigmaPlus`.** Sprint
   028 was the workspace's first paper-axiom-free convexity lemma on
   `sigmaZeroMinus` (N2 partition). Sprint 033 is the **dual on the N1
   partition**, exploiting the *structurally distinct* termwise
   non-negativity of `coeffPlusGap a b k` on N1 (positive-`k` portion)
   and the trivial-equality termwise behaviour at `k = 0`.

2. **First `tsum`-level cross-radius bound on `Σ⁺` evaluated at three
   distinct radii.** Prior workspace `sigmaPlus` lemmas: sprint 025
   (`circleGap_le_sigmaPlus_via_series_split` — single-radius drop-N2),
   sprint 026 (`diskExcess_upper_bound_via_circleGapSeries_eq4_only`
   — single-radius integrated), sprint 032
   (`sigmaPlus_monotone_of_summable` — two-radius monotonicity).
   Sprint 033 is the **first three-radius lemma** on `sigmaPlus`,
   matching the three-radius shape of paper-equation `eq2`.

3. **First lemma to handle the `k = 0 ∈ N1` boundary case in a
   convex-combination context.** Sprint 032 handled `k = 0 ∈ N1` for a
   monotonicity argument (`coeffPlusGap a b 0 ≤ coeffPlusGap a b 0`,
   trivial `le_refl`). Sprint 033 handles it for a convex-combination
   argument (`coeffPlusGap a b 0 ≤ μ₁·coeffPlusGap a b 0 +
   μ₂·coeffPlusGap a b 0`, which collapses to `le_refl` after applying
   `μ₁ + μ₂ = 1`). The collapse mechanism is structurally distinct from
   sprint 032's because it requires the convex-weight sum identity
   `μ₁ + μ₂ = 1` rather than a single termwise comparison.

4. **First two-summability-anchor lemma on the N1 partition.** Sprint
   028 takes one summability anchor (`hSummable_ρ` at the upper
   radius) and uses sprint 012 to derive summability at the inner
   anchors. Sprint 033 takes two summability anchors (`hSummable_r`
   *and* `hSummable_ρ`), since the N1-side counterpart of sprint 012
   (`sigmaPlus_summable_of_summable_at_upper`) does **not** exist in
   the workspace — and producing it would require a separate sprint.
   This is a structurally honest cost of working on N1 vs N2: the
   workspace's existing summability-transfer machinery is N2-only.

5. **Structural completion of the convexity-vs-monotonicity matrix on
   N1.** With sprint 011 (N2 monotonicity), sprint 028 (N2 convexity),
   sprint 032 (N1 monotonicity), and sprint 033 (N1 convexity), the
   workspace has the full 2×2 matrix of paper-axiom-free
   single-partition cross-radius bounds on `sigmaZeroMinus` and
   `sigmaPlus`. Future series-level chains that need to bridge `Σ⁺` or
   `Z` across multiple radii now have all four orthogonal building
   blocks available.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V33 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form series-level
  convexity lemma on `sigmaPlus` over three radii.

Why this is **not** "the same chain" as sprint 028:

* **Different partition.** Sprint 028 operates on the N2 partition
  (`n2Pred a b k = (0 < k ∧ ‖a k‖ < ‖b k‖)`); sprint 033 operates on
  the N1 partition (`n1Pred a b k = (k = 0 ∨ ‖a k‖ ≥ ‖b k‖)`). The
  partitions are structurally distinct and the `k = 0` boundary case
  flips behaviour: trivially excluded from N2 vs. unconditionally
  included in N1.
* **Different exponent shift.** Sprint 028 uses `t ↦ t^(k-1)` (the
  `sigmaZeroMinus`-side `2k-2` exponent forces the `−1` shift);
  sprint 033 uses `t ↦ t^k` directly (the `sigmaPlus`-side `2k`
  exponent has no shift). At `k = 0`, sprint 028 implicitly uses
  `convexOn_pow 0 = convexOn_const` (since `k − 1` is `Nat`-subtracted
  to `0`); sprint 033 also reaches `convexOn_pow 0` at `k = 0` but
  through the no-shift route, and crucially the `k = 0` summand on N1
  is **non-zero** (whereas on N2 it's trivially zero).
* **Different summability shape.** Sprint 028 takes one upper-anchor
  summability premise and uses sprint 012 to derive `Summable` at `c`
  and `r`. Sprint 033 takes **two** summability premises (at lower-`r`
  and upper-`ρ`) because no `sigmaPlus_summable_of_summable_at_upper`
  exists yet. This is a different signature shape, not just a
  parameter relabeling.
* **Different conclusion direction.** Sprint 028: `Z_r ≥
  μ₁·Z_c − μ₂·Z_ρ` (a *lower* bound on `Z_r`, with one of the convex
  weights appearing with a negative sign because the algebra solves
  for `Z_r` in terms of `Z_c, Z_ρ`). Sprint 033: `Σ⁺(c) ≤
  μ₁·Σ⁺(r) + μ₂·Σ⁺(ρ)` (an *upper* bound on `Σ⁺(c)`, with both
  convex weights positive — the natural direction for the convex
  combination of `c²` between `r²` and `ρ²`). This is the more
  primitive form of the convexity inequality; sprint 028's form is a
  rearrangement.

Why this is **not** "the same chain" as sprint 032:

* **Different argument.** Sprint 032 is *monotonicity* (two-radius);
  sprint 033 is *convexity* (three-radius). The mathematical content
  is qualitatively different: monotonicity is a 1-dimensional fact
  (bigger radius → bigger sum on `coeffPlusGap`-non-negative
  partition), convexity is a 2-dimensional fact (interior radius
  bounded above by convex combination of flanking radii).
* **Different downstream application.** Sprint 032 supports
  *re-deriving* sprint 029/030/031 with `paper.eq4`'s first conjunct
  replaced. Sprint 033 supports *new* analytical chains that need to
  bridge `Σ⁺` across three radii — none of the existing workspace
  reducers do this on `Σ⁺`.
* **Different summability discipline.** Sprint 032 takes one
  summability premise at the upper anchor `s` and transfers to `r`
  via the difference `ft − fr`. Sprint 033 takes two summability
  premises at flanking anchors `r` and `ρ` and derives `c` summability
  by termwise sandwich.

Why this is **not** numerical / mechanical:

* The `k = 0` boundary case requires the convex-weight sum identity
  `μ₁ + μ₂ = 1` to reduce the termwise convex-combination inequality
  to `le_refl`. Sprint 028's `k = 0` case is trivial (both sides 0);
  sprint 032's `k = 0` case uses `le_refl` of a constant; sprint
  033's `k = 0` case requires a non-trivial collapse via
  `μ₁ + μ₂ = 1`. This is a structurally novel handling pattern.
* The two-summability-anchor signature is a structurally novel
  signature shape on the N1 side: no prior workspace lemma takes
  two `Summable` premises at distinct radii on the N1 partition.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~13 lines (sprint 028's signature is ~13
  lines; sprint 033 differs by the predicate name, exponent, and the
  added second summability premise).
* The proof body is ~150 lines — sprint 028's body (~200 lines from
  line 4047 onwards) modified with the four substitutions plus the
  `k = 0` boundary handling and the in-house summability-at-`c`
  derivation. Estimated net length similar to sprint 028's, possibly
  shorter due to the simpler exponent (no `2*k − 2 = 2*(k-1)` algebra).
* All Lean idioms used (`convexOn_pow`, `pow_le_pow_left₀`,
  `mul_le_mul_of_nonneg_left`, `Summable.of_nonneg_of_le`,
  `Summable.tsum_le_tsum`, `simpa [...]`, `change ... ≤ ...`) are
  verbatim from sprint 028's body or readily available in Mathlib.
* No new Mathlib lemma archaeology required.
* Estimate: ~150-200 lines for the new theorem. Candidate side lemmas
  ~25 lines each. Total V33 size: ≤ 250 lines.

Why this beats the alternatives I considered (ultrathink):

* **Alternative A: Branch-2 single-`Z` collapse of sprint 030 via
  sprint 011 monotonicity bridge — paper-axiom-`{eq4}`-only mirror of
  sprint 022.** This was the queueable-as-sprint-033 placeholder noted
  by sprint 032's contract. **Demoted: sprint 032's contract analysis
  itself demoted this as a "same chain" (algebraic skeleton verbatim
  from sprint 022 with sprint 030 substituted for sprint 003). Sprint
  031 already shipped the branch-1 sibling of the same shape. Adding
  the branch-2 sibling would complete the `{eq4}`-only single-`Z`
  collapse pair, but that completion is paper-axiom-trace cleanup, not
  novel analytical chain. The bulletin's priority is novel analytical
  chains.**

* **Alternative B: End-to-end branch-1 closing reducer fusing sprint
  031 with sprint 006 to give first paper-axiom-`{eq4, eq8, eq9}`-only
  `valid_of_*` reducer.** **Demoted: sprint 032's contract explicitly
  flagged this as exceeding 1-Generator-session budget (sprint 014's
  body, the natural template, is ~155 lines; the sprint-011/sprint-012
  cascade plumbing on top of sprint 030/031's two new summability
  premises adds another ~30 lines). Same demotion as in sprint 032's
  contract.**

* **Alternative C: Materialise sprint 032 downstream by re-deriving
  sprint 029's `circleGap_inner_bound_via_series_eq4_only` using
  sprints 005/027/032 to give a `paper.eq4`-conjunct-1-only version.**
  **Demoted: pure paper-axiom-trace cleanup. The conclusion is
  identical to sprint 029's (and to sprint 002's). No new analytical
  chain.**

* **Alternative D: Termwise integration of sprint 027 to give a
  series-side closed-form `diskExcess` *identity* via swap-of-sum-and-
  integral.** Genuinely novel — workspace's first `diskExcess`
  *equality*. **Demoted: requires Mathlib lemma archaeology
  (`MeasureTheory.tsum_integral_eq_integral_tsum` or
  `hasSum_integral_of_summable_norm`), flagged as high-risk by sprint
  028 *and* sprint 032 contracts. Same demotion: should be preceded
  by `Scratch/` exploration of the relevant Mathlib namespace.**

* **Alternative E (this sprint, sigmaPlus convexity):** maximises
  analytical novelty per bounded session; closes the
  convexity-vs-monotonicity matrix on N1; structurally distinct from
  all prior sprints; supports future cross-radius `Σ⁺` chains.

* **Alternative F: `Scratch/`-first numerical exploration of
  `sigmaPlus c ≤ sigmaMinus c` (the unique remaining
  non-series-derivable conjunct of `eq4`) for truncated-N series at
  the seed and nearby `c` values, to determine if the inequality is
  tight or has margin and inform a future oracle/proposal.**
  **Demoted: an exploration sprint, not a Lean-shipping sprint. The
  bulletin's working-practices section recommends `Scratch/` work
  before Lean, but a queued *sprint contract* is expected to ship a
  Lean theorem. The Generator role is wired for Lean output. Better
  to spin up a separate `Scratch/` exploration after sprint 033 lands
  rather than spending a Generator session on Python.** Could be
  queued as sprint 034 if sprint 033 closes successfully.

* **Alternative G: A series-level *strict-inequality* version of
  sprint 028 or sprint 032 — the strict variant of the existing
  monotonicity/convexity lemmas.** **Demoted: very small structural
  delta over the existing non-strict versions. Mostly mechanical.**

* **Alternative H: A series-derivation of
  `IntervalIntegrable (fun r => 2 * r * circleGap a b r) volume 0 c`
  from continuity/measurability of `circleGapSeries` on `[0, c)` plus
  uniform summability.** **Demoted: requires `MeasureTheory`-level
  continuity/integrability machinery; high archaeology risk on the
  same scale as alternative D. Should be preceded by `Scratch/`
  exploration.**

* **Alternative I: A series-side lower bound on `circleGap a b ρ` for
  `ρ ∈ (c, 1)` (annulus-side dual of sprint 025).** **Demoted:
  paper.eq8/eq9 are the integral-side identities (`liftGap`
  representation), not pointwise. A series-direct lower bound on
  `circleGap a b ρ` for `ρ > c` would touch a new analytical surface
  but the structural connection to the closing-reducer cone is
  unclear.**

* **Alternative J: Numerical push of any prior reducer at the seed
  via closed-form `paperLambda` envelope or numerical oracle.**
  **Demoted per the bulletin's de-prioritisation of numerical pushes
  against fixed reductions.**

* **Alternative K: An N1-side `sigmaPlus_summable_of_summable_at_upper`
  lemma (the dual of sprint 012's N2-side summability transfer).**
  Genuinely novel — workspace's first N1-side summability transfer.
  **Demoted: would be the *prerequisite* to a single-summability-
  anchor version of sprint 033, but on its own it's a thin lemma with
  no immediate downstream consumer. Better to ship sprint 033 with a
  two-summability-anchor signature first, then if sprint K lands as a
  follow-up, sprint 033 can be re-derived with the cleaner single-
  anchor signature. This decoupling lets sprint 033 ship without
  blocking on sprint K's mechanics.** Queueable as a separate sprint.

Compared to A–K, candidate E (this sprint, the `sigmaPlus` cross-radius
upper bound via N1 termwise convexity with explicit `k = 0` handling)
maximises **analytical novelty per bounded Generator session**: it
ships the **first paper-axiom-free convexity lemma on `sigmaPlus`**, the
**first three-radius `sigmaPlus` argument** in the workspace, the
**first lemma to handle the `k = 0 ∈ N1` boundary case in a
convex-combination context**, and **closes the convexity-vs-monotonicity
matrix on N1** so the workspace has all four building blocks for future
cross-radius series-level chains on `Σ⁺` and `Z`.

It uses **only existing trusted modules + sprint 028's proof skeleton**
— no new Mathlib lemmas, no proposal needed, no risk of Mathlib
archaeology beyond what sprint 028 already cleared.

### Note on the convex-weight sum identity

The convex weights `μ₁ := (ρ² − c²) / (ρ² − r²)` and `μ₂ := (c² − r²) /
(ρ² − r²)` satisfy `μ₁ + μ₂ = 1` (sprint 028 derives this in
`hμ_sum`). At `k = 0`, the termwise convex-combination inequality
`coeffPlusGap a b 0 ≤ μ₁·(coeffPlusGap a b 0) +
μ₂·(coeffPlusGap a b 0)` collapses via `μ₁ + μ₂ = 1` to
`coeffPlusGap a b 0 ≤ (μ₁ + μ₂)·coeffPlusGap a b 0 =
coeffPlusGap a b 0`, i.e., `le_refl _`. This collapse mechanism is
structurally distinct from sprint 032's `k = 0` handling (which uses
`le_refl` directly without a convex-weight sum identity).

### Note on the in-house summability-at-`c` derivation

Sprint 028 uses sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper`
to derive summability at `c` and `r` from the single hypothesis
`hSummable_ρ`. The N1-side counterpart `sigmaPlus_summable_of_summable_at_upper`
does **not** exist in the workspace. Producing it as a side-lemma in
sprint 033 would inflate the contract beyond a single Generator session;
the cleaner shape is to take **two** summability premises (`hSummable_r`
at the lower anchor and `hSummable_ρ` at the upper anchor) and derive
summability at `c` in-house via:

```lean
have hSummable_c :
    Summable (fun k : ℕ =>
      if PaperAxioms.n1Pred a b k then
        PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
      else 0) := by
  -- Termwise: if active, then c^(2k) ≤ μ₁·r^(2k) + μ₂·ρ^(2k)
  -- by convexity of t ↦ t^k at c² = μ₁·r² + μ₂·ρ²; multiply by
  -- coeffPlusGap a b k ≥ 0 (active branch). At k = 0, both sides equal
  -- coeffPlusGap a b 0. So fc k ≤ μ₁·fr k + μ₂·fρ k for all k.
  -- Apply Summable.of_nonneg_of_le with bound (μ₁·fr + μ₂·fρ).
  ...
```

The derivation is essentially the same termwise comparison the main
proof body uses to lift the convex-combination inequality from the
termwise level to the `tsum` level — sharing this comparison between
the summability transfer and the main `tsum_le_tsum` step keeps the
proof body manageable.

### Note on the witness at the seed

V33's `_witness_at_seed` side lemma should exhibit the new lemma's
hypothesis shape at concrete witness values
`r := c_value/2 = 1777/10000`, `c := c_value = 3554/10000`,
`ρ := (c_value + 1)/2 = 6777/10000` (so `0 ≤ r < c < ρ < 1` at the
seed). This demonstrates that the lemma is non-degenerate at the seed.

### Note on hypothesis-count and analytical structure

Sprint 028 has 4 hypothesis cells (paper-axiom-free; `hr_nonneg`,
`hr_lt_c`, `hc_lt_ρ`, `hSummable_ρ`). Sprint 033 has 5 hypothesis cells
(paper-axiom-free; `hr_nonneg`, `hr_lt_c`, `hc_lt_ρ`, `hSummable_r`,
`hSummable_ρ`). The extra hypothesis is the second summability anchor,
needed because no N1-side `sigmaPlus_summable_of_summable_at_upper`
exists yet — see the "Note on the in-house summability-at-`c`
derivation" above.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem sigmaPlus_upper_via_series_convexity
      (a b : ℕ → ℂ) {r c ρ : ℝ}
      (hr_nonneg : 0 ≤ r)
      (hr_lt_c : r < c)
      (hc_lt_ρ : c < ρ)
      (hSummable_r :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)
          else 0))
      (hSummable_ρ :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)
          else 0)) :
      PaperAxioms.sigmaPlus a b c ≤
        ((ρ ^ 2 - c ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b r +
          ((c ^ 2 - r ^ 2) / (ρ ^ 2 - r ^ 2)) * PaperAxioms.sigmaPlus a b ρ
  ```
  Estimated location: append after sprint 032's
  `sigmaPlus_monotone_of_summable` (after current line 4675 + sprint
  032's body length). Estimated ~150-200 lines including the `k = 0`
  boundary handling and the in-house summability-at-`c` derivation.

  The proof body parallels sprint 028's
  `sigmaZeroMinus_lower_via_series_convexity` body
  (`Reduction.lean:4047-`) with the four substitutions described
  above and explicit handling of the `k = 0` case in N1 (which is
  trivially excluded from N2 in sprint 028's body). The
  summability-transfer route is in-house: derive summability at `c`
  from the termwise sandwich using `Summable.of_nonneg_of_le` against
  the bound `μ₁·fr k + μ₂·fρ k`.

  Concretely, the proof skeleton (extracted from sprint 028's body
  with the four substitutions and `k = 0` handling):

  ```lean
  classical
  -- Geometric scaffolding (verbatim from sprint 028).
  have hr_lt_ρ : r < ρ := lt_trans hr_lt_c hc_lt_ρ
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hr_lt_c
  ... (squared geometric facts, weight nonneg, weight sum)
  -- Termwise convexity at the convex combination c² = μ₁·r² + μ₂·ρ².
  have h_term_convexity :
      ∀ k, fc k ≤ μ₁ * fr k + μ₂ * fρ k := by
    intro k
    by_cases hk : PaperAxioms.n1Pred a b k
    · -- Active branch: split on k = 0 vs k ≥ 1.
      by_cases hk0 : k = 0
      · -- k = 0: collapse via μ₁ + μ₂ = 1.
        subst hk0
        have : fc 0 = PaperAxioms.coeffPlusGap a b 0 := by
          simp [fc, hk]
        ...
        nlinarith [hμ_sum]
      · -- k ≥ 1: standard convexity argument on N1's positive-k portion.
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hab : ‖b k‖ ≤ ‖a k‖ := by
          rcases hk with hk0' | hab'
          · exact absurd hk0' hk0
          · linarith
        have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
          unfold PaperAxioms.coeffPlusGap
          nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), sq_nonneg (‖a k‖ + ‖b k‖)]
        -- Convexity of t ↦ t^k on Ici 0 for k ≥ 1.
        have h_convexOn := convexOn_pow k
        have h_convex_combo : μ₁ • (r ^ 2) + μ₂ • (ρ ^ 2) = c ^ 2 := ...
        have h_conv_ineq := h_convexOn.2 h_r_in h_ρ_in hμ₁_nn hμ₂_nn hμ_sum
        rw [h_convex_combo] at h_conv_ineq
        -- (s²)^k = s^(2k)
        have hpow_r : (r ^ 2) ^ k = r ^ (2 * k) := by rw [← pow_mul]
        ... (similarly for c, ρ)
        rw [hpow_r, hpow_c, hpow_ρ] at h_conv_ineq
        -- Multiply by coeffPlusGap a b k ≥ 0.
        have h_with_gap := mul_le_mul_of_nonneg_left h_conv_ineq h_gap_nn
        simp only [fr, fc, fρ, hk, if_true]
        nlinarith [h_with_gap]
    · -- Inactive branch: all three indicator branches are 0.
      simp [fr, fc, fρ, hk]
  -- In-house summability at c via termwise sandwich.
  have hSummable_c : Summable fc := by
    apply Summable.of_nonneg_of_le _ h_term_convexity
        (hSummable_r.const_smul μ₁ |>.add (hSummable_ρ.const_smul μ₂))
    intro k
    by_cases hk : PaperAxioms.n1Pred a b k
    · -- Active branch: fc k = coeffPlusGap a b k * c^(2k).
      ...
    · simp [fc, hk]
  -- Lift to tsum.
  have h_tsum_le : ∑' k, fc k ≤ ∑' k, (μ₁ * fr k + μ₂ * fρ k) :=
    hSummable_c.tsum_le_tsum h_term_convexity (...)
  ...
  ```

  The structure mirrors sprint 028's lines 4047-onwards line-by-line
  with the `k = 0` boundary case as an additional `by_cases hk0` step
  inside the active branch. The in-house summability derivation
  replaces sprint 028's invocation of sprint 012.

- `ProofRefinement/Korenblum/Candidates/V33.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V32),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V32),
  4. Adds two side lemmas
     `v33_sigmaPlus_upper_via_series_convexity_compiles` and
     `v33_sigmaPlus_upper_via_series_convexity_witness_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — five
       cells: `hr_nonneg`, `hr_lt_c`, `hc_lt_ρ`, `hSummable_r`,
       `hSummable_ρ`. Concrete witness: `r := c_value/2 = 1777/10000`,
       `c := c_value = 3554/10000`, `ρ := (c_value + 1)/2 =
       6777/10000`.
     - `_witness_at_seed` demonstrates the convex-combination geometry
       at the seed: `c² = μ₁·r² + μ₂·ρ²` for the chosen `(r, c, ρ)`
       triple, where `μ₁ := (ρ² − c²)/(ρ² − r²)` and `μ₂ := (c² −
       r²)/(ρ² − r²)`. Numerical check: `μ₁ + μ₂ = 1` evaluates true
       at the seed.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V32).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V33` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V33.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V33 ties V32 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V33.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `sigmaPlus_upper_via_series_convexity` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V33.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — the lemma is paper-axiom-free.
   Greppable check: in the body of
   `sigmaPlus_upper_via_series_convexity`, the count of `paper.eq`
   substrings is **0**. (The lemma's signature also does not include
   a `paper : Section2Assumptions ...` parameter.)
7. The proof body invokes the `n1Pred a b` partition predicate
   (greppable: count of `n1Pred` in the body of
   `sigmaPlus_upper_via_series_convexity` is ≥ 1, marking sprint 033
   as the first N1-side convexity argument in the workspace).
8. The proof body invokes `convexOn_pow` (greppable: at least one
   occurrence of `convexOn_pow` in the body), marking sprint 033 as
   the dual of sprint 028's `convexOn_pow`-based argument on N1.
9. The proof body **does not invoke**
   `sigmaZeroMinus_lower_via_series_convexity` (sprint 028) anywhere
   — the structural marker that sprint 033 is the dual N1-side
   argument, not a recasting of sprint 028's N2-side argument.
   Greppable check: count of `sigmaZeroMinus_lower_via_series_convexity`
   substrings in the body is 0.
10. The proof body **does not invoke**
    `sigmaPlus_monotone_of_summable` (sprint 032) anywhere — the
    structural marker that sprint 033 is a convexity argument
    (three-radius), not a chain through sprint 032's monotonicity
    (two-radius). Greppable check: count of
    `sigmaPlus_monotone_of_summable` substrings in the body is 0.
11. The proof body explicitly handles the `k = 0` case (greppable
    marker: at least one occurrence of `k = 0` or `Nat.pos_of_ne_zero`
    or `subst` or a `by_cases` on `k = 0` inside the body, indicating
    the structurally-novel boundary handling). This is the structural
    marker that sprint 033 contributes the new `k = 0 ∈ N1`
    boundary-case-in-convex-combination ingredient.
12. The proof body invokes `Summable.of_nonneg_of_le` or equivalent
    summability-transfer machinery to derive `Summable` at `c` from
    `Summable` at `r` and `ρ` (greppable marker: at least one
    occurrence of `Summable.of_nonneg_of_le` or `Summable.add` or
    `Summable.const_smul` in the body), confirming the in-house
    summability-at-`c` derivation route.

## Out of scope

- Edit older candidates V0–V32.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V33 is the
  same `hEq15_seed_3554` that V0–V32 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land the N1-side `sigmaPlus_summable_of_summable_at_upper` lemma
  (the dual of sprint 012's N2-side summability transfer). This is
  the prerequisite to a *single*-summability-anchor version of sprint
  033, but is out of scope here — sprint 033 ships with the
  two-summability-anchor signature. A future sprint may land the N1
  summability transfer and re-derive sprint 033 in single-anchor form.
- Land any downstream consumer of sprint 033 (e.g., a re-derivation
  of sprint 028's conclusion via the rearranged form, or a
  cross-validation that sprint 033 + sprint 028 jointly imply a
  bidirectional cross-radius identity). Sprint 033 ships only the
  new convexity lemma plus its V33 side-lemma materialisation.
- Land a series-level proof of `paper.eq4`'s second conjunct
  (`sigmaPlus c ≤ sigmaMinus c`). This remains the precise oracle
  target that sprints 032 and 033 *enable* but do not themselves
  discharge. A future planner may file a `Proposals/proposal_001_*.md`
  for this oracle if motivated.
- Materialise sprint 033 in any closing-reducer chain (i.e., do not
  re-derive any `valid_of_*` reducer using sprint 033 yet — that is
  the second-order follow-up work).
- Land the branch-2 single-`Z` `{eq4}`-only collapse of sprint 030
  (alternative A above; sprint 022 mirror). Queueable as a separate
  sprint after sprint 033 lands.
- Land any other partition-side convexity argument (e.g., a
  `t ↦ t^(k-1)` N1 variant, a strict-convexity version, or a
  cross-radius lower bound) — out of scope.

## Time budget

≤ 90 minutes runtime. (Sprint 028's body was the largest series-level
lemma to date; sprint 033's body should be similar in size, and the
in-house summability derivation adds ~30 lines beyond sprint 028's
sprint-012-based derivation.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
