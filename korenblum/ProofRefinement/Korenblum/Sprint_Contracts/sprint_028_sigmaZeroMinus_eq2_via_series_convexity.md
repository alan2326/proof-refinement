# Sprint 028: Series-level proof of `paper.eq2_sigmaZeroMinus_lower` via N2 termwise convexity of `t ↦ t^(k-1)` at `c² = μ_1·r² + μ_2·ρ²` — the workspace's **first paper-axiom-free proof of equation `(2)`** (the cross-radius `Z`-convexity bound), and the **first workspace `tsum_le_tsum` argument that consumes a Mathlib `ConvexOn` instance**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V27.lean`
**Target file**: `Candidates/V28.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem sigmaZeroMinus_lower_via_series_convexity
    (a b : ℕ → ℂ) {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt_c : r < c)
    (hc_lt_ρ : c < ρ)
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.sigmaZeroMinus a b r ≥
      ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
        ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ
```

This is the workspace's **first paper-axiom-free proof of the inequality
direction of Wang's printed equation `(2)`** — i.e.,
`paper.eq2_sigmaZeroMinus_lower`, which `Section2Assumptions` axiomatises
as a function-level inequality, is here recovered as a series-level
`tsum_le_tsum` consequence of termwise convexity of `t ↦ t^(k-1)` on
`[0, ∞)` at the convex combination `c² = μ_1·r² + μ_2·ρ²` where
`μ_1 = (ρ²-c²)/(ρ²-r²) ≥ 0`, `μ_2 = (c²-r²)/(ρ²-r²) ≥ 0`, `μ_1+μ_2 = 1`.

**No `Section2Assumptions` instance is threaded through the new lemma**;
the lemma is parameterised only by `(a, b)`, three radii `0 ≤ r < c < ρ`,
and a single summability premise on the N2-restricted summand at `ρ`.
The summability at `r` and `c` is *derived* in-house via sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` from the single-anchor
premise at `ρ` (matching sprints 011/012's series-side hygiene).

The proof chain, in order:

1. **Reformulate the target as the convexity inequality at `c²`.** The
   stated bound is equivalent (multiply by `(ρ²-c²) > 0` then rearrange)
   to
   ```
   (ρ²-c²) · Z_r + (c²-r²) · Z_ρ ≥ (ρ²-r²) · Z_c.
   ```
   Dividing by `(ρ²-r²) > 0` and naming `μ_1 = (ρ²-c²)/(ρ²-r²)`,
   `μ_2 = (c²-r²)/(ρ²-r²)`, we get the **canonical convex-combination
   form**
   ```
   μ_1 · Z_r + μ_2 · Z_ρ ≥ Z_c
   ```
   with `μ_1, μ_2 ≥ 0`, `μ_1 + μ_2 = 1`, and the convex combination
   identity `μ_1 · r² + μ_2 · ρ² = c²` (verified algebraically:
   `(ρ²-c²)·r² + (c²-r²)·ρ² = r²ρ² − r²c² + c²ρ² − r²ρ² =
   c²(ρ²-r²)`, so `(μ_1·r² + μ_2·ρ²)·(ρ²-r²) = c²(ρ²-r²)`, i.e.
   `μ_1·r² + μ_2·ρ² = c²`).

2. **Establish the termwise convexity inequality.** For each `k ≥ 1`,
   the function `t ↦ t^(k-1) : [0, ∞) → ℝ` is convex (`convexOn_pow
   (k-1)` from `Mathlib/Analysis/Convex/Mul.lean:157`). At the convex
   combination `c² = μ_1·r² + μ_2·ρ²`, the convexity definition gives
   ```
   (c²)^(k-1) ≤ μ_1 · (r²)^(k-1) + μ_2 · (ρ²)^(k-1).
   ```
   Equivalently, after rewriting `(s²)^(k-1) = s^(2k-2)` (true for
   `k ≥ 1`, where `2k - 2 ≥ 0` and the natural-number subtraction is
   well-defined), and multiplying by `coeffMinusGap a b k ≥ 0` (which
   holds on N2 because `‖a_k‖ < ‖b_k‖ ⟹ ‖a_k‖² ≤ ‖b_k‖² ⟹
   coeffMinusGap = ‖b_k‖² − ‖a_k‖² ≥ 0`):
   ```
   coeffMinusGap·c^(2k-2) ≤ μ_1 · coeffMinusGap·r^(2k-2)
                          + μ_2 · coeffMinusGap·ρ^(2k-2).
   ```
   For `k = 0`: `n2Pred a b 0 = (0 < 0 ∧ ...) = False`, so the
   indicator-restricted summand is 0 on both sides — the termwise
   inequality holds trivially as `0 ≤ 0`. (No need to reason about
   `s^(0-2) = s^(-2)` because the `n2Pred` indicator zeros out the
   k=0 contribution.)
   For `k = 1`: `(s²)^0 = 1`, the convexity inequality is
   `1 ≤ μ_1·1 + μ_2·1 = μ_1 + μ_2 = 1` (equality). Multiplying by
   `coeffMinusGap a b 1 ≥ 0` preserves equality. Holds.

3. **Lift the termwise inequality to a `tsum` inequality** via
   `tsum_le_tsum`, exactly mirroring sprint 011's body
   (`Reduction.lean:1283-1348`):
   ```
   ∑' k, (if n2Pred then coeffMinusGap·c^(2k-2) else 0)
     ≤ ∑' k, (if n2Pred then μ_1·coeffMinusGap·r^(2k-2)
                          + μ_2·coeffMinusGap·ρ^(2k-2) else 0).
   ```
   The LHS is `Z_c` by definition (`PaperAxioms.lean:74-77`).

4. **Split the RHS `tsum`** via `Summable.tsum_add` (matching sprint 027's
   pattern at `Reduction.lean:3902+`) into
   ```
   ∑' k, (if n2Pred then μ_1·coeffMinusGap·r^(2k-2) else 0)
     + ∑' k, (if n2Pred then μ_2·coeffMinusGap·ρ^(2k-2) else 0).
   ```

5. **Pull the constants `μ_1` and `μ_2` out of each `tsum`** via
   `tsum_const_mul` (or `Summable.tsum_mul_left`) to obtain
   ```
   μ_1 · Z_r + μ_2 · Z_ρ.
   ```

6. **Rearrange algebraically** (one `field_simp`/`linarith` step using
   `(ρ²-r²) > 0`, `(ρ²-c²) > 0`, and `μ_i` definitions) to recover the
   stated form `Z_r ≥ ((ρ²-r²)/(ρ²-c²))·Z_c − ((c²-r²)/(ρ²-c²))·Z_ρ`.

7. **Discharge the missing summability premises at `r` and `c`** in-house
   via sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper`
   (`Reduction.lean:1425-...`), using `0 ≤ r < c < ρ`. This is the same
   bridging pattern sprint 024 uses
   (`Reduction.lean:3625-...`).

Then ship a `Candidates/V28.lean` at the same `c = 0.3554` that
compiles, scores `≥ V27 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v28_sigmaZeroMinus_eq2_via_series_convexity_compiles` and
`v28_sigmaZeroMinus_eq2_via_series_convexity_recovers_eq2_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. The bulletin **explicitly names** as a high-value axis:

> work on the coefficient side via `sigmaPlus`/`sigmaMinus`/
> `sigmaZeroMinus` structure or the `circleGapSeries` representation
> instead of going through the integrated forms

Sprint 028 ships the workspace's **third paper-axiom-free series-level
identity/inequality on the coefficient side**, after sprint 005
(`sigmaMinus = r²·Z_r`, paper-axiom-free identity), sprint 025
(`circleGap r ≤ sigmaPlus r`, paper-axiom-free inequality, the N1-side
inequality direction of `eq3`), and sprint 027 (`circleGap r =
sigmaPlus r − r²·Z_r`, paper-axiom-free identity, the equality
direction of `eq3`). Sprint 028 closes the corresponding **`eq2` axis**:
the cross-radius lower bound on `Z_r` in terms of `Z_c` and `Z_ρ`,
recovered from termwise convexity of the underlying power series.

After sprint 028 lands, the workspace's series-derivation accumulator
on `Section2Assumptions` reads:

| Paper equation | Status | Workspace lemma |
|----------------|--------|-----------------|
| `eq2` (Z-convexity) | series-derived | sprint 028 |
| `eq3` (circleGap = Σ⁺ − r²·Z) | series-derived (equality) | sprint 027 |
| `eq3` upper bound | series-derived (≤ direction) | sprint 025 |
| `eq4` third conjunct (`Σ⁻ = c²·Z`) | series-derived | sprint 005 |
| `eq4` first conjunct (`Σ⁺ r ≤ Σ⁺ c`) | not derived | (queued for cleanup) |
| `eq4` second conjunct (`Σ⁺ c ≤ Σ⁻ c`) | **not derivable** from series | (sprint 026 contract analysis K) |
| `eq5`, `eq6` | not derived | (paper-internal cross-validation only on branch-2, sprint 022) |
| `eq8`, `eq9`, `eq10`, `eq11` | not derived | (no series-side route — these are function-level lifts) |

That is, after sprint 028, the workspace would have a **complete
series-level proof of `eq2 + eq3` and a partial series-level proof of
`eq4`** — covering 2.5 out of the 4 "`Z`/`Σ`-side" equations in
`Section2Assumptions`. This is a striking accumulation of the
"`Section2Assumptions` is not a black box" thesis.

The structural firsts:

1. **First paper-axiom-free proof of the inequality direction of
   `paper.eq2_sigmaZeroMinus_lower`.** Sprint 027 closed `eq3` (a
   pointwise *equality*); sprint 028 closes `eq2` (a *cross-radius*
   inequality involving three radii `r`, `c`, `ρ`). The *type* of
   inequality is structurally distinct: `eq3` is a single-radius
   equality on `circleGap`, `eq2` is a three-radius affine combination
   on `sigmaZeroMinus`. The proof techniques are also disjoint — sprint
   027 partitions a single `tsum` along an indicator decomposition;
   sprint 028 compares three `tsum`s under a termwise convexity
   inequality. After sprint 028 lands, the workspace has a
   **proof-shaped demonstration** that *both* `eq2` and `eq3` are
   provable from series structure alone. This mirrors the way sprint
   005 was the first "Σ⁻ = c²·Z_c"-flavored series identity (sprint
   027 was the first `circleGap`-side equality, sprint 028 is the
   first cross-radius `Z`-side inequality).

2. **First workspace `tsum_le_tsum` argument that consumes a Mathlib
   `ConvexOn` instance.** Every prior workspace `tsum_le_tsum`
   invocation (sprint 011, sprint 012, sprint 025) used a *direct
   termwise* inequality (`pow_le_pow_left₀`, summand-monotonicity).
   Sprint 028 is the first to invoke `convexOn_pow (k-1)` from
   `Mathlib/Analysis/Convex/Mul.lean:157` to extract a termwise
   convexity inequality and propagate it through the indicator-restricted
   `tsum`. Greppable check: `grep -c "convexOn_pow\|ConvexOn"` in
   `Reduction.lean` rises from 0 to ≥ 2.

3. **First workspace lemma to consume sprint 012 in a *cross-radius
   summability bridge* role between two distinct anchor radii.**
   Sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper` has been
   used five times prior (`Reduction.lean:1542, 1757, 2168, 3537,
   3625+`), but always to bridge summability *between two radii of the
   same chain* (`ρ' ∈ Icc ρ₁ ρ₂` interior to single-anchor `ρ₂`).
   Sprint 028 uses it twice in a single proof body to bridge from a
   single-anchor `ρ` premise to **two different lower anchors** `c` and
   `r` simultaneously (since `0 ≤ r < c < ρ`). This is the first usage
   pattern that exercises sprint 012's transitivity across multiple
   bridging targets in one lemma.

4. **Composition novelty: first sprint to *derive* a member of
   `Section2Assumptions` (rather than *consume* one).** Sprints 005,
   025, 027 derived paper-axiom-free identities/inequalities, but none
   of them are in `Section2Assumptions` directly:
   * Sprint 005's `sigmaMinus = r²·Z_r` is the third conjunct of `eq4`
     (an internal identity used inside the `eq4` premise, but `eq4`
     itself is the *full* tuple).
   * Sprint 025's `circleGap r ≤ sigmaPlus r` is *implied by* `eq3`
     (one-direction consequence) but is not equal to `eq3`.
   * Sprint 027's `circleGap r = sigmaPlus r − r²·Z_r` *is* `eq3` as a
     pointwise equality at a fixed `r`. **First series-derivation of
     a `Section2Assumptions` member.** Sprint 028 is the **second**:
     it derives the `eq2` member of `Section2Assumptions` as a
     pointwise-at-`(r, c, ρ)` series-level inequality.

5. **Quantitative composition: enables a brand-new `eq2 + eq3 + eq4`
   chain whose paper-axiom signature is `{eq4-second-conjunct-only}`.**
   Currently sprint 002's `circleGap_inner_bound_of_eq2_eq3_eq4`
   consumes all three of `paper.eq2`, `paper.eq3`, `paper.eq4`. After
   sprint 028 lands, that chain can be re-derived using *only* the
   `Σ⁺ c ≤ Σ⁻ c` second conjunct of `eq4` (the only piece not
   series-derivable per sprint 026's analysis K). Concretely: substitute
   sprint 027 for `eq3`, sprint 028 for `eq2`, sprint 005 for the third
   conjunct of `eq4`, leaving only `Σ⁺ c ≤ Σ⁻ c` from `paper.eq4` in the
   transitive proof body. **This would be the *first* function-level
   inner-disk bound `circleGap r ≤ A·Z_c + B·Z_ρ` whose paper-axiom
   signature is just one conjunct of one paper equation.** Queueable as
   a follow-up sprint after sprint 028 lands.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V28 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form `tsum`-level
  inequality on `sigmaZeroMinus` parameterised by three radii
  `(r, c, ρ)` with a single summability premise at the upper anchor
  `ρ`, with no integration machinery and no paper-axiom hypothesis.

Why this is **not** "the same chain" as sprint 027:

* **Different paper equation.** Sprint 027 derives `eq3`; sprint 028
  derives `eq2`. These are independent equations in
  `Section2Assumptions`.
* **Different inequality shape.** Sprint 027 is a *single-radius
  equality* on `circleGap r`. Sprint 028 is a *three-radius affine
  inequality* on `sigmaZeroMinus r` in terms of `sigmaZeroMinus c` and
  `sigmaZeroMinus ρ`.
* **Different proof techniques.** Sprint 027 uses N1/N2 indicator
  partition + `Summable.tsum_add` + `tsum_neg`. Sprint 028 uses
  termwise convexity (`convexOn_pow`) + `tsum_le_tsum` +
  `tsum_const_mul` (or `Summable.tsum_mul_left`). The Mathlib lemmas
  invoked are disjoint.
* **Different downstream consumer profile.** Sprint 027 unlocks
  `eq3`-substitution in disk-side bounds (sprint 025/026's
  follow-up roadmap). Sprint 028 unlocks `eq2`-substitution in
  *inner-disk pointwise* bounds (sprint 002's `circleGap_inner_
  bound_of_eq2_eq3_eq4` and downstream sprints 003/004/007/013/014/021
  that transitively depend on it via `paper.eq2`).

Why this is **not** "the same chain" as sprint 011's
`sigmaZeroMinus_monotone_of_summable`:

* **Different inequality type.** Sprint 011 is a *single-direction
  monotonicity* `s ≤ t → Z_s ≤ Z_t`. Sprint 028 is a *cross-radius
  affine* bound `Z_r ≥ A·Z_c − B·Z_ρ` involving three different
  radii.
* **Different termwise inequality.** Sprint 011 uses
  `pow_le_pow_left₀` (a direct termwise *monotonicity*). Sprint 028
  uses `convexOn_pow` (a termwise *convexity* at a convex combination).
* **Different role in chains.** Sprint 011 is consumed inside
  `Z`-monotonicity bridging (sprints 014, 017, 022, 023, 024).
  Sprint 028 is the *bound-generating* lemma at three radii — a
  structural *upper bound on a constant in terms of two endpoint
  values*, which `eq2` then composes via `eq3` into the inner-disk
  bound.

Why this is **not** "the same chain" as sprint 005:

* **Different LHS quantity.** Sprint 005 is on `sigmaMinus`. Sprint
  028 is on `sigmaZeroMinus`.
* **Different inequality direction.** Sprint 005 is an *equality*
  `sigmaMinus = r²·sigmaZeroMinus` at a single radius. Sprint 028
  is an *inequality* `sigmaZeroMinus r ≥ A·Z_c − B·Z_ρ` at three
  radii.
* **Different complexity.** Sprint 005 is a one-step `tsum_congr`
  argument multiplying every summand by `r²`. Sprint 028 is a
  multi-step `tsum_le_tsum` + `tsum_add` + `tsum_const_mul` argument
  using termwise convexity.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~10 lines.
* The proof body is ~80–100 lines, structurally a hybrid of sprint
  011's body (`Reduction.lean:1283-1348`, ~65 lines for the
  `tsum_le_tsum` skeleton) plus sprint 027's body (`Reduction.lean:
  3902+`, ~125 lines for the `Summable.tsum_add` partition skeleton).
  The new ingredient is ~15–25 lines: invoking `convexOn_pow (k-1).2`
  at the convex combination `c² = μ_1·r² + μ_2·ρ²`, with a side
  rewrite to handle `(s²)^(k-1) = s^(2k-2)`.
* All Lean idioms used (`tsum_le_tsum`, `Summable.tsum_add`,
  `tsum_const_mul` / `Summable.tsum_mul_left`, `Summable.indicator`,
  `pow_le_pow_left₀`, `mul_le_mul_of_nonneg_left`, `convexOn_pow`,
  `field_simp`, `linarith`, `nlinarith`, `positivity`, `by_cases`,
  `change`) are **already verified** in either sprints 011/012/025/027
  bodies or in `Mathlib/Analysis/Convex/Mul.lean:157` (for
  `convexOn_pow`).
* The convex-combination identity `(ρ²-c²)·r² + (c²-r²)·ρ² =
  c²·(ρ²-r²)` is one `ring` step; the positivity facts `(ρ²-c²) > 0`,
  `(ρ²-r²) > 0`, `μ_1 ≥ 0`, `μ_2 ≥ 0`, `μ_1+μ_2 = 1` are each one
  `nlinarith`/`field_simp` step.
* Estimate: ~110 lines for the new theorem. Candidate side lemmas
  ~15–25 lines each. Total V28 size: ≤ 110 lines.

Why this beats the alternatives I considered:

* **A: End-to-end closing reducer
  `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window` (D
  from sprint 026's contract).** Mostly mechanical re-derivation of
  sprint 014's body with sprint 026's disk-side substitution. The
  kernel inequality is identical to sprint 014's. **Demoted: low
  analytical novelty per session.** Queueable as a separate sprint
  later.

* **B: Termwise integration of sprints 025/027 to give a series-side
  closed-form `diskExcess ≤ ∑'_{n1Pred} coeffPlusGap·c^(2k+2)/(k+1)`
  (B from sprints 025/026 contracts).** Genuinely novel — would be
  the workspace's first series-level *integrated* bound. However,
  requires `MeasureTheory.tsum_integral_eq_integral_tsum`-style
  swap-of-sum-and-integral machinery. Sprints 025/026/027 all demoted
  this for "Mathlib lemma archaeology risk." **Demoted: same risk
  profile as before.** A future planner can take this with extra
  Mathlib budget.

* **C: Paper-axiom-`eq3`-free counterpart of sprint 002's
  `circleGap_inner_bound_of_eq2_eq3_eq4` via sprint 027 substitution
  (sprint 027 follow-up bullet 1).** The natural mechanical follow-up
  to sprint 027 — substitute sprint 027's equality into sprint 002's
  body, removing `paper.eq3` from the transitive trace. However, the
  paper-axiom signature would still consume `paper.eq2` and
  `paper.eq4` (two paper axioms instead of three — one-axiom
  reduction). **Demoted: marginal novelty, doesn't open a new chain
  category.** Sprint 028 is strictly more impactful: it removes
  `paper.eq2` from *all* transitive chains that consume sprint 002,
  not just one chain.

* **D: Series-level proof of `eq4`'s first conjunct `sigmaPlus r ≤
  sigmaPlus c`** (sprint 026 candidate D, sprint 027 follow-up
  cleanup). Symmetric to sprint 011 on the N1 side: termwise
  `coeffPlusGap·r^(2k) ≤ coeffPlusGap·c^(2k)` for `r ≤ c` since
  `coeffPlusGap ≥ 0` on N1. **Demoted as too thin: a one-direction
  monotonicity lemma, mirror of sprint 011.** Queueable as a
  5-minute corollary alongside a larger sprint.

* **E: Series-level proof of `eq4`'s second conjunct `sigmaPlus c
  ≤ sigmaMinus c` (sprint 026 candidate K).** Sprint 026's analysis
  showed this is **non-derivable from series structure alone** —
  comparing N1-restricted sum `∑'_{N1} coeffPlusGap·c^(2k) ≥ 0` to
  N2-restricted sum `∑'_{N2} coeffMinusGap·c^(2k) ≥ 0` requires a
  cross-set inequality not implied by the partition. **Demoted:
  not derivable from current trust surface; would require a paper
  axiom or oracle.**

* **F: Series-side closed-form *lower* bound on `diskExcess` via
  sprint 027 + integration (sprint 027 follow-up bullet 3).**
  Workspace's first lower bound on diskExcess (every prior bound
  was upper). Requires integration of `−r²·Z_r` term plus
  `sigmaPlus`-positivity. **Demoted: requires integration machinery
  + non-trivial sigmaPlus-positivity argument.** Queueable as a
  separate sprint after Scratch/ exploration.

* **G: Direct end-to-end reducer chaining sprint 028 with sprint
  027 + `eq4` second conjunct + `eq8`+`eq9` to give a one-paper-axiom
  closing reducer.** Tempting but premature — depends on sprint 028
  *and* a function-level paper-axiom-free composition of sprints
  027+028 into the inner-disk pointwise bound (currently in sprint
  002). The composition step is itself a follow-up sprint after 028,
  not in scope here. **Demoted: 028 is the prerequisite; do 028
  first.**

* **H: A series-level proof of `paper.eq2_sigmaZeroMinus_lower`
  *upper bound* counterpart `Z_r ≤ ...` (i.e., the *concavity*
  direction of `t ↦ t^(k-1)`).** `t ↦ t^(k-1)` is convex (not
  concave) for k ≥ 2 on `[0, ∞)`, so the symmetric concavity bound
  does not hold termwise. **Demoted: the inequality direction is
  fixed by convexity; only the lower bound makes sense.**

* **I: Wider three-radius series-level identities (e.g., a
  `Z_r = ...` exact formula in terms of `Z_c`, `Z_ρ`).** No exact
  closed form exists for general coefficients (the series structure
  only gives the convexity *inequality*). **Demoted as not
  algebraically true.**

* **J: A `sigmaPlus`-side analog of sprint 028 via convexity of
  `t ↦ t^k` (instead of `t ↦ t^(k-1)`).** Symmetric structural
  result on the N1 side: `sigmaPlus r ≤ A·sigmaPlus c + B·sigmaPlus ρ`
  via N1 termwise convexity at `r² = μ_1·c² + μ_2·ρ²`. However,
  this requires `r² ∈ [c², ρ²]` (so r ∈ [c, ρ]), which is the
  *opposite* radial regime from sprint 028 (which has r < c).
  Genuinely novel, but the inner-disk inequality `eq4`'s first
  conjunct already covers `sigmaPlus r ≤ sigmaPlus c` for r < c via
  termwise *monotonicity* (not convexity). **Demoted: doesn't fit
  the inner-disk regime that downstream chains use.** Queueable as
  a separate sprint exploring the annulus regime.

* **K: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted per the bulletin.**

Compared to A–K, candidate L (this sprint, the convexity-based
series-level proof of `eq2`) maximises analytical novelty per
bounded Generator session: it ships the **first paper-axiom-free
proof of `eq2`** (the only `Z`-side cross-radius inequality in
`Section2Assumptions`), the **first workspace `tsum_le_tsum` use of
`convexOn_pow`**, and the **second series-derivation of a
`Section2Assumptions` member** (after sprint 027). It uses **only
existing trusted modules + pinned Mathlib + already-verified
`Reduction.lean` patterns** mirrored from sprint 011 (`tsum_le_tsum`
+ termwise inequality skeleton) plus sprint 027 (`Summable.tsum_add`
partition pattern) plus `convexOn_pow` from
`Mathlib/Analysis/Convex/Mul.lean:157`. No proposal needed.

### Note on the convex-combination identity

The convex weights `μ_1 = (ρ²-c²)/(ρ²-r²)`, `μ_2 = (c²-r²)/(ρ²-r²)`
are both ≥ 0 because `(ρ²-c²) > 0` (from `c < ρ`),
`(c²-r²) > 0` (from `r < c`), and `(ρ²-r²) > 0` (from `r < ρ`).
Their sum is `((ρ²-c²) + (c²-r²))/(ρ²-r²) = (ρ²-r²)/(ρ²-r²) = 1`.
The convex combination identity `μ_1·r² + μ_2·ρ² = c²` follows from
```
μ_1·r² + μ_2·ρ²
  = ((ρ²-c²)·r² + (c²-r²)·ρ²)/(ρ²-r²)
  = (r²ρ² − r²c² + c²ρ² − r²ρ²)/(ρ²-r²)
  = c²(ρ²-r²)/(ρ²-r²)
  = c²,
```
which is a single `ring`/`field_simp` step in Lean given the positivity
facts.

### Note on the `(s²)^(k-1) = s^(2k-2)` rewrite

For `k ≥ 1`, `2*k - 2 ≥ 0` and the natural-number subtraction is
well-defined. We have `s^(2k-2) = s^(2(k-1)) = (s²)^(k-1)` (by
`pow_mul`). For `k = 0`, the `n2Pred` indicator zeros out the term,
so the `s^(0-2) = s^0 = 1` (natural-number truncated subtraction)
issue is bypassed entirely. The cleanest Lean handling is to **case
split on the `n2Pred` indicator first** (so the inactive branch
discharges as `0 = 0`), then in the active branch deduce `0 < k`
from `n2Pred a b k = (0 < k ∧ ...)`, then rewrite `s^(2k-2)` to
`(s²)^(k-1)` using `pow_mul` plus `Nat.two_mul_sub_one` (or
`Nat.mul_sub_one` if cleaner) — sprint 011's body uses the same
`s^(2*k-2)` form without rewriting, so we may not even need the
`(s²)^(k-1)` rewrite if `convexOn_pow` can be applied directly to
the squared exponent. **Leave the precise rewrite path flexible
inside the proof body.**

### Note on the summability bridges

`hSummable_ρ : Summable (fun k => if n2Pred then coeffMinusGap·ρ^(2k-2)
else 0)` is the single-anchor summability hypothesis. To apply
`tsum_le_tsum` we need summability of:
* the LHS summand at `c`: `Summable (fun k => if n2Pred then
  coeffMinusGap·c^(2k-2) else 0)`,
* the RHS summands at `r` and `ρ` (the `ρ` side comes from
  `hSummable_ρ` directly; the `r` side comes from sprint 012 with
  `s := r, t := ρ`),
* the c-side comes from sprint 012 with `s := c, t := ρ`.

The cleanest path is two top-level invocations of sprint 012's
`sigmaZeroMinus_summable_of_summable_at_upper` at the start of the
proof, mirroring sprint 024's pattern (`Reduction.lean:3625-...`).

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem sigmaZeroMinus_lower_via_series_convexity
      (a b : ℕ → ℂ) {r c ρ : ℝ}
      (hr_nonneg : 0 ≤ r)
      (hr_lt_c : r < c)
      (hc_lt_ρ : c < ρ)
      (hSummable_ρ :
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
          else 0)) :
      PaperAxioms.sigmaZeroMinus a b r ≥
        ((ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b c -
          ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2)) * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Estimated location: after sprint 027's
  `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
  (around line 4030). Estimated ~110 lines.

- `ProofRefinement/Korenblum/Candidates/V28.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V27),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V27),
  4. Adds two side lemmas `v28_sigmaZeroMinus_eq2_via_series_convexity_compiles`
     and `v28_sigmaZeroMinus_eq2_via_series_convexity_recovers_eq2_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — only
       four cells: non-negativity of the lower radius, strict
       ordering `r < c < ρ`, summability of the N2-indicator
       summand at the upper anchor `ρ`. Concrete witness: pick
       `r := 0`, `c := c_value`, `ρ := 1/2` (or any value in
       `(c_value, 1)`).
     - `_recovers_eq2_at_seed` demonstrates that the new lemma
       *reproduces* the conclusion of `paper.eq2_sigmaZeroMinus_lower`
       at a concrete `(r, c, ρ)` triple at the seed, without
       invoking `paper.eq2_sigmaZeroMinus_lower` in the proof body
       (the `paper` parameter appears only as a structural witness
       for the `Section2Assumptions` type signature). Concrete
       witness: same `(r, c, ρ)` triple.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V27).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V28` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V28.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V28 ties V27 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V28.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `sigmaZeroMinus_lower_via_series_convexity` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V28.lean`'s side lemmas.
6. `grep -c "convexOn_pow\|ConvexOn"` in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` is ≥ 2 (the
   structural marker that sprint 028's body invokes
   `convexOn_pow (k-1)` at least once with the result destructured
   for the convexity inequality at the convex combination).
7. The proof body of the new theorem invokes
   `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012) at
   least once at top level — the structural marker that sprint 028
   uses sprint 012 in a single-anchor multi-target bridging role.

## Out of scope

- Edit older candidates V0–V27.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V28 is the
  same `hEq15_seed_3554` that V0–V27 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land a paper-axiom-free function-level inner-disk bound (i.e.,
  the fusion of sprints 027+028 into a `circleGap`-side bound).
  That is the natural follow-up sprint *after* sprint 028 lands,
  not part of this sprint's scope.
- Land a series-level proof of any `eq4` conjunct beyond the
  already-shipped sprint 005 (`sigmaMinus = c²·Z_c`).
- Materialize sprint 028's lemma in any closing reducer (i.e., do
  not consume sprint 028 inside `valid_of_*` lemmas yet — that is
  follow-up work).
- Termwise integration / swap-of-sum-and-integral machinery
  (candidate B above).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
