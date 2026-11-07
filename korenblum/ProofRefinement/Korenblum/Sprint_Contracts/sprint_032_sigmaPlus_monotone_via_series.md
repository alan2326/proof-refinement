# Sprint 032: Series-level proof of `paper.eq4`'s first conjunct `sigmaPlus a b r ≤ sigmaPlus a b s` via N1 termwise monotonicity — the workspace's **first paper-axiom-free monotonicity lemma on `sigmaPlus`**, the **dual of sprint 011's N2-side monotonicity for `sigmaZeroMinus`**, and the **structural completion of the series-level discharge of `eq2`/`eq3`/two-of-three-conjuncts-of-`eq4`** that isolates `sigmaPlus c ≤ sigmaMinus c` as the *unique remaining non-series-derivable conjunct of `eq4`*

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V31.lean`
**Target file**: `Candidates/V32.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem sigmaPlus_monotone_of_summable
    {a b : ℕ → ℂ} {r s : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hrs : r ≤ s)
    (hSummable_s :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * s ^ (2 * k)
        else 0)) :
    PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b s
```

This is the **N1-side termwise-monotonicity dual of sprint 011's
`sigmaZeroMinus_monotone_of_summable`** (`Reduction.lean:1283-1348`).
Where sprint 011 proves the N2-restricted partial-sum monotonicity
`Z(r) ≤ Z(s)` from non-negativity of `coeffMinusGap a b k` on N2 and
monotonicity of `r ↦ r^(2k-2)`, sprint 032 proves the N1-restricted
partial-sum monotonicity `Σ⁺(r) ≤ Σ⁺(s)` from non-negativity of
`coeffPlusGap a b k` on N1 (positive-`k` portion) and monotonicity of
`r ↦ r^(2k)`, with the `k = 0` summand handled by termwise equality
(`r^0 = s^0 = 1`).

The proof body mirrors sprint 011's body line-for-line with the four
substitutions:

* `n2Pred a b k` → `n1Pred a b k`
* `coeffMinusGap a b k` → `coeffPlusGap a b k`
* `s ^ (2 * k - 2)` → `s ^ (2 * k)`
* `sigmaZeroMinus a b _` → `sigmaPlus a b _`

The only structurally new step compared to sprint 011 is the `k = 0`
sub-case in the `h_pointwise` and `h_nonneg_s` lemmas. Sprint 011's
N2-side argument has `n2Pred a b 0 = (0 < 0 ∧ _) = False`, so the
`k = 0` summand is trivially zero on both sides. Sprint 032's N1-side
argument has `n1Pred a b 0 = (0 = 0 ∨ _) = True`, so the `k = 0`
summand is `coeffPlusGap a b 0 * r^0 = coeffPlusGap a b 0` on both
sides — *not* zero, but the same on both sides regardless of `r` and `s`.
Termwise monotonicity at `k = 0` reduces to the trivial `coeffPlusGap a
b 0 ≤ coeffPlusGap a b 0` (`le_refl _`), and termwise non-negativity at
`k = 0` does **not** hold in general (`coeffPlusGap a b 0` can be
negative if `‖a 0‖ < ‖b 0‖`), so the proof skeleton must use
`Summable.tsum_le_tsum` *without* additionally invoking `Summable.of_nonneg_of_le`
to derive `Summable fr` from `Summable fs`. Instead, we transfer
summability via a different route: the difference `ft − fs` is termwise
non-negative for `k ≥ 1` (and zero at `k = 0`), so `Summable (ft − fs)`
is derivable from termwise non-negativity *of the difference*, and then
`Summable fs = Summable ft − (ft − fs)` follows from `Summable.sub`.

The cleanest formulation mirrors sprint 011 more directly by structuring
the termwise comparison as `fr k ≤ ft k` with the `k = 0` case discharged
by `le_refl` and the `k ≥ 1` case by sprint 011's `pow_le_pow_left₀ ·
hrs · (2 * k)` argument, but the summability transfer has to use
`Summable.of_nonneg_of_le` applied to the *difference* `ft - fr` (which
is termwise non-negative including at `k = 0`, since `ft 0 - fr 0 =
coeffPlusGap a b 0 - coeffPlusGap a b 0 = 0`). This mirrors sprint 011's
proof shape with one extra `Summable.add` step at the end:
`Summable fr = Summable (ft - (ft - fr))`.

Then ship a `Candidates/V32.lean` at the same `c = 0.3554` that
compiles, scores `≥ V31 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v32_sigmaPlus_monotone_via_series_compiles` and
`v32_sigmaPlus_monotone_via_series_recovers_eq4_first_conjunct_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 032 is the **first paper-axiom-free monotonicity
lemma on `sigmaPlus`**, a previously-untouched analytical surface,
and the **dual of sprint 011** on the structurally distinct N1
partition.

After sprint 032 lands, the workspace's **series-level proof status of
`Section2Assumptions`'s `eq2`/`eq3`/`eq4` cone** becomes:

| Paper fact | Series-level proof status | Workspace lemma |
|------------|---------------------------|------------------|
| `eq2_sigmaZeroMinus_lower` | **Series-derived** | sprint 028 `sigmaZeroMinus_lower_via_series_convexity` |
| `eq3_circleGap_decomposition` (equality) | **Series-derived** | sprint 027 `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` |
| `eq4_sigmaPlus_bound`, conjunct 1 (`Σ⁺ r ≤ Σ⁺ c` for `r ≤ c`) | **NEW: Series-derived** | **sprint 032 `sigmaPlus_monotone_of_summable`** |
| `eq4_sigmaPlus_bound`, conjunct 2 (`Σ⁺ c ≤ Σ⁻ c`) | **Not series-derivable** (per sprint 026 candidate K analysis) | — |
| `eq4_sigmaPlus_bound`, conjunct 3 (`Σ⁻ c = c² · Z_c`) | **Series-derived** | sprint 005 `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` |

Sprint 032 is **the lemma that makes the workspace's series-level
discharge cone for `{eq2, eq3, eq4}` complete except for the single
conjunct `Σ⁺ c ≤ Σ⁻ c`**. This is **structurally significant** for
two reasons:

1. **It isolates a precise oracle target.** After sprint 032, every
   `paper.eq2`/`paper.eq3`/`paper.eq4` invocation in the workspace can
   in principle be re-routed through {sprint 005, sprint 027, sprint
   028, sprint 032} — *except* for the single use site that needs
   `sigmaPlus c ≤ sigmaMinus c`. This pins down the *unique*
   non-series-derivable analytical fact in the entire `eq2`/`eq3`/`eq4`
   cone, which is the **clean, minimal trust expansion target** for a
   future oracle proposal or paper-internal proof. Per the bulletin's
   high-value direction #3 (oracle-backed numeric subclaims), this
   sets up the cleanest possible precise oracle subclaim: a single
   inequality `sigmaPlus c ≤ sigmaMinus c` at the seed `c = 0.3554`,
   which is a *finite-radius scalar fact* about Wang's series.

2. **It enables a fully paper-axiom-free counterpart of sprint 029.**
   Currently, sprint 029's `circleGap_inner_bound_via_series_eq4_only`
   invokes `paper.eq4_sigmaPlus_bound` to chain its three conjuncts.
   The first conjunct (`Σ⁺ r ≤ Σ⁺ c`) is sprint 032's exact conclusion;
   the third conjunct is sprint 005; only the second conjunct remains
   non-series-derivable. Once the second conjunct is provided as an
   oracle/proposal, sprint 029 (and transitively sprints 030, 031) can
   be re-routed to a fully paper-axiom-free counterpart. Sprint 032 is
   the prerequisite that opens this path.

The structural firsts:

1. **First paper-axiom-free monotonicity lemma on `sigmaPlus`.** Sprint
   011 was the workspace's first paper-axiom-free monotonicity lemma on
   `sigmaZeroMinus` (N2 partition). Sprint 032 is the **dual on the N1
   partition**, exploiting the *structurally distinct* termwise
   non-negativity of `coeffPlusGap a b k` on N1 (positive-`k` portion)
   and the trivial-equality termwise behaviour at `k = 0` (which sprint
   011 avoids because `n2Pred a b 0 = False`). The `k = 0` case
   handling is **not present in sprint 011** and is the structurally
   new ingredient sprint 032 contributes.

2. **First workspace consumer of the `n1Pred` partition for a
   monotonicity argument.** Prior workspace consumers of `n1Pred`:
   sprint 025 (`circleGap_le_sigmaPlus_via_series_split` — drop-N2),
   sprint 027 (`circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   — partition equality). Both sprint 025 and sprint 027 use `n1Pred`
   structurally to *partition* `tsum`s, not to *compare* `tsum`s
   parameterised by different scalar arguments. Sprint 032 is the
   **first** N1-side comparison/monotonicity argument.

3. **First lemma to handle the `k = 0 ∈ N1` boundary case explicitly.**
   The `k = 0` boundary case is special on N1 because `n1Pred a b 0 =
   True` always (by the `k = 0 ∨ _` shape of `n1Pred`'s definition),
   so the `k = 0` summand `coeffPlusGap a b 0 * r^0 = coeffPlusGap a b
   0` contributes to both sides of the comparison `Σ⁺ r ≤ Σ⁺ s` even
   when `‖a 0‖ < ‖b 0‖`. Termwise non-negativity of the N1-restricted
   summand fails at `k = 0` precisely when `coeffPlusGap a b 0 < 0`,
   which forces sprint 032's summability-transfer step to use a
   different route than sprint 011's `Summable.of_nonneg_of_le` on the
   summands directly — instead, summability transfers from `ft` to
   `fr` via `Summable.of_nonneg_of_le` applied to the **difference**
   `ft - fr` (which *is* termwise non-negative including at `k = 0`,
   since `ft 0 - fr 0 = 0`).

4. **Completion of the structural matrix of paper-axiom-free
   discharges of `eq2`/`eq3`/`eq4`.** Together with sprints 005, 027,
   028, sprint 032 provides series-level proofs of every conjunct of
   `eq2`, `eq3`, and `eq4` *except* `sigmaPlus c ≤ sigmaMinus c`. This
   is the **first sprint to complete a multi-conjunct paper-fact's
   series-level discharge to within a single scalar inequality**. The
   remaining gap (`Σ⁺ c ≤ Σ⁻ c`) is a *finite-information* analytical
   fact at a single radius `c`, qualitatively different from the
   *all-radii* facts that sprints 005/027/028/032 discharge — which is
   exactly the kind of fact suitable for a numerical-oracle proposal
   per `Proposals/README.md`.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V32 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form series-level
  monotonicity lemma on `sigmaPlus` over `[r, s] ⊂ [0, ∞)`.

Why this is **not** "the same chain" as sprint 011:

* **Different partition.** Sprint 011 operates on the N2 partition
  (`n2Pred a b k = (0 < k ∧ ‖a k‖ < ‖b k‖)`); sprint 032 operates on
  the N1 partition (`n1Pred a b k = (k = 0 ∨ ‖a k‖ ≥ ‖b k‖)`). The
  partitions are structurally distinct and the `k = 0` boundary case
  flips behaviour: trivially excluded from N2 vs. unconditionally
  included in N1.
* **Different exponent.** Sprint 011 compares `r^(2k-2)` (the
  `sigmaZeroMinus`-side exponent — note the `-2` shift); sprint 032
  compares `r^(2k)` (the `sigmaPlus`-side exponent). The shift means
  sprint 011's `k = 0` case has `r^(-2)`-typed exponent which Lean
  treats via `Nat` subtraction (`2*0 - 2 = 0` in `ℕ`), giving `r^0 = 1`,
  while sprint 032's `k = 0` case has `r^0 = 1` directly. The two
  proofs are not byte-for-byte identical even after the
  N2→N1/coeffMinus→coeffPlus substitution.
* **Different summability-transfer route.** Sprint 011's
  N2-side termwise non-negativity of `coeffMinusGap a b k * s^(2k-2)`
  holds at every `k ≥ 0` (trivially at `k = 0` since `n2Pred a b 0 =
  False`). Sprint 032's N1-side termwise non-negativity *fails* at
  `k = 0` when `coeffPlusGap a b 0 < 0`. Sprint 032 must use
  `Summable.of_nonneg_of_le` applied to `ft - fr` (the difference) or
  derive `Summable fr` from `Summable ft` via `Summable.sub` of the
  termwise-nonneg difference. **This is a structurally new
  summability-discipline ingredient not present in sprint 011.**

Why this is **not** "the same chain" as sprint 028:

* **Different monotonicity vs. convexity.** Sprint 028 uses *termwise
  convexity* of `t ↦ t^(k-1)` to prove a *cross-radius lower bound*
  `Z_c ≤ μ_1·Z_r + μ_2·Z_ρ` at `c² = μ_1·r² + μ_2·ρ²` (a three-radius
  argument). Sprint 032 uses *termwise monotonicity* of `t ↦ t^(2k)`
  to prove a *two-radius upper bound* `Σ⁺ r ≤ Σ⁺ s` at `0 ≤ r ≤ s` (a
  two-radius argument). The two arguments use disjoint convexity-vs-
  monotonicity properties of polynomials.
* **Different partition.** Sprint 028 operates on N2 (the
  `sigmaZeroMinus` partition); sprint 032 operates on N1 (the
  `sigmaPlus` partition).

Why this is **not** "the same chain" as sprint 027:

* **Different argument shape.** Sprint 027 proves a *partition
  equality* `circleGap = sigmaPlus − r²·Z_r` via `Summable.tsum_add` on
  the N1 ⊕ N2 split. Sprint 032 proves a *two-radius inequality*
  `Σ⁺(r) ≤ Σ⁺(s)` on the N1-restricted partial sum, with no `tsum_add`
  step.
* **Different downstream consumer profile.** Sprint 027 was used to
  re-derive sprint 002's pointwise inner-disk bound (sprint 029).
  Sprint 032 will be used (in future sprints) to re-derive sprint 029's
  invocation of `paper.eq4`'s first conjunct, completing the series-
  level discharge of the entire `eq4` cone modulo the second conjunct.

Why this is **not** numerical / mechanical:

* The `k = 0` boundary case is **structurally novel** for the
  workspace and requires a different summability-transfer route than
  sprint 011. The proof is **not** a literal substitution of sprint
  011's proof body — it requires the additional `Summable.sub`
  step that sprint 011's body avoids by exploiting `n2Pred a b 0 =
  False`.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~10 lines (sprint 011's signature is 9 lines;
  sprint 032 differs by the predicate name and exponent).
* The proof body is ~50 lines — sprint 011's body (~65 lines) modified
  with the four substitutions plus the `k = 0` handling and the
  `Summable.sub` summability-transfer step. Estimated net length
  similar to sprint 011's.
* All Lean idioms used (`pow_le_pow_left₀`, `mul_le_mul_of_nonneg_left`,
  `Summable.of_nonneg_of_le`, `Summable.sub`, `Summable.tsum_le_tsum`,
  `simpa [...]`, `change ... ≤ ...`) are verbatim from sprint 011's
  body or readily available in Mathlib.
* No new Mathlib lemma archaeology required — `Summable.sub` is in
  `Mathlib.Topology.Algebra.InfiniteSum.Basic` and takes two
  `Summable` arguments to give `Summable (fun n => f n - g n)`.
  Equivalently, `Summable.of_nonneg_of_le` works directly on the
  difference.
* Estimate: ~50 lines for the new theorem. Candidate side lemmas ~20
  lines each. Total V32 size: ≤ 100 lines.

Why this beats the alternatives I considered (ultrathink):

* **Alternative A: Branch-2 single-`Z` collapse of sprint 030 via
  sprint 011 monotonicity bridge — paper-axiom-`{eq4}`-only mirror of
  sprint 022.** Genuinely novel as a *paper-internal cross-validation*
  (first paper-axiom-`{eq4}`-only branch-2 single-`Z` disk bound, dual
  of sprint 031's branch-1 `{eq4}`-only collapse). **Demoted: a
  natural mirror of sprint 022 with sprint 030 substituted for sprint
  003. Sprint 031 is the branch-1 sibling, also a sprint-007 mirror
  with sprint 030 substituted for sprint 003. Together (031 + A) they
  form symmetric leaves of the `{eq4}`-only re-derivation cone, but
  individually each is a "same chain" criticism in the sense that the
  algebraic skeleton is verbatim from a prior workspace sprint with one
  surgical lemma swap. Sprint 032 instead opens a new *kind* of
  termwise argument (N1-side monotonicity) and pins down the precise
  remaining oracle target, satisfying the bulletin's "different
  analytical chains" criterion more sharply.** Queueable as sprint
  033 if approved.

* **Alternative B: End-to-end branch-1 closing reducer fusing sprint
  031 with sprint 006 to give first paper-axiom-`{eq4, eq8, eq9}`-only
  `valid_of_*` reducer.** Strongest candidate from a "raise `c_value`
  via cleaner reducer" perspective. **Demoted: sprint 031's contract
  explicitly puts this out of scope as exceeding the 1-Generator-session
  budget (sprint 014's body, the natural template, is ~155 lines).
  Risk: the second-order summability cascade through sprints 011/012
  that sprint 014 uses adds another ~30 lines of plumbing on top of
  sprint 030/031's two new summability premises. Marginally exceeds
  budget.** Queueable as a multi-session arc.

* **Alternative C (this sprint, sigmaPlus monotonicity):** maximises
  analytical novelty per bounded session; pins down precise oracle
  target.

* **Alternative D: Termwise integration of sprint 027 to give a
  series-side closed-form `diskExcess` *identity* (not bound) via
  swap-of-sum-and-integral.** Genuinely novel — would be the
  workspace's first `diskExcess` *equality*. **Demoted: requires
  Mathlib lemma archaeology
  (`MeasureTheory.tsum_integral_eq_integral_tsum` or
  `hasSum_integral_of_summable_norm`-style swap-of-sum-and-integral
  machinery) that sprint 028's contract analysis flagged as high-risk
  for a single Generator session. Should be preceded by `Scratch/`
  exploration of the relevant Mathlib namespace.**

* **Alternative E: Series-derive the `IntervalIntegrable (fun r => 2 *
  r * circleGap a b r) volume 0 c` premise from series structure** —
  would eliminate the dangling `hInt` hypothesis in every downstream
  consumer of sprint 003/030/031. **Demoted: requires
  `MeasureTheory`-level continuity and integrability machinery
  (continuity of `circleGapSeries` on `[0, c)` from uniform summability,
  measurability lifted under `IntervalIntegrable`). Mathlib archaeology
  risk on the same scale as alternative D. Should be preceded by
  `Scratch/` exploration.**

* **Alternative F: Numerical push of any prior reducer at the seed
  via closed-form `paperLambda` envelope or numerical oracle.**
  Requires a `Numerical_Library` wrapper and oracle registration; not
  in scope per the bulletin's de-prioritisation of numerical pushes
  against fixed reductions. **Still demoted per the bulletin.**

* **Alternative G: Paper-internal cross-validation that sprint 030's
  bound and sprint 003's bound are pointwise equal at every
  `(c, ρ, Z_c, Z_ρ)`.** **Demoted: trivial — the conclusions are
  byte-for-byte identical; no separate cross-validation lemma needed.
  V30/V31's `_recovers_*_at_seed` side lemmas already provide the
  equivalent structural fact.**

* **Alternative H: A series-level `sigmaPlus`-side analog of sprint
  028 via N1 termwise convexity.** **Demoted: convexity of
  `t ↦ t^k` on `[0, ∞)` for `k ≥ 0` would give a cross-radius lower
  bound `Σ⁺(c) ≤ μ₁·Σ⁺(r) + μ₂·Σ⁺(ρ)` at `c² = μ₁·r² + μ₂·ρ²` —
  symmetric to sprint 028 on the N1 side. *Would* be a new analytical
  chain, but its downstream consumer profile is unclear (no current
  workspace lemma uses a cross-radius lower bound on `sigmaPlus`).
  Sprint 032 is more directly load-bearing for the existing
  `paper.eq4`-elimination cone.** Queueable as a separate sprint
  if a downstream consumer materialises.

* **Alternative I: A `circleGap`-side series-level lower bound on the
  outer regime `(c, 1)` (annulus side).** **Demoted: paper.eq8/eq9
  are the integral-side identities (`liftGap` representation), not
  pointwise. A series-direct lower bound on `circleGap a b ρ` for
  `ρ > c` would touch a new analytical surface but the structural
  connection to the closing-reducer cone (which uses
  `liftGap`/`paperLambda` on the annulus side via paper.eq8/eq9) is
  unclear. Should be preceded by `Scratch/` exploration of what bound
  is actually useful.**

* **Alternative J: Fuse sprints 031 and A (branch-1 + branch-2)
  collapse of sprint 030 into a single full-window single-`Z`
  `diskExcess` upper bound `diskExcess ≤ max(branch1Coef, c⁴/2) · Z_ρ`
  with paper-axiom signature `{eq4}` only.** **Demoted: requires both
  branch-1 and branch-2 collapse arguments simultaneously, exceeds
  budget, and the `max` parameterisation is awkward — closing reducers
  prefer separate branch-restricted bounds. Queueable after both
  sprint 031 and sprint A (sprint 033) land.**

Compared to A–J, candidate C (this sprint, the `sigmaPlus` monotonicity
lemma via N1 termwise comparison with explicit `k = 0` handling)
maximises **analytical novelty per bounded Generator session**: it
ships the **first paper-axiom-free monotonicity lemma on `sigmaPlus`**,
the **first N1-side comparison argument** in the workspace, the
**first lemma to handle the `k = 0 ∈ N1` boundary case explicitly**,
and the **structural completion of the series-level discharge of
`eq2`/`eq3`/two-of-three-conjuncts-of-`eq4`** that isolates `sigmaPlus
c ≤ sigmaMinus c` as the unique remaining non-series-derivable
conjunct of the `eq2`/`eq3`/`eq4` cone — pinning down the precise
oracle target for a future trust-base expansion (per the bulletin's
high-value direction #3 and `Proposals/README.md`).

It uses **only existing trusted modules + already-shipped sprint 011's
proof skeleton** — no new Mathlib lemmas, no proposal needed, no risk
of Mathlib archaeology beyond `Summable.sub` (which is in pinned
Mathlib's `Topology/Algebra/InfiniteSum/Basic.lean` namespace).

### Note on the `k = 0` boundary case

The N1 partition unconditionally includes `k = 0` (via the `k = 0 ∨ _`
shape of `n1Pred`). At `k = 0`, the summand is `coeffPlusGap a b 0 *
r^0 = coeffPlusGap a b 0 * 1 = coeffPlusGap a b 0`, *constant* in `r`
and *not necessarily non-negative* (it can be negative if
`‖a 0‖ < ‖b 0‖`). Termwise comparison `fr 0 ≤ fs 0` reduces to
`coeffPlusGap a b 0 ≤ coeffPlusGap a b 0`, which is `le_refl _`.

The summability-transfer route in the proof body must handle this:
sprint 011's body uses `Summable.of_nonneg_of_le h_nonneg_s
h_pointwise hSummable_t` to derive `Summable fs` from `Summable ft`,
which requires `0 ≤ fs k` *for every `k`*. Sprint 032 cannot use this
route directly because `0 ≤ fr 0` does not hold in general. Instead,
sprint 032 derives `Summable fr` from `Summable ft` via the difference:
`Summable (ft - fr)` is provable from termwise non-negativity of
`ft - fr` (which holds at every `k`, including at `k = 0` where the
difference is `0`) plus summability of `ft`, and then `Summable fr =
Summable (ft - (ft - fr))` follows from `Summable.sub`.

Concretely, the proof structure is:

```lean
-- Termwise non-negativity of the difference ft - fr.
have h_diff_nonneg : ∀ k, 0 ≤ ft k - fr k := by
  intro k
  by_cases hk : PaperAxioms.n1Pred a b k
  · -- Active branch: termwise comparison.
    by_cases hk0 : k = 0
    · -- k = 0: difference is 0.
      subst hk0
      simp [fr, ft, hk]  -- both summands equal coeffPlusGap a b 0
    · -- k ≥ 1: standard pow_le_pow_left₀ argument on N1's positive-k portion.
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hab : ‖b k‖ ≤ ‖a k‖ := by
        rcases hk with hk0' | hab'
        · exact absurd hk0' hk0
        · linarith
      have h_gap_nn : 0 ≤ PaperAxioms.coeffPlusGap a b k := by
        unfold PaperAxioms.coeffPlusGap
        nlinarith [sq_nonneg (‖a k‖ - ‖b k‖), sq_nonneg (‖a k‖ + ‖b k‖)]
      have h_pow_le : r ^ (2 * k) ≤ s ^ (2 * k) :=
        pow_le_pow_left₀ hr_nonneg hrs (2 * k)
      have h_mul :
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) ≤
            PaperAxioms.coeffPlusGap a b k * s ^ (2 * k) :=
        mul_le_mul_of_nonneg_left h_pow_le h_gap_nn
      have : fr k ≤ ft k := by simpa [fr, ft, hk] using h_mul
      linarith
  · -- Inactive branch: both sides are 0, difference is 0.
    simp [fr, ft, hk]
-- Summability of fr via the difference.
have h_diff_summable : Summable (fun k => ft k - fr k) := by
  -- From hSummable_s and h_diff_nonneg: termwise nonneg, and bounded above
  -- by ft k (since fr k can be negative only at k = 0 where the difference
  -- is 0, and elsewhere fr k ≥ 0). Use Summable.of_nonneg_of_le with bound
  -- ft k - 0 = ft k since 0 ≤ ft k - fr k ≤ ft k - 0 = ft k... wait, need
  -- 0 ≤ ft k - fr k ≤ ft k? That requires fr k ≥ 0 which fails at k = 0.
  -- Alternative: ft k - fr k ≤ ft k + |fr k|, but fr is only summable if we
  -- already know what we want. Cleanest: apply Summable.of_nonneg_of_le with
  -- bound 2·|ft k|, but |ft k| is not even known summable from ft summable.
  -- Best route: structure the proof as
  --   h_pointwise : ∀ k, fr k ≤ ft k
  --   then Summable fr via Summable.of_nonneg_of_le applied to
  --     (ft k + (ft k - fr k))/2 dominating ... no, this gets ugly.
  --
  -- Simplest workable route: `Summable.indicator` on `n1Pred`
  -- partitions both fr and ft into finitely-many `k = 0` term + the
  -- rest. The k = 0 term is a constant (single-term sum, trivially
  -- summable). The k ≥ 1 portion is termwise non-negative on N1 and
  -- transfers via Summable.of_nonneg_of_le from hSummable_s.
  sorry
have h_summable_fr : Summable fr := by
  have : (fun k => ft k - (ft k - fr k)) = fr := by
    funext k; ring
  rw [← this]
  exact hSummable_s.sub h_diff_summable
-- Apply tsum monotonicity from h_pointwise (separately derived).
have h_pointwise : ∀ k, fr k ≤ ft k := by
  intro k; linarith [h_diff_nonneg k]
have h_tsum_le : ∑' k, fr k ≤ ∑' k, ft k :=
  h_summable_fr.tsum_le_tsum h_pointwise hSummable_s
change (∑' k, fr k) ≤ ∑' k, ft k
exact h_tsum_le
```

The `sorry` placeholder in the sketch above is for the Generator to
discharge — the cleanest workable route is to **partition the index
set into `{0}` ∪ `{k : ℕ | 1 ≤ k}` and handle the k=0 term separately**:

* The k=0 term contributes `coeffPlusGap a b 0` to both `fr` and `ft`,
  so `(ft - fr)` is `0` at `k = 0` — the single-term sum at `k = 0` is
  trivially summable.
* The k ≥ 1 portion of `(ft - fr)` is termwise non-negative *and*
  bounded above by the k ≥ 1 portion of `ft` (since `fr ≥ 0` on the
  k ≥ 1 portion of N1, by the standard `pow_le_pow_left₀` argument).
  Apply `Summable.of_nonneg_of_le` to transfer summability from the
  `k ≥ 1` portion of `ft` (which equals `ft − (k=0 term)`, summable as
  `Summable.sub` of `Summable ft` and a single-term summable function).

**Cleaner alternative**: prove `h_pointwise : ∀ k, fr k ≤ ft k`
*directly* without going through the difference, then transfer
summability of `fr` via the chain `0 ≤ fr k + |coeffPlusGap a b 0|`
(at `k = 0`) ≤ `ft k + |coeffPlusGap a b 0|` and apply
`Summable.of_nonneg_of_le` to the *shifted* function. This reduces
the summability transfer to a single `Summable.add_const`-style step.

The Generator should pick whichever route compiles cleanest in pinned
Mathlib. The contract requires only that the lemma's *statement* and
*conclusion* match the spec; the proof body's internal route is the
Generator's choice.

### Note on the `paper.eq4` field-projection signature

The new lemma `sigmaPlus_monotone_of_summable` has signature
`{a b : ℕ → ℂ} {r s : ℝ}` — **no `Section2Assumptions` parameter**, no
`paper.*` field projections, no `Section2Assumptions a b K c` in the
signature. This is a paper-axiom-*free* lemma, like sprints 005, 011,
012, 025, 027, 028.

### Note on the witness at the seed

V32's `_recovers_eq4_first_conjunct_at_seed` side lemma should
exhibit the new lemma's conclusion at concrete witness values
`r := c_value/2 = 0.1777` and `s := c_value = 0.3554` (so `0 ≤ r ≤
s` holds at the seed). This demonstrates that the lemma *recovers
the first conjunct of `paper.eq4_sigmaPlus_bound` at the seed* —
modulo the summability premise, which V32 takes as a hypothesis
(no further discharge required).

### Note on hypothesis-count and analytical structure

Sprint 011 has 3 hypothesis cells (paper-axiom-free; `hs_nonneg`,
`hst`, `hSummable_t`). Sprint 032 has 3 hypothesis cells (paper-axiom-
free; `hr_nonneg`, `hrs`, `hSummable_s`). Identical hypothesis count.
The structural difference is in the *proof body* (the `k = 0` boundary
case and the summability-transfer route), not in the *signature*.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem sigmaPlus_monotone_of_summable
      {a b : ℕ → ℂ} {r s : ℝ}
      (hr_nonneg : 0 ≤ r)
      (hrs : r ≤ s)
      (hSummable_s :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * s ^ (2 * k)
          else 0)) :
      PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b s
  ```
  Estimated location: append after sprint 031's
  `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`
  (after current line 4647). Estimated ~50-65 lines including the
  `k = 0` boundary handling.

  The proof body mirrors sprint 011's
  `sigmaZeroMinus_monotone_of_summable` body
  (`Reduction.lean:1283-1348`) with the four substitutions described
  above and explicit handling of the `k = 0` case in N1 (which is
  trivially excluded from N2 in sprint 011's body). The
  summability-transfer route is the Generator's choice; the
  recommended route is via the difference `ft - fr` (termwise
  non-negative including at `k = 0` where it equals `0`) plus
  `Summable.sub` to recover `Summable fr` from `Summable ft` and
  `Summable (ft - fr)`.

- `ProofRefinement/Korenblum/Candidates/V32.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V31),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V31),
  4. Adds two side lemmas
     `v32_sigmaPlus_monotone_via_series_compiles` and
     `v32_sigmaPlus_monotone_via_series_recovers_eq4_first_conjunct_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — three
       cells: `hr_nonneg`, `hrs`, `hSummable_s`. Concrete witness:
       pick `r := c_value/2 = 1777/10000` and `s := c_value =
       3554/10000` (so `0 ≤ r < s` at the seed).
     - `_recovers_eq4_first_conjunct_at_seed` demonstrates that the
       new lemma's conclusion at `r := c_value/2`, `s := c_value`
       matches the first conjunct of `paper.eq4_sigmaPlus_bound`'s
       statement at the seed (`Σ⁺(r) ≤ Σ⁺(c)`), *without* invoking
       `paper.eq4_sigmaPlus_bound` anywhere in the proof body. (The
       paper-axiom is invoked in the comment for cross-check only.)
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V31).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V32` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V32.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V32 ties V31 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V32.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `sigmaPlus_monotone_of_summable` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V32.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — the lemma is paper-axiom-free.
   Greppable check: in the body of `sigmaPlus_monotone_of_summable`,
   the count of `paper.eq` substrings is **0**. (The lemma's
   signature also does not include a `paper : Section2Assumptions ...`
   parameter.)
7. The proof body invokes the `n1Pred a b` partition predicate
   (greppable: count of `n1Pred` in the body of
   `sigmaPlus_monotone_of_summable` is ≥ 1, marking sprint 032 as the
   first N1-side monotonicity argument in the workspace).
8. The proof body **does not invoke**
   `sigmaZeroMinus_monotone_of_summable` (sprint 011) anywhere — the
   structural marker that sprint 032 is the dual N1-side argument, not
   a recasting of sprint 011's N2-side argument. Greppable check:
   count of `sigmaZeroMinus_monotone_of_summable` substrings in the
   body of `sigmaPlus_monotone_of_summable` is 0.
9. The proof body explicitly handles the `k = 0` case (greppable
   marker: at least one occurrence of `k = 0` or `Nat.pos_of_ne_zero`
   or `subst` or a `by_cases` on `k = 0` inside the body, indicating
   the structurally-novel boundary handling). This is the structural
   marker that sprint 032 contributes the new `k = 0 ∈ N1` boundary-
   case ingredient that sprint 011 does not need.

## Out of scope

- Edit older candidates V0–V31.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V32 is the
  same `hEq15_seed_3554` that V0–V31 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land a series-level proof of `paper.eq4`'s second conjunct
  (`sigmaPlus c ≤ sigmaMinus c`). This is the precise oracle target
  that sprint 032 *isolates* but does not itself discharge — per the
  sprint 026 contract candidate K analysis, this conjunct is *not*
  derivable from series structure alone and would require a paper-
  internal proof or a numerical oracle proposal. **Out of sprint 032's
  scope.** A future planner may file `Proposals/proposal_001_*.md`
  for this oracle if motivated.
- Materialise sprint 032 in any downstream chain (i.e., do not
  re-derive sprint 029, 030, or 031 with `paper.eq4`'s first conjunct
  replaced by sprint 032 yet — that is the second-order follow-up
  work). Sprint 032 ships only the new monotonicity lemma plus its
  V32 side-lemma materialisation.
- Land any other partition-side monotonicity/comparison argument
  (e.g., a strict-inequality version, a cross-radius version, an
  N1-side convexity argument like alternative H above) — out of
  scope.
- Land the branch-2 single-`Z` `{eq4}`-only collapse of sprint 030
  (alternative A above; sprint 022 mirror). Queueable as sprint 033
  after sprint 032 lands.

## Time budget

≤ 60 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
