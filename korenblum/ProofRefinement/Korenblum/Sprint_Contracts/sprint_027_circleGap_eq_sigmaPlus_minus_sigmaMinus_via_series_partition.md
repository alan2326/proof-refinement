# Sprint 027: Series-level *equality* `circleGap a b r = sigmaPlus a b r − r² · sigmaZeroMinus a b r` via N1/N2 `tsum` partition — the workspace's **first paper-axiom-free proof of the equality direction of `paper.eq3_circleGap_decomposition`**, strictly upgrading sprint 025's inequality-direction bound to the full identity, and the **first paper-internal cross-validation that `eq3` is *entirely* derivable from series structure** (not just its inequality consequence)

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V26.lean`
**Target file**: `Candidates/V27.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
    (a b : ℕ → ℂ) {r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hSummable_circleGap :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) :
    PaperAxioms.circleGap a b r =
      PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r
```

This is the workspace's **first paper-axiom-free proof of the *equality
direction* of Wang's printed equation `(3)`** — i.e.,
`paper.eq3_circleGap_decomposition` (`circleGap r = sigmaPlus r −
r² · sigmaZeroMinus r`), which `Section2Assumptions` axiomatises as a
function-level identity, is here recovered as a `tsum`-level identity
from the *definitions* of `circleGap`, `circleGapSeries`, `sigmaPlus`,
`sigmaMinus`, `sigmaZeroMinus`, `coeffPlusGap`, `coeffMinusGap`,
`n1Pred`, `n2Pred` plus sprint 005's already-shipped paper-axiom-free
identity `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. **No
`Section2Assumptions` instance is threaded through the new lemma**;
the lemma is parameterised only by `(a, b)`, `r ≥ 0`, and one
`Summable` premise on the unconditioned `circleGapSeries` summand.

The proof chain, in order:

1. **Unfold `circleGap a b r = circleGapSeries a b r`** (definitional;
   `PaperAxioms.lean:94-95`) and `circleGapSeries` to `∑' k,
   coeffPlusGap a b k · r^(2k)` (definitional; `PaperAxioms.lean:82-83`).

2. **Partition the unconditioned `tsum`** via the trivial pointwise
   identity
   ```
   coeffPlusGap a b k * r ^ (2 * k)
     = (if n1Pred a b k then coeffPlusGap a b k * r ^ (2 * k) else 0)
     + (if n2Pred a b k then coeffPlusGap a b k * r ^ (2 * k) else 0)
   ```
   (which holds termwise because `n1Pred a b k` and `n2Pred a b k`
   partition `ℕ` — exactly one of the two branches is true for each
   `k`, except both are simultaneously false only when `k = 0` and
   `‖a 0‖ < ‖b 0‖`, but `n1Pred a b 0 = (0 = 0 ∨ ‖a 0‖ ≥ ‖b 0‖) =
   True` always; and both are simultaneously true never). Apply
   `tsum_congr` plus `Summable.tsum_add` (or the lower-level
   `tsum_eq_add_tsum` / `HasSum.add` route) to split the LHS `tsum`
   into a sum of the two indicator-restricted `tsum`s.

3. **Identify the N1 piece as `sigmaPlus a b r`** by definitional
   unfold (`PaperAxioms.lean:54-57`).

4. **Identify the N2 piece as `−sigmaMinus a b r`** by pulling the
   sign through:
   ```
   ∑' k, (if n2Pred then coeffPlusGap·r^(2k) else 0)
     = ∑' k, (if n2Pred then −coeffMinusGap·r^(2k) else 0)   -- via coeffPlusGap = −coeffMinusGap on N2
     = − ∑' k, (if n2Pred then coeffMinusGap·r^(2k) else 0)   -- via tsum_neg / Summable.tsum_neg
     = − sigmaMinus a b r                                      -- definitional
   ```
   The first step is a literal arithmetic identity at the summand
   level (`coeffPlusGap a b k = ‖a k‖² − ‖b k‖² = −(‖b k‖² − ‖a k‖²)
   = −coeffMinusGap a b k`); apply `tsum_congr`. The second step
   pulls negation through `tsum` via `tsum_neg`. The third step is
   definitional (`PaperAxioms.lean:64-67`).

5. **Apply sprint 005's identity `sigmaMinus a b r = r² · sigmaZeroMinus
   a b r`** (already in `Reduction.lean:474-503`, paper-axiom-free) to
   rewrite `−sigmaMinus a b r = −r² · sigmaZeroMinus a b r`.

6. **Conclude** `circleGap a b r = sigmaPlus a b r − r² · sigmaZeroMinus
   a b r` by combining steps 3, 4, 5 via `ring` or a `linarith` chain.

This is a strict structural upgrade of sprint 025: where sprint 025
established the *inequality* `circleGap r ≤ sigmaPlus r` by *dropping*
the N2 contribution, sprint 027 establishes the full *equality* by
*identifying* the N2 contribution as `−sigmaMinus = −r² · sigmaZeroMinus`.

Then ship a `Candidates/V27.lean` at the same `c = 0.3554` that
compiles, scores `≥ V26 = 1777/5000`, and *materialises* the new
lemma in side lemmas
`v27_circleGap_eq_via_series_partition_compiles` and
`v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed`. The
sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. The bulletin **explicitly names** as a high-value axis:

> work on the coefficient side via `sigmaPlus`/`sigmaMinus`/
> `sigmaZeroMinus` structure or the `circleGapSeries` representation
> instead of going through the integrated forms

Sprint 027 ships the workspace's **first paper-axiom-free *equality*
proof** along this axis. Sprint 025 was the first *inequality*
direction (`circleGap r ≤ sigmaPlus r`); sprint 026 was the first
*integrated* application (`diskExcess ≤ c⁴ · Z_c` via sprint 025 +
`eq4`). Sprint 027 closes the equality version of sprint 025 — a
structurally distinct category of result that no prior workspace
lemma occupies.

The structural firsts:

1. **First paper-axiom-free proof of the *equality direction* of
   `paper.eq3_circleGap_decomposition`.** Sprint 025 proved only the
   inequality `circleGap r ≤ sigmaPlus r`, which on the paper-axiom
   side follows from `eq3` plus `r²·Z_r ≥ 0`. Sprint 027 proves the
   *full* equality `circleGap r = sigmaPlus r − r²·Z_r` from series
   structure alone, with **zero paper-axiom invocation** anywhere in
   the transitive proof body. After sprint 027 lands, the workspace
   has a **proof-shaped demonstration** that `eq3` is *not just
   inequality-redundant* (sprint 025) but *fully redundant* — it is
   provable as a series-level `tsum` identity. This mirrors sprint
   005's `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` which is the
   paper-axiom-free identity that sprint 025/026/027 build on, and
   sprint 022's branch-2 paper-internal cross-validation of `eq6`
   from `eq2+eq3+eq4`, but at the **fully paper-axiom-free
   `tsum`-identity level** rather than at the function-level bound
   level.

2. **Strict structural upgrade of sprint 025.** Sprint 025's bound
   `circleGap r ≤ sigmaPlus r` is the *consequence* of dropping the
   N2 contribution (which is non-positive). Sprint 027 identifies
   the N2 contribution exactly as `−r²·sigmaZeroMinus r` (which is
   non-positive iff `sigmaZeroMinus ≥ 0`, recovering sprint 025's
   inequality as a corollary). Greppable check: `grep -c
   'circleGap_le_sigmaPlus_via_series_split\|
   circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition'`
   in `Reduction.lean` should show both lemmas distinctly defined.
   A future cleanup sprint can re-derive sprint 025 as a 3-line
   corollary of sprint 027 (subtract `r²·Z_r ≥ 0` from both sides),
   collapsing the two lemmas into a chain — but that is a follow-up,
   not part of this sprint.

3. **First workspace consumer-and-extender of sprint 005's
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` identity in a
   `circleGap`-side equality.** Sprint 005's identity has been
   consumed three times: (i) sprint 005's own `circleGap_outer_lower_
   bound_of_eq8_eq9` (annulus side), (ii) sprint 022's
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` (disk
   side, via `Z`-monotonicity), (iii) sprint 015's
   `diskExcess_upper_bound_via_eq5` (disk side, via direct
   substitution into `eq5`). Sprint 027 is the **first** workspace
   lemma to use sprint 005's identity to **identify the N2-side
   `tsum` summand** as `−r² · sigmaZeroMinus r`, opening the
   `circleGapSeries`-direct *identity-form* axis that the bulletin's
   "work on the coefficient side via `sigmaPlus`/`sigmaMinus`/
   `sigmaZeroMinus` structure or the `circleGapSeries`
   representation" explicitly names.

4. **Composition novelty: sprint 005's first *identity-form*
   downstream consumer.** Sprint 005's identity has been used as a
   one-step rewrite (replace `sigmaMinus ρ` with `ρ²·Z_ρ`). Sprint
   027 uses it inside a *multi-step* `tsum` partition argument: the
   N2-side `tsum` of `coeffPlusGap·r^(2k)` is identified as
   `−sigmaMinus r` first (via `coeffPlusGap = −coeffMinusGap` plus
   `tsum_neg`), and only then the result is further rewritten via
   sprint 005's identity to `−r²·Z_r`. This is a structurally
   distinct usage pattern — sprint 005's identity participates as
   the *final* algebraic substitution after the `tsum` partition
   bookkeeping, not as the *first* substitution.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V27 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form `tsum`-level
  identity on `circleGap a b r` parameterised by a single radius
  `r ≥ 0` and a single summability premise, with no quantification
  over `(c, ρ)` and no paper-axiom hypothesis.

Why this is **not** "the same chain" as sprint 025:

* **Different statement type.** Sprint 025 is an *inequality*
  `circleGap a b r ≤ sigmaPlus a b r`. Sprint 027 is an *equality*
  `circleGap a b r = sigmaPlus a b r − r² · sigmaZeroMinus a b r`.
  An equality strictly determines an inequality (in both directions);
  the inequality determines only the upper bound. The equality
  carries strictly more structural information.
* **Different proof shape.** Sprint 025 *drops* the N2 contribution
  by a termwise non-positivity argument and applies `tsum_le_tsum`
  for an inequality conclusion. Sprint 027 *identifies* the N2
  contribution exactly via a `tsum`-partition / `tsum_add` identity
  argument and applies a sequence of `tsum_congr` / `tsum_neg`
  steps for an equality conclusion. The Mathlib lemmas invoked are
  disjoint (sprint 025: `tsum_le_tsum`, `pow_le_pow_left₀`; sprint
  027: `Summable.tsum_add` or `tsum_eq_add_tsum`, `tsum_neg`,
  `tsum_congr`).
* **Different downstream consumer profile.** Sprint 025 unlocks
  *upper bound* applications (sprint 026's
  `diskExcess_upper_bound_via_circleGapSeries_eq4_only`). Sprint 027
  unlocks *equality-substitution* applications — any future
  workspace lemma that needs to rewrite `circleGap a b r` as
  `sigmaPlus r − r²·Z_r` on the coefficient side, without invoking
  `paper.eq3`. The natural follow-up applications are: (a) a
  paper-axiom-free version of sprint 002's
  `circleGap_inner_bound_of_eq2_eq3_eq4` (which currently consumes
  `eq3`), (b) a paper-axiom-free version of sprint 013's
  `diskExcess_upper_bound_via_eq3_eq4` (which currently consumes
  `eq3`), (c) a `{eq4}`-only version of sprint 014's full-window
  closing reducer that does not even need sprint 025's inequality
  (because sprint 027 gives the full equality, allowing direct
  substitution of `circleGap r = sigmaPlus r − r²·Z_r`).

Why this is **not** "the same chain" as sprint 005's
`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`:

* **Different LHS quantity.** Sprint 005's identity is on `sigmaMinus`.
  Sprint 027's identity is on `circleGap`. The quantities live at
  different layers of the paper structure (`circleGap` is the
  function-level boundary excess; `sigmaMinus` is the N2-restricted
  coefficient sum).
* **Different complexity.** Sprint 005 is a one-step `tsum_congr`
  argument (multiply each summand by `r²`). Sprint 027 is a
  multi-step `tsum` partition argument (split via N1/N2 indicator
  decomposition, then identify each piece, then chain via sprint
  005's identity).
* **Different role.** Sprint 005's identity is the *coefficient-side*
  bridge between two N2-sigma quantities. Sprint 027 is the
  *function-side-to-coefficient-side* bridge, expressing the
  function-level `circleGap` in terms of the coefficient-level
  `sigmaPlus`/`sigmaMinus`/`sigmaZeroMinus` quantities. In Wang's
  paper this is *exactly* the content of equation `(3)`.

Why this is **not** "the same chain" as sprint 026's
`diskExcess_upper_bound_via_circleGapSeries_eq4_only`:

* **Different statement type.** Sprint 026 is an *integrated upper
  bound* on `diskExcess`. Sprint 027 is a *pointwise equality* on
  `circleGap` itself.
* **Different paper-axiom signature.** Sprint 026 consumes
  `paper.eq4_sigmaPlus_bound`. Sprint 027 consumes **zero** paper
  axioms. Sprint 027 is *strictly* more structural than sprint 026.
* **Different role.** Sprint 026 is a closed-form integrated bound
  on `diskExcess` (composable with `annulusExcess`-side bounds in
  closing reducers). Sprint 027 is a structural pointwise equality
  on `circleGap` (a foundational identity from which both upper
  and lower bounds on `circleGap` can be derived without invoking
  `paper.eq3`).

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~6 lines (identical shape to sprint 025
  modulo conclusion type — `=` instead of `≤`).
* The proof body is ~50–80 lines, structurally similar to sprint
  005's `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` body
  (`Reduction.lean:474-503`) but with a `tsum_add` partition step
  prepended and a `tsum_neg` substitution step inserted.
* The proof structure is:
  1. Unfold `circleGap = circleGapSeries`, `circleGapSeries r =
     ∑' k, coeffPlusGap·r^(2k)`, `sigmaPlus r = ∑' k, if n1Pred
     then coeffPlusGap·r^(2k) else 0`, `sigmaMinus r = ∑' k, if
     n2Pred then coeffMinusGap·r^(2k) else 0` (definitional via
     `change` or `simp only`).
  2. Establish termwise identity:
     `coeffPlusGap a b k · r^(2k) = (if n1Pred then ... else 0) +
     (if n2Pred then ... else 0)` for all `k`. Case split on
     `n1Pred a b k`:
     * `true` branch: by `n1Pred ↔ ¬n2Pred` partition fact
       (proved in sprint 025; see "Note on the partition" below
       and sprint 025's contract for the cleanest derivation),
       `n2Pred a b k = false`, so the RHS is
       `coeffPlusGap·r^(2k) + 0 = coeffPlusGap·r^(2k)` = LHS.
     * `false` branch: by partition, `n2Pred a b k = true`, so the
       RHS is `0 + coeffPlusGap·r^(2k) = coeffPlusGap·r^(2k)` = LHS.
  3. Apply `tsum_congr` to lift the termwise identity to a `tsum`
     identity:
     `∑' k, coeffPlusGap·r^(2k) = ∑' k, [(if n1Pred ...) + (if
     n2Pred ...)]`.
  4. Apply `Summable.tsum_add` (or the `tsum_add` lemma — cite
     whichever is cleanest in the pinned Mathlib) to split the RHS
     `tsum`:
     `∑' k, [(if n1Pred ...) + (if n2Pred ...)] = ∑' k, (if n1Pred
     ...) + ∑' k, (if n2Pred ...)`.
     This requires summability of each indicator-restricted summand,
     which follows from `hSummable_circleGap` via:
     - The N1 piece `if n1Pred then f else 0` is dominated termwise
       by `|f|` via the indicator structure; sprint 025's body has
       the exact pattern (`Summable.indicator` on
       `{k | n1Pred a b k}` over `f`).
     - The N2 piece similarly via `Summable.indicator` on the
       complementary set.
  5. Identify the N1-restricted `tsum` as `sigmaPlus a b r` by
     definitional unfold (`PaperAxioms.lean:54-57`).
  6. Identify the N2-restricted `tsum` as `−sigmaMinus a b r`:
     - Termwise identity: on `n2Pred a b k`, `coeffPlusGap a b k =
       ‖a k‖² − ‖b k‖² = −(‖b k‖² − ‖a k‖²) = −coeffMinusGap a b k`.
       So `(if n2Pred then coeffPlusGap·r^(2k) else 0) = −(if n2Pred
       then coeffMinusGap·r^(2k) else 0)` for all `k`.
     - Apply `tsum_congr` to lift to `tsum`:
       `∑' k, (if n2Pred then coeffPlusGap·r^(2k) else 0) = ∑' k,
       −(if n2Pred then coeffMinusGap·r^(2k) else 0)`.
     - Apply `tsum_neg` to pull `−` out of the `tsum`:
       `∑' k, −(if n2Pred then coeffMinusGap·r^(2k) else 0) = − ∑' k,
       (if n2Pred then coeffMinusGap·r^(2k) else 0)`.
     - Identify the inner `tsum` as `sigmaMinus a b r` by
       definitional unfold (`PaperAxioms.lean:64-67`).
  7. Apply sprint 005's
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b r` to rewrite
     `sigmaMinus a b r = r² · sigmaZeroMinus a b r`.
  8. Combine steps 3–7 via `linarith` or `ring` to conclude:
     `circleGap a b r = sigmaPlus a b r + (−r² · sigmaZeroMinus a b
     r) = sigmaPlus a b r − r² · sigmaZeroMinus a b r`.

* All Lean idioms used (`tsum_congr`, `Summable.tsum_add` /
  `tsum_add`, `tsum_neg`, `Summable.indicator`, `change`, `by_cases`,
  `simp`, `unfold`, `linarith`, `ring`, `exact`, `refine`) are
  **already verified at the cited line ranges** in sprint 005
  (`Reduction.lean:474-503`) plus sprint 025 (the partition fact
  and indicator-summability pattern). The summability transfer
  pattern is the same one sprint 025's body uses.
* Estimate: ~80 lines for the new theorem, dominated by the
  termwise-partition step (~20 lines), the `tsum_add` invocation
  with summability transfer (~25 lines), the N2-side sign-pulling
  (~20 lines), and the final ring chain (~15 lines). The candidate
  side lemmas are 10–25 lines each. Total V27 size: ≤ 100 lines.

Why this beats the alternatives I considered:

* **A: End-to-end closing reducer
  `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window`
  fusing sprint 026 + sprint 006 (candidate D from sprint 026's
  contract).** The natural mechanical follow-up to sprint 026 —
  copies sprint 014's body line-for-line, swapping the disk-side
  call from `diskExcess_upper_bound_via_eq3_eq4` to
  `diskExcess_upper_bound_via_circleGapSeries_eq4_only`. Strongest
  objection: this is *mostly mechanical work* on a chain whose
  kernel inequality (`c⁴ ≤ ∫ 2ρ³/Λ`) is identical to sprint 014's
  on the same admissible window — no new analytical territory, no
  new chain through `Section2Assumptions`. It would deliver one new
  closing-reducer paper-axiom signature (`{eq4, eq8, eq9}` strictly
  smaller than `{eq3, eq4, eq8, eq9}`), but the bulletin
  de-prioritises "make the numerics tighter on the same Lean
  closure" which this fits in the "same Lean closure" sense (same
  kernel inequality, same admissible window). **Demoted: high
  mechanical novelty per line, low *analytical* novelty per
  session.** Queueable as a separate sprint after 027 lands and is
  exercised; in fact, sprint 027 makes this future closing reducer
  *also* paper-axiom-eq3-free at the disk side (since sprint 026's
  body doesn't use `eq3` and sprint 006's body doesn't use `eq3`),
  so the candidate-D reducer is a natural sequence after 027.

* **B: Termwise integration of sprint 025 to give a series-side
  closed-form `diskExcess ≤ ∑'_{n1Pred} coeffPlusGap·c^(2k+2)/(k+1)`
  (candidate B from sprint 025 and sprint 026 contracts).**
  Genuinely novel — would be the workspace's first series-level
  *integrated* bound. However, requires
  `MeasureTheory.tsum_integral_eq_integral_tsum` or
  `hasSum_integral_of_summable_norm`-style swap-of-sum-and-integral
  machinery. The exact lemma signatures in the pinned Mathlib
  version may not cleanly match — sprints 025/026 both demoted this
  for "risk of consuming a Generator session on Mathlib lemma
  archaeology." **Demoted: same risk profile, still on the deferred
  queue.** A future planner can take this on as a dedicated sprint
  with extra time budget for Mathlib exploration.

* **C: A series-side proof of `paper.eq4_sigmaPlus_bound`'s second
  conjunct `sigmaPlus c ≤ sigmaMinus c` (sprint 026 candidate K).**
  Sprint 026's contract analysis showed this is **non-derivable
  from series structure** because on N1 we have `‖a_k‖ ≥ ‖b_k‖`,
  which makes `coeffPlusGap = ‖a_k‖² − ‖b_k‖² ≥ 0` on N1, and
  comparing `sigmaPlus c = ∑'_{N1} coeffPlusGap·c^(2k) ≥ 0` to
  `sigmaMinus c = ∑'_{N2} coeffMinusGap·c^(2k) ≥ 0` requires a
  cross-set inequality that does not follow from the partition
  alone. **Demoted: not derivable from current trust surface; would
  still require a paper axiom or oracle.** Sprint 026's analysis
  here is correct.

* **D: A `sigmaPlus`-monotone series-level lemma (`s ≤ t →
  sigmaPlus s ≤ sigmaPlus t`).** Symmetric to sprint 011's
  `sigmaZeroMinus_monotone_of_summable` but for the N1-restricted
  sum with `coeffPlusGap ≥ 0` on N1. Sprint 026 demoted this as
  "too thin" — the lemma is structurally one-line analogous to
  sprint 011, doesn't unlock a new chain. **Demoted: marginal
  novelty, doesn't open a new closing-reducer signature.** A future
  cleanup sprint could land this as a 5-minute lemma alongside a
  larger sprint.

* **E: A series-side `sigmaPlus`-summability transfer
  (`s ≤ t → Summable @ t → Summable @ s`) — analog of sprint 012
  for the N1-restricted sum.** Same character as D — symmetric to
  sprint 012, doesn't open a new chain. **Demoted as too thin.**

* **F: A series-level identity `coeffPlusGap a b k +
  coeffMinusGap a b k = 0 (for k > 0) ∨ ‖a 0‖² − ‖b 0‖² (for k =
  0)`.** This is the underlying arithmetic identity that sprint 027
  unfolds to in step 6's termwise identity. **Demoted: too thin —
  a one-line `unfold`+`ring` at the summand level, doesn't merit a
  full sprint.** Sprint 027 absorbs this as an inline step.

* **G: A series-side closed-form *lower* bound on `diskExcess` via
  sprint 027 + integration.** Once sprint 027 lands the equality
  `circleGap r = sigmaPlus r − r² · Z_r`, integrating against `2r`
  on `[0, c]` gives `diskExcess = ∫₀^c 2r · sigmaPlus r dr − ∫₀^c
  2r³ · Z_r dr`. The first term is ≥ 0 (since `sigmaPlus r ≥ 0` on
  N1, when `coeffPlusGap ≥ 0` on N1 — which holds termwise but
  requires the same kind of non-trivial *positivity-on-N1* argument
  that sprint 005's `sigmaZeroMinus_nonneg_of_pos` already
  discharges for N2). This is a natural follow-up after sprint 027
  but requires non-trivial integration machinery (sprint 026's
  pattern) plus a `sigmaPlus`-positivity lemma.
  **Demoted to a follow-up sprint after 027.**

* **H: A series-level upper bound on `circleGap a b r` for `r ≥ 1`
  (the analytic continuation regime).** `Section2Assumptions`
  controls only `r ∈ [0, 1)`; sprint 005's identity holds on all
  `s` since it's a `tsum_congr` argument, but the
  `circleGapSeries`-level analogous statement may not be
  meaningful for `r > 1` (geometric series may diverge).
  **Demoted: out of the relevant analytic region for the Korenblum
  problem.**

* **I: A series-level proof of `paper.eq4_sigmaPlus_bound`'s third
  conjunct `sigmaMinus c = c² · sigmaZeroMinus c` (the equality
  piece).** This is *exactly* sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`! Already in the
  workspace. Sprint 027 *consumes* this as step 5. **Demoted as
  already done.**

* **J: A series-level proof of `paper.eq2_sigmaZeroMinus_lower`.**
  `eq2` is an *inequality* lower bound on `sigmaZeroMinus r` in
  terms of `sigmaZeroMinus c` and `sigmaZeroMinus ρ`. The closed
  form is a convexity-style bound. Deriving it from series
  structure alone would require a non-trivial term-by-term
  comparison across three radii — speculatively, possible via
  `tsum_le_tsum` plus a termwise convexity argument on
  `r^(2k-2)`. However, this is significantly more delicate than
  sprint 027's `tsum_add` partition argument (no `tsum_add` /
  `tsum_neg` direct route). **Demoted: higher analytical risk,
  needs more design before going to Lean — file as a future
  candidate after `Scratch/` exploration.**

* **K: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted per the bulletin.**

* **L: Strengthen sprint 027 to an absolute summability
  hypothesis (`Summable (fun k => |coeffPlusGap a b k| · r^(2k))`)
  to make the `Summable.tsum_add` step cleaner.** Out of scope for
  *modifying* sprint 027's signature post-hoc. The contract leaves
  the precise summability-transfer path flexible inside the proof
  body — see "Note on the summability transfer" below.

Compared to A–L, candidate M (this sprint, the `tsum`-partition
identity `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`)
maximises analytical novelty per bounded Generator session: it ships
the **first paper-axiom-free *equality* proof of `paper.eq3`** (vs
sprint 025's *inequality* direction), the **strict structural
upgrade of sprint 025**, and the **first workspace `tsum`-partition
identity argument on `circleGapSeries`** (vs sprint 005's single-step
`tsum_congr` on `sigmaMinus`). It uses **only existing trusted
modules + pinned Mathlib + already-verified `Reduction.lean`
patterns** mirrored from sprint 005 (`tsum_congr` machinery) plus
sprint 025 (partition fact + indicator-summability transfer). No
proposal needed.

### Note on the partition `n1Pred ↔ ¬n2Pred`

`n1Pred a b k = (k = 0 ∨ ‖a_k‖ ≥ ‖b_k‖)` and `n2Pred a b k = (0 < k
∧ ‖a_k‖ < ‖b_k‖)`. Their negation: `¬n2Pred a b k = (k = 0 ∨
‖a_k‖ ≥ ‖b_k‖) = n1Pred a b k`. So **`n1Pred` and `n2Pred` partition
`ℕ`** — exactly one is true for each `k`. The proof of the partition
fact is sprint 025's same `push_neg` argument; copy that pattern.

The termwise sum identity `coeffPlusGap·r^(2k) = (if n1Pred then
coeffPlusGap·r^(2k) else 0) + (if n2Pred then coeffPlusGap·r^(2k)
else 0)` then follows by case split on `n1Pred a b k`:
* `true`: RHS = `coeffPlusGap·r^(2k) + 0 = LHS`.
* `false`: by partition `n2Pred = true`, RHS = `0 +
  coeffPlusGap·r^(2k) = LHS`.

### Note on the summability transfer

`hSummable_circleGap : Summable (fun k => coeffPlusGap a b k * r ^
(2 * k))` is the unconditioned summability hypothesis. To apply
`Summable.tsum_add` (or `tsum_add`) in step 4, we need summability
of each indicator-restricted summand:
* `Summable (fun k => if n1Pred a b k then coeffPlusGap a b k * r ^
  (2 * k) else 0)`,
* `Summable (fun k => if n2Pred a b k then coeffPlusGap a b k * r ^
  (2 * k) else 0)`.

The cleanest path is `Summable.indicator` on the sets `{k | n1Pred a
b k}` and `{k | n2Pred a b k}`, with the underlying summable function
being `hSummable_circleGap`. Sprint 025's body uses this exact pattern
— reference `Reduction.lean:3703-...` for the verified Mathlib lemma
sequence.

If `Summable.indicator`'s signature in the pinned Mathlib doesn't
cleanly give the `if-then-else` shape, fall back to:
* `Summable.of_nonneg_of_le` on `|if n1Pred then f else 0| ≤ |f|`
  (requires `f` absolutely summable, i.e., `Summable |f|`),
* OR `Summable.mul_left` with the indicator function multiplication
  pattern: `(if n1Pred then 1 else 0) * f k = (if n1Pred then f k
  else 0)`.

The contract leaves the precise summability-transfer path flexible
— use whatever pinned-Mathlib lemma sequence is cleanest. The
acceptance criteria check only the **conclusion** form and the
**no-paper-axiom** structural guarantee.

### Note on the `tsum_add` invocation

`Summable.tsum_add` typically has signature `Summable f → Summable
g → ∑' x, (f x + g x) = ∑' x, f x + ∑' x, g x` (or the reversed
direction). Use whichever orientation lines up with the goal after
step 3's `tsum_congr`. If the pinned Mathlib only exposes the
forward direction (`tsum_add : Summable f → Summable g → ∑' (f + g)
= ∑' f + ∑' g`), apply `(tsum_add h1 h2).symm` to flip.

### Note on the `tsum_neg` invocation

`tsum_neg` should give `∑' x, −(f x) = − ∑' x, f x` directly (over
any topological additive group; `ℝ` qualifies). If the pinned
Mathlib version requires `Summable f` for this, derive summability
of `(if n2Pred then coeffMinusGap·r^(2k) else 0)` from sprint 005's
identity (which would require some extra work) or alternatively
re-route the proof to apply `tsum_congr` *after* `tsum_neg` rather
than before — the algebra works in either order.

### Note on the witness lemmas at the seed

At the seed `c_value = 0.3554`:
* The first witness lemma `v27_circleGap_eq_via_series_partition_compiles`
  exhibits the new lemma's signature compiles at `r = c_value`,
  *without* discharging the summability premise (the latter
  remains existential / hypothesis-only since it depends on the
  abstract `(a, b)` pair). Mirror sprint 025's
  `v25_circleGap_le_sigmaPlus_compiles` shape.
* The second witness lemma
  `v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed`
  confirms the **structural fact** that sprint 027's identity at
  `r = c_value` *is* the same statement as
  `paper.eq3_circleGap_decomposition c_value` would give from a
  hypothetical `Section2Assumptions` instance — i.e., the new
  lemma's conclusion *literally matches the equality form of*
  `paper.eq3`. (Implementation: state the lemma with
  `Section2Assumptions a b K c_value` in the signature, derive
  `circleGap a b c_value = sigmaPlus a b c_value − c_value² ·
  sigmaZeroMinus a b c_value` via sprint 027 with the appropriate
  summability hypothesis, and check that this *agrees with* the
  conclusion `paper.eq3_circleGap_decomposition c_value` would
  produce. This is a structural equality at the seed — no new axiom,
  no `c_value` push.)

Either witness lemma may use sprint 027 as `=`-rewriting — they
exist purely to verify the new lemma's signature typechecks at the
seed and to demonstrate the equality form's structural agreement
with `paper.eq3`.

### Note on what the witness lemmas should NOT do

Sprint 027's V27 witness lemmas are **structural only** — they
confirm the new lemma's signature compiles at the seed `c_value`
and that the equality form is structurally aligned with `paper.eq3`.
They do **NOT** discharge the summability premise (which remains
an existential hypothesis), they do **NOT** invoke any closing
reducer, and they do **NOT** push `c_value` upward.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    matching the shape above. Place it **after** sprint 026's
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only` at the end
    of the file so the chronological narrative is preserved.

    The proof body must:

    1. **Unfold** `circleGap` and `circleGapSeries` to `tsum`s, plus
       `sigmaPlus`, `sigmaMinus` to their indicator-`tsum`s. Use
       `change` or `show` to expose the underlying `∑'` expressions.

    2. **Establish the termwise partition identity**:
       ```
       coeffPlusGap a b k * r ^ (2 * k)
         = (if n1Pred a b k then coeffPlusGap a b k * r ^ (2 * k) else 0)
         + (if n2Pred a b k then coeffPlusGap a b k * r ^ (2 * k) else 0)
       ```
       for all `k`. Case split on `n1Pred a b k`; in each branch use
       the `n1Pred ↔ ¬n2Pred` partition fact (proved inline via
       `push_neg` mirroring sprint 025's body).

    3. **Lift to `tsum`** via `tsum_congr`:
       ```
       ∑' k, coeffPlusGap a b k * r^(2k)
         = ∑' k, [(if n1Pred ...) + (if n2Pred ...)]
       ```

    4. **Split the `tsum` via `Summable.tsum_add` (or `tsum_add`)**:
       ```
       ∑' k, [(if n1Pred ...) + (if n2Pred ...)]
         = ∑' k, (if n1Pred ...) + ∑' k, (if n2Pred ...)
       ```
       Discharge the two summability premises via `Summable.indicator`
       (or the indicator-multiplication fallback) on
       `hSummable_circleGap`.

    5. **Identify the N1 piece as `sigmaPlus a b r`** by definitional
       unfold.

    6. **Identify the N2 piece as `−sigmaMinus a b r`**:
       * Termwise: `(if n2Pred then coeffPlusGap·r^(2k) else 0) =
         −(if n2Pred then coeffMinusGap·r^(2k) else 0)`. Case split
         on `n2Pred a b k`; on `true`, use `coeffPlusGap = ‖a‖² −
         ‖b‖² = −(‖b‖² − ‖a‖²) = −coeffMinusGap` (`unfold` +
         `ring`); on `false`, both sides are `0` (`if_neg`).
       * Lift via `tsum_congr`: `∑' k, (if n2Pred then
         coeffPlusGap·r^(2k) else 0) = ∑' k, −(if n2Pred then
         coeffMinusGap·r^(2k) else 0)`.
       * Pull `−` out via `tsum_neg`: `= − ∑' k, (if n2Pred then
         coeffMinusGap·r^(2k) else 0)`.
       * Unfold definitionally to `−sigmaMinus a b r`.

    7. **Apply sprint 005's
       `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b r`** to rewrite
       `−sigmaMinus a b r = −r² · sigmaZeroMinus a b r`.

    8. **Conclude** `circleGap a b r = sigmaPlus a b r − r² ·
       sigmaZeroMinus a b r` by combining steps 3–7 via `linarith`,
       `ring`, or a `calc` chain.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 027's
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    is the workspace's **first paper-axiom-free proof of the
    *equality* direction of `paper.eq3_circleGap_decomposition`**,
    a strict structural upgrade of sprint 025's *inequality*
    direction `circleGap r ≤ sigmaPlus r`, and the **first
    workspace `tsum`-partition identity argument on `circleGapSeries`**
    (vs sprint 005's single-step `tsum_congr` on `sigmaMinus`).

  * The body of the new theorem MAY invoke:

    * Definitional unfolding of `PaperAxioms.circleGap`,
      `PaperAxioms.circleGapSeries`, `PaperAxioms.sigmaPlus`,
      `PaperAxioms.sigmaMinus`, `PaperAxioms.sigmaZeroMinus`,
      `PaperAxioms.coeffPlusGap`, `PaperAxioms.coeffMinusGap`,
      `PaperAxioms.n1Pred`, `PaperAxioms.n2Pred`,
    * Sprint 005's `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (the
      *only* prior workspace lemma sprint 027 consumes — paper-axiom-
      free, see `Reduction.lean:474-503`),
    * Mathlib's `tsum_congr`, `Summable.tsum_add` (or `tsum_add`),
      `tsum_neg`, `Summable.indicator` (or the indicator-multiplication
      pattern), `pow_nonneg`, `norm_nonneg`, `Nat.pos_of_ne_zero`,
      `lt_of_not_ge`, `not_or`, `push_neg`,
    * Standard tactics: `by_cases`, `simp`, `change`, `show`, `set`,
      `intro`, `linarith`, `nlinarith`, `exact`, `refine`, `rfl`,
      `ring`, `calc`, `unfold`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that sprint 027
    operates at the **fully paper-axiom-free `tsum`-identity level**):

    * `paper.eq2_sigmaZeroMinus_lower`,
      **`paper.eq3_circleGap_decomposition`** (the structural marker
      — sprint 027 is a paper-axiom-free *re-derivation* of `eq3`,
      so it must not invoke `eq3` itself anywhere),
    * `paper.eq4_sigmaPlus_bound`, `paper.eq5_branch1_sigmaReduction`,
      `paper.eq6_branch2_sigmaReduction`, `paper.eq7_paperK_formula`,
      `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`,
      `paper.eq10_branch1_pointwise`, `paper.eq11_branch2_pointwise`,
      `paper.eq12_branch1_integrated`,
      `paper.eq13_branch2_integrated`, `paper.eq14_combined`,
      `paper.eq15_…` (no paper axiom whatsoever),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
      `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9` (no paper-internal
      derived bridge),
    * Any `valid_of_*` reducer (sprint 027 does not close the
      contract; it is a *structural identity*),
    * Any prior `diskExcess_upper_bound_*`,
      `annulusExcess_lower_bound_*`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `circleGap_le_sigmaPlus_via_series_split` (sprint 025 — sprint
      027 is a strict structural upgrade and must not depend on
      sprint 025; the proof body re-derives the relevant inequality
      machinery from scratch, so the dependency direction is
      cleanly inverted: a future cleanup sprint can re-derive
      sprint 025 *from* sprint 027, but sprint 027 must not depend
      on sprint 025),
    * `sigmaZeroMinus_nonneg_of_pos`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq5`,
      `diskExcess_upper_bound_via_eq6`,
      `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
      `diskExcess_upper_bound_via_circleGapSeries_eq4_only`
      (sprint 027 must close on its own from series structure +
      sprint 005's identity alone),
    * `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`, `branch1SigmaKernel`,
      `branch1PointwiseFactor`, `branch2SigmaKernel`,
      `branch2PointwiseFactor`,
      `mass_mul_le_annulusSlice_of_integral_bound_ae`,
      `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
      `WangPaperSideConditions.paperLambda_pos`,
      `WangOuter.paperLambda` (the entire paper-`Λ` machinery is
      irrelevant to a series-side identity),
    * `Section2Assumptions`, `Section2Objects`, `paper.circleGap`,
      `paper.sigmaPlus`, `paper.sigmaMinus`, `paper.sigmaZeroMinus`,
      `paper.liftGap` (the lemma takes only `(a, b, r)` and a
      summability premise; no `Section2Assumptions` instance is
      threaded through),
    * `intervalIntegral.*`, `MeasureTheory.*`,
      `IntervalIntegrable.*` (sprint 027 is a pointwise *equality*,
      no integration anywhere).

    (Note: `PaperAxioms.circleGap`, `PaperAxioms.circleGapSeries`,
    `PaperAxioms.sigmaPlus`, `PaperAxioms.sigmaMinus`,
    `PaperAxioms.sigmaZeroMinus`, `PaperAxioms.coeffPlusGap`,
    `PaperAxioms.coeffMinusGap`, `PaperAxioms.n1Pred`,
    `PaperAxioms.n2Pred` are EXEMPT and ARE consumed via definitional
    unfolding only. `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` is
    EXEMPT and IS the only workspace lemma consumed.)

  * The new theorem's signature MUST take *exactly* the parameters
    in the goal block above: explicit `(a b : ℕ → ℂ)`, implicit
    `{r : ℝ}`, explicit `(hr_nonneg : 0 ≤ r)`, explicit
    `(hSummable_circleGap : Summable (fun k => coeffPlusGap a b k *
    r ^ (2 * k)))`. The conclusion MUST be exactly
    `PaperAxioms.circleGap a b r = PaperAxioms.sigmaPlus a b r −
    r ^ 2 * PaperAxioms.sigmaZeroMinus a b r`.

* `ProofRefinement/Korenblum/Candidates/V27.lean`:

  * `-- @parent V26`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V26).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V26).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new lemma's signature compiles at the seed `r = c_value`:

    ```lean
    theorem v27_circleGap_eq_via_series_partition_compiles
        (a b : ℕ → ℂ)
        (hSummable :
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
        PaperAxioms.circleGap a b c_value =
          PaperAxioms.sigmaPlus a b c_value -
            c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value :=
      circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
        a b c_value_pos.le hSummable
    ```

  * Additionally, prove a structural side lemma confirming that
    sprint 027's identity at `r = c_value` agrees with what
    `paper.eq3_circleGap_decomposition` would produce from a
    `Section2Assumptions` instance:

    ```lean
    theorem v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed
        (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
        (paper : Section2Assumptions a b K c_value)
        (hSummable :
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
        PaperAxioms.circleGap a b c_value =
          PaperAxioms.sigmaPlus a b c_value -
            c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value := by
      -- Sprint 027's identity gives the conclusion directly,
      -- without invoking `paper.eq3_circleGap_decomposition`.
      exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
        a b c_value_pos.le hSummable
    ```

    The body of this side lemma must NOT invoke
    `paper.eq3_circleGap_decomposition` — the *whole point* is that
    sprint 027 reproduces `eq3`'s conclusion without invoking it.
    The `paper` parameter is present only as a structural witness
    that the equality's *type* matches what `eq3` would produce; the
    actual proof goes through sprint 027 alone.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom `hEq15_seed_3554`. They exist purely to verify the
    new lemma's signature typechecks at the seed `c_value` and to
    demonstrate the equality form's structural agreement with
    `paper.eq3`.

* `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_027 queued: ...` line (after the blank-line separator
  following the sprint_026 PASS line). Once V27 lands and the
  evaluator passes, append the corresponding `sprint_027 PASS:
  ...` line.

* `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting:
  * the new `tsum`-partition equality identity for `circleGap a b r
    = sigmaPlus r − r² · sigmaZeroMinus r`;
  * the strict structural upgrade over sprint 025 (equality vs
    inequality direction);
  * sprint 005's first `circleGap`-side identity-form downstream
    consumer pattern;
  * the natural follow-up roadmap:
    - **Candidate D-revisited from sprint 026's contract** — an
      end-to-end closing reducer
      `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window`
      that fuses sprint 026 with sprint 006's `(8)+(9)`-derived
      annulus bound, achieving paper-axiom signature `{eq4, eq8,
      eq9}` strictly smaller than sprint 014's `{eq3, eq4, eq8,
      eq9}`. Sprint 027 doesn't change this candidate's analysis but
      makes the *transitive trace* even cleaner (sprint 026's body
      doesn't use `eq3`, sprint 006's body doesn't use `eq3`, so
      the closing reducer's transitive paper-axiom set excludes
      `eq3`).
    - **Paper-axiom-`eq3`-free counterparts of sprint 002 / sprint
      013** — by *substituting* sprint 027's equality directly for
      `paper.eq3_circleGap_decomposition` invocations in sprints
      002 and 013, derive paper-axiom-free function-level versions
      `circleGap_inner_bound_via_series_partition_eq2_eq4` and
      `diskExcess_upper_bound_via_series_partition_eq4_only_v2`
      (the latter algebraically identical to sprint 026 but derived
      via the equality-substitution route rather than the
      inequality-drop route).
    - **Series-side closed-form lower bound on `diskExcess`**
      (candidate G above) — once sprint 027's equality lands,
      integrating against `2r` over `[0, c]` gives `diskExcess =
      ∫₀^c 2r·sigmaPlus r dr − ∫₀^c 2r³·Z_r dr`, the workspace's
      first series-level *exact* (not bound) identity for
      `diskExcess` modulo `sigmaPlus`-positivity.
    - **Termwise integration of sprint 025/027** (candidate B from
      sprint 025/026 contracts) — the workspace's first series-level
      *integrated* bound. Still queueable as a separate sprint with
      Mathlib lemma archaeology budget for
      `tsum_integral_eq_integral_tsum`.
    - **Series-side proof of `paper.eq2_sigmaZeroMinus_lower`**
      (candidate J above) — extend sprint 027's `tsum`-partition
      methodology to a three-radius termwise convexity argument.
      Higher analytical risk; needs `Scratch/` exploration first
      per the bulletin's "have direction and evidence before going
      to Lean" rule.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V26.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_026`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V27.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V27.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V27 scores `≥`
   V26 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V27.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the
   build emits them) — no new free-floating axioms.
5. `grep -n 'circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition
   contains:
   * at least one direct invocation of `tsum_congr` (the structural
     marker that sprint 027 operates via termwise-equality `tsum`
     manipulation),
   * at least one direct invocation of `tsum_add` or
     `Summable.tsum_add` (the structural marker that sprint 027
     splits the unconditioned `tsum` into N1- and N2-restricted
     pieces),
   * at least one direct invocation of `tsum_neg` (the structural
     marker that sprint 027 pulls `−` out of the N2-restricted
     `tsum`),
   * at least one direct invocation of
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (the structural
     marker that sprint 027 consumes sprint 005's identity in step
     7),
   * **no direct reference** to any `paper.eq{2..15}_…` field
     projection (especially **no reference** to
     `paper.eq3_circleGap_decomposition`),
   * **no reference** to `circleGap_le_sigmaPlus_via_series_split`
     (sprint 025 — sprint 027 must not depend on sprint 025),
   * **no reference** to any `valid_of_*` reducer,
   * **no reference** to any `diskExcess_upper_bound_*`,
     `annulusExcess_lower_bound_*`,
     `circleGap_inner_bound_of_eq2_eq3_eq4`,
     `circleGap_outer_lower_bound_of_eq8_eq9`,
   * **no reference** to `sigmaZeroMinus_nonneg_of_pos`,
     `sigmaZeroMinus_monotone_of_summable`,
     `sigmaZeroMinus_summable_of_summable_at_upper`,
     `diskExcess_upper_bound_via_eq3_eq4`,
     `diskExcess_upper_bound_via_eq5`,
     `diskExcess_upper_bound_via_eq6`,
     `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
     `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
     `diskExcess_upper_bound_via_circleGapSeries_eq4_only`,
   * **no reference** to `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
     `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9`,
   * **no reference** to `Section2Assumptions`, `Section2Objects`,
     `WangOuter.paperLambda`, `WangPaperSideConditions.paperLambda_pos`,
   * **no reference** to `intervalIntegral.*`, `IntervalIntegrable`,
     `MeasureTheory.volume`, `∫`,
   * **no reference** to `branchSplit`, `branch1SigmaKernel`,
     `branch1PointwiseFactor`, `branch2SigmaKernel`,
     `branch2PointwiseFactor`, `Korenblum.scalarCriterion`,
     `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
     `mass_mul_le_annulusSlice_of_integral_bound_ae`,
     `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`.
6. `grep -n 'v27_circleGap_eq_via_series_partition_compiles\|v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V27.lean`
   returns at least two distinct matches.
7. The conclusion of
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   is exactly
   `PaperAxioms.circleGap a b r = PaperAxioms.sigmaPlus a b r - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r`
   (verify via `grep` of the theorem statement). Note: the
   conclusion is an **equality** `=`, not an inequality `≤` (this
   distinguishes sprint 027 from sprint 025).
8. The signature of
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   contains:
   * the explicit parameters `(a b : ℕ → ℂ)` (verify via `grep`),
   * the implicit parameter `{r : ℝ}` (verify via `grep`),
   * the hypothesis `0 ≤ r` (verify via `grep`),
   * the hypothesis `Summable (fun k : ℕ => PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))`
     (verify via `grep` for `Summable` and `coeffPlusGap`),
   * **no `Section2Assumptions` instance parameter** (verify via
     `grep` — the new lemma's signature does NOT take `paper :
     Section2Assumptions a b K c`),
   * **no implicit `K`, `c` parameters** (verify via `grep` — the
     lemma is parameterised only by `(a, b, r)` and the summability
     premise, exactly mirroring sprint 025's signature shape).
9. The body of `v27_circleGap_eq_via_series_partition_recovers_eq3_at_seed`
   exhibits the equality form
   `circleGap a b c_value = sigmaPlus a b c_value − c_value² ·
   sigmaZeroMinus a b c_value` and discharges *only* via
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   (no invocation of `paper.eq3_circleGap_decomposition` allowed,
   verify via `grep` of the body).
10. **Structural marker — `tsum`-partition argument shipped**:
    `grep -c 'tsum_congr\|tsum_add\|tsum_neg' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
    returns a value strictly greater than the same `grep -c` count
    on the parent commit (V26) — confirming sprint 027 introduces
    new direct invocations of the `tsum`-partition Mathlib machinery.
11. **Paper-axiom-free transitive guarantee**: the new lemma
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    does NOT depend on any `paper.eq{2..15}_…` field (verify via
    `#print axioms` style inspection or by confirming that the
    lemma compiles WITHOUT any `Section2Assumptions` instance in
    its signature — which acceptance criterion 8 enforces). The
    *only* workspace lemma in its transitive closure is sprint 005's
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, itself paper-axiom-
    free.
12. **Equality-form structural guarantee**: sprint 027's conclusion
    is an equality `=`, not an inequality `≤`. Verify via `grep` of
    the theorem statement that the conclusion contains `=` and not
    `≤`. This distinguishes sprint 027 from sprint 025 and is the
    structural marker that sprint 027 is a *strict structural
    upgrade* of sprint 025.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V26.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building any new closing reducer for `ValidKorenblumBound c` —
  sprint 027 is a structural identity only, not a closing reducer.
  The natural follow-up `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window`
  (candidate A above, also candidate D from sprint 026's contract)
  is queueable as a separate sprint after 027.
* Re-deriving sprint 025
  (`circleGap_le_sigmaPlus_via_series_split`) as a corollary of
  sprint 027 (which would be a 3-line `linarith` consequence
  modulo `sigmaZeroMinus ≥ 0` from sprint 005's
  `sigmaZeroMinus_nonneg_of_pos`). Queueable as a separate cleanup
  sprint after 027 — sprint 027 leaves sprint 025 in place as an
  independent lemma with its own proof body.
* Building paper-axiom-`eq3`-free counterparts of sprints 002 and
  013 (substituting sprint 027's equality for
  `paper.eq3_circleGap_decomposition` in their bodies). Queueable
  as separate sprints after 027 lands.
* Building the termwise-integrated series-side bound `diskExcess
  ≤ ∑'_{n1Pred} coeffPlusGap·c^(2k+2)/(k+1)` (candidate B above —
  requires `tsum_integral_eq_integral_tsum`-style swap-of-sum-and-
  integral machinery; queueable as a separate sprint).
* Building a series-side proof of `paper.eq2_sigmaZeroMinus_lower`
  (candidate J above — requires three-radius termwise convexity
  argument; needs `Scratch/` exploration first).
* Building a `sigmaPlus`-monotone series-level lemma (candidate D
  above — too thin).
* Discharging the summability hypothesis for any concrete `(a, b)`
  pair at the seed `c_value` numerically.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new lemma. Sprint 027 alone is **not** a
  closing reducer — it is a structural identity. Closing requires
  composition with downstream lemmas (e.g., the integrated forms
  in the deferred follow-up sprints).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against
  the current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 027 is purely
  structural.
* Modifying any prior `Reduction.lean` lemma (sprints 001–026 are
  consumed only by their existing call sites; sprint 027 adds a
  new lemma in isolation, with sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` invoked as a *consumer*
  but not modified).

## Time budget

≤ 30 minutes runtime. The new lemma is ~80 lines of Lean (~6 lines
for the signature, ~70 lines for the proof body modeled on sprint
005's `tsum_congr` body plus sprint 025's partition-and-indicator
machinery, ~5 lines for the doc comment). The candidate side lemmas
are 10–25 lines each. Total V27 size: ≤ 100 lines. All tactics used
are *already verified* in sprint 005 (`Reduction.lean:474-503` for
the `tsum_congr` machinery) plus sprint 025 (the partition fact
and indicator-summability transfer pattern).

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `Summable.tsum_add` call requires summability of *each* of the
  two indicator-restricted summands, but the natural premise
  `hSummable_circleGap` is summability of the *unconditioned*
  summand. Sprint 025's body has the working pattern for
  `Summable.indicator` derivation; copy that pattern. If the pinned
  Mathlib's `Summable.indicator` doesn't directly produce the
  `if-then-else` shape, fall back to the indicator-multiplication
  pattern: `(if n1Pred then 1 else 0) * f k = (if n1Pred then f k
  else 0)` and use `Summable.mul_left`-style. As a last resort,
  strengthen the contract's summability hypothesis to absolute
  summability `Summable (fun k => |coeffPlusGap a b k| * r^(2k))`
  if and only if it is the *only* path that compiles — but this
  weakens the lemma's downstream usability, so prefer the
  indicator approach first.
* The `tsum_neg` call requires summability of the negated summand —
  use `Summable.indicator` on the N2 set first to establish
  summability of `(if n2Pred then coeffMinusGap·r^(2k) else 0)`,
  then apply `tsum_neg` after the `tsum_congr` step. The
  alternative ordering (`tsum_neg` first, then `tsum_congr`) may
  also work if `tsum_neg` doesn't require summability in the pinned
  Mathlib version.
* The partition fact `n1Pred ↔ ¬n2Pred` step fails — fall back to
  copying sprint 025's body verbatim for the partition derivation
  (sprint 025's body is in `Reduction.lean:3703-...`). The exact
  Lean syntax may need adjustment based on the precise definitions
  of `n1Pred`/`n2Pred` in `KorenblumPaper.PaperAxioms` (lines
  33-39).
* The termwise identity `coeffPlusGap = −coeffMinusGap` step in
  step 6 fails to typecheck — fall back to writing it out by hand:
  `unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap; ring`.
* The final `ring`/`linarith` chain in step 8 fails to close the
  goal — restructure as a `calc` block aligning each rewrite step
  explicitly:
  ```
  calc PaperAxioms.circleGap a b r
      = ∑' k, coeffPlusGap a b k * r^(2k) := rfl
    _ = ∑' k, [(if n1Pred then ... else 0) + (if n2Pred then ... else 0)] := by rw [tsum_congr ...]
    _ = (∑' k, if n1Pred ...) + (∑' k, if n2Pred ...) := tsum_add ...
    _ = sigmaPlus a b r + (∑' k, if n2Pred then coeffPlusGap·r^(2k) else 0) := rfl
    _ = sigmaPlus a b r + (- ∑' k, if n2Pred then coeffMinusGap·r^(2k) else 0) := by ...
    _ = sigmaPlus a b r - sigmaMinus a b r := by ...
    _ = sigmaPlus a b r - r^2 * sigmaZeroMinus a b r := by rw [sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus]
  ```
* Any of acceptance criteria 4, 5, 7, 8, 9, 10, 11, 12 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially `paper.eq3_circleGap_decomposition`,
  which would defeat the *whole point* of paper-axiom-free
  re-derivation, or `circleGap_le_sigmaPlus_via_series_split`,
  which would reverse the intended dependency direction):
  `STATUS=BLOCKED` — that would defeat the **paper-axiom-free
  equality re-derivation** structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain (e.g., a `tsum_add` or `tsum_neg` variant absent from
  the pinned Mathlib): `STATUS=BLOCKED_NEEDS_HUMAN`.
