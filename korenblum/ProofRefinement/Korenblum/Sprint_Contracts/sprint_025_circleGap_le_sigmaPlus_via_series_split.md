# Sprint 025: Series-side upper bound `circleGap a b r ≤ sigmaPlus a b r` via N1/N2 partition — the workspace's **first lemma operating purely at the `circleGapSeries` representation level**, the **first workspace consumer of `coeffPlusGap`/`sigmaPlus`/`n1Pred`**, and a strictly stronger pointwise upper bound on `circleGap` than every existing workspace lemma (no paper-axiom invocation, valid on the **entire disk** `[0, 1)` rather than only `(0, c)` like sprint 002 or only via integrated `(3)+(4)` like sprint 013)

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V24.lean`
**Target file**: `Candidates/V25.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem circleGap_le_sigmaPlus_via_series_split
    (a b : ℕ → ℂ) {r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hSummable_circleGap :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) :
    PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r
```

This is the **series-level identity-form** counterpart of Wang's printed
equation `(3)` (`circleGap r = sigmaPlus r - r²·sigmaZeroMinus r`) but
established **without invoking `paper.eq3_circleGap_decomposition`**. The
proof uses only the *definitions* of `circleGap`, `circleGapSeries`,
`sigmaPlus`, `coeffPlusGap`, `coeffMinusGap`, `n1Pred`, `n2Pred` and the
fact that `n1Pred` and `n2Pred` partition `ℕ` via the cases
`(k = 0) ∨ (‖a_k‖ ≥ ‖b_k‖)` vs `(0 < k ∧ ‖a_k‖ < ‖b_k‖)`. On the `n2Pred`
branch, `coeffPlusGap = ‖a_k‖² − ‖b_k‖² ≤ 0` (by `‖a_k‖ < ‖b_k‖` squared
plus `pow_le_pow_left₀`), so the `n2Pred` summands `coeffPlusGap a b k ·
r^(2k)` are non-positive for `r ≥ 0`, hence dropping them gives
`circleGap a b r = circleGapSeries r ≤ sigmaPlus r`.

The lemma's body is structurally a series-level analog of sprint 011's
`sigmaZeroMinus_monotone_of_summable` proof: split the termwise sum by
the `n1Pred`/`n2Pred` cases, establish termwise non-positivity of the
`n2Pred` contribution, and dispatch via `tsum_le_tsum` /
`Summable.of_nonneg_of_le` from Mathlib. No `Section2Assumptions`
instance is needed — the lemma is parameterised only by `(a, b)`, the
radius `r`, and a single summability premise.

Then ship a `Candidates/V25.lean` at the same `c = 0.3554` that
compiles, scores `≥ V24 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v25_circleGap_le_sigmaPlus_compiles` and
`v25_circleGap_series_split_n2_nonpos_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. The bulletin **explicitly names** as a high-value axis:

> work on the coefficient side via `sigmaPlus`/`sigmaMinus`/
> `sigmaZeroMinus` structure or the `circleGapSeries` representation
> instead of going through the integrated forms

Sprint 025 ships the workspace's **first** lemma along this axis.
Specifically, it introduces three structural firsts that no prior
workspace lemma occupies:

1. **First workspace lemma operating purely at the `circleGapSeries`
   representation level.** Every prior workspace lemma manipulates
   `circleGap a b r` as a function (via `paper.eq3`-decomposition
   into `sigmaPlus − r²·sigmaZeroMinus`, or via integrated bounds on
   `[0, c]` / `[c, 1]`). Sprint 025 is the **first** workspace lemma
   to expand `circleGap a b r = circleGapSeries a b r =
   ∑' k, coeffPlusGap a b k · r^(2k)` (the literal series
   representation, definitionally equal at every `r`) and exploit the
   *termwise structure* directly. This is **not** a re-derivation of
   `paper.eq3_circleGap_decomposition` — the splitting `circleGapSeries
   = sigmaPlus + (sum over N2 of coeffPlusGap · r^(2k))` is a
   **series-internal identity** at the level of the `tsum`
   definitions, not a paper hypothesis. After sprint 025 lands, the
   workspace has its **first** non-trivial closed-form upper bound on
   `circleGap` whose transitive proof body invokes **zero** paper
   axioms — a structurally novel category of lemma that opens the
   `circleGapSeries`-direct sufficient-condition axis the bulletin
   solicits.

2. **First workspace consumer of `coeffPlusGap`, `sigmaPlus`,
   `n1Pred`, and `circleGapSeries`.** Greppable check: every prior
   sprint manipulates `coeffMinusGap`, `sigmaZeroMinus`, `sigmaMinus`,
   `n2Pred` (via sprints 005/011/012/022/023/024). The current
   `Reduction.lean` contains zero direct references to `coeffPlusGap`,
   `sigmaPlus`, `n1Pred`, or `circleGapSeries` outside of paper-axiom
   surface uses (`paper.eq3` mentions `sigmaPlus` but the workspace's
   *own* lemmas have never inspected these objects). Sprint 025 lands
   the workspace's **first** lemma to inspect `coeffPlusGap` and
   `n1Pred` directly, opening the structural-N1/N2 partition axis.
   Greppable verification: `grep -c 'coeffPlusGap\|n1Pred\|sigmaPlus\
   |circleGapSeries' Proof/Reduction.lean` should rise from its
   current count of zero (modulo references inside `Section2Assumptions`
   field projections like `paper.eq4_sigmaPlus_bound`) to at least two
   (one for the lemma signature/body, one for the `Candidates/V25`
   exercising side lemma).

3. **Strictly stronger pointwise upper bound on `circleGap` than every
   existing workspace lemma, with the cleanest premise set.** The
   existing pointwise `circleGap` upper bounds in the workspace are:

   * Sprint 002 `circleGap_inner_bound_of_eq2_eq3_eq4`: bounds
     `circleGap a b r` on `(0, c)` by a *quadratic-in-r* expression
     using `sigmaZeroMinus a b c` and `sigmaZeroMinus a b ρ` —
     consumes `eq2 + eq3 + eq4` paper axioms, requires `0 < r < c <
     ρ < 1` window, requires the auxiliary parameter `ρ`.
   * Sprint 005 `circleGap_outer_lower_bound_of_eq8_eq9`: a *lower*
     bound `2ρ³·Z_ρ/Λ ≤ 2ρ·circleGap a b ρ` on `(c, 1)` — consumes
     `eq8 + eq9`. The opposite direction is not in the workspace.
   * Sprint 013 `diskExcess_upper_bound_via_eq3_eq4`: an *integrated*
     bound on `∫ 2r·circleGap r dr` over `[0, c]`, not a pointwise
     bound on `circleGap a b r` itself.

   Sprint 025's `circleGap_le_sigmaPlus_via_series_split` is **strictly
   structurally cleaner** than all three:
   * No paper-axiom invocation (vs. sprints 002, 005, 013 each consume
     2–3 paper axioms).
   * Valid on the **entire disk** `r ∈ [0, 1)` (modulo summability),
     not just `(0, c)` like sprint 002, and not just via the
     integrated form like sprint 013.
   * No auxiliary radius parameter (sprint 002 needs `ρ`; sprint 025
     just takes the radius `r`).
   * Single summability premise vs sprint 002's three-radius interval
     constraint.

   The cost is a single summability premise on the full
   `circleGapSeries` (`Summable (fun k => coeffPlusGap a b k · r^(2k))`)
   — strictly weaker than the **two** summability premises that
   sprints 022/023 require on `coeffMinusGap·ρ^(2k-2)`, since
   `coeffPlusGap = -coeffMinusGap` on N2 and `r^(2k)` decays at the
   same rate as `r^(2k-2)·r²`.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V25 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form pointwise upper
  bound on `circleGap a b r` parameterised by a single radius `r ∈
  [0, 1)` and a single summability premise, with no quantification
  over `(c, ρ)` and no paper-axiom hypothesis.

Why this is **not** "the same chain" as sprint 002:

* **Disjoint paper-axiom signature.** Sprint 002 consumes `eq2 + eq3
  + eq4`. Sprint 025 consumes **zero** paper axioms — the proof body
  uses only the *definitions* `circleGap`, `circleGapSeries`,
  `sigmaPlus`, `coeffPlusGap`, `coeffMinusGap`, `n1Pred`, `n2Pred`.
* **Disjoint validity region.** Sprint 002 holds on `(0, c)` and
  needs the auxiliary anchor `c < ρ < 1`. Sprint 025 holds on
  `[0, 1)` (in fact on all `r ≥ 0` — but for downstream consumers
  the natural region is `r < 1` so the geometric series controls
  summability).
* **Disjoint RHS shape.** Sprint 002's RHS is a *closed-form
  rational expression* in `c, ρ, r, sigmaZeroMinus a b c, sigmaZeroMinus
  a b ρ`. Sprint 025's RHS is `sigmaPlus a b r` itself — a single
  series-side quantity, no pointwise rational expansion, no `(c, ρ)`
  parameters.

Why this is **not** "the same chain" as `paper.eq3_circleGap_decomposition`:

* Paper equation `(3)` is the **identity** `circleGap r = sigmaPlus r −
  r²·sigmaZeroMinus r` — an *equality* axiomatised in
  `Section2Assumptions`. Sprint 025 is the **inequality** `circleGap r
  ≤ sigmaPlus r`, which on the *paper-axiom side* would follow from
  `eq3` plus `r²·Z_r ≥ 0` (the latter via `sigmaZeroMinus_nonneg_of_pos`).
  Sprint 025 establishes the same inequality **without invoking
  `paper.eq3`** — instead, it uses the *series identity* `circleGapSeries
  r = sigmaPlus r + (∑' k, if n2Pred then coeffPlusGap·r^(2k) else 0)`
  (which is an arithmetic identity over the `tsum`s, with N1/N2
  partitioning the active set) and the termwise non-positivity of
  the N2 contribution.
* This is a **paper-internal cross-validation that `eq3` is structurally
  redundant** with respect to the *inequality* direction — the
  equality `eq3` carries strictly more information than the
  inequality `circleGap ≤ sigmaPlus`, but the inequality is provable
  from series structure alone. Mirrors sprint 022's cross-validation
  that `eq6` is provable from `eq2+eq3+eq4` plus series-monotonicity
  on the branch-2 sub-regime, but at the **series-representation
  level** rather than at the function-bound level.

Why this is **not** "the same chain" as sprint 011's
`sigmaZeroMinus_monotone_of_summable`:

* **Disjoint coefficient family.** Sprint 011 manipulates
  `coeffMinusGap a b k · s^(2k-2)` (the `sigmaZeroMinus`-side
  termwise summands). Sprint 025 manipulates `coeffPlusGap a b k ·
  r^(2k)` (the `circleGapSeries` and `sigmaPlus`-side termwise
  summands). Different partition predicate (`n2Pred` vs `n1Pred`),
  different sign convention (`coeffMinusGap = -coeffPlusGap`),
  different exponent shape (`2k-2` vs `2k`).
* **Different inequality direction.** Sprint 011 establishes a
  *lower* bound on the N2-side sum at one radius from the same
  N2-side sum at a larger radius (`Z_s ≤ Z_t` for `s ≤ t`). Sprint
  025 establishes an *upper* bound on the *full* circleGapSeries by
  the *N1-restricted* sum at the same radius (`circleGap r ≤
  sigmaPlus r`), via dropping the N2 contribution.
* **Different role.** Sprint 011 transports termwise behaviour
  *across radii*. Sprint 025 transports termwise behaviour *across
  index subsets at a fixed radius*.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~6 lines, the proof body is ~30–50 lines,
  modeled directly on sprint 011's body (`Reduction.lean:1283-1348`).
* The proof structure is:
  1. Unfold `circleGap = circleGapSeries` (definitional, one `change`
     or `show`).
  2. Unfold `circleGapSeries r` and `sigmaPlus r` to `tsum`s
     (definitional via `change`).
  3. Define `f k := coeffPlusGap a b k · r^(2k)` (the `circleGapSeries`
     summand) and `g k := if n1Pred a b k then f k else 0` (the
     `sigmaPlus` summand).
  4. Termwise inequality `f k ≤ g k`:
     * If `n1Pred a b k`: `g k = f k`, so `f k ≤ g k` holds with
       equality.
     * If `¬n1Pred a b k`: then `n2Pred a b k` (by partition: not
       (`k=0` ∨ `‖a‖ ≥ ‖b‖`) iff `0 < k` ∧ `‖a‖ < ‖b‖`). Then
       `g k = 0` and `f k = coeffPlusGap a b k · r^(2k) =
       (‖a_k‖² − ‖b_k‖²) · r^(2k) ≤ 0` since `‖a_k‖² ≤ ‖b_k‖²`
       (from `‖a_k‖ < ‖b_k‖` via `pow_le_pow_left₀`) and `r^(2k) ≥ 0`
       (from `hr_nonneg` via `pow_nonneg`). So `f k ≤ 0 = g k`.
  5. Termwise summability: `Summable f` is the hypothesis
     `hSummable_circleGap`. `Summable g` is then derived via
     `Summable.of_nonneg_of_le` applied to the absolute-value
     comparison `|g k| ≤ |f k|` (or alternatively, by noting that
     `g k = if n1Pred then f k else 0` is dominated termwise by
     `|f k|`, and `Summable f → Summable |f|` over `ℝ` requires
     `Summable.of_nonneg_of_le` which doesn't apply directly to `f`
     because `f` may have negative terms; instead use
     `Summable.indicator` or `Summable.of_nonneg_of_le` on the
     non-negative `g` with bound `f.abs`). Actually the cleanest
     path is: `g k = (if n1Pred a b k then 1 else 0) * f k`, and
     `Summable f → Summable g` via Mathlib's `Summable.indicator`
     pattern. As a fallback: prove `g` is summable by case-splitting
     pointwise non-negativity within the n1Pred = false branch
     (`g k = 0` is trivially summable), and for the n1Pred = true
     branch use that `g k = f k` so termwise dominated by `|f k|`.
  6. Apply `tsum_le_tsum` to conclude `∑' f ≤ ∑' g`, which unfolds
     to `circleGapSeries r ≤ sigmaPlus r`, which by definitional
     equality `circleGap a b = circleGapSeries a b` (PaperAxioms.lean:94)
     is `circleGap a b r ≤ sigmaPlus a b r`.

* All Lean idioms used (`tsum_le_tsum`, `Summable.of_nonneg_of_le`,
  `pow_le_pow_left₀`, `pow_nonneg`, `simp`, `change`, `by_cases`,
  `linarith`, `nlinarith`) are **already verified at the cited line
  ranges** in sprint 011 (`Reduction.lean:1283-1348`).
* Estimate: ~50 lines for the new theorem, dominated by the termwise
  case split in step 4 and the summability transfer in step 5. The
  candidate side lemmas are 5–25 lines each. Total V25 size: ≤ 70
  lines.

Why this beats the alternatives I considered:

* **A: Anchor sprint 022's branch-2 disk bound at `c` itself.** The
  sprint 023/024 forward roadmap names this. However, sprint 022's
  signature requires `branchSplit c ≤ ρ`, and re-anchoring at `c`
  requires the *opposite* direction of `Z`-monotonicity (`Z_ρ ≤ Z_c`
  for `c ≤ ρ` — the wrong direction; sprint 011 only gives `Z_s ≤ Z_t`
  for `s ≤ t`). The genuine "anchor at `c`" lemma would re-derive the
  bound from `(2)+(3)+(4)` directly without going through `Z_{ρ}` —
  but that is essentially **sprint 013** (`diskExcess ≤ c⁴ · Z_c`),
  already in the workspace. So alternative A reduces to "sprint 013
  exists". **Demoted: no novelty.**

* **B: A reducer using `eq2` alone (without `eq3`/`eq4`).** `eq2`
  bounds `sigmaZeroMinus r` from below in terms of `sigmaZeroMinus c`
  and `sigmaZeroMinus ρ`. Without `eq3` (which links `circleGap` to
  the sigmas) or `(8)+(9)` (which lifts sigma to circleGap with `Λ`),
  there's no way to translate `eq2` into a disk-side bound. **Demoted:
  not independently viable.**

* **C: A novel reducer using `eq2 + (8)+(9)` *bypassing* `eq3` and
  `eq4`.** Could one bound `circleGap a b r` on the disk via `eq2`
  rearranged as an upper bound on `Z_c`, and then use `(8)+(9)` to
  bound `Z_ρ`? Algebraically: rearrange `eq2` to `Z_c ≤
  ((ρ²−c²)/(ρ²−r²))·Z_r + ((c²−r²)/(ρ²−r²))·Z_ρ` (the convexity-style
  inversion). Combine with `(8)+(9)`: `Z_ρ = sigmaMinus ρ / ρ² ≤
  Λ(c,ρ)·circleGap ρ / ρ²`. Result: a disk-side `Z_c` bound in terms
  of `Z_r` and `circleGap ρ`. This is **highly speculative** — without
  a `Scratch/` derivation showing the algebra collapses to something
  that closes a `ValidKorenblumBound c` proof, we can't write a
  contract for it. The bulletin says "have direction and evidence
  before going to Lean." **Demoted: needs `Scratch/` first.**

* **D: Termwise integration of `circleGapSeries` to give a closed-form
  series-side disk bound `diskExcess ≤ ∑' k ∈ N1, coeffPlusGap a b k ·
  c^(2k+2)/(k+1)`.** This is the integrated counterpart of sprint 025
  — multiply sprint 025's pointwise bound by `2r` and integrate over
  `[0, c]`. Termwise integration of a `tsum` requires
  `MeasureTheory.tsum_integral_eq_integral_tsum` or
  `hasSum_integral_of_summable` style swap-of-sum-and-integral, which
  is **non-trivial Mathlib machinery** and may exceed the bounded-
  Generator-session budget if the pinned Mathlib version's lemma
  signatures don't immediately match. **Demoted to a follow-up sprint
  after 025 lands** — sprint 025 is the structural prerequisite.

* **E: Workspace lemma `sigmaMinus_monotone_of_summable` (`s ≤ t →
  sigmaMinus s ≤ sigmaMinus t`).** Follows in 2 lines from sprint
  005's `sigmaMinus = ρ²·sigmaZeroMinus` identity plus sprint 011's
  `Z`-monotonicity. **Demoted as too thin — would not constitute a
  full sprint.**

* **F: Free-standing paper-internal lemma `eq14_combined_of_eq12_eq13`
  showing `eq14` is derivable from `eq12 + eq13`.** Sprint 001's body
  already includes this derivation; a free-standing lemma would be a
  refactor. Marginal novelty. **Demoted.**

* **G: Termwise integration to give an upper bound `diskExcess ≤ c² ·
  sigmaPlus c` directly from sprint 025 (proposed)**. The closed-form
  consequence of integrating sprint 025: `diskExcess = ∫₀^c 2r·circleGap
  r dr ≤ ∫₀^c 2r·sigmaPlus r dr ≤ ∫₀^c 2r·sigmaPlus c dr = c²·sigmaPlus c`
  (using `eq4`'s `sigmaPlus r ≤ sigmaPlus c` for `r < c`). This would
  be a separate theorem, after 025. **Demoted to follow-up.**

* **H: A `circleGap`-direct *lower* bound on the disk via `eq3`
  rearranged.** From `eq3`: `circleGap r = sigmaPlus r − r²·Z_r`.
  Lower bound on `circleGap` requires lower bound on `sigmaPlus`,
  which paper does not provide directly. **Demoted: not derivable
  from current trust surface.**

* **I: A series-side identity at the `liftGapSeries` level.**
  `Section2Assumptions` does not expose any closed-form structural
  property of `liftGap` beyond `(8)+(9)`, so working at the
  intermediate layer offers no new structural lemma. **Demoted.**

* **J: Discharge sprints 023/024's kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ`
  numerically at the seed.** Demoted in sprints 017/018/019/023/024 —
  needs a closed-form `paperLambda` envelope or numerical oracle,
  neither in scope. Still demoted.

Compared to A–J, candidate K (this sprint,
`circleGap_le_sigmaPlus_via_series_split`) maximises analytical
novelty per bounded Generator session: it ships the **first workspace
lemma operating at the `circleGapSeries` representation level**, the
**first workspace consumer of `coeffPlusGap`/`sigmaPlus`/`n1Pred`**,
and the **first paper-internal cross-validation that the inequality
direction of `eq3` is provable from series structure alone**. It uses
**only existing trusted modules + pinned Mathlib + already-verified
`Reduction.lean` patterns** mirrored from sprint 011's series-level
proof body. No proposal needed.

### Note on the partition `n1Pred ↔ ¬n2Pred`

`n1Pred a b k = (k = 0 ∨ ‖a_k‖ ≥ ‖b_k‖)` and `n2Pred a b k = (0 < k ∧
‖a_k‖ < ‖b_k‖)`. The negation `¬n1Pred a b k = (k ≠ 0 ∧ ‖a_k‖ < ‖b_k‖)
= (0 < k ∧ ‖a_k‖ < ‖b_k‖) = n2Pred a b k`. So `n1Pred` and `n2Pred`
**partition `ℕ`**. This is the structural fact sprint 025's case-split
relies on. The implication `¬n1Pred → n2Pred` should typecheck via a
short `by` block: `by intro h; refine ⟨?_, ?_⟩; ...; exact
(not_or.mp h).1.symm.le_iff_lt.mp (le_of_not_lt …)` — or more cleanly
`by push_neg at h; exact ⟨Nat.pos_of_ne_zero h.1, lt_of_not_ge h.2⟩`.
The cleanest form is to define the local helper:

```lean
have hPartition : ∀ k, ¬PaperAxioms.n1Pred a b k → PaperAxioms.n2Pred a b k := by
  intro k hk
  unfold PaperAxioms.n1Pred PaperAxioms.n2Pred at *
  push_neg at hk
  exact ⟨Nat.pos_of_ne_zero hk.1, lt_of_not_ge hk.2⟩
```

(Or its inverse direction — sprint 025 needs the partition to deduce
that the n1Pred-false branch puts the index in n2Pred, where the
`coeffPlusGap = ‖a‖² − ‖b‖² ≤ 0` non-positivity argument applies.)

### Note on the summability hypothesis shape

The cleanest summability hypothesis for sprint 025 is summability of
the *unconditioned* `circleGapSeries` summand:

```lean
hSummable_circleGap :
  Summable (fun k : ℕ => PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))
```

This is the natural shape because `circleGap a b r = circleGapSeries
a b r = ∑' k, coeffPlusGap a b k · r^(2k)` already requires this
summability for the `tsum` to converge to a finite value. Mathlib's
`tsum_le_tsum` requires both `Summable f` and `Summable g`; the
latter is derived in-house via `Summable.of_nonneg_of_le` or via
`Summable f → Summable (if n1Pred then f else 0)` with the
indicator-style argument: the indicator-restricted summand satisfies
`|if n1Pred then f else 0| ≤ |f|` pointwise, so summability transfers
from `f` to the indicator-restricted version directly.

If the cleanest direct path turns out to be: assume `Summable
(coeffPlusGap a b · r^(2*·)).abs` (i.e., absolute summability), then
the derivation is even cleaner — both sums are absolutely convergent,
termwise comparison via `tsum_le_tsum` is trivial. The contract leaves
the precise summability hypothesis shape flexible: use whatever
Mathlib lemma path is cleanest. The `Candidates/V25.lean` exercising
side lemma will exhibit the chosen shape.

### Note on the witness lemma at the seed

At the seed `c_value = 0.3554`:
* The lemma `circleGap_le_sigmaPlus_via_series_split` is parameterised
  by `r ∈ [0, 1)` and a summability premise; the cleanest concrete
  side lemma at the seed exhibits `r = c_value` and the hypothesis
  shape, *without* discharging the summability premise (the latter
  remains existential / hypothesis-only since it depends on the
  abstract `(a, b)` pair).
* A second, **purely structural** witness lemma confirms the
  termwise non-positivity of the n2Pred contribution at `r = c_value`:
  `∀ k, n2Pred a b k → coeffPlusGap a b k · c_value^(2k) ≤ 0`. This
  is a series-side structural fact at the seed radius.

### Note on what the witness lemma should NOT do

Sprint 025's V25 witness lemma is **structural only** — it confirms
that the new lemma's signature compiles at the seed radius and that
the termwise non-positivity is non-vacuous. It **does NOT** discharge
the summability premise (which remains an existential hypothesis), it
**does NOT** invoke any paper axiom, and it **does NOT** push
`c_value` upward.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `circleGap_le_sigmaPlus_via_series_split`
    matching the shape above. Place it **after** sprint 024's
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
    at the end of the file (after current line 3684) so the
    chronological narrative is preserved.

    The proof body must:

    1. **Unfold `circleGap` and `circleGapSeries`/`sigmaPlus` to
       `tsum`s.** Use `change` or `simp only [PaperAxioms.circleGap,
       PaperAxioms.circleGapSeries, PaperAxioms.sigmaPlus]` to expose
       the underlying `∑'` expressions on both sides.

    2. **Define termwise summands.** Introduce `f k =
       coeffPlusGap a b k · r^(2k)` (the `circleGapSeries` summand)
       and `g k = if n1Pred a b k then coeffPlusGap a b k · r^(2k)
       else 0` (the `sigmaPlus` summand) as `set` bindings.

    3. **Termwise inequality `f k ≤ g k`** by case split on
       `n1Pred a b k`:
       * `true` branch: `g k = f k`, so `f k ≤ g k` holds with
         equality (`le_refl`).
       * `false` branch: `g k = 0` (by `if_neg`). Then derive
         `n2Pred a b k` from the partition (see "Note on the
         partition" above), use `‖a_k‖ < ‖b_k‖` to deduce
         `‖a_k‖² ≤ ‖b_k‖²` via `pow_le_pow_left₀`, hence
         `coeffPlusGap a b k = ‖a_k‖² − ‖b_k‖² ≤ 0`. Combined
         with `r^(2k) ≥ 0` (from `hr_nonneg` via `pow_nonneg`),
         conclude `f k ≤ 0 = g k` via `mul_nonpos_of_nonpos_of_nonneg`
         or `mul_nonneg`/`linarith`.

    4. **Summability transfer** from `Summable f` (the hypothesis
       `hSummable_circleGap`) to `Summable g`. Use the cleanest
       Mathlib lemma — likely `Summable.of_nonneg_of_le` after
       observing that `g k = (if n1Pred a b k then 1 else 0) · f k`
       and bounding `|g k| ≤ |f k|`. Alternative cleaner path: define
       `g'` as the indicator multiplied by `f`, use Mathlib's
       indicator-summability lemma, conclude.

    5. **Apply `tsum_le_tsum`** to `f ≤ g` plus the two summability
       facts to conclude `∑' f ≤ ∑' g`. The LHS is `circleGapSeries
       a b r = circleGap a b r`; the RHS is `sigmaPlus a b r`.
       Conclude.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 025's `circleGap_le_sigmaPlus_via_series_split`
    is the workspace's **first lemma operating purely at the
    `circleGapSeries` representation level**, the **first workspace
    consumer of `coeffPlusGap`/`sigmaPlus`/`n1Pred`**, and the **first
    paper-internal cross-validation that the inequality direction of
    `paper.eq3_circleGap_decomposition` (`circleGap r ≤ sigmaPlus r`)
    is provable from series structure alone, with zero paper-axiom
    invocation in the transitive proof body**.

  * The body of the new theorem MAY invoke:

    * Definitional unfolding of `PaperAxioms.circleGap`,
      `PaperAxioms.circleGapSeries`, `PaperAxioms.sigmaPlus`,
      `PaperAxioms.coeffPlusGap`, `PaperAxioms.coeffMinusGap`,
      `PaperAxioms.n1Pred`, `PaperAxioms.n2Pred`,
    * Mathlib's `tsum_le_tsum`, `Summable.of_nonneg_of_le`,
      `Summable.indicator` (or the equivalent indicator-multiplication
      pattern), `pow_le_pow_left₀`, `pow_nonneg`, `norm_nonneg`,
      `mul_nonpos_of_nonpos_of_nonneg`, `mul_nonneg`,
      `Nat.pos_of_ne_zero`, `lt_of_not_ge`, `not_or`, `push_neg`,
    * Standard tactics: `by_cases`, `simp`, `change`, `set`, `intro`,
      `linarith`, `nlinarith`, `exact`, `refine`, `rfl`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that sprint 025
    operates at the **series-representation level only**, with **zero
    paper-axiom invocation**):

    * `paper.eq2_sigmaZeroMinus_lower`, `paper.eq3_circleGap_decomposition`,
      `paper.eq4_sigmaPlus_bound`, `paper.eq5_branch1_sigmaReduction`,
      `paper.eq6_branch2_sigmaReduction`, `paper.eq7_paperK_formula`,
      `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`,
      `paper.eq10_branch1_pointwise`, `paper.eq11_branch2_pointwise`,
      `paper.eq12_branch1_integrated`, `paper.eq13_branch2_integrated`,
      `paper.eq14_combined`, `paper.eq15_…` (no paper axiom whatsoever),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, `eq10_of_eq5_eq8_eq9`,
      `eq11_of_eq6_eq8_eq9` (no paper-internal derived bridge),
    * Any `valid_of_*` reducer (sprint 025 does not close the contract;
      it is a *structural lemma*),
    * Any prior `diskExcess_upper_bound_*`,
      `annulusExcess_lower_bound_*`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
      `sigmaZeroMinus_nonneg_of_pos`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq5`,
      `diskExcess_upper_bound_via_eq6`,
      `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
      (sprint 025 must close on its own from series structure alone,
      with no transitive workspace-lemma dependency on any prior
      function-level circleGap bound),
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
      `IntervalIntegrable.*` (sprint 025 is a pointwise inequality,
      no integration anywhere).

    (Note: `PaperAxioms.circleGap`, `PaperAxioms.circleGapSeries`,
    `PaperAxioms.sigmaPlus`, `PaperAxioms.coeffPlusGap`,
    `PaperAxioms.coeffMinusGap`, `PaperAxioms.n1Pred`,
    `PaperAxioms.n2Pred` are EXEMPT and ARE consumed via definitional
    unfolding only.)

  * The new theorem's signature MUST take *exactly* the parameters in
    the goal block above: explicit `(a b : ℕ → ℂ)`, implicit `{r : ℝ}`,
    explicit `(hr_nonneg : 0 ≤ r)`, explicit
    `(hSummable_circleGap : Summable (fun k => coeffPlusGap a b k *
    r ^ (2 * k)))`. The conclusion MUST be exactly
    `PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r`.

* `ProofRefinement/Korenblum/Candidates/V25.lean`:

  * `-- @parent V24`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V24).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V24).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new lemma's signature compiles at the seed `r = c_value`:

    ```lean
    theorem v25_circleGap_le_sigmaPlus_compiles
        (a b : ℕ → ℂ)
        (hSummable :
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k))) :
        PaperAxioms.circleGap a b c_value ≤ PaperAxioms.sigmaPlus a b c_value :=
      circleGap_le_sigmaPlus_via_series_split a b c_value_pos.le hSummable
    ```

    (Use `c_value_pos.le : 0 ≤ c_value` for the `hr_nonneg` argument;
    `c_value > 0` was proven in `c_value_pos` already so `.le` gives
    the non-negative version.)

  * Additionally, prove a structural side lemma confirming the
    termwise non-positivity of the n2Pred contribution at `r =
    c_value`:

    ```lean
    theorem v25_circleGap_series_split_n2_nonpos_at_seed
        (a b : ℕ → ℂ) (k : ℕ) (h : PaperAxioms.n2Pred a b k) :
        PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k) ≤ 0 := by
      have hab : ‖a k‖ < ‖b k‖ := h.2
      have ha_nn : 0 ≤ ‖a k‖ := norm_nonneg _
      have h_sq_le : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 :=
        pow_le_pow_left₀ ha_nn hab.le 2
      have h_gap_np : PaperAxioms.coeffPlusGap a b k ≤ 0 := by
        unfold PaperAxioms.coeffPlusGap
        linarith
      have h_pow_nn : 0 ≤ c_value ^ (2 * k) :=
        pow_nonneg c_value_pos.le _
      exact mul_nonpos_of_nonpos_of_nonneg h_gap_np h_pow_nn
    ```

    This side lemma exhibits the **structural fact** that the n2Pred
    contribution to `circleGapSeries c_value` is termwise
    non-positive — the analytical core of sprint 025's argument
    materialised at the seed.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify the new lemma's signature
    typechecks at the seed `c_value` and to demonstrate the termwise
    non-positivity is non-vacuous.

* `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_025 queued: ...` line.

* `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting the new series-representation-level axis,
  the new role for `coeffPlusGap`/`sigmaPlus`/`n1Pred` as
  workspace-internal targets, and the follow-up roadmap (e.g., the
  natural next step is alternative D — termwise integration of
  `circleGap a b r ≤ sigmaPlus a b r` against `2r` over `[0, c]` to
  give `diskExcess ≤ c²·sigmaPlus c`, providing a structurally
  novel **integrated** disk bound that bypasses `eq3` entirely; or
  alternative G — a paper-internal cross-validation
  `diskExcess_upper_bound_via_circleGapSeries_eq4_only` chaining
  sprint 025 with `paper.eq4_sigmaPlus_bound` to give `diskExcess ≤
  c²·sigmaPlus c ≤ c⁴·sigmaZeroMinus c` — algebraically equal to
  sprint 013's bound but derived through a **disjoint paper-axiom
  signature** `{eq4}` instead of `{eq3, eq4}`).

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V24.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_024`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V25.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V25.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V25 scores `≥` V24 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V25.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'circleGap_le_sigmaPlus_via_series_split' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of `tsum_le_tsum` (or an
     equivalent termwise-comparison `tsum` Mathlib lemma — the
     structural marker that sprint 025 operates at the `tsum` level),
   * at least one direct invocation of `pow_le_pow_left₀` or
     `pow_nonneg` (the structural marker that the termwise non-positivity
     argument is materialised),
   * **no direct reference** to any `paper.eq{2..15}_…` field
     projection,
   * **no reference** to any `valid_of_*` reducer,
   * **no reference** to `diskExcess_upper_bound_*`,
     `annulusExcess_lower_bound_*`,
     `circleGap_inner_bound_of_eq2_eq3_eq4`,
     `circleGap_outer_lower_bound_of_eq8_eq9`,
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
     `sigmaZeroMinus_nonneg_of_pos`,
     `sigmaZeroMinus_monotone_of_summable`,
     `sigmaZeroMinus_summable_of_summable_at_upper`,
     `diskExcess_upper_bound_via_eq3_eq4`,
     `diskExcess_upper_bound_via_eq5`,
     `diskExcess_upper_bound_via_eq6`,
     `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
     `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
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
6. `grep -n 'v25_circleGap_le_sigmaPlus_compiles\|v25_circleGap_series_split_n2_nonpos_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V25.lean`
   returns at least two distinct matches.
7. The conclusion of `circleGap_le_sigmaPlus_via_series_split` is
   exactly `PaperAxioms.circleGap a b r ≤ PaperAxioms.sigmaPlus a b r`
   (verify via `grep` of the theorem statement).
8. The signature of `circleGap_le_sigmaPlus_via_series_split` contains:
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
     premise).
9. The body of `v25_circleGap_series_split_n2_nonpos_at_seed`
   exhibits the termwise non-positivity `coeffPlusGap a b k *
   c_value ^ (2 * k) ≤ 0` at any `k` satisfying `n2Pred a b k`, and
   discharges via `pow_le_pow_left₀ + linarith + mul_nonpos_of_*`.
10. **Structural marker**: `grep -c 'coeffPlusGap\|sigmaPlus\|n1Pred\|circleGapSeries' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
    returns a value strictly greater than the same `grep -c` count on
    the parent commit — confirming sprint 025 introduces at least one
    new direct reference to one of these previously-unseen-in-workspace
    objects. (Sprint 025 should add at least 4–6 references across
    the new lemma's signature, body, and definitional unfolds.)
11. **Paper-axiom-free transitive guarantee**: the new lemma
    `circleGap_le_sigmaPlus_via_series_split` does NOT depend on any
    `paper.eq{2..15}_…` field (verify via `#print axioms` style
    inspection or by confirming that the lemma compiles WITHOUT any
    `Section2Assumptions` instance in its signature — which acceptance
    criterion 8 enforces).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V24.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the integrated counterpart `diskExcess ≤ c² · sigmaPlus c`
  (alternative D/G above — termwise integration of the new lemma over
  `[0, c]`, requires `tsum_integral_eq_integral_tsum`-style swap
  machinery; queueable as a separate sprint after 025).
* Building the chained paper-internal cross-validation
  `diskExcess_upper_bound_via_circleGapSeries_eq4_only` (alternative
  G above — would chain sprint 025 with `paper.eq4_sigmaPlus_bound`
  to give `diskExcess ≤ c⁴ · sigmaZeroMinus c`, algebraically equal
  to sprint 013 but derived through a disjoint paper-axiom signature;
  queueable as a separate sprint after 025).
* Building a series-side *lower* bound on `circleGap a b r` from
  `circleGapSeries` structure (alternative H above — not derivable
  without a lower bound on `sigmaPlus`).
* Building a `liftGapSeries`-direct sufficient condition (alternative
  I above — `liftGap` has no closed-form lower bound on the workspace
  trust surface).
* Adding a `sigmaMinus_monotone_of_summable` lemma (alternative E
  above — too thin for a full sprint).
* Adding a paper-internal `eq14_combined_of_eq12_eq13` lemma
  (alternative F above — refactor of sprint 001).
* Building any new closing reducer for `ValidKorenblumBound c` —
  sprint 025 is a structural lemma only, not a closing reducer.
* Discharging the kernel inequalities of any prior sprint at the seed
  `c_value` numerically.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new lemma. Sprint 025 alone is **not** a
  closing reducer — it is a structural inequality. Closing requires
  composition with a downstream lemma (e.g., the integrated form in
  the deferred follow-up sprints).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 025 is purely
  structural.
* Modifying any prior `Reduction.lean` lemma (sprints 001–024 are
  consumed only by their existing call sites; sprint 025 adds a new
  lemma in isolation).

## Time budget

≤ 30 minutes runtime. The new lemma is ~50 lines of Lean (~6 lines
for the signature, ~40 lines for the proof body modeled on sprint
011's body, ~5 lines for the doc comment). The candidate side lemmas
are 5–25 lines each (including the seed-radius witness). Total V25
size: ≤ 70 lines. All tactics used are *already verified* in sprint
011 (`Reduction.lean:1283-1348`).

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `Summable.of_nonneg_of_le` path for the indicator-restricted
  summand `g k = if n1Pred then f k else 0` does not directly apply
  (because `f` may have negative terms, so `g` is not always
  pointwise dominated by a non-negative `f` in absolute value
  cleanly) — fall back to the explicit indicator-multiplication
  pattern: `g k = (if n1Pred a b k then (1 : ℝ) else 0) * f k`, then
  use `Summable.mul_left` or `Summable.indicator`. Alternative
  fallback: prove `Summable g` directly by `Summable.of_nonneg_of_le`
  comparing `|g k| = if n1Pred a b k then |f k| else 0 ≤ |f k|`,
  combined with `Summable f → Summable |f|` over `ℝ` (which holds
  iff `f` is absolutely summable; if Mathlib's `Summable` over `ℝ`
  is not absolute, the contract should require `Summable (|·|·f)`
  instead). The cleanest robust path is to require
  `Summable_abs : Summable (fun k => |coeffPlusGap a b k| * r ^ (2 * k))`
  in the hypothesis (absolute summability), which is a stronger
  hypothesis but enables `Summable.of_nonneg_of_le` to apply to both
  sides directly.
* The partition `¬n1Pred → n2Pred` step fails — fall back to writing
  it out by hand: `intro h; unfold n1Pred at h; push_neg at h;
  exact ⟨Nat.pos_of_ne_zero (fun h_eq => h.1 (Or.inl h_eq)),
  lt_of_not_ge h.2⟩`. The exact Lean syntax may need
  adjustment based on the precise definitions of `n1Pred`/`n2Pred`
  in `KorenblumPaper.PaperAxioms` (lines 33-39); reference sprint
  011's `pow_le_pow_left₀ (norm_nonneg _)` pattern at
  `Reduction.lean:1310` for the squaring step.
* The `tsum_le_tsum` invocation requires both sides to be summable
  in a form where Mathlib accepts the inequality — if the goal after
  unfolding is not exactly `∑' k, f k ≤ ∑' k, g k` but rather involves
  an additional `if`-wrapping or a different `tsum` shape, fall back
  to using `tsum_mono` or rewriting via `tsum_congr` to align the
  shapes.
* The witness lemma `v25_circleGap_series_split_n2_nonpos_at_seed`'s
  body fails to compile — fall back to copying sprint 011's
  `pow_le_pow_left₀` argument verbatim from `Reduction.lean:1308-1313`,
  with `coeffMinusGap → coeffPlusGap` and the inequality direction
  flipped (sprint 011 establishes `coeffMinusGap ≥ 0` on N2, sprint
  025 needs `coeffPlusGap ≤ 0` on N2 — the same algebraic step,
  signs flipped).
* Any of acceptance criteria 4, 5, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially any `paper.eq{2..15}_…` field
  projection or any `Section2Assumptions` instance threading):
  `STATUS=BLOCKED` — that would defeat the **paper-axiom-free
  series-representation-level** structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
