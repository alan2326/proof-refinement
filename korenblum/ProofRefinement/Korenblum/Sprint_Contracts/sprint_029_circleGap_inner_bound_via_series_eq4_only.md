# Sprint 029: Function-level inner-disk pointwise bound `circleGap a b r ≤ A·Z_c + B·Z_ρ` via composition of sprints 027 + 028 + sprint 005 + paper.eq4 only — the workspace's **first function-level closed-form inner-disk bound whose paper-axiom signature is exactly `{eq4}` (no `paper.eq2_sigmaZeroMinus_lower` and no `paper.eq3_circleGap_decomposition` anywhere in the transitive proof body)**, and the **first downstream materialisation of sprint 028 in a function-level chain that previously consumed `paper.eq2`**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V28.lean`
**Target file**: `Candidates/V29.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem circleGap_inner_bound_via_series_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {r ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ
```

The conclusion is **byte-for-byte identical** to sprint 002's
`circleGap_inner_bound_of_eq2_eq3_eq4`
(`Reduction.lean:192-296`). The hypothesis count grows by **exactly two
new summability premises** (`hSummable_circleGap_r` for sprint 027 and
`hSummable_n2_ρ` for sprint 028), but the *paper-axiom signature*
shrinks from `{eq2, eq3, eq4}` (sprint 002) to `{eq4}` only — sprint
027 discharges `eq3`, sprint 028 discharges `eq2`, and the third
conjunct of `eq4` remains accessible via sprint 005 (which sprint 002
also implicitly relies on through `paper.eq4`'s third conjunct).

The proof body re-walks sprint 002's algebraic chain step by step,
substituting:

1. **Step 1 (`h3`, `eq3` invocation, lines 213–218 of sprint 002).**
   Replace `paper.eq3_circleGap_decomposition` with sprint 027's
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   applied to `(a, b, r)`, `hr_nonneg`, `hSummable_circleGap_r`. Same
   pointwise equality `circleGap r = sigmaPlus r − r² · sigmaZeroMinus
   r`, derived without `paper.eq3`.

2. **Step 2 (`h4`, `eq4` invocation, lines 220–227 of sprint 002).**
   Keep verbatim — sprint 002's body uses all three conjuncts of
   `paper.eq4` (`Σ⁺ r ≤ Σ⁺ c`, `Σ⁺ c ≤ Σ⁻ c`, `Σ⁻ c = c² · Z_c`).
   Sprint 005 already gives the third conjunct paper-axiom-free, but
   replacing it inline would not reduce the paper-axiom signature
   (which is the *set* of paper.eq* fields that appear, and dropping
   the third conjunct still leaves `paper.eq4` in the signature). **The
   first conjunct (`Σ⁺ r ≤ Σ⁺ c`) is the only one for which a series
   proof is not yet shipped**; it is queued as a separate cleanup
   sprint (see "Out of scope" below). For sprint 029, keep
   `paper.eq4_sigmaPlus_bound` as the sole paper-axiom invocation.

3. **Step 3 (`h2`, `eq2` invocation, lines 234–241 of sprint 002).**
   Replace `paper.eq2_sigmaZeroMinus_lower` with sprint 028's
   `sigmaZeroMinus_lower_via_series_convexity` applied to `(a, b, r,
   c, ρ)`, `hr_nonneg`, `hr_lt`, `hcρ`, `hSummable_n2_ρ`. Same lower
   bound `Z_r ≥ ((ρ²−r²)/(ρ²−c²)) · Z_c − ((c²−r²)/(ρ²−c²)) · Z_ρ`,
   derived without `paper.eq2`. Note the type signature alignment:
   sprint 028 uses `≥`, while sprint 002's `h2_unfold` uses the same
   `≥`. The `Eq2SigmaZeroMinusLower` `simpa` step in sprint 002 is
   a definitional unfold; sprint 028 already returns the bound in
   the unfolded form, so the `simpa` is unnecessary in sprint 029.

4. **Steps 4–8 (algebraic rearrangement, lines 243–296 of sprint
   002).** Verbatim reuse — the algebra is the same once `h3`, `h4`,
   `h2` are established. The closing `calc` chain, the `hCoeff1` /
   `hCoeff2` denominator manipulation, and the final `rw` are all
   unchanged.

The proof body is structurally **sprint 002's body verbatim** with
exactly two `have h3 := ...` / `have h2 := ...` lines swapped to invoke
sprint 027 and sprint 028 respectively. Estimated body length: ~110
lines (sprint 002 is 105 lines; the swap adds ~5 lines for the
hypothesis plumbing).

Then ship a `Candidates/V29.lean` at the same `c = 0.3554` that
compiles, scores `≥ V28 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v29_circleGap_inner_bound_via_series_eq4_only_compiles` and
`v29_circleGap_inner_bound_via_series_eq4_only_recovers_sprint002_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. After sprints 027 and 028, the workspace has paper-axiom-free
series-level proofs of `eq3` (equality direction) and `eq2`
(cross-radius lower bound) in isolation, but **no function-level chain
yet materialises both substitutions simultaneously into a downstream
inner-disk bound**. Sprint 029 closes that gap.

After sprint 029 lands, the workspace has its **first function-level
inner-disk bound whose transitive proof body invokes exactly one paper
axiom** (`paper.eq4_sigmaPlus_bound`), where every prior workspace
inner-disk bound (sprints 002, 003, 007, 013, 022, 026) consumes
either two or three distinct `paper.eq*` fields:

| Sprint | Result | Paper-axiom signature |
|--------|--------|-----------------------|
| 002    | `circleGap r ≤ A·Z_c + B·Z_ρ` (pointwise) | `{eq2, eq3, eq4}` |
| 003    | `diskExcess ≤ A·Z_c + B·Z_ρ` (integrated) | `{eq2, eq3, eq4}` |
| 007    | `diskExcess ≤ B·Z_ρ` (collapsed, branch-1)| `{eq2, eq3, eq4}` |
| 013    | `diskExcess ≤ c⁴·Z_c` (full window)       | `{eq3, eq4}` |
| 022    | `diskExcess ≤ (c⁴/2)·Z_ρ` (branch-2)       | `{eq2, eq3, eq4}` (collapse via sprint 011) |
| 026    | `diskExcess ≤ c⁴·Z_c` (full window, series-side) | `{eq4}` |
| **029** | `circleGap r ≤ A·Z_c + B·Z_ρ` (pointwise) | **`{eq4}`** |

Sprint 026 was the first integrated disk bound with paper-axiom
signature `{eq4}`. Sprint 029 is the first **pointwise** inner-disk
bound with that same signature — and unlike sprint 026, sprint 029
preserves the **two-radius parameterisation** `(r, ρ)` that downstream
chains exploit (sprints 003, 007, 022 all integrate sprint 002's
pointwise bound; sprint 029 unlocks paper-axiom-`{eq4}`-only versions
of all three).

The structural firsts:

1. **First function-level closed-form inner-disk bound on `circleGap`
   whose paper-axiom signature is `{eq4}` only.** Strictly smaller
   than sprint 002's `{eq2, eq3, eq4}`. This is qualitatively
   significant: the entire downstream cone of pointwise inner-disk
   chains (sprint 003 integrates sprint 002 over `[0, c]`; sprint 007
   collapses sprint 003 to a single Z by dropping the `Z_c` summand;
   sprint 022 mirrors sprint 003 with branch-2 `Z`-collapse) gains a
   sprint-029-rooted counterpart with one paper axiom instead of three.

2. **First workspace lemma to *materialise* sprint 028 in a function-level
   chain.** Sprint 028 is currently a standalone series-level
   inequality with no downstream consumer; sprint 029 is its first
   load-bearing consumption inside a function-level pointwise bound.
   Greppable check: `grep -c "sigmaZeroMinus_lower_via_series_convexity"`
   in `Reduction.lean` rises from 0 to ≥ 1 after sprint 029 (the
   declaration line at `Reduction.lean:4047` is currently the only
   occurrence; sprint 029 adds a *use site*).

3. **First workspace lemma to *materialise* sprint 027 in a function-level
   chain that previously consumed `paper.eq3_circleGap_decomposition`.**
   Sprint 027 is currently used only in its own structural witness
   (V27's `v27_*` side lemmas); sprint 029 is the first lemma in
   `Reduction.lean` to consume sprint 027 inline as a `paper.eq3`
   substitute. Greppable check: `grep -c
   "circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition"`
   in `Reduction.lean` rises from 1 (declaration only) to ≥ 2
   (declaration + use site in sprint 029) after sprint 029.

4. **First workspace lemma whose paper-axiom signature is a *strict
   subset* of an earlier sprint's signature on the same conclusion
   shape.** Sprint 002's conclusion is byte-for-byte identical to
   sprint 029's; sprint 029's paper-axiom signature is `{eq4}`,
   strictly a subset of sprint 002's `{eq2, eq3, eq4}`. This is
   the first time the workspace has produced a paper-axiom-strict-subset
   improvement of an existing function-level lemma's *exact* conclusion
   (sprint 026 had a `{eq4}` signature but with a different conclusion
   shape — integrated rather than pointwise). The structural marker
   is "two transitive proof bodies, one inequality, paper-axiom
   signatures `{eq2, eq3, eq4}` vs `{eq4}`."

5. **Quantitative downstream impact.** Sprint 029 is the prerequisite
   for paper-axiom-`{eq4}`-only counterparts of:
   * sprint 003 (`diskExcess_upper_bound_of_eq2_eq3_eq4` →
     `diskExcess_upper_bound_via_series_eq4_only_v2` — would tie
     sprint 026's bound through a *disjoint* derivation route via the
     pointwise sprint 029 + integration vs sprint 026's direct
     series-pointwise + integration route);
   * sprint 007 (`diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
     → `diskExcess_collapsed_single_Z_via_series_eq4_only` — branch-1
     collapsed bound with `{eq4}` signature);
   * sprint 022 (`diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
     → `diskExcess_branch2_collapse_via_series_eq4_only` — branch-2
     collapsed bound with `{eq4}` signature, completing the dual to
     sprint 016's `{eq6}`-only branch-2 bound).
   These three follow-up sprints are queueable but **out of scope for
   sprint 029** to keep the bounded-Generator-session budget.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V29 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form pointwise
  inequality on `circleGap a b r` with the same conclusion shape as
  sprint 002 but a strictly smaller paper-axiom signature.

Why this is **not** "the same chain" as sprint 002:

* **Different paper-axiom signature.** Sprint 002 consumes
  `paper.eq2`, `paper.eq3`, `paper.eq4`. Sprint 029 consumes only
  `paper.eq4`. **Strict subset reduction.**
* **Different transitive dependencies.** Sprint 002 has zero workspace
  dependencies (it composes paper axioms directly). Sprint 029 depends
  on sprints 027 (for `eq3` equality) and 028 (for `eq2` lower bound)
  as load-bearing intermediaries.
* **Different summability discipline.** Sprint 002 has zero summability
  premises. Sprint 029 has two: one on the `circleGap` series at `r`
  (for sprint 027) and one on the N2-restricted `coeffMinusGap` series
  at `ρ` (for sprint 028). This is the trade-off — sprint 029 needs
  series-level summability premises that sprint 002 hides inside the
  paper-axiom black box.

Why this is **not** "the same chain" as sprints 027 or 028:

* **Different layer.** Sprints 027 and 028 are *series-level*
  lemmas on individual `tsum` quantities. Sprint 029 is a *function-level*
  pointwise inequality on `circleGap a b r` — the integration of two
  series-level identities into a downstream-consumable pointwise
  bound.
* **Different LHS.** Sprint 027's LHS is `circleGap a b r` (an
  equality identity). Sprint 028's LHS is `sigmaZeroMinus a b r` (a
  lower bound at three radii). Sprint 029's LHS is `circleGap a b r`
  (a pointwise upper bound at two radii).
* **Different downstream consumer profile.** Sprint 027 unlocks the
  `eq3`-equality direction in isolated tsum-level identities. Sprint
  028 unlocks the `eq2` lower bound in isolated tsum-level
  inequalities. Sprint 029 fuses both into a function-level inner-disk
  pointwise bound that is the natural input for the integration
  machinery in sprints 003/007/022.

Why this is **not** a numerical / mechanical push:

* The composition is **non-trivial**: it requires correctly threading
  the new summability premises through both intermediate substitutions,
  unfolding the `Eq2SigmaZeroMinusLower` definitional layer that sprint
  002 traverses via `simpa` (sprint 028 already returns the unfolded
  form), and verifying that the algebraic chain of `hStep1`, `hStep2`,
  `hRewrite`, `hCoeff1`, `hCoeff2` — i.e., the entire post-`h2`/`h3`
  body of sprint 002 — composes correctly with the substituted
  ingredients. The result is the **first workspace function-level
  inner-disk bound with a strictly-shrunk paper-axiom signature on an
  identical conclusion**.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~16 lines (sprint 002's signature is 12 lines
  plus 4 lines for the new summability premises and a `paper.eq4`
  invocation comment block).
* The proof body is ~110 lines — sprint 002's body verbatim (~105
  lines) plus ~5 lines of new `have` plumbing for sprints 027/028's
  hypothesis profiles.
* All Lean idioms used (`paper.eq4_sigmaPlus_bound`, `simpa
  [PaperAxioms.Eq4SigmaPlusBound]`, `mul_le_mul_of_nonneg_left`,
  `linarith`, `calc`, `ring`, `simp only [hA_def, mul_div_assoc']`)
  are verbatim from sprint 002's body. The two new ingredients (sprint
  027 and sprint 028) have already been shipped and exercise their
  hypothesis shapes in V27 and V28 side lemmas respectively.
* No new Mathlib lemma archaeology required.
* Estimate: ~110 lines for the new theorem. Candidate side lemmas
  ~30 lines each (showing the lemma's hypothesis shape and confirming
  the conclusion matches sprint 002's at concrete `(r, ρ)` values).
  Total V29 size: ≤ 130 lines.

Why this beats the alternatives I considered:

* **A: Series-level proof of `eq4`'s first conjunct `sigmaPlus r ≤
  sigmaPlus c` (sprint 028 contract candidate D, mirror of sprint
  011 on the N1 side).** Genuinely paper-axiom-free, would trim
  `paper.eq4`'s use in sprint 029 to just the second conjunct. **Demoted:
  too thin (one-direction termwise monotonicity, mirror of sprint
  011), and it does not unlock a *new* function-level chain — it
  marginally reduces the residual `paper.eq4` invocation in sprint
  029, but the paper-axiom signature stays `{eq4}` because Lean's
  signature is computed at the field-projection level (the entire
  `paper.eq4_sigmaPlus_bound` projection is one citation regardless
  of which conjuncts are used). Bundle into a follow-up cleanup sprint
  alongside the equivalent of sprint 005 for the second conjunct (if
  the latter is ever deemed in-scope).** Queueable as a 5-minute
  corollary alongside a larger sprint.

* **B: End-to-end closing reducer
  `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window` (D
  from sprint 026's contract).** Would compose sprint 026 with sprint
  006 to produce a closing reducer with paper-axiom signature `{eq4,
  eq8, eq9}`. **Demoted: mostly mechanical re-derivation of sprint
  014's body with sprint 026's disk-side substitution. Sprint 029 has
  higher analytical novelty per session because it materialises
  *both* sprints 027 and 028 simultaneously, while candidate B only
  materialises sprint 026 (and sprint 026 was already partially
  materialised in V26's side lemmas).** Queueable as a separate sprint
  later.

* **C: Termwise integration of sprint 027 to give a series-side
  closed-form `diskExcess` *identity* (not bound)** (B from sprints
  025/026/027 contracts). **Demoted: still requires
  `tsum_integral_eq_integral_tsum`-style swap-of-sum-and-integral
  machinery. Mathlib lemma archaeology risk per sprint 028's analysis.**
  Queueable separately.

* **D: A `sigmaPlus`-side analog of sprint 028 via convexity of
  `t ↦ t^k` on the *outer* radial regime** (J from sprint 028's
  contract). **Demoted: doesn't fit the inner-disk regime that
  downstream chains use. Would unlock annulus-side chains, but the
  annulus side is already well-served by sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` identity plus sprint
  006's integrated bound — there is no analogous `paper.eq2`-on-the-
  outer-side that needs a series-level discharge.** Queueable as a
  separate sprint exploring the annulus regime.

* **E: Direct paper-axiom-`eq3`-free counterpart of sprint 002 only
  (substitute sprint 027 alone, leave sprint 028 unsubstituted, keep
  `paper.eq2`).** **Demoted: paper-axiom signature reduces from
  `{eq2, eq3, eq4}` to `{eq2, eq4}` — non-trivial improvement, but
  strictly less impactful than candidate L (= sprint 029) which goes
  all the way to `{eq4}`. Since the substitution work for both is
  the same shape (just `paper.eq2` requires sprint 028's summability
  premise on the N2-indicator series), bundling them is the
  marginal-cost minimiser.** Subsumed by sprint 029.

* **F: Direct paper-axiom-`eq2`-free counterpart of sprint 002 only
  (substitute sprint 028 alone, leave sprint 027 unsubstituted, keep
  `paper.eq3`).** Symmetric to E. **Demoted: same reasoning as E.**
  Subsumed by sprint 029.

* **G: Replace sprint 022's branch-2 disk-side cross-validation with
  a fully-paper-axiom-free derivation by chaining sprint 029 with
  sprint 011's `Z`-monotonicity collapse.** Genuinely novel — would
  produce the first paper-axiom-free closed-form branch-2 disk bound
  `diskExcess ≤ (c⁴/2) · Z_ρ`. **Demoted: requires sprint 029 as
  prerequisite plus an integration step plus sprint 011's collapse.
  Multi-step sprint exceeds bounded-Generator-session budget.**
  Queueable as a follow-up to sprint 029.

* **H: A series-level proof of `eq4`'s second conjunct `sigmaPlus c
  ≤ sigmaMinus c`** (sprint 026 candidate K). **Demoted: not derivable
  from series structure alone per sprint 026's analysis.** Would
  require a paper axiom or oracle.

* **I: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted per the bulletin.**

* **J: Cross-validation lemma showing sprint 022's branch-2 bound and
  sprint 016's `eq6`-derived bound are pointwise equal** (sprint 022's
  forward roadmap). **Demoted: paper-internal cross-validation, not a
  new function-level chain.** Queueable separately.

* **K: Fold sprint 005's third-conjunct identity into sprint 029's
  proof body to additionally avoid `paper.eq4`'s third conjunct
  invocation.** As noted under candidate A, this does not reduce the
  paper-axiom *signature* (since `paper.eq4_sigmaPlus_bound` is one
  field projection regardless of which conjuncts are used inside the
  resulting bundled term). **Demoted: cosmetic, no signature impact.**

Compared to A–K, candidate L (this sprint, the function-level
composition of sprints 027 + 028 + paper.eq4 into a paper-axiom-`{eq4}`-
only inner-disk pointwise bound) maximises analytical novelty per
bounded Generator session: it ships the **first function-level inner-disk
bound with paper-axiom signature `{eq4}` only**, the **first downstream
materialisation of sprint 028 in a function-level chain**, and the
**first paper-axiom-strict-subset improvement of a prior workspace
function-level lemma's exact conclusion**. It uses **only existing
trusted modules + already-shipped sprints 005/027/028 + sprint 002's
algebraic skeleton** — no new Mathlib lemmas, no proposal needed, no
risk of Mathlib archaeology.

### Note on the summability premises

Sprint 027's hypothesis is `Summable (fun k => coeffPlusGap a b k *
r ^ (2 * k))` — the unconditioned `circleGapSeries` summand at the
*lower* radius `r`. Sprint 028's hypothesis is `Summable (fun k => if
n2Pred a b k then coeffMinusGap a b k * ρ ^ (2 * k - 2) else 0)` —
the N2-indicator-restricted summand at the *upper* radius `ρ`. These
two premises are independent: one is on the `r`-anchored unconditioned
plus-gap series, the other is on the `ρ`-anchored N2-restricted
minus-gap series. Both are routine summability conditions that
downstream consumers will need to discharge in their own context (e.g.,
from convergence of the underlying Bergman series at `r < 1` and
`ρ < 1`); sprint 029 keeps them as explicit hypotheses.

### Note on the `paper.eq4` field-projection

The signature still includes `paper : Section2Assumptions a b K c`
because `paper.eq4_sigmaPlus_bound` is invoked. The first conjunct
(`Σ⁺ r ≤ Σ⁺ c`) is series-derivable (mirror of sprint 011 on N1);
the third conjunct (`Σ⁻ c = c² · Z_c`) is sprint 005. Only the
**second conjunct** (`Σ⁺ c ≤ Σ⁻ c`) is non-derivable from series
structure (per sprint 026 contract analysis K). A full
paper-axiom-*free* version of sprint 029 would require either (a) a
new oracle/proposal for the second conjunct, or (b) a structurally
different chain that bypasses the second conjunct entirely. Neither
is in sprint 029's scope.

### Note on hypothesis-count growth

Sprint 002 has 5 hypothesis cells (paper, hr_nonneg, hr_lt, hcρ,
hρ1). Sprint 029 has 7 cells (the same five + two summability
premises). The two new cells are routine and do not affect downstream
consumer ergonomics (downstream `diskExcess`-bound chains will
discharge them once at the integration boundary). The pointwise
bound's *closed-form* expression is unchanged.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem circleGap_inner_bound_via_series_eq4_only
      {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
      (paper : Section2Assumptions a b K c)
      {r ρ : ℝ}
      (hr_nonneg : 0 ≤ r)
      (hr_lt : r < c)
      (hcρ : c < ρ)
      (hρ1 : ρ < 1)
      (hSummable_circleGap_r :
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
      (hSummable_n2_ρ :
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
          else 0)) :
      PaperAxioms.circleGap a b r ≤
        (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
            * PaperAxioms.sigmaZeroMinus a b c
          + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
            * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Estimated location: after sprint 028's
  `sigmaZeroMinus_lower_via_series_convexity` (around line 4290).
  Estimated ~110 lines.

  The proof body is sprint 002's body verbatim
  (`Reduction.lean:205-296`) with two surgical replacements:

  - At sprint 002 line 213 (`have h3 := paper.eq3_circleGap_decomposition
    ...`), replace with
    ```lean
    have h3 := circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
      a b hr_nonneg hSummable_circleGap_r
    ```
    (sprint 027's lemma already returns the equality in the unfolded
    form `circleGap r = sigmaPlus r - r² * sigmaZeroMinus r`, so the
    `simpa [PaperAxioms.Eq3CircleGapDecomposition]` step is unnecessary).

  - At sprint 002 line 235 (`have h2 := paper.eq2_sigmaZeroMinus_lower
    ...`), replace with
    ```lean
    have h2 := sigmaZeroMinus_lower_via_series_convexity
      a b hr_nonneg hr_lt hcρ hSummable_n2_ρ
    ```
    (sprint 028's lemma already returns the bound in the unfolded
    form, so the `simpa [PaperAxioms.Eq2SigmaZeroMinusLower]` step is
    unnecessary; the resulting `h2_unfold` step at line 237 collapses
    to a `have h2_unfold := h2` rebinding, or can be omitted entirely).

  All other proof body lines (213–296 of sprint 002) are verbatim.

- `ProofRefinement/Korenblum/Candidates/V29.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V28),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V28),
  4. Adds two side lemmas
     `v29_circleGap_inner_bound_via_series_eq4_only_compiles` and
     `v29_circleGap_inner_bound_via_series_eq4_only_recovers_sprint002_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — seven
       cells: `paper`, `hr_nonneg`, `hr_lt`, `hcρ`, `hρ1`,
       `hSummable_circleGap_r`, `hSummable_n2_ρ`. Concrete witness:
       pick `r := 1/10`, `ρ := 1/2` (or any `(r, ρ)` with
       `0 ≤ r < c_value < ρ < 1`).
     - `_recovers_sprint002_at_seed` demonstrates that the new lemma's
       conclusion is byte-for-byte identical to
       `circleGap_inner_bound_of_eq2_eq3_eq4`'s conclusion at the
       same `(r, ρ)` triple at the seed, *without* invoking
       `paper.eq2_sigmaZeroMinus_lower` or
       `paper.eq3_circleGap_decomposition` anywhere in the proof
       body. The sprint-002 lemma is invoked in the comment for
       cross-check only; the actual proof discharges through sprint
       029.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V28).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V29` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V29.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V29 ties V28 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V29.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `circleGap_inner_bound_via_series_eq4_only` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V29.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke**
   `paper.eq2_sigmaZeroMinus_lower` or
   `paper.eq3_circleGap_decomposition` anywhere — the sole
   `paper.*` field projection is `paper.eq4_sigmaPlus_bound`.
   Greppable check: in the body of
   `circleGap_inner_bound_via_series_eq4_only`, count of
   `paper.eq2` and `paper.eq3` substrings is 0; count of `paper.eq4`
   is exactly 1.
7. The proof body invokes
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   (sprint 027) at least once and
   `sigmaZeroMinus_lower_via_series_convexity` (sprint 028) at least
   once — the structural marker that sprint 029 materialises both
   sprints 027 and 028 in a function-level chain.

## Out of scope

- Edit older candidates V0–V28.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V29 is the
  same `hEq15_seed_3554` that V0–V28 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land a paper-axiom-*free* counterpart of sprint 029 (i.e., a chain
  that also discharges `paper.eq4`'s second conjunct). That requires
  a proposal or oracle for `Σ⁺ c ≤ Σ⁻ c` and is *not* in sprint 029's
  scope.
- Land a series-level proof of any `eq4` conjunct beyond the
  already-shipped sprint 005 (`sigmaMinus = c² · Z_c`). Specifically,
  do not bundle in candidate A (`sigmaPlus_monotone_via_series` for
  the first conjunct) — queue separately.
- Materialise sprint 029 in any *integrated* `diskExcess` bound
  (the natural follow-up sprint G fusing sprint 029 with the
  integration step in sprint 003 or sprint 022). That is the natural
  follow-up sprint *after* sprint 029 lands.
- Materialise sprint 029 in any closing reducer (i.e., do not consume
  sprint 029 inside `valid_of_*` lemmas yet — that is the second-order
  follow-up work).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
