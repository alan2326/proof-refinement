# Sprint 030: Integrated two-`Z` `diskExcess` upper bound via composition of sprint 029 + sprint 003's integration skeleton — the workspace's **first integrated `diskExcess` bound that preserves sprint 003's two-`Z` (two-radius parameterised) closed-form `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)·Z_c + (c⁶/6)/(ρ²−c²)·Z_ρ` while shrinking the paper-axiom signature from `{eq2, eq3, eq4}` (sprint 003) to `{eq4}` only**, and the **first downstream materialisation of sprint 029 in an integrated chain**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V29.lean`
**Target file**: `Candidates/V30.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_series_eq4_only_two_Z
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c
        + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ
```

The closed-form RHS is **byte-for-byte identical** to sprint 003's
`diskExcess_upper_bound_of_eq2_eq3_eq4`
(`Reduction.lean:304-435`). The hypothesis count grows by **exactly two
new summability premises**:

* `hSummable_circleGap` is sprint 029's `circleGap` series summability,
  but quantified uniformly over `r ∈ [0, c)` — necessary because the
  `Step A` pointwise-bound construction in sprint 003's body invokes
  the inner-disk lemma at every `r ∈ Ioo 0 c`. This matches the shape
  of sprint 026's first summability premise (`Reduction.lean:3782-3785`).
* `hSummable_n2_ρ` is sprint 029's N2-restricted minus-gap series
  summability at the *single* upper anchor `ρ` (no quantification
  over `r`, because the summability premise is at `ρ`, not at the
  inner-disk variable).

The *paper-axiom signature* shrinks from `{eq2, eq3, eq4}` (sprint 003)
to `{eq4}` only — sprint 027 discharges `eq3`, sprint 028 discharges
`eq2`, both are already wrapped inside sprint 029, and the third
conjunct of `eq4` remains accessible via sprint 005 (which sprint 003
also implicitly relies on through `paper.eq4`'s third conjunct, both
through sprint 002 and now through sprint 029).

The proof body re-walks sprint 003's algebraic chain (Step A through
Step F, `Reduction.lean:328-435`) **verbatim**, with **exactly one
surgical replacement** at Step A:

1. **Step A (`hPointwise`, lines 328-346 of sprint 003).** Replace the
   call
   ```lean
   have hBound :=
     circleGap_inner_bound_of_eq2_eq3_eq4 paper hr_nonneg hr_lt hcρ hρ1
   ```
   with
   ```lean
   have hBound :=
     circleGap_inner_bound_via_series_eq4_only
       paper hr_nonneg hr_lt hcρ hρ1
       (hSummable_circleGap hr_nonneg hr_lt) hSummable_n2_ρ
   ```
   The conclusion of `circleGap_inner_bound_via_series_eq4_only` is
   byte-for-byte identical to sprint 002's
   `circleGap_inner_bound_of_eq2_eq3_eq4` (cf. sprint 029's contract
   acceptance criterion 5), so the downstream `simpa [hu_def, hZc_def,
   hZρ_def] using hBound` rewrite at sprint 003 line 345 succeeds
   verbatim.

2. **Steps B–F (lines 347-435 of sprint 003).** Verbatim reuse — the
   algebraic decomposition of the upper bound into
   `A_coef·r + B_coef·r³ + C_coef·r⁵`, the integration via
   `integral_pow` and `integral_const_mul`, the closed-form
   rearrangement via `field_simp; ring`, and the final `calc` chain to
   `diskExcess` are all unchanged because they operate on sprint 002's
   conclusion shape, which sprint 029 reproduces.

The proof body is structurally **sprint 003's body verbatim** with
exactly one `have hBound := ...` line swapped to invoke sprint 029
(passing through both summability premises). Estimated body length: ~115
lines (sprint 003 is 113 lines; the swap adds ~2 lines for the
hypothesis plumbing).

Then ship a `Candidates/V30.lean` at the same `c = 0.3554` that
compiles, scores `≥ V29 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v30_disk_bound_via_series_eq4_only_two_Z_compiles` and
`v30_disk_bound_via_series_eq4_only_two_Z_recovers_sprint003_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. After sprint 029, the workspace has its first **pointwise**
inner-disk bound with paper-axiom signature `{eq4}`. Sprint 030 lifts
that pointwise bound to the **integrated** layer that downstream
closing reducers actually consume.

After sprint 030 lands, the workspace has its **first integrated
two-`Z` `diskExcess` upper bound whose transitive proof body invokes
exactly one paper axiom** (`paper.eq4_sigmaPlus_bound`), where every
prior workspace integrated two-`Z` `diskExcess` bound consumes either
two or three distinct `paper.eq*` fields:

| Sprint | Result | Paper-axiom signature |
|--------|--------|-----------------------|
| 003    | `diskExcess ≤ A·Z_c + B·Z_ρ` (two-Z, full window) | `{eq2, eq3, eq4}` |
| 007    | `diskExcess ≤ B·Z_ρ` (single-Z, branch-1)         | `{eq2, eq3, eq4}` |
| 013    | `diskExcess ≤ c⁴·Z_c` (single-Z, full window)     | `{eq3, eq4}` |
| 015    | `diskExcess ≤ branch1SigmaKernel·ρ²·Z_ρ` (single-Z, branch-1) | `{eq5}` (+ sprint 005) |
| 016    | `diskExcess ≤ (c⁴/2)·Z_ρ` (single-Z, branch-2)    | `{eq6}` (+ sprint 005) |
| 022    | `diskExcess ≤ (c⁴/2)·Z_ρ` (single-Z, branch-2)    | `{eq2, eq3, eq4}` (+ sprint 011) |
| 026    | `diskExcess ≤ c⁴·Z_c` (single-Z, full window, series-side) | `{eq4}` |
| **030** | `diskExcess ≤ A·Z_c + B·Z_ρ` (two-Z, full window) | **`{eq4}`** |

Sprint 026 was the first **integrated single-Z** disk bound with
paper-axiom signature `{eq4}`. Sprint 030 is the first **integrated
two-Z** disk bound with that same signature — and unlike sprint 026,
sprint 030 preserves the **two-radius parameterisation** `(c, ρ)` and
the **two-Z structure** that the downstream branch-collapse cone
exploits (sprint 007 collapses sprint 003 by dropping the `Z_c` summand
on branch-1; sprint 022 collapses sprint 003 by absorbing `Z_c` into
`Z_ρ` on branch-2 via sprint 011).

The structural firsts:

1. **First integrated two-`Z` `diskExcess` upper bound with paper-axiom
   signature `{eq4}` only.** Strictly smaller than sprint 003's
   `{eq2, eq3, eq4}`. This is qualitatively significant: the entire
   downstream cone of branch-collapse integrated bounds (sprint 007's
   branch-1 collapse, sprint 022's branch-2 collapse) gains a
   sprint-030-rooted counterpart with one paper axiom instead of three,
   *while preserving the two-`Z` finesse* — sprint 026's bound is
   strictly weaker in the two-`Z` sense (it is the single-`Z` form
   `c⁴·Z_c` obtained by chaining sprint 002's three conjuncts of
   `paper.eq4_sigmaPlus_bound` to anchor everything at `c`).

2. **First workspace lemma to *materialise* sprint 029 in an integrated
   chain.** Sprint 029 is currently a standalone series-derived
   pointwise inequality with no downstream consumer that integrates it;
   sprint 030 is its first load-bearing consumption inside an integrated
   `diskExcess` bound. Greppable check:
   `grep -c "circleGap_inner_bound_via_series_eq4_only"` in
   `Reduction.lean` rises from 1 (declaration only at line 4300) to
   ≥ 2 (declaration + use site in sprint 030) after sprint 030.

3. **First workspace lemma whose paper-axiom signature is a *strict
   subset* of an earlier sprint's signature on the same conclusion
   shape, at the integrated layer.** Sprint 003's conclusion is
   byte-for-byte identical to sprint 030's; sprint 030's paper-axiom
   signature is `{eq4}`, strictly a subset of sprint 003's
   `{eq2, eq3, eq4}`. This generalises sprint 029's pointwise-layer
   strict-subset improvement to the *integrated* layer — the structural
   marker that the entire transitive `Reduction.lean` cone rooted at
   sprint 003 (sprints 003, 007, 022, plus the closing reducers
   `valid_of_disk_eq3_eq4_*`, `valid_of_disk_eq6_*`,
   `valid_of_disk_eq2_eq3_eq4_collapse_*`) admits a paper-axiom-`{eq4}`-
   only re-routing.

4. **Quantitative downstream impact.** Sprint 030 is the prerequisite
   for paper-axiom-`{eq4}`-only counterparts of:
   * sprint 007 (`diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
     → `diskExcess_collapsed_single_Z_via_series_eq4_only` — drops the
     `Z_c` summand on `(c, branchSplit c]` to give a `Z_ρ`-only bound,
     paper-axiom-`{eq4}`-only counterpart of sprint 007);
   * sprint 022 (`diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
     → `diskExcess_branch2_collapse_via_series_eq4_only` — collapses the
     two `Z` summands into a single `(c⁴/2)·Z_ρ` form on branch-2 via
     sprint 011, paper-axiom-`{eq4}`-only counterpart of sprint 022);
   * a future `valid_of_disk_eq4_only_annulus_eq8_eq9_full_window` end-to-
     end closing reducer with paper-axiom signature `{eq4, eq8, eq9}`,
     strictly smaller than sprint 014's `{eq3, eq4, eq8, eq9}`.

   These three follow-up sprints are queueable but **out of scope for
   sprint 030** to keep the bounded-Generator-session budget.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V30 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form integrated
  `diskExcess` upper bound with the same RHS as sprint 003 but a
  strictly smaller paper-axiom signature.

Why this is **not** "the same chain" as sprint 003:

* **Different paper-axiom signature.** Sprint 003 transitively consumes
  `paper.eq2`, `paper.eq3`, `paper.eq4` (through its dependency on
  sprint 002). Sprint 030 transitively consumes only `paper.eq4`.
  **Strict subset reduction.**
* **Different transitive dependencies.** Sprint 003 depends on sprint
  002 (which composes paper axioms directly). Sprint 030 depends on
  sprint 029 (which depends on sprints 027, 028, and indirectly 005)
  as load-bearing intermediaries — sprint 030 is the *integrated layer*
  re-anchoring of the entire series-derived `eq2`/`eq3`/`eq4`-third-
  conjunct cone built by sprints 005/027/028/029.
* **Different summability discipline.** Sprint 003 has zero summability
  premises. Sprint 030 has two: a quantified one on the `circleGap`
  series at every `r ∈ [0, c)` (for sprint 029's first hypothesis) and
  a single-anchor one on the N2-restricted `coeffMinusGap` series at
  `ρ` (for sprint 029's second hypothesis). This is the trade-off —
  sprint 030 needs series-level summability premises that sprint 003
  hides inside the paper-axiom black box.

Why this is **not** "the same chain" as sprint 026:

* **Different conclusion shape.** Sprint 026 ships the *single*-`Z`
  form `diskExcess ≤ c⁴ · sigmaZeroMinus a b c` (one anchor at `c`,
  no `ρ`-dependence on the RHS). Sprint 030 ships the *two*-`Z` form
  `diskExcess ≤ A(c,ρ)·Z_c + B(c,ρ)·Z_ρ` (two anchors, `c` and `ρ`,
  with `ρ` as a free parameter `> c`). The two-`Z` structure is
  qualitatively richer: sprint 022 collapses sprint 003's two-`Z` into
  a single-`Z` form `(c⁴/2)·Z_ρ` on branch-2 by absorbing `Z_c` into
  `Z_ρ` via sprint 011's monotonicity (needs the `Z_c` summand to start
  with); sprint 026's single-`Z` `c⁴·Z_c` cannot be collapsed in this
  way. Sprint 030 thus unlocks paper-axiom-`{eq4}`-only versions of
  the entire branch-1 / branch-2 collapse cone that sprint 026 cannot
  reach.
* **Different upstream paper-axiom usage pattern.** Sprint 026 uses
  `paper.eq4_sigmaPlus_bound` to chain `sigmaPlus r ≤ sigmaPlus c ≤
  sigmaMinus c = c² · Z_c` (anchoring at `c` *before* integration —
  this is what produces the single-`Z` form). Sprint 030's chain via
  sprint 029 uses `paper.eq4_sigmaPlus_bound` differently: sprint 029
  combines `paper.eq4` with sprint 028's `Z_r ≥ μ_1·Z_c − μ_2·Z_ρ`
  cross-radius lower bound to expose the `(c, ρ)` two-anchor form
  *before* multiplying by `2r` and integrating. The final integrated
  result therefore retains `Z_ρ`-dependence even though both bounds
  share the `{eq4}` paper-axiom signature.

Why this is **not** "the same chain" as sprint 029:

* **Different layer.** Sprint 029 is *pointwise* on `circleGap a b r`
  for fixed `r`. Sprint 030 is *integrated* over `r ∈ [0, c]` against
  the polar Jacobian `2r`, giving `diskExcess` directly.
* **Different downstream consumer profile.** Sprint 029 unlocks
  paper-axiom-`{eq4}`-only pointwise inputs for any chain that
  integrates `circleGap` (potentially many: integration windows, polar
  weights, branch-restricted intervals). Sprint 030 commits to the
  full-window `[0, c]` integration with the polar Jacobian `2r`,
  matching exactly the shape that downstream `valid_of_*` reducers
  consume.

Why this is **not** a numerical / mechanical push:

* The composition is **load-bearing**: sprint 030 is the first
  workspace lemma in which the *integrated* `diskExcess` shape inherits
  *both* of sprint 029's series-level summability premises through the
  integral. The quantification of `hSummable_circleGap` over `r ∈
  [0, c)` mirrors sprint 026's pattern but combined with sprint 029's
  two-radius parameterisation produces a **new hypothesis profile** in
  the workspace: a quantified summability premise at the lower anchor
  `r` *plus* a single-anchor summability premise at the upper anchor
  `ρ`, both flowing through the same integrated bound. The first cell
  is paper-axiom-free (sprint 027's hypothesis shape, lifted under
  `∀ r ∈ Ioo 0 c`); the second cell is paper-axiom-free (sprint 028's
  hypothesis shape at the upper anchor). Validating that this
  hypothesis profile composes cleanly through sprint 003's integration
  skeleton is the analytical contribution of sprint 030.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~21 lines (sprint 003's signature is 11 lines
  plus 8 lines for the two new summability premises and 2 lines of
  comment lifting).
* The proof body is ~115 lines — sprint 003's body verbatim (~113
  lines) plus ~2 lines of new `have hBound := ...` plumbing for sprint
  029's hypothesis profile.
* All Lean idioms used (`mul_le_mul_of_nonneg_left`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`, `@integral_pow 0 c n`,
  `convert h using 2 <;> norm_num`,
  `intervalIntegral.integral_const_mul`, `field_simp; ring`,
  `change AnnulusIntegralReduction.annulusSlice ... = _ ; rfl`,
  closing `calc`) are verbatim from sprint 003's body. The new
  ingredient (sprint 029) has already been shipped and exercised in
  V29's side lemmas.
* No new Mathlib lemma archaeology required.
* Estimate: ~115 lines for the new theorem. Candidate side lemmas
  ~30 lines each (showing the lemma's hypothesis shape and confirming
  the conclusion matches sprint 003's at concrete `(c, ρ)` values).
  Total V30 size: ≤ 130 lines.

Why this beats the alternatives I considered:

* **A: Series-level proof of `eq4`'s first conjunct `sigmaPlus r ≤
  sigmaPlus c` via N1 termwise monotonicity (sprint 028 contract
  candidate D, mirror of sprint 011).** Genuinely paper-axiom-free,
  would trim sprint 029's residual `paper.eq4` invocation to just the
  second conjunct. **Demoted: too thin (one-direction termwise
  monotonicity, mirror of sprint 011), and the paper-axiom *signature*
  stays `{eq4}` because Lean's signature counts the entire
  `paper.eq4_sigmaPlus_bound` field projection regardless of which
  conjuncts are used. Marginal value compared to sprint 030, which
  unlocks an entirely new integrated-layer lemma.** Queueable as a
  cleanup sprint after sprint 030.

* **B: End-to-end closing reducer
  `valid_of_disk_eq4_only_annulus_eq8_eq9_full_window` (D from sprint
  026's contract).** Would compose sprint 030 *or* sprint 026 with
  sprint 006's `(8)+(9)`-derived annulus bound. **Demoted: requires
  sprint 030 as prerequisite (or restricts to the single-`Z` sprint-026
  shape, which makes the closing reducer strictly weaker than sprint
  014's full-window kernel `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ` because sprint
  026 anchors the disk side at `c` itself, eliminating the `ρ`
  parameter on the disk side and forcing kernel comparison `c⁴·Z_c
  ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ·Z_{ρ'}` — equivalent only after `Z`-monotonicity
  collapse, which adds another layer). With sprint 030 in hand, the
  closing reducer becomes a clean sprint-014 mirror with
  `paper.eq3_circleGap_decomposition` excised. **Mostly mechanical
  re-derivation of sprint 014's body with sprint 030's disk-side
  substitution. Sprint 030 has higher analytical novelty per session
  because it materialises sprint 029 in the integrated layer for the
  first time, while candidate B is the natural follow-up sprint
  *after* sprint 030 lands.** Queueable as a separate sprint later.

* **C: Termwise integration of sprint 027 to give a series-side
  closed-form `diskExcess` *identity* (not bound).** Requires
  `MeasureTheory.tsum_integral_eq_integral_tsum`-style swap-of-sum-
  and-integral machinery in the pinned Mathlib. **Demoted: Mathlib
  lemma archaeology risk per sprint 028's analysis. Genuinely novel
  but high-risk for a single Generator session.** Queueable separately.

* **D: A `sigmaPlus`-side analog of sprint 028 via convexity of
  `t ↦ t^k` on the *outer* radial regime.** **Demoted: doesn't fit
  the inner-disk regime that downstream chains use. Would unlock
  annulus-side chains, but the annulus side is already well-served
  by sprint 005's identity plus sprint 006's integrated bound — there
  is no analogous `paper.eq2`-on-the-outer-side that needs a
  series-level discharge.** Queueable as a separate sprint exploring
  the annulus regime.

* **E: Direct integration of sprint 029 to yield the *single*-`Z` form
  `diskExcess ≤ c⁴·Z_c` (i.e., a sprint-026 mirror via sprint 029
  instead of sprint 025).** **Demoted: sprint 026 already exists with
  paper-axiom signature `{eq4}` via the inequality-drop route. The
  equality-substitution route via sprint 027 (or sprint 029) would
  produce an algebraically identical bound through a structurally
  different path — paper-internal cross-validation only, not a new
  conclusion. Queueable as a structural-cross-validation sprint after
  sprint 030 lands.**

* **F: Branch-1 collapse of sprint 030 (drop the `Z_c` summand on
  `(c, branchSplit c]` to give `diskExcess ≤ B·Z_ρ`,
  paper-axiom-`{eq4}`-only counterpart of sprint 007).** Genuinely
  novel — would produce the first paper-axiom-`{eq4}`-only branch-1
  collapsed disk bound. **Demoted: requires sprint 030 as prerequisite
  plus sprint 007's branch-split algebra. Multi-step sprint exceeds
  bounded-Generator-session budget.** Queueable as the natural
  follow-up to sprint 030.

* **G: Branch-2 collapse of sprint 030 via sprint 011 (absorb `Z_c`
  into `Z_ρ` on branch-2 to give `diskExcess ≤ (c⁴/2)·Z_ρ`,
  paper-axiom-`{eq4}`-only counterpart of sprint 022).** Same shape as
  candidate F. **Demoted: requires sprint 030 as prerequisite plus
  sprint 011's monotonicity bridge plus sprint 022's algebraic
  identity. Multi-step sprint exceeds bounded-Generator-session
  budget.** Queueable as a follow-up after sprint 030.

* **H: A series-level proof of `eq4`'s second conjunct `sigmaPlus c ≤
  sigmaMinus c`** (sprint 026 candidate K). **Demoted: not derivable
  from series structure alone per sprint 026's analysis.** Would
  require a paper axiom or oracle.

* **I: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted per the bulletin.**

* **J: Paper-internal cross-validation that sprint 030's bound and
  sprint 003's bound are pointwise equal (i.e., a corollary that they
  agree at every `(c, ρ, Z_c, Z_ρ)`).** **Demoted: trivial — the
  conclusions are byte-for-byte identical; no separate cross-validation
  lemma needed. The materialisation in V30's `_recovers_sprint003_at_seed`
  side lemma is sufficient.**

Compared to A–J, candidate (this sprint, the integrated counterpart of
sprint 029 via sprint 003's integration skeleton) maximises analytical
novelty per bounded Generator session: it ships the **first integrated
two-`Z` `diskExcess` upper bound with paper-axiom signature `{eq4}`
only**, the **first downstream materialisation of sprint 029 in an
integrated chain**, and the **first paper-axiom-strict-subset
improvement of a prior workspace integrated lemma's exact conclusion**.
It uses **only existing trusted modules + already-shipped sprints
003/029 + sprint 003's integration skeleton** — no new Mathlib lemmas,
no proposal needed, no risk of Mathlib archaeology.

### Note on the summability premises

Sprint 029's first hypothesis is `Summable (fun k => coeffPlusGap a b k *
r ^ (2 * k))` at a *single* radius `r`. Sprint 030 quantifies this
over `r ∈ Ioo 0 c` because sprint 003's `Step A` (lines 328-346)
invokes the inner-disk pointwise bound at every `r ∈ Ioo 0 c`. The
precise universe quantifier shape `∀ ⦃r : ℝ⦄, 0 ≤ r → r < c → Summable
...` matches sprint 026's pattern (`Reduction.lean:3782-3785`).

Sprint 029's second hypothesis is at the upper anchor `ρ`, which is a
single fixed value in sprint 030's signature (it is the same `ρ` as in
the conclusion's RHS). No quantification is needed for this premise.

Both summability premises are paper-axiom-free hypothesis shapes — they
mention only series objects (`coeffPlusGap`, `coeffMinusGap`, `n2Pred`)
defined in `KorenblumPaper.PaperAxioms` without consuming any
`Section2Assumptions` field. Downstream consumers of sprint 030 will
need to discharge them in their own context (e.g., from convergence of
the underlying Bergman series at `r < 1` and `ρ < 1`).

### Note on the `paper.eq4` field-projection

The signature still includes `paper : Section2Assumptions a b K c`
because sprint 029 (which sprint 030 consumes) invokes
`paper.eq4_sigmaPlus_bound`. Per sprint 029's contract, only the
**second conjunct** of `paper.eq4_sigmaPlus_bound` (`Σ⁺ c ≤ Σ⁻ c`) is
non-derivable from series structure. A full paper-axiom-*free* version
of sprint 030 would require a proposal/oracle for `Σ⁺ c ≤ Σ⁻ c`. Out
of scope for sprint 030.

### Note on hypothesis-count growth

Sprint 003 has 4 hypothesis cells (paper, hc_pos, hcρ, hρ1, hInt — 5
counting `paper`). Sprint 030 has 7 cells (the same five + two
summability premises). The two new cells are routine and paper-axiom-
free. Closing reducers consuming sprint 030 will need to discharge
both summability premises once at the boundary.

### Note on the `hInt` integrability premise

Sprint 030 inherits sprint 003's `hInt : IntervalIntegrable (fun r =>
2 * r * PaperAxioms.circleGap a b r) volume 0 c` premise verbatim.
This is **not** a new dependency introduced by sprint 030 — it is
sprint 003's own integrability premise, kept identical because the
integration skeleton in Step C and beyond (lines 371-435 of sprint
003) needs it to apply `intervalIntegral.integral_mono_on_of_le_Ioo`.
Series-derivation of `hInt` is queueable as a separate sprint (it
would require a series-level continuity or measurability argument on
`circleGapSeries` lifted under integration), but is **out of scope**
for sprint 030.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem diskExcess_upper_bound_via_series_eq4_only_two_Z
      {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
      (paper : Section2Assumptions a b K c)
      {ρ : ℝ}
      (hc_pos : 0 < c)
      (hcρ : c < ρ)
      (hρ1 : ρ < 1)
      (hSummable_circleGap :
        ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
      (hSummable_n2_ρ :
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
          else 0))
      (hInt :
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b c
          + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Estimated location: after sprint 029's
  `circleGap_inner_bound_via_series_eq4_only` (around line 4420).
  Estimated ~115 lines.

  The proof body is sprint 003's body verbatim (`Reduction.lean:318-435`)
  with one surgical replacement at sprint 003 line 338-339:

  - Replace
    ```lean
    have hBound :=
      circleGap_inner_bound_of_eq2_eq3_eq4 paper hr_nonneg hr_lt hcρ hρ1
    ```
    with
    ```lean
    have hBound :=
      circleGap_inner_bound_via_series_eq4_only
        paper hr_nonneg hr_lt hcρ hρ1
        (hSummable_circleGap hr_nonneg hr_lt) hSummable_n2_ρ
    ```

  All other proof body lines (319-435 of sprint 003) are verbatim. The
  conclusion of `circleGap_inner_bound_via_series_eq4_only` is
  byte-for-byte identical to sprint 002's, so the downstream `simpa
  [hu_def, hZc_def, hZρ_def] using hBound` step at line 345 succeeds
  without modification.

- `ProofRefinement/Korenblum/Candidates/V30.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V29),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V29),
  4. Adds two side lemmas
     `v30_disk_bound_via_series_eq4_only_two_Z_compiles` and
     `v30_disk_bound_via_series_eq4_only_two_Z_recovers_sprint003_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — seven
       cells: `paper`, `hc_pos`, `hcρ`, `hρ1`, `hSummable_circleGap`
       (quantified over `r ∈ Ioo 0 c`), `hSummable_n2_ρ` (at the upper
       anchor `ρ`), and `hInt`. Concrete witness: pick `ρ := 1/2`
       (so `c_value < ρ < 1` at the seed).
     - `_recovers_sprint003_at_seed` demonstrates that the new lemma's
       conclusion is byte-for-byte identical to
       `diskExcess_upper_bound_of_eq2_eq3_eq4`'s conclusion at the
       same `ρ` value at the seed, *without* invoking
       `paper.eq2_sigmaZeroMinus_lower` or
       `paper.eq3_circleGap_decomposition` anywhere in the proof
       body. The sprint-003 lemma is invoked in the comment for
       cross-check only; the actual proof discharges through sprint
       030.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V29).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V30` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V30.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V30 ties V29 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V30.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `diskExcess_upper_bound_via_series_eq4_only_two_Z` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V30.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke**
   `paper.eq2_sigmaZeroMinus_lower` or
   `paper.eq3_circleGap_decomposition` anywhere — the only paper-axiom
   invocations in the *transitive* proof body trace through
   `circleGap_inner_bound_via_series_eq4_only` to
   `paper.eq4_sigmaPlus_bound`. Greppable check: in the body of
   `diskExcess_upper_bound_via_series_eq4_only_two_Z`, count of
   `paper.eq2` and `paper.eq3` substrings is 0; count of `paper.eq4`
   substrings is 0 (paper.eq4 is invoked only inside sprint 029's
   body, not directly inside sprint 030's body).
7. The proof body invokes
   `circleGap_inner_bound_via_series_eq4_only` (sprint 029) at least
   once — the structural marker that sprint 030 materialises sprint
   029 in an integrated chain. Greppable check:
   `grep -c "circleGap_inner_bound_via_series_eq4_only"` in the body
   of `diskExcess_upper_bound_via_series_eq4_only_two_Z` is at least 1.
8. The proof body **does not invoke**
   `circleGap_inner_bound_of_eq2_eq3_eq4` (sprint 002) anywhere — the
   structural marker that sprint 030 takes the series-derived
   inner-disk bound, not sprint 002's paper-axiom-`{eq2,eq3,eq4}`
   inner-disk bound. Greppable check: count of
   `circleGap_inner_bound_of_eq2_eq3_eq4` substrings in the body of
   `diskExcess_upper_bound_via_series_eq4_only_two_Z` is 0.

## Out of scope

- Edit older candidates V0–V29.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V30 is the
  same `hEq15_seed_3554` that V0–V29 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land a paper-axiom-*free* counterpart of sprint 030 (i.e., a chain
  that also discharges `paper.eq4`'s second conjunct). That requires
  a proposal or oracle for `Σ⁺ c ≤ Σ⁻ c` and is *not* in sprint 030's
  scope.
- Land a series-level proof of any `eq4` conjunct beyond the
  already-shipped sprint 005 (`sigmaMinus = c² · Z_c`). Specifically,
  do not bundle in candidate A (`sigmaPlus_monotone_via_series` for
  the first conjunct) — queue separately.
- Materialise sprint 030 in any branch-1 or branch-2 collapsed
  `diskExcess` bound (the natural follow-up sprints F and G fusing
  sprint 030 with sprint 007's branch-1 algebra or sprint 011's
  monotonicity bridge for branch-2 collapse). Those are the natural
  follow-up sprints *after* sprint 030 lands.
- Materialise sprint 030 in any closing reducer (i.e., do not consume
  sprint 030 inside `valid_of_*` lemmas yet — that is the second-order
  follow-up work, candidate B).
- Series-derive the `hInt` integrability premise (would require a
  series-level continuity argument on `circleGapSeries` lifted under
  `IntervalIntegrable`; queueable separately).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
