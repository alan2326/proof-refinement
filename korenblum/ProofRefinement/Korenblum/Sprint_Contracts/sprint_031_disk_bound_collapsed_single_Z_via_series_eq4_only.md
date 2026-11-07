# Sprint 031: Branch-1 single-`Z` collapse of sprint 030's integrated two-`Z` `diskExcess` upper bound — the workspace's **first paper-axiom-`{eq4}`-only branch-1 single-`Z` `diskExcess` upper bound**, the **first downstream materialisation of sprint 030 in a branch-collapse chain**, and the **first paper-axiom-strict-subset improvement of sprint 007's exact branch-1 single-`Z` integrated-layer conclusion**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V30.lean`
**Target file**: `Candidates/V31.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2)
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
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
        * PaperAxioms.sigmaZeroMinus a b ρ
```

The conclusion is **byte-for-byte identical** to sprint 007's
`diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
(`Reduction.lean:597-636`). The hypothesis count grows by **exactly two
new summability premises** — `hSummable_circleGap` (quantified over
`r ∈ [0, c)`) and `hSummable_n2_ρ` (at the upper anchor `ρ`) — but the
*paper-axiom signature* shrinks from `{eq2, eq3, eq4}` (sprint 007) to
`{eq4}` only — sprint 027 discharges `eq3`, sprint 028 discharges
`eq2`, both wrapped inside sprint 030 (which sprint 031 consumes), and
the third conjunct of `eq4` remains accessible via sprint 005.

The proof body re-walks sprint 007's algebraic chain (the entire
40-line body, `Reduction.lean:611-636`) **verbatim**, with **exactly
one surgical replacement** at line 615-616:

1. **Sprint 003 invocation (line 615-616 of sprint 007).** Replace the
   call
   ```lean
   have hUpper :=
     diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt
   ```
   with
   ```lean
   have hUpper :=
     diskExcess_upper_bound_via_series_eq4_only_two_Z
       paper hc_pos hcρ hρ1 hSummable_circleGap hSummable_n2_ρ hInt
   ```
   The conclusion of `diskExcess_upper_bound_via_series_eq4_only_two_Z`
   is byte-for-byte identical to sprint 003's
   `diskExcess_upper_bound_of_eq2_eq3_eq4` (cf. sprint 030's contract
   acceptance criterion 6 and sprint 030's
   `_recovers_sprint003_at_seed` side lemma), so the downstream
   `linarith [hUpper, hαZc_nonpos]` step at sprint 007 line 636 succeeds
   verbatim.

2. **All other proof body lines (611-635 of sprint 007).** Verbatim
   reuse — the positivity of the denominator `ρ²−c²`, the
   `sigmaZeroMinus_nonneg_of_pos` invocation at `c`, the algebraic
   non-positivity argument for the `Z_c` coefficient on the
   branch-split sub-regime (`hNumNonpos`, `hc4_nonneg`, `hα_nonpos`,
   `hαZc_nonpos`), and the closing `linarith` are all unchanged
   because they operate on sprint 003's conclusion shape, which sprint
   030 reproduces.

The proof body is structurally **sprint 007's body verbatim** with
exactly one `have hUpper := ...` line swapped to invoke sprint 030
(passing through both summability premises). Estimated body length:
~40 lines (sprint 007 is 40 lines; the swap adds ~1 line for the
hypothesis plumbing).

Then ship a `Candidates/V31.lean` at the same `c = 0.3554` that
compiles, scores `≥ V30 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v31_disk_bound_collapsed_single_Z_via_series_eq4_only_compiles` and
`v31_disk_bound_collapsed_single_Z_via_series_eq4_only_recovers_sprint007_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. After sprint 030, the workspace has its first **integrated
two-`Z` `diskExcess` upper bound with paper-axiom signature `{eq4}`
only**. Sprint 031 lifts that integrated two-`Z` bound to its
**branch-1-collapsed single-`Z`** form — which is the input shape that
the closing-reducer cone of branch-1 single-`Z` reducers (sprint 008,
sprint 019, sprint 021) consumes.

After sprint 031 lands, the workspace has its **first integrated
single-`Z` branch-1 collapsed `diskExcess` upper bound whose transitive
proof body invokes exactly one paper axiom** (`paper.eq4_sigmaPlus_bound`,
inside sprint 029, inside sprint 030), where every prior workspace
integrated single-`Z` branch-1 collapsed `diskExcess` bound consumes
either two or three distinct `paper.eq*` fields:

| Sprint | Result | Paper-axiom signature |
|--------|--------|-----------------------|
| 007    | `diskExcess ≤ (c⁶/6)/(ρ²−c²)·Z_ρ` (single-Z, branch-1 collapse of sprint 003) | `{eq2, eq3, eq4}` |
| 015    | `diskExcess ≤ branch1SigmaKernel·ρ²·Z_ρ` (single-Z, branch-1, via `(5)`) | `{eq5}` (+ sprint 005) |
| **031** | `diskExcess ≤ (c⁶/6)/(ρ²−c²)·Z_ρ` (single-Z, branch-1 collapse of sprint 030) | **`{eq4}`** |

The structural firsts:

1. **First integrated single-`Z` branch-1 collapsed `diskExcess` upper
   bound with paper-axiom signature `{eq4}` only.** Strictly smaller
   than sprint 007's `{eq2, eq3, eq4}`. Sprint 015's `{eq5}` signature
   is also single-axiom but on a structurally different
   parameterisation (`branch1SigmaKernel·ρ²·Z_ρ` vs sprint 007/031's
   `(c⁶/6)/(ρ²−c²)·Z_ρ` — the closed-form coefficients are
   *algebraically equal* on `(c, branchSplit c]` by sprint 022's
   forward roadmap candidate iii, but the parameterisations differ).
   Sprint 031 is the **first** branch-1 single-`Z` bound preserving
   sprint 007's exact closed-form coefficient `(c⁶/6)/(ρ²−c²)` while
   shrinking the paper-axiom signature.

2. **First workspace lemma to *materialise* sprint 030 in a
   branch-collapse chain.** Sprint 030 is currently a standalone
   integrated two-`Z` `diskExcess` upper bound with no downstream
   consumer that collapses it; sprint 031 is its first load-bearing
   consumption inside a branch-collapse single-`Z` bound. Greppable
   check: `grep -c "diskExcess_upper_bound_via_series_eq4_only_two_Z"`
   in `Reduction.lean` rises from 1 (declaration only at line 4432) to
   ≥ 2 (declaration + use site in sprint 031) after sprint 031.

3. **First workspace lemma whose paper-axiom signature is a *strict
   subset* of an earlier sprint's signature on the same conclusion
   shape, at the branch-1 single-`Z` integrated layer.** Sprint 007's
   conclusion is byte-for-byte identical to sprint 031's; sprint 031's
   paper-axiom signature is `{eq4}`, strictly a subset of sprint 007's
   `{eq2, eq3, eq4}`. This generalises sprint 030's integrated-layer
   strict-subset improvement (over sprint 003) to the *branch-collapse*
   layer — the structural marker that the entire transitive
   `Reduction.lean` cone rooted at sprint 007 (sprint 007 itself plus
   the closing reducers `valid_of_eq10_subinterval_branch1`,
   `valid_of_eq5_eq8_eq9_subinterval_branch1`,
   `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`) admits a
   paper-axiom-`{eq4}`-only re-routing.

4. **Quantitative downstream impact.** Sprint 031 is the prerequisite
   for the future paper-axiom-`{eq4, eq8, eq9}`-only branch-1 closing
   reducer that fuses sprint 031's branch-1 single-`Z` disk bound with
   sprint 006's `(8)+(9)`-derived annulus bound — the branch-1
   counterpart of the natural sprint-030+sprint-006 full-window closing
   reducer. This would be the workspace's first single-branch closing
   reducer with paper-axiom signature `{eq4, eq8, eq9}`, strictly
   smaller than any existing closing reducer's signature on the
   branch-1 sub-regime. **Out of scope for sprint 031** to keep the
   bounded-Generator-session budget.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V31 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form integrated
  branch-1 single-`Z` `diskExcess` upper bound with the same RHS as
  sprint 007 but a strictly smaller paper-axiom signature.

Why this is **not** "the same chain" as sprint 007:

* **Different paper-axiom signature.** Sprint 007 transitively consumes
  `paper.eq2`, `paper.eq3`, `paper.eq4` (through its dependency on
  sprint 003). Sprint 031 transitively consumes only `paper.eq4`.
  **Strict subset reduction.**
* **Different transitive dependencies.** Sprint 007 depends on sprint
  003 (which composes paper axioms directly through sprint 002).
  Sprint 031 depends on sprint 030 (which depends on sprint 029, which
  in turn depends on sprints 027, 028, 005) as load-bearing
  intermediaries — sprint 031 is the *branch-collapse* layer
  re-anchoring of the entire series-derived `eq2`/`eq3`/`eq4`-third-
  conjunct cone built by sprints 005/027/028/029/030.
* **Different summability discipline.** Sprint 007 has zero
  summability premises. Sprint 031 has two: a quantified one on the
  `circleGap` series at every `r ∈ [0, c)` (for sprint 029's first
  hypothesis, lifted through sprint 030) and a single-anchor one on
  the N2-restricted `coeffMinusGap` series at `ρ` (for sprint 029's
  second hypothesis, lifted through sprint 030). This is the trade-off
  — sprint 031 needs series-level summability premises that sprint 007
  hides inside the paper-axiom black box.

Why this is **not** "the same chain" as sprint 030:

* **Different conclusion shape.** Sprint 030 ships the *two*-`Z` form
  `diskExcess ≤ A(c,ρ)·Z_c + B(c,ρ)·Z_ρ` (two anchors, `c` and `ρ`).
  Sprint 031 ships the *single*-`Z` form `diskExcess ≤
  (c⁶/6)/(ρ²−c²)·Z_ρ` (one anchor at `ρ` only) on the
  branch-1 sub-regime `(c, branchSplit c]`. The single-`Z` form is
  qualitatively narrower (it requires the additional hypothesis
  `3·ρ² ≤ 4·c²` confining `ρ` to the lower branch sub-regime) but
  qualitatively cleaner (it eliminates the `Z_c` summand entirely,
  making the bound directly comparable to sprint 015's branch-1
  single-`Z` bound and directly consumable by closing reducers like
  sprint 008's `valid_of_eq10_subinterval_branch1`).
* **Different downstream consumer profile.** Sprint 030 unlocks
  paper-axiom-`{eq4}`-only inputs for full-window closing reducers
  (sprint 014's natural `{eq4, eq8, eq9}` mirror). Sprint 031 unlocks
  paper-axiom-`{eq4}`-only inputs for branch-1 single-`Z` closing
  reducers (sprint 008's natural `{eq4, eq8, eq9}` mirror, sprint
  019's natural `{eq4, eq8, eq9}` mirror). The two sprints serve
  *different downstream consumer cones*.

Why this is **not** "the same chain" as sprint 015:

* **Different parameterisation of the closed-form coefficient.** Sprint
  015 ships `branch1SigmaKernel c ρ · ρ² · Z_ρ` (a kernel function of
  `(c, ρ)` derived through `paper.eq5_branch1_sigmaReduction`). Sprint
  031 ships `(c⁶/6)/(ρ²−c²) · Z_ρ` (sprint 003's exact closed-form
  RHS, branch-collapsed). The two coefficients are *algebraically
  equal* on `(c, branchSplit c]` but their *parameterised forms*
  differ — sprint 015's form exposes the kernel function, sprint 031's
  form exposes sprint 003's polynomial-over-polynomial closed form.
* **Different paper-axiom path.** Sprint 015 uses `paper.eq5` directly
  to short-circuit the integration. Sprint 031 uses `paper.eq4` only,
  through the integration via sprint 030. Both have single-axiom
  signatures but the axioms are disjoint.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~24 lines (sprint 007's signature is 14 lines
  plus ~10 lines for the two new summability premises and 1 line of
  comment lifting).
* The proof body is ~40 lines — sprint 007's body verbatim (40 lines)
  plus ~1 line of new `have hUpper := ...` plumbing for sprint 030's
  hypothesis profile.
* All Lean idioms used (`nlinarith`, `mul_nonpos_of_nonneg_of_nonpos`,
  `div_nonpos_of_nonpos_of_nonneg`, `mul_nonpos_of_nonpos_of_nonneg`,
  `linarith`) are verbatim from sprint 007's body. The new ingredient
  (sprint 030) has already been shipped and exercised in V30's side
  lemmas.
* No new Mathlib lemma archaeology required.
* Estimate: ~40 lines for the new theorem. Candidate side lemmas ~30
  lines each (showing the lemma's hypothesis shape and confirming the
  conclusion matches sprint 007's at concrete `(c, ρ)` values, where
  `ρ ∈ (c, branchSplit c]` is non-empty at the seed because sprint 007
  already exercises this regime — `branchSplit (3554/10000) ≈
  0.4103`, and any `ρ ∈ (0.3554, 0.4103]` works; sprint 015's V15
  uses `ρ = 0.38`, sprint 022's V22 uses `ρ = 1/2 > branchSplit
  c_value` (branch-2), so for branch-1 we'll use `ρ := 0.4` matching
  sprint 015's regime).
* Total V31 size: ≤ 130 lines.

Why this beats the alternatives I considered:

* **A: Branch-2 collapse of sprint 030 via sprint 011 monotonicity
  bridge (mirror of sprint 022 rooted at sprint 030, paper-axiom-
  `{eq4}`-only counterpart of sprint 022).** Genuinely novel —
  produces the first paper-axiom-`{eq4}`-only branch-2 single-`Z`
  collapsed disk bound. **Demoted: requires three load-bearing
  intermediaries (sprint 030 + sprint 011's monotonicity + sprint
  022's `field_simp; ring` algebraic identity). The sprint 011
  invocation needs a third summability premise at `c` (or transferred
  from `ρ` via sprint 012), pushing the hypothesis count from 6 cells
  to 8 cells. Marginally exceeds the 1-Generator-session budget when
  combined with the surrounding plumbing for the convex-combination
  monotonicity argument. Queueable as a separate sprint 032.**
  Sprint 031 (branch-1 collapse) is the simpler, lower-risk twin —
  the `Z_c` summand is *dropped* (single sign argument) rather than
  *absorbed* (sign argument + monotonicity bridge + algebraic
  collapse identity). Both are distinct chains; sprint 031 ships
  first.

* **B: End-to-end full-window closing reducer
  `valid_of_disk_eq4_only_annulus_eq8_eq9_full_window` fusing sprint
  030 + sprint 006 (D from sprints 026/030 contracts).** Would
  produce the workspace's first paper-axiom-`{eq4, eq8, eq9}`-only
  end-to-end closing reducer. **Demoted: requires re-walking sprint
  014's body (~155 lines) verbatim with one substitution. The body
  is dense with annulus-side integrability plumbing, summability
  cascades through sprints 011/012, and the cross-anchor monotonicity
  bridge from `Z_c` to `Z_ρ'`. Sprint 014's body is the longest
  single closing-reducer body in `Reduction.lean` (line 1686-1841),
  exceeding the 1-Generator-session budget. Queueable as a separate
  sprint after sprint 031 lands, when the branch-1 disk-side input
  is already in `{eq4}` form.**

* **C: A `sigmaPlus`-side analog of sprint 028 via N1 termwise
  monotonicity (sprint 028 contract candidate D, mirror of sprint
  011 on the `sigmaPlus` side).** Genuinely paper-axiom-free, would
  trim sprint 029's residual `paper.eq4` invocation to just the
  second conjunct. **Demoted: too thin (one-direction termwise
  monotonicity, mirror of sprint 011), and the paper-axiom *signature*
  stays `{eq4}` because Lean's signature counts the entire
  `paper.eq4_sigmaPlus_bound` field projection regardless of which
  conjuncts are used. Marginal value compared to sprint 031, which
  unlocks an entirely new branch-collapse layer.** Queueable as a
  cleanup sprint.

* **D: Termwise integration of sprint 027 (or sprint 025) to give a
  series-side closed-form `diskExcess` *identity* via swap-of-sum-
  and-integral.** Requires `MeasureTheory.tsum_integral_eq_integral_tsum`
  -style machinery in the pinned Mathlib. **Demoted: Mathlib lemma
  archaeology risk per sprint 028's analysis. Genuinely novel but
  high-risk for a single Generator session.** Queueable separately.

* **E: A series-level proof of `paper.eq4`'s second conjunct
  `sigmaPlus c ≤ sigmaMinus c` to make sprint 030 *fully* paper-axiom-
  free.** **Demoted: not derivable from series structure alone per
  sprint 026 contract analysis K. Would require a paper axiom or
  oracle proposal.** Out of sprint 031's scope.

* **F: Branch-1 *and* branch-2 collapse of sprint 030 in the same
  sprint (combined sprint 031+032).** **Demoted: exceeds bounded-
  Generator-session budget. Sprint 031 ships the simpler half
  (branch-1, single sign argument); sprint 032 will ship the
  branch-2 half if approved.**

* **G: A `sigmaZeroMinus` *upper* bound (companion to sprint 028's
  lower bound) via termwise concavity.** **Demoted: `t ↦ t^(k-1)`
  is convex on `[0, ∞)` for `k ≥ 1`, not concave, so the dual
  argument doesn't apply directly. Would require a different convexity
  argument (e.g., on `t ↦ -t^(k-1)` is concave, but only on bounded
  intervals where the bound is meaningful). Higher analytical risk;
  unclear if a useful bound is derivable. Queueable as `Scratch/`
  exploration.**

* **H: Paper-internal cross-validation that sprint 030's bound and
  sprint 003's bound are pointwise equal (i.e., a corollary that they
  agree at every `(c, ρ, Z_c, Z_ρ)`).** **Demoted: trivial — the
  conclusions are byte-for-byte identical; no separate cross-validation
  lemma needed. The materialisation in V30's
  `_recovers_sprint003_at_seed` side lemma already provides the
  equivalent structural fact.**

* **I: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted per the bulletin.**

Compared to A–I, candidate (this sprint, the branch-1 single-`Z`
collapse of sprint 030 via sprint 007's algebraic skeleton) maximises
analytical novelty per bounded Generator session: it ships the **first
paper-axiom-`{eq4}`-only branch-1 single-`Z` collapsed `diskExcess`
upper bound**, the **first downstream materialisation of sprint 030 in
a branch-collapse chain**, and the **first paper-axiom-strict-subset
improvement of sprint 007's exact branch-1 single-`Z` integrated-layer
conclusion**. It uses **only existing trusted modules + already-shipped
sprints 007/030 + sprint 007's collapse skeleton** — no new Mathlib
lemmas, no proposal needed, no risk of Mathlib archaeology.

### Note on the summability premises

Sprint 030's two summability premises (`hSummable_circleGap` quantified
over `r ∈ [0, c)`, and `hSummable_n2_ρ` at the upper anchor `ρ`) are
inherited verbatim by sprint 031 — no new summability discipline is
introduced. The branch-1 collapse argument operates entirely on sprint
030's *conclusion shape* (the two-`Z` closed-form upper bound) without
re-touching the underlying series.

### Note on the `paper.eq4` field-projection

The signature still includes `paper : Section2Assumptions a b K c`
because sprint 030 (which sprint 031 consumes) invokes
`paper.eq4_sigmaPlus_bound` (inside sprint 029's body). Sprint 031's
*direct* proof body invokes zero `paper.eq*` fields — it only consumes
sprint 030's bound and sprint 006's `sigmaZeroMinus_nonneg_of_pos`
(itself paper-axiom-free).

### Note on the branch-split sub-regime hypothesis `hρ_branch`

Sprint 031 inherits sprint 007's `hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2`
hypothesis verbatim. This is the *necessary* hypothesis for the
branch-1 collapse: it is precisely the condition under which the `Z_c`
coefficient `α(c, ρ) := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-positive, so
that dropping the `α·Z_c` summand from sprint 003/030's two-`Z` upper
bound preserves the inequality direction. The hypothesis is equivalent
to `ρ ≤ branchSplit c` (where `branchSplit c = c · √(4/3)` ≈ `1.155·c`).

### Note on hypothesis-count growth

Sprint 007 has 5 hypothesis cells (paper, hc_pos, hcρ, hρ_branch, hρ1,
hInt — 6 counting `paper`). Sprint 031 has 8 cells (the same six + two
summability premises). The two new cells are routine and paper-axiom-
free. Closing reducers consuming sprint 031 will need to discharge
both summability premises once at the boundary.

### Note on the witness `ρ` value at the seed

Sprint 015 (the only other workspace branch-1 single-`Z` disk bound)
uses `ρ = 0.38` at the seed (`branchSplit(3554/10000) ≈ 0.4103`, so
the branch-1 sub-regime is `(0.3554, 0.4103]`). Sprint 031's V31
candidate file should use a witness `ρ` in the same regime. Concrete
choice: `ρ := 4/10` (= 0.4), which satisfies `c_value < ρ ≤
branchSplit c_value` because:
- `c_value = 3554/10000 = 0.3554 < 0.4`,
- `branchSplit c_value = c_value · √(4/3) ≥ c_value · (115/100) =
  3554·115/1000000 = 408710/1000000 ≈ 0.4087`, so `0.4 ≤ branchSplit
  c_value`,
- equivalently, `3·(0.4)² = 0.48` and `4·(0.3554)² ≈ 0.5052`, so
  `3·ρ² ≤ 4·c²` holds.
This `ρ` value also satisfies `ρ < 1`. The `hρ_branch` hypothesis is
discharged via `norm_num` once sprint 031's V31 plugs in the concrete
witnesses for `c_value` and `ρ`.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only
      {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
      (paper : Section2Assumptions a b K c)
      {ρ : ℝ}
      (hc_pos : 0 < c)
      (hcρ : c < ρ)
      (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2)
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
        (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Estimated location: after sprint 030's
  `diskExcess_upper_bound_via_series_eq4_only_two_Z` (around line
  4577). Estimated ~40 lines.

  The proof body is sprint 007's body verbatim (`Reduction.lean:611-636`)
  with one surgical replacement at sprint 007 line 615-616:

  - Replace
    ```lean
    have hUpper :=
      diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt
    ```
    with
    ```lean
    have hUpper :=
      diskExcess_upper_bound_via_series_eq4_only_two_Z
        paper hc_pos hcρ hρ1 hSummable_circleGap hSummable_n2_ρ hInt
    ```

  All other proof body lines (611-614, 617-636 of sprint 007) are
  verbatim. The conclusion of
  `diskExcess_upper_bound_via_series_eq4_only_two_Z` is byte-for-byte
  identical to sprint 003's, so the downstream `linarith [hUpper,
  hαZc_nonpos]` step at sprint 007 line 636 succeeds without
  modification.

- `ProofRefinement/Korenblum/Candidates/V31.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V30),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V30),
  4. Adds two side lemmas
     `v31_disk_bound_collapsed_single_Z_via_series_eq4_only_compiles`
     and
     `v31_disk_bound_collapsed_single_Z_via_series_eq4_only_recovers_sprint007_at_seed`
     exercising the new generic lemma:
     - `_compiles` exhibits the new lemma's hypothesis shape — eight
       cells: `paper`, `hc_pos`, `hcρ`, `hρ_branch`, `hρ1`,
       `hSummable_circleGap` (quantified over `r ∈ Ioo 0 c`),
       `hSummable_n2_ρ` (at the upper anchor `ρ`), and `hInt`.
       Concrete witness: pick `ρ := 4/10` (so `c_value < ρ < 1` and
       `3·ρ² ≤ 4·c²` at the seed; see the "Note on the witness `ρ`
       value at the seed" section above).
     - `_recovers_sprint007_at_seed` demonstrates that the new lemma's
       conclusion is byte-for-byte identical to
       `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`'s
       conclusion at the same `ρ` value at the seed, *without*
       invoking `paper.eq2_sigmaZeroMinus_lower` or
       `paper.eq3_circleGap_decomposition` anywhere in the proof
       body. The sprint-007 lemma is invoked in the comment for
       cross-check only; the actual proof discharges through sprint
       031.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V30).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V31` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V31.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V31 ties V30 at the
   seed; the new lemma is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V31.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V31.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke**
   `paper.eq2_sigmaZeroMinus_lower` or
   `paper.eq3_circleGap_decomposition` anywhere — the only paper-axiom
   invocations in the *transitive* proof body trace through
   `diskExcess_upper_bound_via_series_eq4_only_two_Z` to sprint 029
   to `paper.eq4_sigmaPlus_bound`. Greppable check: in the body of
   `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`,
   the count of `paper.eq2`, `paper.eq3`, `paper.eq4`, `paper.eq5`,
   `paper.eq6`, `paper.eq7`, `paper.eq8`, `paper.eq9`, `paper.eq10`,
   `paper.eq11`, `paper.eq12`, `paper.eq13`, `paper.eq14`,
   `paper.eq15` substrings is **0**.
7. The proof body invokes
   `diskExcess_upper_bound_via_series_eq4_only_two_Z` (sprint 030) at
   least once — the structural marker that sprint 031 materialises
   sprint 030 in a branch-collapse chain. Greppable check:
   `grep -c "diskExcess_upper_bound_via_series_eq4_only_two_Z"` in the
   body of
   `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only` is
   at least 1.
8. The proof body **does not invoke**
   `diskExcess_upper_bound_of_eq2_eq3_eq4` (sprint 003) anywhere — the
   structural marker that sprint 031 takes the series-derived
   integrated bound, not sprint 003's paper-axiom-`{eq2, eq3, eq4}`
   integrated bound. Greppable check: count of
   `diskExcess_upper_bound_of_eq2_eq3_eq4` substrings in the body of
   `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only` is
   0.

## Out of scope

- Edit older candidates V0–V30.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V31 is the
  same `hEq15_seed_3554` that V0–V30 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land a paper-axiom-*free* counterpart of sprint 031 (i.e., a chain
  that also discharges `paper.eq4`'s second conjunct). That requires
  a proposal or oracle for `Σ⁺ c ≤ Σ⁻ c` and is *not* in sprint 031's
  scope.
- Land a series-level proof of any `eq4` conjunct beyond the
  already-shipped sprint 005 (`sigmaMinus = c² · Z_c`). Specifically,
  do not bundle in candidate C
  (`sigmaPlus_monotone_via_series` for the first conjunct) — queue
  separately.
- Materialise sprint 031 in any closing reducer (i.e., do not consume
  sprint 031 inside `valid_of_*` lemmas yet — that is the second-order
  follow-up work, the natural sprint-031+sprint-006 branch-1 closing
  reducer with paper-axiom signature `{eq4, eq8, eq9}`).
- Land the branch-2 counterpart (sprint 031's natural twin via sprint
  011's monotonicity bridge — alternative A above). Queueable as
  sprint 032 after sprint 031 lands.
- Series-derive the `hInt` integrability premise (would require a
  series-level continuity argument on `circleGapSeries` lifted under
  `IntervalIntegrable`; queueable separately).

## Time budget

≤ 60 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
