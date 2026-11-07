# Sprint 026: Closed-form full-disk upper bound `diskExcess ≤ c⁴ · sigmaZeroMinus c` via sprint 025 + `eq4` only — first paper-internal cross-validation that sprint 013's bound is derivable through a **disjoint paper-axiom signature** `{eq4}` instead of `{eq3, eq4}`, and the workspace's first integrated disk bound whose transitive proof body invokes **zero** uses of `paper.eq3_circleGap_decomposition`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V25.lean`
**Target file**: `Candidates/V26.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_circleGapSeries_eq4_only
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) MeasureTheory.volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c
```

The proof chain, in order:

1. **Pointwise upper bound on `circleGap r` for `r ∈ Ioo 0 c`** by chaining
   sprint 025's `circleGap_le_sigmaPlus_via_series_split` with the **first
   conjunct** of `paper.eq4_sigmaPlus_bound`. Specifically, for any
   `r ∈ Ioo 0 c`:

   * Sprint 025: `circleGap a b r ≤ sigmaPlus a b r` (consumes the
     summability premise `hSummable hr.1.le hr.2` at radius `r`; **no
     paper-axiom invocation**).
   * `paper.eq4_sigmaPlus_bound hr.1.le hr.2 hc_lt_one`'s first conjunct:
     `sigmaPlus a b r ≤ sigmaPlus a b c`.
   * `paper.eq4_sigmaPlus_bound hr.1.le hr.2 hc_lt_one`'s second conjunct
     plus the `c²·Z_c` identity (third conjunct): `sigmaPlus a b c ≤
     sigmaMinus a b c = c² · sigmaZeroMinus a b c`.
   * Compose: `circleGap a b r ≤ c² · sigmaZeroMinus a b c`.

2. **Multiply the pointwise bound by the polar Jacobian `2r ≥ 0`** to
   obtain `2r · circleGap a b r ≤ 2r · c² · sigmaZeroMinus a b c` on
   `Ioo 0 c`.

3. **Integrate over `[0, c]`** via
   `intervalIntegral.integral_mono_on_of_le_Ioo` (the same Mathlib lemma
   sprint 003 uses at `Reduction.lean` lines ~640-700). The RHS integral
   collapses in closed form: `∫_{0}^{c} 2r · c² · Z_c dr =
   c² · Z_c · ∫_{0}^{c} 2r dr = c² · Z_c · c² = c⁴ · sigmaZeroMinus a b c`.
   The LHS integral is `diskExcess (circleGap a b) c` by definition
   (`PaperAxioms.diskExcess` unfolds to
   `AnnulusIntegralReduction.annulusSlice circleGap 0 c` which in turn
   unfolds to `∫ r in 0..c, 2 * r * circleGap r` — sprint 003's body
   already pivots on this exact identity). Conclude
   `diskExcess (circleGap a b) c ≤ c⁴ · sigmaZeroMinus a b c`.

This bound is **algebraically identical** to sprint 013's
`diskExcess_upper_bound_via_eq3_eq4`, but the **transitive paper-axiom
signature** is strictly smaller:

| Bound | Paper-axiom signature | Workspace lemmas consumed |
|-------|----------------------|---------------------------|
| Sprint 013 | `{eq3, eq4}` | `sigmaZeroMinus_nonneg_of_pos` |
| Sprint 026 | `{eq4}` | `circleGap_le_sigmaPlus_via_series_split` (sprint 025) |

The closed-form output is identical (`diskExcess ≤ c⁴ · sigmaZeroMinus a b c`)
on the same admissible region (the full disk `[0, c]`, no `ρ`-window, no
`branchSplit` constraint), but sprint 026 demonstrates that the bound is
derivable **without ever invoking `paper.eq3_circleGap_decomposition`** —
which is the structural marker that sprint 025's series-level identity
is *strictly stronger* than sprint 013 needed `eq3` to be.

Then ship a `Candidates/V26.lean` at the same `c = 0.3554` that
compiles, scores `≥ V25 = 1777/5000`, and *materialises* the new lemma
in side lemmas
`v26_disk_bound_via_circleGapSeries_eq4_only_compiles` and
`v26_disk_bound_signature_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. The bulletin **explicitly names** as a high-value axis:

> chain different paper equations — try `eq3` decomposition + `eq4`
> `Σ⁺` bound + `eq8`/`eq9` lift bridges + `eq10`/`eq11` pointwise
> + `eq12`/`eq13` integrated forms in combinations the seed doesn't use,
> without going through `eq14_combined` or `Eq15ScalarBound`

Sprint 026 ships the workspace's **first** integrated disk bound whose
proof body invokes `paper.eq4` but **not** `paper.eq3`. This is a
genuinely novel paper-axiom combination — *every* prior workspace
disk-side bound consumes either `{eq3, eq4}` (sprint 013), `{eq2, eq3,
eq4}` (sprints 002/003/007/022), `{eq5}` (sprint 015), or `{eq6}`
(sprint 016). No prior workspace bound uses `eq4` standalone (without
`eq3`).

The structural firsts:

1. **First workspace disk bound with paper-axiom signature `{eq4}` only.**
   Greppable verification: every prior disk-side `_upper_bound_*` lemma
   in `Proof/Reduction.lean` either invokes `paper.eq3` (sprints 002,
   003, 007, 013, 022) or `paper.eq5`/`paper.eq6` (sprints 015, 016).
   Sprint 026 lands the **first** disk-side bound that consumes
   `paper.eq4` *standalone*. The transitive trace through workspace
   lemmas is `circleGap_le_sigmaPlus_via_series_split` (sprint 025,
   paper-axiom-free) → `paper.eq4_sigmaPlus_bound` → integration
   machinery (`intervalIntegral.*`). Greppable check via
   `#print axioms diskExcess_upper_bound_via_circleGapSeries_eq4_only`
   should not list any `paper.eq3` use.

2. **First paper-internal cross-validation that sprint 013's
   `{eq3, eq4}` bound is achievable through a strictly smaller paper-
   axiom signature `{eq4}`.** Mirrors sprint 022's cross-validation
   pattern (sprint 022 showed sprint 016's `{eq6}` branch-2 bound is
   achievable through `{eq2, eq3, eq4}`), but inverted — instead of
   replacing one paper axiom with three, sprint 026 replaces two paper
   axioms with one. The structural information transferred from
   `paper.eq3` to sprint 025 is the **inequality direction**
   `circleGap r ≤ sigmaPlus r` — which sprint 025 proved is provable
   from series structure alone without `eq3`. After sprint 026 lands,
   the workspace has a **proof-shaped demonstration** that `eq3` is
   *strictly stronger than necessary* for the disk-side bound: the
   inequality direction, which is all sprint 013 actually used from
   `eq3`, is provable from series structure.

3. **First integrated workspace bound that consumes a workspace-internal
   pointwise series bound.** Sprint 025's
   `circleGap_le_sigmaPlus_via_series_split` is a pointwise `circleGap`
   bound at the series-representation level. Sprint 026 is the first
   workspace lemma to *integrate* a series-level pointwise bound over
   `[0, c]`, opening a new analytical-composition pattern: pointwise
   series bounds → integrated disk bounds via the `2r` Jacobian. This
   pattern is structurally distinct from the existing
   `diskExcess_upper_bound_*` lemmas which all integrate
   `paper.eq3`/`paper.eq5`/`paper.eq6`-derived pointwise bounds.

4. **Composition novelty: sprint 025's first downstream consumer.**
   Sprint 025 lands as a structural pointwise lemma without immediate
   downstream use. Sprint 026 is the **first** workspace lemma to
   consume `circleGap_le_sigmaPlus_via_series_split`, demonstrating
   the lemma's role as a foundational bridge between the
   `circleGapSeries`-level structural results and the function-level
   integrated bounds that closing reducers depend on.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V26 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form integrated upper
  bound on `diskExcess` parameterised by `(a, b, c)`, the summability
  family at radii `r < c`, and the `2r·circleGap` integrability
  hypothesis (mirroring sprint 003's hypothesis shape).

Why this is **not** "the same chain" as sprint 013:

* **Disjoint paper-axiom signature.** Sprint 013 consumes `eq3 + eq4`.
  Sprint 026 consumes **only `eq4`**. The pointwise-bound step that
  sprint 013 derives from `eq3` (the rearrangement `circleGap r =
  sigmaPlus r − r²·Z_r ≤ sigmaPlus r` via `r²·Z_r ≥ 0`) is replaced
  in sprint 026 by sprint 025's series-level identity-direction
  inequality (the rearrangement `circleGapSeries r =
  ∑'_{n1Pred} coeffPlusGap·r^(2k) + ∑'_{n2Pred} coeffPlusGap·r^(2k) ≤
  ∑'_{n1Pred} coeffPlusGap·r^(2k) = sigmaPlus r` via N2-summands ≤ 0).
  These are **structurally disjoint chains** — sprint 013's path uses
  `eq3` as a paper hypothesis, sprint 026's path uses no paper axiom
  for the corresponding step.
* **Disjoint workspace dependency.** Sprint 013 consumes
  `sigmaZeroMinus_nonneg_of_pos` (sprint 005's `Z ≥ 0` lemma). Sprint
  026 does **not** consume this — sprint 025 already discharges the
  termwise-dropping argument internally via `pow_le_pow_left₀` plus
  `pow_nonneg`.
* **Disjoint summability hypothesis shape.** Sprint 013 takes no
  summability hypothesis (it lives at the function level). Sprint 026
  takes a uniform summability hypothesis over `r ∈ [0, c)`, which is
  the natural cost of the series-level approach.

Why this is **not** "the same chain" as sprint 025:

* **Different statement type.** Sprint 025 is a *pointwise* inequality
  on `circleGap a b r ≤ sigmaPlus a b r` at a single radius `r`.
  Sprint 026 is an *integrated* inequality on `diskExcess ≤ c⁴ · Z_c`,
  obtained by integrating sprint 025's pointwise bound (after further
  pointwise compression via `eq4`).
* **Different paper-axiom signature.** Sprint 025 consumes **zero**
  paper axioms. Sprint 026 consumes `paper.eq4_sigmaPlus_bound`. These
  are different layers of the analytical chain.
* **Different role.** Sprint 025 is a structural pointwise lemma
  (foundational bridge). Sprint 026 is a closed-form integrated bound
  on `diskExcess` (composable with `annulusExcess`-side lower bounds
  in future closing reducers, e.g., the future sprint that fuses
  sprint 026 with sprint 006 for an end-to-end `{eq4, eq8, eq9}`-only
  reducer — strictly fewer paper axioms than any current closing
  reducer).

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~10 lines; the proof body is ~50–80 lines,
  modeled directly on sprint 003's body (`Reduction.lean` lines ~640-700)
  with the pointwise-bound step replaced by a 5-line composition of
  sprint 025 with `paper.eq4_sigmaPlus_bound`.
* The proof structure is:
  1. Establish the pointwise bound `∀ r ∈ Ioo 0 c, circleGap a b r ≤
     c² · sigmaZeroMinus a b c` by combining sprint 025 (`circleGap r ≤
     sigmaPlus r`) with `paper.eq4_sigmaPlus_bound` (the chain
     `sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c² · sigmaZeroMinus c`).
  2. Multiply by `2r ≥ 0` to get `2r · circleGap a b r ≤
     2r · c² · sigmaZeroMinus a b c` on `Ioo 0 c`.
  3. Integrate via `intervalIntegral.integral_mono_on_of_le_Ioo`
     (sprint 003's exact pattern). The RHS is integrable as a constant
     times a polynomial; the LHS integrability is the explicit
     hypothesis.
  4. Compute the RHS integral in closed form: `∫_{0}^{c} 2r · c² · Z_c dr
     = c² · Z_c · c² = c⁴ · Z_c`. (Use `integral_const_mul` and the
     `∫₀^c 2r dr = c²` identity, both already verified in sprint 003.)
  5. Identify the LHS as `diskExcess (circleGap a b) c` via the
     `PaperAxioms.diskExcess` definitional unfold and
     `AnnulusIntegralReduction.annulusSlice` definitional unfold (both
     verified in sprint 003 / sprint 015).
* All Lean idioms used (`intervalIntegral.integral_mono_on_of_le_Ioo`,
  `integral_const_mul`, `integral_pow`, `pow_nonneg`, `linarith`,
  `nlinarith`, `field_simp`, `ring`) are **already verified at the
  cited line ranges** in sprint 003.
* Estimate: ~80 lines for the new theorem, dominated by the
  pointwise-bound composition (~20 lines) and the integration step
  (~50 lines, mostly book-keeping for the closed-form RHS evaluation).
  The candidate side lemmas are 10–25 lines each. Total V26 size:
  ≤ 100 lines.

Why this beats the alternatives I considered:

* **A: Sprint 011-style series-level monotonicity for `sigmaPlus`
  (`s ≤ t → sigmaPlus a b s ≤ sigmaPlus a b t`).** Reproduces the
  *forward* direction of `eq4`'s first conjunct from series structure
  alone (paper-axiom-free). Algebraically clean but the analytical
  payoff is lower — sprint 011 already gives the analogous result for
  `sigmaZeroMinus`, and adding the `sigmaPlus` counterpart is a
  symmetric generalisation that doesn't open a new chain. **Demoted:
  marginal novelty, doesn't unlock a new closing-reducer signature.**

* **B: Termwise integration of sprint 025 to give a series-side
  closed-form `diskExcess ≤ ∑'_{n1Pred} coeffPlusGap a b k · c^(2k+2)/(k+1)`.**
  Genuinely novel, would be the workspace's first series-level
  integrated bound. However, requires `MeasureTheory.tsum_integral_eq_integral_tsum`
  or `hasSum_integral_of_summable_norm`-style swap-of-sum-and-integral
  machinery, which is non-trivial Mathlib. The exact lemma signatures
  in the pinned Mathlib version may not cleanly match — risk of
  consuming a Generator session on Mathlib lemma archaeology rather
  than actual proof construction. **Demoted: high risk for one bounded
  session; can be queued as a follow-up after 026 lands sprint 025's
  first downstream consumer.**

* **C: Series-level proof of `eq3` itself** (the equality
  `circleGap r = sigmaPlus r − r²·sigmaZeroMinus r` from `tsum`
  identity). Cleaner than sprint 025's inequality-direction bound and
  fully validates `eq3` from series structure. Requires
  `Summable.tsum_add` plus an arithmetic identity proof that
  `n1Pred + n2Pred = ⊤` partition holds termwise as a sum identity.
  **Demoted: same analytical layer as sprint 025 (peer rather than
  consumer); doesn't open a new closing-reducer signature; requires
  delicate `tsum_add` manipulations that risk exceeding the session
  budget.** A future planner can queue this after sprint 026.

* **D: A reducer using `eq4` standalone (without `eq3`/`eq5`/`eq6`
  on the disk side) plus `(8)+(9)` on the annulus side.** Would be
  the closing-reducer counterpart of sprint 026 — an end-to-end
  `ValidKorenblumBound c` reducer with paper-axiom signature
  `{eq4, eq8, eq9}`, strictly smaller than any current closing
  reducer (sprint 014 uses `{eq3, eq4, eq8, eq9}`; sprint 017 uses
  `{eq6, eq8, eq9}`; sprint 023 uses `{eq2, eq3, eq4, eq8, eq9}`).
  **Demoted: needs sprint 026 first.** The natural sequencing is
  026 → reducer in a follow-up sprint, mirroring the
  013 → 014 sequencing. Closing-reducer kernel inequality would be
  identical to sprint 014's `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`, with
  the same admissible window, so D doesn't unlock new numerical
  territory either — it's a paper-axiom-signature optimisation.

* **E: A series-side disk bound `diskExcess ≤ c² · sigmaPlus c`**
  (intermediate stop, *before* chaining `sigmaPlus c ≤ sigmaMinus c =
  c²·Z_c`). This is what alternative D in sprint 025's contract names
  but requires only the *first* conjunct of `eq4`. Cleaner statement
  (one fewer `eq4`-conjunct to invoke), but the closed-form RHS
  `c² · sigmaPlus c` is not in the same form as any existing closing
  reducer's kernel inequality. **Considered but demoted in favor of
  K1 (sprint 026)**: chaining all three conjuncts of `eq4` lands the
  bound in the canonical form `c⁴·Z_c` that exactly matches sprint
  013's RHS, maximising the cross-validation novelty (same closed-form
  output, smaller paper-axiom signature). The intermediate `c² ·
  sigmaPlus c` form can be queued as a separate follow-up if useful.

* **F: A `circleGapSeries`-direct *lower* bound on `diskExcess` from
  series structure.** Demoted in sprint 025's contract analysis (no
  lower bound on `sigmaPlus` available from current trust surface).

* **G: A reducer for branch-2 by chaining sprint 025 with `eq6`
  instead of `eq4`.** `eq6` doesn't compose with `circleGap r ≤
  sigmaPlus r` on the disk side — `eq6` already directly gives a
  `diskExcess ≤ branch2SigmaKernel · sigmaMinus ρ` bound (sprint 016
  reduces this to `(c⁴/2) · sigmaZeroMinus ρ`). **Demoted: structural
  mismatch — sprint 025 produces `circleGap r ≤ sigmaPlus r`, not
  `circleGap r ≤ sigmaMinus ρ`, so chaining with `eq6` is a non-sequitur.**

* **H: Numerical push of any prior reducer at the seed.** Requires
  closed-form `paperLambda` envelope or numerical oracle — not in
  scope. **Still demoted.**

* **I: Strengthen sprint 025's hypothesis to absolute summability
  (`Summable (fun k => |coeffPlusGap a b k| · r^(2k))`)** to make the
  termwise-comparison summability transfer cleaner. **Out of scope:
  modifies sprint 025's signature, would require V25 edit (forbidden).**

* **J: A `sigmaPlus`-monotone cousin of sprint 011 at the series level
  (`s ≤ t → sigmaPlus a b s ≤ sigmaPlus a b t` from `coeffPlusGap a b k
  · s^(2k) ≤ coeffPlusGap a b k · t^(2k)` for `coeffPlusGap ≥ 0` on
  N1).** Symmetric to sprint 011 but for the N1-restricted sum.
  **Demoted: too thin — sprint 026 can use `paper.eq4`'s first
  conjunct directly without needing the series-level monotonicity
  (which is what `eq4` *is*).** A future cleanup sprint could collapse
  this dependency on `eq4` to a series-level proof, but that doubles
  back to candidate A's territory.

* **K: A series-side proof of `paper.eq4_sigmaPlus_bound`'s second
  and third conjuncts (`sigmaPlus c ≤ sigmaMinus c = c²·Z_c`).** This
  would, in combination with candidate A above, prove `eq4` entirely
  from series structure — eliminating sprint 026's *only* paper-axiom
  dependency. Algebraically: `sigmaMinus c = ∑'_{n2Pred} coeffMinusGap·
  c^(2k) = c² · ∑'_{n2Pred} coeffMinusGap · c^(2k-2) = c² ·
  sigmaZeroMinus c` is a literal arithmetic identity at the `tsum`
  level. The other inequality `sigmaPlus c ≤ sigmaMinus c` requires
  `coeffPlusGap a b 0 + coeffPlusGap a b k · c^(2k) [for n1Pred k] ≤
  coeffMinusGap a b k · c^(2k) [for n2Pred k]` — which on N1 gives
  `‖a_k‖² − ‖b_k‖² ≤ ‖b_k‖² − ‖a_k‖²` iff `‖a_k‖ ≤ ‖b_k‖` — but on N1
  we have `‖a_k‖ ≥ ‖b_k‖`! So the `sigmaPlus c ≤ sigmaMinus c`
  direction is **non-obvious from series structure** — it's a genuine
  paper inequality, not a series-level identity. **Demoted: not derivable
  from series structure alone, would still require a paper axiom or
  oracle.** Sprint 026 keeps `eq4` as the load-bearing paper axiom.

Compared to A–K, candidate L (this sprint, the integrated full-disk
bound `diskExcess_upper_bound_via_circleGapSeries_eq4_only`) maximises
analytical novelty per bounded Generator session: it ships the **first
workspace disk bound with paper-axiom signature `{eq4}` only**, the
**first paper-internal cross-validation that sprint 013's `{eq3, eq4}`
bound is derivable through a strictly smaller paper-axiom signature**,
and **sprint 025's first downstream consumer** (validating that sprint
025's series-level pointwise bound composes cleanly with paper-axiom
material into integrated workspace bounds). It uses **only existing
trusted modules + pinned Mathlib + already-verified `Reduction.lean`
patterns** (sprint 003's integration body + sprint 025's pointwise
bound). No proposal needed.

### Note on the integrability hypothesis shape

The hypothesis
`hInt : IntervalIntegrable (fun r => 2 * r * PaperAxioms.circleGap a b r) MeasureTheory.volume 0 c`
matches sprint 003's exact hypothesis shape verbatim (see
`Reduction.lean` ~line 645). This is the natural shape because
`PaperAxioms.diskExcess (circleGap a b) c` unfolds to
`AnnulusIntegralReduction.annulusSlice (circleGap a b) 0 c`, which in
turn unfolds to `∫ r in 0..c, 2 * r * circleGap a b r`. The
integrability hypothesis is stated externally because
`Section2Assumptions` does not expose it — same as sprint 003.

### Note on the summability hypothesis shape

The hypothesis
`hSummable : ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c → Summable (fun k => coeffPlusGap a b k * r ^ (2 * k))`
is the *uniform* summability hypothesis required to invoke sprint 025
at every `r ∈ Ioo 0 c` inside the integrand. The implicit-binder shape
`{r : ℝ}` matches `paper.eq4_sigmaPlus_bound`'s implicit-`r` style.
The natural alternative — assuming summability only at `r = c` and
deriving summability at `r < c` via a geometric-tail comparison
(`Summable f at c → Summable f at r` for `r ≤ c` since the summand
decays in `r`) — would be a clean follow-up but is not on the critical
path: the uniform-over-`Ioo 0 c` shape is what the integration step
literally needs, so deriving it from a single-point summability
hypothesis would be additional bookkeeping that the current sprint
doesn't need to land. (A future cleanup sprint can introduce
`circleGapSeries_summable_of_summable_at_upper`, the analog of
`sigmaZeroMinus_summable_of_summable_at_upper` from sprint 012, to
collapse the universal-`r` shape to a single-point shape at `r = c`.)

### Note on the witness lemma at the seed

At the seed `c_value = 0.3554`:
* The lemma `diskExcess_upper_bound_via_circleGapSeries_eq4_only` is
  parameterised by an abstract `Section2Assumptions` instance plus the
  uniform summability and integrability hypotheses; the cleanest
  concrete side lemma at the seed exhibits the bound's signature
  compiles with `c_value` substituted everywhere, *without* discharging
  the summability or integrability premises (both remain existential
  hypothesis-only since they depend on the abstract `(a, b)` pair).
* A second, **structural** witness lemma confirms that the closed-form
  RHS `c_value^4 * sigmaZeroMinus a b c_value` is well-formed at the
  seed and that the bound's algebraic form
  `(c_value^4) = (1777/5000)^4` is non-trivial.

### Note on what the witness lemmas should NOT do

Sprint 026's V26 witness lemmas are **structural only** — they confirm
that the new lemma's signature compiles at the seed `c_value` and that
the bound's RHS is well-formed. They do **NOT** discharge the
summability or integrability premises (which remain existential
hypotheses), they do **NOT** invoke any closing reducer, and they do
**NOT** push `c_value` upward.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only`
    matching the shape above. Place it **after** sprint 025's
    `circleGap_le_sigmaPlus_via_series_split` at the end of the file
    so the chronological narrative is preserved.

    The proof body must:

    1. **Establish the pointwise bound** `∀ r ∈ Set.Ioo 0 c, circleGap
       a b r ≤ c² · sigmaZeroMinus a b c` by intro-ing `r` with `hr :
       r ∈ Set.Ioo 0 c`, then composing:
       * `hSeries := circleGap_le_sigmaPlus_via_series_split a b
         hr.1.le (hSummable hr.1.le hr.2)`: yields
         `circleGap a b r ≤ sigmaPlus a b r`.
       * `hEq4 := paper.eq4_sigmaPlus_bound hr.1.le hr.2 hc_lt_one`:
         yields `sigmaPlus a b r ≤ sigmaPlus a b c ∧ sigmaPlus a b c ≤
         sigmaMinus a b c ∧ sigmaMinus a b c = c² · sigmaZeroMinus a b c`.
       * Destructure: `⟨hPlus_r_le_c, hPlus_c_le_minus_c, hMinus_c_eq⟩
         := hEq4`.
       * Compose: `circleGap a b r ≤ sigmaPlus a b r ≤ sigmaPlus a b c
         ≤ sigmaMinus a b c = c² · sigmaZeroMinus a b c`. Use
         `le_trans` chain or a `calc` block. The final `=` step
         rewrites via `hMinus_c_eq`.

    2. **Multiply by `2r ≥ 0`** to get `2 * r * circleGap a b r ≤
       2 * r * (c^2 * sigmaZeroMinus a b c)` on `Set.Ioo 0 c`. Use
       `mul_le_mul_of_nonneg_left` with `0 ≤ 2 * r` from `hr.1.le`
       and the pointwise bound from step 1.

    3. **Integrate over `[0, c]`** via
       `intervalIntegral.integral_mono_on_of_le_Ioo`:
       * The lemma signature (sprint 003's `Reduction.lean` ~line 670):
         `intervalIntegral.integral_mono_on_of_le_Ioo : a ≤ b →
         IntervalIntegrable f volume a b → IntervalIntegrable g volume
         a b → (∀ x ∈ Set.Ioo a b, f x ≤ g x) → ∫ x in a..b, f x ≤ ∫ x
         in a..b, g x`.
       * `f := fun r => 2 * r * circleGap a b r` (LHS, integrability
         from `hInt`).
       * `g := fun r => 2 * r * (c^2 * sigmaZeroMinus a b c)` (RHS,
         integrability from
         `(IntervalIntegrable.const_mul ... 2)` or
         `intervalIntegrable_id.mul_const _` style, applied to the
         polynomial `2 * r`; the constant `c^2 * sigmaZeroMinus a b c`
         is pulled out via `IntervalIntegrable.mul_const`).
       * Pointwise bound from step 2.

    4. **Compute the RHS integral in closed form**:
       `∫ r in 0..c, 2 * r * (c^2 * sigmaZeroMinus a b c) =
       (c^2 * sigmaZeroMinus a b c) * ∫ r in 0..c, 2 * r =
       (c^2 * sigmaZeroMinus a b c) * c^2 = c^4 * sigmaZeroMinus a b c`.
       Use `intervalIntegral.integral_const_mul` (or its left/right
       variant) to pull out the constant, then `intervalIntegral.integral_const_mul`
       on `2`, then the elementary `∫ r in 0..c, r = c^2 / 2` (which is
       `integral_id_of_le` or the specialisation of `integral_pow` at
       `n = 1`). Sprint 003's body already establishes `∫₀^c 2r dr =
       c²` — copy that pattern verbatim. Conclude
       `∫ r in 0..c, 2 * r * (c^2 * sigmaZeroMinus a b c) = c^4 *
       sigmaZeroMinus a b c` via `field_simp; ring` or `ring`.

    5. **Identify the LHS as `diskExcess`**:
       `∫ r in 0..c, 2 * r * circleGap a b r = diskExcess (circleGap
       a b) c` by `unfold PaperAxioms.diskExcess
       AnnulusIntegralReduction.annulusSlice` (sprint 003's body has
       this unfold, copy verbatim).

    6. **Conclude** `diskExcess (circleGap a b) c ≤ c^4 ·
       sigmaZeroMinus a b c` via the chain from steps 3, 4, 5.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 026's
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only` is the
    workspace's **first integrated disk bound with paper-axiom
    signature `{eq4}` only** (vs sprint 013's `{eq3, eq4}`), the
    **first paper-internal cross-validation that sprint 013's bound
    is derivable through a strictly smaller paper-axiom signature**,
    and **sprint 025's first downstream consumer**.

  * The body of the new theorem MAY invoke:

    * Sprint 025's `circleGap_le_sigmaPlus_via_series_split`,
    * `paper.eq4_sigmaPlus_bound` field projection (with appropriate
      hypotheses `0 ≤ r ∧ r < c ∧ c < 1`),
    * Definitional unfolding of `PaperAxioms.diskExcess` and
      `AnnulusIntegralReduction.annulusSlice`,
    * Mathlib's `intervalIntegral.integral_mono_on_of_le_Ioo`,
      `intervalIntegral.integral_const_mul`,
      `intervalIntegral.integral_mul_const`,
      `intervalIntegral.integral_id`, `integral_pow`,
      `IntervalIntegrable.const_mul`, `IntervalIntegrable.mul_const`,
      `intervalIntegrable_id`, `intervalIntegrable_const`,
      `mul_le_mul_of_nonneg_left`, `pow_nonneg`, `le_refl`, `le_trans`,
    * Standard tactics: `intro`, `simp`, `unfold`, `change`, `rw`,
      `linarith`, `nlinarith`, `field_simp`, `ring`, `calc`, `exact`,
      `refine`, `obtain`, `have`, `show`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that sprint 026
    operates with **only `eq4` from the paper axiom side**, with **no
    `eq3` reference whatsoever**):

    * `paper.eq3_circleGap_decomposition` (the structural marker —
      sprint 026 must not invoke `eq3` directly; the `circleGap r ≤
      sigmaPlus r` step is discharged by sprint 025 instead),
    * `paper.eq2_sigmaZeroMinus_lower`,
      `paper.eq5_branch1_sigmaReduction`,
      `paper.eq6_branch2_sigmaReduction`,
      `paper.eq7_paperK_formula`,
      `paper.eq8_sigma_to_liftGap`,
      `paper.eq9_liftGap_to_circleGap`,
      `paper.eq10_branch1_pointwise`,
      `paper.eq11_branch2_pointwise`,
      `paper.eq12_branch1_integrated`,
      `paper.eq13_branch2_integrated`,
      `paper.eq14_combined`,
      `paper.eq15_*` (no other paper axiom — only `eq4`),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
      `eq10_of_eq5_eq8_eq9`,
      `eq11_of_eq6_eq8_eq9` (no paper-internal derived bridge),
    * Any prior `diskExcess_upper_bound_*` workspace lemma
      (sprints 003, 007, 013, 015, 016, 022 — sprint 026 must close
      on its own from sprint 025 + `eq4` + integration; no transitive
      workspace-lemma dependency on any prior `diskExcess` bound),
    * `circleGap_inner_bound_of_eq2_eq3_eq4` (sprint 002 — strictly
      uses `eq3`),
    * `circleGap_outer_lower_bound_of_eq8_eq9` (sprint 005 —
      structurally orthogonal),
    * `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (sprint 005 — would
      route through `eq8`/`eq9`-derived material; the `c² · Z_c =
      sigmaMinus c` identity needed in step 1 is supplied by
      `eq4`'s third conjunct directly),
    * `sigmaZeroMinus_nonneg_of_pos`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`
      (these are not needed because sprint 025 already discharges the
      termwise-dropping argument internally; if the proof body finds
      itself needing one of these, that signals the chain has drifted
      away from the intended sprint-025-direct path),
    * Any `valid_of_*` reducer (sprint 026 does not close the
      contract; it is a *bound* on `diskExcess`, not a closing
      reducer).

    (Note: sprint 025's `circleGap_le_sigmaPlus_via_series_split` is
    EXEMPT and IS the load-bearing pointwise bound consumed by the
    body; `paper.eq4_sigmaPlus_bound` is EXEMPT and is the only
    `paper.eq*` field projection consumed.)

  * The new theorem's signature MUST take *exactly* the parameters
    specified in the goal block: implicit `{a b : ℕ → ℂ}`, implicit
    `{K : ℝ → ℝ → ℝ}`, implicit `{c : ℝ}`, explicit
    `(paper : Section2Assumptions a b K c)`, explicit `(hc_pos : 0 < c)`,
    explicit `(hc_lt_one : c < 1)`, explicit
    `(hSummable : ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c → Summable (...))`,
    explicit `(hInt : IntervalIntegrable (fun r => 2 * r * circleGap
    a b r) volume 0 c)`. The conclusion MUST be exactly
    `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    c^4 * PaperAxioms.sigmaZeroMinus a b c`.

* `ProofRefinement/Korenblum/Candidates/V26.lean`:

  * `-- @parent V25`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V25).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V25).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new lemma's signature compiles at the seed `c_value`:

    ```lean
    theorem v26_disk_bound_via_circleGapSeries_eq4_only_compiles
        (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
        (paper : Section2Assumptions a b K c_value)
        (hSummable :
          ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
            Summable (fun k : ℕ =>
              PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
        (hInt :
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r)
            MeasureTheory.volume 0 c_value) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
      diskExcess_upper_bound_via_circleGapSeries_eq4_only
        paper c_value_pos c_value_lt_one hSummable hInt
    ```

    (Use `c_value_pos : 0 < c_value` and `c_value_lt_one : c_value < 1`
    if already available in the workspace; if not, prove inline via
    `by norm_num [c_value]`.)

  * Additionally, prove a structural side lemma confirming that the
    closed-form RHS at the seed `c_value^4 = (1777/5000)^4` evaluates
    to a positive rational:

    ```lean
    theorem v26_disk_bound_rhs_coefficient_at_seed :
        (0 : ℝ) < c_value ^ 4 := by
      unfold c_value
      norm_num
    ```

    This side lemma exhibits the **structural fact** that the new
    bound's coefficient is non-trivial at the seed (positive), so the
    bound is non-vacuous when `sigmaZeroMinus a b c_value > 0`.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify the new lemma's signature
    typechecks at the seed `c_value` and to demonstrate the
    coefficient is non-zero.

* `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_026 queued: ...` line (after the blank-line separator
  following the sprint_025 PASS line), then once V26 lands and the
  evaluator passes, append the corresponding
  `sprint_026 PASS: ...` line.

* `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting:
  * the new disk-bound paper-axiom signature `{eq4}` (vs sprint 013's
    `{eq3, eq4}`);
  * sprint 025's first downstream consumer pattern (pointwise series
    bound → integrated disk bound via the `2r` Jacobian and
    `intervalIntegral.integral_mono_on_of_le_Ioo`);
  * the natural follow-up roadmap:
    - candidate D from this contract (an end-to-end closing reducer
      `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window`
      that fuses sprint 026 with sprint 006's `(8)+(9)`-derived
      annulus bound, achieving paper-axiom signature `{eq4, eq8, eq9}`
      strictly smaller than sprint 014's `{eq3, eq4, eq8, eq9}`),
    - candidate B from this contract (termwise integration of sprint
      025 to give a series-side closed-form
      `diskExcess ≤ ∑'_{n1Pred} coeffPlusGap·c^(2k+2)/(k+1)`,
      requiring `tsum_integral_eq_integral_tsum`-style swap-of-sum-
      and-integral machinery — queueable as a separate sprint),
    - candidate C from this contract (series-level proof of `eq3`
      itself as an equality from `tsum` partition identity — would
      eliminate sprint 026's `eq4` dependency to a pure series-level
      proof if combined with candidate K's *other* direction).

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V25.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_025`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V26.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V26.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V26 scores `≥` V25 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V26.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the
   build emits them) — no new free-floating axioms.
5. `grep -n 'diskExcess_upper_bound_via_circleGapSeries_eq4_only' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition
   contains:
   * exactly one direct invocation of
     `circleGap_le_sigmaPlus_via_series_split` (the structural marker
     that sprint 026 consumes sprint 025),
   * exactly one direct invocation of `paper.eq4_sigmaPlus_bound`
     (the only `paper.eq*` field projection allowed),
   * at least one direct invocation of
     `intervalIntegral.integral_mono_on_of_le_Ioo` (the structural
     marker that the integration step is materialised),
   * **no direct reference** to `paper.eq3_circleGap_decomposition`
     (the structural marker that sprint 026 bypasses `eq3`),
   * **no direct reference** to any other `paper.eq{2,5..15}_…`
     field projection,
   * **no reference** to any `valid_of_*` reducer,
   * **no reference** to any prior `diskExcess_upper_bound_*`
     workspace lemma (sprints 003, 007, 013, 015, 016, 022),
   * **no reference** to `circleGap_inner_bound_of_eq2_eq3_eq4`,
     `circleGap_outer_lower_bound_of_eq8_eq9`,
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
     `sigmaZeroMinus_monotone_of_summable`,
     `sigmaZeroMinus_summable_of_summable_at_upper`,
   * **no reference** to `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
     `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9`,
     `WangOuter.paperLambda`, `WangPaperSideConditions.paperLambda_pos`,
   * **no reference** to `branchSplit`, `branch1SigmaKernel`,
     `branch1PointwiseFactor`, `branch2SigmaKernel`,
     `branch2PointwiseFactor`, `Korenblum.scalarCriterion`,
     `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
     `mass_mul_le_annulusSlice_of_integral_bound_ae`,
     `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`.
6. `grep -n 'v26_disk_bound_via_circleGapSeries_eq4_only_compiles\|v26_disk_bound_rhs_coefficient_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V26.lean`
   returns at least two distinct matches.
7. The conclusion of `diskExcess_upper_bound_via_circleGapSeries_eq4_only`
   is exactly
   `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤ c^4 * PaperAxioms.sigmaZeroMinus a b c`
   (verify via `grep` of the theorem statement).
8. The signature of `diskExcess_upper_bound_via_circleGapSeries_eq4_only`
   contains:
   * the implicit parameters `{a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}`
     (verify via `grep`),
   * the `Section2Assumptions a b K c` instance parameter,
   * the hypothesis `0 < c` and `c < 1`,
   * the universal summability hypothesis
     `∀ ⦃r : ℝ⦄, 0 ≤ r → r < c → Summable (...)` referencing
     `PaperAxioms.coeffPlusGap`,
   * the integrability hypothesis `IntervalIntegrable` referencing
     `2 * r * PaperAxioms.circleGap a b r`.
9. **Paper-axiom-signature guarantee**: the new lemma
   `diskExcess_upper_bound_via_circleGapSeries_eq4_only` consumes
   exactly one `paper.eq*` field projection: `paper.eq4_sigmaPlus_bound`.
   Verify via `grep -c 'paper\.eq[0-9]' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   in the line range of the new theorem returning exactly the count
   for `paper.eq4_sigmaPlus_bound` and zero for any other `paper.eq*`.
10. **Structural marker — sprint 025 consumption**: the new lemma's
    body contains at least one direct invocation of
    `circleGap_le_sigmaPlus_via_series_split` (sprint 025), making
    sprint 026 the **first downstream consumer** of sprint 025.
11. **Composition guarantee**: `#print axioms
    diskExcess_upper_bound_via_circleGapSeries_eq4_only` (or
    equivalent) does not list `paper.eq3_circleGap_decomposition` as
    a transitive dependency, even via `Section2Assumptions` field
    projections — sprint 025's body is paper-axiom-free, so the only
    `Section2Assumptions` field touched in the entire transitive
    closure is `eq4_sigmaPlus_bound`.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V25.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the closing-reducer counterpart
  `valid_of_disk_eq4_circleGapSeries_annulus_eq8_eq9_full_window`
  (candidate D above — would fuse sprint 026 with sprint 006's
  `(8)+(9)`-derived annulus bound for an end-to-end `{eq4, eq8, eq9}`-
  only `ValidKorenblumBound c` reducer, strictly smaller paper-axiom
  signature than sprint 014's `{eq3, eq4, eq8, eq9}`; queueable as a
  separate sprint after 026 lands).
* Building the termwise-integrated series-side bound
  `diskExcess ≤ ∑'_{n1Pred} coeffPlusGap a b k · c^(2k+2)/(k+1)`
  (candidate B above — requires
  `MeasureTheory.tsum_integral_eq_integral_tsum`-style swap-of-sum-
  and-integral machinery; queueable as a separate sprint after 026).
* Building a series-level proof of `paper.eq3_circleGap_decomposition`
  itself (candidate C above — would prove the *equality* `circleGap r
  = sigmaPlus r − r²·sigmaZeroMinus r` from `tsum` partition identity
  alone, fully eliminating `eq3`; same analytical layer as sprint 025
  rather than a downstream consumer).
* Building a `sigmaPlus`-monotone series-level lemma (candidate A
  above — symmetric to sprint 011 but for `coeffPlusGap` on the
  N1-restricted sum; would re-derive the *forward* direction of
  `eq4`'s first conjunct paper-axiom-free).
* Building a series-side disk bound `diskExcess ≤ c² · sigmaPlus c`
  (candidate E above — intermediate stop *before* chaining all three
  conjuncts of `eq4`; queueable separately if useful).
* Discharging the summability or integrability hypotheses for any
  concrete `(a, b)` pair at the seed `c_value` numerically.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new lemma. Sprint 026 alone is **not** a
  closing reducer — it is a structural integrated bound on `diskExcess`.
  Closing requires composition with an `annulusExcess`-side bound in
  the deferred follow-up sprint (candidate D).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 026 is purely
  structural.
* Modifying any prior `Reduction.lean` lemma (sprints 001–025 are
  consumed only by their existing call sites; sprint 026 adds a new
  lemma in isolation, with sprint 025 invoked as a *consumer* but not
  modified).

## Time budget

≤ 30 minutes runtime. The new lemma is ~80 lines of Lean (~10 lines
for the signature, ~20 lines for the pointwise-bound composition step,
~50 lines for the integration step modeled on sprint 003's body). The
candidate side lemmas are 10–25 lines each. Total V26 size: ≤ 100
lines. All tactics used are *already verified* in sprint 003
(`Reduction.lean` ~lines 640-700 for the integration pattern) plus
sprint 025 (`Reduction.lean` end of file for the pointwise series
bound). The composition is a structurally clean glue lemma — no new
Mathlib lemma archaeology needed.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `intervalIntegral.integral_mono_on_of_le_Ioo` invocation requires
  both sides to be `IntervalIntegrable` — if the constant-times-`2r`
  RHS integrability proof is not immediate, fall back to copying
  sprint 003's exact pattern at `Reduction.lean` ~line 670 for the
  RHS integrability via `intervalIntegrable_id.const_mul`.
* The closed-form RHS evaluation `∫₀^c 2r · (c² · Z_c) dr =
  c⁴ · Z_c` requires the elementary `∫₀^c r dr = c²/2`. Sprint 003's
  body uses `@integral_pow 0 c 1` with cleanup; copy that pattern
  verbatim. If `intervalIntegral.integral_const_mul` doesn't unfold
  cleanly when the constant is a product `c² · Z_c`, factor as
  `(c² · Z_c) · (∫₀^c 2r dr)` first via `mul_comm` rewrites and pull
  out via `intervalIntegral.integral_const_mul` in two steps.
* The pointwise composition step in step 1 hits a Lean unification
  issue with `paper.eq4_sigmaPlus_bound`'s implicit-`{r}` binder —
  fall back to `paper.eq4_sigmaPlus_bound (r := r) hr.1.le hr.2
  hc_lt_one` with the explicit-`r` invocation. Reference sprint 003's
  body for the analogous pattern with `paper.eq3_circleGap_decomposition`.
* The summability hypothesis shape causes a unification issue with
  sprint 025's signature — sprint 025 takes `{r : ℝ}` implicit and
  `(hr_nonneg : 0 ≤ r)` explicit; if the call site needs to pass `r`
  explicitly, use `circleGap_le_sigmaPlus_via_series_split (r := r)
  a b hr.1.le (hSummable hr.1.le hr.2)` with the explicit-`r`
  invocation.
* The `diskExcess`/`annulusSlice` definitional unfold step in step 5
  fails — fall back to copying sprint 003's exact `unfold` invocation
  verbatim (`unfold PaperAxioms.diskExcess
  AnnulusIntegralReduction.annulusSlice`) or use `change` to manually
  align the goal shape.
* Any of acceptance criteria 4, 5, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially `paper.eq3_circleGap_decomposition`,
  which would reduce sprint 026 to "sprint 013 with extra steps"):
  `STATUS=BLOCKED` — that would defeat the **paper-axiom signature
  cross-validation** structural guarantee, the entire point of the
  sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
