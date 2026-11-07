# Sprint 013: Closed-form single-`Z_c` disk-side upper bound via `eq3 + eq4` only — `diskExcess ≤ c⁴ · sigmaZeroMinus c`, valid on the full disk and free of any `ρ`-window

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V12.lean`
**Target file**: `Candidates/V13.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c
```

The proof chain, in order:

1. **Pointwise upper bound on `circleGap r` for `r ∈ Ioo 0 c`** by combining
   only `paper.eq3_circleGap_decomposition` and `paper.eq4_sigmaPlus_bound`,
   plus `sigmaZeroMinus_nonneg_of_pos` (sprint 005). Specifically:

   * `eq3 r` (for `0 ≤ r ∧ r < 1`):
     `circleGap r = sigmaPlus r − r²·sigmaZeroMinus r`.
   * `eq4 r` (for `0 ≤ r ∧ r < c ∧ c < 1`):
     `sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c²·sigmaZeroMinus c`,
     hence `sigmaPlus r ≤ c²·sigmaZeroMinus c`.
   * Sprint 005's `sigmaZeroMinus_nonneg_of_pos a b hr_pos` (for `0 < r`):
     `0 ≤ sigmaZeroMinus a b r`, hence `0 ≤ r²·sigmaZeroMinus r`.
   * Combine: `circleGap r = sigmaPlus r − r²·sigmaZeroMinus r ≤ sigmaPlus r ≤
     c²·sigmaZeroMinus c`.

   The combined pointwise bound on `Ioo 0 c` is

   ```
   ∀ r ∈ Set.Ioo 0 c, circleGap a b r ≤ c² * sigmaZeroMinus a b c.
   ```

2. **Multiply pointwise by the polar Jacobian `2r ≥ 0`** to get
   `2r·circleGap r ≤ 2r·c²·sigmaZeroMinus c` on `Ioo 0 c`.

3. **Integrate over `[0, c]`** via
   `intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hInt _ pointwise`,
   exactly the pattern already used in
   `diskExcess_upper_bound_of_eq2_eq3_eq4` (sprint 003) at
   `Reduction.lean:380`. The integral of the RHS is

   ```
   ∫_0^c 2r·c²·sigmaZeroMinus c dr = c²·sigmaZeroMinus c · ∫_0^c 2r dr
                                   = c²·sigmaZeroMinus c · c²
                                   = c⁴·sigmaZeroMinus c.
   ```

   The constant factor `c²·sigmaZeroMinus c` pulls out via
   `intervalIntegral.integral_const_mul` and the inner integral is
   `∫_0^c 2r dr = c²` (a one-line `@integral_pow 0 c 1` + `norm_num`
   computation, exactly the pattern at `Reduction.lean:383-386`).

4. **Identify** `diskExcess (circleGap a b) c` with
   `∫ r in (0:ℝ)..c, 2 * r * circleGap a b r` via `change` +
   `AnnulusIntegralReduction.annulusSlice` definitional unfolding (the
   pattern used at `Reduction.lean:423-427`), then chain via `calc`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V13.lean` at the same `c = 0.3554` that compiles,
scores `≥ V12`, and *materialises* the new lemma in two side lemmas
`v13_diskExcess_upper_bound_via_eq3_eq4_compiles` and
`v13_diskExcess_upper_bound_via_eq3_eq4_chain_compiles` (mirroring V3's
`v3_diskExcess_upper_bound_chain_compiles` pattern). The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. The first bullet of "axes worth exploring" reads
verbatim:

> chain different paper equations — try `eq3` decomposition + `eq4` `Σ⁺`
> bound + `eq8`/`eq9` lift bridges + `eq10`/`eq11` pointwise + `eq12`/`eq13`
> integrated forms in combinations the seed doesn't use, without going
> through `eq14_combined` or `Eq15ScalarBound`.

Sprint 013 is precisely a sprint along this axis. It produces a
**brand-new closed-form disk-side upper bound** that uses *only* `eq3`
and `eq4` (plus sprint 005 nonnegativity). The bound is qualitatively
different from every prior disk-side bound in the workspace along three
independent axes:

1. **Strictly fewer paper hypotheses than sprint 002+003.** Sprint 002's
   `circleGap_inner_bound_of_eq2_eq3_eq4` uses the **full triple**
   `(eq2, eq3, eq4)` — and `eq2`'s appearance forces a free `ρ`-parameter
   into the bound (because `eq2` lower-bounds `sigmaZeroMinus(r)` in
   terms of `sigmaZeroMinus(c)` and `sigmaZeroMinus(ρ)`). Sprint 013
   uses **only `(eq3, eq4)`** and *never substitutes* the
   `r²·sigmaZeroMinus r` term — instead it **drops** it via
   non-negativity from sprint 005. The result is genuinely structurally
   simpler: a single-`Z_c` bound with **no `ρ` appearance** at all.

2. **Single explicit Z value (`Z_c`), free of any `ρ`-window choice.**
   Every prior disk-side bound (sprints 002, 003, 007) carries a free
   `ρ`-parameter that has to be optimised numerically. Sprint 003's
   integrated bound is
   `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)·Z_c + (c⁶/6)/(ρ²−c²)·Z_ρ` — a *two-Z*
   bound with both `Z_c` and `Z_ρ` and explicit `ρ`-dependence.
   Sprint 007's "single-Z" collapse drops the `Z_c` term, leaving
   `(c⁶/6)/(ρ²−c²)·Z_ρ`, but **only on the branch-split sub-regime
   `(c, branchSplit c]`** and still in `Z_ρ`. Sprint 013's bound
   `c⁴·Z_c` has **no `ρ` at all**, **no regime restriction**, and
   carries the unique scalar coefficient `c⁴` — much cleaner.

3. **Valid on the full disk regime, not a sub-regime.** Sprint 007's
   single-Z collapse is only valid when `3ρ² ≤ 4c²` (i.e.
   `ρ ≤ branchSplit c = √(4/3)·c`). Sprint 013's bound is valid for
   *any* `c ∈ (0, 1)` — no `ρ` to constrain. This makes it directly
   composable with annulus-side bounds over **arbitrary windows
   `[ρ₁, ρ₂] ⊂ (c, 1)`**, not just sub-windows of `(c, branchSplit c]`.
   This is a strict structural improvement over the sprint 007–012
   chain, which inherits the branch-split constraint at every link.

   Concretely, the natural follow-up reducer (queued for a future
   sprint, not this one) is:

   ```text
   diskExcess
     ≤ c⁴ · sigmaZeroMinus c                         -- sprint 013
     ≤ c⁴ · sigmaZeroMinus a b ρ₁                    -- sprint 011 monotonicity (c ≤ ρ₁)
     ≤ c⁴ · (RHS / ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ)         -- sprint 006 + sprint 011
     ≤ annulusExcess
   ```

   The Z-free kernel inequality reduces to
   `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`, which **no longer carries the
   `(ρ₁²−c²)` denominator** of sprint 010's `(c⁶/6)/(ρ₁²−c²) ≤ ∫…`.
   Removing that pathological denominator is a strict structural
   simplification: the LHS no longer blows up as `ρ₁ → c`.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V13 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form upper bound on
  `diskExcess` that holds for *any* paper-faithful instance.
* No concrete numerical tuple is committed; no `ρ`-window is named.

Why this is **not** "the same chain" as sprint 002, 003, or 007:

* Sprint 002/003 use the **full triple** `(eq2, eq3, eq4)` to bound
  `circleGap(r)` pointwise in terms of `Z_c` AND `Z_ρ`, then integrate.
  Sprint 013 uses **only `(eq3, eq4)`** to bound `circleGap(r)`
  pointwise in terms of `Z_c` ONLY (no `Z_ρ`, no `ρ`).

* Sprint 007 takes sprint 003's two-`Z` bound and sign-analyses the
  `Z_c` coefficient on the branch-split sub-regime to drop the term.
  Sprint 013 takes a **fundamentally different approach**: drop the
  `r²·Z_r` term from `eq3` directly via sprint 005 non-negativity,
  *before* substituting any `Z_r` lower bound. Sprint 007 ends up at
  `(c⁶/6)/(ρ²−c²)·Z_ρ` (single Z but in `Z_ρ`, with `ρ` and a regime
  restriction). Sprint 013 ends up at `c⁴·Z_c` (single Z in `Z_c`, no
  `ρ`, no regime restriction).

* The two single-Z bounds are **incomparable**: sprint 007's
  `(c⁶/6)/(ρ²−c²)·Z_ρ` involves the *outer-radius* Z-value `Z_ρ`,
  while sprint 013's `c⁴·Z_c` involves the *inner-radius* Z-value
  `Z_c`. They feed into different downstream chains:
  sprint 007 → sprint 009/010 (Z-free via common-`Z_ρ`-factor extraction
  on the annulus side); sprint 013 → a future Z-free chain that uses
  sprint 011 monotonicity to dominate `Z_c` by `Z_ρ`. Two independent
  routes through the same disk side.

Why this is **bounded enough for one Generator session**:

* The pointwise bound proof is genuinely small:
  * `eq3 r` rewrite (1 line via `simpa [PaperAxioms.Eq3CircleGapDecomposition]`).
  * `eq4 r` triple destructuring (3 lines, exactly as in sprint 002 at
    `Reduction.lean:220-227`).
  * `sigmaPlus r ≤ c²·Z_c` chain (3 lines via `le_trans` + `rw`,
    exactly as in sprint 002 at `Reduction.lean:228-233`).
  * `sigmaZeroMinus r ≥ 0` from sprint 005 (1 line, only invoked for
    `0 < r`).
  * Combine via `linarith` (1 line).
  Estimate: ≤ 15 lines for the pointwise bound.

* The integration step is even simpler than sprint 003 because the RHS
  is `2r·(c²·Z_c)`, a single linear-in-`r` term with a constant
  coefficient. No polynomial decomposition into `A·r + B·r³ + C·r⁵`
  is needed.
  * `intervalIntegral.integral_mono_on_of_le_Ioo` (1 line, exact pattern
    of sprint 003 at `Reduction.lean:380`).
  * `intervalIntegral.integral_const_mul` to pull `c²·Z_c` outside the
    integral (1-2 lines).
  * `∫_0^c 2r dr = c²` via `@integral_pow 0 c 1` + `norm_num`
    (3 lines, exactly the pattern of sprint 003 at
    `Reduction.lean:383-386`).
  * `change` + `rfl` to identify `diskExcess` with the integral
    (3 lines, exactly the pattern of sprint 003 at `Reduction.lean:423-427`).
  * `calc` chain (5-7 lines).
  Estimate: ≤ 20 lines for the integration step.

* Total for the new theorem: ≤ 40 lines of Lean. Roughly half the size
  of sprint 003.

* The candidate side lemmas are one to three lines each.

* All Mathlib lemmas needed (`intervalIntegral.integral_mono_on_of_le_Ioo`,
  `intervalIntegral.integral_const_mul`, `@integral_pow`,
  `Continuous.intervalIntegrable`) are *already used* in sprint 003,
  verified at `Reduction.lean:375-410`. Risk of "Mathlib lemma name
  mismatch" is essentially zero.

Why this beats the obvious alternatives I considered:

* **A: discharge the upper-edge summability premise of sprint 012's
  reducer via `‖b k‖ ≤ M` + `summable_geometric`.** Modest novelty —
  it would be the **third** series-side sprint in a row (after sprints
  011 and 012), and risks looking like flavour-cloning. Also, it
  doesn't open a new analytical *chain* — it just discharges one
  premise of an existing chain. Demoted: less analytical chain
  novelty than candidate L (sprint 013), even though the technical
  ingredient (geometric tail) is new.

* **B: parallel `sigmaPlus` series-level non-negativity bound.** Build
  a series-side lemma about `sigmaPlus` analogous to
  `sigmaZeroMinus_nonneg_of_pos` but for `sigmaPlus`. Genuinely novel
  series-side axis but speculative — the workspace doesn't currently
  consume `sigmaPlus`-non-negativity anywhere, and `n1Pred` includes
  `k = 0` which has different sign handling. No immediate downstream
  consumer. Demoted to "future / needs concrete consumer first".

* **C: discharge integrability of `2ρ³/paperLambda(c,ρ)` on
  `[ρ₁, ρ₂] ⊂ (c, 1)` via continuity of `paperLambda`.** Requires
  `WangPaperSideConditions.paperLambda_aemeasurableOn_Icc`, which
  lives **outside the workspace allowlist** — same blocker as sprint
  011's candidate analysis. Would require a `Proposals/` entry to
  expand `[workspace_import_policy]`. Demoted because it requires a
  non-oracle trust expansion that is not approved.

* **D: closed-form `sigmaZeroMinus(0)` series identity.** Compute
  `sigmaZeroMinus a b 0` in closed form via the series structure
  (`0^(2k-2)` is `1` only at `k=1`, where `2k-2=0`, and `0` for
  `k ≥ 2`). Genuinely novel series-side axis (third series-side lemma
  after sprints 011+012, but qualitatively distinct: it's a
  *closed-form value* of the `tsum` at a boundary, not a
  monotonicity/summability result). However, attempting to combine
  this with `eq2` at `r = 0` to upper-bound `Z_c` in terms of `Z_ρ`
  yields a **strictly worse** disk bound than sprint 003 in the
  regime where the Z_c coefficient is positive (because
  upper-bounding `Z_c` with a positive coefficient *increases* the
  bound), and a strictly worse bound than sprint 007 in the
  branch-split regime. Demoted: structural novelty without a useful
  downstream consumer.

* **E: branch-2 mirror of sprint 008** on `(branchSplit c, 1)`. Pure
  flavour-clone of sprint 008, exactly the "three flavours of the
  same chain" pattern the bulletin warns against. Demoted.

* **F: prove `Eq15ScalarBound` in Lean for `c = 0.3554` symbolically**
  to remove the `hEq15_seed_3554` axiom. Pure numerical push against
  the existing chain — exactly what the bulletin de-prioritises.

Compared to A–F, candidate L (this sprint) maximises analytical novelty
per bounded Generator session: it ships a **brand-new closed-form
disk-side upper bound** that opens a **new disk-to-annulus reduction
chain valid on the full window `(c, 1)`** (no branch-split
restriction), uses **only `(eq3, eq4)`** plus sprint 005 nonnegativity
(strictly fewer paper hypotheses than every prior disk bound in the
workspace), and uses **only existing trusted modules + pinned Mathlib**
in patterns already verified by sprint 003. No proposal needed.

### Note on the `r = 0` edge

The pointwise bound is stated on `Set.Ioo 0 c`, which excludes `r = 0`.
This is the *same* convention used by sprint 002's
`circleGap_inner_bound_of_eq2_eq3_eq4` (whose bound is also stated
pointwise on `Ioo 0 c`, then a.e.-extended via
`intervalIntegral.integral_mono_on_of_le_Ioo` for the integration step).
Sprint 013's pointwise bound only consumes `0 < r` (to invoke sprint 005
`sigmaZeroMinus_nonneg_of_pos` with positive `r`). The `r = 0` boundary
is measure zero and is handled implicitly by the `_of_le_Ioo` integral
monotonicity lemma (which only requires the pointwise bound on the open
interval `Ioo 0 c`, not on the closed `Icc 0 c`).

### Note on why the bound is not improved by retaining the `r²·Z_r` term

The bound `circleGap r = sigmaPlus r − r²·Z_r ≤ sigmaPlus r ≤ c²·Z_c`
*drops* the non-negative term `r²·Z_r`. One might worry that retaining
it gives a tighter bound — but doing so requires either substituting a
*lower* bound on `Z_r` (which is what sprint 002 does via `eq2`,
producing the two-`Z` `circleGap_inner_bound_of_eq2_eq3_eq4` bound) or
keeping `Z_r` as a third unknown (which makes the integrated bound
non-closed-form). The whole point of sprint 013 is to **avoid `eq2`**
and produce a single-`Z` bound — dropping the `r²·Z_r` term is the
price (and the structural feature) of that goal. The resulting bound
`c⁴·Z_c` is intentionally *not* the tightest possible upper bound;
its value lies in being a single-`Z`, `ρ`-free, regime-free closed-form
bound that supports a **downstream Z-free chain over the full window
`(c, 1)`** (queued for a future sprint).

### Note on the natural follow-up reducer (queued, NOT in this sprint)

After sprint 013 lands, a future sprint will combine it with sprint
006's `annulusExcess_lower_bound_of_eq8_eq9` and sprint 011's
`sigmaZeroMinus_monotone_of_summable` to ship a brand-new reducer:

```lean
theorem valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            -- (integrability + summability premises)
            c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

Note the Z-free kernel inequality `c⁴ ≤ ∫…` — *no* `(ρ₁²−c²)`
denominator (unlike sprint 010's reducer) and *no* `3ρ₁² ≤ 4c²`
branch-split constraint (unlike sprints 007/009/010/011/012). That
follow-up is **not** in scope for sprint 013. Sprint 013 ships only the
new disk bound; the reducer is a separate sprint that benefits from
V13 as parent.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem `diskExcess_upper_bound_via_eq3_eq4`
    matching the shape above. The proof body must:

    1. Establish positivity of `c` (already a hypothesis). No
       `ρ`-positivity is needed — `ρ` does not appear.
    2. Build the pointwise upper bound on `Ioo 0 c`:

       ```lean
       have hPointwise :
           ∀ r ∈ Set.Ioo (0 : ℝ) c,
             PaperAxioms.circleGap a b r ≤
               c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
         intro r hr
         have hr_pos : 0 < r := hr.1
         have hr_nonneg : 0 ≤ r := hr_pos.le
         have hr_lt : r < c := hr.2
         have hr_lt_one : r < 1 := lt_trans hr_lt hc_lt_one
         -- eq3 r
         have h3 :
             PaperAxioms.circleGap a b r =
               PaperAxioms.sigmaPlus a b r -
                 r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
           have := paper.eq3_circleGap_decomposition (r := r) hr_nonneg hr_lt_one
           simpa [PaperAxioms.Eq3CircleGapDecomposition] using this
         -- eq4 r: sigmaPlus r ≤ c²·Z_c.
         have h4 :=
           paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
         have h4_unfold :
             PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
               PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
               PaperAxioms.sigmaMinus a b c =
                 c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
           simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
         obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
         have hSigmaPlus_le :
             PaperAxioms.sigmaPlus a b r ≤
               c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
           have : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
             le_trans h4a h4b
           rw [h4c] at this
           exact this
         -- sprint 005 non-negativity of sigmaZeroMinus at r > 0.
         have hZr_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b r :=
           sigmaZeroMinus_nonneg_of_pos a b hr_pos
         have hr2_nonneg : 0 ≤ r ^ 2 := by positivity
         have hr2_Zr_nonneg :
             0 ≤ r ^ 2 * PaperAxioms.sigmaZeroMinus a b r :=
           mul_nonneg hr2_nonneg hZr_nonneg
         -- Combine via h3 + monotonicity.
         linarith
       ```

       This block uses **only** `paper.eq3_circleGap_decomposition`,
       `paper.eq4_sigmaPlus_bound`, and `sigmaZeroMinus_nonneg_of_pos`.
       It must **not** invoke `paper.eq2_*`, `paper.eq5_*`, `paper.eq6_*`,
       `paper.eq7_*`, `paper.eq8_*`, `paper.eq9_*`, `paper.eq10_*`,
       `paper.eq11_*`, `paper.eq12_*`, `paper.eq13_*`, `paper.eq14_*`,
       `paper.eq15_*`, `circleGap_inner_bound_of_eq2_eq3_eq4`,
       `WangOuter.paperLambda`, `Korenblum.scalarCriterion`, or any
       other already-proved lemma in `Reduction.lean`.

    3. Multiply pointwise by `2r ≥ 0`:

       ```lean
       have hPointwise_jac :
           ∀ r ∈ Set.Ioo (0 : ℝ) c,
             2 * r * PaperAxioms.circleGap a b r ≤
               2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) := by
         intro r hr
         have hr_nonneg : 0 ≤ r := hr.1.le
         have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
         exact mul_le_mul_of_nonneg_left (hPointwise r hr) h2r_nonneg
       ```

    4. Establish integrability of the RHS (a constant multiple of `2r`):

       ```lean
       have hRhsCont :
           Continuous
             (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) := by
         fun_prop
       have hRhsIntegrable :
           IntervalIntegrable
             (fun r => 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
             volume 0 c :=
         hRhsCont.intervalIntegrable _ _
       ```

    5. Integrate via `intervalIntegral.integral_mono_on_of_le_Ioo`
       (mirror sprint 003 at `Reduction.lean:380`):

       ```lean
       have hIntegralMono :
           ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r ≤
             ∫ r in (0 : ℝ)..c,
               2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) :=
         intervalIntegral.integral_mono_on_of_le_Ioo hc_pos.le hInt
           hRhsIntegrable hPointwise_jac
       ```

    6. Compute the closed-form RHS integral:

       ```lean
       have hPow1 : ∫ r in (0 : ℝ)..c, r = c ^ 2 / 2 := by
         have h := @integral_pow 0 c 1
         simp only [pow_one] at h
         convert h using 2 <;> norm_num
       have hRhsClosedForm :
           ∫ r in (0 : ℝ)..c,
               2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)
             = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := by
         have hRewrite :
             (fun r : ℝ =>
               2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c))
               = fun r =>
                 (2 * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c)) * r := by
           funext r; ring
         rw [hRewrite, intervalIntegral.integral_const_mul, hPow1]
         ring
       ```

    7. Identify `diskExcess` with the integral and chain via `calc`:

       ```lean
       have hDiskExcess :
           PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
             ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
         change AnnulusIntegralReduction.annulusSlice
           (PaperAxioms.circleGap a b) 0 c = _
         rfl
       rw [hDiskExcess]
       calc
         ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r
             ≤ ∫ r in (0 : ℝ)..c,
                 2 * r * (c ^ 2 * PaperAxioms.sigmaZeroMinus a b c) :=
               hIntegralMono
           _ = c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hRhsClosedForm
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 013's `diskExcess_upper_bound_via_eq3_eq4` is the
    workspace's **first single-`Z_c` disk-side upper bound** —
    `diskExcess ≤ c⁴·sigmaZeroMinus c`. It uses only `eq3` and `eq4`
    (avoiding `eq2`) and drops the `r²·Z_r` term via sprint 005
    non-negativity. Unlike sprint 003's two-`Z` bound (which carries
    both `Z_c` and `Z_ρ`) and sprint 007's single-`Z_ρ` collapse on the
    branch-split sub-regime, this bound carries only `Z_c`, has no
    `ρ`-dependence, and is valid on the full disk regime `c ∈ (0, 1)`.
    Composing it with sprint 006's annulus lower bound + sprint 011
    monotonicity yields a Z-free reducer over the **full window
    `[ρ₁, ρ₂] ⊂ (c, 1)`** (queued for a future sprint), with kernel
    inequality `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` — strictly cleaner
    than sprint 010's `(c⁶/6)/(ρ₁²−c²) ≤ ∫…`.

  * The body of `diskExcess_upper_bound_via_eq3_eq4` MAY invoke:

    * `paper.eq3_circleGap_decomposition`,
    * `paper.eq4_sigmaPlus_bound`,
    * `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
    * `intervalIntegral.integral_mono_on_of_le_Ioo`,
    * `intervalIntegral.integral_const_mul`,
    * `@integral_pow`,
    * `Continuous.intervalIntegrable`,
    * `mul_le_mul_of_nonneg_left`, `mul_nonneg`, `le_trans`, `linarith`,
      `simpa`, `convert`, `change`, `rfl`, `ring`, `field_simp`,
      `norm_num`, `positivity`, `fun_prop`, `funext`,
    * `PaperAxioms.Eq3CircleGapDecomposition`,
      `PaperAxioms.Eq4SigmaPlusBound` (definitional unfoldings),
    * `AnnulusIntegralReduction.annulusSlice` (definitional unfolding
      via `change`).

    The body must **NOT** invoke any of the following forbidden
    references (verify via `grep -nE` against the substring of the
    theorem body):

    * `paper.eq2_`, `paper.eq5_`, `paper.eq6_`, `paper.eq7_`,
      `paper.eq8_`, `paper.eq9_`, `paper.eq10_`, `paper.eq11_`,
      `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
    * `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `annulusExcess_lower_bound_of_eq8_eq9`,
      `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`,
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `eq15_implies_disk_le_annulus`,
    * `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
      `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
      `branchSplit`, `branch1SigmaKernel`, `branch1PointwiseFactor`,
      `branch2PointwiseFactor`, `liftGap`,
    * `paper.eq3_circleGap_decomposition` and `paper.eq4_sigmaPlus_bound`
      MUST each appear **at most once** as a hypothesis invocation
      (verified by `grep -c`); the rest of the proof body should
      manipulate the resulting concrete inequalities, not re-invoke the
      paper hypotheses.

  * The new theorem's signature MUST take *only*: `(paper :
    Section2Assumptions a b K c)`, `(hc_pos : 0 < c)`,
    `(hc_lt_one : c < 1)`, and
    `(hInt : IntervalIntegrable (fun r => 2*r*PaperAxioms.circleGap a b r) volume 0 c)`.
    It MUST NOT take any `ρ`, `ρ₁`, `ρ₂`, or other `ρ`-related
    parameter — the absence of `ρ` from the signature is the
    structural marker that this bound is *intrinsically* a function of
    `c` alone.

* `ProofRefinement/Korenblum/Candidates/V13.lean`:

  * `-- @parent V12`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V12).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V12).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new theorem at a generic `Section2Assumptions` instance at the
    seed `c_value`:

    ```lean
    theorem v13_diskExcess_upper_bound_via_eq3_eq4_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        (hInt :
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
      diskExcess_upper_bound_via_eq3_eq4 paper c_value_pos c_value_lt_one hInt
    ```

  * Additionally, prove a *verifying* side lemma that exhibits the
    closed-form structural identity at the seed (the bound's RHS in a
    name the next sprint can pattern-match on):

    ```lean
    theorem v13_diskExcess_upper_bound_via_eq3_eq4_chain_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (_paper : Section2Assumptions a b K c_value),
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
        ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
          (paper : Section2Assumptions a b K c_value),
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
            c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
      fun {a b K} paper =>
        diskExcess_upper_bound_via_eq3_eq4 paper c_value_pos c_value_lt_one
          (h_witness paper)
    ```

    Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify that the new lemma
    typechecks at the seed `c_value` and to materialise its use in
    V13's call graph.

  * No additional structural witness lemma is required — the new
    theorem has no geometric `(ρ₁, ρ₂)` parameters that would need
    a witness.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V12.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_012`.

### Note on `eq3` requiring `r < 1` vs `r < c < 1`

`paper.eq3_circleGap_decomposition` requires `0 ≤ r ∧ r < 1`. Inside
`Ioo 0 c`, we have `r < c` and `c < 1` (from `hc_lt_one`), so
`r < 1` follows from `lt_trans hr_lt hc_lt_one`. The `hc_lt_one`
hypothesis is required for this transitivity step — it is the
**only** reason `hc_lt_one` appears in the theorem signature, beyond
its use in the `eq4` invocation.

### Note on the absence of `paper.eq2_*`

The sprint 002 bound `circleGap_inner_bound_of_eq2_eq3_eq4` substitutes
`Z_r ≥ A·Z_c − B·Z_ρ` (from `eq2`) into the `r²·Z_r` term of `eq3`. This
substitution is what *introduces* `Z_ρ` into the bound and forces the
free `ρ`-parameter. Sprint 013 takes the alternative route: instead of
substituting a lower bound on `Z_r`, **drop the `r²·Z_r` term entirely**
via non-negativity. The result is a single-`Z_c` bound with no `Z_ρ`
appearance.

### Note on the trivial integration step

The integration step in sprint 013 is much simpler than sprint 003's
because the RHS is `2r·(c²·Z_c)`, a single linear-in-`r` term with a
constant coefficient. Specifically:

* Pull `(c²·Z_c)` out of the integral via `integral_const_mul`:
  `∫_0^c 2r·(c²·Z_c) dr = (2·c²·Z_c) · ∫_0^c r dr = (2·c²·Z_c) · (c²/2) = c⁴·Z_c`.
* `∫_0^c r dr = c²/2` is exactly the `hPow1` lemma already used in
  sprint 003 (verified at `Reduction.lean:383-386`).
* No polynomial decomposition, no `field_simp + ring` for the closed-form
  step (only a `ring` to collapse `2 * (c² * Z_c) * (c²/2) = c⁴ * Z_c`).

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V13.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V13.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V13 scores `≥` V12 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V13.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'diskExcess_upper_bound_via_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one use of `paper.eq3_circleGap_decomposition`,
   * exactly one use of `paper.eq4_sigmaPlus_bound`,
   * at least one use of `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
   * exactly one use of `intervalIntegral.integral_mono_on_of_le_Ioo`,
   * at least one use of `intervalIntegral.integral_const_mul`,
   * at least one use of `@integral_pow` (or unqualified `integral_pow`),
   * no reference to `paper.eq2`, `paper.eq5`, `paper.eq6`, `paper.eq7`,
     `paper.eq8`, `paper.eq9`, `paper.eq10`, `paper.eq11`, `paper.eq12`,
     `paper.eq13`, `paper.eq14`, `paper.eq15`.
6. `grep -n 'v13_diskExcess_upper_bound_via_eq3_eq4_compiles\|v13_diskExcess_upper_bound_via_eq3_eq4_chain_compiles' korenblum/ProofRefinement/Korenblum/Candidates/V13.lean`
   returns at least two distinct matches (V13 actually invokes the
   new lemma in both side-lemma bodies).
7. The body of `diskExcess_upper_bound_via_eq3_eq4` does NOT mention
   any of the forbidden references listed in "Concrete edits expected"
   (verify via `grep -nE` against the substring of the theorem body):
   `paper.eq2_`, `paper.eq5_`, `paper.eq6_`, `paper.eq7_`, `paper.eq8_`,
   `paper.eq9_`, `paper.eq10_`, `paper.eq11_`, `paper.eq12_`,
   `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   `sigmaZeroMinus_monotone_of_summable`,
   `sigmaZeroMinus_summable_of_summable_at_upper`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`,
   `valid_of_eq10_subinterval_branch1`,
   `valid_of_collapsed_disk_eq8_eq9_lower`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
   `eq15_implies_disk_le_annulus`,
   `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
   `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
   `branchSplit`, `branch1SigmaKernel`, `branch1PointwiseFactor`,
   `branch2PointwiseFactor`, `liftGap`.
8. The new `diskExcess_upper_bound_via_eq3_eq4` lemma's signature does
   NOT take any `ρ`, `ρ₁`, `ρ₂`, or other `ρ`-related parameter —
   verify by inspecting the signature (it should take only
   `(paper : Section2Assumptions a b K c)`, `(hc_pos : 0 < c)`,
   `(hc_lt_one : c < 1)`, and the `IntervalIntegrable` hypothesis
   on `(fun r => 2*r*PaperAxioms.circleGap a b r)` over `(0, c)`).
   This is the structural marker that the bound is intrinsically a
   function of `c` alone — no free outer-radius parameter.
9. The conclusion of `diskExcess_upper_bound_via_eq3_eq4` is exactly
   `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
   c ^ 4 * PaperAxioms.sigmaZeroMinus a b c` (verify via `grep` of
   the theorem statement) — no parenthesisation differences, no
   reordering of factors, no extra constants.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V12.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Discharging the `IntervalIntegrable (fun r => 2*r*circleGap a b r)
  volume 0 c` premise. It is intentionally left as a hypothesis,
  consistent with sprint 003's same premise. Deriving it in-house
  from `Section2Assumptions` is the subject of a separate future
  sprint.
* Building the follow-up reducer
  `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` (the natural
  next step after sprint 013). That reducer needs sprint 011
  monotonicity + sprint 006 annulus bound + sprint 013 disk bound +
  three integrability/summability premises, and is comparable in
  size to sprint 013 itself. Queue it as a separate sprint.
* Pushing `c_value` upward in this sprint — the goal is the structural
  disk-side bound, not a numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 013 is purely
  structural — numerical work belongs in a separate sprint.
* Refactoring or simplifying sprints 001–012. Their lemmas are
  consumed verbatim as `sigmaZeroMinus_nonneg_of_pos` (sprint 005)
  is the only existing-Reduction.lean lemma sprint 013 invokes.
* Generalising the new theorem to `r ∈ Ioo 0 c'` with `c' ≤ c`. The
  natural left-edge integration is over the full disk `[0, c]`; a
  sub-interval generalisation would add bookkeeping without enabling
  any new downstream use.
* Adding a parallel `eq3 + eq4` *annulus*-side bound (i.e., bounding
  `circleGap r` upward on `r ∈ (c, 1)`). `eq4` requires `r < c`, so
  it does not apply on the annulus side. A symmetric annulus bound
  would need a different paper hypothesis chain (e.g. `eq8 + eq9`,
  which is sprint 005's chain). Out of scope for sprint 013.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new disk bound. That would require the
  follow-up reducer (out of scope above) plus discharge of its
  kernel inequality, integrability premises, and summability premise.

## Time budget

≤ 30 minutes runtime. The new disk bound is ~40 lines of Lean,
roughly half the size of sprint 003's
`diskExcess_upper_bound_of_eq2_eq3_eq4` (which is ~140 lines). All
Mathlib idioms used (`integral_mono_on_of_le_Ioo`, `integral_const_mul`,
`@integral_pow`, `Continuous.intervalIntegrable`, `change` +
`AnnulusIntegralReduction.annulusSlice`, `simpa [Eq3CircleGapDecomposition]`,
`simpa [Eq4SigmaPlusBound]`) are *already verified* in sprints 002+003
at `Reduction.lean:185-435`. The candidate side lemmas are one to
three lines each.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `paper.eq3_circleGap_decomposition` does not unfold cleanly via
  `simpa [PaperAxioms.Eq3CircleGapDecomposition]` — the pattern is
  *already* used at `Reduction.lean:215-218` in sprint 002, so this
  is known to work in the pinned Mathlib. If for some reason the
  unfolding differs, mirror the existing call site verbatim.
* `paper.eq4_sigmaPlus_bound` does not unfold cleanly via
  `simpa [PaperAxioms.Eq4SigmaPlusBound]` — the pattern is *already*
  used at `Reduction.lean:222-227`. Same fix.
* `intervalIntegral.integral_mono_on_of_le_Ioo` requires
  `IntervalIntegrable` for *both* sides, plus the pointwise bound on
  the open interval `Set.Ioo 0 c`. The pattern is *already* used at
  `Reduction.lean:380` with the exact arguments
  `(hc_le, hInt, hLinIntegrable, hPointwise)`. Mirror that signature.
* `intervalIntegral.integral_const_mul` may require a specific argument
  order (the constant on the LEFT of `*`). The pattern in sprint 003
  at `Reduction.lean:408-409` shows the call. If the integrand is in
  the form `2 * r * (c² * Z_c)`, rewrite via `funext r; ring` to
  put it in the form `(2 * c² * Z_c) * r`, then apply
  `integral_const_mul`.
* `@integral_pow 0 c 1` requires the explicit type-ascription form
  to avoid `intervalIntegral.integral_pow` (which doesn't exist) —
  see Experience.md sprint 003 entry: "Use `@integral_pow 0 c n` and
  clean up the `0^(n+1) = 0` term with `convert ... using 2 <;>
  norm_num`". Mirror the existing pattern at `Reduction.lean:383-386`
  verbatim.
* `change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap
  a b) 0 c = _` followed by `rfl` — the pattern is *already* used at
  `Reduction.lean:425-427` in sprint 003. Mirror verbatim.
* `sigmaZeroMinus_nonneg_of_pos a b hr_pos` requires `0 < r`. From
  `r ∈ Ioo 0 c`, we have `hr.1 : 0 < r`. Pass `hr.1` as the
  positivity hypothesis. The pattern is *already* used at
  `Reduction.lean:618-619` in sprint 007 (with `hc_pos` for
  `c > 0`).
* The final `linarith` call (in the pointwise bound) requires
  `circleGap a b r = sigmaPlus a b r - r² * sigmaZeroMinus a b r`,
  `sigmaPlus a b r ≤ c² * sigmaZeroMinus a b c`, and
  `0 ≤ r² * sigmaZeroMinus a b r` in scope. All three are
  established by the preceding lines.
* If `linarith` fails on the final pointwise step, fall back to
  `calc`:

  ```lean
  calc PaperAxioms.circleGap a b r
      = PaperAxioms.sigmaPlus a b r
          - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := h3
    _ ≤ PaperAxioms.sigmaPlus a b r := by linarith
    _ ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := hSigmaPlus_le
  ```

* Any of acceptance criteria 4, 5, 6, 7, 8, 9 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat the
  "only `eq3 + eq4`" structural guarantee of this sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
