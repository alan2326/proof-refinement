# Sprint 021: Decoupled disk-anchor reducer `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` — the workspace's **first closing reducer with a free disk-side anchor `ρ_disk` decoupled from the annulus window `[ρ₁, ρ₂]`**, the **first reducer whose disk-side bound is the non-constant kernel `branch1SigmaKernel c ρ_disk · ρ_disk² · Z_{ρ_disk}` (varying with `ρ_disk` in `(c, branchSplit c)`)**, and the **first reducer whose Z-extraction step bridges from a strictly interior anchor `ρ_disk < ρ₁` to the annulus window via two cascaded series-monotonicity invocations**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V20.lean`
**Target file**: `Candidates/V21.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ_disk ρ₁ ρ₂ : ℝ,
          c < ρ_disk ∧ ρ_disk < PaperAxioms.branchSplit c ∧
          ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) ≤
              ∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The admissible witness exposes **three independent radial parameters**:

* `ρ_disk ∈ (c, branchSplit c)` — the disk-side anchor where sprint 015's
  `diskExcess_upper_bound_via_eq5` is evaluated;
* `[ρ₁, ρ₂]` with `ρ_disk ≤ ρ₁ ≤ ρ₂ < 1` — the annulus-side window where
  sprint 006's `annulusExcess_lower_bound_of_eq8_eq9` is integrated.

This is the **first workspace closing reducer whose disk-side anchor and
annulus-side window are decoupled free parameters**. Every prior closing
reducer either:

* anchors the disk side at `c` (sprint 014, via sprint 013's `c⁴ · Z_c`); or
* anchors the disk side at `ρ₁` (sprint 017, via sprint 016's `c⁴/2 · Z_{ρ₁}`
  with `ρ₁` simultaneously the annulus-window left edge); or
* uses no series-side disk bound at all (sprints 008, 018, 019, 020).

Sprint 021 takes sprint 015's *non-constant in `ρ_disk`* disk-side bound
`branch1SigmaKernel c ρ_disk · ρ_disk² · Z_{ρ_disk}` and pairs it with sprint
006's annulus integral over a *separate* free window `[ρ₁, ρ₂]`. The Z
extraction now requires the cascade

`Z_{ρ_disk} ≤ Z_{ρ₁} ≤ Z_{ρ'} for every ρ' ∈ [ρ₁, ρ₂]`

which uses sprint 011 *twice* (once at `ρ_disk → ρ₁`, once at `ρ₁ → ρ'`) plus
sprint 012's summability transfer at the right edge.

The proof body fuses six already-verified workspace ingredients:

1. **Disk-side bound at `ρ_disk`.** Apply
   `diskExcess_upper_bound_via_eq5 paper hcρ_disk hρ_disk_split` to obtain
   `diskExcess ≤ branch1SigmaKernel c ρ_disk · ρ_disk² · Z_{ρ_disk}`. No
   integration on the disk side.

2. **Cascaded Z-monotonicity.** Apply
   `sigmaZeroMinus_monotone_of_summable` (sprint 011) once to get
   `Z_{ρ_disk} ≤ Z_{ρ₁}` (using `ρ_disk ≤ ρ₁` and a summability hypothesis at
   `ρ₁`). Apply it again on each `ρ' ∈ [ρ₁, ρ₂]` (mirroring sprint 017's
   `hZmono` block, `Reduction.lean:2016-2029`) to get
   `Z_{ρ₁} ≤ Z_{ρ'}`. Compose: `Z_{ρ_disk} ≤ Z_{ρ'}` for every
   `ρ' ∈ [ρ₁, ρ₂]`. The summability premise at `ρ₁` is derived from the
   summability at `ρ₂` (the witness's last `Summable` field) by sprint 012's
   `sigmaZeroMinus_summable_of_summable_at_upper hρ₁_nonneg hρ₁_le_ρ₂
   hSummable_top`. The summability premise needed by sprint 011 at the inner
   step also follows from sprint 012 applied at each `ρ'`.

3. **Multiply the kernel inequality by `Z_{ρ_disk} ≥ 0`.** Mirror sprint
   017's `hStepA` (`Reduction.lean:1998-2003`):
   `(branch1SigmaKernel c ρ_disk · ρ_disk²) · Z_{ρ_disk} ≤
    (∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ') · Z_{ρ_disk}`.

4. **Pull `Z_{ρ_disk}` inside the integral.** Mirror sprint 017's `hStepB`
   (`Reduction.lean:2005-2014`) via `intervalIntegral.integral_mul_const`.

5. **Integrate the cascaded pointwise bound to dominate by sprint 006's
   integrand `2ρ'³ · Z_{ρ'} / Λ(c,ρ')`.** Mirror sprint 017's `hPointwise`
   block (`Reduction.lean:2037-2052`), but with `Z_{ρ_disk}` (not `Z_{ρ₁}`)
   on the LHS. The integrand-monotonicity argument is identical once the
   pointwise inequality `Z_{ρ_disk} ≤ Z_{ρ'}` is in scope.

6. **Final calc chain.** `diskExcess ≤ … ≤ ∫_{ρ₁..ρ₂} 2ρ'³ · Z_{ρ'}/Λ(c,ρ') dρ' ≤ annulusExcess`. The last step uses sprint 006's
   `annulusExcess_lower_bound_of_eq8_eq9` directly.

Then ship a `Candidates/V21.lean` at the same `c = 0.3554` that compiles,
scores `≥ V20`, and *materialises* the new lemma in side lemmas
`v21_decoupled_anchor_compiles` and
`v21_decoupled_anchor_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so the
score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c` headroom.
Sprint 021 ships a structurally novel reducer along three independent axes
that no prior workspace sprint touches:

1. **First closing reducer with a free disk-side anchor decoupled from the
   annulus window.** Every prior workspace closing reducer that mixes a disk
   bound with an annulus integral pins the two together: sprint 014 forces
   `ρ_disk = c` (sprint 013's input), sprint 017 forces `ρ_disk = ρ₁` (sprint
   016's input). Sprint 021 lets `ρ_disk ∈ (c, branchSplit c)` and
   `[ρ₁, ρ₂] ⊆ [ρ_disk, 1)` vary independently. **At the seed**
   `c_value = 0.3554`, this enlarges the witness space along an entirely new
   dimension: a witness like `ρ_disk = 0.38, ρ₁ = 0.42, ρ₂ = 0.7` is
   admissible to sprint 021 with `ρ_disk` strictly less than `branchSplit
   c_value ≈ 0.4103` and `ρ₁` strictly greater than `branchSplit c_value` —
   inadmissible to every prior reducer. Sprint 014 forces `ρ_disk = c`;
   sprint 017 forces `ρ_disk = ρ₁ ≥ branchSplit c_value` (i.e. branch-2 disk
   anchor only). Sprint 021 is the **only** workspace reducer admitting a
   branch-1 disk anchor combined with a branch-2-or-straddling annulus
   window.

2. **First reducer whose disk-side bound is the non-constant kernel
   `branch1SigmaKernel c ρ_disk · ρ_disk²` (varying with `ρ_disk`).** Sprint
   014's disk side is `c⁴` (the `(3)+(4)` integrated form anchored at `r =
   c`); sprint 017's disk side collapses algebraically to the constant
   `c⁴/2`. Sprint 021's disk side `branch1SigmaKernel c ρ_disk · ρ_disk²`
   does *not* collapse to a constant in `ρ_disk`: explicitly,
   `branch1SigmaKernel c ρ ρ² = ρ²·(c⁴ − 2c²ρ² + ρ⁴)/(2(ρ² − c²)²) · ρ²`
   *(the published Wang formula; verify in
   `KorenblumPaper.PaperAxioms.branch1SigmaKernel`)*. Optimizing the witness
   over `ρ_disk ∈ (c, branchSplit c)` becomes a genuine new degree of
   freedom — at `ρ_disk = c⁺` the kernel diverges (so the bound is
   trivially loose), but as `ρ_disk → branchSplit c` the kernel approaches
   the closed-form `c⁴/2` (where sprint 015's bound meets sprint 016's
   bound, by the paper-internal cross-check noted in sprint 015's bulletin
   entry). The kernel `branch1SigmaKernel c ρ_disk · ρ_disk²` strictly
   decreases as `ρ_disk` increases on `(c, branchSplit c)`, so the *tightest*
   sprint-015 disk-side bound is at `ρ_disk → branchSplit c⁻`. Sprint 021
   exposes this optimization — sprints 014/017 don't even have the parameter
   to optimize over.

3. **First reducer whose Z-extraction step requires a *cascaded*
   `sigmaZeroMinus` monotonicity bridge from `ρ_disk` interior to the
   annulus window**: `Z_{ρ_disk} ≤ Z_{ρ₁} ≤ Z_{ρ'}` for every `ρ' ∈
   [ρ₁, ρ₂]`. Sprint 014's Z-extraction is one-step `Z_c ≤ Z_{ρ'}` (with
   `ρ_disk = c`); sprint 017's is one-step `Z_{ρ₁} ≤ Z_{ρ'}` (with `ρ_disk
   = ρ₁`). Sprint 021 chains *two* applications of
   `sigmaZeroMinus_monotone_of_summable` — first at the boundary `ρ_disk →
   ρ₁` (using a summability hypothesis at `ρ₁` derived from the witness's
   summability at `ρ₂` via sprint 012), then on each `ρ' ∈ [ρ₁, ρ₂]`
   (mirroring sprint 017's `hZmono` block exactly). This is the **first
   workspace reducer that proves a series-level inequality `Z_{ρ_disk} ≤
   Z_{ρ'}` between two points neither of which is a window endpoint**.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V21 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` parameterised by *three*
  independent radial knobs `(ρ_disk, ρ₁, ρ₂)` plus the kernel inequality
  premise.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the decoupled-anchor sub-regime is non-empty at the
  seed — the kernel inequality `branch1SigmaKernel c ρ_disk · ρ_disk² ≤
  ∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ'` is **not** numerically discharged at the
  seed in this sprint and remains an existential premise on the new
  reducer.

Why this is **not** "the same chain" as sprint 017:

* **Different disk-side equation consumed.** Sprint 017 consumes
  `paper.eq6_branch2_sigmaReduction` via `diskExcess_upper_bound_via_eq6`,
  with admissibility `branchSplit c < ρ_disk = ρ₁`. Sprint 021 consumes
  `paper.eq5_branch1_sigmaReduction` via `diskExcess_upper_bound_via_eq5`,
  with admissibility `c < ρ_disk < branchSplit c`. **Disjoint paper-axiom
  consumption on the disk side, disjoint admissibility regions for
  `ρ_disk`.**
* **Decoupled disk anchor.** Sprint 017 forces `ρ_disk = ρ₁`, collapsing
  the cascade to a single Z-monotonicity invocation. Sprint 021 has
  `ρ_disk ≤ ρ₁` as a strict inequality (two distinct radial parameters),
  requiring the cascaded Z-monotonicity bridge described above. **The
  proof body has a strictly larger Z-monotonicity argument by exactly one
  cascade step.**
* **Different kernel shape on the disk side.** Sprint 017's disk-side
  kernel collapses to the constant `c⁴/2`. Sprint 021's disk-side
  kernel `branch1SigmaKernel c ρ_disk · ρ_disk²` does *not* collapse to a
  constant in `ρ_disk` — it is a genuine function of `ρ_disk` over
  `(c, branchSplit c)`. **Sprint 021's reducer signature exposes
  `ρ_disk` as a free parameter that sprint 017 cannot.**
* **Different admissible windows.** Sprint 017 requires `branchSplit c <
  ρ₁ ≤ ρ₂ < 1`. Sprint 021 requires `c < ρ_disk < branchSplit c` and
  `ρ_disk ≤ ρ₁ ≤ ρ₂ < 1`, which **admits annulus windows
  `[ρ₁, ρ₂]` with `ρ₁ < branchSplit c`** (i.e. annulus windows that
  start in the branch-1 sub-regime), strictly enlarging the
  admissibility cell.

Why this is **not** "the same chain" as sprint 014:

* **Different disk-side equation.** Sprint 014 consumes
  `(3)+(4)` via sprint 013's `diskExcess_upper_bound_via_eq3_eq4` with
  closed form `c⁴ · Z_c`. Sprint 021 consumes `(5)` via sprint 015's
  `diskExcess_upper_bound_via_eq5` with closed form `branch1SigmaKernel
  c ρ_disk · ρ_disk² · Z_{ρ_disk}`. **Disjoint disk-side paper-axiom
  consumption, disjoint disk-side closed forms.**
* **Variable disk anchor vs. fixed disk anchor at `c`.** Sprint 014
  pins the disk-side `Z` evaluation at `r = c`; sprint 021 evaluates
  `Z` at a free anchor `ρ_disk ∈ (c, branchSplit c)`. **Sprint 021's
  reducer optimizes over `ρ_disk` — sprint 014 cannot.**
* **One-cascade vs. two-cascade Z-monotonicity bridge.** Sprint 014's
  Z-monotonicity is `Z_c ≤ Z_{ρ'}` for `ρ' ∈ [ρ₁, ρ₂] ⊂ (c, 1)` — one
  step. Sprint 021's bridge is `Z_{ρ_disk} ≤ Z_{ρ₁} ≤ Z_{ρ'}` — two
  cascaded steps with intermediate summability transfer at `ρ₁`. **The
  proof body invokes `sigmaZeroMinus_monotone_of_summable` strictly more
  times than sprint 014 (two vs. one cascade levels).**

Why this is **not** "the same chain" as sprints 008/018/019/020 (the
direct-pointwise-bound chains):

* **Series-level disk reduction.** Sprints 008/018/019/020 close via the
  pointwise paper inequalities `(10)`/`(11)` (or their derivations) plus
  a windowed mass premise on `scalarIntegrand1` or `scalarIntegrand2`.
  No `sigmaZeroMinus`, no `sigmaMinus` appears in their proof bodies.
  Sprint 021's disk side sits squarely in the series world: it consumes
  `(5)` and produces a `branch1SigmaKernel · ρ_disk² · Z_{ρ_disk}`
  expression. **Disjoint analytical chains; sprint 021 has no
  `mass_mul_le_annulusSlice_of_integral_bound_ae` invocations and no
  `paperScalarIntegrand1_intervalIntegrable` invocations.**
* **No annulus slice splitting.** Sprints 008/018/019/020 split the
  annulus excess into adjacent slices via `annulusSlice_add_adjacent`.
  Sprint 021 invokes sprint 006's `annulusExcess_lower_bound_of_eq8_eq9`
  directly — no slice splitting on the annulus side.

Why this is **bounded enough for one Generator session**:

* Six already-verified ingredients: `diskExcess_upper_bound_via_eq5`
  (sprint 015), `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006),
  `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
  `sigmaZeroMinus_monotone_of_summable` (sprint 011),
  `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012),
  `intervalIntegral.integral_mul_const` (Mathlib).
* The proof body is a **structural elaboration of sprint 017's body**,
  swapping sprint 016 → sprint 015 on the disk side and adding **one
  extra Z-monotonicity step** at the start of the cascade. Sprint 017's
  body (`Reduction.lean:1957-…`) is the precise template; the new step
  is a single `have hZ_disk_le_ρ₁ : Z_{ρ_disk} ≤ Z_{ρ₁} := …` followed
  by a `le_trans` composition with sprint 017's existing
  `hZmono`-equivalent block.
* Concretely, the new analytical step is:

  ```lean
  -- Cascaded Z-monotonicity from ρ_disk to ρ₁:
  have hSummable_ρ₁ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ₁ ^ (2 * k - 2)
        else 0) :=
    sigmaZeroMinus_summable_of_summable_at_upper
      hρ₁_nonneg hρ₁_le_ρ₂ hSummable_top
  have hZ_disk_le_ρ₁ :
      PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
        PaperAxioms.sigmaZeroMinus a b ρ₁ :=
    sigmaZeroMinus_monotone_of_summable
      hρ_disk_nonneg hρ_disk_le_ρ₁ hSummable_ρ₁
  -- Then sprint 017's existing inner-cascade block gives
  -- Z_{ρ₁} ≤ Z_{ρ'} for every ρ' ∈ [ρ₁, ρ₂]; compose via le_trans.
  have hZmono_full :
      ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
        PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
          PaperAxioms.sigmaZeroMinus a b ρ' := by
    intro ρ' hρ'
    exact le_trans hZ_disk_le_ρ₁ (hZmono_inner ρ' hρ')
  ```

  Everything else in the proof body is **verbatim sprint 017
  scaffolding** with `Z_{ρ₁}` replaced by `Z_{ρ_disk}` and the multiply-
  and-pull-constant steps now using `Z_{ρ_disk}` instead of `Z_{ρ₁}`.
* Estimate: ~250 lines for the new theorem (slightly shorter than
  sprint 017's ~234 lines because the disk-side collapse is simpler —
  sprint 015's output already exposes `branch1SigmaKernel c ρ_disk ·
  ρ_disk²` in the form needed; no `field_simp` collapse to a constant
  is required since the kernel stays as a function of `ρ_disk`).
* No new Mathlib lemmas needed. Every Lean idiom used
  (`diskExcess_upper_bound_via_eq5`,
  `annulusExcess_lower_bound_of_eq8_eq9`,
  `sigmaZeroMinus_nonneg_of_pos`,
  `sigmaZeroMinus_monotone_of_summable`,
  `sigmaZeroMinus_summable_of_summable_at_upper`,
  `intervalIntegral.integral_mul_const`,
  `intervalIntegral.integral_mono_on`,
  `mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left`,
  `div_nonneg`, `le_trans`, `WangPaperSideConditions.paperLambda_pos`,
  `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`, `calc`)
  is **already verified at the cited line ranges in sprints 015 and
  017**.
* The candidate side lemmas are 5–25 lines each (matching V19/V20).
  Total V21 size: ≤ 130 lines.

Why this beats the alternatives I considered (ultrathink phase):

* **A: Branch-2 mirror of sprint 019 — `valid_of_eq6_eq8_eq9_subinterval_branch2`
  via `eq11_of_eq6_eq8_eq9`.** Sprint 020's contract explicitly
  demoted this as "diminishing analytical return — third
  consecutive mechanical mirror of sprints 008/018/019." The bulletin
  rule ("if a sprint reduces to 'more of the same chain', reject it
  and require a structural proposal") applies. **Demoted.**

* **B: Straddling-window reducer in derived-pointwise form via
  `eq10_of_eq5_eq8_eq9` + `eq11_of_eq6_eq8_eq9`.** Mechanical
  combination of sprint 020 + sprint 019's derivation chains.
  Mostly compositional, low novelty per Generator session.
  **Demoted.**

* **C (selected, this sprint): decoupled-anchor reducer mixing sprint
  015 and sprint 006 with cascaded Z-monotonicity.** Highest analytical
  novelty per Generator session: ships **three** simultaneously novel
  ingredients (free disk anchor, non-constant disk kernel, cascaded
  series-level monotonicity bridge). All ingredients pre-verified;
  proof shape mirrors sprint 017 with one extra cascade step. **Selected.**

* **D: New `(2)`-derived two-anchor upper bound on `Z_c` (i.e. solving
  `(2)` for `Z_c`).** From `(2)`: `Z_r ≥ ((ρ²−r²)/(ρ²−c²))·Z_c −
  ((c²−r²)/(ρ²−c²))·Z_ρ`, so `Z_c ≤ ((ρ²−c²)·Z_r + (c²−r²)·Z_ρ)/(ρ²−r²)`
  for `r ∈ [0, c)` and `ρ ∈ (c, 1)`. Could substitute into sprint 013's
  `diskExcess ≤ c⁴ · Z_c` to give a two-anchor bound on `diskExcess`.
  **Demoted: the resulting kernel has both `Z_r` *and* `Z_ρ`, which
  doesn't collapse to a single Z that can be extracted via
  monotonicity. Pursuing it would require a multi-anchor extraction
  lemma not in the current toolkit. Speculative — file as a future
  proposal if multi-anchor `Z` arithmetic becomes needed.**

* **E: Series-level continuity / left-edge limit lemmas for `s ↦
  sigmaZeroMinus a b s`.** Speculative; demoted in sprints 016–020
  with no concrete consumer queued. **Still demoted.**

* **F: `paperLambda` upper-envelope from `paper.eq7_paperK_formula`
  alone.** Speculative; requires structural exploration of
  `OneModePaperBridge` interior beyond a single Generator session.
  **Demoted.**

* **G: Numerical-oracle registration discharging the kernel
  `branch1SigmaKernel c ρ_disk · ρ_disk² ≤ ∫ 2ρ'³/Λ` at the seed.**
  Premature — needs sprint 021's reducer signature to exist first
  (so the oracle has a Lean-facing target). After sprint 021, this
  becomes a viable follow-up. **Deferred to a post-021 sprint.**

* **H: Z-free version of sprint 017** (extract `Z_{ρ₁}` from both
  sides). Demoted in sprints 018/019 as low-novelty refactor. **Still
  demoted.**

* **I: `(2)+(3)+(4)`-chain straddling reducer** — mirror sprint 020's
  shape but consume sprint 002's `circleGap_inner_bound_of_eq2_eq3_eq4`
  on the disk side. **Demoted: structurally similar to sprint 020 with
  a disk-side ingredient swap; the analytical novelty per session is
  lower than sprint 021's three new structural axes.**

* **J: Cross-validation theorem `branch1SigmaKernel c ρ · ρ² · Z_ρ ≤
  c⁴/2 · Z_ρ` on `ρ → branchSplit c⁻`** — the closed-form witness that
  sprint 015's kernel collapses to sprint 016's at the branch boundary.
  Demoted in sprint 020's contract as too narrow. **Still demoted.**

Compared to A–J, candidate C (this sprint, sprint 021,
`valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`) maximises
analytical novelty per bounded Generator session: it ships the **first
workspace closing reducer with three independent radial parameters**,
the **first reducer whose disk-side closed form is a non-constant
function of a free anchor `ρ_disk`**, and the **first reducer whose Z-
extraction step is a *cascade* of two `sigmaZeroMinus` monotonicity
invocations bridging from a non-window-endpoint anchor**. It uses **only
existing trusted modules + pinned Mathlib + already-verified
`Reduction.lean` lemmas** in patterns directly mirrored from sprint 017.
No proposal needed.

### Note on `branch1SigmaKernel c ρ_disk · ρ_disk²` — algebraic shape

From `KorenblumPaper.PaperAxioms.branch1SigmaKernel` (verify at the
definition site), the kernel `branch1SigmaKernel c ρ` is the closed form
the paper attaches to `(5)`. The product `branch1SigmaKernel c ρ · ρ²`
appearing in sprint 015's output is left **uncollapsed** in sprint 021's
contract — it is **not** algebraically simplified to a closed form
involving `c, ρ_disk` because the published shape `branch1SigmaKernel c
ρ_disk · ρ_disk²` is the natural form of sprint 015's output and is what
the witness's kernel inequality expects on the LHS.

If the Generator finds the literal expression `branch1SigmaKernel c
ρ_disk * ρ_disk ^ 2` cumbersome, it MAY introduce a local abbreviation
via `let K_disk := PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2`
and reuse `K_disk` throughout, matching sprint 017's approach with
`c^4/2` (at `Reduction.lean:1986-1988`). The contract's witness
signature must, however, use the literal `PaperAxioms.branch1SigmaKernel
c ρ_disk * ρ_disk ^ 2` form — **no algebraic simplification of the
disk-side kernel is required or admitted in this sprint**.

### Note on the witness lemma at the seed

At the seed `c_value = 0.3554`, `branchSplit c_value = c_value · √(4/3)
≈ 0.4103`. The cleanest concrete witness is the **degenerate** case
`ρ_disk = ρ₁ = ρ₂ = (c_value + branchSplit c_value)/2` collapsed at the
midpoint of `(c_value, branchSplit c_value)`. The conditions reduce to:

* `c_value < (c_value + branchSplit c_value)/2` ⟺ `c_value < branchSplit
  c_value` (sprint 017's body, `Reduction.lean:1963-1972`);
* `(c_value + branchSplit c_value)/2 < branchSplit c_value` ⟺ `c_value <
  branchSplit c_value` (same);
* `(c_value + branchSplit c_value)/2 ≤ (c_value + branchSplit c_value)/2`
  trivially `le_rfl`;
* `(c_value + branchSplit c_value)/2 ≤ (c_value + branchSplit c_value)/2`
  trivially `le_rfl`;
* `(c_value + branchSplit c_value)/2 < 1` ⟺ `branchSplit c_value < 2 −
  c_value ≈ 1.6446`, which holds because `branchSplit c_value < 1` (V8's
  `v8_split_lt_one_at_seed` body).

A **simpler** alternative witness: pick `ρ_disk = ρ₁ = ρ₂ = c_value +
ε` for any rational `ε ∈ (0, branchSplit c_value − c_value)`. The
cleanest is `ρ_disk = ρ₁ = ρ₂ = 4/10`:
* `c_value < 4/10` ⟺ `0.3554 < 0.4` (`norm_num`);
* `4/10 < branchSplit c_value` ⟺ `4/10 < c_value · √(4/3) = 0.3554 ·
  √(4/3) ≈ 0.4103`. This needs `√(4/3) > 4/(10 · 0.3554) =
  10000/(10 · 3554) = 1000/3554 ≈ 1.1255`, achievable via `nlinarith`
  with `1.13² = 1.2769 < 4/3 = 1.333…` (so `√(4/3) > 1.13 > 1.1255`).

The **degenerate-midpoint** witness is preferred for time-budget reasons
because it inherits the existing `c_value < branchSplit c_value` lemma
verbatim from sprint 017. The `4/10` witness requires **one extra
`nlinarith` block** to discharge `4/10 < branchSplit c_value` —
acceptable but not minimal.

### Note on what the witness lemma should NOT do

Sprint 021's V21 witness lemma is **structural only** — it confirms that
the admissible-window predicate `c_value < ρ_disk < branchSplit c_value
∧ ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1` is non-vacuous at the seed by
exhibiting concrete `ρ_disk, ρ₁, ρ₂`. It **does NOT discharge the
integrability premises, the summability premise, nor the kernel
inequality `branch1SigmaKernel c ρ_disk · ρ_disk² ≤ ∫_{ρ₁..ρ₂}
2ρ'³/Λ(c,ρ') dρ'`**. Those remain as existential hypotheses on the new
reducer, just like V8/V14/V17/V18/V19/V20's witnesses do not discharge
their respective sprints' premises.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` matching the
    shape above. The proof body must:

    1. **Open `valid_of` framework.** `refine ⟨hc_pos, hc_lt_one, ?_⟩;
       intro a b K paper; obtain ⟨ρ_disk, ρ₁, ρ₂, hcρ_disk,
       hρ_disk_split, hρ_disk_le_ρ₁, hρ₁_le_ρ₂, hρ₂_lt_one,
       hIntCircle, hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
       h_witness paper`.

    2. **Geometric scaffolding.** Derive `hρ_disk_pos := lt_trans
       hc_pos hcρ_disk`, `hρ_disk_nonneg := hρ_disk_pos.le`,
       `hρ_disk_lt_one := lt_of_lt_of_lt hρ_disk_split hSplit_lt_one`
       (where `hSplit_lt_one` is derived locally as in sprint 017's
       body `Reduction.lean:1963-1972`), `hρ₁_pos := lt_of_lt_of_le
       hρ_disk_pos hρ_disk_le_ρ₁`, `hρ₁_nonneg := hρ₁_pos.le`,
       `hρ₁_le_ρ₂_alt`, `hρ₂_pos := lt_of_lt_of_le hρ₁_pos hρ₁_le_ρ₂`,
       `hρ₂_nonneg := hρ₂_pos.le`, `hcρ₁ := lt_of_lt_of_le hcρ_disk
       hρ_disk_le_ρ₁`, `hρ₁_lt_one := lt_of_le_of_lt hρ₁_le_ρ₂
       hρ₂_lt_one`. Mirror sprint 017's scaffolding block at
       `Reduction.lean:1957-1976`.

    3. **Disk-side bound at `ρ_disk` via sprint 015.** `have hDiskRaw
       := diskExcess_upper_bound_via_eq5 paper hcρ_disk
       hρ_disk_split`. This gives `diskExcess ≤ branch1SigmaKernel c
       ρ_disk · ρ_disk² · Z_{ρ_disk}` with the kernel **left
       uncollapsed**.

    4. **Z_{ρ_disk} ≥ 0 via sprint 005.** `have hZ_disk_nonneg :
       0 ≤ PaperAxioms.sigmaZeroMinus a b ρ_disk :=
       sigmaZeroMinus_nonneg_of_pos a b hρ_disk_pos`.

    5. **Step (a): multiply the kernel inequality by `Z_{ρ_disk} ≥ 0`.**
       Mirror sprint 017's `hStepA` (`Reduction.lean:1998-2003`):

       ```lean
       have hStepA :
           (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) *
               PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
             (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
               * PaperAxioms.sigmaZeroMinus a b ρ_disk :=
         mul_le_mul_of_nonneg_right hKernel hZ_disk_nonneg
       ```

    6. **Step (b): pull `Z_{ρ_disk}` inside the integral.** Mirror
       sprint 017's `hStepB` (`Reduction.lean:2005-2014`):

       ```lean
       have hStepB :
           (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
               * PaperAxioms.sigmaZeroMinus a b ρ_disk =
             ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                   * PaperAxioms.sigmaZeroMinus a b ρ_disk :=
         (intervalIntegral.integral_mul_const
             (PaperAxioms.sigmaZeroMinus a b ρ_disk)
             (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
       ```

    7. **Cascaded Z-monotonicity bridge** — the **unique new step**.
       First derive summability at `ρ₁` from summability at `ρ₂` via
       sprint 012:

       ```lean
       have hSummable_ρ₁ :
           Summable (fun k : ℕ =>
             if PaperAxioms.n2Pred a b k then
               PaperAxioms.coeffMinusGap a b k * ρ₁ ^ (2 * k - 2)
             else 0) :=
         sigmaZeroMinus_summable_of_summable_at_upper
           hρ₁_nonneg hρ₁_le_ρ₂ hSummable_top
       ```

       Then derive the boundary inequality `Z_{ρ_disk} ≤ Z_{ρ₁}` via
       sprint 011:

       ```lean
       have hZ_disk_le_ρ₁ :
           PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
             PaperAxioms.sigmaZeroMinus a b ρ₁ :=
         sigmaZeroMinus_monotone_of_summable
           hρ_disk_nonneg hρ_disk_le_ρ₁ hSummable_ρ₁
       ```

       Then derive the inner-cascade `Z_{ρ₁} ≤ Z_{ρ'}` for `ρ' ∈
       [ρ₁, ρ₂]`, **verbatim from sprint 017**'s `hZmono` block at
       `Reduction.lean:2016-2029`:

       ```lean
       have hZmono_inner :
           ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
             PaperAxioms.sigmaZeroMinus a b ρ₁ ≤
               PaperAxioms.sigmaZeroMinus a b ρ' := by
         intro ρ' hρ'
         have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
         have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
         have hρ'_nonneg : 0 ≤ ρ' :=
           le_of_lt (lt_of_lt_of_le hρ₁_pos hρ₁_le_ρ')
         have hSummable_ρ' :=
           sigmaZeroMinus_summable_of_summable_at_upper
             hρ'_nonneg hρ'_le_ρ₂ hSummable_top
         exact sigmaZeroMinus_monotone_of_summable
           hρ₁_nonneg hρ₁_le_ρ' hSummable_ρ'
       ```

       Compose via `le_trans`:

       ```lean
       have hZmono_full :
           ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
             PaperAxioms.sigmaZeroMinus a b ρ_disk ≤
               PaperAxioms.sigmaZeroMinus a b ρ' := by
         intro ρ' hρ'
         exact le_trans hZ_disk_le_ρ₁ (hZmono_inner ρ' hρ')
       ```

    8. **Step (c): integrate the cascaded pointwise bound to dominate
       by sprint 006's integrand `2ρ'³ · Z_{ρ'} / Λ(c,ρ')`.** Mirror
       sprint 017's `hPointwise` block (`Reduction.lean:2037-2052`)
       with `Z_{ρ_disk}` in place of `Z_{ρ₁}`. The integrand
       monotonicity argument is identical once `hZmono_full` is in
       scope. Then apply `intervalIntegral.integral_mono_on` (or
       `intervalIntegral.integral_mono_on_of_le_Ioo` if the bound is
       on `Set.Ioo`).

    9. **Step (d): dominate by sprint 006's annulus-excess lower
       bound.**

       ```lean
       have hAnnulus :=
         annulusExcess_lower_bound_of_eq8_eq9 paper hcρ₁ hρ₁_le_ρ₂
           hρ₂_lt_one hIntCircle hIntLambdaZ
       ```

       (Verify sprint 006's signature at `Reduction.lean:649-…` and
       feed it the matching premises.)

    10. **Final calc chain.** Compose:

        ```lean
        calc
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
              ≤ PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2 *
                  PaperAxioms.sigmaZeroMinus a b ρ_disk := hDiskRaw
          _ = (PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) *
                PaperAxioms.sigmaZeroMinus a b ρ_disk := by ring
          _ ≤ (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
                * PaperAxioms.sigmaZeroMinus a b ρ_disk := hStepA
          _ = ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                   * PaperAxioms.sigmaZeroMinus a b ρ_disk := hStepB
          _ ≤ ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                   WangOuter.paperLambda K c ρ' := by
                exact intervalIntegral.integral_mono_on hρ₁_le_ρ₂
                  hIntLambda_mul hIntLambdaZ hPointwise
          _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c :=
              hAnnulus
        ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 021's `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`
    is the workspace's **first closing reducer with three independent
    radial parameters** `(ρ_disk, ρ₁, ρ₂)`, the **first reducer
    whose disk-side bound is the non-constant kernel `branch1SigmaKernel
    c ρ_disk · ρ_disk²` (varying with `ρ_disk` over `(c, branchSplit
    c)`)**, and the **first reducer whose Z-extraction is a cascade of
    two `sigmaZeroMinus` monotonicity invocations bridging from a non-
    window-endpoint disk anchor**. Sprint 021's sufficient condition is
    a strict generalisation of sprint 017's branch-2 reducer (it
    introduces a free `ρ_disk` parameter; sprint 017 forces `ρ_disk =
    ρ₁` collapsing to the constant `c⁴/2` kernel) and admits annulus
    windows with `ρ₁ < branchSplit c` that no prior reducer addresses.

  * The body of `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`
    MAY invoke:

    * `paper.eq5_branch1_sigmaReduction` (only via the wrapper
      `diskExcess_upper_bound_via_eq5` from sprint 015 — the body
      should NOT invoke `paper.eq5_branch1_sigmaReduction` directly,
      to maintain the chain-via-sprint-015 structural marker),
    * `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`,
      `paper.eq7_paperK_formula` (via the wrapper
      `annulusExcess_lower_bound_of_eq8_eq9` from sprint 006 — these
      should also be invoked via sprint 006's wrapper, not directly),
    * `diskExcess_upper_bound_via_eq5` (sprint 015's main output,
      the unique direct disk-side workspace lemma consumed),
    * `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006's main
      output, the unique direct annulus-side workspace lemma consumed),
    * `sigmaZeroMinus_nonneg_of_pos` (sprint 005's series identity
      consequence),
    * `sigmaZeroMinus_monotone_of_summable` (sprint 011's
      monotonicity, consumed twice — once at `ρ_disk → ρ₁`, once at
      `ρ₁ → ρ'` for each `ρ' ∈ [ρ₁, ρ₂]`),
    * `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012's
      summability transfer, consumed at least twice — once at `ρ₂ →
      ρ₁` and once per `ρ'` in the inner cascade),
    * `intervalIntegral.integral_mul_const`,
      `intervalIntegral.integral_mono_on`,
      `IntervalIntegrable.mul_const`,
      `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `div_nonneg`, `le_trans`, `lt_trans`, `lt_of_lt_of_le`,
      `lt_of_le_of_lt`,
      `WangPaperSideConditions.paperLambda_pos`,
      `Real.sqrt_nonneg`, `Real.sq_sqrt` (for the local
      `c < branchSplit c` derivation, verbatim from sprint 017),
      `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`,
      `calc`, `rfl`, `unfold`, `show`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that the new reducer
    reaches closure through the **sprint 015 + sprint 006 + sprints
    011/012 chain only**, with the sprint-015-anchored disk side
    decoupled from the annulus window):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq6_`,
      `paper.eq10_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
      `paper.eq14_`, `paper.eq15_` (only `(5)+(7)+(8)+(9)` of the paper
      hypotheses are admitted along this chain),
    * `paper.eq5_branch1_sigmaReduction` directly (must go through
      `diskExcess_upper_bound_via_eq5`),
    * `paper.eq8_sigma_to_liftGap` directly,
      `paper.eq9_liftGap_to_circleGap` directly (must go through
      `annulusExcess_lower_bound_of_eq8_eq9`),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
      `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9` (no derived paper
      theorems — sprint 021 must use the published `(5)` only via
      sprint 015 and the published `(8)+(9)` only via sprint 006),
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
      `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`,
      `valid_of_eq11_subinterval_branch2`,
      `valid_of_eq5_eq8_eq9_subinterval_branch1`,
      `valid_of_eq10_eq11_straddling_window` (no upstream closing
      reducer — sprint 021 must close on its own),
    * `eq15_implies_disk_le_annulus`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq6` (these are markers of the
      `(2)+(3)+(4)` and `(6)` disk-side chains — sprint 021 must
      consume only the `(5)` disk-side chain via sprint 015),
    * `circleGap_outer_lower_bound_of_eq8_eq9` directly (must go
      through sprint 006's wrapper, not sprint 005's pointwise bound),
    * `mass_mul_le_annulusSlice_of_integral_bound_ae`,
      `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
      `annulusDensity_nonneg_of_lt`, `annulusExcess_nonneg`,
      `paperScalarIntegrand1_intervalIntegrable`,
      `paperScalarIntegrand2_intervalIntegrable` (these are markers of
      the windowed-mass-premise chains in sprints 008/018/019/020 —
      sprint 021 takes a different annulus-side route via sprint 006),
    * `branch1PointwiseFactor`, `branch2PointwiseFactor`,
      `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
      `Korenblum.scalarCriterion` (these are markers of the
      pointwise/integrated paper inequalities `(10)–(14)`),
    * `branch2SigmaKernel`, `sigmaPlus`, `sigmaMinus`,
      `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` directly,
      `paper.liftGap` (these are markers of the branch-2 disk chain
      and the `sigmaMinus`-internal route — sprint 021 stays on the
      branch-1 disk side via sprint 015 and reaches `sigmaZeroMinus`
      via that wrapper).

    (Note: `branch1SigmaKernel` and `WangOuter.paperLambda` are EXEMPT —
    they appear in sprint 015's output and sprint 006's output
    respectively, and in the kernel inequality on the LHS/RHS of the
    witness premise. `Section2Assumptions` is EXEMPT — it is the input.
    `PaperAxioms.diskExcess`, `PaperAxioms.annulusExcess`,
    `PaperAxioms.sigmaZeroMinus`, `PaperAxioms.circleGap`,
    `PaperAxioms.coeffMinusGap`, `PaperAxioms.n2Pred` are EXEMPT — they
    are the output expressions of sprints 005/006/015 and the witness's
    summability/integrability premises.)

  * The new theorem's signature MUST take *exactly* the parameters in
    the goal block above. The existential conjunction must enforce
    `c < ρ_disk` strict, `ρ_disk < PaperAxioms.branchSplit c` strict,
    `ρ_disk ≤ ρ₁` weak, `ρ₁ ≤ ρ₂` weak, `ρ₂ < 1` strict (no
    open/closed swaps). The kernel inequality must be the **literal
    LHS** `(PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) ≤
    ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'` —
    not algebraically simplified, not collapsed via `field_simp`.

* `ProofRefinement/Korenblum/Candidates/V21.lean`:

  * `-- @parent V20`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V20).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V20).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v21_decoupled_anchor_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ_disk ρ₁ ρ₂ : ℝ,
              c_value < ρ_disk ∧
              ρ_disk < PaperAxioms.branchSplit c_value ∧
              ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
                  volume c_value 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 *
                    PaperAxioms.sigmaZeroMinus a b ρ' /
                      WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 /
                    WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                Summable (fun k : ℕ =>
                  if PaperAxioms.n2Pred a b k then
                    PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                  else 0) ∧
                (PaperAxioms.branch1SigmaKernel c_value ρ_disk *
                    ρ_disk ^ 2) ≤
                  ∫ ρ' in ρ₁..ρ₂,
                    2 * ρ' ^ 3 /
                      WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor
        c_value_pos c_value_lt_one h_witness
    ```

  * Additionally, prove a structural witness lemma confirming the
    decoupled-anchor sub-regime is non-vacuous at the seed by
    exhibiting a concrete `(ρ_disk, ρ₁, ρ₂)`:

    ```lean
    theorem v21_decoupled_anchor_witness_at_seed :
        ∃ ρ_disk ρ₁ ρ₂ : ℝ,
          c_value < ρ_disk ∧
          ρ_disk < PaperAxioms.branchSplit c_value ∧
          ρ_disk ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      -- Degenerate single-point witness at the midpoint of
      -- (c_value, branchSplit c_value).
      -- Use the literal mid := (c_value + branchSplit c_value) / 2.
      refine ⟨(c_value + PaperAxioms.branchSplit c_value) / 2,
              (c_value + PaperAxioms.branchSplit c_value) / 2,
              (c_value + PaperAxioms.branchSplit c_value) / 2,
              ?_, ?_, le_rfl, le_rfl, ?_⟩
      · -- c_value < (c_value + branchSplit c_value)/2
        --   ⟺ c_value < branchSplit c_value
        have hSplit_gt_c : c_value < PaperAxioms.branchSplit c_value := by
          unfold PaperAxioms.branchSplit
          have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
          have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
            Real.sqrt_nonneg _
          have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
            Real.sq_sqrt (le_of_lt h_pos)
          have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
            nlinarith [h_sq, h_sqrt_nonneg]
          have hc_pos : (0 : ℝ) < c_value := c_value_pos
          nlinarith [h_sqrt_gt_one, hc_pos]
        linarith
      · -- (c_value + branchSplit c_value)/2 < branchSplit c_value
        --   ⟺ c_value < branchSplit c_value (same as above)
        have hSplit_gt_c : c_value < PaperAxioms.branchSplit c_value := by
          unfold PaperAxioms.branchSplit
          have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
          have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
            Real.sqrt_nonneg _
          have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
            Real.sq_sqrt (le_of_lt h_pos)
          have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
            nlinarith [h_sq, h_sqrt_nonneg]
          have hc_pos : (0 : ℝ) < c_value := c_value_pos
          nlinarith [h_sqrt_gt_one, hc_pos]
        linarith
      · -- (c_value + branchSplit c_value)/2 < 1
        --   ⟺ c_value + branchSplit c_value < 2
        --   ⟸ c_value < 1 ∧ branchSplit c_value < 1
        have hSplit_lt_one : PaperAxioms.branchSplit c_value < 1 := by
          unfold PaperAxioms.branchSplit
          have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
          have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
            Real.sqrt_nonneg _
          have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
            Real.sq_sqrt (le_of_lt h_pos)
          have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
            have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by
              norm_num
            nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
          have hc : c_value = 3554 / 10000 := rfl
          rw [hc]
          nlinarith [hsqrt_lt, hsqrt_nonneg]
        have hc_lt_one : c_value < (1 : ℝ) := c_value_lt_one
        linarith
    ```

    The degenerate single-point witness `ρ_disk = ρ₁ = ρ₂ = (c_value +
    branchSplit c_value)/2` confirms the decoupled-anchor predicate is
    non-vacuous without committing to any non-trivial numerical bound
    beyond `c_value < branchSplit c_value` (already established) and
    `branchSplit c_value < 1` (already established in V8). Each
    `nlinarith` block is verbatim sprint 017's body
    (`Reduction.lean:1963-1972`) or sprint 020's
    `v20_straddling_window_witness_at_seed` body.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify the new reducer's
    signature typechecks at the seed `c_value` and to demonstrate
    the decoupled-anchor witness is non-vacuous.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V20.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_020`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V21.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V21.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V21 scores `≥` V20 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V21.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of `diskExcess_upper_bound_via_eq5`
     (the unique sprint-015 wrapper consumption),
   * exactly one direct invocation of
     `annulusExcess_lower_bound_of_eq8_eq9` (the unique sprint-006
     wrapper consumption),
   * **at least two** invocations of
     `sigmaZeroMinus_monotone_of_summable` (one at the boundary
     `ρ_disk → ρ₁`, one inside the inner cascade per `ρ' ∈ [ρ₁,
     ρ₂]`),
   * **at least two** invocations of
     `sigmaZeroMinus_summable_of_summable_at_upper` (one at `ρ₂ →
     ρ₁`, one per `ρ'` inside the inner cascade),
   * exactly one invocation of `sigmaZeroMinus_nonneg_of_pos`,
   * **no direct reference** to `paper.eq2_`, `paper.eq3_`,
     `paper.eq4_`, `paper.eq6_`, `paper.eq10_`, `paper.eq11_`,
     `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
   * **no direct reference** to `paper.eq5_branch1_sigmaReduction`,
     `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`
     (these must be consumed only via the sprint-015 and sprint-006
     wrappers),
   * **no reference** to `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9`,
     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
   * **no reference** to any prior `valid_of_*` reducer,
   * **no reference** to `mass_mul_le_annulusSlice_of_integral_bound_ae`,
     `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
     `paperScalarIntegrand1_intervalIntegrable`,
     `paperScalarIntegrand2_intervalIntegrable`,
     `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
     `Korenblum.scalarCriterion`, `branch1PointwiseFactor`,
     `branch2PointwiseFactor`,
   * **no reference** to `branch2SigmaKernel`, `sigmaPlus`,
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
     `circleGap_inner_bound_of_eq2_eq3_eq4`,
     `diskExcess_upper_bound_of_eq2_eq3_eq4`,
     `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
     `diskExcess_upper_bound_via_eq3_eq4`,
     `diskExcess_upper_bound_via_eq6`,
     `circleGap_outer_lower_bound_of_eq8_eq9`,
     `paper.liftGap`.
6. `grep -n 'v21_decoupled_anchor_compiles\|v21_decoupled_anchor_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V21.lean`
   returns at least two distinct matches.
7. The conclusion of `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`
   is exactly `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_witness` existential body in
   `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` contains:
   * the constraint `c < ρ_disk` (verify via `grep`),
   * the constraint `ρ_disk < PaperAxioms.branchSplit c` (verify via `grep`),
   * the constraint `ρ_disk ≤ ρ₁` (verify via `grep`),
   * the constraint `ρ₁ ≤ ρ₂` (verify via `grep`),
   * the constraint `ρ₂ < 1` (verify via `grep`),
   * the literal kernel inequality
     `(PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2) ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'`
     (verify via `grep` for the substring
     `PaperAxioms.branch1SigmaKernel c ρ_disk * ρ_disk ^ 2`).
9. The body of `v21_decoupled_anchor_witness_at_seed` exhibits a
   concrete `(ρ_disk, ρ₁, ρ₂)` with `c_value < ρ_disk < branchSplit
   c_value ∧ ρ_disk ≤ ρ₁ ≤ ρ₂ < 1` (verify via `grep` of the theorem
   body for the witness expression `(c_value + PaperAxioms.branchSplit
   c_value) / 2` appearing as the witness for all three of `ρ_disk`,
   `ρ₁`, `ρ₂` in the degenerate single-point case).
10. The new theorem's `h_witness` admits **decoupled-anchor** windows:
    its conjunction allows `ρ_disk < ρ₁` strictly *and* `ρ_disk = ρ₁`
    (the weak `≤` form). Verify via `grep` that the conjunction body
    contains exactly the string `ρ_disk ≤ ρ₁` (not `ρ_disk < ρ₁`,
    not `ρ_disk = ρ₁`).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V20.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the branch-2 mirror via `eq11_of_eq6_eq8_eq9` (alternative A
  above — diminishing analytical return).
* Building the straddling derived-pointwise reducer (alternative B
  above — mostly compositional).
* Building the `(2)`-derived two-anchor `Z_c` upper bound (alternative
  D above — requires multi-anchor `Z` arithmetic not in current toolkit).
* Building Z-free version of sprint 017 (alternative H above —
  low-novelty refactor).
* Building `(2)+(3)+(4)`-chain straddling reducer (alternative I
  above — structurally similar to sprint 020).
* Discharging the kernel inequality `branch1SigmaKernel c ρ_disk ·
  ρ_disk² ≤ ∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ'` numerically at the seed
  `c_value` — this requires a `paperLambda` envelope or a numerical
  oracle, both out of scope for this sprint.
* Algebraically simplifying the disk-side kernel
  `branch1SigmaKernel c ρ_disk · ρ_disk²` to a closed form involving
  only `c, ρ_disk` (e.g. `ρ_disk⁴(c⁴ − 2c²ρ_disk² + ρ_disk⁴)/(2(ρ_disk²
  − c²)²)`). Sprint 015's output is the natural form; collapsing it
  would only obscure the kernel's `ρ_disk`-dependence and make the
  kernel inequality harder to read. **Out of scope for sprint 021;
  may be useful in a future sprint that wants to compute concrete
  numerics.**
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the kernel inequality (out of scope above) or a
  qualitatively new analytical witness.
* Any modification to sprint 015's `diskExcess_upper_bound_via_eq5`,
  sprint 006's `annulusExcess_lower_bound_of_eq8_eq9`, sprint 011's
  `sigmaZeroMinus_monotone_of_summable`, sprint 012's
  `sigmaZeroMinus_summable_of_summable_at_upper`, or sprint 005's
  `sigmaZeroMinus_nonneg_of_pos` (all consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 021 is purely
  structural.

## Time budget

≤ 45 minutes runtime. The new reducer is ~250 lines of Lean —
slightly heavier than sprint 017's ~234 lines because of the cascaded
Z-monotonicity bridge (one extra `have hZ_disk_le_ρ₁` block and one
extra `le_trans` composition step), but otherwise architecturally
identical: same scaffolding, same step sequence (a)/(b)/(c)/(d), same
final `calc` shape. All tactics used are *already verified* in sprint
015 (`Reduction.lean:1841-1869`), sprint 006 (`Reduction.lean:649-…`),
sprint 011 (`Reduction.lean:1283-1361`), sprint 012
(`Reduction.lean:1425-1496`), and sprint 017 (`Reduction.lean:1933-…`).
The candidate side lemmas are 5–25 lines each (matching V19/V20 plus
one extra `nlinarith` block per witness conjunction). Total V21 size:
≤ 130 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The cascaded Z-monotonicity bridge fails to compose cleanly (e.g.
  `le_trans hZ_disk_le_ρ₁ (hZmono_inner ρ' hρ')` does not unify) —
  fall back to inlining `sigmaZeroMinus_monotone_of_summable` twice
  per `ρ'` (once at `ρ_disk → ρ₁`, once at `ρ₁ → ρ'`) and dropping
  the `hZ_disk_le_ρ₁` named hypothesis.
* `sigmaZeroMinus_summable_of_summable_at_upper` cannot be invoked at
  `ρ₂ → ρ₁` due to a signature mismatch — verify the signature at
  `Reduction.lean:1425-…` and adjust argument order accordingly.
  Sprint 017's body invokes it at `Reduction.lean:2025-2027` with
  `(hρ'_nonneg) (hρ'_le_ρ₂) hSummable_top`; sprint 021 mirrors with
  `(hρ₁_nonneg) (hρ₁_le_ρ₂) hSummable_top`.
* Sprint 015's signature at `Reduction.lean:1841-1869` cannot
  accommodate the strict inequalities `c < ρ_disk < branchSplit c` (it
  may want them as separate hypotheses or in a different order) — fall
  back to copying the exact argument shape from sprint 015's call site
  in V15 and adjusting witness construction accordingly.
* Sprint 006's signature at `Reduction.lean:649-…` cannot accommodate
  the annulus window `[ρ₁, ρ₂]` with `c < ρ₁ ≤ ρ₂ < 1` (e.g. it may
  require `ρ₁ < ρ₂` strictly) — fall back to copying the exact
  argument shape from the existing sprint-006 consumer in sprint 014's
  body (`valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
  `Reduction.lean:1686-…`) and adjusting witness construction
  accordingly. **In particular, if sprint 006 requires `ρ₁ < ρ₂`
  strictly, the witness lemma's degenerate single-point witness
  `ρ_disk = ρ₁ = ρ₂` becomes inadmissible**; in that case fall back to
  the non-degenerate witness `ρ_disk = (c_value + branchSplit
  c_value)/2`, `ρ₁ = (c_value + branchSplit c_value)/2 + 1/100`, `ρ₂ =
  (c_value + branchSplit c_value)/2 + 2/100`. (Verify
  `(c_value + branchSplit c_value)/2 + 2/100 < 1` via the `branchSplit
  c_value < 1` lemma plus `c_value < 1` plus `2/100 < 1/100`.)
* The witness lemma's `c_value < (c_value + branchSplit c_value)/2`
  step or its mirror cannot close cleanly — fall back to copying
  sprint 017's body block at `Reduction.lean:1963-1972` verbatim
  (already verified working in V17/V18/V19/V20).
* The witness lemma's `(c_value + branchSplit c_value)/2 < 1` step
  fails — fall back to V8's verbatim witness `v8_split_lt_one_at_seed`
  body (already verified working in V8/V20).
* Any of acceptance criteria 4, 5, 7, 8, 9, 10 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5: `STATUS=BLOCKED` — that would defeat the
  "sprint 015 + sprint 006 + sprints 011/012 chain only" structural
  guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
