# Sprint 023: Branch-2 closing reducer `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window` — the workspace's **first end-to-end `ValidKorenblumBound c` proof on the branch-2 sub-regime that does *not* invoke `paper.eq6_branch2_sigmaReduction` anywhere in its transitive proof body**, the **first paper-internal cross-validation at the closing-reducer level on the branch-2 axis** (mirroring sprint 022's disk-side cross-validation), and the **first closing reducer to consume sprint 022's `(2)+(3)+(4)`-derived branch-2 disk bound**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V22.lean`
**Target file**: `Candidates/V23.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
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
            (c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The closed-form scalar kernel `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` is
**numerically identical** to sprint 017's
`valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` kernel, and the
admissible-window region is also numerically identical
(`branchSplit c ≤ ρ₁ ≤ ρ₂ < 1`; sprint 017 uses the strict form
`branchSplit c < ρ₁`, but sprint 022's input lemma admits the closed
form `branchSplit c ≤ ρ`, so the closed-form weak inequality flows
through). What changes is the **disk-side derivation chain**:

* **Sprint 017**: disk side via `diskExcess_upper_bound_via_eq6` (sprint
  016), which directly invokes `paper.eq6_branch2_sigmaReduction`.
* **Sprint 023 (this sprint)**: disk side via
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` (sprint
  022), which invokes `paper.eq2_sigmaZeroMinus_lower`,
  `paper.eq3_circleGap_decomposition`, `paper.eq4_sigmaPlus_bound`
  (via sprint 003) plus `sigmaZeroMinus_monotone_of_summable`
  (sprint 011) — **with zero invocation of `paper.eq6_branch2_sigmaReduction`**
  anywhere in the transitive call graph.

The full proof body is sprint 017's body verbatim, with **two single-
line substitutions**:

1. The disk-side input swaps `diskExcess_upper_bound_via_eq6 paper
   hSplit_lt_ρ₁ hρ₁_lt_one` (sprint 017's line 2120-2121) for
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse paper
   hc_pos hSplit_le_ρ₁ hρ₁_lt_one hIntDiskInner hSummable_ρ₁`. The
   new disk-side input *already* delivers the bound in the closed
   form `(c⁴/2) · Z_{ρ₁}` directly (sprint 022's RHS is
   `(c^4/2) * sigmaZeroMinus a b ρ₁`), so sprint 017's
   `branch2SigmaKernel`-collapse step (`hCollapse` at line 2123-2127)
   is **eliminated entirely** — sprint 023 needs no `field_simp`
   collapse on the kernel since sprint 022's bound is already in the
   merged form. Net change: −5 lines from sprint 017's structure.

2. Sprint 022's premise list adds (a) an extra integrability premise
   `IntervalIntegrable (fun r => 2 * r * circleGap a b r) volume 0 c`
   (sprint 003's premise, transitively required by sprint 022's body)
   and (b) an extra summability premise
   `Summable (fun k => if n2Pred a b k then coeffMinusGap a b k *
   ρ₁ ^ (2*k - 2) else 0)` (sprint 011's premise, transitively
   required by sprint 022's `Z_c → Z_{ρ₁}` collapse). Both are
   threaded through the existential `h_witness` premise alongside
   sprint 017's existing premises.

   Note that the summability premise here is at `ρ₁` (the disk-side
   anchor), **independently** of sprint 017's existing summability
   premise at `ρ₂` (the annulus-side anchor). The `ρ₁`-side
   summability is needed by sprint 022's body for the `Z_c → Z_{ρ₁}`
   collapse; the `ρ₂`-side summability is needed for the annulus-side
   `Z_{ρ₁} ≤ Z_{ρ'}` monotonicity (sprint 012's transfer to interior
   `ρ' ∈ [ρ₁, ρ₂]`). Both are existential premises on the new
   reducer, just as in sprint 017.

3. Geometric scaffolding: derive `hSplit_le_ρ₁ : branchSplit c ≤ ρ₁`
   directly from the existential's `branchSplit c ≤ ρ₁` (sprint 023
   uses the closed-form weak inequality, matching sprint 022's input
   shape). Derive `hcρ₁ : c < ρ₁` via
   `hcρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁`, where
   `hSplit_gt_c : c < branchSplit c` is the same `√(4/3) > 1`
   nlinarith pattern used at sprint 017's lines 2104-2114 and
   sprint 022's lines 1959-1968.

The remaining proof body (steps `hStepA`/`hStepB`/`hZmono`/`hStepC`,
the annulus-side `annulusExcess_lower_bound_of_eq8_eq9` invocation,
the final `calc` chain) is **verbatim from sprint 017's lines
2138-2237** with no modifications other than the `hSplit_lt_ρ₁ →
hSplit_le_ρ₁` weak/strict adjustment and the addition of two extra
hypotheses to the proof scope.

Then ship a `Candidates/V23.lean` at the same `c = 0.3554` that
compiles, scores `≥ V22 = 1777/5000`, and *materialises* the new
reducer in side lemmas `v23_disk_eq2_eq3_eq4_collapse_branch2_window_compiles`
and `v23_branch2_window_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15`
so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 023 ships a structurally novel closing reducer
along three axes that no prior workspace closing reducer touches:

1. **First end-to-end `ValidKorenblumBound c` proof on the branch-2
   sub-regime whose transitive proof body invokes zero
   `paper.eq6_branch2_sigmaReduction` references.** The current
   workspace has exactly two end-to-end closing reducers on the
   branch-2 sub-regime: sprint 017's
   `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` (which invokes
   `paper.eq6_branch2_sigmaReduction` via sprint 016's
   `diskExcess_upper_bound_via_eq6`, see `Reduction.lean:1894-1895`)
   and sprint 018's `valid_of_eq11_subinterval_branch2` (which uses
   `paper.eq11_branch2_pointwise` directly — but `(11)` is *itself*
   provable from `(6)+(8)+(9)` in `KorenblumPaper.PaperAxioms` via
   `eq11_of_eq6_eq8_eq9` at `PaperAxioms.lean:446`, so the `(11)`
   chain is *paper-internally* downstream of `(6)`). Sprint 023 ships
   the **first end-to-end branch-2 closer whose transitive proof
   body contains no reference to `eq6` and no reference to `eq11`**:
   it consumes `paper.eq2_sigmaZeroMinus_lower`,
   `paper.eq3_circleGap_decomposition`, `paper.eq4_sigmaPlus_bound`,
   `paper.eq8_sigmaToLiftGap`, `paper.eq9_liftGapToCircleGap`, and
   `paper.eq7_paperK_formula`, plus the workspace series-monotonicity
   lemmas (sprints 011/012). After sprint 023 lands, the workspace
   has **two structurally disjoint paper-axiom signatures** for
   end-to-end branch-2 closure: `{eq6, eq8, eq9, eq7, series}` (sprint
   017) and `{eq2, eq3, eq4, eq8, eq9, eq7, series}` (sprint 023).
   This is a paper-internal cross-validation at the closing-reducer
   level — exactly the structural extension that sprint 022's
   `Experience.md` forward roadmap (item (i)) names as the natural
   follow-up.

2. **First closing reducer to consume sprint 022's
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`.** Sprint
   022 produces a generic disk-side bound on the branch-2 sub-regime
   without committing to any particular closing chain. Sprint 023 is
   the first sprint to *materialise* sprint 022's bound in a real
   end-to-end `ValidKorenblumBound c` proof — promoting the disk-side
   cross-validation lemma to a closing-reducer-level cross-validation,
   exactly the same step-up that sprint 017 made over sprint 016
   (sprint 016 ships the disk-side `(6)`-derived bound; sprint 017
   promotes it to an end-to-end branch-2 closer). This is *not*
   "the same chain" as sprint 017 because the disk-side chain consumes
   a structurally disjoint set of paper axioms (`{eq2, eq3, eq4}` +
   series-monotonicity instead of `{eq6}`), and the disk-side proof
   body sequence is genuinely different (sprint 022's body explicitly
   invokes sprint 003's two-`Z` integrated bound, then collapses
   `Z_c → Z_{ρ₁}` via sprint 011 — neither step appears in sprint 016's
   body, which is a 4-line `calc` on top of `paper.eq6_branch2_sigmaReduction`
   + sprint 005's series identity).

3. **First closing reducer with two *independent* series-summability
   premises (one at the disk-side anchor `ρ₁`, one at the
   annulus-side anchor `ρ₂`).** Sprint 017's existential premise
   carries one `Summable …` cell at `ρ₂` (used for the annulus-side
   `Z_{ρ₁} ≤ Z_{ρ'}` monotonicity transfer to interior points
   `ρ' ∈ [ρ₁, ρ₂]` via sprint 012). Sprint 022's input adds one
   `Summable …` cell at `ρ` (used for the disk-side `Z_c ≤ Z_ρ`
   collapse via sprint 011). Sprint 023 inherits *both*: its
   `h_witness` existential body carries summability at `ρ₁` (sprint
   022's premise) **and** summability at `ρ₂` (sprint 017's premise).
   The two summability premises are at *different radii* and serve
   *different roles* in the closing chain:
   * `Summable @ ρ₁` discharges the disk-side `Z_c → Z_{ρ₁}`
     collapse inside sprint 022's body.
   * `Summable @ ρ₂` discharges the annulus-side
     `Z_{ρ₁} ≤ Z_{ρ'}, ρ' ∈ [ρ₁, ρ₂]` monotonicity inside sprint
     017's body.

   No prior workspace closing reducer carries summability premises at
   two distinct radii. This is a **measurable structural signal** that
   sprint 023's chain is genuinely different from any single prior
   chain — both halves of the disjoint `(2)+(3)+(4)` and `(8)+(9)`
   chains independently rely on series-monotonicity at distinct
   anchors, in a way that no single prior reducer needs.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V23 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` parameterised by the witness
  window `(ρ₁, ρ₂) ⊆ [branchSplit c, 1)` and the kernel inequality
  `c⁴/2 ≤ ∫ 2ρ³/Λ`, with no commitment to a concrete `(c, ρ₁, ρ₂)`
  tuple beyond the structural witness lemma.
* The kernel inequality is **not** numerically discharged at the
  seed — it remains an existential premise on the new reducer,
  identical to sprint 017's premise.

Why this is **not** "the same chain" as sprint 017:

* **Disjoint paper-axiom signature on the disk side.** Sprint 017's
  disk-side input is `diskExcess_upper_bound_via_eq6` (sprint 016),
  whose proof body invokes `paper.eq6_branch2_sigmaReduction`
  directly (`Reduction.lean:1894-1895`). Sprint 023's disk-side input
  is `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` (sprint
  022), whose proof body invokes `paper.eq2_sigmaZeroMinus_lower`,
  `paper.eq3_circleGap_decomposition`, `paper.eq4_sigmaPlus_bound`
  (via sprint 003) and `sigmaZeroMinus_monotone_of_summable` (sprint
  011) — **zero invocation of `eq6` anywhere in the transitive call
  graph**. The two reducers' disk-side paper-axiom signatures are
  **completely disjoint**: `{eq6}` vs `{eq2, eq3, eq4}`.
* **Different transitive-axiom set.** A `#print axioms` on
  `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
  vs `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` will reveal
  measurably different transitive consumption: sprint 023's reducer
  will *not* mention `Eq6Branch2SigmaReduction`-related field
  projections, while sprint 017's does. (Verifiable by post-merge
  axiom-extraction.)
* **Different premise count and shape.** Sprint 023's `h_witness`
  carries 8 conjunction cells: 3 geometric (`branchSplit c ≤ ρ₁`,
  `ρ₁ ≤ ρ₂`, `ρ₂ < 1`), 4 integrability (the existing 3 sprint-017
  cells plus the new sprint-022 disk-side `IntervalIntegrable
  (2r·circleGap) volume 0 c`), and 2 summability (one at `ρ₁` for the
  disk-side collapse, one at `ρ₂` for the annulus-side monotonicity).
  Sprint 017 has 6 cells. The two new cells (one integrability, one
  summability, both required transitively by sprint 022) are the
  **measurable structural cost** of the alternative chain.

Why this is **not** "the same chain" as sprint 022 alone:

* **End-to-end vs disk-only.** Sprint 022 ships a disk-side bound
  `diskExcess ≤ (c⁴/2) · Z_ρ`. Sprint 023 ships an end-to-end
  `ValidKorenblumBound c` proof that **composes** sprint 022's
  disk-side bound with sprint 006's annulus-side lower bound and
  sprint 017's chain-glue (`hStepA`/`hStepB`/`hZmono`/`hStepC`/
  `annulusExcess_lower_bound_of_eq8_eq9` cascade) to close the
  full Korenblum bound. The promotion from "disk-side bound" to
  "end-to-end closure" is the same step-up that sprint 017 made
  over sprint 016 — and the workspace's first such step-up on the
  branch-2 sub-regime that does not consume `eq6`.

Why this is **not** "the same chain" as sprint 018 (`valid_of_eq11_subinterval_branch2`):

* **Different disk-side input.** Sprint 018 uses
  `paper.eq11_branch2_pointwise` directly (which is paper-internally
  derivable from `(6)+(8)+(9)` via `eq11_of_eq6_eq8_eq9` at
  `PaperAxioms.lean:446`). Sprint 023 uses sprint 022's
  `(2)+(3)+(4)`-derived bound and never references `eq11` or `eq6`.
  Different paper-axiom signatures even modulo the
  `eq11_of_eq6_eq8_eq9` bridge.
* **Different annulus-side machinery.** Sprint 018 closes the
  contract by integrating `(11)` against `2ρ` to produce a windowed
  mass condition `1 ≤ ∫_{ρ₁..ρ₂} scalarIntegrand2`, then dominates
  via `mass_mul_le_annulusSlice_of_integral_bound_ae`. Sprint 023
  uses the sprint-017 cascade
  (`Z_{ρ₁} ≤ Z_{ρ'} ≤ Z`-weighted integrand → annulus excess) via
  sprint 006's `annulusExcess_lower_bound_of_eq8_eq9`. **Disjoint
  annulus-side bridges.**

Why this is **bounded enough for one Generator session**:

* The proof body is sprint 017's body
  (`Reduction.lean:2099-2237`) with **two single-line substitutions**:
  1. The disk-side `hDiskRaw` invocation swaps `diskExcess_upper_bound_via_eq6`
     for `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`.
  2. The `hCollapse` algebraic step (5 lines) is **deleted** because
     sprint 022's bound is already in the closed form `(c⁴/2) · Z_{ρ₁}`,
     not `branch2SigmaKernel c ρ₁ · ρ₁² · Z_{ρ₁}`.
* The geometric scaffolding (`hSplit_gt_c`, `hcρ₁`, `hρ₁_pos`) is
  verbatim from sprint 017's lines 2104-2117, with the only change
  being `hSplit_lt_ρ₁ : branchSplit c < ρ₁` becoming `hSplit_le_ρ₁ :
  branchSplit c ≤ ρ₁` (matching sprint 022's input shape). Compose
  via `hcρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁`.
* The remaining `hStepA`, `hStepB`, `hZmono`, `hStepC`, annulus-side
  `hAnn`, and final `calc` blocks are **literally verbatim** from
  sprint 017's lines 2138-2237.
* All Lean idioms used (`mul_le_mul_of_nonneg_right`,
  `intervalIntegral.integral_mul_const`,
  `sigmaZeroMinus_summable_of_summable_at_upper`,
  `sigmaZeroMinus_monotone_of_summable`,
  `WangPaperSideConditions.paperLambda_pos`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `annulusExcess_lower_bound_of_eq8_eq9`) are **already verified at
  the cited line ranges** in sprint 017.
* Estimate: ~145 lines for the new theorem (5 lines shorter than
  sprint 017 because `hCollapse` is eliminated, plus 5-7 lines added
  for threading the two new hypotheses), dominated by verbatim
  duplication of sprint 017's body.
* The candidate side lemmas are 5–25 lines each (matching sprints
  017, 022). Total V23 size: ≤ 90 lines.

Why this beats the alternatives I considered:

* **A: Branch-1 mirror — `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch1_window`
  using sprint 007's branch-1 `(2)+(3)+(4)` collapse.**
  Sprint 015's bulletin entry already records that sprint 015's
  `(5)`-derived branch-1 bound is **algebraically equal** to sprint
  007's `(2)+(3)+(4)`-derived bound on `(c, branchSplit c]`:
  `branch1SigmaKernel c ρ · ρ² = (c⁶/6)/(ρ²−c²)`. So sprint 021's
  `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` is *already*
  a branch-1 closer whose disk-side closed form is identical to
  sprint 007's `(2)+(3)+(4)` collapsed bound. A new branch-1 closer
  swapping sprint 015's `(5)`-input for sprint 007's `(2)+(3)+(4)`-
  input would **produce the same RHS** (by sprint 015's bulletin
  entry) and be merely a notational rewrite. **Demoted: same closed
  form, not a structurally distinct chain.** (Note: this is
  *different* from the branch-2 case, where sprint 022 vs sprint 016
  produce the *same* closed form `(c⁴/2)·Z_ρ` from *different paper
  axioms* — that cross-validation is structurally meaningful because
  `(6)` is a *separate paper hypothesis* in `Section2Assumptions`,
  whereas `(5)` is also a separate hypothesis but the workspace
  already has the equivalent decoupled-anchor closer via sprint 021's
  `(5)`-input. The branch-2 case is novel because no prior closer
  uses `(2)+(3)+(4)` on branch-2; the branch-1 case would not be.)

* **B: Cross-validation algebraic identity
  `branch1SigmaKernel c ρ · ρ² = (c⁶/6)/(ρ²−c²)` on
  `(c, branchSplit c]`** — the third item in sprint 022's forward
  roadmap. **Demoted as a one-line `field_simp; ring` identity that
  doesn't constitute a full sprint** (it would be a 5-line workspace
  helper lemma at most, and its only consumer would be a hypothetical
  alternative branch-1 mirror sprint A above, itself demoted).

* **C: A closing reducer using `paper.eq14_combined` directly
  *bypassing* `(15)`** (`valid_of_eq14_combined_with_unit_lower`).
  **Demoted**: `eq14_combined` has the form `scalarCriterion · diskExcess
  ≤ annulusExcess` (`PaperAxioms.lean:236-239`), which only delivers
  `diskExcess ≤ annulusExcess` when `1 ≤ scalarCriterion` — but the
  latter is *exactly* the `(15)` input that the seed axiom provides.
  This sprint would just relocate the seed axiom inside a new reducer,
  not produce any genuinely independent chain. The existing
  `valid_of_eq15` already carries this composition (see
  `Reduction.lean:70-87`).

* **D: Re-derive `eq14_combined` from `eq12 + eq13` directly inside
  `Reduction.lean`** as a paper-internal cross-validation lemma
  `eq14_of_eq12_eq13_with_adjacency`. **Demoted**: this is essentially
  a refactor of sprint 001's body — sprint 001 *already* combines
  `(12)+(13)` to dominate the scalar-criterion times disk excess. A
  separately named lemma would be valuable only as an
  `KorenblumPaper.*` paper-internal theorem (cf. sprint 022's
  `Experience.md` item (ii)), not as a new workspace `valid_of_*`
  reducer.

* **E: Series-level continuity / left-edge limit for `s ↦
  sigmaZeroMinus a b s`.** Demoted in sprints 016/017/018/019 as
  speculative, no concrete consumer queued. Still demoted.

* **F: A fully-quantified paper-internal lemma `eq6_of_eq2_eq3_eq4`**
  (sprint 022's `Experience.md` item (ii)). This requires editing
  `KorenblumPaper.PaperAxioms.lean`, which mandates a `Proposals/`
  entry per the workspace import policy. **Demoted to a separate
  proposal track.**

* **G: A reducer working at the `liftGap` intermediate layer.**
  Speculative — `Section2Assumptions` does not expose any closed-form
  *lower* bound on `liftGap` independent of `(8)+(9)`, so working at
  the intermediate layer offers no new closure route. **Demoted**.

* **H: A `circleGapSeries`-direct sufficient condition** (closed-form
  `diskExcess` bound expressed as a single series rather than via
  `sigmaZeroMinus`). The bulletin lists this axis as illustrative,
  but no concrete consumer is queued and it requires structural
  exploration before it can be a contract. **Demoted**.

* **I: Numerical-oracle registration discharging the kernel
  `c⁴/2 ≤ ∫ 2ρ³/Λ` at the seed.** Demoted in sprints 017/018/019 —
  needs a specific sub-window and closed-form `Λ`-bound shape,
  neither currently established. Still demoted.

Compared to A–I, candidate J (this sprint,
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`)
maximises analytical novelty per bounded Generator session: it ships
the **first end-to-end branch-2 closing reducer with zero `eq6`
invocation in its transitive proof body**, the **first closing reducer
to materialise sprint 022's disk-side cross-validation in an
end-to-end Korenblum bound proof**, and the **first reducer with two
independent series-summability premises at distinct anchors**. It uses
**only existing trusted modules + pinned Mathlib + already-verified
`Reduction.lean` lemmas** in patterns directly mirrored from sprint
017. No proposal needed.

### Note on the scaffolding overlap with sprint 017

The proof body shares the following blocks with sprint 017
**verbatim**:

* Geometric scaffolding `hSplit_gt_c`/`hcρ₁`/`hρ₁_pos`/`hρ₁_nonneg`
  (sprint 017 lines 2104-2118), with the single difference that
  sprint 023 carries `hSplit_le_ρ₁ : branchSplit c ≤ ρ₁` (closed
  form, matching sprint 022's input) instead of sprint 017's
  `hSplit_lt_ρ₁ : branchSplit c < ρ₁`. The combination
  `hcρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁` is one Lean
  expression long.
* `hStepA`/`hStepB`/`hZmono`/`hStepC` (sprint 017 lines 2138-2217).
* `hAnn` invocation of `annulusExcess_lower_bound_of_eq8_eq9`
  (sprint 017 lines 2218-2221).
* Final `calc` chain `diskExcess ≤ (c⁴/2)·Z_{ρ₁} ≤ … ≤ annulusExcess`
  (sprint 017 lines 2222-2237).

The proof body **differs** from sprint 017 only in:

* The `hDiskRaw` step (sprint 017 line 2120-2121): swap
  `diskExcess_upper_bound_via_eq6 paper hSplit_lt_ρ₁ hρ₁_lt_one` for
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse paper
  hc_pos hSplit_le_ρ₁ hρ₁_lt_one hIntDiskInner hSummable_ρ₁`.
* The `hCollapse`/`hDisk` block (sprint 017 lines 2123-2135): **delete
  entirely**. Sprint 022 already returns the bound in the form
  `(c^4/2) * sigmaZeroMinus a b ρ₁`, so no `branch2SigmaKernel`
  collapse is needed; rename `hDiskRaw` to `hDisk`.
* The existential destructuring (sprint 017 line 2101-2103): expand
  to 8 cells: `⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
  hIntDiskInner, hIntLambdaZ, hIntLambda, hSummable_ρ₁,
  hSummable_top, hKernel⟩`. (Order is geometric-then-integrability-
  then-summability-then-kernel; the precise order must match the
  conjunction order in the goal block above.)

### Note on the witness lemma at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value = c_value · √(4/3) ≈ 0.4103`.
* For an admissible window we need `branchSplit c_value ≤ ρ₁ ≤ ρ₂ <
  1`. The cleanest concrete witness is the *degenerate single-point*
  window `(ρ₁, ρ₂) = (1/2, 1/2)`, mirroring sprint 022's witness at
  `ρ = 1/2`: `branchSplit c_value ≤ 1/2` is sprint 022's
  `v22_branch2_witness_at_seed` first conjunct (verbatim), `1/2 ≤
  1/2` is `le_refl`, `1/2 < 1` is `norm_num`. The witness lemma's
  body can therefore be a 4-line copy of sprint 022's witness with
  the additional `1/2 ≤ 1/2 := le_refl` cell.

### Note on what the witness lemma should NOT do

Sprint 023's V23 witness lemma is **structural only** — it confirms
that the admissibility predicate `branchSplit c_value ≤ ρ₁ ≤ ρ₂ < 1`
is non-vacuous at the seed by exhibiting concrete `ρ₁, ρ₂`. It **does
NOT** discharge any of the integrability premises, the two summability
premises, or the kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ`. Those remain as
existential hypotheses on the new reducer, just like every prior
closing reducer's premises.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
    matching the shape above. Place it **after** sprint 017's
    `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` (around the
    end of the file, after the most recent reducer
    `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` at line 3253)
    so the chronological narrative is preserved. The proof body must:

    1. **Open `valid_of` framework.** `refine ⟨hc_pos, hc_lt_one, ?_⟩;
       intro a b K paper; obtain ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂,
       hρ₂_lt_one, hIntCircle, hIntDiskInner, hIntLambdaZ,
       hIntLambda, hSummable_ρ₁, hSummable_top, hKernel⟩ :=
       h_witness paper`.

    2. **Geometric scaffolding.** Verbatim from sprint 017 lines
       2104-2118, with the single line
       `have hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁`
       replaced by
       `have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁`.

    3. **Disk-side bound via sprint 022.**

       ```lean
       have hDisk :
           PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ :=
         diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse
           paper hc_pos hSplit_le_ρ₁ hρ₁_lt_one hIntDiskInner hSummable_ρ₁
       ```

       (No `hCollapse`/`hDiskRaw` chain needed; sprint 022 returns the
       bound in the merged form directly.)

    4. **`hStepA`, `hStepB`, `hZmono`, `hStepC` blocks.** Verbatim
       from sprint 017 lines 2138-2217.

    5. **Annulus-side `hAnn` invocation.** Verbatim from sprint 017
       lines 2218-2221.

    6. **Final calc chain.** Verbatim from sprint 017 lines 2222-2237.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 023's
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
    is the workspace's **first end-to-end `ValidKorenblumBound c`
    proof on the branch-2 sub-regime that does *not* invoke
    `paper.eq6_branch2_sigmaReduction` anywhere in its transitive
    proof body**, the **first paper-internal cross-validation at the
    closing-reducer level on the branch-2 axis** (mirroring sprint
    022's disk-side cross-validation), and the **first closing
    reducer to consume sprint 022's `(2)+(3)+(4)`-derived branch-2
    disk bound**.

  * The body of the new theorem MAY invoke:

    * `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
      (sprint 022's lemma — the unique disk-side input),
    * `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006's annulus
      lower bound),
    * `sigmaZeroMinus_monotone_of_summable` (sprint 011, transitively
      via sprint 022's body and the annulus-side `hZmono` block),
    * `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012,
      annulus-side summability transfer),
    * `sigmaZeroMinus_nonneg_of_pos` (transitively via sprint 022 +
      annulus-side; not needed directly in the new body since sprint
      017's `hZ_ρ₁_nonneg` step uses it),
    * `WangPaperSideConditions.paperLambda_pos`,
    * `intervalIntegral.integral_mul_const`,
    * `intervalIntegral.integral_mono_on_of_le_Ioo`,
    * `mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left`,
      `div_nonneg`, `add_le_add`,
    * `Real.sqrt_nonneg`, `Real.sq_sqrt`, `nlinarith`, `field_simp`,
      `ring`, `linarith`, `positivity`, `calc`, `change`, `unfold`,
      `rw`, `simpa`,
    * Definitional unfolding of `PaperAxioms.branchSplit`,
      `PaperAxioms.diskExcess`, `PaperAxioms.annulusExcess`,
      `Section2Assumptions`, `WangOuter.paperLambda`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that the new reducer
    reaches closure through the `(2)+(3)+(4) + (8)+(9) + series` chain
    only, with **zero `eq6` and zero `eq11` consumption anywhere in
    the transitive proof body**):

    * `paper.eq5_branch1_sigmaReduction` (no branch-1 paper input),
    * `paper.eq6_branch2_sigmaReduction` (the structural marker —
      the entire purpose of this sprint is to close the contract on
      branch-2 *without* this hypothesis),
    * `paper.eq10_branch1_pointwise` (no branch-1 paper input),
    * `paper.eq11_branch2_pointwise` (sprint 018's chain — disjoint),
    * `paper.eq12_branch1_integrated`, `paper.eq13_branch2_integrated`,
      `paper.eq14_combined`, `paper.eq15_…` (no integrated-branch
      input, and no `(14)`/`(15)` route),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, `eq10_of_eq5_eq8_eq9`,
      `eq11_of_eq6_eq8_eq9` (no derived paper-internal
      cross-validations — sprint 023 must compose the existing
      sprint 022 disk-side bound and sprint 006 annulus-side bound
      directly),
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
      `valid_of_eq10_eq11_straddling_window`,
      `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` (no
      upstream closing reducer — sprint 023 must close on its own
      by composing the `(2)+(3)+(4)` disk bound with the `(8)+(9)`
      annulus bound),
    * `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq5`,
      `diskExcess_upper_bound_via_eq6`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
      (no other disk-side inputs — sprint 022's lemma is the unique
      disk-side input),
    * `branch1SigmaKernel`, `branch1PointwiseFactor`,
      `branch2SigmaKernel`, `branch2PointwiseFactor`,
      `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2` (these are markers of the `(5)`,
      `(6)`, `(10)`, `(11)`, `(12)`, `(13)`, `(15)` chains — all
      forbidden along this chain),
    * `mass_mul_le_annulusSlice_of_integral_bound_ae`,
      `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`
      (these are markers of the windowed-mass closing chains — sprint
      023's annulus side uses sprint 006's
      `annulusExcess_lower_bound_of_eq8_eq9` exclusively).

    (Note: `paper.eq2_sigmaZeroMinus_lower`,
    `paper.eq3_circleGap_decomposition`,
    `paper.eq4_sigmaPlus_bound`, `paper.eq8_sigmaToLiftGap`,
    `paper.eq9_liftGapToCircleGap`, `paper.eq7_paperK_formula`,
    `paper.circleGap`, and `Section2Assumptions` are EXEMPT and ARE
    transitively consumed via the disk-side and annulus-side input
    lemmas. `WangOuter.paperLambda` and
    `WangPaperSideConditions.paperLambda_pos` are EXEMPT — they are
    named ingredients of the kernel inequality and the
    `Λ`-positivity lemma. `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    `circleGap_outer_lower_bound_of_eq8_eq9`, and
    `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` are
    EXEMPT — they are transitively consumed via sprint 022's body
    and sprint 006's body, and the **direct** invocations from sprint
    023's body are the two named lemmas
    `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` and
    `annulusExcess_lower_bound_of_eq8_eq9`.)

  * The new theorem's signature MUST take *exactly* the parameters in
    the goal block above. The 8 existential conjunction cells must
    appear in the order listed in the goal block: 3 geometric (in
    order `branchSplit c ≤ ρ₁`, `ρ₁ ≤ ρ₂`, `ρ₂ < 1`), 4
    integrability (`(2ρ·circleGap) volume c 1`,
    `(2r·circleGap) volume 0 c`, `(2ρ³·Z/Λ) volume ρ₁ ρ₂`,
    `(2ρ³/Λ) volume ρ₁ ρ₂`), 2 summability (one at `ρ₁` for the
    disk-side `Z_c → Z_{ρ₁}` collapse, one at `ρ₂` for the annulus-
    side monotonicity transfer), and 1 kernel inequality
    (`c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ`). The disk-side `branchSplit c ≤ ρ₁`
    must appear with the *closed-form weak inequality* (matching
    sprint 022's input shape), not the strict form
    `branchSplit c < ρ₁` (which sprint 017 uses).

* `ProofRefinement/Korenblum/Candidates/V23.lean`:

  * `-- @parent V22`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V22).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V22).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v23_disk_eq2_eq3_eq4_collapse_branch2_window_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              PaperAxioms.branchSplit c_value ≤ ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
                  volume c_value 1 ∧
                IntervalIntegrable
                  (fun r => 2 * r * PaperAxioms.circleGap a b r)
                  volume 0 c_value ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                Summable (fun k : ℕ =>
                  if PaperAxioms.n2Pred a b k then
                    PaperAxioms.coeffMinusGap a b k * ρ₁ ^ (2 * k - 2)
                  else 0) ∧
                Summable (fun k : ℕ =>
                  if PaperAxioms.n2Pred a b k then
                    PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                  else 0) ∧
                (c_value ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                                2 * ρ' ^ 3
                                  / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
        c_value_pos c_value_lt_one h_witness
    ```

  * Additionally, prove a structural witness lemma confirming the
    branch-2 admissibility predicate is non-vacuous at the seed by
    exhibiting concrete `(ρ₁, ρ₂) = (1/2, 1/2)` (degenerate
    single-point window, mirroring sprint 022's witness shape):

    ```lean
    theorem v23_branch2_window_witness_at_seed :
        PaperAxioms.branchSplit c_value ≤ (1 : ℝ) / 2 ∧
          (1 : ℝ) / 2 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
      refine ⟨?_, le_rfl, by norm_num⟩
      -- branchSplit c_value ≤ 1/2: verbatim from sprint 022's
      -- v22_branch2_witness_at_seed first conjunct.
      unfold PaperAxioms.branchSplit
      have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
      have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) := Real.sqrt_nonneg _
      have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
        Real.sq_sqrt (le_of_lt h_pos)
      have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
        have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by norm_num
        nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
      have hc : c_value = 3554 / 10000 := rfl
      rw [hc]
      nlinarith [hsqrt_lt, hsqrt_nonneg]
    ```

    The degenerate single-point window `ρ₁ = ρ₂ = 1/2` confirms the
    admissibility predicate is non-vacuous without committing to
    nontrivial numerical bounds beyond sprint 022's already-verified
    `branchSplit c_value ≤ 1/2`.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify the new reducer's signature
    typechecks at the seed `c_value` and to demonstrate the
    branch-2 window is non-vacuous.

* `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_023 queued: ...` line.

* `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting the closing-reducer-level paper-internal
  cross-validation, the disjoint paper-axiom signatures `{eq6,eq8,eq9}`
  vs `{eq2,eq3,eq4,eq8,eq9}` for end-to-end branch-2 closure, and the
  follow-up roadmap (e.g., the natural next step would be a Z-free
  variant of sprint 023 mirroring the relationship between sprint 014
  and sprint 017's Z-using counterpart).

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V22.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_022`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V23.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V23.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V23 scores `≥` V22 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V23.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of
     `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
   * exactly one direct invocation of
     `annulusExcess_lower_bound_of_eq8_eq9`,
   * exactly one direct invocation of
     `sigmaZeroMinus_summable_of_summable_at_upper`,
   * exactly one direct invocation of
     `sigmaZeroMinus_monotone_of_summable` (for the annulus-side
     `Z_{ρ₁} ≤ Z_{ρ'}` step; sprint 022's body uses it for the
     disk-side `Z_c ≤ Z_{ρ₁}` step and that invocation is transitive,
     not direct from sprint 023's body),
   * **no direct reference** to `paper.eq6_branch2_sigmaReduction`,
     `paper.eq11_branch2_pointwise`, `paper.eq5_branch1_sigmaReduction`,
     `paper.eq10_branch1_pointwise`, `paper.eq12_branch1_integrated`,
     `paper.eq13_branch2_integrated`, `paper.eq14_combined`, or
     `paper.eq15_…`,
   * **no reference** to any of the prior `valid_of_*` reducers,
   * **no reference** to `diskExcess_upper_bound_via_eq6`,
     `diskExcess_upper_bound_via_eq5`,
     `diskExcess_upper_bound_via_eq3_eq4`,
     `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
   * **no reference** to `mass_mul_le_annulusSlice_of_integral_bound_ae`,
     `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
     `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
     `Korenblum.scalarIntegrand2`, `branch1SigmaKernel`,
     `branch1PointwiseFactor`, `branch2SigmaKernel`,
     `branch2PointwiseFactor`,
   * **no reference** to `eq11_of_eq6_eq8_eq9`,
     `eq10_of_eq5_eq8_eq9`,
     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`.
6. `grep -n 'v23_disk_eq2_eq3_eq4_collapse_branch2_window_compiles\|v23_branch2_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V23.lean`
   returns at least two distinct matches.
7. The conclusion of
   `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
   is exactly `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_witness` existential body in the new theorem contains:
   * the constraint `PaperAxioms.branchSplit c ≤ ρ₁` (closed-form weak
     inequality — verify via `grep`),
   * the constraint `ρ₁ ≤ ρ₂` (verify via `grep`),
   * the constraint `ρ₂ < 1` (verify via `grep`),
   * **two distinct `Summable` cells** — one with `ρ₁ ^ (2 * k - 2)`
     and one with `ρ₂ ^ (2 * k - 2)` (verify via `grep` for both
     `ρ₁ ^ (2 * k - 2)` and `ρ₂ ^ (2 * k - 2)` substrings within the
     existential body),
   * the kernel inequality
     `(c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'`
     (verify via `grep`).
9. The body of `v23_branch2_window_witness_at_seed` exhibits the
   concrete witness `(ρ₁, ρ₂) = (1/2, 1/2)` and discharges the three
   conjuncts `branchSplit c_value ≤ 1/2`, `1/2 ≤ 1/2`, `1/2 < 1`.
10. **Transitive axiom signature check**: the new reducer's body
    contains no direct invocation of `paper.eq6_branch2_sigmaReduction`
    (verify via `grep -n 'paper.eq6_' Proof/Reduction.lean` — the
    only matches should be inside `diskExcess_upper_bound_via_eq6`'s
    body, sprint 016's body, and sprint 017's transitive consumption
    via sprint 016, NOT inside the new sprint 023 reducer's body).
11. The new reducer is the workspace's first end-to-end
    `ValidKorenblumBound c` proof on the branch-2 sub-regime
    `[branchSplit c, 1)` whose direct body invokes neither
    `paper.eq6_branch2_sigmaReduction` (sprint 017's chain) nor
    `paper.eq11_branch2_pointwise` (sprint 018's chain). Verifiable
    by `grep` over the new theorem's body.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V22.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the branch-1 mirror `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch1_window`
  (alternative A above — demoted because the closed form is identical
  to sprint 015's `(5)`-derived form already used by sprint 021).
* Building the cross-validation algebraic identity
  `branch1SigmaKernel c ρ · ρ² = (c⁶/6)/(ρ²−c²)` (alternative B above
  — too narrow for a full sprint).
* Building the `eq14`-direct closing reducer (alternative C above —
  just relocates the seed axiom).
* Building the paper-internal lemma `eq14_of_eq12_eq13` (alternative D
  above — refactor of sprint 001).
* Adding a fully-quantified `eq6_of_eq2_eq3_eq4` paper-internal lemma
  (sprint 022's `Experience.md` item (ii) — requires
  `KorenblumPaper.*` proposal, separate track).
* Working at the `liftGap` intermediate layer (alternative G — no
  closed-form lower bound available).
* Building a `circleGapSeries`-direct sufficient condition
  (alternative H — needs structural exploration first).
* Discharging the kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ` numerically at
  the seed `c_value` (alternative I — requires `paperLambda` envelope
  or numerical oracle, both out of scope for this sprint).
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the kernel inequality (out of scope above) or a
  qualitatively new analytical witness that closes the kernel from
  paper hypotheses alone.
* Any modification to sprint 022's
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`, sprint
  017's `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`, or any of
  the sprint 005/006/011/012 series-level lemmas (these are consumed
  verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 023 is purely
  structural.

## Time budget

≤ 45 minutes runtime. The new reducer is ~145 lines of Lean —
slightly shorter than sprint 017 (~140 lines, lines 2075-2237) because
the `hCollapse`/`hDisk` substep is eliminated, with ~5 extra lines
threading the two new hypotheses (one integrability, one summability
at `ρ₁`) through the existential destructuring. All tactics used are
*already verified* in sprint 017 (`Reduction.lean:2099-2237`) and
sprint 022 (`Reduction.lean:1942-…`). The candidate side lemmas are
5–25 lines each (including the witness at the seed). Total V23 size:
≤ 90 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* Sprint 022's lemma signature does not accept the closed-form weak
  inequality `branchSplit c ≤ ρ₁` cleanly (e.g. requires strict
  ordering or a different premise shape) — fall back to sprint 022's
  exact signature at `Reduction.lean:1942-1958` and adjust the
  `h_witness` existential cell accordingly. Sprint 022's signature is
  `(hρ_split : PaperAxioms.branchSplit c ≤ ρ)` so this should
  compose directly.
* The annulus-side `annulusExcess_lower_bound_of_eq8_eq9` invocation
  expects `c < ρ₁` (strict) but sprint 023 only carries
  `branchSplit c ≤ ρ₁`. Fall back: derive `hcρ₁ : c < ρ₁` from
  `hSplit_le_ρ₁` and `hSplit_gt_c` via `lt_of_lt_of_le` (one line),
  then pass `hcρ₁` to sprint 006's invocation as in sprint 017
  line 2220.
* The `hZmono` block from sprint 017 (lines 2158-2171) fails to
  type-check on the new scope due to the second summability premise
  being at `ρ₂` instead of `ρ₁` — sprint 017's body already discharges
  this correctly via `sigmaZeroMinus_summable_of_summable_at_upper`
  with the `ρ' ≤ ρ₂` hypothesis, so a verbatim copy should work. If
  not, fall back to inlining the `summable_at_upper` derivation
  explicitly.
* The witness lemma `v23_branch2_window_witness_at_seed`'s
  `branchSplit c_value ≤ 1/2` step fails — fall back to copying
  sprint 022's `v22_branch2_witness_at_seed` body verbatim and
  threading `le_rfl` for the `1/2 ≤ 1/2` cell.
* Any of acceptance criteria 4, 5, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially `paper.eq6_branch2_sigmaReduction`,
  `paper.eq11_branch2_pointwise`, or any prior closing reducer):
  `STATUS=BLOCKED` — that would defeat the **first end-to-end
  branch-2 closer with zero `eq6` and zero `eq11` consumption**
  structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
