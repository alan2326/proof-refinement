# Sprint 024: Branch-2 closing reducer `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable` — the workspace's **first end-to-end branch-2 `ValidKorenblumBound c` proof with zero `eq6` consumption AND only one series-summability premise**, collapsing sprint 023's two-anchor summability shape (`Z @ ρ₁` and `Z @ ρ₂`) into a single point summability premise at `ρ₂` via sprint 012's transfer

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V23.lean`
**Target file**: `Candidates/V24.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable
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

This is **strictly weaker on the `Summable …` axis** than sprint 023's
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`:
sprint 023 demands two summability cells (`@ ρ₁` and `@ ρ₂`); sprint 024
demands only one (`@ ρ₂`). The seven other premises and the kernel
inequality `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ` are bit-identical to
sprint 023.

The proof body is a **5–10 line wrapper** around sprint 023:

1. Destructure the new (1-summability-cell) `h_witness`.

2. Discharge `hSummable_ρ₁` in-house via sprint 012's
   `sigmaZeroMinus_summable_of_summable_at_upper` applied at `s = ρ₁`,
   `t = ρ₂`, using `0 ≤ ρ₁` (from `c < ρ₁`) and `ρ₁ ≤ ρ₂` (from the
   destructured premise) and `hSummable_top`.

3. Apply
   `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
   (sprint 023) to `hc_pos`, `hc_lt_one`, and a fresh `h_witness'`
   bundling the destructured premises plus the in-house `hSummable_ρ₁`.

The geometric scaffolding step `hSplit_gt_c` (used to derive `c < ρ₁`
from `branchSplit c ≤ ρ₁`) is needed to obtain `0 ≤ ρ₁` for the
`sigmaZeroMinus_summable_of_summable_at_upper` call. Verbatim from
sprint 023's lines 3484-3494 (`Reduction.lean`).

Then ship a `Candidates/V24.lean` at the same `c = 0.3554` that
compiles, scores `≥ V23 = 1777/5000`, and *materialises* the new
reducer in side lemmas
`v24_branch2_uniformSummable_compiles` and
`v24_branch2_uniformSummable_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15`
so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 024 ships a structurally novel closing
reducer along three orthogonal axes that no prior workspace closing
reducer occupies simultaneously:

1. **First end-to-end branch-2 closing reducer with both `zero eq6
   consumption` AND `one summability premise`.** Sprint 017's
   `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` has one
   summability premise (at `ρ₂`) but consumes `paper.eq6_branch2_sigmaReduction`.
   Sprint 023's `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
   has zero `eq6` consumption but two summability premises (at `ρ₁`
   and `ρ₂`). Sprint 024 is the **first reducer that combines both
   structural improvements**: zero `eq6` consumption (transitive proof
   body uses `(2)+(3)+(4)+(8)+(9)+series` instead of `(6)+(8)+(9)+series`)
   *and* a single summability premise at the right edge `ρ₂` only.
   The premise count drops from sprint 023's 8 cells to sprint 024's
   7 cells.

2. **First materialisation of `sigmaZeroMinus_summable_of_summable_at_upper`
   (sprint 012) in a non-self-bridging role.** Sprint 012's lemma is
   currently consumed in three places in `Reduction.lean`:
   * line 1542, inside
     `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`'s
     body, *to build the universal-Icc summability witness for sprint
     011's reducer* (interior-bridging role: bridges `Summable @ ρ₂`
     to `Summable @ ρ'` for every `ρ' ∈ Icc ρ₁ ρ₂`).
   * line 1757, inside
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`'s body, in the
     same interior-bridging role.
   * lines 2168 and 3537, inside sprint 017 and sprint 023 respectively,
     also in the interior-bridging role.

   Sprint 024 is the **first reducer to consume sprint 012 in a
   *single-anchor disk-side bridging role*** (bridges `Summable @ ρ₂`
   to `Summable @ ρ₁` specifically, where `ρ₁` is a *fixed left-edge
   anchor* for the disk-side input — sprint 022 — rather than an
   interior point of an integration loop). This is structurally
   distinct because the `s, t` arguments to sprint 012 are
   `s = ρ₁, t = ρ₂` (rather than `s = ρ', t = ρ₂` for varying `ρ'`),
   discharging summability for a single fixed point rather than for an
   `Icc`-quantified family. **Materialises sprint 012 in a structurally
   new role.**

3. **First branch-2 closing reducer that mirrors sprint 014's
   single-summability shape but on the branch-2 sub-regime.** Sprint
   014's `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` is the
   workspace's existing single-summability closer on the **full
   window** `[ρ₁, ρ₂] ⊂ (c, 1)`, anchored at the disk-side at `c`
   itself via sprint 013's `(3)+(4)`-derived bound `c⁴ · Z_c`. Sprint
   024 is the natural branch-2 analogue: single-summability closer on
   the **branch-2 sub-window** `[ρ₁, ρ₂] ⊂ [branchSplit c, 1)`,
   anchored at the disk-side at `ρ₁` via sprint 022's
   `(2)+(3)+(4)+series-mono`-derived bound `(c⁴/2) · Z_{ρ₁}`. The
   kernel inequality is `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ` — strictly half
   sprint 014's `c⁴ ≤ ∫` LHS budget. Same window shape, same paper-
   axiom signature on the annulus side, **half the disk-side LHS
   budget** thanks to the branch-split confinement. After sprint 024
   lands, the workspace has:

   * sprint 014: single-summability, full-window, kernel `c⁴ ≤ ∫`,
     paper-axiom signature `{eq3, eq4, eq8, eq9}`.
   * sprint 024: single-summability, branch-2 sub-window, kernel
     `c⁴/2 ≤ ∫`, paper-axiom signature `{eq2, eq3, eq4, eq8, eq9}`.

   The two reducers are **structurally complementary**: sprint 014
   trades window admissibility for kernel budget (full window, looser
   kernel); sprint 024 trades kernel budget for window admissibility
   (branch-2 sub-window, tighter kernel). **Single-summability shape
   is the structural feature that unifies them**, and sprint 024 is the
   first to deliver it on branch-2.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V24 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` parameterised by the witness
  window `(ρ₁, ρ₂) ⊆ [branchSplit c, 1)`, the same kernel inequality
  as sprint 023, and **strictly fewer summability premises** than any
  prior branch-2 closing reducer that uses `(2)+(3)+(4)`.
* The kernel inequality is **not** numerically discharged at the
  seed — it remains an existential premise on the new reducer,
  identical to sprint 023's premise.

Why this is **not** "the same chain" as sprint 023:

* **Strictly weaker premise set on the summability axis.** Sprint
  023's `h_witness` carries 8 conjunction cells, including 2
  summability cells (at `ρ₁` and `ρ₂`). Sprint 024's `h_witness`
  carries 7 conjunction cells, including only 1 summability cell
  (at `ρ₂`). Any caller that previously instantiated sprint 023 must
  produce two `Summable …` proofs; the same caller can now invoke
  sprint 024 with a single `Summable …` proof, since sprint 012
  derives the second one in-house. **Strictly fewer obligations on
  the caller.** Verifiable by counting the existential `∧` cells in
  the two reducer signatures.

* **Different transitive call graph at the closing-reducer entry.**
  Sprint 023's body invokes sprint 012 (`sigmaZeroMinus_summable_of_summable_at_upper`)
  exactly once, *inside the `hZmono` Icc-loop body* (line 3537), in
  the interior-bridging role. Sprint 024's body additionally invokes
  sprint 012 *outside the `hZmono` Icc-loop*, *as a top-level pre-
  step before calling sprint 023*, in the single-anchor disk-side
  bridging role. The new top-level invocation is a **measurable
  structural marker** that sprint 024's chain is genuinely different
  from a verbatim sprint 023 call.

* **Different role for sprint 022.** Sprint 023 invokes sprint 022's
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` directly
  with the caller-supplied `hSummable_ρ₁`. Sprint 024 invokes sprint
  022 indirectly via sprint 023, and the `hSummable_ρ₁` argument is
  *derived in-house*, not caller-supplied. The disk-side input chain
  is `caller's hSummable_top → sprint 012 → in-house hSummable_ρ₁ →
  sprint 022 → (c⁴/2) · Z_{ρ₁}` instead of sprint 023's
  `caller's hSummable_ρ₁ → sprint 022 → (c⁴/2) · Z_{ρ₁}`. **One
  more link in the disk-side chain, derived from one fewer caller
  obligation.**

Why this is **not** "the same chain" as sprint 014:

* **Different paper-axiom signature on the disk side.** Sprint 014's
  disk-side input is sprint 013's `diskExcess_upper_bound_via_eq3_eq4`,
  which uses `paper.eq3_circleGap_decomposition` and
  `paper.eq4_sigmaPlus_bound` plus `sigmaZeroMinus_nonneg_of_pos`
  to drop the `Z_r` term. Sprint 024's disk-side input is sprint 022's
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`, which
  uses `paper.eq2_sigmaZeroMinus_lower`,
  `paper.eq3_circleGap_decomposition`, `paper.eq4_sigmaPlus_bound`
  plus `sigmaZeroMinus_monotone_of_summable` to *bound* `Z_c ≤ Z_ρ₁`
  rather than dropping it. **Disjoint disk-side derivation** — sprint
  013 uses `(3)+(4)` only and drops `Z_r`; sprint 022 uses
  `(2)+(3)+(4)+series-mono` and merges `Z_c` into `Z_ρ₁`.
* **Different admissible window region.** Sprint 014: `c < ρ₁`,
  full window. Sprint 024: `branchSplit c ≤ ρ₁`, branch-2 sub-window.
* **Different LHS budget.** Sprint 014: `c⁴`. Sprint 024: `c⁴/2`.

Why this is **not** "the same chain" as sprint 017:

* Sprint 017 carries `paper.eq6_branch2_sigmaReduction` consumption
  in its transitive proof body (via sprint 016's
  `diskExcess_upper_bound_via_eq6`). Sprint 024's transitive proof
  body, via sprint 023, does not — it composes sprint 022's
  `(2)+(3)+(4)+series-mono` chain with sprint 006's `(8)+(9)`
  annulus chain. **Disjoint paper-axiom signatures**: `{eq6, eq8, eq9}`
  vs `{eq2, eq3, eq4, eq8, eq9}`.

Why this is **bounded enough for one Generator session**:

* The proof body is a **5–10 line wrapper** around sprint 023.
* Geometric scaffolding `hSplit_gt_c`/`hcρ₁`/`hρ₁_pos`/`hρ₁_nonneg`
  is verbatim from sprint 023 lines 3484-3497, with no modification.
* The single new step is the in-house `hSummable_ρ₁` derivation:
  ```lean
  have hSummable_ρ₁ :=
    sigmaZeroMinus_summable_of_summable_at_upper
      hρ₁_nonneg hρ₁₂ hSummable_top
  ```
  which is a single-line invocation matching sprint 023's interior
  invocation at line 3537 (with `ρ' := ρ₁`, `hρ'_nonneg := hρ₁_nonneg`,
  `hρ'_le_ρ₂ := hρ₁₂`).
* The remaining proof body is a `refine
  valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
  hc_pos hc_lt_one ?_; intro a b K paper'; ...` — but actually a
  cleaner pattern is to define a `h_witness'` by re-packing the
  destructured cells with the in-house `hSummable_ρ₁` and feed it to
  the existing reducer directly. The wrapper pattern is exactly
  sprint 012's
  `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
  (`Reduction.lean:1497-1546`) which sprint 024's body should mirror
  verbatim modulo theorem names.
* Estimate: ~50 lines for the new theorem (5 lines geometric
  scaffolding + 5 lines in-house summability + 10 lines existential
  re-packing + 30 lines for the signature itself). Sprint 023's
  signature is ~30 lines, sprint 024's is one summability cell shorter
  (~25 lines).
* The candidate side lemmas are 5–25 lines each (matching sprints
  023, 022). Total V24 size: ≤ 80 lines.
* All Lean idioms used (`sigmaZeroMinus_summable_of_summable_at_upper`,
  `lt_of_lt_of_le`, `lt_trans`, `Real.sqrt_nonneg`, `Real.sq_sqrt`,
  `nlinarith`,
  `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`)
  are **already verified at the cited line ranges** in sprints 012,
  022, 023.

Why this beats the alternatives I considered:

* **A: Branch-1 mirror — `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch1_window`
  using sprint 007's `(2)+(3)+(4)`-derived collapse on the branch-1
  sub-regime `(c, branchSplit c]`.** Sprint 023 explicitly demoted
  this candidate, arguing that sprint 015's `(5)`-derived branch-1
  bound is *algebraically equal* to sprint 007's `(2)+(3)+(4)`-derived
  bound on `(c, branchSplit c]` (sprint 015 bulletin entry), and
  sprint 021's `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`
  is already a branch-1 closer using sprint 015's bound. A new
  branch-1 closer using sprint 007 would produce the same RHS as
  sprint 021. **Demoted: parent planner already rejected; nothing
  has changed structurally.**

* **B: Anchor disk side at `c` itself on branch-2 via sprint 011's
  `Z_c ≤ Z_ρ` collapse, eliminating the `[branchSplit c, 1)` window
  constraint on the disk side.** Sprint 023's Experience.md forward
  roadmap explicitly names this as the natural follow-up. However,
  sprint 022's signature requires `branchSplit c ≤ ρ`, so the
  disk-side bound `(c⁴/2) · Z_ρ` is not directly available at `ρ = c`.
  To anchor at `c`, one would need a *new* disk-side bound — perhaps
  fusing sprint 022's body with sprint 011's `Z_c ≤ Z_{branchSplit c}`
  to push the anchor leftward to `c`, but that requires a separate
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse_to_Z_c`
  lemma. Combined with the closing reducer, this is two lemmas in
  one sprint — exceeds the bounded-Generator-session budget. **Demoted
  for now; queueable as a separate sprint after 024.**

* **C: Cross-validation lemma `branch1SigmaKernel c ρ · ρ² =
  (c⁶/6)/(ρ²−c²)` on `(c, branchSplit c]`** — sprint 023 alternative B,
  demoted as a one-line `field_simp; ring` identity. Still demoted.

* **D: A `circleGapSeries`-direct sufficient condition** (closed-form
  `diskExcess` bound expressed as a single series rather than via
  `sigmaZeroMinus`). Bulletin axis but speculative. **Demoted**.

* **E: A reducer working at the `liftGap` intermediate layer.**
  `Section2Assumptions` does not expose any closed-form lower bound on
  `liftGap` independent of `(8)+(9)`, so working at the intermediate
  layer offers no new closure route. **Demoted**.

* **F: Series-level *upper* bound on `sigmaZeroMinus` — a workspace
  lemma `sigmaZeroMinus_le_of_summable_above` analogous to sprint 011
  but in the reverse direction, useful for substituting `Z_ρ` *down*
  to a smaller anchor.** This would require a *different* underlying
  series identity (the negative direction of the `pow_le_pow_left₀`
  argument doesn't preserve summability), and Mathlib does not directly
  give a Cauchy-test-style upper-bound lemma without additional
  hypotheses. Speculative; needs structural exploration first. **Demoted**.

* **G: Numerical-oracle registration discharging the kernel
  `c⁴/2 ≤ ∫ 2ρ³/Λ` at the seed.** Demoted in sprints 017/018/019/023 —
  needs a specific sub-window and closed-form `Λ`-bound shape, neither
  currently established. Still demoted.

* **H: Refactor sprint 012 to a more general lemma
  `sigmaZeroMinus_summable_pointwise_of_summable_at_upper_bound`** that
  takes a general upper bound `t` (not just a fixed `ρ₂`). Unnecessary
  generalisation: sprint 012's existing signature already takes
  arbitrary `s ≤ t`. **Demoted as a no-op refactor.**

* **I: Numerical exploration in `Scratch/` of which `(ρ₁, ρ₂)` pair
  on branch-2 minimises the kernel `c⁴/2 ≤ ∫ 2ρ³/Λ` LHS-RHS gap at the
  seed `c = 0.3554`.** This is the right next step to push `c_value`
  upward, but it requires a closed-form `paperLambda` envelope, which
  is not yet exposed in the workspace. **Demoted**: needs a separate
  proposal track for `paperLambda` envelope structure first.

Compared to A–I, candidate J (this sprint,
`valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`)
maximises analytical novelty per bounded Generator session: it ships
the **first end-to-end branch-2 closing reducer with both zero `eq6`
consumption AND only one summability premise**, the **first
materialisation of sprint 012 in a single-anchor disk-side bridging
role**, and the **first single-summability branch-2 closer mirroring
sprint 014's full-window single-summability shape**. It uses **only
existing trusted modules + pinned Mathlib + already-verified
`Reduction.lean` lemmas** in patterns directly mirrored from sprints
012, 022, 023. No proposal needed.

### Note on the structural relationship to sprint 011/012

Sprint 011 (`sigmaZeroMinus_monotone_of_summable`) and sprint 012
(`sigmaZeroMinus_summable_of_summable_at_upper`) form a **two-lemma
unit**: sprint 011 gives `Z_s ≤ Z_t` from summability at `t`; sprint
012 lifts summability at `t` to summability at `s ≤ t`. Together,
they collapse two-anchor `Summable @ s, Summable @ t` premises to
one-anchor `Summable @ t` premises.

The workspace currently exhibits this two-lemma unit in three closing
reducers:

* sprint 011's `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`
  (uses sprint 011 directly, with universal Icc summability premise).
* sprint 012's `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
  (sprint 011 → uniformSummable wrapper via sprint 012).
* sprint 014's `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`
  (full-window single-summability closer, uses sprint 011 + sprint 012
  in-house).

Sprint 023 has the **two-anchor shape** (one summability premise per
anchor); sprint 024 is the **uniformSummable wrapper** that collapses
to single-anchor — completing the analogous progression on the branch-2
axis. **Sprint 024 is the missing piece in the sprint 011/012 → uniform
summability deployment matrix on the `(2)+(3)+(4)+series-mono` chain.**

### Note on the witness lemma at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value = c_value · √(4/3) ≈ 0.4103`.
* For an admissible window we need `branchSplit c_value ≤ ρ₁ ≤ ρ₂ <
  1`. The cleanest concrete witness is the *degenerate single-point*
  window `(ρ₁, ρ₂) = (1/2, 1/2)`, mirroring sprint 023's witness at
  `(1/2, 1/2)`. The witness lemma's body can therefore be a 4-line
  copy of sprint 023's `v23_branch2_window_witness_at_seed`.

### Note on what the witness lemma should NOT do

Sprint 024's V24 witness lemma is **structural only** — it confirms
that the admissibility predicate `branchSplit c_value ≤ ρ₁ ≤ ρ₂ < 1`
is non-vacuous at the seed by exhibiting concrete `ρ₁, ρ₂`. It **does
NOT** discharge any of the integrability premises, the summability
premise, or the kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ`. Those remain as
existential hypotheses on the new reducer.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
    matching the shape above. Place it **after** sprint 023's
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
    at the end of the file (after current line 3606), so the
    chronological narrative is preserved.

    The proof body must:

    1. **Open `valid_of` framework via sprint 023.** A clean pattern:
       ```lean
       refine valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window
         hc_pos hc_lt_one ?_
       intro a b K paper
       obtain ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
           hIntDiskInner, hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
         h_witness paper
       ```

    2. **Geometric scaffolding for `0 ≤ ρ₁`.** Verbatim from
       sprint 023 lines 3484-3497:
       ```lean
       have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
         unfold PaperAxioms.branchSplit
         have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
         have h_sqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
           Real.sqrt_nonneg _
         have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
           Real.sq_sqrt (le_of_lt h_pos)
         have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
           nlinarith [h_sq, h_sqrt_nonneg]
         nlinarith [h_sqrt_gt_one, hc_pos]
       have hcρ₁ : c < ρ₁ := lt_of_lt_of_le hSplit_gt_c hSplit_le_ρ₁
       have hρ₁_pos : 0 < ρ₁ := lt_trans hc_pos hcρ₁
       have hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le
       ```

    3. **In-house derivation of `hSummable_ρ₁`** via sprint 012:
       ```lean
       have hSummable_ρ₁ :=
         sigmaZeroMinus_summable_of_summable_at_upper
           hρ₁_nonneg hρ₁₂ hSummable_top
       ```

    4. **Re-pack the existential bundle for sprint 023.** All 8 cells
       in the order sprint 023 expects (3 geometric, 4 integrability,
       2 summability, 1 kernel — see sprint 023 line 3480-3482):
       ```lean
       exact ⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
         hIntDiskInner, hIntLambdaZ, hIntLambda, hSummable_ρ₁,
         hSummable_top, hKernel⟩
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 024's
    `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
    is the workspace's **first end-to-end branch-2 closing reducer
    with zero `eq6` consumption AND only one series-summability
    premise**, collapsing sprint 023's two-anchor summability shape
    (`Z @ ρ₁` and `Z @ ρ₂`) into a single point summability premise at
    `ρ₂` via sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper`
    transfer applied at `s = ρ₁, t = ρ₂`. Mirrors sprint 012's
    relationship to sprint 011, and sprint 014's single-summability
    shape on the full window — first deployment of that shape on the
    branch-2 sub-window.

  * The body of the new theorem MAY invoke:

    * `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
      (sprint 023, the *unique* closing-reducer dispatch),
    * `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012, in
      the new single-anchor disk-side bridging role),
    * `Real.sqrt_nonneg`, `Real.sq_sqrt`, `nlinarith`, `lt_of_lt_of_le`,
      `lt_trans`, `le_of_lt`, `norm_num`,
    * Definitional unfolding of `PaperAxioms.branchSplit`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that sprint 024
    defers to sprint 023 for all closure machinery, and that the new
    chain remains within the `(2)+(3)+(4)+(8)+(9)+series` paper-axiom
    signature):

    * `paper.eq5_branch1_sigmaReduction`,
    * `paper.eq6_branch2_sigmaReduction`,
    * `paper.eq10_branch1_pointwise`,
    * `paper.eq11_branch2_pointwise`,
    * `paper.eq12_branch1_integrated`,
    * `paper.eq13_branch2_integrated`,
    * `paper.eq14_combined`,
    * `paper.eq15_…`,
    * Any other `valid_of_*` reducer than sprint 023
      (specifically forbidden: `valid_of_eq15`, `valid_of_eq12_eq13`,
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
      `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor`),
    * `diskExcess_upper_bound_*`,
    * `annulusExcess_lower_bound_*`,
    * `circleGap_inner_bound_of_eq2_eq3_eq4`,
    * `circleGap_outer_lower_bound_of_eq8_eq9`,
    * `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    * `sigmaZeroMinus_nonneg_of_pos`,
    * `sigmaZeroMinus_monotone_of_summable` (forbidden: this is
      *transitively* consumed via sprint 023 and via sprint 022, but
      sprint 024's body has no direct need; the only direct invocation
      of a sprint 011/012 lemma is sprint 012, in the new disk-side
      bridging role),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, `eq10_of_eq5_eq8_eq9`,
      `eq11_of_eq6_eq8_eq9`,
    * `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`, `branch1SigmaKernel`,
      `branch1PointwiseFactor`, `branch2SigmaKernel`,
      `branch2PointwiseFactor`,
    * `mass_mul_le_annulusSlice_of_integral_bound_ae`,
      `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
    * `WangPaperSideConditions.paperLambda_pos`,
      `intervalIntegral.integral_mul_const`,
      `intervalIntegral.integral_mono_on_of_le_Ioo`,
      `mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left`,
      `div_nonneg` (these are markers of the `hStepA`/`hStepB`/`hStepC`
      annulus-side cascade, all of which sprint 024 defers to sprint
      023's body and must NOT re-invoke directly).

    (Note: `paper.eq2_sigmaZeroMinus_lower`,
    `paper.eq3_circleGap_decomposition`,
    `paper.eq4_sigmaPlus_bound`, `paper.eq8_sigmaToLiftGap`,
    `paper.eq9_liftGapToCircleGap`, `paper.eq7_paperK_formula`,
    `paper.circleGap`, and `Section2Assumptions` are EXEMPT and ARE
    transitively consumed via sprint 023's body. `WangOuter.paperLambda`
    is EXEMPT — it is a named ingredient of the kernel inequality.
    `PaperAxioms.branchSplit` is EXEMPT — it appears in the witness
    type signature.)

  * The new theorem's signature MUST take *exactly* the parameters in
    the goal block above. The 7 existential conjunction cells must
    appear in the order listed in the goal block: 3 geometric (in
    order `branchSplit c ≤ ρ₁`, `ρ₁ ≤ ρ₂`, `ρ₂ < 1`), 4
    integrability (`(2ρ·circleGap) volume c 1`,
    `(2r·circleGap) volume 0 c`, `(2ρ³·Z/Λ) volume ρ₁ ρ₂`,
    `(2ρ³/Λ) volume ρ₁ ρ₂`), 1 summability (at `ρ₂` only — the
    distinguishing structural feature vs sprint 023), and 1 kernel
    inequality (`c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ`).

* `ProofRefinement/Korenblum/Candidates/V24.lean`:

  * `-- @parent V23`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V23).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V23).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v24_branch2_uniformSummable_compiles
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
                    PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                  else 0) ∧
                (c_value ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                                2 * ρ' ^ 3
                                  / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable
        c_value_pos c_value_lt_one h_witness
    ```

  * Additionally, prove a structural witness lemma confirming the
    branch-2 admissibility predicate is non-vacuous at the seed by
    exhibiting concrete `(ρ₁, ρ₂) = (1/2, 1/2)`:

    ```lean
    theorem v24_branch2_uniformSummable_witness_at_seed :
        PaperAxioms.branchSplit c_value ≤ (1 : ℝ) / 2 ∧
          (1 : ℝ) / 2 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
      refine ⟨?_, le_rfl, by norm_num⟩
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

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify the new reducer's signature
    typechecks at the seed `c_value` and to demonstrate the
    branch-2 window is non-vacuous.

* `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_024 queued: ...` line.

* `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting the single-summability collapse on the
  branch-2 axis, the new role for sprint 012 as a single-anchor
  disk-side bridging lemma, and the follow-up roadmap (e.g., the
  natural next step would be the alternative-B sprint anchoring the
  disk side at `c` itself on branch-2 via a new
  `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_to_Z_c` lemma —
  enabling a kernel inequality with no `[branchSplit c, 1)` constraint
  on either side).

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V23.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_023`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V24.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V24.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V24 scores `≥` V23 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V24.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of
     `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
     (sprint 023 — the unique closing-reducer dispatch),
   * exactly one direct invocation of
     `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012 — the
     in-house single-anchor disk-side bridging derivation),
   * **no direct reference** to `paper.eq6_branch2_sigmaReduction`,
     `paper.eq11_branch2_pointwise`, `paper.eq5_branch1_sigmaReduction`,
     `paper.eq10_branch1_pointwise`, `paper.eq12_branch1_integrated`,
     `paper.eq13_branch2_integrated`, `paper.eq14_combined`, or
     `paper.eq15_…`,
   * **no reference** to any other prior `valid_of_*` reducer (only
     `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`
     is allowed),
   * **no reference** to `diskExcess_upper_bound_*`,
     `annulusExcess_lower_bound_*`,
     `circleGap_inner_bound_of_eq2_eq3_eq4`,
     `circleGap_outer_lower_bound_of_eq8_eq9`,
     `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
     `sigmaZeroMinus_nonneg_of_pos`,
     `sigmaZeroMinus_monotone_of_summable`,
   * **no reference** to `mass_mul_le_annulusSlice_of_integral_bound_ae`,
     `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
     `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
     `Korenblum.scalarIntegrand2`, `branch1SigmaKernel`,
     `branch1PointwiseFactor`, `branch2SigmaKernel`,
     `branch2PointwiseFactor`,
   * **no reference** to `eq11_of_eq6_eq8_eq9`,
     `eq10_of_eq5_eq8_eq9`,
     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
   * **no reference** to `WangPaperSideConditions.paperLambda_pos`,
     `intervalIntegral.integral_mul_const`,
     `intervalIntegral.integral_mono_on_of_le_Ioo` (markers of the
     `hStepA`/`hStepB`/`hStepC` cascade — defer to sprint 023).
6. `grep -n 'v24_branch2_uniformSummable_compiles\|v24_branch2_uniformSummable_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V24.lean`
   returns at least two distinct matches.
7. The conclusion of
   `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window_uniformSummable`
   is exactly `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_witness` existential body in the new theorem contains:
   * the constraint `PaperAxioms.branchSplit c ≤ ρ₁` (closed-form weak
     inequality — verify via `grep`),
   * the constraint `ρ₁ ≤ ρ₂` (verify via `grep`),
   * the constraint `ρ₂ < 1` (verify via `grep`),
   * **exactly one `Summable` cell** at `ρ₂ ^ (2 * k - 2)` (verify via
     `grep` for `Summable` substring count within the existential body
     — should be exactly 1, not 2),
   * **no occurrence** of `ρ₁ ^ (2 * k - 2)` (verify via `grep` —
     sprint 024's signature has *no* summability cell at `ρ₁`, that
     is the structural distinguishing feature from sprint 023),
   * the kernel inequality
     `(c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'`
     (verify via `grep`).
9. The body of `v24_branch2_uniformSummable_witness_at_seed` exhibits
   the concrete witness `(ρ₁, ρ₂) = (1/2, 1/2)` and discharges the
   three conjuncts `branchSplit c_value ≤ 1/2`, `1/2 ≤ 1/2`, `1/2 < 1`.
10. **Premise count check**: the new reducer's existential body has
    **exactly 7 conjunction cells** (3 geometric + 4 integrability + 1
    summability + 1 kernel = 9 atoms but bundled as 7 outer cells in
    the goal-block ordering). Verifiable by counting `∧` operators in
    the printed theorem statement.
11. **Structural marker**: the new reducer is the workspace's first
    end-to-end branch-2 closing reducer with both
    `paper.eq6_branch2_sigmaReduction = 0 invocations` (transitively,
    via sprint 023) AND `Summable @ ρ₁ = 0 caller obligations` (the
    summability premise list contains only `Summable @ ρ₂`, not also
    `Summable @ ρ₁` as in sprint 023). Verifiable by `grep` count of
    `Summable` within the new theorem's signature.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V23.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the branch-1 mirror (alternative A above — demoted by
  parent planner in sprint 023).
* Building the disk-anchor-at-`c` branch-2 closer (alternative B above
  — requires a new `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_to_Z_c`
  lemma, exceeds bounded-Generator-session budget; queueable as a
  separate sprint after 024).
* Building the cross-validation algebraic identity
  `branch1SigmaKernel c ρ · ρ² = (c⁶/6)/(ρ²−c²)` (alternative C —
  too narrow for a full sprint).
* Building a `circleGapSeries`-direct sufficient condition
  (alternative D — needs structural exploration first).
* Working at the `liftGap` intermediate layer (alternative E — no
  closed-form lower bound available).
* Adding a series-level upper-bound lemma for `sigmaZeroMinus`
  (alternative F — needs structural exploration first).
* Discharging the kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ` numerically at
  the seed `c_value` (alternative G — requires `paperLambda` envelope
  or numerical oracle, both out of scope for this sprint).
* Numerical exploration of `(ρ₁, ρ₂)` minimisers in `Scratch/`
  (alternative I — needs `paperLambda` envelope first).
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires a numerical closure
  of the kernel inequality (out of scope above) or a qualitatively new
  analytical witness.
* Any modification to sprints 022 or 023's existing lemmas
  (`diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
  `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window`),
  or any of the sprint 005/006/011/012 series-level lemmas (these
  are consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 024 is purely
  structural.

## Time budget

≤ 30 minutes runtime. The new reducer is a thin wrapper around sprint
023 — ~50 lines of Lean: ~25 lines for the signature (one summability
cell shorter than sprint 023's signature), ~20 lines for the proof
body (10 lines of geometric scaffolding verbatim from sprint 023, 1
line of `sigmaZeroMinus_summable_of_summable_at_upper` invocation, ~9
lines of existential re-packing). All tactics used are *already
verified* in sprint 012 (`Reduction.lean:1497-1546`) and sprint 023
(`Reduction.lean:3448-3606`). The candidate side lemmas are 5–25 lines
each (including the witness at the seed). Total V24 size: ≤ 80 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* Sprint 023's existential cell ordering does not match the
  re-packing order specified above — fall back to inspecting sprint
  023's exact cell order at `Reduction.lean:3480-3482` and adjusting
  the re-packing tuple in step 4 above to match. The 12-tuple shape
  is `⟨ρ₁, ρ₂, hSplit_le_ρ₁, hρ₁₂, hρ₂_lt_one, hIntCircle,
  hIntDiskInner, hIntLambdaZ, hIntLambda, hSummable_ρ₁, hSummable_top,
  hKernel⟩` — note `hSummable_ρ₁` precedes `hSummable_top` (sprint
  023's ordering at line 3481).
* `sigmaZeroMinus_summable_of_summable_at_upper` requires
  `0 ≤ s ≤ t` and summability at `t`; sprint 024 must thread
  `hρ₁_nonneg` (derived in step 2) and `hρ₁₂` (destructured in
  step 1) and `hSummable_top` (destructured in step 1). All three
  are in scope after step 2.
* The geometric scaffolding `hSplit_gt_c` step fails — fall back to
  copying sprint 023 lines 3484-3493 verbatim. Sprint 022 lines
  1959-1968 carry the same proof and can serve as a secondary
  reference.
* Any of acceptance criteria 4, 5, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5: `STATUS=BLOCKED` — that would defeat the
  **single-summability** structural guarantee or break the chain
  isolation from sprint 023.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
