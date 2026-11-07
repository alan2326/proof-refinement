# Sprint 017: Branch-2-only single-`Z_{ρ₁}` closing reducer fusing sprint 016's disk bound with sprints 005/006/011/012's annulus side — `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`, the workspace's **first closing reducer that lives entirely on the branch-2 sub-regime `(branchSplit c, 1)`** and the **first closing reducer with no disk-side integrability premise**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V16.lean`
**Target file**: `Candidates/V17.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_eq6_annulus_eq8_eq9_branch2_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
            (c ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                            2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The proof chain follows sprint 014's blueprint, with three load-bearing
substitutions:

1. **Disk-side anchor.** Replace sprint 014's call to
   `diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one hIntDisk`
   (which gives `diskExcess ≤ c⁴ · Z_c` and consumes a disk-side
   integrability premise) by sprint 016's
   `diskExcess_upper_bound_via_eq6 paper hSplit_lt_ρ₁ hρ₁_lt_one`
   (which gives `diskExcess ≤ branch2SigmaKernel c ρ₁ · ρ₁² · Z_{ρ₁}`
   with **no integrability premise** at all). Then collapse the
   structural form via `unfold PaperAxioms.branch2SigmaKernel; field_simp;
   ring` (with `ρ₁ ≠ 0` from `0 < c < ρ₁`) to land at the simplified
   closed form `(c⁴/2) · Z_{ρ₁}`.

2. **Z-monotonicity anchor.** Replace sprint 014's `Z_c ≤ Z_{ρ'}`
   monotonicity (anchored at `c`) by `Z_{ρ₁} ≤ Z_{ρ'}` (anchored at the
   left edge of the window `ρ₁ ∈ (branchSplit c, 1)`). The discharge is
   structurally identical: `sigmaZeroMinus_summable_of_summable_at_upper`
   transports summability from `ρ₂` to each `ρ' ∈ [ρ₁, ρ₂]`, then
   `sigmaZeroMinus_monotone_of_summable` yields `Z_{ρ₁} ≤ Z_{ρ'}` (since
   `0 ≤ ρ₁ ≤ ρ'` from the window).

3. **Annulus-side closure.** Identical to sprint 014: invoke
   `annulusExcess_lower_bound_of_eq8_eq9 paper hc_pos hcρ₁ hρ₁₂
   hρ₂_lt_one hIntCircle hIntLambdaZ` (where `hcρ₁ : c < ρ₁` is
   derived from `c < branchSplit c < ρ₁` via
   `WangPaperSideConditions.branchSplit_pos_of_pos` /
   `branchSplit_gt_self_of_pos`, OR more simply from the bound
   `c < c · √(4/3)` for `c > 0` since `√(4/3) > 1`).

The kernel inequality LHS is `c⁴/2` rather than sprint 014's `c⁴` —
**a strict factor-of-2 reduction in the budget that must be discharged
by the same RHS shape `∫ 2ρ³/Λ`**.

The fixed final theorem shape `ValidKorenblumBound c_value` is
unchanged.

Then ship a `Candidates/V17.lean` at the same `c = 0.3554` that
compiles, scores `≥ V16`, and *materialises* the new lemma in side
lemmas `v17_branch2_window_reducer_compiles` and
`v17_branch2_window_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 016 explicitly queued this exact sprint
as the natural follow-up to its branch-2 disk-side bound:

> Out of scope: Building any reducer that combines sprint 016 with
> sprint 005/006 into a closing chain (the natural follow-ups
> `valid_of_eq6_eq8_eq9_branch2_singleton`, …). Those reducers require
> non-trivial single-point disk vs windowed annulus constructions,
> comparable in size to sprint 016 itself. **Queue as separate sprints.**

Sprint 017 ships exactly this queued reducer. It is **a genuinely new
analytical chain**, not a flavour clone, on five independent axes:

1. **First workspace closing reducer that lives entirely on the
   branch-2 sub-regime `(branchSplit c, 1)`.** Every prior closing
   reducer's admissible window is *either* inside the branch-1
   sub-regime (sprint 008: `[ρ₁, ρ₂] ⊆ (c, branchSplit c]`), *or*
   spans both branches via the branch-split constraint (sprints
   009-012: `ρ ∈ (c, branchSplit c]`), *or* anchors disk-side at `c`
   itself with no branch sensitivity (sprints 013-014: `[ρ₁, ρ₂] ⊆
   (c, 1)`, disk side at `ρ = c`). **No prior closing reducer's
   window is constrained to lie in `(branchSplit c, 1)`.** Sprint 017
   fills this analytical gap: the admissible window must satisfy
   `branchSplit c < ρ₁ ≤ ρ₂ < 1`, the branch-2 sub-regime exactly,
   reaching closure via Wang's branch-2 reduction `(6)` and the
   annulus-side bridge `(8)+(9)`.

2. **First workspace closing reducer with no disk-side integrability
   premise.** Sprint 014 carries
   `IntervalIntegrable (fun r => 2 * r * circleGap a b r) volume 0 c`
   as an explicit hypothesis (because the disk anchor `c⁴ · Z_c` is
   produced by `diskExcess_upper_bound_via_eq3_eq4`, which integrates
   over `[0, c]`). Sprint 016's `diskExcess_upper_bound_via_eq6` has
   **no integration step at all** — it consumes only `eq6` and the
   sprint 005 series identity. Therefore sprint 017's disk-side has
   **zero integrability premises**. The only integrability premises
   in the entire reducer are annulus-side (the `[ρ₁, ρ₂]`
   `IntervalIntegrable` premises mirror sprint 014 verbatim, and the
   global `[c, 1]` integrability that sprint 006 needs). This is a
   genuine premise reduction — sprint 017's admissible-witness
   conjunction is **strictly smaller** than sprint 014's (one fewer
   integrability premise, no `r ↦ 2r·circleGap` over `[0,c]` needed
   anywhere in the chain).

3. **First workspace reducer to consume sprint 016's `eq6`-based disk
   bound.** Sprint 016 lands the disk bound but does not exercise it
   in any closing chain. Sprint 017 ships the **first closing
   reducer to consume `paper.eq6_branch2_sigmaReduction` (transitively
   via sprint 016) in the disk side**. Until sprint 017, the only
   closing reducers in `Reduction.lean` consume `(2)+(3)+(4)+(8)+(9)`
   (sprints 009-014) or `(7)+(10)` (sprint 008) on the disk side.
   Sprint 017 is the **first to use `(6)+(8)+(9)`**, opening the
   `eq6`-based closure axis. After this sprint, the workspace will
   have closing reducers via `(2)+(3)+(4)+(8)+(9)`, `(7)+(10)`, AND
   `(6)+(8)+(9)` — three structurally distinct paper-equation chains
   to closure.

4. **Strictly tighter kernel inequality than sprint 014 in the
   branch-2 sub-regime.** Sprint 014's kernel inequality reads
   `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` and admits any `[ρ₁, ρ₂] ⊂ (c, 1)`.
   Sprint 017's kernel inequality reads
   `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` and admits any `[ρ₁, ρ₂] ⊂
   (branchSplit c, 1)`. **In the branch-2 sub-regime where both
   reducers are admissible, sprint 017's LHS is strictly half of
   sprint 014's** — the same RHS shape needs to clear half the LHS.
   For any branch-2 window where sprint 014 closes the contract,
   sprint 017 closes it with a factor-of-2 margin to spare. For
   branch-2 windows where sprint 014's RHS lies in
   `[c⁴/2, c⁴)`, **only sprint 017 closes the contract**. This
   directly serves planning goal (3): a precise oracle-backed
   subclaim that supports a future increase in `c_value`. (At the
   seed `c = 0.3554`, `c⁴ ≈ 0.01595` and `c⁴/2 ≈ 0.00797`, so
   sprint 017 needs to clear half the budget that sprint 014 clears
   — meaningful for any future numerical push.)

5. **Disk-side anchor at the window's left edge `ρ₁`, not at `c`.**
   Sprint 014 anchors its single-`Z` disk bound at `ρ = c` (giving
   `c⁴ · Z_c`). Sprint 017 anchors at the window's *left edge*
   `ρ = ρ₁ ∈ (branchSplit c, 1)` (giving `(c⁴/2) · Z_{ρ₁}`). This is
   the **first workspace single-`Z` closing reducer where the disk-side
   `Z`-anchor is a free window-relative parameter** — sprint 014's
   anchor is fixed at `c`, sprints 011/012 anchor at the branch-1
   left edge but require `ρ₁ ≤ branchSplit c`, sprint 008 has no
   single-`Z` shape. The Z-monotonicity discharge then becomes
   `Z_{ρ₁} ≤ Z_{ρ'}` instead of `Z_c ≤ Z_{ρ'}` — a structurally
   parallel but *anchor-shifted* monotonicity premise.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V17 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` that holds for *any*
  paper-faithful instance, parameterised by the witness window
  `(ρ₁, ρ₂)` and a single scalar kernel inequality.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the branch-2 sub-regime is non-empty at the seed
  (re-using the V16 witness `ρ = 5/10`).

Why this is **not** "the same chain" as any prior closing reducer:

* **Different disk-side ingredient.** Sprint 014 uses
  `diskExcess_upper_bound_via_eq3_eq4` (sprint 013, full disk regime,
  integration over `[0, c]`). Sprint 017 uses
  `diskExcess_upper_bound_via_eq6` (sprint 016, branch-2 sub-regime,
  zero integration). These are derived from disjoint sets of paper
  hypotheses (`eq3+eq4` vs `eq6`).
* **Different admissible window.** Sprint 014 admits any `[ρ₁, ρ₂] ⊂
  (c, 1)`. Sprint 017 admits only `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`.
  These are genuinely different admissibility predicates.
* **Different LHS scalar.** Sprint 014: `c⁴`. Sprint 017: `c⁴/2`.
* **Different `Z`-anchor.** Sprint 014: `Z_c`. Sprint 017: `Z_{ρ₁}`.
* **Different premise count.** Sprint 014 carries two integrability
  premises that touch the disk (`[0, c]` and `[c, 1]`). Sprint 017
  carries only one (`[c, 1]`).

Why this is **not** "the same chain" as sprint 008 (`eq10`-based
sub-interval branch-1 reducer):

* Sprint 008 lives on **branch 1** (`[ρ₁, ρ₂] ⊆ (c, branchSplit c]`);
  sprint 017 lives on **branch 2** (`[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`).
* Sprint 008's chain is `(7)+(10)` (consumes `eq10` directly). Sprint
  017's chain is `(6)+(8)+(9)+`series (consumes `eq6` directly +
  `eq8+eq9` for the annulus side). These overlap in *no* paper
  hypothesis.
* Sprint 008's mode-mass shape is `1 ≤ ∫ scalarIntegrand1`, a
  branch-1 mode mass premise. Sprint 017's mode-mass shape is
  `c⁴/2 ≤ ∫ 2ρ³/Λ`, a branch-2 raw-Λ kernel premise. Different LHS
  shape, different RHS shape.

Why this is **bounded enough for one Generator session**:

* The proof body is a textbook adaptation of sprint 014's chain with
  three substitutions (disk-side ingredient, monotonicity anchor,
  kernel scalar). Estimate: ≤ 100 lines of Lean for the new theorem
  (sprint 014's body is ~140 lines; sprint 017 saves ~40 lines by
  dropping the disk integrability machinery and the disk-anchor
  re-anchoring).
* No new Mathlib lemmas needed. Every Lean idiom used
  (`mul_le_mul_of_nonneg_left`, `intervalIntegral.integral_mul_const`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `sigmaZeroMinus_monotone_of_summable`,
  `sigmaZeroMinus_summable_of_summable_at_upper`,
  `annulusExcess_lower_bound_of_eq8_eq9`,
  `diskExcess_upper_bound_via_eq6`, `field_simp`, `ring`, `calc`) is
  **already verified in sprint 014 at `Reduction.lean:1686-1827` and
  in sprint 016 at `Reduction.lean:1885-1913`**.
* The disk-side closed-form collapse `branch2SigmaKernel c ρ₁ * ρ₁²
  = c⁴/2` is one `unfold; field_simp; ring` step, mirroring the
  sprint 002 → sprint 003 polynomial collapse pattern.
* The candidate side lemmas are one to three lines each (sprint 016
  shows the V-side typechecking pattern). Total V17 size: ≤ 80 lines.

Why this beats the alternatives I considered:

* **A: Z-free version of sprint 017** (extract `Z_{ρ₁}` from both
  sides via sprint 011 monotonicity, leaving the kernel
  `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` literally Z-free). This is the
  natural sprint-018 follow-up after sprint 017 lands, mirroring how
  sprint 014 followed sprint 013. Demoted **only** because it requires
  sprint 017's base reducer first as a building block — queue as
  sprint 018.

* **B: `eq11`-based branch-2 mirror of sprint 008
  `valid_of_eq11_subinterval_branch2`.** Sprint 016's contract demoted
  this as flavour clone of sprint 008. The demotion still applies:
  every step has a 1↔2 substitution against sprint 008's body, no new
  analytical content. **Demoted as flavour clone.**

* **C: Combined `eq5 + eq6` full-annulus disk bound (alternative H
  from sprint 016).** Mechanical disjunction of sprints 015 and 016
  via `if ρ ≤ branchSplit c then … else …`. No new analytical chain
  through `Section2Assumptions` — just a glue lemma. **Demoted as
  glue, not a new chain.**

* **D: Closed-form `sigmaZeroMinus` series identity at `s = 0`.**
  Sprint 016 demoted as "structural novelty without a useful
  downstream consumer." Still no consumer queued. **Demoted.**

* **E: Continuity of `s ↦ sigmaZeroMinus a b s`.** Sprint 016 demoted
  as speculative. **Demoted.**

* **F: Dropping the `Summable` premise via a new ambient summability
  lemma.** Would need to derive series-level summability from
  `Section2Assumptions` alone (which currently does not expose any
  summability of `b k` directly). Speculative — likely needs an
  ambient hypothesis bounding `‖b k‖` from above. **Demoted: needs
  trust expansion or proposal.**

* **G: `Λ`-upper-envelope oracle that discharges the kernel
  inequality `c⁴/2 ≤ ∫ 2ρ³/Λ` for `c = 0.3554` numerically.** Would
  enable a literal `c_value` push at the seed via sprint 017. But
  this requires either a `WangPaperSideConditions.paperLambda_le_*`
  closed-form (lives outside the workspace allowlist) or a
  `lemma.toml:[[oracles]]` registration with a `Numerical_Library`
  function. The latter is in scope per `AGENT_BRIEF.md`'s "Numerical
  tooling" section, but **specifying the oracle correctly requires
  knowing the specific sub-window `[ρ₁, ρ₂]` and the `Λ`-bound shape**
  — neither is currently established. **Demoted: queue as a separate
  sprint after sprint 017 establishes the closure-from-kernel
  reducer, so the oracle has a concrete consumer.**

* **H: Symbolic upper bound on `paperLambda` from
  `paper.eq7_paperK_formula` alone.** Promising but speculative —
  `paperLambda` is defined in `KorenblumPaper.OneModePaperBridge`
  via Wang's complicated `M(c, ρ)` formula, and no closed-form
  upper envelope is exposed. **Demoted: requires investigating
  the `OneModePaperBridge` interior, which is beyond a single
  Generator session.**

Compared to A–H, candidate I (this sprint, candidate F in the planner
analysis) maximises analytical novelty per bounded Generator session:
it ships the **first workspace closing reducer that lives entirely on
the branch-2 sub-regime**, the **first closing reducer with no
disk-side integrability premise**, and the **first reducer to consume
sprint 016's `eq6`-based disk bound**. It uses **only existing trusted
modules + pinned Mathlib + already-verified Reduction.lean lemmas**
in patterns directly mirrored from sprint 014. No proposal needed.

### Note on the disk-side closed-form collapse

Sprint 016's disk bound is in **structural form**:

```
diskExcess ≤ branch2SigmaKernel c ρ₁ * ρ₁^2 * sigmaZeroMinus a b ρ₁
```

We need the **simplified form** `(c⁴/2) * sigmaZeroMinus a b ρ₁` to
match sprint 014's blueprint. The collapse is a one-step algebraic
identity:

```lean
have hCollapse :
    PaperAxioms.branch2SigmaKernel c ρ₁ * ρ₁ ^ 2 = c ^ 4 / 2 := by
  unfold PaperAxioms.branch2SigmaKernel
  have hρ₁_ne : ρ₁ ≠ 0 := ne_of_gt hρ₁_pos
  field_simp
  ring
```

where `hρ₁_pos : 0 < ρ₁` follows from
`branchSplit c < ρ₁` and `0 < c < branchSplit c` (the latter from
`branchSplit c = c · √(4/3) > c · 1 = c > 0`). The Generator may
need a small helper `branchSplit_pos_of_pos : 0 < c → 0 < branchSplit c`
or simply `lt_trans hc_pos hcρ₁` after deriving `c < branchSplit c`.

### Note on deriving `c < ρ₁` from `branchSplit c < ρ₁`

`branchSplit c = c · √(4/3) > c` for `c > 0` since `√(4/3) > 1`. The
required helper:

```lean
have hSplit_gt_c : c < PaperAxioms.branchSplit c := by
  unfold PaperAxioms.branchSplit
  have h_sqrt_gt_one : (1 : ℝ) < Real.sqrt (4 / 3) := by
    have h_one_sq : (1 : ℝ) ^ 2 < 4 / 3 := by norm_num
    have h_one_nonneg : (0 : ℝ) ≤ 1 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3),
               Real.sqrt_nonneg (4 / 3 : ℝ)]
  nlinarith [Real.sqrt_nonneg (4 / 3 : ℝ), h_sqrt_gt_one, hc_pos]
```

Then `hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁`.

The Generator may also choose to factor this out as a separate
helper `branchSplit_gt_self_of_pos` if convenient, but a one-shot
inline derivation is acceptable.

### Note on `0 ≤ ρ₁` for the monotonicity discharge

`sigmaZeroMinus_monotone_of_summable` requires `0 ≤ ρ₁` and
`ρ₁ ≤ ρ'`. Both follow from the witness window:
* `0 ≤ ρ₁` from `0 < c < branchSplit c < ρ₁`.
* `ρ₁ ≤ ρ'` from the membership `ρ' ∈ Set.Icc ρ₁ ρ₂`.

Compare sprint 014, where the monotonicity anchor is at `c` and so
the premises become `0 ≤ c` (from `hc_pos.le`) and `c ≤ ρ'` (from
`hc_le_ρ'`). Sprint 017 anchors at `ρ₁` instead, so the premises
become `0 ≤ ρ₁` (from `hρ₁_nonneg`) and `ρ₁ ≤ ρ'` (from
`hρ₁_le_ρ'`).

### Note on the witness window at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value ≈ 0.4103`.
* Any `ρ₁, ρ₂` with `0.4103 < ρ₁ ≤ ρ₂ < 1` is admissible. Natural
  witness choice: `(ρ₁, ρ₂) = (5/10, 7/10) = (0.5, 0.7)`. Sprint 014's
  V14 already exercises a window `(5/10, 7/10)` with
  `ρ₁ = 0.5 > branchSplit c_value`, so the witness is already
  verified feasible at the seed.

### Note on what the witness lemma should NOT do

Sprint 017's V17 witness lemma is **structural only** — it confirms
that the admissible-window predicate `branchSplit c_value < ρ₁ ≤ ρ₂
< 1` is non-vacuous at the seed by exhibiting concrete `ρ₁, ρ₂`. It
**does NOT discharge any of the integrability premises, the
summability premise, or the kernel inequality**. Those remain as
existential hypotheses on the new reducer, just like sprint 014's
V14 witness does not discharge sprint 014's premises.

Discharging the kernel inequality numerically at the seed would
require a `paperLambda` closed-form upper envelope (alternative H
above) or an oracle (alternative G above), both of which are
out-of-scope for sprint 017.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` matching the
    shape above. The proof body must:

    1. **Unpack the witness.** Destructure
       `h_witness paper` into
       `⟨ρ₁, ρ₂, hSplit_lt_ρ₁, hρ₁₂, hρ₂_lt_one,
          hIntCircle, hIntLambdaZ, hIntLambda,
          hSummable_top, hKernel⟩`.

    2. **Derive geometric scaffolding.**
       * `hSplit_gt_c : c < branchSplit c` (helper above).
       * `hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁`.
       * `hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one`.
       * `hρ₁_pos : 0 < ρ₁ := lt_trans hc_pos hcρ₁`.
       * `hρ₁_nonneg : 0 ≤ ρ₁ := hρ₁_pos.le`.

    3. **Disk-side bound.** Invoke sprint 016:
       ```lean
       have hDiskRaw :=
         diskExcess_upper_bound_via_eq6 paper hSplit_lt_ρ₁ hρ₁_lt_one
       ```
       Then collapse the kernel:
       ```lean
       have hCollapse :
           PaperAxioms.branch2SigmaKernel c ρ₁ * ρ₁ ^ 2 = c ^ 4 / 2 := by
         unfold PaperAxioms.branch2SigmaKernel
         have : ρ₁ ≠ 0 := ne_of_gt hρ₁_pos
         field_simp
         ring
       have hDisk :
           PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := by
         calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
             ≤ PaperAxioms.branch2SigmaKernel c ρ₁ * ρ₁ ^ 2 *
                 PaperAxioms.sigmaZeroMinus a b ρ₁ := hDiskRaw
           _ = c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := by
                 rw [hCollapse]
       ```

    4. **Anchor `Z_{ρ₁}` non-negativity.** Via sprint 005:
       ```lean
       have hZ_ρ₁_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ₁ :=
         sigmaZeroMinus_nonneg_of_pos a b hρ₁_pos
       ```

    5. **Step (a): multiply the kernel inequality by `Z_{ρ₁} ≥ 0`.**
       Mirrors sprint 014's `hStepA` exactly, with `Z_c → Z_{ρ₁}`
       and LHS scalar `c⁴ → c⁴/2`.

    6. **Step (b): pull `Z_{ρ₁}` inside the integral.** Mirrors
       sprint 014's `hStepB` with `Z_c → Z_{ρ₁}`.

    7. **Step (c): build pointwise `Z_{ρ₁} ≤ Z_{ρ'}` via sprint 011
       + sprint 012.** Mirrors sprint 014's `hZmono` and
       `hPointwise`/`hStepC` with the anchor `c → ρ₁`. The
       monotonicity premises become:
       ```lean
       have hZmono : ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
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

    8. **Step (d): annulus-side bound via sprint 006.** Mirrors
       sprint 014's `hAnn` verbatim:
       ```lean
       have hAnn :=
         annulusExcess_lower_bound_of_eq8_eq9
           paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
       ```

    9. **Final `calc` chain.** Mirrors sprint 014's final calc with
       the disk-side LHS `c⁴ * Z_c → c⁴/2 * Z_{ρ₁}`:
       ```lean
       change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
         PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
       calc
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
             ≤ c ^ 4 / 2 * PaperAxioms.sigmaZeroMinus a b ρ₁ := hDisk
         _ ≤ (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
               * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepA
         _ = ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                   * PaperAxioms.sigmaZeroMinus a b ρ₁ := hStepB
         _ ≤ ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                   WangOuter.paperLambda K c ρ' := hStepC
         _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 017's
    `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` is the
    workspace's **first closing reducer that lives entirely on the
    branch-2 sub-regime `(branchSplit c, 1)`**, the **first closing
    reducer with no disk-side integrability premise**, and the
    **first reducer to consume sprint 016's `eq6`-based disk bound
    in a closing chain**. The kernel inequality `c⁴/2 ≤ ∫_{ρ₁..ρ₂}
    2ρ³/Λ(c,ρ)` is **strictly weaker (factor of 2 in the LHS)**
    than sprint 014's `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ)` on the same
    branch-2 sub-window, opening the natural Z-free follow-up
    (sprint 018, queued separately).

  * The body of `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`
    MAY invoke:

    * `diskExcess_upper_bound_via_eq6` (sprint 016),
    * `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006),
    * `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
    * `sigmaZeroMinus_monotone_of_summable` (sprint 011),
    * `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012),
    * `PaperAxioms.branch2SigmaKernel`, `PaperAxioms.branchSplit`
      (definitional unfolding),
    * `Real.sqrt`, `Real.sq_sqrt`, `Real.sqrt_nonneg` (for the
      `branchSplit c > c` helper),
    * `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `intervalIntegral.integral_mul_const`,
      `intervalIntegral.integral_mono_on_of_le_Ioo`,
      `IntervalIntegrable.mul_const`,
      `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`,
      `calc`, `change`, `unfold`, `rw`, `simpa`.

    The body must **NOT** invoke any of the following forbidden
    references:

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
      `paper.eq7_`, `paper.eq10_`, `paper.eq11_`, `paper.eq12_`,
      `paper.eq13_`, `paper.eq14_`, `paper.eq15_` (the proof must
      use **only** `eq6`, `eq8`, `eq9` — and these only via the
      sprint 006, sprint 011, sprint 012, sprint 016 helpers),
    * direct calls to `paper.eq6_branch2_sigmaReduction`,
      `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`
      (the proof must invoke these *only* through the existing
      Reduction.lean wrappers),
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
      `eq15_implies_disk_le_annulus`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq5`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
    * `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`,
      `branch1SigmaKernel`, `branch1PointwiseFactor`,
      `branch2PointwiseFactor`, `liftGap`.

    (Note: `WangOuter.paperLambda` and
    `WangPaperSideConditions.paperLambda_pos` are EXEMPT and ARE
    needed — they are the named ingredients of the kernel and the
    annulus-side bound. `Section2Assumptions` is also EXEMPT — it is
    the input. `branch2SigmaKernel` is EXEMPT — it appears in
    sprint 016's bound shape.)

  * The new theorem's signature MUST take *exactly*: `(hc_pos : 0 < c)`,
    `(hc_lt_one : c < 1)`, and `(h_witness : ∀ {a b K} (paper : Section2Assumptions a b K c), ∃ ρ₁ ρ₂ : ℝ, …)`
    where the existential body is the conjunction listed in the Goal
    section. It MUST NOT take any standalone `IntervalIntegrable`
    premise outside the `h_witness` existential, and MUST NOT take a
    standalone `Summable` premise outside the `h_witness` existential.

* `ProofRefinement/Korenblum/Candidates/V17.lean`:

  * `-- @parent V16`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V16).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V16).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v17_branch2_window_reducer_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
                (c_value ^ 4 / 2) ≤ ∫ ρ' in ρ₁..ρ₂,
                                      2 * ρ' ^ 3 /
                                      WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_disk_eq6_annulus_eq8_eq9_branch2_window
        c_value_pos c_value_lt_one h_witness
    ```

  * Additionally, prove a structural witness lemma confirming the
    branch-2 sub-regime is non-vacuous at the seed by exhibiting
    a concrete `(ρ₁, ρ₂)`:

    ```lean
    theorem v17_branch2_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨5 / 10, 7 / 10, ?_, ?_, ?_⟩
      · -- branchSplit c_value ≈ 0.4103 < 0.5
        show PaperAxioms.branchSplit c_value < (5 / 10 : ℝ)
        unfold PaperAxioms.branchSplit
        have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
        have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
          Real.sqrt_nonneg _
        have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
          Real.sq_sqrt (le_of_lt h_pos)
        have hsqrt_lt : Real.sqrt (4 / 3) < (13 / 10 : ℝ) := by
          have h_sq_lt : (4 / 3 : ℝ) < ((13 / 10 : ℝ)) ^ 2 := by norm_num
          nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
        have hc : c_value = 3554 / 10000 := rfl
        rw [hc]
        nlinarith [hsqrt_lt, hsqrt_nonneg]
      · norm_num
      · norm_num
    ```

    The witness `(ρ₁, ρ₂) = (5/10, 7/10)` is identical to V14's
    window, enabling cross-reference. Any `(ρ₁, ρ₂)` with
    `branchSplit c_value < ρ₁ ≤ ρ₂ < 1` would suffice.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify the new reducer's
    signature typechecks at the seed `c_value` and to demonstrate
    the branch-2 window is non-vacuous.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V16.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_016`.

### Note on the `hSplit_gt_c` derivation

The fact `c < branchSplit c` is needed twice:
1. To derive `c < ρ₁` from `branchSplit c < ρ₁` (for the annulus-side
   call `annulusExcess_lower_bound_of_eq8_eq9` which takes `hcρ : c < ρ`).
2. To certify `0 < ρ₁` (for the disk-side collapse `branch2SigmaKernel
   c ρ₁ * ρ₁² = c⁴/2` which divides by `ρ₁²`).

The Generator may choose either:
* derive it inline with `nlinarith` (sketch above),
* OR factor it as a small private helper at the top of the proof,
* OR use existing Mathlib `Real.one_lt_sqrt` / `Real.sqrt_lt_one` /
  `Real.sqrt_lt'` if a more direct shape is available.

If `nlinarith` cannot close the `1 < √(4/3)` step cleanly, the fallback
is to use `Real.lt_sqrt` (one_lt iff version) to reduce
`1 < √(4/3)` to `1² < 4/3`, which is `norm_num`.

### Note on the `branch2SigmaKernel` collapse

`branch2SigmaKernel c ρ = c⁴ / (2 · ρ²)`, so
`branch2SigmaKernel c ρ * ρ² = c⁴ / (2 · ρ²) * ρ² = c⁴ / 2` provided
`ρ² ≠ 0`, i.e. `ρ ≠ 0`. The Generator must explicitly pass
`hρ₁_ne : ρ₁ ≠ 0` to `field_simp`. The `unfold; field_simp; ring`
pattern is well-tested at sprint 003's coefficient-collapse step
(`Reduction.lean:~440` area).

### Note on what `annulusExcess_lower_bound_of_eq8_eq9` requires

Sprint 006's signature requires (verified at `Reduction.lean:649`):
* `paper : Section2Assumptions a b K c`,
* `hc_pos : 0 < c`,
* `hcρ₁ : c < ρ₁`,
* `hρ₁₂ : ρ₁ ≤ ρ₂`,
* `hρ₂_lt_one : ρ₂ < 1`,
* `hIntCircle : IntervalIntegrable (fun ρ => 2 * ρ * circleGap a b ρ)
   volume c 1`,
* `hIntLambdaZ : IntervalIntegrable (fun ρ' => 2 * ρ' ^ 3 *
   sigmaZeroMinus a b ρ' / paperLambda K c ρ') volume ρ₁ ρ₂`.

Sprint 017's `h_witness` exposes all of these (after `hcρ₁` is derived
from `hSplit_lt_ρ₁` + `hSplit_gt_c`).

### Note on the additional `hIntLambda` premise

Sprint 014 carries `hIntLambda : IntervalIntegrable (fun ρ' => 2 * ρ'^3
/ paperLambda K c ρ') volume ρ₁ ρ₂` to allow the integration
`integral_mono_on_of_le_Ioo` step in `hStepC`. Sprint 017's
`h_witness` carries the same premise — it is needed for the same
step (`hStepC`).

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V17.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V17.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V17 scores `≥` V16 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V17.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_disk_eq6_annulus_eq8_eq9_branch2_window' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one use of `diskExcess_upper_bound_via_eq6`,
   * exactly one use of `annulusExcess_lower_bound_of_eq8_eq9`,
   * at least one use of `sigmaZeroMinus_monotone_of_summable`,
   * at least one use of `sigmaZeroMinus_summable_of_summable_at_upper`,
   * at least one use of `sigmaZeroMinus_nonneg_of_pos`,
   * no reference to `paper.eq2_`, `paper.eq3_`, `paper.eq4_`,
     `paper.eq5_`, `paper.eq7_`, `paper.eq10_`, `paper.eq11_`,
     `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
   * no direct invocation of `paper.eq6_branch2_sigmaReduction`,
     `paper.eq8_sigma_to_liftGap`, or
     `paper.eq9_liftGap_to_circleGap` (these must be reached only
     transitively through the named Reduction.lean wrappers),
   * no reference to any of the prior `valid_of_*` reducers
     (`valid_of_eq15`, `valid_of_eq12_eq13`,
     `valid_of_eq2_eq3_eq4_annulus_budget`,
     `valid_of_eq10_subinterval_branch1`,
     `valid_of_collapsed_disk_eq8_eq9_lower*`,
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`).
6. `grep -n 'v17_branch2_window_reducer_compiles\|v17_branch2_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V17.lean`
   returns at least two distinct matches.
7. The conclusion of `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`
   is exactly `ValidKorenblumBound c` (verify via `grep` of the
   theorem statement).
8. The `h_witness` existential body in
   `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` contains:
   * the constraint `PaperAxioms.branchSplit c < ρ₁` (verify via `grep`),
   * the constraint `c ^ 4 / 2 ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'` (verify via `grep` of the kernel inequality form),
   * **NO** `IntervalIntegrable (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c` premise (verify via `grep`: this premise must NOT appear in the new reducer's signature — the structural marker that the disk side has no integrability requirement).
9. The body of `v17_branch2_window_witness_at_seed` exhibits a
   concrete `(ρ₁, ρ₂)` with `ρ₁, ρ₂ ∈ ℝ` literals and
   `branchSplit c_value < ρ₁ ≤ ρ₂ < 1` (verify via `grep` of the
   theorem body for two numeric literals — `5 / 10`, `7 / 10`, or
   any other admissible pair).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V16.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no
  new import allowances).
* Building the Z-free version of sprint 017 (alternative A above —
  extracting `Z_{ρ₁}` from both sides via sprint 011 monotonicity).
  Queue as **sprint 018**, mirroring the sprint 013 → sprint 014
  evolution.
* Building the `eq11`-based branch-2 mirror of sprint 008
  (alternative B — flavour clone, demoted permanently).
* Building the combined `eq5 + eq6` full-annulus disk bound
  (alternative C — mechanical disjunction, not a new chain).
* Discharging the kernel inequality `c⁴/2 ≤ ∫ 2ρ³/Λ` numerically
  at the seed `c_value` — this requires a `paperLambda` envelope
  or a numerical oracle, both out of scope for this sprint.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the kernel inequality (out of scope above) or a
  qualitatively new analytical witness that closes the kernel from
  paper hypotheses alone.
* Any modification to sprint 016's `diskExcess_upper_bound_via_eq6`,
  sprint 006's `annulusExcess_lower_bound_of_eq8_eq9`, sprint 011's
  `sigmaZeroMinus_monotone_of_summable`, or sprint 012's
  `sigmaZeroMinus_summable_of_summable_at_upper` (these are
  consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against
  the current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 017 is
  purely structural.

## Time budget

≤ 35 minutes runtime. The new reducer is ~100 lines of Lean,
slightly smaller than sprint 014's ~140 lines (sprint 017 saves on
disk-side machinery). All tactics used are *already verified* in
sprints 006, 011, 012, 014, 016 at the cited line ranges.
The candidate side lemmas are 5–25 lines each (including the
witness at the seed). Total V17 size: ≤ 80 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `hSplit_gt_c : c < branchSplit c` derivation cannot be
  closed by `nlinarith` cleanly — fallback is to use
  `Real.one_lt_sq_iff_one_lt_abs` style chaining or
  `Real.lt_sqrt`. If that also fails, factor `hSplit_gt_c` as a
  `private lemma branchSplit_gt_self_of_pos : 0 < c → c < branchSplit c`
  immediately above the new theorem, with an explicit proof using
  `Real.sq_sqrt` + `nlinarith`.
* The `branch2SigmaKernel` collapse `unfold; field_simp; ring`
  fails — fallback is `unfold PaperAxioms.branch2SigmaKernel; rw
  [div_mul_eq_mul_div, mul_comm (c^4) (ρ₁^2), mul_div_assoc, ...]`
  with explicit step-by-step rewrites. Sprint 003 has a similar
  pattern at `Reduction.lean:~440`.
* The annulus-side call `annulusExcess_lower_bound_of_eq8_eq9`
  cannot be invoked due to a signature mismatch (e.g. argument
  order or implicit-vs-explicit difference) — verify the exact
  signature at `Reduction.lean:649` and adjust the call site
  accordingly.
* `intervalIntegral.integral_mono_on_of_le_Ioo` requires a specific
  argument order — verify against sprint 014's invocation at
  `Reduction.lean:1806`.
* The witness lemma `v17_branch2_window_witness_at_seed` may struggle
  if `nlinarith` cannot bound `Real.sqrt (4/3)` from above by `13/10`
  cleanly — fallback to the V14/V16 pattern (already verified
  feasible). Or pick a larger `ρ₁`, e.g. `6/10` or `7/10`, which
  satisfies `branchSplit c_value < ρ₁` more comfortably.
* Any of acceptance criteria 4, 5, 7, 8, 9 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5: `STATUS=BLOCKED` — that would defeat the
  "only `eq6` + `eq8` + `eq9` (via wrappers)" structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
