# Sprint 019: `(5)+(8)+(9)`-derived branch-1 sub-interval sufficient condition `valid_of_eq5_eq8_eq9_subinterval_branch1` — the workspace's **first closing reducer that re-derives Wang's pointwise `(10)` internally from `(5)+(8)+(9)` instead of consuming `paper.eq10_branch1_pointwise` directly**, the **first invocation of `KorenblumPaper.PaperAxioms.eq10_of_eq5_eq8_eq9` by any workspace theorem**, and the **first paper-internal cross-validation that the `(5)+(8)+(9)`-derivation chain and the printed `(10)` chain close the contract via the *same effective* sufficient condition** on the branch-1 sub-regime

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V18.lean`
**Target file**: `Candidates/V19.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_eq5_eq8_eq9_subinterval_branch1
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hIntDensity :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        IntervalIntegrable
          (AnnulusIntegralReduction.annulusDensity paper.circleGap)
          volume c 1)
    (h_window :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c
```

The signature is **identical** to sprint 008's `valid_of_eq10_subinterval_branch1`
(`Reduction.lean:833-851`). What changes is the **proof body**: instead of
invoking `paper.eq10_branch1_pointwise` directly to obtain the pointwise
inequality

```lean
PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
    * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
  PaperAxioms.circleGap a b ρ
```

(sprint 008 at `Reduction.lean:923-927`), sprint 019's body **re-derives** the
same inequality by invoking the already-proven theorem
`PaperAxioms.eq10_of_eq5_eq8_eq9` with the inputs
`paper.eq5_branch1_sigmaReduction`, `paper.eq8_sigma_to_liftGap`, and
`paper.eq9_liftGap_to_circleGap`:

```lean
have h10Derived :
    PaperAxioms.Eq10Branch1Pointwise K c
      (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (PaperAxioms.circleGap a b) :=
  PaperAxioms.eq10_of_eq5_eq8_eq9
    (K := K) (c := c)
    (innerExcess := PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
    (sigmaMinus := PaperAxioms.sigmaMinus a b)
    (liftGap := paper.liftGap)
    (circleGap := PaperAxioms.circleGap a b)
    hc_pos hSplit_lt_one
    paper.eq5_branch1_sigmaReduction
    paper.eq8_sigma_to_liftGap
    paper.eq9_liftGap_to_circleGap
have h10 :
    PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
        * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.circleGap a b ρ :=
  h10Derived hcρ hρ_split
```

After this single substitution, the rest of the proof body **is verbatim
sprint 008's body** (lines 928-1067 of `Reduction.lean`): the same
`mul_le_mul_of_nonneg_left h10 h2ρ_nonneg`, the same
`unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor;
field_simp; ring` collapse, the same `Ioo → Icc` lift, the same
`mass_mul_le_annulusSlice_of_integral_bound_ae`, the same annulus-side
splitting and slice non-negativities, the same final `calc`.

Then ship a `Candidates/V19.lean` at the same `c = 0.3554` that compiles,
scores `≥ V18`, and *materialises* the new lemma in side lemmas
`v19_eq5_eq8_eq9_subinterval_branch1_compiles` and
`v19_branch1_window_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so the
score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 019 is the natural and bounded next move on
three independent novelty axes that no prior workspace sprint touches:

1. **First workspace consumer of `KorenblumPaper.PaperAxioms.eq10_of_eq5_eq8_eq9`.**
   The trusted module `KorenblumPaper.PaperAxioms` exposes two derived
   theorems that have **never** been invoked by any workspace reducer:
   `eq10_of_eq5_eq8_eq9` (lines 391-440) and `eq11_of_eq6_eq8_eq9` (lines
   446-…). Both prove that the printed pointwise inequalities `(10)`/`(11)`
   are *redundant* in `Section2Assumptions`: they are derivable from
   `(5)+(8)+(9)` and `(6)+(8)+(9)` respectively. Sprint 019 is the **first
   workspace closing reducer that consumes one of these derived theorems**,
   re-deriving `(10)` inline from `(5)+(8)+(9)` rather than invoking the
   redundant `paper.eq10_branch1_pointwise` field. After sprint 019 the
   workspace will have **proof that the closing reducer can be expressed
   over the strictly smaller paper-hypothesis surface** `{(5),(7),(8),(9)}`
   on the branch-1 sub-regime, and `paper.eq10_branch1_pointwise` will no
   longer be a load-bearing hypothesis along this chain. This is a
   structural reduction in trust-surface obligation that no prior workspace
   sprint has demonstrated.

2. **First paper-internal cross-validation at the *closing-reducer level*
   that two structurally disjoint paper-equation paths converge on the
   same effective sufficient condition on the branch-1 sub-regime.** Sprint
   008's `valid_of_eq10_subinterval_branch1` consumes `paper.eq10_branch1_pointwise`
   directly: a single paper field. Sprint 019's `valid_of_eq5_eq8_eq9_subinterval_branch1`
   consumes `paper.eq5_branch1_sigmaReduction`,
   `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`: three
   different paper fields. Both reducers carry the **identical** mass
   premise `1 ≤ ∫_{ρ₁..ρ₂} scalarIntegrand1 c (paperLambda K c) ρ` over a
   sub-window `[ρ₁, ρ₂] ⊆ (c, branchSplit c]`. After sprint 019 the
   workspace has Lean proof that the **direct `(10)` chain** (sprint 008)
   and the **derived `(5)+(8)+(9)` chain** (sprint 019) close the
   `ValidKorenblumBound c` contract via *literally the same kernel
   inequality* on the *same* admissible sub-region. This mirrors the
   cross-validation theme already proven on different axes: sprint 015
   versus sprint 007 (`(5)`-direct disk bound vs `(2)+(3)+(4)`-derived disk
   bound, same algebraic form), sprint 018 versus sprint 017
   (`(7)+(11)`-direct closing vs `(6)+(8)+(9)+series`-derived closing,
   same kernel scalar `c⁴/2`). Sprint 019 plays the analogous role for
   sprint 008, completing the **branch-1** axis of the closing-reducer
   cross-validation matrix.

3. **First closing reducer that exposes `paper.liftGap` as an explicit
   sigma-to-circle bridge intermediary.** Every prior closing reducer either
   (a) bypasses the lift entirely (sprints 008/018 use `(10)`/`(11)`
   directly), (b) collapses through it via the convenience bridge
   `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (sprints 005/006/017), or
   (c) does not touch the sigma side at all (sprints 001/002/003/007/013).
   Sprint 019 is the first workspace closing reducer in which the explicit
   `paper.liftGap` intermediate quantity from
   `Eq8SigmaToLiftGap c (sigmaMinus a b) liftGap` and
   `Eq9LiftGapToCircleGap K c liftGap (PaperAxioms.circleGap a b)` is
   *threaded through the proof argument* via `eq10_of_eq5_eq8_eq9`. This
   exposes the `liftGap` field of `Section2Objects` as a load-bearing
   intermediate in a workspace closing reducer for the first time.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V19 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient condition
  for `ValidKorenblumBound c` that holds for *any* paper-faithful instance,
  parameterised by the witness window `(ρ₁, ρ₂)` and a single scalar mass
  premise on `scalarIntegrand1`.
* No concrete numerical tuple is committed beyond a one-line witness lemma
  confirming the branch-1 sub-regime is non-empty at the seed. Mirror
  sprint 008's V8 witness lemma `v8_split_lt_one_at_seed` (which already
  established `c_value < branchSplit c_value` and `branchSplit c_value < 1`
  at the seed `c_value = 0.3554`).

Why this is **not** "the same chain" as sprint 008:

* **Disjoint paper hypotheses consumed.** Sprint 008's body invokes
  `paper.eq10_branch1_pointwise` directly. Sprint 019's body invokes
  `paper.eq5_branch1_sigmaReduction`, `paper.eq8_sigma_to_liftGap`, and
  `paper.eq9_liftGap_to_circleGap` — and **must not** invoke
  `paper.eq10_branch1_pointwise`. Even though
  `paper.eq10_branch1_pointwise` is logically derivable from
  `paper.eq5_branch1_sigmaReduction + paper.eq8_sigma_to_liftGap +
  paper.eq9_liftGap_to_circleGap` via `eq10_of_eq5_eq8_eq9`, the two
  proofs go through **different fields of the `Section2Assumptions`
  structure**. After sprint 019 the workspace will demonstrably *not*
  require `paper.eq10_branch1_pointwise` along this chain — a structural
  reduction in load-bearing fields that sprint 008 cannot make.
* **Different intermediate quantities materialised.** Sprint 008's body
  goes directly from `paper.eq10_branch1_pointwise` to
  `branch1PointwiseFactor · diskExcess ≤ circleGap`. Sprint 019's body
  must materialise three intermediate facts: the `Σ⁻ ≤ kernel · diskExcess`
  step from `(5)`, the `Σ⁻ ≤ liftGap` step from `(8)`, and the
  `liftGap ≤ Λ · circleGap` step from `(9)`. The `liftGap` quantity
  appears explicitly in the proof; sprint 008's proof never mentions it.
* **Different `KorenblumPaper.PaperAxioms` theorems consumed.** Sprint 008
  consumes only `Eq10Branch1Pointwise` (definitionally, via
  `paper.eq10_branch1_pointwise`). Sprint 019 consumes
  `eq10_of_eq5_eq8_eq9` (a derived theorem), which transitively uses
  `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (another derived theorem).
  These two derived theorems have **never** been consumed by any workspace
  closing reducer; this is the first workspace sprint to materialise their
  call sites in `Reduction.lean`.

Why this is **not** "the same chain" as sprint 015:

* **Different output type.** Sprint 015 produces a *disk-side* bound:
  `diskExcess ≤ branch1SigmaKernel c ρ · ρ² · sigmaZeroMinus a b ρ`. It
  does **not** close the contract; it is a building block. Sprint 019
  produces a *closing reducer*: `ValidKorenblumBound c` is the conclusion.
  The two theorems live at different levels of the proof stack.
* **Different paper hypotheses consumed.** Sprint 015 consumes only
  `paper.eq5_branch1_sigmaReduction` plus the series identity
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. Sprint 019 consumes
  `paper.eq5_branch1_sigmaReduction`, `paper.eq7_paperK_formula` (via
  the integrability hook), `paper.eq8_sigma_to_liftGap`,
  `paper.eq9_liftGap_to_circleGap`. The chains overlap on `(5)` only.
* **Different machinery.** Sprint 015 has no integrability premises, no
  windowed mass condition, no annulus-density splitting. Sprint 019 has
  all of these (it is a *closing* reducer).

Why this is **not** "the same chain" as sprint 017:

* **Different branch.** Sprint 017 closes on the **branch-2 sub-regime**
  `(branchSplit c, 1)`. Sprint 019 closes on the **branch-1 sub-regime**
  `(c, branchSplit c]`. The two admissibility predicates are mutually
  disjoint (modulo the boundary point `ρ = branchSplit c`).
* **Different annulus-side machinery.** Sprint 017 produces a windowed
  annulus *lower* bound via the `(8)+(9)`-chain on the annulus side
  (`annulusExcess_lower_bound_of_eq8_eq9`). Sprint 019 uses
  `mass_mul_le_annulusSlice_of_integral_bound_ae` to produce a windowed
  annulus *slice upper* bound on `diskExcess` instead. **Different
  annulus-side architecture.**
* **`(8)+(9)` is consumed in opposite roles.** In sprint 017, `(8)+(9)`
  bridges from `Σ⁻` to `circleGap` on the **annulus side** (transferring
  `sigmaZeroMinus ρ` to `circleGap ρ`). In sprint 019, `(8)+(9)` is
  combined with `(5)` to derive `(10)` on the **disk side** (transferring
  the `(5)` lower bound on `Σ⁻` into a pointwise upper bound on
  `branch1PointwiseFactor · diskExcess`). The role of the `(8)+(9)`
  bridge is structurally different.

Why this is **bounded enough for one Generator session**:

* The proof body is a **mechanical extension** of sprint 008's body at
  `Reduction.lean:833-1067` — only the pointwise step (lines 922-927) is
  replaced; the rest is verbatim. Estimate: ≤ 250 lines of Lean for the
  new theorem, dominated by the verbatim sprint-008 mass-side machinery.
* No new Mathlib lemmas needed. Every Lean idiom used is already verified
  at the cited line ranges in sprint 008
  (`mass_mul_le_annulusSlice_of_integral_bound_ae`,
  `paperScalarIntegrand1_intervalIntegrable`, `annulusSlice_add_adjacent`,
  `annulusSlice_nonneg_of_ae`, `annulusDensity_nonneg_of_lt`,
  `paperLambda_pos`, `Measure.restrict_congr_set`, `Ioo_ae_eq_Icc`,
  `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`,
  `mul_le_mul_of_nonneg_left`, `mono_set`, `calc`).
* The only genuinely new step is one call to
  `PaperAxioms.eq10_of_eq5_eq8_eq9` with five named arguments — this is
  fully verified at `KorenblumPaper/PaperAxioms.lean:391-440` and has a
  documented signature. The transitive `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`
  call is internal to `eq10_of_eq5_eq8_eq9`'s body and need not be
  invoked separately.
* The candidate side lemmas are 5–25 lines each (matching sprint 008/018's
  patterns). Total V19 size: ≤ 80 lines.

Why this beats the alternatives I considered:

* **A: Z-free version of sprint 017** (extract `Z_{ρ₁}` from both sides
  via sprint 011 monotonicity, leaving the kernel
  `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` literally Z-free). Sprint 018's
  contract explicitly demoted this as a *refactor* with low analytical
  novelty per Generator session — "it does not derive a new sufficient
  condition, just rewrites sprint 017's existing condition with `Z_{ρ₁}`
  extracted via the same `mul_le_mul_of_nonneg_right +
  intervalIntegral.integral_mul_const` pattern already exercised in
  sprint 010 and sprint 014". The bulletin's current priority continues
  to de-prioritize "more-of-the-same" chain extensions. **Demoted as
  refactor — high-bandwidth but low-novelty.**

* **B: Branch-2 mirror — `valid_of_eq6_eq8_eq9_subinterval_branch2`**
  via `PaperAxioms.eq11_of_eq6_eq8_eq9`. This is sprint 019's natural
  branch-2 mirror. However, sprint 018 just shipped the branch-2 short
  chain (`(7)+(11)`-direct), and choosing branch-2 here would be
  immediately mirroring the just-shipped sprint 018. The branch-1
  variant (this sprint) has not been mirrored yet — sprint 008 was 11
  sprints ago — so it strictly increases the workspace's coverage
  diversity. **Demoted: queue separately as sprint 020 if the next
  planner judges branch-2 derived-pointwise valuable.**

* **C: A *unified* closing reducer that derives both `(10)` and `(11)`
  from `(5)+(6)+(8)+(9)` and dispatches by branch.** Mechanical
  disjunction (similar to alternative C demoted in sprints 017/018);
  exposes no new analytical chain through `Section2Assumptions`.
  **Demoted as glue.**

* **D: Combined `eq5 + eq6` full-annulus disk bound.** Demoted in
  sprints 017/018 as glue. **Still demoted.**

* **E: New series-level continuity / left-edge limit lemmas for
  `s ↦ sigmaZeroMinus a b s`.** Demoted in sprints 016/017/018 as
  speculative, no concrete consumer queued. **Still demoted.**

* **F: `paperLambda` upper-envelope from `paper.eq7_paperK_formula`
  alone.** Speculative — `paperLambda` is defined in
  `KorenblumPaper.OneModePaperBridge` via Wang's complicated
  `M(c, ρ)` formula, and no closed-form upper envelope is exposed.
  Investigating the `OneModePaperBridge` interior is beyond a single
  Generator session. **Demoted: requires structural exploration before
  it can be queued as a contract.**

* **G: Numerical-oracle registration discharging the kernel
  `c⁴/2 ≤ ∫ 2ρ³/Λ` at the seed.** Demoted in sprint 018 — needs a
  specific sub-window and closed-form `Λ`-bound shape, neither
  currently established. **Still demoted.**

* **H: A pure-`eq2` disk-side reducer.** Sprint 018's contract demoted
  this as wrong sign (`eq2` is a *lower* bound on `Z(r)`, not an upper
  bound on `circleGap r`). **Still demoted.**

* **I: A second `eq11`-based reducer using `eq11` plus a windowed
  `eq2`-style lower bound on `Z`.** Sprint 018's contract demoted as
  speculative. **Still demoted.**

* **J: Cross-validation theorem `branch1SigmaKernel c ρ · ρ² ·
  sigmaZeroMinus a b ρ ≤ (sprint 003's collapsed RHS expression)`** —
  shipping a Lean theorem that proves sprint 015's branch-1 disk bound
  and sprint 007's `(2)+(3)+(4)`-based collapsed bound on `(c,
  √(4/3)c]` are *literally equal*. Narrow (a single algebraic
  identity), no closing reducer involved, doesn't increase the
  workspace's closing-reducer coverage. **Demoted: too narrow.**

Compared to A–J, candidate K (this sprint,
`valid_of_eq5_eq8_eq9_subinterval_branch1`) maximises analytical novelty
per bounded Generator session: it ships the **first workspace consumer of
`PaperAxioms.eq10_of_eq5_eq8_eq9`**, the **first closing reducer that
re-derives Wang's pointwise `(10)` inline from `(5)+(8)+(9)`**, the **first
paper-internal closing-reducer-level cross-validation that the direct
`(10)` chain (sprint 008) and the derived `(5)+(8)+(9)` chain converge on
the same kernel inequality on the same admissible sub-region**, and the
**first workspace closing reducer in which `paper.liftGap` is materialised
as a load-bearing intermediate**. It uses **only existing trusted modules
+ pinned Mathlib + already-verified `Reduction.lean` lemmas** in patterns
directly mirrored from sprint 008. No proposal needed.

### Note on the `eq10_of_eq5_eq8_eq9` invocation

The signature at `KorenblumPaper/PaperAxioms.lean:391-400` is:

```lean
theorem eq10_of_eq5_eq8_eq9
    {K : ℝ → ℝ → ℝ}
    {c innerExcess : ℝ}
    {sigmaMinus liftGap circleGap : ℝ → ℝ}
    (hc : 0 < c)
    (hsplit1 : branchSplit c < 1)
    (h5 : Eq5Branch1SigmaReduction c innerExcess sigmaMinus)
    (h8 : Eq8SigmaToLiftGap c sigmaMinus liftGap)
    (h9 : Eq9LiftGapToCircleGap K c liftGap circleGap) :
    Eq10Branch1Pointwise K c innerExcess circleGap
```

The natural call site in sprint 019's body, immediately after the geometric
scaffolding, is:

```lean
have hSplit_lt_one' : PaperAxioms.branchSplit c < 1 := hSplit_lt_one
have h10Derived :
    PaperAxioms.Eq10Branch1Pointwise K c
      (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
      (PaperAxioms.circleGap a b) :=
  PaperAxioms.eq10_of_eq5_eq8_eq9
    (sigmaMinus := PaperAxioms.sigmaMinus a b)
    (liftGap := paper.liftGap)
    hc_pos hSplit_lt_one'
    paper.eq5_branch1_sigmaReduction
    paper.eq8_sigma_to_liftGap
    paper.eq9_liftGap_to_circleGap
```

Then inside the pointwise loop body (mirroring sprint 008
`Reduction.lean:913-955`), replace the line

```lean
have h10 : … := paper.eq10_branch1_pointwise hcρ hρ_split
```

with

```lean
have h10 : … := h10Derived hcρ hρ_split
```

The named field `paper.liftGap` is the `Section2Objects.liftGap` field
inherited via `extends Section2Objects a b K c` in the
`Section2Assumptions` structure (`KorenblumPaper/PaperAxioms.lean:309-313`).
It is exposed as `paper.liftGap : ℝ → ℝ` directly.

### Note on the `circleGap`-side argument vs. the `paper.circleGap` projection

Sprint 008's body uses both `PaperAxioms.circleGap a b` (the explicit
function) and `paper.circleGap` (the `Section2Objects.circleGap`
projection); they are definitionally equal via `Section2Objects.circleGap`
(`KorenblumPaper/PaperAxioms.lean:294-299`). When invoking
`eq10_of_eq5_eq8_eq9`, pass the explicit `PaperAxioms.circleGap a b` as
the `circleGap` named argument so the conclusion type
`Eq10Branch1Pointwise K c (diskExcess (PaperAxioms.circleGap a b) c)
(PaperAxioms.circleGap a b)` matches `paper.eq10_branch1_pointwise`'s
implicit instantiation in `Section2Assumptions`. The `paper.circleGap`
projection should be reserved for the annulus-density side (where sprint
008 already uses it consistently).

### Note on the witness window at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value ≈ 0.4103 > c_value`.
* Any `ρ₁, ρ₂` with `c_value < ρ₁ ≤ ρ₂ ≤ branchSplit c_value` is
  admissible.
* Natural witness choice: `(ρ₁, ρ₂) = (4/10, 41/100)`. The lower bound
  needs `0.3554 < 0.4`, which is `norm_num`. The upper bound needs
  `0.41 ≤ branchSplit c_value = 0.3554 · √(4/3)`. We have `√(4/3) >
  1.154` (since `1.154² = 1.331716 < 4/3 ≈ 1.3333`), so `branchSplit
  c_value > 0.3554 · 1.154 = 0.41013…`, but `0.41 < 0.41013…`. The
  fallback is to set `ρ₁ = ρ₂ = 4/10` (single-point window) which
  trivially satisfies `c_value < ρ₁ ≤ ρ₂ ≤ branchSplit c_value`
  *provided* one proves `ρ₁ ≤ branchSplit c_value`, i.e., `0.4 ≤
  branchSplit 0.3554`. This requires bounding `√(4/3)` from *below*
  by `1.126…` since `0.4 / 0.3554 ≈ 1.1255`. The cleanest approach:
  bound `√(4/3) ≥ 1.13` via `1.13² = 1.2769 < 4/3` and `nlinarith`;
  then `branchSplit c_value ≥ 0.3554 · 1.13 = 0.40160 > 0.4`. The
  witness lemma's body should mirror sprint 008's V8 witness lemma
  `v8_split_lt_one_at_seed` (verified-working) for the
  `branchSplit c_value < 1` direction, and add a symmetric
  `branchSplit c_value > c_value` direction via `√(4/3) > 1`.

If the planner judges this numerical bound risky to derive cleanly via
`nlinarith` in 5 minutes of generator effort, the *fallback witness* is
the **degenerate single-point window** `ρ₁ = ρ₂ = branchSplit c_value`
itself: trivially `c_value < branchSplit c_value` (already in V8's
witness as a side fact) and `branchSplit c_value ≤ branchSplit c_value`
(by `le_refl`). This avoids the lower-bound derivation entirely, and the
window `(branchSplit c_value, branchSplit c_value)` is admissible per
the contract (`c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ branchSplit c`).

### Note on what the witness lemma should NOT do

Sprint 019's V19 witness lemma is **structural only** — it confirms that
the admissible-window predicate `c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤
branchSplit c_value` is non-vacuous at the seed by exhibiting concrete
`ρ₁, ρ₂`. It **does NOT discharge any of the integrability premises, nor
the mass premise `1 ≤ ∫ scalarIntegrand1`**. Those remain as existential
hypotheses on the new reducer, just like V8/V14/V17/V18's witnesses do not
discharge their respective sprints' premises.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_eq5_eq8_eq9_subinterval_branch1` matching the shape above.
    The proof body must:

    1. **Open `valid_of` framework.** `refine ⟨hc_pos, hc_lt_one, ?_⟩;
       intro a b K paper; obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_split,
       hMass⟩ := h_window paper`.

    2. **Geometric scaffolding.** Verbatim from sprint 008 body
       (`Reduction.lean:856-864`): derive `hSplit_le_one`, `hρ₂_lt_one`,
       `hρ₂_le_one`, `hcρ₂`, `hc_le_ρ₁`, `hc_le_ρ₂`, `hρ₁_lt_one`,
       `hc_le_one`.

    3. **Derive `(10)` from `(5)+(8)+(9)` via
       `PaperAxioms.eq10_of_eq5_eq8_eq9`.** This is the **single new
       step** (relative to sprint 008):

       ```lean
       have h10Derived :
           PaperAxioms.Eq10Branch1Pointwise K c
             (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
             (PaperAxioms.circleGap a b) :=
         PaperAxioms.eq10_of_eq5_eq8_eq9
           (sigmaMinus := PaperAxioms.sigmaMinus a b)
           (liftGap := paper.liftGap)
           hc_pos hSplit_lt_one
           paper.eq5_branch1_sigmaReduction
           paper.eq8_sigma_to_liftGap
           paper.eq9_liftGap_to_circleGap
       ```

    4. **Global annulus-density integrability.** Verbatim from sprint
       008 (`Reduction.lean:866-869`).

    5. **Sub-interval integrability of `annulusDensity` via `mono_set`.**
       Verbatim from sprint 008 (`Reduction.lean:871-902`).

    6. **Sub-interval integrability of `scalarIntegrand1` via the paper
       hook.** Verbatim from sprint 008 (`Reduction.lean:903-910`).

    7. **Pointwise bound on `Ioo ρ₁ ρ₂`.** Verbatim from sprint 008
       (`Reduction.lean:912-955`), with the **single substitution**:

       ```lean
       have h10 :
           PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
               * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             PaperAxioms.circleGap a b ρ :=
         h10Derived hcρ hρ_split
       ```

       (replacing sprint 008's
       `paper.eq10_branch1_pointwise hcρ hρ_split` at line 927).

    8. **`Ioo → Icc` lift.** Verbatim from sprint 008
       (`Reduction.lean:957-985`).

    9. **`mass_mul_le_annulusSlice_of_integral_bound_ae`.** Verbatim
       from sprint 008 (`Reduction.lean:986-998`).

    10. **Annulus-side splitting and slice non-negativities.** Verbatim
        from sprint 008 (`Reduction.lean:1004-1052`).

    11. **Final calc chain.** Verbatim from sprint 008
        (`Reduction.lean:1054-1066`).

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 019's
    `valid_of_eq5_eq8_eq9_subinterval_branch1` is the workspace's
    **first closing reducer that re-derives Wang's pointwise `(10)`
    internally from `(5)+(8)+(9)` instead of consuming
    `paper.eq10_branch1_pointwise` directly**, the **first invocation of
    `KorenblumPaper.PaperAxioms.eq10_of_eq5_eq8_eq9` by any workspace
    theorem**, and a paper-internal cross-validation that the direct
    `(10)` chain (sprint 008) and the derived `(5)+(8)+(9)` chain close
    the contract via the same effective sufficient condition on the
    branch-1 sub-regime. After this sprint, the workspace has Lean
    proof that `paper.eq10_branch1_pointwise` is a redundant field of
    `Section2Assumptions` along this closing chain.

  * The body of `valid_of_eq5_eq8_eq9_subinterval_branch1` MAY invoke:

    * `PaperAxioms.eq10_of_eq5_eq8_eq9` (the unique direct-derivation
      consumption — this is the **whole point** of the sprint),
    * `paper.eq5_branch1_sigmaReduction`,
      `paper.eq8_sigma_to_liftGap`,
      `paper.eq9_liftGap_to_circleGap`,
      `paper.eq7_paperK_formula` (via the integrability hook),
    * `paper.liftGap` (via the `Section2Objects` projection inherited
      through `extends`),
    * `paper.circleGap` (annulus-density side, matching sprint 008),
    * `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
    * `WangPaperSideConditions.paperLambda_pos`,
    * `AnnulusIntegralReduction.annulusDensity`,
    * `AnnulusIntegralReduction.annulusSlice`,
    * `AnnulusIntegralReduction.annulusSlice_add_adjacent`,
    * `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae`,
    * `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`,
    * `annulusDensity_nonneg_of_lt` (defined locally in
      `Reduction.lean` and used by sprint 008 — re-used verbatim),
    * `PaperAxioms.branch1PointwiseFactor`, `PaperAxioms.branchSplit`,
      `Korenblum.scalarIntegrand1` (definitional unfolding),
    * `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `IntervalIntegrable.mono_set`, `Measure.restrict_congr_set`,
      `Ioo_ae_eq_Icc`, `ae_restrict_iff' measurableSet_Ioo`,
      `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`,
      `calc`, `change`, `unfold`, `rw`, `simpa`,
      `Filter.Eventually.of_forall`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that the new reducer
    reaches closure through the **derived `(5)+(8)+(9)` chain only**,
    not via the direct `(10)` field):

    * `paper.eq10_branch1_pointwise` (this is the **whole point** of
      the sprint — the reducer must use only `(5)+(8)+(9)` and the
      derived theorem `eq10_of_eq5_eq8_eq9`, never the direct field
      `eq10_branch1_pointwise`),
    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq6_`,
      `paper.eq11_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_`,
      `paper.eq15_` (only `(5)+(7)+(8)+(9)` of the paper hypotheses
      are admitted along this chain),
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
      `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`,
      `valid_of_eq11_subinterval_branch2` (no upstream closing
      reducer — sprint 019 must close on its own from
      `(5)+(7)+(8)+(9)`),
    * `eq15_implies_disk_le_annulus`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_via_eq3_eq4`,
      `diskExcess_upper_bound_via_eq5`,
      `diskExcess_upper_bound_via_eq6`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `annulusExcess_lower_bound_of_eq8_eq9`,
      `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
      `sigmaZeroMinus_nonneg_of_pos`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`
      (these are markers of the `(2)+(3)+(4)` chain or the
      series-level chain — both unrelated to the `(5)+(8)+(9)` chain
      sprint 019 establishes).

    (Note: `WangOuter.paperLambda` and
    `WangPaperSideConditions.paperLambda_pos` are EXEMPT and ARE
    needed — they are named ingredients of `scalarIntegrand1` and the
    integrand non-negativity proofs. `Section2Assumptions` is EXEMPT
    — it is the input. `branch1PointwiseFactor` and `scalarIntegrand1`
    are EXEMPT — they appear in the derived `(10)`'s shape and in the
    windowed mass premise respectively.
    `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` is EXEMPT (it is invoked
    transitively *inside* `eq10_of_eq5_eq8_eq9`'s body but not by the
    sprint-019 body directly).)

  * The new theorem's signature MUST take *exactly*: `(hc_pos : 0 < c)`,
    `(hc_lt_one : c < 1)`, `(hSplit_lt_one : PaperAxioms.branchSplit c <
    1)`, `(hIntDensity : ∀ {a b K} (paper : Section2Assumptions a b K
    c), IntervalIntegrable (annulusDensity paper.circleGap) volume c
    1)`, and `(h_window : ∀ {a b K} (paper : Section2Assumptions a b K
    c), ∃ ρ₁ ρ₂ : ℝ, c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ branchSplit c ∧ 1 ≤
    ∫ ρ in ρ₁..ρ₂, scalarIntegrand1 c (paperLambda K c) ρ)`. (This
    signature is **identical** to sprint 008's
    `valid_of_eq10_subinterval_branch1` — the entire structural novelty
    is in the proof body, not in the statement.)

* `ProofRefinement/Korenblum/Candidates/V19.lean`:

  * `-- @parent V18`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V18).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V18).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v19_eq5_eq8_eq9_subinterval_branch1_compiles
        (hSplit_lt_one : PaperAxioms.branchSplit c_value < 1)
        (hIntDensity :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            IntervalIntegrable
              (AnnulusIntegralReduction.annulusDensity paper.circleGap)
              volume c_value 1)
        (h_window :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value ∧
                (1 : ℝ) ≤
                  ∫ ρ in ρ₁..ρ₂,
                    Korenblum.scalarIntegrand1 c_value
                      (WangOuter.paperLambda K c_value) ρ) :
        ValidKorenblumBound c_value :=
      valid_of_eq5_eq8_eq9_subinterval_branch1
        c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window
    ```

  * Additionally, prove a structural witness lemma confirming the
    branch-1 sub-regime is non-vacuous at the seed by exhibiting
    a concrete `(ρ₁, ρ₂)`:

    ```lean
    theorem v19_branch1_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ ≤ PaperAxioms.branchSplit c_value := by
      -- Degenerate single-point window at branchSplit c_value itself.
      refine ⟨PaperAxioms.branchSplit c_value, PaperAxioms.branchSplit c_value, ?_, le_rfl, le_rfl⟩
      show c_value < PaperAxioms.branchSplit c_value
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
    ```

    The degenerate single-point window `ρ₁ = ρ₂ = branchSplit c_value`
    sidesteps any numerical-bound risk on `√(4/3)` from below.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify the new reducer's
    signature typechecks at the seed `c_value` and to demonstrate the
    branch-1 window is non-vacuous.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V18.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_018`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V19.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V19.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V19 scores `≥` V18 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V19.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_eq5_eq8_eq9_subinterval_branch1' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of
     `PaperAxioms.eq10_of_eq5_eq8_eq9`,
   * exactly one invocation of `paper.eq5_branch1_sigmaReduction`,
   * exactly one invocation of `paper.eq8_sigma_to_liftGap`,
   * exactly one invocation of `paper.eq9_liftGap_to_circleGap`,
   * at least one invocation of `paper.liftGap`,
   * exactly one invocation of `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
   * at least one invocation of `mass_mul_le_annulusSlice_of_integral_bound_ae`,
   * **zero** direct references to `paper.eq10_branch1_pointwise` (this
     is the structural marker that the reducer reaches closure
     **without** consuming the redundant printed `(10)` field),
   * no direct reference to `paper.eq2_`, `paper.eq3_`, `paper.eq4_`,
     `paper.eq6_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
     `paper.eq14_`, `paper.eq15_`,
   * no reference to any of the prior `valid_of_*` reducers
     (`valid_of_eq15`, `valid_of_eq12_eq13`,
     `valid_of_eq2_eq3_eq4_annulus_budget`,
     `valid_of_eq10_subinterval_branch1`,
     `valid_of_collapsed_disk_eq8_eq9_lower*`,
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
     `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`,
     `valid_of_eq11_subinterval_branch2`),
   * no reference to `sigmaZeroMinus_*`, `sigmaMinus_*`,
     `circleGap_inner_bound_*`, `circleGap_outer_lower_bound_*`,
     `diskExcess_upper_bound_*`, `annulusExcess_lower_bound_*`.
6. `grep -n 'v19_eq5_eq8_eq9_subinterval_branch1_compiles\|v19_branch1_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V19.lean`
   returns at least two distinct matches.
7. The conclusion of `valid_of_eq5_eq8_eq9_subinterval_branch1` is
   exactly `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_window` existential body in
   `valid_of_eq5_eq8_eq9_subinterval_branch1` contains:
   * the constraint `c < ρ₁` (verify via `grep`),
   * the constraint `ρ₂ ≤ PaperAxioms.branchSplit c` (verify via `grep`),
   * the constraint `(1 : ℝ) ≤ ∫ ρ in ρ₁..ρ₂, Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ`
     (verify via `grep` of the mass inequality form).
9. The body of `v19_branch1_window_witness_at_seed` exhibits a
   concrete `(ρ₁, ρ₂)` with `c_value < ρ₁ ≤ ρ₂ ≤ branchSplit c_value`
   (verify via `grep` of the theorem body for at least one occurrence
   of `PaperAxioms.branchSplit` or a numeric literal pair lying in the
   admissible band).
10. The new theorem's signature MUST be **statement-identical** to
    sprint 008's `valid_of_eq10_subinterval_branch1` modulo the theorem
    name. Verify by grepping both signatures and confirming the only
    text difference (modulo whitespace) is the theorem name itself.
    The structural novelty must be **entirely in the proof body**.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V18.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the branch-2 mirror via `eq11_of_eq6_eq8_eq9` (alternative
  B above — queue separately as **sprint 020** if the next planner
  judges branch-2 derived-pointwise valuable).
* Building a *unified* closing reducer that derives both `(10)` and
  `(11)` from `(5)+(6)+(8)+(9)` and dispatches by branch (alternative
  C — mechanical disjunction, not a new chain).
* Building the Z-free version of sprint 017 (alternative A above —
  refactor with low novelty).
* Discharging the mass inequality `1 ≤ ∫ scalarIntegrand1`
  numerically at the seed `c_value` — this requires a `paperLambda`
  envelope or a numerical oracle, both out of scope for this sprint.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the mass inequality (out of scope above) or a
  qualitatively new analytical witness that closes the mass inequality
  from paper hypotheses alone.
* Any modification to sprint 008's `valid_of_eq10_subinterval_branch1`,
  sprint 015's `diskExcess_upper_bound_via_eq5`, sprint 017's
  `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`, sprint 018's
  `valid_of_eq11_subinterval_branch2`, or the locally-defined helpers
  `annulusDensity_nonneg_of_lt`, `annulusSlice_nonneg_of_ae`,
  `annulusSlice_add_adjacent` (these are consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 019 is purely
  structural.
* *Dropping* `eq10_branch1_pointwise` from `Section2Assumptions`. Even
  though sprint 019 demonstrates that `eq10_branch1_pointwise` is
  *redundant* along this chain, removing the field would break sprint
  008's `valid_of_eq10_subinterval_branch1` and any V8/V14 candidate
  that exercises it. Field removal is a structural change requiring
  a separate proposal — not part of this sprint.

## Time budget

≤ 35 minutes runtime. The new reducer is ~250 lines of Lean,
matching sprint 008's ~234 lines line-for-line with a single ~10-line
new derivation block (`h10Derived`) inserted between the geometric
scaffolding and the pointwise loop body. All tactics used are *already
verified* in sprint 008 at `Reduction.lean:833-1067`. The
`PaperAxioms.eq10_of_eq5_eq8_eq9` invocation is verified at
`KorenblumPaper/PaperAxioms.lean:391-440` and has a documented signature.
The candidate side lemmas are 5–25 lines each (including the witness
at the seed). Total V19 size: ≤ 80 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `eq10_of_eq5_eq8_eq9` call fails to type-check due to argument
  inference issues — fall back to passing all explicit arguments by
  name (`{K := K}`, `{c := c}`, `{innerExcess := …}`,
  `{sigmaMinus := PaperAxioms.sigmaMinus a b}`, `{liftGap :=
  paper.liftGap}`, `{circleGap := PaperAxioms.circleGap a b}`).
* The `paper.liftGap` projection cannot be resolved (e.g. namespace
  issue) — try `paper.toSection2Objects.liftGap` as the explicit form
  (per `extends Section2Objects a b K c` at
  `KorenblumPaper/PaperAxioms.lean:309-313`).
* The substitution at the pointwise step (replacing
  `paper.eq10_branch1_pointwise hcρ hρ_split` with `h10Derived hcρ
  hρ_split`) fails to unify — verify that `h10Derived`'s type matches
  `Eq10Branch1Pointwise K c (diskExcess (PaperAxioms.circleGap a b)
  c) (PaperAxioms.circleGap a b)` exactly. The term
  `Eq10Branch1Pointwise K c innerExcess circleGap` unfolds to
  `∀ ⦃ρ : ℝ⦄, c < ρ → ρ < branchSplit c → branch1PointwiseFactor c
  (paperLambda K c) ρ * innerExcess ≤ circleGap ρ`. If unification
  fails, add an explicit `change` step or invoke
  `simpa [PaperAxioms.Eq10Branch1Pointwise] using …`.
* The witness lemma `v19_branch1_window_witness_at_seed`'s
  `nlinarith` step for `c_value < branchSplit c_value` cannot close
  cleanly — fallback is to use the verbatim `hsplit : c <
  branchSplit c` block from sprint 017's body at
  `Reduction.lean:1963-1972` (already verified working in V17).
* Any of acceptance criteria 4, 5, 7, 8, 9, 10 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially
  `paper.eq10_branch1_pointwise`): `STATUS=BLOCKED` — that would
  defeat the "derived `(10)` via `(5)+(8)+(9)` only" structural
  guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
