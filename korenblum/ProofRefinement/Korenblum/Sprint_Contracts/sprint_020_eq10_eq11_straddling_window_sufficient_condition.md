# Sprint 020: Straddling-window `(10)+(11)` sufficient condition `valid_of_eq10_eq11_straddling_window` — the workspace's **first closing reducer whose admissible window crosses `branchSplit c` interior to itself**, the **first reducer whose mass premise is a sum of two integrals over disjoint sub-intervals (one branch-1, one branch-2)**, and the **first reducer to close the contract via simultaneous use of the two printed pointwise inequalities `(10)` and `(11)`**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V19.lean`
**Target file**: `Candidates/V20.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_eq10_eq11_straddling_window
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
          c < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c ∧
            PaperAxioms.branchSplit c ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              (∫ ρ in ρ₁..PaperAxioms.branchSplit c,
                Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) +
              (∫ ρ in PaperAxioms.branchSplit c..ρ₂,
                Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)) :
    ValidKorenblumBound c
```

The admissible window `[ρ₁, ρ₂]` is a **straddling sub-interval**: `c < ρ₁ ≤
branchSplit c ≤ ρ₂ < 1`. The mass premise is the **sum of two integrals**:
`scalarIntegrand1` over the branch-1 piece `[ρ₁, branchSplit c]` plus
`scalarIntegrand2` over the branch-2 piece `[branchSplit c, ρ₂]`. This is the
*first* workspace reducer whose admissibility predicate is non-vacuous on
straddling windows (e.g. `(0.4, 0.5)` at the seed crosses `branchSplit 0.3554
≈ 0.4103`) — every prior branch-1 reducer requires `ρ₂ ≤ branchSplit c` and
every prior branch-2 reducer requires `ρ₁ ≥ branchSplit c`.

The proof body fuses sprint 008's branch-1 machinery and sprint 018's branch-2
machinery into a single argument:

1. **Pointwise bounds on the two open sub-intervals.** On `Ioo ρ₁ (branchSplit
   c)` apply `paper.eq10_branch1_pointwise` and the algebraic collapse
   `2ρ · branch1PointwiseFactor · D = scalarIntegrand1 · D`. On
   `Ioo (branchSplit c) ρ₂` apply `paper.eq11_branch2_pointwise` and the
   sprint-018 collapse `2ρ · branch2PointwiseFactor · D = scalarIntegrand2 · D`.

2. **Two parallel applications of
   `mass_mul_le_annulusSlice_of_integral_bound_ae`.** Define
   `M₁ := ∫ ρ in ρ₁..branchSplit c, scalarIntegrand1 …` and
   `M₂ := ∫ ρ in branchSplit c..ρ₂, scalarIntegrand2 …`. Apply
   `mass_mul_le_annulusSlice_of_integral_bound_ae` once with mass `M₁` to get
   `M₁ · diskExcess ≤ annulusSlice paper.circleGap ρ₁ (branchSplit c)`, and
   once with mass `M₂` to get
   `M₂ · diskExcess ≤ annulusSlice paper.circleGap (branchSplit c) ρ₂`.

3. **Add the two inequalities and use `M₁ + M₂ ≥ 1`** (the mass premise) to
   conclude
   `diskExcess ≤ annulusSlice ρ₁ (branchSplit c) + annulusSlice (branchSplit c) ρ₂`.
   The annulus-slice sum equals `annulusSlice ρ₁ ρ₂` by
   `annulusSlice_add_adjacent` (already proven in `Reduction.lean` and used
   verbatim by sprints 008/018).

4. **Dominate by the full annulus excess.** Split
   `annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1`
   via two adjacency applications, discharge the side-slice non-negativities
   via `annulusSlice_nonneg_of_ae` (verbatim from sprint 008's body
   `Reduction.lean:1019-1052`).

5. **Final `calc`.** `diskExcess ≤ annulusSlice ρ₁ ρ₂ ≤ annulusSlice c 1 =
   annulusExcess … c`. Definitionally close.

Then ship a `Candidates/V20.lean` at the same `c = 0.3554` that compiles,
scores `≥ V19`, and *materialises* the new lemma in side lemmas
`v20_eq10_eq11_straddling_window_compiles` and
`v20_straddling_window_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so the
score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 020 is the natural next move on three
independent novelty axes that no prior workspace sprint touches:

1. **First closing reducer with a straddling-window admissibility
   predicate.** Every prior workspace closing reducer that takes a free
   sub-window — sprints 008, 014, 017, 018, 019, plus the
   collapsed-disk reducers from sprints 009–012 — confines the window to
   *one side* of `branchSplit c`. Sprint 008/019 require `c < ρ₁ ≤ ρ₂ ≤
   branchSplit c`; sprint 017/018 require `branchSplit c ≤ ρ₁ ≤ ρ₂ < 1`;
   sprint 014 anchors at `c` with `[ρ₁, ρ₂] ⊆ (c, 1)` but the **disk-side
   bound `c⁴ · sigmaZeroMinus a b c`** (sprint 013) is a single Z, not a
   branch-split form. **Sprint 020 is the first reducer whose admissible
   window can contain `branchSplit c` strictly inside `(ρ₁, ρ₂)`**, e.g.
   any window with `c < ρ₁ < branchSplit c < ρ₂ < 1`. At the seed
   `c_value = 0.3554`, the natural witness `(ρ₁, ρ₂) = (4/10, 5/10)`
   straddles `branchSplit 0.3554 ≈ 0.4103` — admissible to sprint 020,
   inadmissible to sprints 008/014/017/018/019. This **strictly enlarges
   the workspace's space of admissible witness windows**.

2. **First closing reducer whose mass premise is a *sum of two* integrals
   over disjoint sub-intervals.** Every prior reducer that uses a windowed
   mass premise carries a single integral: sprint 008 has `1 ≤ ∫
   scalarIntegrand1` over `[ρ₁, ρ₂] ⊂ (c, branchSplit c]`, sprint 018 has
   `1 ≤ ∫ scalarIntegrand2` over `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`, sprint
   017 has `c⁴/2 ≤ ∫ 2ρ³·Z_ρ/Λ` over `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`,
   sprint 014 has `c⁴ ≤ ∫ 2ρ³/Λ` over `[ρ₁, ρ₂] ⊂ (c, 1)`. Sprint 020
   carries the sum
   `1 ≤ (∫_{ρ₁..branchSplit c} scalarIntegrand1) +
        (∫_{branchSplit c..ρ₂} scalarIntegrand2)` — the **first reducer
   whose closing condition combines the two branch-mode integrands in one
   premise**. This sufficient condition is **strictly weaker than either
   single-branch sufficient condition** on the same straddling window:
   any straddling window admissible to sprint 008 (impossible — sprint
   008 doesn't admit straddling) or sprint 018 (impossible — sprint 018
   doesn't admit straddling) is also admissible to sprint 020, plus
   sprint 020 admits straddling windows that neither sprint admits. Note
   the relationship to sprint 001's `valid_of_eq12_eq13`: sprint 001's
   mass condition is the *full-window* sum `∫_c^{branchSplit c}
   scalarIntegrand1 + ∫_{branchSplit c}^1 scalarIntegrand2 =
   scalarCriterion`, derived from the *integrated* (12) and (13). Sprint
   020 uses the *unintegrated* (10) and (11) over a *strict sub-window*
   that need not start at `c` or end at `1` — strictly finer-grained.

3. **First closing reducer to invoke both `paper.eq10_branch1_pointwise`
   and `paper.eq11_branch2_pointwise` simultaneously.** Sprint 008
   consumes `eq10` only; sprint 018 consumes `eq11` only; sprint 019
   consumes `(5)+(8)+(9)` only and re-derives `eq10` inline; sprint 017
   consumes `(6)+(8)+(9)+series` only. Sprint 020 is the **first
   workspace closing reducer that reaches the contract by consuming both
   printed pointwise inequalities `(10)` and `(11)` directly within the
   same proof body**. After this sprint, the workspace will have Lean
   proof that the printed pointwise pair `(10)+(11)` together suffice to
   close the contract over a strict sub-window straddling `branchSplit
   c` — a structural fact that none of sprints 008/017/018/019 establish
   on their own.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V20 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` that holds for *any* paper-faithful
  instance, parameterised by the witness window `(ρ₁, ρ₂)` and a single
  *summed* mass premise.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the straddling sub-regime is non-empty at the seed.
* The mass inequality `1 ≤ M₁ + M₂` is **not** numerically discharged at
  the seed in this sprint — it remains an existential premise on the new
  reducer, like every prior closing reducer's mass premise.

Why this is **not** "the same chain" as sprint 001:

* **Different admissibility regime.** Sprint 001 fixes the window at
  `[c, branchSplit c]` and `[branchSplit c, 1]` — the full disjoint
  branches. Sprint 020 admits any *strict sub-window* `[ρ₁, ρ₂]` with
  `c < ρ₁ ≤ branchSplit c ≤ ρ₂ < 1`. Sprint 020 strictly generalises in
  one direction (free `ρ₁, ρ₂`), but is strictly weaker in another (the
  full window has integrals over `(c, 1)`, this is over `(ρ₁, ρ₂) ⊊
  (c, 1)`).
* **Different paper hypotheses consumed.** Sprint 001 consumes
  `paper.eq12_branch1_integrated` and `paper.eq13_branch2_integrated`
  (the *integrated* paper inequalities). Sprint 020 consumes
  `paper.eq10_branch1_pointwise` and `paper.eq11_branch2_pointwise` (the
  *unintegrated* pointwise paper inequalities). These are different
  fields of `Section2Assumptions`. Sprint 020 must **NOT** invoke `(12)`
  or `(13)`.
* **Different annulus-side architecture.** Sprint 001 uses the explicit
  hypothesis `annulusLeftExcess + annulusRightExcess ≤ annulusExcess`
  passed in as a side condition. Sprint 020 derives the corresponding
  three-piece annulus splitting `annulusSlice c 1 = annulusSlice c ρ₁ +
  annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1` internally via
  `annulusSlice_add_adjacent`, then uses
  `annulusSlice_add_adjacent` *again* on `annulusSlice ρ₁ ρ₂` to split
  at `branchSplit c`. **Different splitting depth (4 pieces vs. 2
  pieces).**

Why this is **not** "the same chain" as sprints 008 + 018 stacked:

* **Single closing reducer, not a disjunction.** A trivial "stack" would
  be `if ρ ≤ branchSplit c then valid_of_eq10_subinterval_branch1 else
  valid_of_eq11_subinterval_branch2` over branch-disjoint windows. That
  is the alternative C demoted in sprints 017/018/019 as glue. Sprint
  020 is qualitatively different: a **single reducer** with a **single
  unified mass premise** `1 ≤ M₁ + M₂` whose admissibility region
  *crosses* the boundary that the two stacked reducers can never cross.
* **Strictly weaker sufficient condition.** On a fixed straddling window
  `[ρ₁, ρ₂]` with `c < ρ₁ < branchSplit c < ρ₂ < 1`, neither sprint 008
  nor sprint 018 is applicable (their admissibility predicates exclude
  straddling windows). Sprint 020 gives the *only* workspace closing
  route on such a window. Equivalently: there exist `(c, ρ₁, ρ₂)`
  configurations for which the workspace's space of valid sufficient
  conditions strictly grows with sprint 020. Glue stacking grows the
  conjunction of admissibility predicates by `OR`; sprint 020 grows it
  by adding a genuinely new admissibility cell.
* **New mass-decomposition argument.** The proof body must split the
  mass integral at `branchSplit c`, apply two parallel pointwise bounds
  (one per branch), and recombine via the addition-adjacent identity
  on annulus slices. This recombination step has no analogue in
  sprints 008 or 018 — both close via a single
  `mass_mul_le_annulusSlice_of_integral_bound_ae` call. Sprint 020
  performs **two** such calls and adds them.

Why this is **not** "the same chain" as sprint 014:

* **Disk-side bound shape.** Sprint 014's disk-side input is `c⁴ ·
  sigmaZeroMinus a b c` (sprint 013), pinned at `r = c`. Sprint 020's
  disk-side input is the direct `branchPointwiseFactor · diskExcess ≤
  circleGap ρ` from `(10)` and `(11)`, varying with `ρ`. **Different
  algebraic forms.**
* **Different annulus-side machinery.** Sprint 014 uses
  `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006) — a windowed
  annulus *lower* bound. Sprint 020 uses
  `mass_mul_le_annulusSlice_of_integral_bound_ae` — a windowed annulus
  *slice upper* bound on `diskExcess`. **Disjoint annulus-side
  bridges.**
* **Z-elimination vs Z-free.** Sprint 014's path goes through `Z` and
  ends at a Z-free kernel inequality `c⁴ ≤ ∫ 2ρ³/Λ`. Sprint 020 does
  not touch `sigmaZeroMinus`, `sigmaMinus`, or `Z` at all — it works
  directly from the pointwise (10)+(11) hypotheses to the annulus
  slice. **Sprint 020 has no series-level lemmas in its proof body.**

Why this is **bounded enough for one Generator session**:

* The proof body fuses two **already-verified** sub-routines: sprint
  008's branch-1 pointwise-to-annulus-slice argument
  (`Reduction.lean:856-1067`) and sprint 018's branch-2 pointwise-to-
  annulus-slice argument (`Reduction.lean:2109-…`). Both are
  ~234 lines line-by-line, but each sub-routine in sprint 020 operates
  on a *smaller* sub-interval (`[ρ₁, branchSplit c]` for branch-1,
  `[branchSplit c, ρ₂]` for branch-2 — half-open at one end), so each
  sub-routine is moderately shorter than the full sprint 008/018 body.
  Estimate: ~350 lines for the new theorem, dominated by the duplicated
  scaffolding.
* No new Mathlib lemmas needed. Every Lean idiom used
  (`mass_mul_le_annulusSlice_of_integral_bound_ae`,
  `paperScalarIntegrand1_intervalIntegrable`,
  `paperScalarIntegrand2_intervalIntegrable`,
  `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
  `annulusDensity_nonneg_of_lt`, `paperLambda_pos`,
  `Measure.restrict_congr_set`, `Ioo_ae_eq_Icc`, `field_simp`, `ring`,
  `linarith`, `nlinarith`, `positivity`, `mul_le_mul_of_nonneg_left`,
  `mono_set`, `calc`) is **already verified at the cited line ranges
  in sprints 008 and 018**.
* The new step is the **adding** of the two
  `mass_mul_le_annulusSlice_of_integral_bound_ae` outputs and the
  **summing of integrals** in the mass premise. Concretely:

  ```lean
  -- After two parallel mass_mul_le_annulusSlice applications:
  have hM₁ : M₁ * D ≤ annulusSlice paper.circleGap ρ₁ (branchSplit c) := …
  have hM₂ : M₂ * D ≤ annulusSlice paper.circleGap (branchSplit c) ρ₂ := …
  have hSum : (M₁ + M₂) * D ≤
      annulusSlice paper.circleGap ρ₁ (branchSplit c) +
      annulusSlice paper.circleGap (branchSplit c) ρ₂ := by
    have : (M₁ + M₂) * D = M₁ * D + M₂ * D := by ring
    rw [this]
    exact add_le_add hM₁ hM₂
  -- The annulus-slice sum collapses via annulusSlice_add_adjacent:
  have hAdj : annulusSlice paper.circleGap ρ₁ (branchSplit c) +
              annulusSlice paper.circleGap (branchSplit c) ρ₂ =
              annulusSlice paper.circleGap ρ₁ ρ₂ :=
    annulusSlice_add_adjacent paper.circleGap hρ₁_split hsplit_ρ₂
  rw [hAdj] at hSum
  -- Use M₁ + M₂ ≥ 1 to dominate D by the slice:
  have hSliceDominates : D ≤ annulusSlice paper.circleGap ρ₁ ρ₂ := by
    have hOne : (1 : ℝ) * D ≤ (M₁ + M₂) * D :=
      mul_le_mul_of_nonneg_right hMass hD_nonneg
    linarith [hSum, hOne, by simpa using (one_mul D : (1:ℝ)*D = D)]
  ```

  This is the unique new analytical step; everything else is sprint-008
  / sprint-018 boilerplate.
* The candidate side lemmas are 5–25 lines each (matching sprints 008,
  018, 019). Total V20 size: ≤ 80 lines.

Why this beats the alternatives I considered:

* **A: Branch-2 mirror of sprint 019 — `valid_of_eq6_eq8_eq9_subinterval_branch2`
  via `eq11_of_eq6_eq8_eq9`.** This is sprint 019's natural symmetric
  partner: ship the first workspace consumer of
  `KorenblumPaper.PaperAxioms.eq11_of_eq6_eq8_eq9` and re-derive
  `(11)` inline from `(6)+(8)+(9)`. **Demoted: mostly mechanical
  mirroring of sprint 019's proof body, which was itself a mostly
  mechanical extension of sprint 008. Two consecutive mechanical
  extensions trigger the bulletin's "more-of-the-same" demotion.** The
  novelty would be a *third* consumer of the same `eq8eq9_sigma_to_circleBridge`
  pattern — diminishing analytical return per Generator session.
  Queue separately as **sprint 021** if the next planner judges the
  branch-2 derived-pointwise variant valuable.

* **C: Combined `eq5 + eq6` full-annulus disk bound (`diskExcess ≤
  branchKernel(ρ) · ρ² · sigmaZeroMinus a b ρ` over `(c, 1)` with a
  branch-split `if ρ ≤ branchSplit c then …`).** Sprint 017's
  contract demoted this as glue: "Mechanical disjunction of sprints
  015 and 016 via `if ρ ≤ branchSplit c then … else …`. No new
  analytical chain through `Section2Assumptions` — just a glue
  lemma." **Still demoted.**

* **D: Z-free version of sprint 017** (extract `Z_{ρ₁}` from both
  sides via sprint 011 monotonicity, leaving the kernel
  `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` literally Z-free). **Demoted
  in sprints 018/019 as refactor with low novelty.** Same demotion
  applies.

* **E: New series-level continuity / left-edge limit lemmas for
  `s ↦ sigmaZeroMinus a b s`.** Demoted in sprints 016/017/018/019
  as speculative, no concrete consumer queued. **Still demoted.**

* **F: `paperLambda` upper-envelope from `paper.eq7_paperK_formula`
  alone.** Speculative — `paperLambda` is defined in
  `KorenblumPaper.OneModePaperBridge` via Wang's complicated
  `M(c, ρ)` formula, and no closed-form upper envelope is exposed.
  Investigating the `OneModePaperBridge` interior is beyond a
  single Generator session. **Demoted: requires structural
  exploration before it can be queued as a contract.**

* **G: Numerical-oracle registration discharging the kernel
  `c⁴/2 ≤ ∫ 2ρ³/Λ` at the seed.** Demoted in sprint 018/019 — needs
  a specific sub-window and closed-form `Λ`-bound shape, neither
  currently established. **Still demoted.**

* **H: A pure-`eq2` disk-side reducer.** Sprint 018's contract
  demoted this as wrong sign. **Still demoted.**

* **I: A second `eq11`-based reducer using `eq11` plus a windowed
  `eq2`-style lower bound on `Z`.** Sprint 018's contract demoted as
  speculative. **Still demoted.**

* **J: Cross-validation theorem `branch1SigmaKernel c ρ · ρ² ·
  sigmaZeroMinus a b ρ ≤ (sprint 003's collapsed RHS expression)`.**
  Sprint 019's contract demoted as too narrow. **Still demoted.**

* **K (sprint 019, just shipped): `(5)+(8)+(9)`-derived branch-1
  reducer.** Already done.

Compared to A–K, candidate L (this sprint,
`valid_of_eq10_eq11_straddling_window`) maximises analytical novelty per
bounded Generator session: it ships the **first workspace closing
reducer with a straddling-window admissibility predicate**, the **first
mass premise that sums two integrals over disjoint sub-intervals**, and
the **first proof body to invoke both `paper.eq10_branch1_pointwise`
and `paper.eq11_branch2_pointwise` directly**. It uses **only existing
trusted modules + pinned Mathlib + already-verified `Reduction.lean`
lemmas** in patterns directly mirrored from sprints 008 and 018. No
proposal needed.

### Note on the algebraic collapses

Identical to sprint 008's branch-1 collapse (`Reduction.lean:942-950`)
on the branch-1 sub-piece, and identical to sprint 018's branch-2
collapse on the branch-2 sub-piece. Symbolically:

```lean
-- Branch-1 piece (verbatim from sprint 008):
have hRewriteLHS_b1 :
    2 * ρ *
        (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
        * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
  unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
  field_simp
  ring

-- Branch-2 piece (verbatim from sprint 018):
have hRewriteLHS_b2 :
    2 * ρ *
        (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
      Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
        * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
  unfold Korenblum.scalarIntegrand2 PaperAxioms.branch2PointwiseFactor
  field_simp
  ring
```

### Note on the integrability calls

Each branch piece needs its own integrability hook. The branch-1 piece
uses `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
on `[ρ₁, branchSplit c] ⊆ [c, 1]`; the branch-2 piece uses
`WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable` on
`[branchSplit c, ρ₂] ⊆ [c, 1]`. Concretely:

```lean
-- Branch-1 sub-interval integrability (use hcρ₁ and hSplit_le_one):
have hModeInt_b1 :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      volume ρ₁ (PaperAxioms.branchSplit c) :=
  WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
    hc_pos hρ₁_split hcρ₁.le hSplit_le_one paper.eq7_paperK_formula
-- Branch-2 sub-interval integrability (use hSplit_lt_one and hSplit_le_ρ₂):
have hModeInt_b2 :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
      volume (PaperAxioms.branchSplit c) ρ₂ :=
  WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable
    hc_pos hsplit_ρ₂ (le_trans hcρ₁.le hρ₁_split) hρ₂_lt_one.le
    paper.eq7_paperK_formula
```

(Argument order matches sprint 008's call site at
`Reduction.lean:908-910` and sprint 018's analogous call.)

### Note on the witness window at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value = c_value · √(4/3) ≈ 0.4103`.
* For a *straddling* window we need `c_value < ρ₁ ≤ branchSplit c_value
  ≤ ρ₂ < 1`. The cleanest concrete witness is the *degenerate*
  straddling window `(ρ₁, ρ₂) = (branchSplit c_value, branchSplit
  c_value)` collapsed at `branchSplit c_value` itself: trivially
  `branchSplit c_value ≤ branchSplit c_value` (`le_refl`) and
  `branchSplit c_value ≤ branchSplit c_value` (`le_refl`); the
  conditions `c_value < branchSplit c_value` and `branchSplit c_value <
  1` reduce to the already-proven helpers `c_value < branchSplit
  c_value` (sprint 017's body, `Reduction.lean:1963-1972`) and
  `branchSplit c_value < 1` (sprint 008's `v8_split_lt_one_at_seed`).
  This degenerate witness sidesteps any numerical-bound risk on
  `√(4/3)` and demonstrates the admissibility predicate is non-vacuous.

  *Non-degenerate fallback* (only if the planner judges the degenerate
  witness too thin): pick `(ρ₁, ρ₂) = (4/10, 5/10)`. The constraints
  `c_value < 4/10` (i.e. `0.3554 < 0.4`) and `5/10 < 1` are
  `norm_num`. The interesting constraints are `4/10 ≤ branchSplit
  c_value` and `branchSplit c_value ≤ 5/10`. The lower bound needs
  `√(4/3) ≥ 4/(10 · 0.3554) ≈ 1.1255`, achievable via `nlinarith` with
  `1.13² = 1.2769 < 4/3`. The upper bound needs `√(4/3) · 0.3554 ≤
  0.5`, i.e. `√(4/3) ≤ 5/(10 · 0.3554) ≈ 1.4068`, achievable via
  `nlinarith` with `1.41² = 1.9881 > 4/3` (so `√(4/3) < 1.41`).
  However, this bumps the witness lemma's complexity by ~15 lines of
  `nlinarith` plumbing — the **degenerate single-point straddling
  witness is preferred** for time-budget reasons.

### Note on what the witness lemma should NOT do

Sprint 020's V20 witness lemma is **structural only** — it confirms that
the admissible-window predicate `c_value < ρ₁ ∧ ρ₁ ≤ branchSplit c_value
∧ branchSplit c_value ≤ ρ₂ ∧ ρ₂ < 1` is non-vacuous at the seed by
exhibiting concrete `ρ₁, ρ₂`. It **does NOT discharge the integrability
premises, nor the mass premise `1 ≤ M₁ + M₂`**. Those remain as
existential hypotheses on the new reducer, just like V8/V14/V17/V18/V19's
witnesses do not discharge their respective sprints' premises.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem `valid_of_eq10_eq11_straddling_window`
    matching the shape above. The proof body must:

    1. **Open `valid_of` framework.** `refine ⟨hc_pos, hc_lt_one, ?_⟩;
       intro a b K paper; obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_split,
       hsplit_ρ₂, hρ₂_lt_one, hMass⟩ := h_window paper`.

    2. **Geometric scaffolding.** Derive `hSplit_le_one`,
       `hcρ₂` (via `lt_of_lt_of_le hcρ₁ (le_trans hρ₁_split
       hsplit_ρ₂)`), `hSplit_pos := lt_trans hc_pos hcρ₁ |>.trans_le
       hρ₁_split` (i.e. `0 < branchSplit c`), `hc_le_ρ₁`,
       `hSplit_le_ρ₂`, `hρ₁_le_split`, `hρ₂_le_one`,
       `hρ₁_lt_one := lt_of_le_of_lt (le_trans hρ₁_split hsplit_ρ₂)
       hρ₂_lt_one`, `hc_le_one`.

    3. **Global annulus-density integrability.** `have hIntCircle :=
       hIntDensity paper`.

    4. **Sub-interval integrability of `annulusDensity` via `mono_set`.**
       Need `IntervalIntegrable` on the four sub-intervals
       `[c, ρ₁]`, `[ρ₁, branchSplit c]`, `[branchSplit c, ρ₂]`, and
       `[ρ₂, 1]`, plus a global `[ρ₁, ρ₂]`. Mirror sprint 008's
       `huIcc_…` and `hIntDens_…` blocks (`Reduction.lean:871-902`).

    5. **Sub-interval integrability of `scalarIntegrand1` and
       `scalarIntegrand2`.** Use the two paper hooks per the snippets
       above.

    6. **Pointwise bound on `Ioo ρ₁ (branchSplit c)`.** Mirror sprint
       008's `hPointwiseIoo` block (`Reduction.lean:913-955`), with
       `paper.eq10_branch1_pointwise hcρ hρ_split` driving the
       pointwise step. This branch-1 piece needs a separate `hcρ : c <
       ρ` derivation from `hρ ∈ Ioo ρ₁ (branchSplit c)` and
       `hcρ₁ : c < ρ₁`.

    7. **Pointwise bound on `Ioo (branchSplit c) ρ₂`.** Mirror sprint
       018's analogous block, with `paper.eq11_branch2_pointwise
       hsplit_ρ hρ_one` driving the pointwise step. This branch-2
       piece needs a separate `hcρ : c < ρ` derivation from `hρ ∈ Ioo
       (branchSplit c) ρ₂` and `hcρ₁.trans_le hρ₁_split`.

    8. **`Ioo → Icc` lift on each branch piece.** Verbatim from sprint
       008's lift step (`Reduction.lean:957-985`), once per piece.

    9. **`mass_mul_le_annulusSlice_of_integral_bound_ae` on each
       branch piece.** Verbatim from sprint 008
       (`Reduction.lean:986-998`), once per piece. Define
       `M₁ := ∫ ρ in ρ₁..branchSplit c, scalarIntegrand1 …` and
       `M₂ := ∫ ρ in branchSplit c..ρ₂, scalarIntegrand2 …`. Get

       ```lean
       have hM₁_slice :
           M₁ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             AnnulusIntegralReduction.annulusSlice paper.circleGap
               ρ₁ (PaperAxioms.branchSplit c) := …
       have hM₂_slice :
           M₂ * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             AnnulusIntegralReduction.annulusSlice paper.circleGap
               (PaperAxioms.branchSplit c) ρ₂ := …
       ```

    10. **Add the two slice inequalities.** Use
        `add_le_add hM₁_slice hM₂_slice` and the algebraic identity
        `(M₁ + M₂) · D = M₁ · D + M₂ · D` (one-line `ring`) to obtain

        ```lean
        have hSum_slice :
            (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              AnnulusIntegralReduction.annulusSlice paper.circleGap
                ρ₁ (PaperAxioms.branchSplit c) +
              AnnulusIntegralReduction.annulusSlice paper.circleGap
                (PaperAxioms.branchSplit c) ρ₂ := …
        ```

    11. **Collapse the slice sum via `annulusSlice_add_adjacent`.**
        At adjacency `branchSplit c`:

        ```lean
        have hAdj_split :
            AnnulusIntegralReduction.annulusSlice paper.circleGap
              ρ₁ (PaperAxioms.branchSplit c) +
            AnnulusIntegralReduction.annulusSlice paper.circleGap
              (PaperAxioms.branchSplit c) ρ₂ =
            AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
          AnnulusIntegralReduction.annulusSlice_add_adjacent paper.circleGap
            hρ₁_le_split hSplit_le_ρ₂
        ```

        (Verify the exact signature of `annulusSlice_add_adjacent` —
        sprint 008 uses it at `Reduction.lean:1004-1015`. The
        adjacency arguments are `ρ₁ ≤ branchSplit c` and `branchSplit
        c ≤ ρ₂`.) Rewrite `hSum_slice` via `hAdj_split`.

    12. **Use `1 ≤ M₁ + M₂` to dominate `D` by the slice.**

        ```lean
        have hD_nonneg : 0 ≤ PaperAxioms.diskExcess
            (PaperAxioms.circleGap a b) c := …  -- via diskExcess_nonneg
        have hSliceDominates :
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
              AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
          have hOneStep :
              (1 : ℝ) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
                (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c :=
            mul_le_mul_of_nonneg_right hMass hD_nonneg
          calc
            PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
                = 1 * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
                  rw [one_mul]
            _ ≤ (M₁ + M₂) * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c :=
                  hOneStep
            _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ := by
                  rw [← hAdj_split]; exact hSum_slice
        ```

    13. **Annulus-side splitting and slice non-negativities.** Verbatim
        from sprint 008 (`Reduction.lean:1004-1052`):
        `annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ +
        annulusSlice ρ₂ 1` via two adjacency applications, then
        discharge `annulusSlice c ρ₁ ≥ 0` and `annulusSlice ρ₂ 1 ≥ 0`
        via `annulusSlice_nonneg_of_ae` and the local helper
        `annulusDensity_nonneg_of_lt`.

    14. **Final calc chain.** Mirror sprint 008's final calc
        (`Reduction.lean:1054-1066`):

        ```lean
        calc
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
              ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap ρ₁ ρ₂ :=
                hSliceDominates
          _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := by
              -- via the three-piece split + side-slice non-negativities
              linarith
          _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := rfl
        ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 020's `valid_of_eq10_eq11_straddling_window` is
    the workspace's **first closing reducer with a straddling-window
    admissibility predicate**, the **first reducer whose mass premise
    sums two integrals over disjoint branch sub-intervals**, and the
    **first reducer to invoke both `paper.eq10_branch1_pointwise` and
    `paper.eq11_branch2_pointwise` simultaneously**. Sprint 020's
    sufficient condition is strictly weaker than either single-branch
    sufficient condition on the same straddling window, and admits a
    region of `(ρ₁, ρ₂)`-pairs that no prior reducer can address.

  * The body of `valid_of_eq10_eq11_straddling_window` MAY invoke:

    * `paper.eq10_branch1_pointwise` (the unique direct branch-1
      paper-axiom consumption),
    * `paper.eq11_branch2_pointwise` (the unique direct branch-2
      paper-axiom consumption),
    * `paper.eq7_paperK_formula` (via the integrability hooks),
    * `paper.circleGap` (annulus-density side, matching sprints 008
      and 018),
    * `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
    * `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`,
    * `WangPaperSideConditions.paperLambda_pos`,
    * `AnnulusIntegralReduction.annulusDensity`,
    * `AnnulusIntegralReduction.annulusSlice`,
    * `AnnulusIntegralReduction.annulusSlice_add_adjacent`,
    * `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae`,
    * `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`,
    * `annulusDensity_nonneg_of_lt`, `annulusExcess_nonneg` (locally
      defined helpers in `Reduction.lean`),
    * `PaperAxioms.branch1PointwiseFactor`,
      `PaperAxioms.branch2PointwiseFactor`, `PaperAxioms.branchSplit`,
      `PaperAxioms.diskExcess`, `PaperAxioms.annulusExcess` (definitional
      unfolding),
    * `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`
      (definitional unfolding),
    * `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `add_le_add`, `IntervalIntegrable.mono_set`,
      `Measure.restrict_congr_set`, `Ioo_ae_eq_Icc`,
      `ae_restrict_iff' measurableSet_Ioo`, `field_simp`, `ring`,
      `linarith`, `nlinarith`, `positivity`, `calc`, `change`,
      `unfold`, `rw`, `simpa`, `Filter.Eventually.of_forall`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that the new reducer
    reaches closure through the **direct `(10)+(11)` chain only**, with
    *both* branches consumed via *direct paper fields*, not via the
    `(5)+(8)+(9)` or `(6)+(8)+(9)` derivation chains):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
      `paper.eq6_`, `paper.eq8_`, `paper.eq9_`, `paper.eq12_`,
      `paper.eq13_`, `paper.eq14_`, `paper.eq15_` (only `(7)+(10)+(11)`
      of the paper hypotheses are admitted along this chain),
    * `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, `eq10_of_eq5_eq8_eq9`,
      `eq11_of_eq6_eq8_eq9` (no derived theorems — sprint 020 must
      consume the printed `(10)` and `(11)` directly, not re-derive
      them),
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
      `valid_of_eq5_eq8_eq9_subinterval_branch1` (no upstream closing
      reducer — sprint 020 must close on its own from
      `(7)+(10)+(11)`),
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
      `sigmaZeroMinus_summable_of_summable_at_upper`,
      `paper.liftGap` (these are markers of the `(2)+(3)+(4)` /
      `(5)+(8)+(9)` / `(6)+(8)+(9)` / series-level chains — all
      unrelated to the direct `(10)+(11)` chain sprint 020
      establishes),
    * `branch1SigmaKernel`, `branch2SigmaKernel`, `sigmaPlus`,
      `sigmaZeroMinus`, `sigmaMinus`, `Korenblum.scalarCriterion`
      (these are markers of the `Σ`-side / integrated chains).

    (Note: `WangOuter.paperLambda` and
    `WangPaperSideConditions.paperLambda_pos` are EXEMPT and ARE
    needed — they are named ingredients of `scalarIntegrand1`,
    `scalarIntegrand2`, and the integrand non-negativity proofs.
    `Section2Assumptions` is EXEMPT — it is the input.
    `branch1PointwiseFactor` and `branch2PointwiseFactor` are EXEMPT —
    they appear in the `(10)` and `(11)` shapes respectively.
    `scalarIntegrand1` and `scalarIntegrand2` are EXEMPT — they appear
    in the windowed mass premise.)

  * The new theorem's signature MUST take *exactly* the parameters in
    the goal block above. The two existential conjunction cells
    `c < ρ₁ ∧ ρ₁ ≤ branchSplit c` and `branchSplit c ≤ ρ₂ ∧ ρ₂ < 1`
    must appear with the indicated comparison directions (no
    open/closed swaps). The mass premise must be the **literal sum**
    `(∫ ρ in ρ₁..branchSplit c, scalarIntegrand1 …) + (∫ ρ in
    branchSplit c..ρ₂, scalarIntegrand2 …)` — not equivalent forms
    like `∫ ρ in ρ₁..ρ₂, (if ρ ≤ branchSplit c then scalarIntegrand1
    else scalarIntegrand2) …`.

* `ProofRefinement/Korenblum/Candidates/V20.lean`:

  * `-- @parent V19`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V19).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V19).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v20_eq10_eq11_straddling_window_compiles
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
              c_value < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c_value ∧
                PaperAxioms.branchSplit c_value ≤ ρ₂ ∧ ρ₂ < 1 ∧
                (1 : ℝ) ≤
                  (∫ ρ in ρ₁..PaperAxioms.branchSplit c_value,
                    Korenblum.scalarIntegrand1 c_value
                      (WangOuter.paperLambda K c_value) ρ) +
                  (∫ ρ in PaperAxioms.branchSplit c_value..ρ₂,
                    Korenblum.scalarIntegrand2 c_value
                      (WangOuter.paperLambda K c_value) ρ)) :
        ValidKorenblumBound c_value :=
      valid_of_eq10_eq11_straddling_window
        c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window
    ```

  * Additionally, prove a structural witness lemma confirming the
    straddling sub-regime is non-vacuous at the seed by exhibiting a
    concrete `(ρ₁, ρ₂)`:

    ```lean
    theorem v20_straddling_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ PaperAxioms.branchSplit c_value ∧
            PaperAxioms.branchSplit c_value ≤ ρ₂ ∧ ρ₂ < 1 := by
      -- Degenerate single-point straddling witness at branchSplit c_value.
      refine ⟨PaperAxioms.branchSplit c_value, PaperAxioms.branchSplit c_value,
              ?_, le_rfl, le_rfl, ?_⟩
      · -- c_value < branchSplit c_value
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
      · -- branchSplit c_value < 1: copy from V8 / V19 witness pattern
        show PaperAxioms.branchSplit c_value < (1 : ℝ)
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
    ```

    The degenerate single-point straddling witness `ρ₁ = ρ₂ =
    branchSplit c_value` confirms the straddling-window predicate is
    non-vacuous without committing to non-trivial numerical bounds.
    The `c_value < branchSplit c_value` block is verbatim from sprint
    019's `v19_branch1_window_witness_at_seed`; the `branchSplit
    c_value < 1` block is verbatim from sprint 018's
    `v18_branch2_window_witness_at_seed` first conjunct (with `5 / 10`
    replaced by `1`).

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify the new reducer's signature
    typechecks at the seed `c_value` and to demonstrate the
    straddling window is non-vacuous.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V19.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_019`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V20.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V20.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V20 scores `≥` V19 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V20.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_eq10_eq11_straddling_window' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of `paper.eq10_branch1_pointwise`,
   * exactly one direct invocation of `paper.eq11_branch2_pointwise`,
   * exactly one invocation of
     `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
   * exactly one invocation of
     `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`,
   * **at least two** invocations of
     `mass_mul_le_annulusSlice_of_integral_bound_ae` (one per branch),
   * **at least two** invocations of `annulusSlice_add_adjacent` (one
     for the slice-sum collapse at `branchSplit c`, one for the
     three-piece annulus-excess split — sprint 008 already uses two
     such invocations for the latter purpose),
   * no direct reference to `paper.eq2_`, `paper.eq3_`, `paper.eq4_`,
     `paper.eq5_`, `paper.eq6_`, `paper.eq8_`, `paper.eq9_`,
     `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
   * no reference to `eq10_of_eq5_eq8_eq9`, `eq11_of_eq6_eq8_eq9`,
     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`,
   * no reference to any of the prior `valid_of_*` reducers,
   * no reference to `sigmaZeroMinus_*`, `sigmaMinus_*`,
     `circleGap_inner_bound_*`, `circleGap_outer_lower_bound_*`,
     `diskExcess_upper_bound_*`, `annulusExcess_lower_bound_*`,
     `paper.liftGap`, `branch1SigmaKernel`, `branch2SigmaKernel`,
     `Korenblum.scalarCriterion`.
6. `grep -n 'v20_eq10_eq11_straddling_window_compiles\|v20_straddling_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V20.lean`
   returns at least two distinct matches.
7. The conclusion of `valid_of_eq10_eq11_straddling_window` is exactly
   `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_window` existential body in
   `valid_of_eq10_eq11_straddling_window` contains:
   * the constraint `c < ρ₁` (verify via `grep`),
   * the constraint `ρ₁ ≤ PaperAxioms.branchSplit c` (verify via `grep`),
   * the constraint `PaperAxioms.branchSplit c ≤ ρ₂` (verify via `grep`),
   * the constraint `ρ₂ < 1` (verify via `grep`),
   * the literal *summed* mass inequality
     `(1 : ℝ) ≤ (∫ ρ in ρ₁..PaperAxioms.branchSplit c, Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ) + (∫ ρ in PaperAxioms.branchSplit c..ρ₂, Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)`
     (verify via `grep` for the two `∫ … in …` substrings on either
     side of `+` within a single conjunction cell).
9. The body of `v20_straddling_window_witness_at_seed` exhibits a
   concrete `(ρ₁, ρ₂)` with `c_value < ρ₁ ≤ branchSplit c_value ≤ ρ₂
   < 1` (verify via `grep` of the theorem body for `branchSplit
   c_value` appearing as the witness for both `ρ₁` and `ρ₂` in the
   degenerate single-point case, or for two numeric literals in the
   admissible non-degenerate case).
10. The new theorem's `h_window` admits **straddling** windows: its
    conjunction allows both `ρ₁ < branchSplit c < ρ₂` *and* `ρ₁ ≤
    branchSplit c ≤ ρ₂` configurations; in particular the strict
    forms `c < ρ₁` and `ρ₂ < 1` are present, and the boundary forms
    `ρ₁ ≤ branchSplit c` and `branchSplit c ≤ ρ₂` are present (as
    inequalities, not strict). Verify via `grep` that none of `ρ₁ <
    branchSplit c`, `branchSplit c < ρ₂`, `ρ₂ ≤ branchSplit c`, or
    `branchSplit c < ρ₁` appears in the existential conjunction —
    only `c < ρ₁`, `ρ₁ ≤ branchSplit c`, `branchSplit c ≤ ρ₂`, `ρ₂ <
    1`.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V19.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Building the `(6)+(8)+(9)`-derived branch-2 mirror of sprint 019
  via `eq11_of_eq6_eq8_eq9` (alternative A above — queue separately
  as **sprint 021** if the next planner judges branch-2 derived-
  pointwise valuable).
* Building the combined `eq5 + eq6` full-annulus disk bound
  (alternative C above — mechanical disjunction, not a new chain).
* Building the Z-free version of sprint 017 (alternative D above —
  refactor with low novelty).
* Discharging the mass inequality `1 ≤ M₁ + M₂` numerically at the
  seed `c_value` — this requires a `paperLambda` envelope or a
  numerical oracle, both out of scope for this sprint.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the mass inequality (out of scope above) or a
  qualitatively new analytical witness that closes the mass inequality
  from paper hypotheses alone.
* Any modification to sprints 008's `valid_of_eq10_subinterval_branch1`,
  sprint 018's `valid_of_eq11_subinterval_branch2`, sprint 019's
  `valid_of_eq5_eq8_eq9_subinterval_branch1`, or the locally-defined
  helpers `annulusDensity_nonneg_of_lt`, `annulusSlice_nonneg_of_ae`,
  `annulusSlice_add_adjacent` (these are consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 020 is purely
  structural.

## Time budget

≤ 45 minutes runtime. The new reducer is ~350 lines of Lean —
moderately heavier than sprints 008 (~234 lines) and 018 (~235 lines)
because it duplicates the pointwise+mass machinery once per branch,
but lighter than the sum of the two because the geometric scaffolding
is shared. All tactics used are *already verified* in sprints 008
(`Reduction.lean:833-1067`) and 018 (`Reduction.lean:2109-…`). The
candidate side lemmas are 5–25 lines each (including the witness at
the seed). Total V20 size: ≤ 90 lines (slightly larger than V19's V19
because the witness lemma combines two `nlinarith` blocks).

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The two-piece pointwise-to-slice argument fails to compose (e.g. the
  algebraic identity `(M₁ + M₂) · D = M₁ · D + M₂ · D` does not unify
  cleanly with the `add_le_add hM₁ hM₂` step) — fall back to expressing
  the addition explicitly via
  `linarith [hM₁_slice, hM₂_slice, hMass]` once `hD_nonneg` and the
  one-mul collapse are in scope.
* `annulusSlice_add_adjacent` cannot be invoked at `branchSplit c`
  due to a signature mismatch (e.g. it requires strict ordering rather
  than weak) — fall back to the verbatim sprint 008 invocation pattern
  at `Reduction.lean:1004-1015` and adjust accordingly. Sprint 008's
  body uses `annulusSlice_add_adjacent` with two adjacency arguments
  `c ≤ ρ₁` and `ρ₁ ≤ ρ₂`; sprint 020's analogue at the slice-sum step
  uses `ρ₁ ≤ branchSplit c` and `branchSplit c ≤ ρ₂`.
* The integrability hooks fail to type-check on the *split* sub-intervals
  (e.g. `[ρ₁, branchSplit c]` instead of `[ρ₁, ρ₂]`) — fall back to
  proving sub-interval integrability via `IntervalIntegrable.mono_set`
  applied to the global integrability on `[c, 1]`, mirroring sprint
  008's `Reduction.lean:871-902` block.
* The witness lemma `v20_straddling_window_witness_at_seed`'s
  `nlinarith` step for `c_value < branchSplit c_value` cannot close
  cleanly — fall back to copying sprint 017's body block at
  `Reduction.lean:1963-1972` (already verified working in V17).
* The witness lemma's `branchSplit c_value < 1` step fails — fall back
  to V8's verbatim witness `v8_split_lt_one_at_seed` body (already
  verified working in V8).
* Any of acceptance criteria 4, 5, 7, 8, 9, 10 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5 (especially any prior `valid_of_*` reducer
  or any series-level lemma): `STATUS=BLOCKED` — that would defeat
  the "direct `(7)+(10)+(11)` chain only" structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
