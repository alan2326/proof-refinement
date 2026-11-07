# Sprint 018: `eq11`-based branch-2 sub-interval sufficient condition `valid_of_eq11_subinterval_branch2` — the workspace's **first consumer of Wang's printed equation `(11)`**, the **first closing reducer reaching the branch-2 sub-regime via the short `(7)+(11)` chain** (no `(8)+(9)`+series machinery), and the **first cross-validation of two structurally disjoint paper-equation paths to the same effective branch-2 kernel scalar `c⁴/2`**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V17.lean`
**Target file**: `Candidates/V18.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_eq11_subinterval_branch2
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
          PaperAxioms.branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (1 : ℝ) ≤
              ∫ ρ in ρ₁..ρ₂,
                Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c
```

The proof body is the **branch-2 mirror** of sprint 008's
`valid_of_eq10_subinterval_branch1` body (`Reduction.lean:833-1067`).
Each branch-1 ingredient gets swapped for its already-existing
branch-2 counterpart, with no new analytical infrastructure required:

| Sprint 008 (branch-1) | Sprint 018 (branch-2) |
|---|---|
| `paper.eq10_branch1_pointwise` | `paper.eq11_branch2_pointwise` |
| `PaperAxioms.branch1PointwiseFactor` | `PaperAxioms.branch2PointwiseFactor` |
| `Korenblum.scalarIntegrand1` | `Korenblum.scalarIntegrand2` |
| `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable` | `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable` |
| Window: `c < ρ₁ ≤ ρ₂ ≤ branchSplit c` | Window: `branchSplit c < ρ₁ ≤ ρ₂ < 1` |
| Sub-region constraints used: `c ≤ ρ₁`, `ρ₂ ≤ branchSplit c ≤ 1` | Sub-region constraints used: `c ≤ branchSplit c ≤ ρ₁`, `ρ₂ ≤ 1` |
| Side-slice non-negativity: `[c, ρ₁]`, `[ρ₂, 1]` | Side-slice non-negativity: `[c, ρ₁]`, `[ρ₂, 1]` |
| Algebraic identity:`2ρ · branch1PointwiseFactor c Λ ρ = scalarIntegrand1 c Λ ρ` (i.e. `2ρ · 6ρ²(ρ²−c²)/(c⁶·Λ) = 12ρ³(ρ²−c²)/(c⁶·Λ)`) | Algebraic identity: `2ρ · branch2PointwiseFactor c Λ ρ = scalarIntegrand2 c Λ ρ` (i.e. `2ρ · 2ρ²/(c⁴·Λ) = 4ρ³/(c⁴·Λ)`) |
| Annulus-side splitting: `annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ + annulusSlice ρ₂ 1` | Identical splitting (annulus-side architecture is branch-agnostic) |

The closing chain is structurally identical to sprint 008:

1. Multiply `paper.eq11_branch2_pointwise hρ_split hρ1 :
   branch2PointwiseFactor c Λ ρ · diskExcess ≤ circleGap ρ` by
   `2ρ ≥ 0` to obtain pointwise
   `scalarIntegrand2 c Λ ρ · diskExcess ≤ annulusDensity paper.circleGap ρ`
   on the open `Ioo ρ₁ ρ₂`, after the algebraic identity
   `2ρ · 2ρ²/(c⁴·Λ) = 4ρ³/(c⁴·Λ)` discharged by `field_simp; ring`.
2. Lift `Ioo → Icc` via `Measure.restrict_congr_set Ioo_ae_eq_Icc`.
3. Apply
   `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`
   with `mass = 1` and the witness `1 ≤ ∫ scalarIntegrand2`.
4. Split `annulusSlice c 1` via `annulusSlice_add_adjacent` twice and
   discharge the side-slice non-negativities via
   `annulusSlice_nonneg_of_ae` (sprint 008 has this verbatim).
5. Identify `annulusSlice c 1 = annulusExcess … c` (definitional `rfl`).

Then ship a `Candidates/V18.lean` at the same `c = 0.3554` that
compiles, scores `≥ V17`, and *materialises* the new lemma in side
lemmas `v18_eq11_subinterval_branch2_compiles` and
`v18_branch2_window_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 018 is the natural and bounded
next move on three independent novelty axes that no prior workspace
sprint touches:

1. **First workspace consumer of Wang's printed equation `(11)`.**
   `Section2Assumptions` exposes ten paper inequalities
   (`eq2`–`eq14`); after sprint 017, the workspace consumes
   `eq2`, `eq3`, `eq4`, `eq5`, `eq6`, `eq7`, `eq8`, `eq9`, `eq10`,
   `eq12`, `eq13`, `eq14`, `eq15` — but `eq11` has **never** been
   consumed by any workspace theorem. Sprint 018 fills this exact gap:
   it ships the **first closing reducer to consume
   `paper.eq11_branch2_pointwise` directly**. After this sprint, the
   workspace will have closing reducers via every paper-equation chain
   except those depending on `eq11`'s mirror in branches not yet
   discovered. This pushes the workspace to *complete coverage of
   Wang's printed pointwise inequalities*: `(10)+(11)`.

2. **First short closing chain on the branch-2 sub-regime.** Sprint
   017 ships the **only** prior closing reducer entirely on the
   branch-2 sub-regime, but it goes through the **long** chain
   `(6)+(8)+(9)+series`: disk-side via `eq6_branch2_sigmaReduction`,
   then `Σ⁻ → liftGap` via `eq8`, then `liftGap → Λ·circleGap` via
   `eq9`, plus sprint 005's series identity for `Σ⁻ = ρ²·Σ⁻₀` and
   sprints 011/012 for `Z`-monotonicity transfer across the window.
   Sprint 018 ships the **first short** closing chain on the
   branch-2 sub-regime, going through the **direct** `(7)+(11)`
   chain: paper equation `(11)` directly bounds
   `branch2PointwiseFactor · diskExcess ≤ circleGap`, then we
   integrate against `2ρ` to produce
   `scalarIntegrand2 · diskExcess ≤ annulusDensity`, dominated
   by the windowed annulus excess via the existing
   `mass_mul_le_annulusSlice_of_integral_bound_ae` machinery. **No
   `(8)`, no `(9)`, no series-level `sigmaZeroMinus` lemmas, no
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` identity.** The chain
   shrinks from "5 paper ingredients" (sprint 017) to "2 paper
   ingredients" (sprint 018).

3. **First cross-validation of two structurally disjoint paths to the
   same effective branch-2 kernel scalar `c⁴/2`.** Sprint 017's
   reducer requires
   `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` (kernel inequality after
   factor extraction). Sprint 018's reducer, when expanded, requires
   `1 ≤ ∫_{ρ₁..ρ₂} 4ρ³/(c⁴·Λ(c,ρ)) dρ`, which is *literally*
   `c⁴/4 ≤ ∫_{ρ₁..ρ₂} ρ³/Λ(c,ρ) dρ`, equivalently
   `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`. **Algebraically identical
   kernel scalar.** This means the two structurally disjoint
   paper-equation paths
   – `(6)+(8)+(9)+series` (sprint 017, "long path") and
   – `(7)+(11)` (sprint 018, "short path")
   converge on **exactly the same effective scalar threshold**.
   This is a **paper-internal cross-check**: Wang's pointwise
   `(11)` and Wang's `(6)+(8)+(9)` chain are not independent
   inequalities — they should yield the same kernel constant on the
   branch-2 sub-regime, and sprint 018 verifies this in Lean.
   Compare to how sprint 015 (`eq5`-based disk bound on branch 1)
   cross-validates sprint 007 (`eq2+eq3+eq4`-based collapsed disk
   bound on branch 1) and recovers the same `branch1SigmaKernel ·
   ρ² · Z_ρ` form — sprint 018 plays the analogous role on the
   branch-2 sub-regime, but at the *closing* level (not just the
   disk-bound level).

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V18 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form sufficient
  condition for `ValidKorenblumBound c` that holds for *any*
  paper-faithful instance, parameterised by the witness window
  `(ρ₁, ρ₂)` and a single scalar mass premise on `scalarIntegrand2`.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the branch-2 sub-regime is non-empty at the seed
  (re-using the V14/V17 witness `(0.5, 0.7)`, since
  `branchSplit c_value ≈ 0.4103 < 0.5`).

Why this is **not** "the same chain" as sprint 008:

* **Different paper equation.** Sprint 008 consumes
  `paper.eq10_branch1_pointwise`. Sprint 018 consumes
  `paper.eq11_branch2_pointwise`. These are *disjoint* paper
  hypotheses — neither implies the other.
* **Different admissible region.** Sprint 008 admits any
  `[ρ₁, ρ₂] ⊆ (c, branchSplit c]`. Sprint 018 admits any
  `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`. **The two admissibility
  predicates are mutually disjoint** (modulo the boundary point
  `ρ = branchSplit c`).
* **Different mode integrand.** Sprint 008's mass premise is
  `1 ≤ ∫ scalarIntegrand1 = ∫ 12ρ³(ρ²−c²)/(c⁶·Λ)`. Sprint 018's
  mass premise is `1 ≤ ∫ scalarIntegrand2 = ∫ 4ρ³/(c⁴·Λ)`. The
  branch-2 integrand is **structurally simpler** (no `ρ²−c²`
  factor, lower power of `c` in the denominator).
* **Different pointwise factor.** `branch1PointwiseFactor`
  involves `(ρ²−c²)`; `branch2PointwiseFactor` does not. Sprint
  018's `field_simp; ring` collapse step works on `2ρ · 2ρ²/(c⁴·Λ)
  = 4ρ³/(c⁴·Λ)`, which is **a strictly simpler algebraic
  identity** than sprint 008's
  `2ρ · 6ρ²(ρ²−c²)/(c⁶·Λ) = 12ρ³(ρ²−c²)/(c⁶·Λ)`.

Why this is **not** "the same chain" as sprint 017:

* **Different paper equations consumed.** Sprint 017 consumes
  `eq6+eq8+eq9` (transitively, plus sprint 005's series identity
  and sprints 011/012's series-level transfer). Sprint 018
  consumes `eq11` only (plus sprint 008's annulus-density
  splitting plumbing, which is `eq11`-agnostic).
* **Disk-side machinery.** Sprint 017 needs the algebraic collapse
  `branch2SigmaKernel c ρ · ρ² = c⁴/2`, the `Z_{ρ₁} ≥ 0`
  positivity, the series-level `Z`-monotonicity transfer through
  `[ρ₁, ρ₂]`, and the integrability of
  `2ρ³·Z_{ρ'}/Λ(c,ρ')` on `[ρ₁, ρ₂]`. Sprint 018 needs **none of
  these** — its disk-side bound is the direct
  `branch2PointwiseFactor c Λ ρ · diskExcess ≤ circleGap ρ`,
  closing immediately upon integration against `2ρ` over a
  branch-2 sub-window.
* **Annulus-side machinery.** Sprint 017 produces an annulus
  *windowed* lower bound `annulusExcess ≥ ∫ 2ρ³·Z_{ρ'}/Λ(c,ρ')`
  via the `(8)+(9)`-derived chain. Sprint 018 produces an annulus
  *windowed slice* upper bound `annulusSlice ρ₁ ρ₂ ≥ diskExcess`
  via the direct `mass_mul_le_annulusSlice_of_integral_bound_ae`
  machinery. **Different annulus-side bridges.**
* **Premise count.** Sprint 017's witness existential carries 6
  conjuncts after the window membership: `IntervalIntegrable` on
  `[c, 1]`, `IntervalIntegrable` of `2ρ³Z_{ρ'}/Λ`, `IntervalIntegrable`
  of `2ρ³/Λ`, `Summable` at `ρ₂`, and the kernel inequality. Sprint
  018's witness existential carries **1** conjunct after the window
  membership: the mass inequality `1 ≤ ∫ scalarIntegrand2`. The
  global `IntervalIntegrable (annulusDensity paper.circleGap) volume
  c 1` is hoisted to the outer signature (matching sprint 008's
  shape). **Sprint 018 has the smallest witness existential of any
  branch-2 closing reducer in the workspace.**

Why this is **bounded enough for one Generator session**:

* The proof body is a **mechanical mirror** of sprint 008's body at
  `Reduction.lean:833-1067` — every step has a 1↔2 substitution.
  Estimate: ≤ 235 lines of Lean for the new theorem (sprint 008's
  body is ~234 lines and the branch-2 mirror is essentially line-by-line
  with the substitutions in the table above).
* No new Mathlib lemmas needed. Every Lean idiom used
  (`mass_mul_le_annulusSlice_of_integral_bound_ae`,
  `paperScalarIntegrand2_intervalIntegrable`,
  `annulusSlice_add_adjacent`, `annulusSlice_nonneg_of_ae`,
  `annulusDensity_nonneg_of_lt`, `paperLambda_pos`,
  `Measure.restrict_congr_set`, `Ioo_ae_eq_Icc`, `field_simp`,
  `ring`, `linarith`, `nlinarith`, `positivity`, `mul_le_mul_of_nonneg_left`,
  `mono_set`, `calc`) is **already verified at the cited line ranges
  in sprint 008** (`Reduction.lean:833-1067`).
* The integrability call `paperScalarIntegrand2_intervalIntegrable`
  is verified at `WangPaperSideConditions.lean:143` and has the same
  signature as `paperScalarIntegrand1_intervalIntegrable` (which
  sprint 008 invokes at `Reduction.lean:908`).
* The candidate side lemmas are 5–25 lines each (sprint 017's V17
  shows the V-side typechecking pattern). Total V18 size: ≤ 80 lines.

Why this beats the alternatives I considered:

* **A: Z-free version of sprint 017** (extract `Z_{ρ₁}` from both
  sides via sprint 011 monotonicity, leaving the kernel
  `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` literally Z-free). This is the
  natural "sprint 014 → sprint 010 evolution" applied to sprint
  017, and **sprint 017's contract explicitly designates this as
  sprint 018**. However, on closer inspection it is mostly a
  *refactor*: it does not derive a new sufficient condition, just
  rewrites sprint 017's existing condition with `Z_{ρ₁}` extracted
  via the same `mul_le_mul_of_nonneg_right` + `intervalIntegral.integral_mul_const`
  pattern already exercised in sprint 010 and sprint 014. The
  bulletin's current priority de-prioritizes "more-of-the-same"
  chain extensions; A's analytical content per Generator session
  is low (a Z-elimination is one structural step, not a new
  paper-equation chain). **Demoted as refactor — high-bandwidth
  but low-novelty.** Queue separately as **sprint 019** if the
  next planner judges Z-elimination valuable as a building block
  for a `paperLambda` envelope sprint.

* **C: Combined `eq5 + eq6` full-annulus disk bound.** Sprint 017's
  contract demoted this as "Mechanical disjunction of sprints 015
  and 016 via `if ρ ≤ branchSplit c then … else …`. No new
  analytical chain through `Section2Assumptions` — just a glue
  lemma." The demotion still applies. **Demoted as glue.**

* **D: New series-level continuity / left-edge limit lemmas for
  `s ↦ sigmaZeroMinus a b s`.** Demoted in sprints 016/017 as
  speculative, no concrete consumer queued. **Still demoted.**

* **E: `paperLambda` upper-envelope from `paper.eq7_paperK_formula`
  alone.** Speculative — `paperLambda` is defined in
  `KorenblumPaper.OneModePaperBridge` via Wang's complicated
  `M(c, ρ)` formula, and no closed-form upper envelope is exposed.
  Investigating the `OneModePaperBridge` interior is beyond a
  single Generator session. **Demoted: requires structural
  exploration before it can be queued as a contract.**

* **F: Numerical-oracle registration discharging the kernel
  `c⁴/2 ≤ ∫ 2ρ³/Λ` at the seed.** Would enable a literal `c_value`
  push at the seed via sprint 017 *or* sprint 018. But specifying
  the oracle correctly requires knowing the specific sub-window
  `[ρ₁, ρ₂]` and a closed-form `Λ`-bound shape — neither is
  currently established. **Demoted: queue after sprint 018
  establishes the second-route closure-from-mass reducer (sprint
  018 supplies the natural mass-side oracle target
  `1 ≤ ∫ scalarIntegrand2` with a strictly simpler integrand than
  sprint 017's kernel).**

* **G: A pure-`eq2` disk-side reducer (use only paper equation
  `(2)`).** Wrong direction — `eq2` is a *lower* bound on `Z(r)`,
  not an upper bound on `circleGap r`. **Demoted: wrong sign.**

* **H: A second `eq11`-based reducer using `eq11` plus a windowed
  `eq2`-style lower bound on `Z`.** Speculative — requires combining
  `(11)` with `(2)` in a non-obvious way, no concrete
  recipe yet. **Demoted: needs scratch exploration first.**

Compared to A–H, candidate B (this sprint, `valid_of_eq11_subinterval_branch2`)
maximises analytical novelty per bounded Generator session: it ships
the **first workspace consumer of Wang's printed equation `(11)`**, the
**first short closing chain `(7)+(11)` on the branch-2 sub-regime**,
and the **first cross-validation of two structurally disjoint
paper-equation paths to the same effective branch-2 kernel scalar
`c⁴/2`**. It uses **only existing trusted modules + pinned Mathlib +
already-verified Reduction.lean lemmas** in patterns directly mirrored
from sprint 008. No proposal needed.

### Note on the algebraic collapse

Sprint 008 has the analogous identity at `Reduction.lean:942-950`:

```lean
have hRewriteLHS :
    2 * ρ *
        (PaperAxioms.branch1PointwiseFactor c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
        * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
  unfold Korenblum.scalarIntegrand1 PaperAxioms.branch1PointwiseFactor
  field_simp
  ring
```

Sprint 018's analogue is **strictly simpler**: no `(ρ²−c²)` factor,
lower powers of `c`. The collapse should work with the same `unfold;
field_simp; ring` pattern:

```lean
have hRewriteLHS :
    2 * ρ *
        (PaperAxioms.branch2PointwiseFactor c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c) =
      Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ
        * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c := by
  unfold Korenblum.scalarIntegrand2 PaperAxioms.branch2PointwiseFactor
  field_simp
  ring
```

Symbolically: `2 · ρ · (2ρ²/(c⁴·Λ) · D) = 4ρ³·D/(c⁴·Λ) = scalarIntegrand2 · D`.
Both sides require `c⁴ ≠ 0` (i.e. `c ≠ 0`), which is `ne_of_gt
(by positivity)` from `hc_pos`.

### Note on `paperScalarIntegrand2_intervalIntegrable`

The sprint 008 invocation at `Reduction.lean:908-910` is:

```lean
have hModeInt :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      volume ρ₁ ρ₂ :=
  WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
    hc_pos hρ₁₂ hcρ₁.le (le_trans hρ₂_split hSplit_le_one)
    paper.eq7_paperK_formula
```

For sprint 018 the analogue is:

```lean
have hModeInt :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ)
      volume ρ₁ ρ₂ :=
  WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable
    hc_pos hρ₁₂ (le_trans hSplit_gt_c.le hSplit_lt_ρ₁.le) hρ₂_lt_one.le
    paper.eq7_paperK_formula
```

where `hSplit_gt_c : c < branchSplit c` is derived from
`Real.sqrt(4/3) > 1` (already used inline in sprint 017's body at
`Reduction.lean:1963-1972` — copy that block).

Both calls have the same signature `(hc, hab, hca, hb1, hPaperK)`.
Note `paper.eq7_paperK_formula : Eq7PaperKFormula K c` is
definitionally equal to `WangKernelExact.PaperKFormula K c`, so it
should be passed directly without unfolding.

### Note on the side-slice non-negativities

Sprint 008 splits `annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂
+ annulusSlice ρ₂ 1` and discharges the side-slice non-negativities via
`annulusSlice_nonneg_of_ae` after deriving `annulusDensity ≥ 0` on each
side slice via `annulusDensity_nonneg_of_lt`. The argument is
**branch-agnostic**: the side slices `[c, ρ₁]` and `[ρ₂, 1]` lie in
`(c, 1)` regardless of branch. Sprint 018 reuses **verbatim** the
side-slice non-negativity proofs from sprint 008 (`Reduction.lean:1019-1052`),
adjusted only for the new derivation of `c < ρ₁` (now via
`hSplit_gt_c.trans hSplit_lt_ρ₁`).

### Note on the witness window at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value ≈ 0.4103`.
* Any `ρ₁, ρ₂` with `0.4103 < ρ₁ ≤ ρ₂ < 1` is admissible. Natural
  witness choice: `(ρ₁, ρ₂) = (5/10, 7/10) = (0.5, 0.7)`. V14 and
  V17 already exercise this window with `ρ₁ = 0.5 > branchSplit
  c_value`, so the witness is already verified feasible at the seed.

### Note on what the witness lemma should NOT do

Sprint 018's V18 witness lemma is **structural only** — it confirms
that the admissible-window predicate `branchSplit c_value < ρ₁ ≤ ρ₂ < 1`
is non-vacuous at the seed by exhibiting concrete `ρ₁, ρ₂`. It
**does NOT discharge any of the integrability premises, nor the mass
premise `1 ≤ ∫ scalarIntegrand2`**. Those remain as existential
hypotheses on the new reducer, just like V8/V14/V17's witnesses do
not discharge their respective sprints' premises.

Discharging the mass inequality `1 ≤ ∫_{ρ₁..ρ₂} scalarIntegrand2`
numerically at the seed would require either an explicit `paperLambda`
upper envelope (alternative E) or a numerical oracle (alternative F),
both out-of-scope for sprint 018.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_eq11_subinterval_branch2` matching the shape above.
    The proof body must:

    1. **Open `valid_of` framework.** `refine ⟨hc_pos, hc_lt_one, ?_⟩;
       intro a b K paper; obtain ⟨ρ₁, ρ₂, hSplit_lt_ρ₁, hρ₁₂, hρ₂_lt_one,
       hMass⟩ := h_window paper`.

    2. **Geometric scaffolding.** Derive `hSplit_gt_c : c <
       branchSplit c` (block from sprint 017's body, lines 1963-1972)
       and the consequent geometric lemmas `hcρ₁`, `hcρ₂`,
       `hSplit_le_one`, `hc_le_ρ₁`, `hc_le_ρ₂`, `hρ₁_lt_one`,
       `hρ₁_le_one`, `hρ₂_le_one`, `hc_le_one`.

    3. **Global annulus-density integrability.** `have hIntCircle :=
       hIntDensity paper`.

    4. **Sub-interval integrability of `annulusDensity` via `mono_set`.**
       Mirror sprint 008's `huIcc_…` and `hIntDens_…` blocks
       (`Reduction.lean:871-902`).

    5. **Sub-interval integrability of `scalarIntegrand2` via the
       paper hook.** Use
       `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`
       with `hca := le_trans hSplit_gt_c.le hSplit_lt_ρ₁.le` and
       `hb1 := hρ₂_lt_one.le`.

    6. **Pointwise bound on `Ioo ρ₁ ρ₂`.** Mirror sprint 008's
       `hPointwiseIoo` block (`Reduction.lean:913-955`), with the
       branch-2 paper equation, factor, and integrand substitutions
       per the table above. The algebraic collapse step uses
       `unfold Korenblum.scalarIntegrand2 PaperAxioms.branch2PointwiseFactor;
       field_simp; ring`.

    7. **`Ioo → Icc` lift.** Verbatim from sprint 008
       (`Reduction.lean:957-985`).

    8. **`mass_mul_le_annulusSlice_of_integral_bound_ae`.** Verbatim
       from sprint 008 (`Reduction.lean:986-998`), with
       `modeIntegrand := fun ρ => Korenblum.scalarIntegrand2 c
       (WangOuter.paperLambda K c) ρ`.

    9. **Annulus-side splitting and slice non-negativities.** Verbatim
       from sprint 008 (`Reduction.lean:1004-1052`).

    10. **Final calc chain.** Mirror sprint 008's final calc
        (`Reduction.lean:1054-1066`).

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 018's
    `valid_of_eq11_subinterval_branch2` is the workspace's **first
    consumer of Wang's printed equation `(11)`**, the **first
    closing reducer reaching the branch-2 sub-regime via the short
    `(7)+(11)` chain** (no `(8)+(9)`+series machinery), and a
    cross-validation of the structurally disjoint
    `(6)+(8)+(9)+series` chain (sprint 017) on the **same**
    branch-2 sub-regime. Both chains converge on the same effective
    kernel scalar after expansion.

  * The body of `valid_of_eq11_subinterval_branch2` MAY invoke:

    * `paper.eq11_branch2_pointwise` (the unique direct paper-axiom
      consumption — this is the **whole point** of the sprint),
    * `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`,
    * `WangPaperSideConditions.paperLambda_pos`,
    * `AnnulusIntegralReduction.annulusDensity`,
    * `AnnulusIntegralReduction.annulusSlice`,
    * `AnnulusIntegralReduction.annulusSlice_add_adjacent`,
    * `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae`,
    * `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound_ae`,
    * `annulusDensity_nonneg_of_lt` (defined locally in
      `Reduction.lean` and used by sprint 008 — re-used verbatim),
    * `PaperAxioms.branch2PointwiseFactor`, `PaperAxioms.branchSplit`,
      `Korenblum.scalarIntegrand2` (definitional unfolding),
    * `Real.sqrt`, `Real.sq_sqrt`, `Real.sqrt_nonneg` (for the
      `branchSplit c > c` helper),
    * `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `IntervalIntegrable.mono_set`, `Measure.restrict_congr_set`,
      `Ioo_ae_eq_Icc`, `ae_restrict_iff' measurableSet_Ioo`,
      `field_simp`, `ring`, `linarith`, `nlinarith`, `positivity`,
      `calc`, `change`, `unfold`, `rw`, `simpa`,
      `Filter.Eventually.of_forall`.

    The body must **NOT** invoke any of the following forbidden
    references (these are the structural markers that the new
    reducer reaches closure through the **short `(7)+(11)` chain
    only**):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
      `paper.eq6_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`,
      `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`
      (the proof must use **only** `eq11` + `eq7` — the latter via
      `paper.eq7_paperK_formula`),
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
      `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`,
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
    * `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `branch1SigmaKernel`, `branch1PointwiseFactor`,
      `branch2SigmaKernel`, `liftGap`, `sigmaPlus`,
      `sigmaZeroMinus`, `sigmaMinus`.

    (Note: `WangOuter.paperLambda` and
    `WangPaperSideConditions.paperLambda_pos` are EXEMPT and ARE
    needed — they are named ingredients of `scalarIntegrand2` and
    the integrand non-negativity proofs. `Section2Assumptions` is
    EXEMPT — it is the input. `branch2PointwiseFactor` and
    `scalarIntegrand2` are EXEMPT — they appear in `eq11`'s shape
    and in the windowed mass premise respectively.)

  * The new theorem's signature MUST take *exactly*: `(hc_pos : 0 <
    c)`, `(hc_lt_one : c < 1)`, `(hSplit_lt_one : PaperAxioms.branchSplit c
    < 1)`, `(hIntDensity : ∀ {a b K} (paper : Section2Assumptions a b
    K c), IntervalIntegrable (annulusDensity paper.circleGap) volume
    c 1)`, and `(h_window : ∀ {a b K} (paper : Section2Assumptions a
    b K c), ∃ ρ₁ ρ₂ : ℝ, branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
    1 ≤ ∫ ρ in ρ₁..ρ₂, scalarIntegrand2 c (paperLambda K c) ρ)`.
    (This signature mirrors sprint 008 exactly with branch-1 →
    branch-2 substitutions.)

* `ProofRefinement/Korenblum/Candidates/V18.lean`:

  * `-- @parent V17`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V17).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V17).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer's signature compiles at the seed `c_value`:

    ```lean
    theorem v18_eq11_subinterval_branch2_compiles
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
              PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                (1 : ℝ) ≤
                  ∫ ρ in ρ₁..ρ₂,
                    Korenblum.scalarIntegrand2 c_value
                      (WangOuter.paperLambda K c_value) ρ) :
        ValidKorenblumBound c_value :=
      valid_of_eq11_subinterval_branch2
        c_value_pos c_value_lt_one hSplit_lt_one hIntDensity h_window
    ```

  * Additionally, prove a structural witness lemma confirming the
    branch-2 sub-regime is non-vacuous at the seed by exhibiting
    a concrete `(ρ₁, ρ₂)`:

    ```lean
    theorem v18_branch2_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          PaperAxioms.branchSplit c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨5 / 10, 7 / 10, ?_, ?_, ?_⟩
      · -- branchSplit c_value ≈ 0.4103 < 0.5 (mirror of V17 witness)
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

    The witness `(ρ₁, ρ₂) = (5/10, 7/10)` is identical to V14's and
    V17's window, enabling cross-reference and sharing the verified
    `branchSplit` bound.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify the new reducer's
    signature typechecks at the seed `c_value` and to demonstrate
    the branch-2 window is non-vacuous.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V17.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_017`.

### Note on the `hSplit_gt_c` derivation

Identical to sprint 017's body at `Reduction.lean:1963-1972`. Copy
the block verbatim:

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
```

### Note on `hcρ₁` derivation

`hcρ₁ : c < ρ₁ := lt_trans hSplit_gt_c hSplit_lt_ρ₁` — single-step
via the above helper.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V18.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V18.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V18 scores `≥` V17 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V18.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_eq11_subinterval_branch2' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one direct invocation of `paper.eq11_branch2_pointwise`,
   * exactly one invocation of `WangPaperSideConditions.paperScalarIntegrand2_intervalIntegrable`,
   * at least one invocation of `mass_mul_le_annulusSlice_of_integral_bound_ae`,
   * no direct reference to `paper.eq2_`, `paper.eq3_`, `paper.eq4_`,
     `paper.eq5_`, `paper.eq6_`, `paper.eq8_`, `paper.eq9_`,
     `paper.eq10_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_`,
     `paper.eq15_`,
   * no reference to any of the prior `valid_of_*` reducers
     (`valid_of_eq15`, `valid_of_eq12_eq13`,
     `valid_of_eq2_eq3_eq4_annulus_budget`,
     `valid_of_eq10_subinterval_branch1`,
     `valid_of_collapsed_disk_eq8_eq9_lower*`,
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`,
     `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`),
   * no reference to `sigmaZeroMinus_*`, `sigmaMinus_*`,
     `circleGap_inner_bound_*`, `circleGap_outer_lower_bound_*`,
     `diskExcess_upper_bound_*`, `annulusExcess_lower_bound_*`
     (these are the markers of the long `(6)+(8)+(9)+series` chain
     and must NOT appear in the short `(7)+(11)` chain).
6. `grep -n 'v18_eq11_subinterval_branch2_compiles\|v18_branch2_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V18.lean`
   returns at least two distinct matches.
7. The conclusion of `valid_of_eq11_subinterval_branch2` is exactly
   `ValidKorenblumBound c` (verify via `grep` of the theorem
   statement).
8. The `h_window` existential body in
   `valid_of_eq11_subinterval_branch2` contains:
   * the constraint `PaperAxioms.branchSplit c < ρ₁` (verify via `grep`),
   * the constraint `(1 : ℝ) ≤ ∫ ρ in ρ₁..ρ₂, Korenblum.scalarIntegrand2 c (WangOuter.paperLambda K c) ρ`
     (verify via `grep` of the mass inequality form).
9. The body of `v18_branch2_window_witness_at_seed` exhibits a
   concrete `(ρ₁, ρ₂)` with `ρ₁, ρ₂ ∈ ℝ` literals and
   `branchSplit c_value < ρ₁ ≤ ρ₂ < 1` (verify via `grep` of the
   theorem body for two numeric literals — `5 / 10`, `7 / 10`, or
   any other admissible pair).
10. The new theorem's `h_window` existential signature MUST NOT
    contain any of `Summable`, `sigmaZeroMinus`, `sigmaMinus`,
    `liftGap`, `circleGap a b`, `branch2SigmaKernel`, or `c ^ 4 / 2`
    — these are the structural markers of the long sprint 017
    chain and must be absent from the short sprint 018 chain
    (verify via `grep`).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V17.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no
  new import allowances).
* Building the Z-free version of sprint 017 (alternative A above —
  extracting `Z_{ρ₁}` from sprint 017's chain). Queue as **sprint
  019** if the next planner judges Z-elimination valuable as a
  building block for a `paperLambda` envelope sprint.
* Building the combined `eq5 + eq6` full-annulus disk bound
  (alternative C — mechanical disjunction, not a new chain).
* Discharging the mass inequality `1 ≤ ∫ scalarIntegrand2`
  numerically at the seed `c_value` — this requires a `paperLambda`
  envelope or a numerical oracle, both out of scope for this sprint.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires either a numerical
  closure of the mass inequality (out of scope above) or a
  qualitatively new analytical witness that closes the mass
  inequality from paper hypotheses alone.
* Any modification to sprint 008's `valid_of_eq10_subinterval_branch1`,
  sprint 017's `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`, or
  the locally-defined helpers `annulusDensity_nonneg_of_lt`,
  `annulusSlice_nonneg_of_ae`, `annulusSlice_add_adjacent` (these
  are consumed verbatim).
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against
  the current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 018 is
  purely structural.

## Time budget

≤ 35 minutes runtime. The new reducer is ~235 lines of Lean,
matching sprint 008's ~234 lines line-for-line with the branch-1 →
branch-2 substitutions in the table above. All tactics used are
*already verified* in sprint 008 at `Reduction.lean:833-1067` and in
sprint 017 at `Reduction.lean:1963-1972` (for the
`hSplit_gt_c` helper). The candidate side lemmas are 5–25 lines
each (including the witness at the seed). Total V18 size: ≤ 80 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* The `hSplit_gt_c : c < branchSplit c` derivation cannot be
  closed by `nlinarith` cleanly — fallback is to use
  `Real.one_lt_sqrt` / `Real.sqrt_lt'` style chaining or factor as
  a `private lemma branchSplit_gt_self_of_pos` immediately above
  the new theorem.
* The algebraic collapse `2ρ · branch2PointwiseFactor c Λ ρ =
  scalarIntegrand2 c Λ ρ` fails under `unfold; field_simp; ring`
  — fallback to explicit `div_mul_eq_mul_div` rewrites mirroring
  sprint 008's `Reduction.lean:942-950` pattern.
* The annulus-density side-slice non-negativity proofs fail to
  type-check — verify `annulusDensity_nonneg_of_lt` and
  `annulusSlice_nonneg_of_ae` signatures by reading the sprint 008
  callsites at `Reduction.lean:1019-1052`.
* `paperScalarIntegrand2_intervalIntegrable` cannot be invoked due
  to a signature mismatch (e.g. argument order) — verify the exact
  signature at `WangPaperSideConditions.lean:143-152` and adjust
  the call site accordingly.
* The witness lemma `v18_branch2_window_witness_at_seed` may
  struggle if `nlinarith` cannot bound `Real.sqrt (4/3)` from above
  by `13/10` cleanly — fallback to V17's verbatim pattern (already
  verified feasible in `Candidates/V17.lean:87-106`).
* Any of acceptance criteria 4, 5, 7, 8, 9, 10 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 5: `STATUS=BLOCKED` — that would defeat the
  "only `eq7` + `eq11` (via the integrability hook + the direct
  paper-axiom call)" structural guarantee.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
