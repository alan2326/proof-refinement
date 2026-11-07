# Sprint 015: Direct disk-side single-`Z_ρ` upper bound via `eq5` only — `diskExcess ≤ branch1SigmaKernel c ρ · ρ²·sigmaZeroMinus a b ρ` on the branch-1 sub-regime, the workspace's first lemma to consume Wang's printed equation `(5)`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V14.lean`
**Target file**: `Candidates/V15.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_eq5
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hcρ : c < ρ)
    (hρ_split : ρ < PaperAxioms.branchSplit c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch1SigmaKernel c ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ
```

The proof chain is genuinely tiny:

1. **Invoke `paper.eq5_branch1_sigmaReduction`** at `ρ` with `hcρ` and
   `hρ_split` to get
   `diskExcess (circleGap a b) c ≤ branch1SigmaKernel c ρ · sigmaMinus a b ρ`.
   Unfolding the definition `Eq5Branch1SigmaReduction` this is the
   pointwise inequality on the disk excess at any single
   `ρ ∈ (c, branchSplit c)`. No integration, no `eq2`, no `eq3`,
   no `eq4`, no integrability premise.

2. **Rewrite via sprint 005** `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ`
   to convert `sigmaMinus a b ρ = ρ²·sigmaZeroMinus a b ρ`.

3. **Combine** by `linarith`/`calc` to land at the stated bound. Done.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V15.lean` at the same `c = 0.3554` that compiles,
scores `≥ V14`, and *materialises* the new lemma in two side lemmas
`v15_diskExcess_upper_bound_via_eq5_compiles` and
`v15_branch_split_witness_at_seed`. The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. The first bullet of "axes worth exploring" reads
verbatim:

> chain different paper equations — try `eq3` decomposition + `eq4`
> `Σ⁺` bound + `eq8`/`eq9` lift bridges + `eq10`/`eq11` pointwise +
> `eq12`/`eq13` integrated forms in combinations the seed doesn't use,
> without going through `eq14_combined` or `Eq15ScalarBound`.

`paper.eq5_branch1_sigmaReduction` is the *one Section 2 hypothesis
that no existing workspace lemma in `Reduction.lean` consumes*
(verified by `grep -c 'paper\.eq5\|eq5_branch1_sigmaReduction'
Reduction.lean` returning `0`). Sprint 015 is the first workspace
lemma to tap it — strictly novel along this axis.

The new bound is qualitatively different from every prior disk-side
bound in the workspace along three independent axes:

1. **Single-step proof; no integration.** Every prior disk-side upper
   bound (sprints 002, 003, 007, 013) goes through the integration
   `∫_{0}^{c} 2r · circleGap a b r dr = diskExcess` and is built from
   a *pointwise* bound on `circleGap r` for `r ∈ Ioo 0 c`. Sprint 015
   bypasses this entirely: `eq5` is *already* an integrated statement
   that bounds `diskExcess` directly. **No `IntervalIntegrable`
   premise is needed**, no `intervalIntegral.integral_mono_on_*`
   step, no `@integral_pow` computation. The full proof is ~10 lines
   versus sprint 013's ~110 lines.

2. **Genuinely uses Wang's `(5)` for the first time in the
   workspace.** Every prior disk-side bound builds from
   `(eq3, eq4)` (sprints 002, 003, 007, 013) plus optionally `eq2`
   (sprints 002, 003, 007). Sprint 015 uses **only `eq5`**, plus the
   sprint 005 series identity `sigmaMinus = ρ²·sigmaZeroMinus`.
   Sprint 005's helper lemma `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
   is currently consumed only by sprint 005's own
   `circleGap_outer_lower_bound_of_eq8_eq9` and sprint 006's
   `sigmaZeroMinus_nonneg_of_pos`. Sprint 015 is its third consumer,
   in a fundamentally new context — the *disk* side rather than the
   annulus side.

3. **Provides a cross-check on sprint 007.** Sprint 007's
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
   establishes the bound `diskExcess ≤ (c⁶/6)/(ρ²−c²) · Z_ρ` on
   `(c, branchSplit c]` via the lengthy `(eq2 + eq3 + eq4)`
   integrated chain. Computing `branch1SigmaKernel c ρ · ρ² =
   (c⁶/(6·ρ²·(ρ²−c²))) · ρ² = c⁶/(6·(ρ²−c²))` shows that sprint 015's
   bound `branch1SigmaKernel c ρ · ρ² · Z_ρ` reduces to **exactly**
   `(c⁶/6)/(ρ²−c²) · Z_ρ` — the same closed-form scalar coefficient
   as sprint 007's bound. This is a striking paper-internal
   cross-check: Wang's `eq5` is the *integrated form* of the
   `(eq2 + eq3 + eq4)` chain on the branch-1 sub-regime. Sprints 007
   and 015 reach the same closed form by two structurally disjoint
   routes through `Section2Assumptions`.

   Concretely:

   ```text
   sprint 007:  (eq2 + eq3 + eq4) → integrate → drop Z_c on (c, branchSplit c]
                → (c⁶/6)/(ρ²−c²) · Z_ρ
   sprint 015:  eq5 → rewrite sigmaMinus = ρ²·Z_ρ
                → c⁶/(6·(ρ²−c²)) · Z_ρ           [same closed form]
   ```

   No prior workspace lemma exposes this equivalence. Sprint 015
   makes it provable inside the workspace by exhibiting the alternate
   route.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V15 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form upper bound on
  `diskExcess` that holds for *any* paper-faithful instance and any
  single `ρ ∈ (c, branchSplit c)`.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the regime is non-vacuous at the seed.

Why this is **not** "the same chain" as sprints 007 or 013:

* Sprint 007 reaches `(c⁶/6)/(ρ²−c²) · Z_ρ` by integrating the
  *pointwise inner-disk bound* `circleGap_inner_bound_of_eq2_eq3_eq4`
  and then dropping the `Z_c` term via sign analysis on the
  branch-split sub-regime. Sprint 015 reaches the same bound by
  invoking `eq5` directly — no integration, no pointwise bound on
  `circleGap r`, no sign analysis. Two completely disjoint proof
  trees in `Reduction.lean` that produce the same closed form.

* Sprint 013 ships the full-disk-regime single-`Z_c` bound `c⁴ · Z_c`
  by integrating the pointwise bound from `(eq3 + eq4)` only.
  Sprint 015 ships the branch-1-sub-regime single-`Z_ρ` bound by
  invoking `eq5` directly. Different regimes (full disk vs
  branch-1), different `Z`-anchor (`Z_c` vs `Z_ρ`), different
  coefficient (`c⁴` vs `c⁶/(6·(ρ²−c²))`), different paper hypotheses
  (`eq3 + eq4 + sprint 005` vs `eq5 + sprint 005`).

* Both new bounds are *complementary*: sprint 013's
  `c⁴ · Z_c` dominates sprint 015's bound on small `ρ` near `c`
  (where `(ρ²−c²) → 0` so sprint 015 blows up), and sprint 015's
  bound dominates on `ρ` near `branchSplit c` (where
  `c⁴·Z_c` vs `c⁶/(6·(ρ²−c²))·Z_ρ` is closer to a tie when
  `Z_ρ ≪ Z_c`). They are not redundant.

Why this is **bounded enough for one Generator session**:

* The proof body is a textbook three-line chain: invoke `eq5`,
  rewrite via `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, conclude.
  Estimate: ≤ 15 lines of Lean for the new theorem.

* No new Mathlib lemmas needed. The `simpa
  [PaperAxioms.Eq5Branch1SigmaReduction]` unfolding pattern is a
  syntactic mirror of sprint 008's `simpa
  [PaperAxioms.Eq10Branch1Pointwise]` at `Reduction.lean:920-927`
  and sprint 005's `simpa
  [PaperAxioms.Eq8SigmaToLiftGap]`-style usage. Risk of "Mathlib
  lemma name mismatch" is essentially zero.

* The candidate side lemmas are one to three lines each. Total V15
  size: ≤ 50 lines.

Why this beats the alternatives I considered:

* **A: branch-2 mirror sprint that ships `valid_of_eq11_subinterval_branch2`,
  the symmetric counterpart of sprint 008.** Genuinely complements
  sprint 008 (covers `[branchSplit c, 1]` instead of
  `[c, branchSplit c]`). However, it is *structurally a flavour
  clone* of sprint 008 — every step has a 1↔2 substitution. The
  bulletin explicitly de-prioritises "three flavours of the same
  chain". Demoted to a backup direction.

* **B: discharge the kernel inequality `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`
  symbolically by upper-bounding `paperLambda K c ρ` via a closed-form
  envelope.** Requires either a `WangPaperSideConditions.paperLambda_le_*`
  or a numerical oracle. The first lives outside the workspace
  allowlist; the second needs a `lemma.toml:[[oracles]]` entry that
  is not yet specified. Demoted: needs trust expansion.

* **C: discharge the single-point summability premise of
  sprints 012/014 via a geometric-tail comparison.** Would require
  a hypothesis bounding `‖b k‖` from above (e.g. `‖b k‖ ≤ M ·
  R^k` for some `R < 1/ρ₂`), which is not part of
  `Section2Assumptions`. Demoted: needs ambient hypothesis not in
  the trust surface.

* **D: build a cross-chain reducer
  `valid_of_eq5_eq8_eq9_branch1_singleton`** that fuses the new
  sprint 015 disk bound with sprint 005's annulus pointwise bound
  to ship a `ValidKorenblumBound`-closing reducer at a single
  `ρ ∈ (c, branchSplit c)`. This is a natural *follow-up* to
  sprint 015. However, it requires constructing an
  `annulusExcess` lower bound from a pointwise bound at a single
  point, which is non-trivial (sprint 006 integrates over an
  interval, not a single point) — combining the two requires a
  separate "single-point disk vs windowed annulus" reducer that
  picks `ρ ∈ [ρ₁, ρ₂]` and dominates `branch1SigmaKernel c ρ ·
  ρ² · Z_ρ ≤ ∫_{ρ₁..ρ₂} 2(ρ')³ · Z_{ρ'} / Λ(c, ρ') dρ'`. That is
  a separate sprint (sprint 016 candidate); sprint 015 ships the
  bound only.

* **E: closed-form `sigmaZeroMinus(0)` series identity.** Genuinely
  novel series-side axis but speculative — the workspace doesn't
  currently consume it anywhere, and the natural application
  (combining with `eq2` at `r = 0`) yields a strictly worse disk
  bound than sprints 003/007/013. Demoted: structural novelty
  without a useful downstream consumer.

* **F: prove `Eq15ScalarBound` in Lean for `c = 0.3554`
  symbolically.** Pure numerical push against the existing chain —
  exactly what the bulletin de-prioritises.

* **G: continuity of `s ↦ sigmaZeroMinus a b s` on `[0, 1)` as a
  third series-level lemma.** Speculative — the workspace doesn't
  currently consume continuity. Filed mentally for a future sprint
  after a concrete consumer is identified.

* **H: `eq6`-based branch-2 disk bound mirror of E.** Same as A —
  flavour-clone of sprint 015 but on the branch-2 sub-regime. After
  sprint 015 lands, this is a candidate for sprint 016 or 017 if
  the branch-2 cone becomes load-bearing in a future numerical
  push. Not for sprint 015.

Compared to A–H, candidate E (this sprint) maximises analytical
novelty per bounded Generator session: it ships the **first workspace
lemma to consume Wang's `eq5`**, exposes a brand-new disk-side bound
shape (single-`Z_ρ`, single-`ρ` parameter, no integration, no
integrability premise), and provides a paper-internal cross-check
that the existing sprint 007 bound coincides exactly with the
closed-form `eq5` bound. It uses **only existing trusted modules +
pinned Mathlib** in patterns already verified by sprints 005, 008.
No proposal needed.

### Note on the sub-regime `(c, branchSplit c)` (open at both ends)

`Eq5Branch1SigmaReduction` is stated as `∀ ⦃ρ⦄, c < ρ → ρ <
branchSplit c → …` (strictly open at both ends). Sprint 015's
hypothesis `(hcρ : c < ρ)` and `(hρ_split : ρ < branchSplit c)`
mirror this exactly. The closed boundary `ρ = branchSplit c` is
intentionally excluded — sprint 008 (`valid_of_eq10_subinterval_branch1`)
handles the closed-boundary case via `eq10`, which is derived from
`eq5 + eq8 + eq9`; sprint 015 stays at the raw `eq5` level so the
boundary is naturally open.

### Note on the Z-anchor differences

* Sprint 013 anchors `Z` at `c` (the disk radius itself). Bound:
  `c⁴ · Z_c`. Valid on full disk regime.
* Sprint 015 anchors `Z` at `ρ` (an outer point in the branch-1
  sub-regime). Bound: `(c⁶/(6·(ρ²−c²))) · Z_ρ`. Valid on
  `(c, branchSplit c)`.
* Sprint 007 (legacy) reaches sprint 015's closed form via the
  longer integration route.

The two new bounds (sprints 013, 015) are mutually incomparable:
each dominates in a different region of the `(c, ρ)` parameter
space. A future numerical sprint that searches over `ρ` may
legitimately prefer one over the other depending on the
relationship between `Z_c` and `Z_ρ`.

### Note on what `branch1SigmaKernel c ρ * ρ²` simplifies to

```
branch1SigmaKernel c ρ * ρ²
  = (c⁶ / (6 · ρ² · (ρ² − c²))) · ρ²
  = c⁶ / (6 · (ρ² − c²))
  = (c⁶ / 6) / (ρ² − c²)
```

Sprint 015 keeps the bound in the **structural form**
`branch1SigmaKernel c ρ * ρ² * sigmaZeroMinus a b ρ` rather than
the simplified form `(c⁶/6)/(ρ²−c²) · sigmaZeroMinus a b ρ`. This
is intentional: keeping the `branch1SigmaKernel`-named factor
makes the lemma a textbook restatement of `eq5` + the series
identity, which (a) is the cleanest possible match for an
inversion via `paper.eq5_branch1_sigmaReduction`, and (b) makes
the cross-check against sprint 007 *visible at the lemma name
level* without requiring the reader to perform the algebraic
collapse mentally. A downstream sprint that wants the simplified
form can `simp only [branch1SigmaKernel]; ring` in two lines.

### Note on the absence of `hc_pos`

`Eq5Branch1SigmaReduction` itself does not require `0 < c` — it is
a universal statement over `ρ` with two strict inequalities. Sprint
015's signature therefore does *not* need a separate `(hc_pos : 0 <
c)` hypothesis: `c < ρ` and `ρ < branchSplit c = c · √(4/3)` together
imply `c > 0` only when one already knows `c < c · √(4/3)`, which
requires `c > 0`. To keep the lemma fully general (so it can be
instantiated at any `c`), we simply *omit* `hc_pos` from the
signature; if `c ≤ 0`, the implication is vacuous in a useful sense
(the witness `ρ` cannot exist with both `c < ρ` and `ρ < c · √(4/3)`
when `c ≤ 0` because `c · √(4/3) ≤ c`). Mirror sprint 007's
signature, which *does* take `hc_pos` explicitly because its proof
uses it to derive `0 < ρ²−c²`; sprint 015's proof does not.

If the Generator finds that a single internal step requires
`(0 < ρ ∨ 0 < c)` (e.g. because of a `pow_two` positivity step),
the fallback is to add `(hρ_pos : 0 < ρ)` derived from
`lt_trans hcρ_dummy hcρ` if `hc_pos` is otherwise required —
but the proof as sketched does *not* require any positivity step.

### Note on what `Section2Assumptions` exposes

`paper.eq5_branch1_sigmaReduction` has type
`Eq5Branch1SigmaReduction c (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
(PaperAxioms.sigmaMinus a b)`, which definitionally equals

```
∀ ⦃ρ : ℝ⦄, c < ρ → ρ < PaperAxioms.branchSplit c →
  PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.branch1SigmaKernel c ρ *
      PaperAxioms.sigmaMinus a b ρ
```

The Generator should `simpa [PaperAxioms.Eq5Branch1SigmaReduction]
using paper.eq5_branch1_sigmaReduction (ρ := ρ) hcρ hρ_split` to
unfold the definition (mirroring the existing pattern at
`Reduction.lean:920-927` for `eq10` and `Reduction.lean:217-218`
for `eq3`).

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem `diskExcess_upper_bound_via_eq5`
    matching the shape above. The proof body must:

    1. Invoke `paper.eq5_branch1_sigmaReduction` at `ρ`:

       ```lean
       have h5 :=
         paper.eq5_branch1_sigmaReduction (ρ := ρ) hcρ hρ_split
       have h5_unfold :
           PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             PaperAxioms.branch1SigmaKernel c ρ *
               PaperAxioms.sigmaMinus a b ρ := by
         simpa [PaperAxioms.Eq5Branch1SigmaReduction] using h5
       ```

    2. Rewrite via sprint 005:

       ```lean
       have hSigmaIdentity :
           PaperAxioms.sigmaMinus a b ρ =
             ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ :=
         sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
       ```

    3. Conclude via `calc`:

       ```lean
       calc
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
             ≤ PaperAxioms.branch1SigmaKernel c ρ *
                 PaperAxioms.sigmaMinus a b ρ := h5_unfold
           _ = PaperAxioms.branch1SigmaKernel c ρ *
                 (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ) := by
                 rw [hSigmaIdentity]
           _ = PaperAxioms.branch1SigmaKernel c ρ * ρ ^ 2 *
                 PaperAxioms.sigmaZeroMinus a b ρ := by ring
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 015's `diskExcess_upper_bound_via_eq5` is
    the workspace's **first lemma to consume Wang's printed
    equation `(5)` directly**. It produces a single-`Z_ρ`,
    single-`ρ`, no-integration disk-side upper bound on
    `(c, branchSplit c)` whose closed form
    `(c⁶/(6·(ρ²−c²))) · Z_ρ` coincides with sprint 007's
    integrated bound — providing a paper-internal cross-check
    that Wang's `(5)` is the integrated form of the
    `(eq2 + eq3 + eq4)` chain on the branch-1 sub-regime. The
    proof bypasses every integration step in sprints 002/003/007/013,
    consuming only `paper.eq5_branch1_sigmaReduction` plus the
    sprint 005 series identity
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`.

  * The body of `diskExcess_upper_bound_via_eq5` MAY invoke:

    * `paper.eq5_branch1_sigmaReduction`,
    * `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (sprint 005),
    * `simpa`, `calc`, `rw`, `ring`,
    * `PaperAxioms.Eq5Branch1SigmaReduction` (definitional
      unfolding).

    The body must **NOT** invoke any of the following forbidden
    references (verify via `grep -nE` against the substring of
    the theorem body):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq6_`,
      `paper.eq7_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`,
      `paper.eq11_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_`,
      `paper.eq15_` (the proof must use **only** `eq5`),
    * `intervalIntegral.`, `IntervalIntegrable`, `integral_`,
      `volume`, `MeasureTheory.` (the proof must perform
      **no** integration step — the absence of any integration
      machinery is the structural marker that the proof is
      single-step),
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
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `annulusExcess_lower_bound_of_eq8_eq9`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`,
      `sigmaZeroMinus_nonneg_of_pos`,
    * `WangOuter.paperLambda`,
      `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`,
      `branch1PointwiseFactor`, `branch2PointwiseFactor`,
      `branch2SigmaKernel`, `liftGap`.

  * The new theorem's signature MUST take *only*: `(paper :
    Section2Assumptions a b K c)`, an implicit `{ρ : ℝ}`,
    `(hcρ : c < ρ)`, and `(hρ_split : ρ < PaperAxioms.branchSplit c)`.
    It MUST NOT take `(hc_pos : 0 < c)`, `(hc_lt_one : c < 1)`,
    or any `IntervalIntegrable` premise — the absence of these is
    the structural marker that this bound bypasses every
    integration step.

* `ProofRefinement/Korenblum/Candidates/V15.lean`:

  * `-- @parent V14`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V14).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V14).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises
    the new theorem at a generic `Section2Assumptions` instance
    at the seed `c_value`:

    ```lean
    theorem v15_diskExcess_upper_bound_via_eq5_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ : ℝ}
        (hcρ : c_value < ρ)
        (hρ_split : ρ < PaperAxioms.branchSplit c_value) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          PaperAxioms.branch1SigmaKernel c_value ρ * ρ ^ 2 *
            PaperAxioms.sigmaZeroMinus a b ρ :=
      diskExcess_upper_bound_via_eq5 paper hcρ hρ_split
    ```

  * Additionally, prove a tiny structural witness lemma
    confirming the regime `c_value < ρ < branchSplit c_value` is
    non-vacuous at the seed:

    ```lean
    theorem v15_branch_split_witness_at_seed :
        ∃ ρ : ℝ, c_value < ρ ∧ ρ < PaperAxioms.branchSplit c_value := by
      refine ⟨38 / 100, ?_, ?_⟩
      · norm_num [c_value]
      · -- branchSplit c_value = c_value · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103
        unfold PaperAxioms.branchSplit
        have hsqrt : (1.154 : ℝ) < Real.sqrt (4 / 3) := by
          rw [show (4 : ℝ) / 3 = (4/3 : ℝ) from rfl]
          have h_le : ((1.154 : ℝ)) ^ 2 < 4 / 3 := by norm_num
          have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
          nlinarith [Real.sq_sqrt (le_of_lt h_pos),
                     Real.sqrt_nonneg ((4 : ℝ) / 3)]
        nlinarith [hsqrt, Real.sqrt_nonneg ((4 : ℝ) / 3),
                   c_value_pos]
    ```

    The witness `ρ = 38/100 = 0.38` satisfies `c_value = 0.3554 <
    0.38` and `0.38 < branchSplit c_value ≈ 0.4103`. If `nlinarith`
    cannot close the second inequality cleanly, the fallback is to
    introduce a closed-form lower bound on `Real.sqrt (4/3)`, e.g.
    `1.15 < Real.sqrt (4/3)` via `Real.sqrt_lt_sqrt` and `1.15^2 =
    1.3225 < 4/3 ≈ 1.3333`, then chain to `0.38 < 0.3554 · 1.15 =
    0.40871`. The Generator may also use the simpler
    over-approximation `branchSplit c_value > c_value` (always true
    since `√(4/3) > 1`), giving the trivial witness `ρ = c_value +
    ε` for small `ε`; but that doesn't *exhibit* a `ρ` strictly
    less than `branchSplit c_value` at a numerical value the
    downstream consumer would actually use, so the explicit `38/100`
    witness is preferred.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify that the new lemma
    typechecks at the seed `c_value` and to demonstrate that the
    branch-1 sub-regime is non-vacuous at the seed.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V14.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_014`.

### Note on the `simpa` unfolding

`paper.eq5_branch1_sigmaReduction (ρ := ρ) hcρ hρ_split` returns a
term of type `PaperAxioms.diskExcess (PaperAxioms.circleGap a b)
c ≤ PaperAxioms.branch1SigmaKernel c ρ * PaperAxioms.sigmaMinus
a b ρ` *up to definitional unfolding of
`Eq5Branch1SigmaReduction`*. Lean may or may not perform the
unfolding automatically. The `simpa
[PaperAxioms.Eq5Branch1SigmaReduction] using …` pattern forces the
unfolding (mirroring the existing successful pattern at
`Reduction.lean:217-218` for `eq3` and `Reduction.lean:226` for
`eq4`). If that fails, the fallback is:

```lean
have h5 :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch1SigmaKernel c ρ *
        PaperAxioms.sigmaMinus a b ρ :=
  paper.eq5_branch1_sigmaReduction hcρ hρ_split
```

(direct application, relying on `Eq5Branch1SigmaReduction` reducing
to the inequality form by `rfl`).

### Note on the witness `ρ = 38/100`

At the seed `c_value = 0.3554`:
* `branchSplit c_value = 0.3554 · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103`.
* `38/100 = 0.38` satisfies `0.3554 < 0.38 < 0.4103`. ✓

The choice `ρ = 38/100` is deliberately *between* `c_value` and
`branchSplit c_value` to demonstrate the sub-regime is non-vacuous
at the seed. If a different witness is easier to discharge in
`nlinarith` / `Real.sqrt_lt_sqrt` / etc., the Generator may pick
any ρ ∈ (0.3554, 0.4103) — the exact value is not load-bearing,
only the structural fact that the sub-regime is non-vacuous.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V15.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V15.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V15 scores `≥` V14 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V15.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'diskExcess_upper_bound_via_eq5' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one use of `paper.eq5_branch1_sigmaReduction`,
   * exactly one use of `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   * no reference to `paper.eq2`, `paper.eq3`, `paper.eq4`,
     `paper.eq6`, `paper.eq7`, `paper.eq8`, `paper.eq9`,
     `paper.eq10`, `paper.eq11`, `paper.eq12`, `paper.eq13`,
     `paper.eq14`, `paper.eq15`,
   * no reference to `intervalIntegral.`, `IntervalIntegrable`,
     `integral_pow`, `integral_mono_on`, `integral_const_mul`,
     `integral_mul_const` (the proof must perform NO integration).
6. `grep -n 'v15_diskExcess_upper_bound_via_eq5_compiles\|v15_branch_split_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V15.lean`
   returns at least two distinct matches (V15 invokes the new lemma
   in `v15_diskExcess_upper_bound_via_eq5_compiles` and exercises
   the branch-1 witness).
7. The body of `diskExcess_upper_bound_via_eq5` does NOT mention
   any of the forbidden references listed in "Concrete edits
   expected" (verify via `grep -nE` against the substring of the
   theorem body):
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq6_`,
   `paper.eq7_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`,
   `paper.eq11_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_`,
   `paper.eq15_`,
   `intervalIntegral.`, `IntervalIntegrable`, `integral_pow`,
   `integral_mono_on`, `integral_const_mul`, `integral_mul_const`,
   `MeasureTheory.`, `volume`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
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
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaZeroMinus_monotone_of_summable`,
   `sigmaZeroMinus_summable_of_summable_at_upper`,
   `sigmaZeroMinus_nonneg_of_pos`,
   `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
   `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
   `branch1PointwiseFactor`, `branch2PointwiseFactor`,
   `branch2SigmaKernel`, `liftGap`.
8. The new `diskExcess_upper_bound_via_eq5` lemma's signature does
   NOT take any `IntervalIntegrable` premise, no `(hc_pos : 0 < c)`
   premise, no `(hc_lt_one : c < 1)` premise — verify by
   inspecting the signature. The full premise list is exactly
   `(paper : Section2Assumptions a b K c)`, `{ρ : ℝ}`,
   `(hcρ : c < ρ)`, `(hρ_split : ρ < PaperAxioms.branchSplit c)`.
   This is the structural marker that this bound bypasses every
   integration step.
9. The conclusion of `diskExcess_upper_bound_via_eq5` is exactly
   `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
   PaperAxioms.branch1SigmaKernel c ρ * ρ ^ 2 *
   PaperAxioms.sigmaZeroMinus a b ρ` (verify via `grep` of the
   theorem statement) — no parenthesisation differences, no
   reordering of factors, no extra constants, the
   `branch1SigmaKernel`-named factor is preserved (not pre-collapsed
   to the simplified `(c⁶/6)/(ρ²−c²)` form).
10. The body of `v15_branch_split_witness_at_seed` exhibits a
    concrete `ρ ∈ (c_value, branchSplit c_value)` (verify via
    `grep` of the theorem body for at least one numeric literal
    — `38 / 100`, `0.38`, or any other value strictly between
    `c_value` and `branchSplit c_value`).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V14.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no
  new import allowances).
* Building the natural follow-up reducer
  `valid_of_eq5_eq8_eq9_branch1_singleton` that fuses sprint 015
  with sprint 005 to ship a `ValidKorenblumBound`-closing chain
  at a single `ρ ∈ (c, branchSplit c)`. That reducer requires
  combining a single-`ρ` disk bound with a windowed annulus
  lower bound, which needs a new "single-point disk vs windowed
  annulus" reduction shape — comparable in size to sprint 015
  itself. Queue it as a separate sprint.
* Building the `eq6`-based branch-2 mirror
  `diskExcess_upper_bound_via_eq6` on `(branchSplit c, 1)`.
  Symmetric flavour-clone of sprint 015; bulletin
  de-prioritises this. May be queued later if branch-2 becomes
  load-bearing.
* Pushing `c_value` upward in this sprint — the goal is the
  structural disk-side bound, not a numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against
  the current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 015 is
  purely structural — numerical work belongs in a separate sprint.
* Refactoring or simplifying sprints 001–014. Their lemmas are
  consumed verbatim. (Sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` is the only
  existing-Reduction.lean lemma sprint 015 invokes.)
* Generalising the new theorem to cover the closed boundary
  `ρ = branchSplit c` — `Eq5Branch1SigmaReduction` is open at
  both ends, mirroring Wang's printed statement. The closed
  boundary is naturally covered by the derived `eq10` chain
  (sprints 008/014).
* Replacing the seed `valid_of_eq15` discharge of the sink
  theorem with a proof via the new disk bound. That requires
  the follow-up reducer (out of scope above) plus a chain that
  closes `ValidKorenblumBound` from a single-`ρ` disk bound.
* Composing sprint 015 with sprint 013 — both are disk-side
  bounds; they are not directly composable. The natural
  composition is sprint 015 + sprint 005 (annulus side), which
  is the queued follow-up.

## Time budget

≤ 25 minutes runtime. The new disk bound is ~15 lines of Lean,
roughly one-quarter the size of sprint 013's
`diskExcess_upper_bound_via_eq3_eq4` (~110 lines). All Mathlib
idioms used (`simpa [PaperAxioms.Eq5Branch1SigmaReduction]`,
`calc`, `rw`, `ring`) are *already verified* in sprints 005, 008
at `Reduction.lean:217-227, 920-927`. The candidate side lemmas
are one to three lines each. The structural witness lemma is
≤ 10 lines (the only non-trivial step is bounding
`Real.sqrt (4/3)` from below by a rational, which is a standard
`nlinarith` / `Real.sqrt_lt_sqrt` pattern).

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `paper.eq5_branch1_sigmaReduction` does not unfold cleanly via
  `simpa [PaperAxioms.Eq5Branch1SigmaReduction]` — fallback is
  direct application without `simpa`, since
  `Eq5Branch1SigmaReduction c innerExcess sigmaMinus` is
  definitionally `∀ ⦃ρ⦄, c < ρ → ρ < branchSplit c →
  innerExcess ≤ branch1SigmaKernel c ρ * sigmaMinus ρ`, so
  `paper.eq5_branch1_sigmaReduction hcρ hρ_split` should give
  the inequality directly.
* `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ` should be a
  one-line invocation since the lemma takes only `(a b : ℕ → ℂ)
  (s : ℝ)` and is already in `Reduction.lean` at line 474.
* The final `calc` may fail on the last step if `ring` does not
  unify `branch1SigmaKernel c ρ * (ρ^2 * Z_ρ)` with
  `branch1SigmaKernel c ρ * ρ^2 * Z_ρ` (associativity). The
  fallback is `mul_assoc` or `ring_nf`.
* The `v15_branch_split_witness_at_seed` may struggle if
  `nlinarith` cannot bound `Real.sqrt (4/3)` from below by `1.15`
  cleanly. Fallback: replace `38/100` with a smaller witness
  closer to `c_value`, e.g. `36/100`, that satisfies `c_value <
  36/100 < c_value · √(4/3)` more comfortably. Or: use
  `Real.sqrt_lt_sqrt`-style chaining (`Real.lt_sqrt` /
  `Real.sqrt_lt'`) explicitly.
* Any of acceptance criteria 4, 5, 6, 7, 8, 9, 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat
  the "only `eq5` + sprint 005" structural guarantee of this
  sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
