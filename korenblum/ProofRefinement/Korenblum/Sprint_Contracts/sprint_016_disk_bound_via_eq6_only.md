# Sprint 016: Direct branch-2 disk-side single-`Z_ρ` upper bound via `eq6` only — `diskExcess ≤ branch2SigmaKernel c ρ · ρ²·sigmaZeroMinus a b ρ` on the branch-2 sub-regime, the workspace's first lemma to consume Wang's printed equation `(6)` and the first single-`Z` disk bound with a coefficient that is **constant in `ρ`** (`c⁴/2`)

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V15.lean`
**Target file**: `Candidates/V16.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_eq6
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hρ_split : PaperAxioms.branchSplit c < ρ)
    (hρ1 : ρ < 1) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch2SigmaKernel c ρ * ρ ^ 2 *
        PaperAxioms.sigmaZeroMinus a b ρ
```

The proof chain is genuinely tiny and **mirrors sprint 015 line-for-line**, with `eq5 → eq6` and `branch1SigmaKernel → branch2SigmaKernel`:

1. **Invoke `paper.eq6_branch2_sigmaReduction`** at `ρ` with `hρ_split`
   and `hρ1` to get
   `diskExcess (circleGap a b) c ≤ branch2SigmaKernel c ρ · sigmaMinus a b ρ`.
   Unfolding the definition `Eq6Branch2SigmaReduction` this is the
   pointwise inequality on the disk excess at any single
   `ρ ∈ (branchSplit c, 1)`. No integration, no `eq2`, no `eq3`,
   no `eq4`, no `eq5`, no integrability premise.

2. **Rewrite via sprint 005** `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ`
   to convert `sigmaMinus a b ρ = ρ²·sigmaZeroMinus a b ρ`.

3. **Combine** by `calc` to land at the stated bound. Done.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V16.lean` at the same `c = 0.3554` that compiles,
scores `≥ V15`, and *materialises* the new lemma in two side lemmas
`v16_diskExcess_upper_bound_via_eq6_compiles` and
`v16_branch2_witness_at_seed`. The sink theorem `korenblum_constant_search`
is still discharged via `valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. The first bullet of "axes worth exploring" reads
verbatim:

> chain different paper equations — try `eq3` decomposition + `eq4`
> `Σ⁺` bound + `eq8`/`eq9` lift bridges + `eq10`/`eq11` pointwise +
> `eq12`/`eq13` integrated forms in combinations the seed doesn't use,
> without going through `eq14_combined` or `Eq15ScalarBound`.

`paper.eq6_branch2_sigmaReduction` is — together with
`paper.eq11_branch2_pointwise` — one of the **only two paper hypotheses
that no existing workspace lemma in `Reduction.lean` consumes** (verified
by `grep -nE 'paper\.eq[0-9]+_' Reduction.lean | sort -u`, which shows
hits for `eq2`, `eq3`, `eq4`, `eq5`, `eq7`, `eq8`, `eq9`, `eq10`, `eq12`,
`eq13`, `eq14` — and **no** hits for `eq6` or `eq11`). Sprint 016 ships
the workspace's first consumer of `eq6`, retiring one of the last two
unconsumed paper hypotheses on the disk side and bringing the disk-side
paper-equation coverage to **complete** (eq2, eq3, eq4, eq5, eq6 all
consumed).

The new bound is qualitatively different from every prior disk-side
bound in the workspace along three independent axes:

1. **First disk-side bound on the branch-2 sub-regime
   `(branchSplit c, 1)`.** Every prior disk-side bound in the workspace
   targets either the full disk regime (sprints 003, 013) or the
   branch-1 sub-regime `(c, branchSplit c)` (sprints 002, 007, 015).
   The annulus regime `(branchSplit c, 1)` — which spans roughly
   `(0.41, 1)` at the seed `c = 0.3554`, i.e. about **60%** of the
   length of `(c, 1)` — currently has **no bespoke disk-side bound**.
   Sprint 016 fills this analytical gap: `diskExcess ≤ branch2SigmaKernel
   c ρ · ρ² · sigmaZeroMinus a b ρ` is valid for *any* single
   `ρ ∈ (branchSplit c, 1)`, the entire sub-regime sprints 015 and 008
   cannot reach.

2. **First disk-bound coefficient that is constant in `ρ` after the `ρ²`
   collapses with the kernel denominator.** Computing
   `branch2SigmaKernel c ρ · ρ² = (c⁴/(2·ρ²)) · ρ² = c⁴/2` shows that
   sprint 016's bound simplifies *algebraically* to

   ```
   diskExcess ≤ (c⁴/2) · sigmaZeroMinus a b ρ
   ```

   — a **constant-in-ρ coefficient** times the single Z value `Z_ρ`.
   Compare:

   * Sprint 007 (branch-1, branch-split sub-regime):
     `diskExcess ≤ (c⁶/6)/(ρ²−c²) · Z_ρ` — coefficient blows up as
     `ρ → c`.
   * Sprint 013 (full disk, ρ-free anchor):
     `diskExcess ≤ c⁴ · Z_c` — anchored at `c`, no ρ-parameter.
   * Sprint 015 (branch-1, branch-split sub-regime):
     `diskExcess ≤ branch1SigmaKernel c ρ · ρ² · Z_ρ
       = (c⁶/(6·(ρ²−c²))) · Z_ρ` — coefficient blows up as `ρ → c`.
   * **Sprint 016 (branch-2, beyond branch-split sub-regime):**
     `diskExcess ≤ (c⁴/2) · Z_ρ` — coefficient is `c⁴/2`, **independent
     of `ρ`** within the sub-regime. The bound is uniform across the
     entire branch-2 sub-regime: no blow-up, no `ρ`-tuning needed for
     coefficient sharpness. This is structurally new.

3. **Strict tightness comparison with sprint 013.** Sprint 013's bound
   `c⁴ · Z_c` and sprint 016's bound `(c⁴/2) · Z_ρ` are **directly
   comparable** because both have closed-form numerical coefficients.
   By sprint 011 monotonicity (`Z_c ≤ Z_ρ` for any `ρ ≥ c`), the ratio
   `(c⁴/2 · Z_ρ) / (c⁴ · Z_c) = (1/2)·(Z_ρ/Z_c) ≥ 1/2`. So sprint 016's
   bound is **at most a factor of 2 worse than sprint 013's** in the
   `Z`-anchor — and tighter than sprint 013 whenever `Z_ρ ≤ 2·Z_c`. Since
   sprint 011 only guarantees `Z_c ≤ Z_ρ` (no upper envelope), this
   tightness comparison depends on the instance, but the closed-form
   numerical relationship between sprints 013 and 016 is itself a new
   structural fact the workspace can now expose.

   Concretely, the closed-form ratio table on the branch-2 sub-regime is
   currently:

   ```text
   sprint 013:  diskExcess ≤ c⁴      · Z_c     (anchored at c, no ρ)
   sprint 016:  diskExcess ≤ (c⁴/2)  · Z_ρ     (anchored at any ρ in
                                                (branchSplit c, 1),
                                                coefficient constant in ρ)
   ```

   Sprint 016 demonstrates for the first time that on the branch-2
   sub-regime, the disk excess admits a `(c⁴/2)·Z_ρ`-shaped bound
   anchored at any outer point — qualitatively unlike sprint 015's
   branch-1 bound (which has the pathological `(ρ²−c²)` denominator).

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V16 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form upper bound on
  `diskExcess` that holds for *any* paper-faithful instance and any
  single `ρ ∈ (branchSplit c, 1)`.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma confirming the sub-regime is non-vacuous at the seed.

Why this is **not** "the same chain" as sprint 015:

* **Different paper hypothesis.** Sprint 015 invokes
  `paper.eq5_branch1_sigmaReduction`. Sprint 016 invokes
  `paper.eq6_branch2_sigmaReduction`. These are distinct, separately-
  axiomatised members of `Section2Assumptions` — Wang's paper handles
  them separately as branch-1 and branch-2 reductions.

* **Different regime of validity.** Sprint 015 holds on
  `(c, branchSplit c)`. Sprint 016 holds on `(branchSplit c, 1)`. The
  two sub-regimes are **disjoint** and **complementary** — together
  they cover the open annulus `(c, 1)` modulo the single boundary point
  `branchSplit c`. Sprint 015 *cannot* reach the branch-2 sub-regime.

* **Different closed-form coefficient shape.** Sprint 015's coefficient
  `c⁶/(6·(ρ²−c²))` blows up as `ρ → c` and decays as `ρ → 1`. Sprint
  016's coefficient `c⁴/2` is **constant in `ρ`**: it does not vary
  across the branch-2 sub-regime. This is a qualitatively different
  ρ-asymptotic profile.

* **Different downstream consumer behaviour.** Sprint 015's bound, when
  fused with sprint 005/006 + sprint 011/012 (the hypothetical
  follow-up reducer noted in sprint 015's "alternative D"), yields a
  Z-free kernel inequality `(c⁶/6)/(ρ₁²−c²) ≤ ∫…` — *literally
  identical* to sprint 010's kernel due to the algebraic coincidence
  noted in sprint 015's contract (the `branch1SigmaKernel·ρ²` collapse).
  Sprint 016's bound, when fused similarly, yields a fundamentally
  different kernel `(c⁴/2) ≤ ∫_{ρ₁..ρ₂} 2(ρ')³·Z_{ρ'}/(Λ·Z_ρ) dρ'` (or,
  after a Z_ρ extraction at left edge ρ₁, `(c⁴/2) ≤ ∫_{ρ₁..ρ₂}
  2(ρ')³/Λ(c,ρ') dρ'`) — same RHS shape as sprint 014's kernel but with
  a strictly larger LHS by a factor of `c⁴/2 / c⁴ = 1/2`. So **sprint
  016 produces a structurally distinct downstream reducer** rather than
  a renamed instance of an existing one.

Why this is **bounded enough for one Generator session**:

* The proof body is a textbook three-line chain: invoke `eq6`,
  rewrite via `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, conclude.
  Estimate: ≤ 15 lines of Lean for the new theorem — **identical** in
  size to sprint 015.

* No new Mathlib lemmas needed. The `simpa
  [PaperAxioms.Eq6Branch2SigmaReduction]` unfolding pattern is a
  *direct mirror* of sprint 015's `simpa
  [PaperAxioms.Eq5Branch1SigmaReduction]` at `Reduction.lean:1856`.
  Risk of "Mathlib lemma name mismatch" is essentially zero.

* The candidate side lemmas are one to three lines each. Total V16
  size: ≤ 50 lines.

Why this beats the alternatives I considered:

* **A: cross-chain reducer `valid_of_eq5_eq8_eq9_branch1_singleton`
  fusing sprint 015 with sprint 005/006.** Sprint 015's contract
  already noted this as the natural follow-up (its "alternative D").
  However, on careful inspection, the algebraic coincidence
  `branch1SigmaKernel c ρ · ρ² = (c⁶/6)/(ρ²−c²)` means that the
  resulting closing reducer (after Z-extraction at the left edge ρ₁)
  produces a Z-free kernel `(c⁶/6)/(ρ₁²−c²) ≤ ∫_{ρ₁..ρ₂} 2(ρ')³/Λ
  dρ'` — *literally the same kernel* as sprint 010's
  `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`. The reducer would be
  operationally a *renamed instance* of sprint 011/012's chain, with
  the disk-side ingredient swapped from sprint 007 to sprint 015 but
  no new analytical content. Demoted: novelty would be only at the
  proof-tree level, not at the analytical-chain level.

* **B: branch-2 mirror of sprint 008
  `valid_of_eq11_subinterval_branch2`.** Genuinely complements sprint
  008 (covers `[branchSplit c, 1]` instead of `[c, branchSplit c]`).
  Sprint 015's contract demoted this exact direction as "structurally
  a flavour clone of sprint 008 — every step has a 1↔2 substitution".
  That demotion still applies: a full closing reducer mirror of
  sprint 008 would re-derive the same `mass_mul_le_annulusSlice_*`
  +  `annulusSlice_add_adjacent` chain with `eq10 → eq11` and
  `branch1 → branch2` substitutions. Demoted as flavour clone.

* **C: closed-form `sigmaZeroMinus(0)` series identity.** Genuinely
  novel series-side axis but speculative — the workspace doesn't
  currently consume it anywhere, and the natural application
  (combining with `eq2` at `r = 0`) yields a strictly worse disk
  bound than sprints 003/007/013 in their respective regimes.
  Demoted: structural novelty without a useful downstream consumer.

* **D: continuity of `s ↦ sigmaZeroMinus a b s` on `[0, 1)` as a
  third series-level lemma.** Speculative — the workspace doesn't
  currently consume continuity. Filed mentally for a future sprint
  after a concrete consumer is identified.

* **E: prove `Eq15ScalarBound` in Lean for `c = 0.3554` symbolically
  to remove the seed axiom.** Pure numerical push against the existing
  chain — exactly what the bulletin de-prioritises.

* **F: discharge the kernel inequality of sprint 010/011/012/014
  symbolically by upper-bounding `paperLambda K c ρ` via a closed-form
  envelope.** Requires either a `WangPaperSideConditions.paperLambda_le_*`
  or a numerical oracle. The first lives outside the workspace
  allowlist; the second needs a `lemma.toml:[[oracles]]` entry that
  is not yet specified. Demoted: needs trust expansion.

* **G: discharge the single-point summability premise of
  sprints 012/014 via a geometric-tail comparison.** Would require a
  hypothesis bounding `‖b k‖` from above (e.g. `‖b k‖ ≤ M · R^k` for
  some `R < 1/ρ₂`), which is not part of `Section2Assumptions`.
  Demoted: needs ambient hypothesis not in the trust surface.

* **H: combined `eq5 + eq6` full-annulus disk bound.** This would
  ship a single bound

  ```
  diskExcess ≤ if ρ ≤ branchSplit c
                 then branch1SigmaKernel c ρ · ρ² · Z_ρ
                 else branch2SigmaKernel c ρ · ρ² · Z_ρ
  ```

  valid on the entire `(c, 1)` regime. It naturally requires sprint
  016 to land first (since it depends on the eq6 bound being
  available). Queue as a separate sprint 017 follow-up after sprint
  016 lands.

Compared to A–H, candidate I (this sprint) maximises analytical
novelty per bounded Generator session: it ships the **first workspace
lemma to consume Wang's `eq6`**, exposes a brand-new disk-side bound
shape (single-`Z_ρ`, single-`ρ` parameter, no integration, **constant
coefficient `c⁴/2` in `ρ`**, valid on the previously-uncovered
branch-2 sub-regime `(branchSplit c, 1)`), and provides a structurally
distinct downstream Z-free chain that does NOT reduce algebraically to
sprint 010's kernel. It uses **only existing trusted modules + pinned
Mathlib** in patterns already verified by sprints 005, 015. No proposal
needed.

### Note on the sub-regime `(branchSplit c, 1)` (open at both ends)

`Eq6Branch2SigmaReduction` is stated as `∀ ⦃ρ⦄, branchSplit c < ρ →
ρ < 1 → …` (strictly open at both ends, mirroring Wang's printed
statement). Sprint 016's hypothesis `(hρ_split : branchSplit c < ρ)`
and `(hρ1 : ρ < 1)` mirror this exactly. The closed boundaries
`ρ = branchSplit c` and `ρ = 1` are intentionally excluded — sprint
008 (`valid_of_eq10_subinterval_branch1`) handles the closed-boundary
case `ρ = branchSplit c` from the branch-1 side via `eq10`, which is
derived from `eq5 + eq8 + eq9`; sprint 016 stays at the raw `eq6`
level so the boundary is naturally open.

### Note on the closed-form coefficient simplification

The structural form `branch2SigmaKernel c ρ · ρ²` simplifies to:

```
branch2SigmaKernel c ρ · ρ²
  = (c⁴ / (2 · ρ²)) · ρ²
  = c⁴ / 2
```

Sprint 016 keeps the bound in the **structural form**
`branch2SigmaKernel c ρ * ρ² * sigmaZeroMinus a b ρ` rather than
the simplified form `(c⁴/2) · sigmaZeroMinus a b ρ`. This is
intentional: keeping the `branch2SigmaKernel`-named factor makes
the lemma a textbook restatement of `eq6` + the series identity,
which is the cleanest possible match for an inversion via
`paper.eq6_branch2_sigmaReduction`. A downstream sprint that wants
the simplified form can `simp only [branch2SigmaKernel]; ring` in
two lines. (In particular, the constant-in-ρ feature is available
to any consumer that performs this two-line collapse.)

### Note on the absence of `hc_pos`

`Eq6Branch2SigmaReduction` itself does not require `0 < c` — it is a
universal statement over `ρ` with two strict inequalities. Sprint
016's signature therefore does *not* need a separate `(hc_pos : 0 < c)`
hypothesis. This **mirrors sprint 015** exactly. If the Generator
finds that a single internal step requires positivity (it should not,
based on sprint 015's experience), the fallback is to add
`(hρ_pos : 0 < ρ)` derived from `lt_of_le_of_lt (Real.sqrt_nonneg _)
(by …)` — but the proof as sketched does not require any positivity
step.

### Note on what `Section2Assumptions` exposes

`paper.eq6_branch2_sigmaReduction` has type
`Eq6Branch2SigmaReduction c (PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c)
(PaperAxioms.sigmaMinus a b)`, which definitionally equals

```
∀ ⦃ρ : ℝ⦄, PaperAxioms.branchSplit c < ρ → ρ < 1 →
  PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
    PaperAxioms.branch2SigmaKernel c ρ *
      PaperAxioms.sigmaMinus a b ρ
```

The Generator should `simpa [PaperAxioms.Eq6Branch2SigmaReduction]
using paper.eq6_branch2_sigmaReduction (ρ := ρ) hρ_split hρ1` to
unfold the definition (mirroring the existing successful pattern at
`Reduction.lean:1850-1856` for `eq5`).

### Note on the branch-2 witness window at the seed

At the seed `c_value = 0.3554`:
* `branchSplit c_value = 0.3554 · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103`.
* Any `ρ ∈ (0.4103, 1)` is admissible. Natural witness choices:
  `ρ = 5/10 = 0.5`, `ρ = 7/10 = 0.7`, `ρ = 9/10 = 0.9`. Sprint 014's
  V14 already exercises a window `(5/10, 7/10)` with `ρ₁ = 5/10 >
  branchSplit c_value`, so the witness `ρ = 5/10` is already verified
  feasible by V14's `v14_window_witness_at_seed`.

Sprint 016 picks `ρ = 5/10` to keep the witness identical in numerical
shape to sprint 014's (allowing easy cross-reference in any downstream
sprint that combines the two), but the exact numeric value is not
load-bearing — any `ρ ∈ (0.4103, 1)` would do.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem `diskExcess_upper_bound_via_eq6`
    matching the shape above. The proof body must:

    1. Invoke `paper.eq6_branch2_sigmaReduction` at `ρ`:

       ```lean
       have h6 :=
         paper.eq6_branch2_sigmaReduction (ρ := ρ) hρ_split hρ1
       have h6_unfold :
           PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
             PaperAxioms.branch2SigmaKernel c ρ *
               PaperAxioms.sigmaMinus a b ρ := by
         simpa [PaperAxioms.Eq6Branch2SigmaReduction] using h6
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
             ≤ PaperAxioms.branch2SigmaKernel c ρ *
                 PaperAxioms.sigmaMinus a b ρ := h6_unfold
           _ = PaperAxioms.branch2SigmaKernel c ρ *
                 (ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ) := by
                 rw [hSigmaIdentity]
           _ = PaperAxioms.branch2SigmaKernel c ρ * ρ ^ 2 *
                 PaperAxioms.sigmaZeroMinus a b ρ := by ring
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 016's `diskExcess_upper_bound_via_eq6` is the
    workspace's **first lemma to consume Wang's printed equation `(6)`
    directly** and the **first disk-side bound on the branch-2
    sub-regime `(branchSplit c, 1)`**. It produces a single-`Z_ρ`,
    single-`ρ`, no-integration disk-side upper bound whose closed form
    `(c⁴/2) · Z_ρ` (after the algebraic collapse `branch2SigmaKernel c ρ
    · ρ² = c⁴/2`) is the **first workspace disk-bound coefficient that
    is constant in `ρ`**. The proof bypasses every integration step in
    sprints 002/003/007/013 and the entire branch-1 chain
    sprint 015 sits in, consuming only `paper.eq6_branch2_sigmaReduction`
    plus the sprint 005 series identity
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. Together with sprint 015,
    this completes the disk-side coverage of Wang's equations
    {`eq2`, `eq3`, `eq4`, `eq5`, `eq6`}.

  * The body of `diskExcess_upper_bound_via_eq6` MAY invoke:

    * `paper.eq6_branch2_sigmaReduction`,
    * `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (sprint 005),
    * `simpa`, `calc`, `rw`, `ring`,
    * `PaperAxioms.Eq6Branch2SigmaReduction` (definitional
      unfolding).

    The body must **NOT** invoke any of the following forbidden
    references (verify via `grep -nE` against the substring of the
    theorem body):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
      `paper.eq7_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`,
      `paper.eq11_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_`,
      `paper.eq15_` (the proof must use **only** `eq6`),
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
      `diskExcess_upper_bound_via_eq5`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `annulusExcess_lower_bound_of_eq8_eq9`,
      `sigmaZeroMinus_monotone_of_summable`,
      `sigmaZeroMinus_summable_of_summable_at_upper`,
      `sigmaZeroMinus_nonneg_of_pos`,
    * `WangOuter.paperLambda`,
      `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`,
      `branch1SigmaKernel`,
      `branch1PointwiseFactor`, `branch2PointwiseFactor`,
      `liftGap`.

    (Note: `branch2SigmaKernel` and `branchSplit` MAY appear in the
    proof body, since they are the named structural ingredients of
    `Eq6Branch2SigmaReduction` itself.)

  * The new theorem's signature MUST take *only*: `(paper :
    Section2Assumptions a b K c)`, an implicit `{ρ : ℝ}`,
    `(hρ_split : PaperAxioms.branchSplit c < ρ)`, and `(hρ1 : ρ < 1)`.
    It MUST NOT take `(hc_pos : 0 < c)`, `(hc_lt_one : c < 1)`,
    or any `IntervalIntegrable` premise — the absence of these is
    the structural marker that this bound bypasses every
    integration step.

* `ProofRefinement/Korenblum/Candidates/V16.lean`:

  * `-- @parent V15`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V15).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V15).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises
    the new theorem at a generic `Section2Assumptions` instance
    at the seed `c_value`:

    ```lean
    theorem v16_diskExcess_upper_bound_via_eq6_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ : ℝ}
        (hρ_split : PaperAxioms.branchSplit c_value < ρ)
        (hρ1 : ρ < 1) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          PaperAxioms.branch2SigmaKernel c_value ρ * ρ ^ 2 *
            PaperAxioms.sigmaZeroMinus a b ρ :=
      diskExcess_upper_bound_via_eq6 paper hρ_split hρ1
    ```

  * Additionally, prove a tiny structural witness lemma confirming
    the regime `branchSplit c_value < ρ < 1` is non-vacuous at the
    seed:

    ```lean
    theorem v16_branch2_witness_at_seed :
        ∃ ρ : ℝ, PaperAxioms.branchSplit c_value < ρ ∧ ρ < 1 := by
      refine ⟨5 / 10, ?_, ?_⟩
      · -- branchSplit c_value = c_value · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103
        show PaperAxioms.branchSplit c_value < (5 / 10 : ℝ)
        unfold PaperAxioms.branchSplit
        have h_pos : (0 : ℝ) < 4 / 3 := by norm_num
        have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (4 / 3) :=
          Real.sqrt_nonneg _
        have h_sq : Real.sqrt (4 / 3) ^ 2 = 4 / 3 :=
          Real.sq_sqrt (le_of_lt h_pos)
        -- Want: c_value · √(4/3) < 0.5, i.e. √(4/3) < 0.5/c_value ≈ 1.4068.
        -- Since √(4/3) ≈ 1.1547 < 1.41, we get the result.
        have hsqrt_lt : Real.sqrt (4 / 3) < (141 / 100 : ℝ) := by
          have h_sq_lt : (4 / 3 : ℝ) < ((141 / 100 : ℝ)) ^ 2 := by norm_num
          nlinarith [h_sq, hsqrt_nonneg, h_sq_lt]
        have hc : c_value = 3554 / 10000 := rfl
        rw [hc]
        nlinarith [hsqrt_lt, hsqrt_nonneg]
      · norm_num
    ```

    The witness `ρ = 5/10 = 0.5` satisfies `branchSplit c_value
    ≈ 0.4103 < 0.5 < 1`. If `nlinarith` cannot close the first
    inequality cleanly, the fallback is to use a smaller upper bound on
    `√(4/3)`, e.g. `√(4/3) < 1.16` via
    `Real.sqrt_lt'` and `1.16² = 1.3456 > 4/3 ≈ 1.3333`, then chain to
    `c_value · √(4/3) < 0.3554 · 1.16 ≈ 0.4123 < 0.5`. The Generator
    may also pick a larger witness like `ρ = 7/10` (which is the
    sprint 014 `ρ₂` value) for an even more comfortable margin if
    `nlinarith` struggles. The exact witness value is not load-bearing,
    only the structural fact that the sub-regime is non-vacuous.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify that the new lemma
    typechecks at the seed `c_value` and to demonstrate that the
    branch-2 sub-regime is non-vacuous at the seed.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no
  edits to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits
  to `Candidates/V0.lean`–`V15.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_015`.

### Note on the `simpa` unfolding

`paper.eq6_branch2_sigmaReduction (ρ := ρ) hρ_split hρ1` returns a
term of type `PaperAxioms.diskExcess (PaperAxioms.circleGap a b)
c ≤ PaperAxioms.branch2SigmaKernel c ρ * PaperAxioms.sigmaMinus
a b ρ` *up to definitional unfolding of
`Eq6Branch2SigmaReduction`*. Lean may or may not perform the
unfolding automatically. The `simpa
[PaperAxioms.Eq6Branch2SigmaReduction] using …` pattern forces the
unfolding (mirroring the existing successful pattern at
`Reduction.lean:1850-1856` for `eq5`). If that fails, the fallback
is:

```lean
have h6 :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      PaperAxioms.branch2SigmaKernel c ρ *
        PaperAxioms.sigmaMinus a b ρ :=
  paper.eq6_branch2_sigmaReduction hρ_split hρ1
```

(direct application, relying on `Eq6Branch2SigmaReduction` reducing
to the inequality form by `rfl`).

### Note on the witness `ρ = 5/10`

At the seed `c_value = 0.3554`:
* `branchSplit c_value = 0.3554 · √(4/3) ≈ 0.3554 · 1.1547 ≈ 0.4103`.
* `5/10 = 0.5` satisfies `0.4103 < 0.5 < 1`. ✓

The choice `ρ = 5/10` is the same numerical value as sprint 014's
`ρ₁` (the left edge of V14's witness window `(5/10, 7/10)`), enabling
a future cross-chain sprint that combines sprint 016's bound at
`ρ = 5/10` with sprint 014's window. Any `ρ ∈ (0.4103, 1)` would
suffice — the value is structural, not load-bearing.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V16.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V16.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V16 scores `≥` V15 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V16.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'diskExcess_upper_bound_via_eq6' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one use of `paper.eq6_branch2_sigmaReduction`,
   * exactly one use of `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   * no reference to `paper.eq2`, `paper.eq3`, `paper.eq4`,
     `paper.eq5`, `paper.eq7`, `paper.eq8`, `paper.eq9`,
     `paper.eq10`, `paper.eq11`, `paper.eq12`, `paper.eq13`,
     `paper.eq14`, `paper.eq15`,
   * no reference to `intervalIntegral.`, `IntervalIntegrable`,
     `integral_pow`, `integral_mono_on`, `integral_const_mul`,
     `integral_mul_const` (the proof must perform NO integration).
6. `grep -n 'v16_diskExcess_upper_bound_via_eq6_compiles\|v16_branch2_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V16.lean`
   returns at least two distinct matches (V16 invokes the new lemma
   in `v16_diskExcess_upper_bound_via_eq6_compiles` and exercises
   the branch-2 witness).
7. The body of `diskExcess_upper_bound_via_eq6` does NOT mention
   any of the forbidden references listed in "Concrete edits
   expected" (verify via `grep -nE` against the substring of the
   theorem body):
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
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
   `diskExcess_upper_bound_via_eq5`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaZeroMinus_monotone_of_summable`,
   `sigmaZeroMinus_summable_of_summable_at_upper`,
   `sigmaZeroMinus_nonneg_of_pos`,
   `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
   `Korenblum.scalarIntegrand1`, `Korenblum.scalarIntegrand2`,
   `branch1SigmaKernel`, `branch1PointwiseFactor`,
   `branch2PointwiseFactor`, `liftGap`.
   (`branch2SigmaKernel` and `branchSplit` are EXEMPT from this list —
   they are the named ingredients of `Eq6Branch2SigmaReduction` itself.)
8. The new `diskExcess_upper_bound_via_eq6` lemma's signature does
   NOT take any `IntervalIntegrable` premise, no `(hc_pos : 0 < c)`
   premise, no `(hc_lt_one : c < 1)` premise — verify by inspecting
   the signature. The full premise list is exactly
   `(paper : Section2Assumptions a b K c)`, `{ρ : ℝ}`,
   `(hρ_split : PaperAxioms.branchSplit c < ρ)`, `(hρ1 : ρ < 1)`.
   This is the structural marker that this bound bypasses every
   integration step.
9. The conclusion of `diskExcess_upper_bound_via_eq6` is exactly
   `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
   PaperAxioms.branch2SigmaKernel c ρ * ρ ^ 2 *
   PaperAxioms.sigmaZeroMinus a b ρ` (verify via `grep` of the
   theorem statement) — no parenthesisation differences, no
   reordering of factors, no extra constants, the
   `branch2SigmaKernel`-named factor is preserved (not pre-collapsed
   to the simplified `c⁴/2` form).
10. The body of `v16_branch2_witness_at_seed` exhibits a concrete
    `ρ ∈ (branchSplit c_value, 1)` (verify via `grep` of the theorem
    body for at least one numeric literal — `5 / 10`, `0.5`,
    `7 / 10`, `0.7`, or any other value strictly between
    `branchSplit c_value ≈ 0.4103` and `1`).

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V15.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no
  new import allowances).
* Building any reducer that combines sprint 016 with sprint 005/006
  into a closing chain (the natural follow-ups
  `valid_of_eq6_eq8_eq9_branch2_singleton`, or a cross-chain sprint
  fusing sprint 015 + sprint 016 into a full-window single-Z disk
  bound). Those reducers require non-trivial single-point disk vs
  windowed annulus constructions, comparable in size to sprint 016
  itself. Queue as separate sprints.
* Building the `eq11`-based branch-2 mirror
  `valid_of_eq11_subinterval_branch2` (the symmetric flavour-clone of
  sprint 008). As noted in the bulletin, full closing reducer mirrors
  are flavour clones; demoted permanently unless the branch-2 cone
  becomes load-bearing in a numerical push.
* Building the **combined** `eq5 + eq6` full-annulus disk bound
  (alternative H above). Queue as sprint 017 or later — depends on
  sprint 016 landing first.
* Pushing `c_value` upward in this sprint — the goal is the
  structural disk-side bound, not a numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against
  the current trust surface.
* Touching `Numerical_Library/` or `Scratch/`. Sprint 016 is
  purely structural — numerical work belongs in a separate sprint.
* Refactoring or simplifying sprints 001–015. Their lemmas are
  consumed verbatim. (Sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` is the only
  existing-Reduction.lean lemma sprint 016 invokes.)
* Generalising the new theorem to cover the closed boundaries
  `ρ = branchSplit c` or `ρ = 1` — `Eq6Branch2SigmaReduction` is
  open at both ends, mirroring Wang's printed statement.
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new disk bound. That requires the follow-up
  reducer (out of scope above) plus a chain that closes
  `ValidKorenblumBound` from a single-`ρ` disk bound on the
  branch-2 sub-regime.
* Composing sprint 016 with sprints 013 or 015 — sprints 013, 015,
  and 016 are all disk-side bounds; they are not directly composable
  with each other (they all bound the same LHS). The natural
  composition is sprint 016 + sprints 005/006 (annulus side), which
  is the queued follow-up.

## Time budget

≤ 25 minutes runtime. The new disk bound is ~15 lines of Lean,
**identical** in size to sprint 015's `diskExcess_upper_bound_via_eq5`
(~30 lines including the doc comment). All Mathlib idioms used
(`simpa [PaperAxioms.Eq6Branch2SigmaReduction]`, `calc`, `rw`, `ring`)
are *already verified* in sprint 015 at `Reduction.lean:1841-1869`.
The candidate side lemmas are one to three lines each. The structural
witness lemma is ≤ 15 lines (the only non-trivial step is bounding
`Real.sqrt (4/3)` from above by a rational, which is a standard
`nlinarith` / `Real.sq_sqrt` pattern — the *opposite* direction from
sprint 015's witness lemma, which bounded `√(4/3)` from below).

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `paper.eq6_branch2_sigmaReduction` does not unfold cleanly via
  `simpa [PaperAxioms.Eq6Branch2SigmaReduction]` — fallback is
  direct application without `simpa`, since
  `Eq6Branch2SigmaReduction c innerExcess sigmaMinus` is
  definitionally `∀ ⦃ρ⦄, branchSplit c < ρ → ρ < 1 →
  innerExcess ≤ branch2SigmaKernel c ρ * sigmaMinus ρ`, so
  `paper.eq6_branch2_sigmaReduction hρ_split hρ1` should give
  the inequality directly.
* `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ` should be a
  one-line invocation since the lemma takes only `(a b : ℕ → ℂ)
  (s : ℝ)` and is already in `Reduction.lean` at line 474.
* The final `calc` may fail on the last step if `ring` does not
  unify `branch2SigmaKernel c ρ * (ρ^2 * Z_ρ)` with
  `branch2SigmaKernel c ρ * ρ^2 * Z_ρ` (associativity). The
  fallback is `mul_assoc` or `ring_nf`.
* The `v16_branch2_witness_at_seed` may struggle if `nlinarith`
  cannot bound `Real.sqrt (4/3)` from above by `1.41` cleanly.
  Fallback: replace `5/10` with a larger witness, e.g.
  `7/10 = 0.7`, that satisfies `branchSplit c_value ≈ 0.4103 <
  7/10 < 1` more comfortably (in particular, `0.7 / c_value
  ≈ 1.97 ≫ √(4/3) ≈ 1.155`, so the `nlinarith` margin is
  enormous). Or: use `Real.sqrt_lt'` style chaining
  (`Real.sqrt_lt_sqrt`) explicitly.
* Any of acceptance criteria 4, 5, 6, 7, 8, 9, 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat
  the "only `eq6` + sprint 005" structural guarantee of this
  sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
