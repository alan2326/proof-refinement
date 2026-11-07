# Sprint 010: First `Z`-free sufficient condition for `ValidKorenblumBound` — common-`Z_ρ` extraction on top of sprint 009

**Created**: 2026-05-02 17:30 by Planner
**Parent candidate**: `Candidates/V9.lean`
**Target file**: `Candidates/V10.lean`
**Direction**: section2-proof

## Goal

Ship one *new generic Lean theorem* in `Proof/Reduction.lean` that produces
the workspace's **first `sigmaZeroMinus`-free sufficient condition** for
`ValidKorenblumBound c`. The new reducer specialises sprint 009's cross-chain
reducer by requiring the disk witness `ρ` to lie *inside* the annulus window
`[ρ₁, ρ₂]` together with a pointwise `Z`-monotonicity hypothesis
`∀ ρ' ∈ [ρ₁, ρ₂], sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ'` — under
which the common factor `Z_ρ ≥ 0` can be extracted from both sides of the
sprint 009 kernel inequality, leaving a sufficient condition that mentions
`c`, `ρ`, `ρ₁`, `ρ₂`, and `paperLambda K c ρ'` only — **no
`sigmaZeroMinus` symbol on either side**.

```lean
theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ ρ₁ ρ₂ : ℝ,
          c < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c ^ 2 ∧ ρ < 1 ∧
            c < ρ₁ ∧ ρ₁ ≤ ρ ∧ ρ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            (∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
              PaperAxioms.sigmaZeroMinus a b ρ
                ≤ PaperAxioms.sigmaZeroMinus a b ρ') ∧
            (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The proof body is structured (still bounded — see "Time budget"):

1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
2. `obtain ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁ρ, hρρ₂, hρ₂_lt_one,
   hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hZmono, hKernel⟩ :=
   h_witness paper`.
3. Derive the geometric scaffolding: `hρ₁₂ : ρ₁ ≤ ρ₂` from `hρ₁ρ.trans hρρ₂`,
   and the `0 ≤ Z_ρ` from `sigmaZeroMinus_nonneg_of_pos a b (lt_trans hc_pos
   hcρ)` (sprint 005's helper). Call this `hZρ_nonneg`.
4. **Discharge the sprint 009 kernel inequality** by multiplying the
   `Z`-free `hKernel` premise by `Z_ρ ≥ 0` on the left and dominating the
   resulting RHS by the `Z`-weighted integral via interval-integral
   monotonicity. Concretely:
   - **(a)** `(c⁶/6)/(ρ²−c²) · Z_ρ ≤ (∫ ρ' in ρ₁..ρ₂, 2ρ'³ / Λ(c,ρ')) · Z_ρ`
     by `mul_le_mul_of_nonneg_right hKernel hZρ_nonneg`.
   - **(b)** Pull `Z_ρ` inside the integral as a constant scalar:
     `(∫ ρ' in ρ₁..ρ₂, 2ρ'³/Λ(c,ρ')) · Z_ρ
        = ∫ ρ' in ρ₁..ρ₂, (2ρ'³/Λ(c,ρ')) · Z_ρ`
     via `intervalIntegral.integral_mul_const` (or
     `mul_comm` + `integral_const_mul`).
   - **(c)** Apply `intervalIntegral.integral_mono_on_of_le_Ioo` to upgrade
     the integrand from `(2ρ'³/Λ(c,ρ')) · Z_ρ` to
     `(2ρ'³/Λ(c,ρ')) · Z_ρ' = 2ρ'³·Z_ρ'/Λ(c,ρ')` using `hZmono` (the
     pointwise `Z_ρ ≤ Z_ρ'` inequality, restricted to `Ioo ρ₁ ρ₂` via
     `Set.mem_Icc.mpr ⟨hρ.1.le, hρ.2.le⟩`) and the non-negativity of the
     `2ρ'³/Λ(c,ρ')` factor (`WangPaperSideConditions.paperLambda_pos`
     plus `0 ≤ ρ'^3` from `ρ' > c > 0`). The two `IntervalIntegrable`
     premises (`hIntLambda` for the `Z`-free kernel, `hIntLambdaZ` for the
     `Z`-weighted kernel) are exactly what `integral_mono_on_of_le_Ioo`
     consumes.
   - Chain (a) → (b) → (c) to obtain
     `(c⁶/6)/(ρ²−c²)·Z_ρ ≤ ∫ ρ' in ρ₁..ρ₂, 2ρ'³·Z_ρ'/Λ(c,ρ')`.
5. **Invoke sprint 009 (`valid_of_collapsed_disk_eq8_eq9_lower`)** with the
   reconstructed kernel inequality. Specifically: build a `h_witness'`
   bundle for sprint 009 by re-packing `(ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1,
   hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambdaZ, …)` plus
   the kernel inequality from step 4, then apply
   `valid_of_collapsed_disk_eq8_eq9_lower hc_pos hc_lt_one h_witness'`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V10.lean` at the same `c = 0.3554` that compiles,
scores `≥ V9`, and *materializes* the new `Z`-free reducer in a side
lemma `v10_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_chain_compiles`
exercised against an abstract witness/integrability bundle (mirroring V9's
`v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles` pattern). The
sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — the strongest sprint outcome is a *new chain* that
produces a structurally distinct sufficient condition, not a numerical
push.

Sprint 009's reducer
`valid_of_collapsed_disk_eq8_eq9_lower` exposes a sufficient condition

```text
(c⁶/6)/(ρ²−c²) · Z_ρ
  ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')³ · Z_ρ' / Λ(c, ρ')
```

that mentions `Z_ρ` on the LHS *and* `Z_ρ'` inside the RHS integrand. To
turn that condition into something a future `c`-pushing sprint can attack
via *pure numerical work* (or a numerical oracle) one of these symbols
has to be eliminated. The **most general route** to elimination is the
common-factor extraction that sprint 009's "Why" section explicitly
calls out as follow-up route (b):

> common-`Z_ρ` factor extraction with the disk witness placed inside the
> annulus window

Sprint 010 implements that route, producing the workspace's first
sufficient condition

```text
(c⁶/6)/(ρ²−c²)
  ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')³ / Λ(c, ρ')
```

— a **purely numerical inequality** between two scalar quantities. The
LHS is a closed-form rational function of `c` and `ρ`. The RHS is an
integral over `[ρ₁, ρ₂] ⊆ (c, 1)` whose integrand is a closed-form
function of `c` and `ρ'`. **Both sides are independent of `Section2Assumptions`
data** (no `circleGap`, no `sigmaZeroMinus`, no `sigmaPlus` — only `c`
and `paperLambda K c ρ'`, where `paperLambda` is itself a closed-form
expression in `K` and the polar coordinates).

This is qualitatively new in three independent ways:

1. **First `Z`-free sufficient condition.** Every prior reducer in
   `Reduction.lean` retains `Z_·` (or `circleGap`, or `sigmaPlus`) on
   at least one side of its sufficient condition:
   - `valid_of_eq15`, `valid_of_eq12_eq13`,
     `valid_of_eq2_eq3_eq4_annulus_budget`, and sprint 008's
     `valid_of_eq10_subinterval_branch1` all retain `circleGap` (via
     `scalarIntegrand1`/`scalarIntegrand2` or via `annulusExcess`).
   - Sprint 009 retains `Z_ρ` on the LHS *and* inside the kernel.
   Sprint 010's sufficient condition mentions **none** of `circleGap`,
   `sigmaZeroMinus`, `sigmaPlus`, `sigmaMinus`, `diskExcess`, or
   `annulusExcess`. This is the workspace's first such condition and is
   the cleanest possible "shift the problem to a numerical comparison"
   move.
2. **Cross-window monotonicity premise.** The pointwise `Z`-monotonicity
   hypothesis `∀ ρ' ∈ [ρ₁, ρ₂], Z_ρ ≤ Z_ρ'` is a *structural* statement
   about the coefficient sequence `(b_n)` — namely, that
   `Σ |b_n|² ρ^{2n}` (the series defining `sigmaZeroMinus`) attains its
   minimum on `[ρ₁, ρ₂]` at the disk witness `ρ`. This is a clean
   monotonicity question separable from the analytical chain itself,
   and can be discharged in a future sprint either via a series-level
   lemma about `circleGapSeries` (the bulletin's "axes worth exploring"
   explicitly mentions `circleGapSeries` representation) or via a
   pointwise lower bound on `(b_n)`.
3. **Three downstream attack routes opened cleanly.** With the `Z`-free
   condition `(c⁶/6)/(ρ²−c²) ≤ ∫ 2ρ'³/Λ(c,ρ') dρ'` in hand, future
   sprints can:
     (i) **Bound `Λ(c, ρ')` from above by a closed-form `Λmax(c, ρ')`**
         (e.g. via `WangPaperSideConditions.paperLambda_le_of_witness`
         — which already exists in the trusted surface) and substitute
         to get `(c⁶/6)/(ρ²−c²) ≤ ∫ 2ρ'³/Λmax(c,ρ') dρ'`, which is a
         closed-form integral comparison.
     (ii) **Register a numerical oracle** returning a certified lower
          bound on `∫ 2ρ'³/Λ(c,ρ') dρ'` and discharge the inequality
          numerically — this is the workspace's first natural place to
          register an oracle since both sides are concrete functions of
          `c, ρ, ρ₁, ρ₂` alone.
     (iii) **Close the inequality symbolically** for a specific
           `(c, ρ, ρ₁, ρ₂)` by exhibiting an explicit antiderivative of
           `2ρ'³/Λ(c,ρ')` (possible if `paperLambda K c ρ'` has a
           tractable closed form, which `WangCertificateCore` exposes).

Why this is **not** a numerical-budget push:

- The triple `(ρ, ρ₁, ρ₂)` and the `Z`-monotonicity premise are
  exposed as `forall`/explicit hypotheses inside `h_witness`. No
  concrete tuple is committed.
- `c_value` stays at `3554/10000`; V10 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
- The sufficient condition the new theorem exposes is qualitatively
  different from sprint 009's — both `Z`-symbols are gone — not a
  tightening of an existing chain.

Why this is **not** "the same chain" as sprint 009:

- Sprint 009 produces the cross-chain glue. Sprint 010 produces a
  *strictly stronger* sufficient condition by a separate analytic
  move (factor extraction + integral monotonicity with a constant
  factor). The chain depth grows by one more analytic step, and the
  final symbol set on both sides is strictly smaller.
- The new structural ingredient is the *Z-monotonicity hypothesis*,
  which has not appeared in any prior sprint's premise list.

Why this is **bounded enough for one Generator session**:

- The proof body is genuinely tiny:
  * one `refine` + one `obtain` (≤ 5 lines of premise unpacking),
  * one `mul_le_mul_of_nonneg_right` to push `Z_ρ` to the right (1 line),
  * one `integral_mul_const` (or `integral_const_mul` after a
    `mul_comm`) to pull `Z_ρ` into the integral (1–2 lines),
  * one `integral_mono_on_of_le_Ioo` upgrading
    `(2ρ'³/Λ(c,ρ'))·Z_ρ` to `2ρ'³·Z_ρ'/Λ(c,ρ')` (≤ 10 lines including
    the pointwise non-negativity proof of `2ρ'³/Λ(c,ρ')` and the
    `hZmono` conjunction),
  * one application of `valid_of_collapsed_disk_eq8_eq9_lower` with the
    re-packaged `h_witness'` (≤ 8 lines of `refine ⟨…, …⟩`).
  Estimate: ≤ 40 lines of Lean in `Reduction.lean`.
- No new Mathlib lemmas needed beyond
  `intervalIntegral.integral_mul_const` /
  `intervalIntegral.integral_const_mul`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `mul_le_mul_of_nonneg_right`, and
  `WangPaperSideConditions.paperLambda_pos` (already used in sprints
  005, 008, 009).
- The candidate side lemma is a one-line application of the new
  theorem against an abstract witness bundle.
- The structural witness lemma is ≤ 5 lines using the same
  `4/10` disk witness as sprint 009 and a tiny window like
  `[4/10, 5/10]`.

Why this beats the obvious alternatives I considered:

- **A: closed-form `paperLambda` envelope reducer.** Would build a
  generic theorem of shape "if `paperLambda K c ρ' ≤ Λmax` on
  `[ρ₁, ρ₂]` then `∫ 2ρ'³·Z_ρ'/Λ(c,ρ') ≥ (1/Λmax)·∫ 2ρ'³·Z_ρ'`" and
  combine with sprint 009. **Demoted** because the new opaque thing
  (`Λmax`) is essentially the same shape as the old (a `Λ` value); the
  resulting condition still mentions `Z_ρ` on the LHS *and inside the
  RHS integrand*. Net symbol-elimination: zero. Less novel than
  candidate E.
- **B: weighted-integration generalisation of sprint 006.** Generalise
  sprint 006 to integrate against an arbitrary non-negative weight
  `w(ρ')` instead of the constant `2ρ` Jacobian. **Demoted** because
  the resulting upper bound doesn't directly close to `annulusExcess`
  unless `w ≡ 1`; would need a separate parallel sprint to use it.
- **C: equation `(3)` decomposition + `(4)` `Σ⁺` reducer producing a
  `sigmaPlus`-based disk-side bound** parallel to the existing
  `sigmaZeroMinus`-based one. Genuinely novel structural axis but
  *risky* for one Generator session — would require new lemmas about
  `circleGapSeries` and we have no `Scratch/`-side numerical evidence
  that the resulting bound is non-trivial. Better to file as a
  proposal first; if the next planner has Scratch/ evidence in hand,
  it becomes a great future sprint. Demoted to "future / needs Scratch
  evidence first".
- **D: branch-2 mirror of sprint 008** on `(branchSplit c, 1)`. Pure
  flavour-clone of sprint 008, exactly the "three flavours of the same
  chain" pattern the bulletin warns against. Demoted.
- **F: prove `Eq15ScalarBound` in Lean for `c = 0.3554`.** Pure
  numerical push against the existing chain — exactly what the
  bulletin de-prioritises.

Compared to A–F, candidate E (this sprint) maximises analytical
novelty per bounded Generator session: it produces the workspace's
first `Z`-free sufficient condition, uses *only existing lemmas* plus
two named Mathlib integral lemmas, and opens three independent
follow-up attack routes (closed-form `Λ` bound, registered numerical
oracle, or symbolic antiderivative).

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic theorem
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` matching the shape
    above. The proof body must:
      1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
      2. `obtain ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁ρ, hρρ₂,
          hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda,
          hZmono, hKernel⟩ := h_witness paper`.
      3. Derive `hρ₁₂ : ρ₁ ≤ ρ₂` (`hρ₁ρ.trans hρρ₂`) and
         `hZρ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ`
         (`sigmaZeroMinus_nonneg_of_pos a b (lt_trans hc_pos hcρ)`).
      4. Build the kernel inequality
         `(c^6/6)/(ρ^2 − c^2) · sigmaZeroMinus a b ρ
            ≤ ∫ ρ' in ρ₁..ρ₂, 2·(ρ')^3 · sigmaZeroMinus a b ρ'
                / paperLambda K c ρ'`
         in a `have hKernel'` via the three sub-steps spelled out in the
         "Goal" section (mul_le_mul_of_nonneg_right; integral_mul_const
         / integral_const_mul; integral_mono_on_of_le_Ioo with `hZmono`).
      5. Apply `valid_of_collapsed_disk_eq8_eq9_lower hc_pos hc_lt_one`
         to a re-packed `h_witness'` bundle that supplies `(ρ, ρ₁, ρ₂)`,
         all the geometric/integrability premises, and the new
         `hKernel'`.

  - The new theorem's body MAY invoke
    `valid_of_collapsed_disk_eq8_eq9_lower` (sprint 009),
    `sigmaZeroMinus_nonneg_of_pos` (sprint 005's helper),
    `WangPaperSideConditions.paperLambda_pos` (already used in sprints
    005, 008, 009), and the named Mathlib lemmas
    `intervalIntegral.integral_mul_const`,
    `intervalIntegral.integral_const_mul`,
    `intervalIntegral.integral_mono_on_of_le_Ioo`,
    `mul_le_mul_of_nonneg_right`. The body must NOT mention
    `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
    `paper.eq7_paperK_formula`, `paper.eq8_`, `paper.eq9_`,
    `paper.eq10_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
    `paper.eq14_combined`, `paper.eq15_`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
    `Korenblum.scalarIntegrand2`, `valid_of_eq15`,
    `valid_of_eq12_eq13`, `valid_of_eq2_eq3_eq4_annulus_budget`,
    `valid_of_eq10_subinterval_branch1`, `eq15_implies_disk_le_annulus`,
    `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
    `circleGap_outer_lower_bound_of_eq8_eq9`,
    `annulusExcess_lower_bound_of_eq8_eq9`,
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. The intent is that
    sprint 010 is a **pure refinement on top of sprint 009** — it
    reaches sprint 009 through `valid_of_collapsed_disk_eq8_eq9_lower`
    and never reaches into the layers below. (`sigmaZeroMinus_nonneg_of_pos`
    is the single permitted exception because non-negativity of
    `Z_ρ` is what justifies the `mul_le_mul_of_nonneg_right` step at
    the top of the refinement.)

  - Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 010 produces the workspace's **first
    `Z`-free sufficient condition** for `ValidKorenblumBound c` — a
    condition that mentions `c, ρ, ρ₁, ρ₂` and `paperLambda K c ρ'`
    only, with no `circleGap`, `sigmaZeroMinus`, `sigmaPlus`,
    `sigmaMinus`, `diskExcess`, or `annulusExcess` symbols on either
    side. The reducer specialises sprint 009 by requiring the disk
    witness `ρ ∈ [ρ₁, ρ₂]` and a pointwise `Z_ρ ≤ Z_ρ'` monotonicity
    hypothesis on the window. This opens three independent follow-up
    attack routes for a future `c`-pushing sprint without any
    trust-base expansion: (i) closed-form upper-bound substitution for
    `paperLambda K c ρ'` via
    `WangPaperSideConditions.paperLambda_le_of_witness`, (ii) a
    registered numerical-integration oracle on the now-purely-numerical
    `(c⁶/6)/(ρ²−c²) ≤ ∫ 2ρ'³/Λ(c,ρ')` inequality, or (iii) a symbolic
    antiderivative of `2ρ'³/Λ(c,ρ')`.

- `ProofRefinement/Korenblum/Candidates/V10.lean`:
  - `-- @parent V9`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0–V9).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V9; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v10_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_chain_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ ρ₁ ρ₂ : ℝ,
              c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 ∧
                c_value < ρ₁ ∧ ρ₁ ≤ ρ ∧ ρ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                IntervalIntegrable
                  (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c_value 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                (∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
                  PaperAxioms.sigmaZeroMinus a b ρ
                    ≤ PaperAxioms.sigmaZeroMinus a b ρ') ∧
                (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
                  ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_collapsed_disk_eq8_eq9_lower_Z_free
        c_value_pos c_value_lt_one h_witness
    ```

    so the new `Z`-free reducer is exercised at the seed `c_value`
    against an abstract witness bundle, but the sink theorem is still
    discharged via `valid_of_eq15`. The side lemma must NOT be
    `axiom`-ed and must NOT call the seed axiom. It exists purely to
    verify that the new reduction chain typechecks at the seed
    `c_value`.

  - Additionally, prove a tiny structural witness lemma confirming
    that the geometric scaffolding `c_value < ρ₁ ≤ ρ ≤ ρ₂ < 1` and
    `3ρ² ≤ 4c_value²` is non-vacuous at the seed (i.e. there exists a
    triple `(ρ, ρ₁, ρ₂)` satisfying all the disk-side and
    annulus-side constraints simultaneously, with `ρ ∈ [ρ₁, ρ₂]`):

    ```lean
    theorem v10_window_witness_at_seed :
        ∃ ρ ρ₁ ρ₂ : ℝ,
          c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 ∧
            c_value < ρ₁ ∧ ρ₁ ≤ ρ ∧ ρ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨4 / 10, 4 / 10, 5 / 10, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        norm_num [c_value]
    ```

    (Sanity check: `c_value = 0.3554`, `4·c_value² ≈ 0.50524`,
    `3·0.4² = 0.48 ≤ 0.50524`, and `0.3554 < 0.4 = 0.4 ≤ 0.5 < 1`.
    The witness lemma is local to V10 and is not used elsewhere — its
    purpose is to demonstrate that the geometric scaffolding of
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`'s `h_witness`
    premise is non-vacuous at the seed. The pointwise `Z`-monotonicity
    premise and the kernel inequality premise are not part of the
    geometric scaffolding and are intentionally not discharged here —
    they are the subject of future sprints.)

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V9.lean`,
  no edits to `Sprint_Contracts/sprint_001…sprint_009`.

### Note on the disk witness ρ inside the annulus window

The contract's `h_witness` premise fuses sprint 009's `(ρ, ρ₁, ρ₂)` triple
into the constrained shape `c < ρ₁ ≤ ρ ≤ ρ₂ < 1`. This is *deliberately
stronger* than sprint 009's contract, which kept `ρ` and `[ρ₁, ρ₂]`
independent. The whole point of sprint 010 is to exploit the constraint
that `ρ` lies inside `[ρ₁, ρ₂]` so the common factor `Z_ρ` can be pulled
out. A future sprint that instead loosens the relationship is welcome
but must rely on a different mechanism (e.g. a localised `Z_ρ`
substitution or a Z-free pointwise lower bound).

### Note on the two integrability premises

The contract takes **two** annulus-side integrability premises:
`hIntLambdaZ` (the `Z`-weighted kernel, identical to sprint 009's) and
`hIntLambda` (the `Z`-free kernel, new in sprint 010). Both must be
explicit because the proof uses both: `hIntLambdaZ` is forwarded to
sprint 009's reducer, and `hIntLambda` is consumed by the
`integral_mono_on_of_le_Ioo` step that lifts the `Z`-free integral to
the `Z`-weighted one. A future sprint that derives `hIntLambdaZ` from
`hIntLambda` plus boundedness of `sigmaZeroMinus` on the window would
collapse the two into one, but that derivation is not in scope here.

### Note on the `Z`-monotonicity premise

The premise `∀ ρ' ∈ Icc ρ₁ ρ₂, sigmaZeroMinus a b ρ ≤ sigmaZeroMinus
a b ρ'` is the new structural ingredient. It is naturally satisfied
when `ρ` is the left endpoint `ρ₁` of the window *and* `sigmaZeroMinus`
is non-decreasing on `[ρ, ρ₂]`. The latter is a property of the series
`Σ |b_n|² ρ^{2n}`, which is non-decreasing in `ρ` for any non-negative
coefficient sequence — but this is *not yet exposed* by
`Section2Assumptions`. A natural follow-up sprint is to prove
`sigmaZeroMinus_nondecreasing` from a representation lemma; until then,
the premise is taken explicitly. Future planners should treat the
`sigmaZeroMinus_nondecreasing` lemma as a high-value mid-term target
because it would discharge the entire `hZmono` premise from the witness
bundle.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V10.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V10.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V10 scores `≥` V9 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V10.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains:
   - exactly one use of `valid_of_collapsed_disk_eq8_eq9_lower`
     (sprint 009),
   - at least one use of either `mul_le_mul_of_nonneg_right` or
     equivalent monotonicity lemma,
   - at least one use of `intervalIntegral.integral_mono_on_of_le_Ioo`,
   - at least one of `intervalIntegral.integral_mul_const` or
     `intervalIntegral.integral_const_mul`.
6. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free' korenblum/ProofRefinement/Korenblum/Candidates/V10.lean`
   returns at least one match (V10 actually invokes the new reduction in
   its body, inside
   `v10_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_chain_compiles`).
7. The body of `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` does NOT
   mention any of the forbidden references listed in "Concrete edits
   expected" (the `paper.eq*_*`, `Korenblum.scalar*`, sub-layer
   `valid_of_*`, `eq15_implies_disk_le_annulus`, the
   `circleGap_*_bound_of_*`, `diskExcess_upper_bound_*`,
   `circleGap_outer_*`, `annulusExcess_lower_bound_*`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` set). The *only* allowed
   in-workspace references are
   `valid_of_collapsed_disk_eq8_eq9_lower` (sprint 009) and
   `sigmaZeroMinus_nonneg_of_pos` (sprint 005's helper). Verify with
   `grep -nE` against the substring of the theorem body.
8. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes sprint 009 at least once (the
   new `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` body must
   contain a match in addition to sprint 009's own definition site —
   so the count of matches strictly exceeds the count from before
   sprint 010).
9. `grep -n 'v10_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V10.lean`
   returns exactly one definition site (the small structural witness
   lemma confirming the geometric scaffolding is non-vacuous at the
   seed `c_value`).
10. The new theorem's signature is structurally a *strict refinement* of
    sprint 009's: the `h_witness` bundle includes the strict ordering
    `c < ρ₁ ≤ ρ ≤ ρ₂ < 1` (verified by the presence of `ρ₁ ≤ ρ` and
    `ρ ≤ ρ₂` substring constraints in the witness shape, distinguishable
    from sprint 009's `c < ρ₁` ∧ `ρ₁ ≤ ρ₂` ∧ `ρ₂ < 1`), and contains
    *both* the `Z`-weighted and `Z`-free integrability premises plus the
    pointwise `Z`-monotonicity hypothesis. Verify by:
    `grep -A 25 'theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean | grep -E 'ρ₁ ≤ ρ|ρ ≤ ρ₂|sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ''`
    returns at least three matches (one for each substring).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`–`V9.lean`, or any file in
  `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
- Discharging *any* of the four explicit premises in `h_witness` from
  `Section2Assumptions`: the two integrability premises (`hIntLambdaZ`,
  `hIntLambda`), the pointwise `Z`-monotonicity premise (`hZmono`), or
  the kernel inequality premise (`hKernel`). They are intentionally
  taken as explicit premises packed into `h_witness`. Deriving any of
  them in-house is the subject of a separate sprint.
- Discharging the `Z`-monotonicity premise via a generic
  `sigmaZeroMinus_nondecreasing` lemma. That lemma is the natural
  high-value follow-up but requires reaching into `Section2Assumptions`
  / `circleGapSeries` representation work that is too large for this
  sprint. File as a separate sprint (or proposal) after sprint 010
  lands.
- Discharging the kernel inequality
  `(c^6/6)/(ρ^2 − c^2) ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 / paperLambda K c ρ' dρ'`
  itself. That is the explicit subject of a future sprint
  (numerical oracle, closed-form `paperLambda` envelope substitution,
  or symbolic antiderivative; see "Why" section, paragraph on future
  `c`-pushing routes).
- Choosing any concrete `(ρ, ρ₁, ρ₂)` triple beyond the V10 witness
  lemma `v10_window_witness_at_seed` (which only verifies the
  geometric scaffolding is non-vacuous; the integrability,
  `Z`-monotonicity, and kernel inequality premises are NOT
  discharged). The free parameters must remain `forall`-quantified
  inside `h_witness`.
- Refactoring or simplifying sprints 001–009. Their lemmas are
  consumed verbatim (sprint 010 only *adds* one new theorem and one
  V10 candidate).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`.
  That requires discharging the kernel inequality at the seed
  `c_value`, which is the subject of a future sprint.
- Adding a *Z-monotonicity-free* variant that uses a different
  factoring strategy (e.g. integrating against a constant lower
  bound). Strictly the common-factor extraction in this sprint.
- Adding a *symmetric* variant where instead of `Z_ρ ≤ Z_ρ'` we use
  `Z_ρ ≥ Z_ρ'` (and reverse the direction) — the inequality direction
  matters for the chain to close in the right direction.
- Pushing `c_value` upward in this sprint — the goal is the
  structural `Z`-free reducer, not a numerical push. Any future sprint
  that *does* push `c` is expected to consume
  `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` by proving the
  `Z`-free kernel inequality at the new `c` and exhibiting a window
  on which `Z` is non-decreasing.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.

## Time budget

≤ 35 minutes runtime. The new theorem is genuinely small: ~25–40
lines of Lean, since the heavy lifter (sprint 009) is already in
`Reduction.lean` with a contract that exactly accepts the
re-packaged witness bundle. The proof body is essentially one
`obtain` (~5 lines), three named `have`s for the `Z_ρ` extraction
chain (~15 lines including the pointwise non-negativity proof of
`2ρ'^3/Λ(c,ρ')` for `integral_mono_on_of_le_Ioo`), and one
application of `valid_of_collapsed_disk_eq8_eq9_lower` with the
re-packaged `h_witness'` (~10 lines). The candidate side lemma is
one line. The structural witness lemma is ≤ 5 lines using the
same `4/10` disk witness as sprint 009.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Sprint 009's `valid_of_collapsed_disk_eq8_eq9_lower`'s `h_witness`
  shape does not exactly match what we re-pack in step 5 (e.g. the
  order of premises in the existential is different from what's
  expected): re-read sprint 009's signature in `Reduction.lean` and
  re-pack the bundle in the exact order. The order in the contract
  above mirrors sprint 009's; if Lean disagrees, follow Lean.
- `intervalIntegral.integral_mul_const` does not exist in the pinned
  Mathlib (Lean 4 v4.28.0 / Mathlib v4.28.0): try
  `intervalIntegral.integral_const_mul` after a `mul_comm`, or
  use the calculation `∫ f · k = k · ∫ f` via `simp` with
  `intervalIntegral.integral_mul_const`-equivalent. If neither works,
  fall back to `Eq.trans` with an explicit
  `intervalIntegral.integral_congr` that pulls the constant out.
- `intervalIntegral.integral_mono_on_of_le_Ioo` requires both
  integrand integrability premises in a specific order; sprint 006
  already uses this exact lemma so the call shape is known to work.
  If a signature mismatch arises, mirror sprint 006's call site.
- The pointwise non-negativity of `2ρ'^3/Λ(c,ρ')` on `Ioo ρ₁ ρ₂`
  cannot be discharged with `WangPaperSideConditions.paperLambda_pos`
  + `pow_nonneg`: try the explicit
  `div_nonneg (by positivity) hΛpos.le`. If `paperLambda_pos`'s
  signature requires a `(K := K) (c := c) (ρ := ρ')` pattern and one
  of those is implicit, mirror the call from sprint 005's
  `circleGap_outer_lower_bound_of_eq8_eq9` (line ~534 of
  `Reduction.lean`).
- The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat the
  refinement-on-top-of-sprint-009 design of this sprint and
  indicates the contract needs revision.
- The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
- The structural witness lemma `v10_window_witness_at_seed` fails to
  close with `norm_num [c_value]`: try `decide` on each conjunct
  individually, fall back to explicit `nlinarith [c_value]`, or pick
  a slightly different `(ρ, ρ₁, ρ₂)` triple (e.g. `(38/100, 38/100,
  45/100)` instead of `(4/10, 4/10, 5/10)`). The triple `(4/10,
  4/10, 5/10)` is known to satisfy all seven conjuncts at
  `c_value = 0.3554`; if `norm_num` cannot close one of them, name
  it explicitly with `refine ⟨_, ?_, ?_, _, _, _, _⟩` and discharge
  the failing one with `nlinarith` or a manual chain.
- Any of acceptance criteria 4, 5, 6, 7, 8, 9, or 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
