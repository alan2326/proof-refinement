# Sprint 011: First series-level monotonicity lemma for `sigmaZeroMinus`, used to discharge sprint 010's `Z`-monotonicity premise at the left-edge witness `ρ = ρ₁`

**Created**: 2026-05-02 18:00 by Planner
**Parent candidate**: `Candidates/V10.lean`
**Target file**: `Candidates/V11.lean`
**Direction**: section2-proof

## Goal

Ship two new generic Lean lemmas in `Proof/Reduction.lean`:

1. **A series-level monotonicity lemma**

   ```lean
   theorem sigmaZeroMinus_monotone_of_summable
       {a b : ℕ → ℂ} {s t : ℝ}
       (hs_nonneg : 0 ≤ s)
       (hst : s ≤ t)
       (hSummable_t :
         Summable (fun k : ℕ =>
           if PaperAxioms.n2Pred a b k then
             PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
           else 0)) :
       PaperAxioms.sigmaZeroMinus a b s ≤ PaperAxioms.sigmaZeroMinus a b t
   ```

   The proof unfolds `sigmaZeroMinus` to its `tsum` form, derives summability of
   the smaller series at `s` from that of the larger series at `t` via
   `Summable.of_nonneg_of_le` (each summand at `s` is non-negative and bounded
   above by the same summand at `t`), and applies `Summable.tsum_le_tsum` with
   the pointwise inequality on summands. Pointwise inequality on summands
   follows from:

   * **`n2Pred a b k` case:** `coeffMinusGap a b k = ‖b k‖² − ‖a k‖² > 0`
     (since `n2Pred a b k = (0 < k ∧ ‖a k‖ < ‖b k‖)`), hence
     `coeffMinusGap k * s^(2k-2) ≤ coeffMinusGap k * t^(2k-2)` by
     `mul_le_mul_of_nonneg_left` and `pow_le_pow_left hs_nonneg hst (2*k-2)`
     (`2k-2` is a `Nat`-subtraction with `0 < k` so it equals `2k-2 ≥ 0`; for
     `k = 0` the `n2Pred` branch is unreachable, so the `if` makes the case
     vacuous).
   * **`¬ n2Pred a b k` case:** both summands are `0`.

2. **A specialised left-edge reducer eliminating sprint 010's `hZmono` premise**

   ```lean
   theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
       {c : ℝ}
       (hc_pos : 0 < c)
       (hc_lt_one : c < 1)
       (h_witness :
         ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
           (paper : Section2Assumptions a b K c),
           ∃ ρ₁ ρ₂ : ℝ,
             c < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c ^ 2 ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
                 Summable (fun k : ℕ =>
                   if PaperAxioms.n2Pred a b k then
                     PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
                   else 0)) ∧
               (c ^ 6 / 6) / (ρ₁ ^ 2 - c ^ 2)
                 ≤ ∫ ρ' in ρ₁..ρ₂,
                     2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
       ValidKorenblumBound c
   ```

   The proof body:

   * `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free hc_pos hc_lt_one ?_;
     intro a b K paper`.
   * `obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one, hIntDisk,
     hIntCircle, hIntLambdaZ, hIntLambda, hSummable, hKernel⟩ := h_witness paper`.
   * Build the sprint 010 witness bundle by *re-using* `ρ = ρ₁`. Specifically,
     supply `(ρ₁, ρ₁, ρ₂)` as the `(ρ, ρ₁, ρ₂)` triple of sprint 010 and
     discharge `hZmono` via the new monotonicity lemma:

     ```text
     for ρ' ∈ Icc ρ₁ ρ₂,
       sigmaZeroMinus a b ρ₁
         ≤ sigmaZeroMinus a b ρ'      -- by sigmaZeroMinus_monotone_of_summable
                                       -- with s = ρ₁, t = ρ', hSummable ρ' (·∈ Icc ρ₁ ρ₂)
     ```

     The non-negativity hypothesis `0 ≤ ρ₁` follows from `lt_trans hc_pos hcρ₁`,
     and `ρ₁ ≤ ρ'` follows from `(Set.mem_Icc.mp hρ').1`.
   * `ρ₁ ≤ ρ₁` is `le_refl _`; `ρ₁ ≤ ρ₂` is `hρ₁₂`.
   * Finally, repackage and call
     `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V11.lean` at the same `c = 0.3554` that compiles,
scores `≥ V10`, and *materialises* both new lemmas in two side lemmas
`v11_sigmaZeroMinus_monotone_compiles` and
`v11_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_chain_compiles`
exercised against abstract witness/integrability bundles (mirroring V10's
`v10_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_chain_compiles` pattern).
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 010 produced the workspace's first `Z`-free
sufficient condition, but its closure required **three** explicit dangling
premises:

1. `hZmono : ∀ ρ' ∈ [ρ₁, ρ₂], sigmaZeroMinus a b ρ ≤ sigmaZeroMinus a b ρ'`
2. Two `IntervalIntegrable` premises (`hIntLambdaZ`, `hIntLambda`)
3. The Z-free kernel inequality
   `(c⁶/6)/(ρ²−c²) ≤ ∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ'`

Sprint 010's "Note on the Z-monotonicity premise" explicitly flags the first
premise as the natural mid-term target:

> A natural follow-up sprint is to prove `sigmaZeroMinus_nondecreasing` from
> a representation lemma; until then, the premise is taken explicitly. Future
> planners should treat the `sigmaZeroMinus_nondecreasing` lemma as a
> high-value mid-term target because it would discharge the entire `hZmono`
> premise from the witness bundle.

Sprint 011 is precisely that follow-up. It is qualitatively new along three
independent axes:

1. **First series-level lemma in the workspace.** Every prior sprint
   (001–010) treats `sigmaZeroMinus`, `sigmaPlus`, `sigmaMinus`, `circleGap`
   as **opaque functions** constrained only by the `Section2Assumptions`
   typeclass hypotheses (`eq2`–`eq14`). No prior sprint reaches into the
   actual `tsum` definitions in `KorenblumPaper.PaperAxioms`. Sprint 011
   opens this *entirely new analytical axis*: derive a property of
   `sigmaZeroMinus` from its **internal series structure** rather than from
   a paper-faithful axiom. The bulletin's "axes worth exploring" block
   explicitly mentions this axis ("work on the coefficient side via
   `sigmaPlus`/`sigmaMinus`/`sigmaZeroMinus` structure or the
   `circleGapSeries` representation instead of going through the integrated
   forms").

2. **Strict refinement of sprint 010's reducer with one structural premise
   eliminated.** The new reducer
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` strictly refines
   sprint 010 by *removing* the pointwise `Z`-monotonicity premise from the
   witness bundle, replacing it with a **purely series-side summability
   premise** `Summable (fun k => if n2Pred a b k then coeffMinusGap a b k *
   ρ' ^ (2*k-2) else 0)`. Summability is a clean *convergence* property,
   completely separable from any analytical chain — and is naturally
   satisfied for `ρ' < 1` on any sequence with reasonable decay. This is a
   **strictly cleaner premise shape**: a future sprint that wants to
   discharge it can do so via Cauchy/ratio/comparison tests, none of which
   require any paper-faithful structure.

3. **Direct support for a future c-pushing sprint.** With the monotonicity
   lemma in place, the path to a c-push becomes:

   * pick a window `[ρ₁, ρ₂] ⊂ (c, branchSplit c]` (e.g. `[0.4, 0.5]` at the
     seed),
   * verify the kernel inequality
     `(c⁶/6)/(ρ₁²−c²) ≤ ∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ'` numerically (via
     `Scratch/`-side SymPy/numerical integration first, then either
     symbolically in Lean or via a registered numerical-integration oracle),
   * supply summability of the `sigmaZeroMinus` series at each `ρ' ∈ [ρ₁,
     ρ₂]`. Summability of this kind of series is a standard Mathlib lemma
     for any `ρ' < 1` (geometric tail bound), and any future sprint can
     pull it straight from `Mathlib`.

   Sprint 010's `hZmono` premise was the **only** premise that could not be
   discharged from generic series/summability data — it required an
   ordering on values of an opaque function. Sprint 011 removes that
   asymmetry.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V11 still discharges the sink theorem via
  `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorems are purely structural: the series-level lemma is a
  generic monotonicity result that holds for *any* coefficient sequence
  `(a, b)`, and the new reducer is a generic specialisation of sprint 010
  that holds for *any* witness bundle.
* No concrete numerical tuple is committed.

Why this is **not** "the same chain" as sprint 010:

* Sprint 010's body re-packages sprint 009's witness bundle and applies
  scalar-extraction and integral monotonicity. Sprint 011's monotonicity
  lemma is an entirely new derivation that inspects the **`tsum`
  representation** of `sigmaZeroMinus`. The chain depth grows by one
  step into a previously unexplored layer (the actual coefficient series),
  and the final witness-bundle shape eliminates a structural premise
  rather than tightening the kernel inequality.
* The new reducer's witness bundle has *one fewer* structural premise
  than sprint 010's, replacing `∀ ρ' ∈ [ρ₁, ρ₂], Z_ρ ≤ Z_ρ'` with
  `∀ ρ' ∈ [ρ₁, ρ₂], Summable …`. The two are not interchangeable: the
  former is a statement *about the value* of an opaque function, the
  latter is a statement *about the convergence* of its defining series.

Why this is **bounded enough for one Generator session**:

* The series-level lemma's proof is genuinely small:
  * Unfold `sigmaZeroMinus` to the `tsum` form (`unfold` or `simp only`).
  * Pointwise inequality on summands (one `if`/`then`/`else` split, plus
    `mul_le_mul_of_nonneg_left` + `pow_le_pow_left` in the `n2Pred` branch,
    plus `le_refl` in the other branch).
  * Summability transfer from `t`-side to `s`-side via
    `Summable.of_nonneg_of_le` (each `s`-side summand is non-negative and
    `≤` the corresponding `t`-side summand).
  * Apply `Summable.tsum_le_tsum`.
  Estimate: ≤ 25 lines of Lean.

* The specialised reducer's proof is even smaller:
  * `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free hc_pos hc_lt_one ?_`
    + `intro a b K paper`.
  * `obtain` the new witness bundle.
  * Reconstruct sprint 010's witness bundle with `ρ = ρ₁`, discharging
    `hZmono` via the new monotonicity lemma applied pointwise.
  Estimate: ≤ 30 lines of Lean.

* The candidate side lemmas are one line each.

* No new Mathlib lemmas needed beyond `Summable.tsum_le_tsum` (used 8+
  times in pinned Mathlib, e.g. `MeasureTheory/VectorMeasure/Basic.lean:907`
  with the exact signature
  `Summable.tsum_le_tsum (h : ∀ a, f a ≤ g a) (hf : Summable f) (hg : Summable g)`),
  `Summable.of_nonneg_of_le`, `mul_le_mul_of_nonneg_left`,
  `pow_le_pow_left`. All of these are foundational Mathlib lemmas in the
  pinned toolchain (Lean 4 v4.28.0 / Mathlib v4.28.0).

Why this beats the obvious alternatives I considered:

* **A: closed-form `paperLambda` envelope substitution to discharge
  the kernel inequality.** Would need an *upper* bound on `paperLambda K c
  ρ'` to lower-bound the integrand `2ρ'³/Λ`. The trusted surface
  (`KorenblumPaper.{PaperAxioms, PaperEq15, OneModePaperBridge}`) exposes
  `paperLambda_ge_half : 1/2 ≤ paperLambda K c ρ` (from
  `WangPaperSideConditions`, which is *not* in the workspace allowlist
  directly but is transitively reachable via `PaperAxioms`'s import). That
  gives `1/Λ ≤ 2`, an *upper* bound on `1/Λ` — which gives an *upper*
  bound on the integrand, **the wrong direction** for proving the kernel
  inequality. The lemma we'd actually want — `paperLambda_le_of_witness`
  — lives in `WangCertificateCore`, which is **not on the allowlist**.
  Using it would require a `Proposals/` entry to expand
  `[workspace_import_policy]`. Demoted because it requires a non-oracle
  trust expansion that is not approved.

* **B: parallel `sigmaPlus` disk-side bound via `eq3 + eq4`.** Build a
  second disk-side upper bound that goes through `sigmaPlus` instead of
  `sigmaZeroMinus`, using `eq3 : circleGap = sigmaPlus − r²·sigmaZeroMinus`
  and `eq4 : sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c² · sigmaZeroMinus
  c`. Genuinely novel structural axis but **risky** for one Generator
  session: the resulting upper bound's coefficient signs need to be
  determined by hand (or in `Scratch/`), and there's no advance evidence
  that the resulting bound is non-trivial relative to sprint 003's
  `(2)+(3)+(4)` bound. Better to file as a future sprint after `Scratch/`-side
  numerical exploration. Demoted to "future / needs Scratch evidence first".

* **C: discharge one of the two integrability premises in sprint 010.**
  Would derive `IntervalIntegrable (fun ρ' => 2ρ'³ / Λ(c,ρ'))` on a
  closed sub-interval `[ρ₁, ρ₂] ⊂ (c, 1)` from the trusted surface's
  `paperLambda_aemeasurableOn_Icc` (in `WangPaperSideConditions`, again
  transitively reachable). Modest novelty — it just turns one
  `IntervalIntegrable` hypothesis into `MeasureTheory`-side data
  (continuity of `Λ`, polynomial integrand). Discharge route is mostly
  bookkeeping. Demoted relative to sprint 011: discharging the
  `Z`-monotonicity premise is a strictly more structural move (introduces
  series-level reasoning to the workspace), and discharging *one* of the
  two `IntervalIntegrable` premises still leaves the other
  (`hIntLambdaZ`, the `Z`-weighted kernel) undischarged. The integrability
  story is best handled in a separate later sprint when both can be done
  together.

* **D: branch-2 mirror of sprint 008** on `(branchSplit c, 1)`. Pure
  flavour-clone of sprint 008, exactly the "three flavours of the same
  chain" pattern the bulletin warns against. Demoted.

* **E: prove `Eq15ScalarBound` in Lean for `c = 0.3554` symbolically**
  to remove the `hEq15_seed_3554` axiom. Pure numerical push against the
  existing chain — exactly what the bulletin de-prioritises.

* **F: closed-form Lipschitz bound on `Λ(c, ρ)` over `ρ ∈ [ρ₁, ρ₂]`.**
  Would help with route (iii) of sprint 010's "Why" (symbolic
  antiderivative of `2ρ'³/Λ`), but the structural information about `Λ`'s
  local behaviour is in `WangCertificateCore`/`WangKernelExact` (not on
  the allowlist) — same trust-expansion blocker as candidate A.

Compared to A–F, candidate G (this sprint, with G1 = monotonicity lemma +
G2 = left-edge reducer) maximises analytical novelty per bounded Generator
session: it produces the *workspace's first series-level lemma* about
`sigmaZeroMinus`, eliminates a structural premise from sprint 010's
reducer (and therefore directly supports the next c-push), and uses
*only existing trusted modules* + pinned Mathlib. No proposal needed.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem `sigmaZeroMinus_monotone_of_summable`
    matching the shape above. The proof body must:

    1. Unfold `PaperAxioms.sigmaZeroMinus` to its `tsum` form. The
       definition uses `by classical; exact ∑' k, if … then … else 0`,
       so a `simp only [PaperAxioms.sigmaZeroMinus]` (or `unfold` +
       `show`) should expose the underlying `∑'`.
    2. Define the two summands

       ```text
       f s k = if PaperAxioms.n2Pred a b k then
                 PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
               else 0
       ```

       and `g k = f t k`.
    3. Show the pointwise inequality `f s k ≤ f t k` for all `k`. Two
       cases:

       * **`h : n2Pred a b k`**: from `n2Pred a b k = (0 < k ∧ ‖a k‖ <
         ‖b k‖)` derive `0 < coeffMinusGap a b k = ‖b k‖² − ‖a k‖²` via
         `sq_lt_sq'`/`sq_lt_sq` (or directly: `0 ≤ ‖a k‖`, `‖a k‖ < ‖b k‖`,
         hence `‖a k‖² < ‖b k‖²` by `sq_lt_sq` or `mul_self_lt_mul_self`).
         Combine with `pow_le_pow_left hs_nonneg hst (2*k-2)` to get
         `coeffMinusGap a b k * s^(2k-2) ≤ coeffMinusGap a b k * t^(2k-2)`.
         Both `if` branches reduce to this inequality on the `then` branch.
       * **`h : ¬ n2Pred a b k`**: both summands reduce to `0`; `le_refl _`.
    4. Show summability of the `s`-side series. The `s`-side summand is
       non-negative (in the `then` branch: `coeffMinusGap a b k > 0` and
       `s^(2k-2) ≥ 0` from `0 ≤ s`; in the `else` branch: `0`), and
       bounded above by the corresponding `t`-side summand by step 3.
       Apply `Summable.of_nonneg_of_le` (or equivalently
       `summable_of_nonneg_of_le`) with the pointwise non-negativity and
       the pointwise bound, plus `hSummable_t`.
    5. Apply `Summable.tsum_le_tsum (h_pointwise) (hSummable_s)
       hSummable_t` (signature mirrors
       `MeasureTheory/VectorMeasure/Basic.lean:907`).
    6. Conclude `sigmaZeroMinus a b s ≤ sigmaZeroMinus a b t` after
       re-folding the `tsum` back.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 011's `sigmaZeroMinus_monotone_of_summable` is the
    workspace's **first series-level lemma about `sigmaZeroMinus`** — it
    derives monotonicity of the `tsum`-defined function from termwise
    monotonicity of its non-negative summands, conditional on summability
    at the larger argument. This unlocks the natural left-edge use-case of
    sprint 010's `Z`-free reducer.

  * Add the new generic theorem
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` matching the
    shape above. The proof body must:

    1. `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free hc_pos
        hc_lt_one ?_; intro a b K paper`.
    2. `obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one,
        hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hSummable,
        hKernel⟩ := h_witness paper`.
    3. Repackage as a sprint-010-shaped existential with `ρ = ρ₁`:

       ```lean
       refine ⟨ρ₁, ρ₁, ρ₂, hcρ₁, hρ₁_branch, ?, hcρ₁, le_refl _, hρ₁₂,
         hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda,
         ?, hKernel⟩
       ```

       * The `?` for `ρ₁ < 1` follows from `lt_of_le_of_lt hρ₁₂ hρ₂_lt_one`
         (i.e. `ρ₁ ≤ ρ₂ < 1`).
       * The `?` for the `Z`-monotonicity premise discharges via:

         ```lean
         intro ρ' hρ'
         have hρ'_in : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
         have hρ₁_nonneg : 0 ≤ ρ₁ := le_of_lt (lt_trans hc_pos hcρ₁)
         exact sigmaZeroMinus_monotone_of_summable
                 hρ₁_nonneg hρ'_in (hSummable ρ' hρ')
         ```

       Lean will unify the result with the expected `sigmaZeroMinus a b ρ
       ≤ sigmaZeroMinus a b ρ'` shape under `ρ := ρ₁`.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 011's
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` is the
    workspace's first reducer that consumes a **purely series-side
    summability premise** in place of sprint 010's pointwise
    `Z`-monotonicity premise. The disk witness is fixed at `ρ = ρ₁` (the
    left edge of the annulus window), the `Z`-monotonicity premise is
    discharged in-house from `sigmaZeroMinus_monotone_of_summable`, and
    the resulting witness bundle replaces the pointwise function-value
    inequality with a series-level convergence hypothesis — strictly
    cleaner shape, suitable for direct discharge by Cauchy/ratio/comparison
    tests on `[ρ₁, ρ₂] ⊂ (c, 1)` in a future sprint.

  * The body of `sigmaZeroMinus_monotone_of_summable` MAY invoke
    `PaperAxioms.sigmaZeroMinus` (the underlying definition, exposed via
    `simp only` / `unfold`), `PaperAxioms.n2Pred`,
    `PaperAxioms.coeffMinusGap`, `Summable.tsum_le_tsum`,
    `Summable.of_nonneg_of_le` (or equivalent),
    `mul_le_mul_of_nonneg_left`, `pow_le_pow_left`,
    `pow_nonneg`, `sq_lt_sq` / `mul_self_lt_mul_self`, and standard `simp`
    lemmas. The body must NOT mention any `paper.eq*_*` (this lemma is
    **independent of `Section2Assumptions`** — it's a pure property of
    `sigmaZeroMinus` as a series), nor any of the existing `valid_of_*`,
    `circleGap_*`, `diskExcess_*`, `annulusExcess_*`, or
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. The lemma is genuinely
    new-ground and must not depend on the rest of the chain.

  * The body of
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` MAY invoke
    *only* `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` (sprint 010)
    and `sigmaZeroMinus_monotone_of_summable` (the new sprint 011 lemma).
    The body must NOT mention `paper.eq2_`, `paper.eq3_`, `paper.eq4_`,
    `paper.eq5_`, `paper.eq6_`, `paper.eq7_paperK_formula`, `paper.eq8_`,
    `paper.eq9_`, `paper.eq10_`, `paper.eq11_`, `paper.eq12_`,
    `paper.eq13_`, `paper.eq14_combined`, `paper.eq15_`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
    `Korenblum.scalarIntegrand2`, `valid_of_eq15`, `valid_of_eq12_eq13`,
    `valid_of_eq2_eq3_eq4_annulus_budget`,
    `valid_of_eq10_subinterval_branch1`,
    `valid_of_collapsed_disk_eq8_eq9_lower` (sprint 009 — sprint 011 only
    talks to sprint 010, not sprint 009 directly),
    `eq15_implies_disk_le_annulus`,
    `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
    `circleGap_outer_lower_bound_of_eq8_eq9`,
    `annulusExcess_lower_bound_of_eq8_eq9`,
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    `sigmaZeroMinus_nonneg_of_pos`. The intent is that sprint 011's
    reducer is a **pure refinement on top of sprint 010** — it reaches
    sprint 010 through `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` and
    nothing else, plus the new monotonicity lemma to discharge `hZmono`.

* `ProofRefinement/Korenblum/Candidates/V11.lean`:

  * `-- @parent V10`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V10).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly
    as in V1–V10; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).

  * Prove the final sink theorem via `valid_of_eq15` (so the score does
    not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    monotonicity lemma against an abstract series-summability hypothesis
    at the seed `c_value`:

    ```lean
    theorem v11_sigmaZeroMinus_monotone_compiles
        (a b : ℕ → ℂ)
        (s t : ℝ)
        (hs_nonneg : 0 ≤ s)
        (hst : s ≤ t)
        (hSummable_t :
          Summable (fun k : ℕ =>
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
            else 0)) :
        PaperAxioms.sigmaZeroMinus a b s
          ≤ PaperAxioms.sigmaZeroMinus a b t :=
      sigmaZeroMinus_monotone_of_summable hs_nonneg hst hSummable_t
    ```

  * Additionally, prove a *verifying* side lemma exercising the new
    left-edge reducer at the seed `c_value`:

    ```lean
    theorem v11_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_chain_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              c_value < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c_value ^ 2 ∧
                ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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
                  Summable (fun k : ℕ =>
                    if PaperAxioms.n2Pred a b k then
                      PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
                    else 0)) ∧
                (c_value ^ 6 / 6) / (ρ₁ ^ 2 - c_value ^ 2)
                  ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
        c_value_pos c_value_lt_one h_witness
    ```

    Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify that the new lemmas typecheck at
    the seed `c_value`.

  * Additionally, prove a tiny structural witness lemma confirming the
    geometric scaffolding `c_value < ρ₁ ≤ ρ₂ < 1` and `3ρ₁² ≤ 4·c_value²`
    is non-vacuous at the seed (i.e. there exists a pair `(ρ₁, ρ₂)`
    satisfying all four constraints simultaneously):

    ```lean
    theorem v11_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c_value ^ 2 ∧
            ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨4 / 10, 5 / 10, ?_, ?_, ?_, ?_⟩ <;>
        norm_num [c_value]
    ```

    Sanity: identical to V10's `(4/10, 4/10, 5/10)` witness, dropping the
    middle `ρ` slot. The witness lemma is local to V11 and is not used
    elsewhere — its purpose is to demonstrate that the geometric
    scaffolding of the new `_atLeftEdge` reducer's `h_witness` premise is
    non-vacuous at the seed `c_value`. The summability and kernel
    inequality premises are not part of the geometric scaffolding and
    are intentionally not discharged here.

* No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V10.lean`,
  no edits to `Sprint_Contracts/sprint_001…sprint_010`.

### Note on the choice `ρ = ρ₁` (left-edge specialisation)

Sprint 010's `hZmono` premise `∀ ρ' ∈ [ρ₁, ρ₂], Z_ρ ≤ Z_ρ'` is naturally
satisfied when `ρ = ρ₁` is the *left endpoint* of the window, because then
`ρ ≤ ρ'` for every `ρ' ∈ [ρ₁, ρ₂]`. The right-edge specialisation `ρ = ρ₂`
would require an *anti*-monotonicity statement on `[ρ₁, ρ₂]`, which is
false for `sigmaZeroMinus` (the function is non-decreasing). Mid-window
choices `ρ ∈ (ρ₁, ρ₂)` would split the window into a sub-window where
`ρ' ≤ ρ` (anti-monotonicity needed) and one where `ρ ≤ ρ'`
(monotonicity), so the `hZmono` premise can't be discharged uniformly
on the whole window. Hence the natural left-edge specialisation.

### Note on the summability premise

The `Summable` premise is taken `∀ ρ' ∈ Icc ρ₁ ρ₂` (one summability
hypothesis per `ρ'` in the window), not as a single hypothesis. This is
because each `ρ'`-summability is a separate convergence statement. A
future sprint could *uniformise* this — derive a single
`Summable (fun k => coeffMinusGap a b k * ρ₂^(2k-2))` from a tail bound
on `(b k - a k)` and observe that `ρ' ≤ ρ₂` makes the `ρ'`-series
dominated by the `ρ₂`-series, hence summable. That uniformisation is the
natural next sprint *after* sprint 011 lands. For now the universally
quantified summability premise is the cleanest formulation.

### Note on `2 * k - 2` vs `2 * (k - 1)` in the `n2Pred` branch

The paper definition of `sigmaZeroMinus` uses `s ^ (2 * k - 2)` with `Nat`
subtraction. Inside the `n2Pred a b k` branch we have `0 < k`, so
`2 * k - 2 = 2 * (k - 1)` as `Nat`s, and `s ^ (2*k - 2) = s ^ (2*(k-1)) =
(s^2)^(k-1)`. The pointwise inequality `s^(2k-2) ≤ t^(2k-2)` follows
from `pow_le_pow_left hs_nonneg hst (2*k-2)` regardless of how the
exponent is rewritten, so no `Nat`-subtraction reasoning is required in
the proof body — `pow_le_pow_left` handles the `Nat`-subtracted exponent
directly.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V11.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V11.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V11 scores `≥` V10 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V11.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'sigmaZeroMinus_monotone_of_summable' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least two matches: one definition site, plus at least one
   call site inside
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`. The body of
   the definition contains:
   * exactly one use of `Summable.tsum_le_tsum` (or
     `tsum_le_tsum`/`Summable.tsum_mono` if Lean's name resolution prefers
     a different alias),
   * at least one use of `pow_le_pow_left` (or equivalent monotonicity of
     real powers in the base),
   * no reference to `paper.eq*_*`, no reference to any existing
     `valid_of_*` or `circleGap_*` or `diskExcess_*` or
     `annulusExcess_*` lemma.
6. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site. The body of that theorem contains:
   * exactly one use of `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`
     (sprint 010),
   * at least one use of `sigmaZeroMinus_monotone_of_summable` (the new
     sprint 011 lemma).
7. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge\|sigmaZeroMinus_monotone_of_summable' korenblum/ProofRefinement/Korenblum/Candidates/V11.lean`
   returns at least two distinct matches (V11 actually invokes both new
   lemmas in its body, inside
   `v11_sigmaZeroMinus_monotone_compiles` and
   `v11_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_chain_compiles`).
8. The body of `sigmaZeroMinus_monotone_of_summable` does NOT mention any
   of the following forbidden references (verify via `grep -nE` against
   the substring of the theorem body): `paper.eq`, `Section2Assumptions`,
   `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
   `Korenblum.scalarIntegrand2`, `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`,
   `valid_of_eq10_subinterval_branch1`,
   `valid_of_collapsed_disk_eq8_eq9_lower`,
   `eq15_implies_disk_le_annulus`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   `sigmaZeroMinus_nonneg_of_pos`. The lemma is **independent of any
   paper-side hypothesis** — it is a pure series-monotonicity result.
9. The body of `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`
   does NOT mention any of the forbidden references listed in "Concrete
   edits expected" beyond the two allowed
   (`valid_of_collapsed_disk_eq8_eq9_lower_Z_free` and
   `sigmaZeroMinus_monotone_of_summable`). Verify via `grep -nE` against
   the substring of the theorem body.
10. `grep -n 'v11_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V11.lean`
    returns exactly one definition site (the small structural witness
    lemma confirming the geometric scaffolding is non-vacuous at the
    seed `c_value`).
11. The new `sigmaZeroMinus_monotone_of_summable` lemma's signature does
    NOT take any `Section2Assumptions` argument — verify by inspecting
    the signature (it should take only `(a b : ℕ → ℂ)`, `(s t : ℝ)`,
    `0 ≤ s`, `s ≤ t`, and the `Summable` hypothesis at `t`). This is the
    structural marker that the lemma is genuinely series-side and
    independent of any paper-faithful axiom.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V10.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Discharging *any* of the explicit premises in the new
  `_atLeftEdge` reducer's `h_witness`: the two integrability premises
  (`hIntLambdaZ`, `hIntLambda`), the summability premise (`hSummable`),
  or the kernel inequality premise (`hKernel`). They are intentionally
  taken as explicit premises packed into `h_witness`. Deriving any of
  them in-house from `Section2Assumptions` is the subject of separate
  future sprints.
* Discharging the kernel inequality
  `(c^6/6)/(ρ₁^2 − c^2) ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 / paperLambda K c ρ' dρ'`
  itself. That is the explicit subject of a future sprint (numerical
  oracle, closed-form `paperLambda` envelope substitution after a
  trust-base proposal, or symbolic antiderivative).
* Discharging the universal summability premise `∀ ρ' ∈ Icc ρ₁ ρ₂,
  Summable (…)`. The natural follow-up is to derive a single
  `Summable` hypothesis at `ρ' = ρ₂` and dominate the rest by it
  (since `ρ' ≤ ρ₂` makes the `ρ'`-series dominated termwise). That
  uniformisation step is left for a separate sprint.
* Choosing any concrete `(ρ₁, ρ₂)` pair beyond the V11 witness lemma
  `v11_window_witness_at_seed` (which only verifies the geometric
  scaffolding is non-vacuous; the summability and kernel inequality
  premises are NOT discharged). The free parameters must remain
  `forall`-quantified inside `h_witness`.
* Adding a *right-edge* variant `_atRightEdge` with `ρ = ρ₂`. As noted
  above, this would require an *anti*-monotonicity statement on
  `sigmaZeroMinus`, which is false. The right-edge specialisation is
  not a useful reducer.
* Adding a *mid-window* variant that splits the window into `[ρ₁, ρ]`
  and `[ρ, ρ₂]` and discharges `hZmono` separately on each piece. That
  would require deriving sprint 010's reducer for half-windows and
  patching them — strictly more work than the natural left-edge
  specialisation, and not a strict improvement (the mid-window kernel
  inequality is identical to the full-window one, so the mid-window
  specialisation buys nothing).
* Refactoring or simplifying sprints 001–010. Their lemmas are consumed
  verbatim (sprint 011 only *adds* one new theorem and one new
  reducer).
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new `_atLeftEdge` reducer. That requires
  discharging the kernel inequality, the integrability premises, and
  the summability premise at the seed `c_value`, which is the subject
  of multiple future sprints.
* Pushing `c_value` upward in this sprint — the goal is the structural
  monotonicity lemma plus left-edge reducer specialisation, not a
  numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/`. Sprint 011 is purely structural —
  numerical work belongs in a separate sprint that follows.

## Time budget

≤ 35 minutes runtime. The new monotonicity lemma is ~25 lines of Lean
(unfold + cases on `n2Pred` + termwise inequality + `Summable.tsum_le_tsum`).
The new reducer is ~30 lines (refine + obtain + repackage + discharge
`hZmono` from monotonicity lemma). The candidate side lemmas are one
line each. The structural witness lemma is ≤ 5 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `Summable.tsum_le_tsum` does not exist with the expected signature in
  the pinned Mathlib (Lean 4 v4.28.0 / Mathlib v4.28.0) — known to exist
  per `MeasureTheory/VectorMeasure/Basic.lean:907`. If name resolution
  picks a different alias, try `tsum_le_tsum` (without the `Summable.`
  prefix) or `tsum_mono`. If neither works, fall back to `HasSum.le` on
  the underlying `HasSum` from `Summable.hasSum`.
* `Summable.of_nonneg_of_le` does not exist as named — try
  `summable_of_nonneg_of_le`, `Summable.of_le`, or
  `Summable.comparison`. Mathlib's standard summable-comparison lemma
  for non-negative real-valued series is the right tool; if the exact
  name differs, mirror an existing call site (a `grep -rn
  'Summable.of_nonneg' korenblum/.lake/packages/mathlib/`
  in the Generator's working session will surface the correct name).
* The unfolding of `PaperAxioms.sigmaZeroMinus` to its `tsum` form via
  `simp only` / `unfold` does not work cleanly because the definition
  uses `by classical; exact …`. Try `show` with the explicit `tsum`
  expression, or `change` to the explicit `tsum`-shaped goal. As a last
  resort, prove the lemma in two halves: first
  `sigmaZeroMinus a b s = ∑' k, …` and second the `∑'`-level
  monotonicity, then chain.
* `pow_le_pow_left` requires `0 ≤ s` as an explicit argument — the
  signature in the pinned Mathlib is
  `pow_le_pow_left (h : 0 ≤ s) (hst : s ≤ t) (n : ℕ) : s^n ≤ t^n`.
  Make sure to pass `hs_nonneg` as the first argument.
* The proof of `coeffMinusGap a b k > 0` from `n2Pred a b k` requires
  `‖a k‖ ^ 2 < ‖b k‖ ^ 2`. From `‖a k‖ < ‖b k‖` and `0 ≤ ‖a k‖`,
  `0 ≤ ‖b k‖`, this is `sq_lt_sq'` or `mul_self_lt_mul_self` (the
  exact lemma name in pinned Mathlib varies — `pow_lt_pow_left` works
  too: `pow_lt_pow_left h h' (n := 2)` with `h : ‖a k‖ < ‖b k‖` and
  `h' : 0 ≤ ‖a k‖`).
* The non-negativity of `coeffMinusGap a b k * s^(2*k-2)` in the
  summability transfer step requires `0 ≤ s`. This is `hs_nonneg`,
  passed through.
* The repackaging step in
  `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` requires
  matching the exact existential-shape of sprint 010's `h_witness` (10
  conjuncts plus an `∀`-statement plus a final inequality). Re-read
  sprint 010's signature in `Reduction.lean` (line ~1141 onward) and
  re-pack the bundle in the **exact** order. The order in this contract
  mirrors sprint 010's; if Lean disagrees, follow Lean.
* The `change`/`refine` for the `Z`-monotonicity discharge step requires
  the `∀ ρ' ∈ Set.Icc ρ₁ ρ₂, …` shape rather than `∀ ρ', ρ' ∈ … → …`.
  `intro ρ' hρ'` in Lean 4 may parse the membership as either; if there's
  a unification failure, try `intro ρ'; intro hρ'` or unfold
  `Set.mem_Icc` first.
* Any of acceptance criteria 4, 5, 6, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in acceptance
  criteria 8 or 9: `STATUS=BLOCKED` — that would defeat the
  series-side independence of this sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
* The structural witness lemma `v11_window_witness_at_seed` fails to
  close with `norm_num [c_value]`: try `decide`, `nlinarith`, or pick a
  slightly different `(ρ₁, ρ₂)` triple. The pair `(4/10, 5/10)` is
  known to satisfy all four conjuncts at `c_value = 0.3554`
  (`4·c_value² ≈ 0.5052`, `3·0.4² = 0.48 ≤ 0.5052`); if `norm_num`
  cannot close one, name it explicitly with `refine ⟨_, ?_, ?_, _⟩`
  and discharge the failing one with `nlinarith` or a manual chain.
