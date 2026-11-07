# Sprint 012: Series-side summability uniformization — dominate the universal `Summable ∀ ρ' ∈ Icc ρ₁ ρ₂` premise of sprint 011 by a single `Summable` hypothesis at `ρ₂`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V11.lean`
**Target file**: `Candidates/V12.lean`
**Direction**: section2-proof

## Goal

Ship two new generic Lean lemmas in `Proof/Reduction.lean`:

1. **A series-level summability-domination lemma**

   ```lean
   theorem sigmaZeroMinus_summable_of_summable_at_upper
       {a b : ℕ → ℂ} {s t : ℝ}
       (hs_nonneg : 0 ≤ s)
       (hst : s ≤ t)
       (hSummable_t :
         Summable (fun k : ℕ =>
           if PaperAxioms.n2Pred a b k then
             PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
           else 0)) :
       Summable (fun k : ℕ =>
         if PaperAxioms.n2Pred a b k then
           PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
         else 0)
   ```

   The proof body is a near-direct port of the comparison-test step already
   buried inside sprint 011's `sigmaZeroMinus_monotone_of_summable` — extract
   it as a standalone lemma. Specifically:

   * Termwise non-negativity of the `s`-side summand (in the `n2Pred` branch:
     `coeffMinusGap a b k ≥ 0` from `‖a k‖ < ‖b k‖`, and `s^(2k-2) ≥ 0` from
     `0 ≤ s`; in the inactive branch: `0`).
   * Termwise domination `s-side ≤ t-side` for every `k` (in the `n2Pred`
     branch: `coeffMinusGap ≥ 0` plus `pow_le_pow_left₀ hs_nonneg hst (2*k-2)`;
     in the inactive branch: `0 ≤ 0`).
   * Apply `Summable.of_nonneg_of_le` with non-negativity, domination, and
     `hSummable_t`.

2. **A specialised right-edge-summability reducer eliminating sprint 011's
   universal `∀ ρ' ∈ Icc ρ₁ ρ₂, Summable …` premise**

   ```lean
   theorem valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable
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
               Summable (fun k : ℕ =>
                 if PaperAxioms.n2Pred a b k then
                   PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                 else 0) ∧
               (c ^ 6 / 6) / (ρ₁ ^ 2 - c ^ 2)
                 ≤ ∫ ρ' in ρ₁..ρ₂,
                     2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
       ValidKorenblumBound c
   ```

   The proof body:

   * `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge hc_pos hc_lt_one ?_;
     intro a b K paper`.
   * `obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle,
     hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ := h_witness paper`.
   * Reconstruct sprint 011's witness bundle by upgrading the single
     `hSummable_top` to a universally-quantified summability statement on
     `[ρ₁, ρ₂]`:

     ```text
     intro ρ' hρ'
     have hρ'_in : ρ' ∈ Set.Icc ρ₁ ρ₂ := hρ'
     have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ'_in).2
     have hρ'_nonneg : 0 ≤ ρ' :=
       le_of_lt (lt_trans hc_pos (lt_of_lt_of_le hcρ₁ (Set.mem_Icc.mp hρ'_in).1))
     exact sigmaZeroMinus_summable_of_summable_at_upper
             hρ'_nonneg hρ'_le_ρ₂ hSummable_top
     ```
   * Re-pack: `exact ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one, hIntDisk,
     hIntCircle, hIntLambdaZ, hIntLambda, hSummable_uniform, hKernel⟩`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V12.lean` at the same `c = 0.3554` that compiles,
scores `≥ V11`, and *materialises* both new lemmas in two side lemmas
`v12_sigmaZeroMinus_summable_of_summable_at_upper_compiles` and
`v12_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable_chain_compiles`
exercised against abstract witness/integrability/single-summability bundles
(mirroring V11's `v11_*_chain_compiles` pattern).
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 011 produced the workspace's first
series-level lemma about `sigmaZeroMinus`, but the resulting left-edge
reducer `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` still
carries a **universally quantified summability premise**
`∀ ρ' ∈ Icc ρ₁ ρ₂, Summable (fun k => if n2Pred a b k then coeffMinusGap a b
k * ρ' ^ (2*k-2) else 0)` — one summability statement *per `ρ'` in the
window*.

Sprint 011's "Note on the summability premise" explicitly flags this as the
natural follow-up:

> A future sprint could *uniformise* this — derive a single
> `Summable (fun k => coeffMinusGap a b k * ρ₂^(2k-2))` from a tail bound
> on `(b k - a k)` and observe that `ρ' ≤ ρ₂` makes the `ρ'`-series
> dominated by the `ρ₂`-series, hence summable. That uniformisation is the
> natural next sprint *after* sprint 011 lands.

Sprint 012 is precisely that uniformisation step. It is qualitatively new
along three independent axes:

1. **Strict refinement of sprint 011's reducer with one structural
   ∀-quantified premise *collapsed* to a single point premise.** The new
   reducer
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
   strictly refines sprint 011 by *replacing* the universal summability
   premise `∀ ρ' ∈ Icc ρ₁ ρ₂, Summable …` with a **single point
   summability** `Summable …` at the upper edge `ρ₂`. This is a
   structurally cleaner premise: a future sprint that wants to discharge
   it can name a *single* convergence statement at `ρ' = ρ₂ < 1` and let
   Mathlib's standard ratio/comparison/geometric-tail machinery close it,
   instead of having to discharge a family of convergence statements
   indexed by `ρ' ∈ [ρ₁, ρ₂]`.

2. **Second series-level lemma in the workspace, structurally distinct
   from sprint 011.** Sprint 011 ships
   `sigmaZeroMinus_monotone_of_summable`, a *value-monotonicity* result
   for the series sum. Sprint 012 ships
   `sigmaZeroMinus_summable_of_summable_at_upper`, a *summability-transfer*
   result for the underlying terms. The two results are independent — one
   talks about the value of `tsum` once it converges, the other talks
   about whether `tsum` converges at all. Together they form the
   workspace's first *coordinated pair* of series-side reasoning lemmas
   for `sigmaZeroMinus`. The bulletin's "axes worth exploring" block
   explicitly mentions this axis ("work on the coefficient side via
   `sigmaPlus`/`sigmaMinus`/`sigmaZeroMinus` structure or the
   `circleGapSeries` representation instead of going through the
   integrated forms").

3. **Direct support for a future `c`-pushing sprint.** With both the
   monotonicity lemma (sprint 011) *and* the summability-domination lemma
   (sprint 012) in place, the path to a `c`-push becomes:

   * pick a window `[ρ₁, ρ₂] ⊂ (c, branchSplit c]` with `ρ₂ < 1`,
   * verify the kernel inequality
     `(c⁶/6)/(ρ₁²−c²) ≤ ∫_{ρ₁..ρ₂} 2ρ'³/Λ(c,ρ') dρ'` (numerically in
     `Scratch/`, then symbolically/oracularly in Lean),
   * supply a *single* `Summable (… ρ₂^(2k-2) …)` witness at the upper
     edge — for any sequence `(a_k, b_k)` with `‖b_k − a_k‖ = O(1)` (a
     mild decay assumption, derivable from the bounded analytic function
     setting), the series converges geometrically since `ρ₂ < 1`,
   * supply integrability of the kernel `2ρ'³/Λ(c,ρ')` and the weighted
     kernel `2ρ'³·Z_ρ'/Λ(c,ρ')` (separate sprint).

   Sprint 011's universal-summability premise was the **only** premise
   that could not be discharged from a single point statement — it
   required a family of convergence facts indexed by a continuous
   parameter. Sprint 012 removes that asymmetry, replacing the
   `∀ ρ'`-quantified premise with a single point convergence statement at
   `ρ' = ρ₂`.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V12 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorems are purely structural: the summability-domination
  lemma is a generic comparison-test result that holds for *any*
  coefficient sequence `(a, b)` and *any* non-negative `s ≤ t`, and the
  new reducer is a generic specialisation of sprint 011 that holds for
  *any* witness bundle.
* No concrete numerical tuple is committed.

Why this is **not** "the same chain" as sprint 011:

* Sprint 011's body inspects the `tsum` representation to derive a
  *value-level* monotonicity statement
  `sigmaZeroMinus a b s ≤ sigmaZeroMinus a b t`. Sprint 012's
  summability-domination lemma is a *convergence-level* statement about
  the *underlying terms* — it does not touch `tsum` at all, only the
  termwise summands. The two lemmas live in genuinely different layers of
  the series stack: sprint 011 reasons about the *value* of an already-
  convergent `tsum`; sprint 012 reasons about *whether* the `tsum`
  converges in the first place.
* The new reducer's witness bundle has *one fewer ∀-quantifier* than
  sprint 011's, replacing `∀ ρ' ∈ [ρ₁, ρ₂], Summable …` with
  `Summable … at ρ₂`. The two are not interchangeable: the former is a
  *family* of convergence statements indexed by a continuous parameter,
  the latter is a *single point* convergence statement, dramatically
  easier to discharge in any future sprint.

Why this is **bounded enough for one Generator session**:

* The summability-domination lemma's proof is genuinely small and
  *literally a sub-proof* of sprint 011's `sigmaZeroMinus_monotone_of_summable`:
  the steps "termwise non-negativity of `s`-side summands" + "termwise
  domination of `s`-side by `t`-side" + `Summable.of_nonneg_of_le` are
  already worked out in `Reduction.lean:1303-1342`. The Generator's job
  is to extract these steps as a standalone lemma. Estimate: ≤ 25 lines
  of Lean (and partial copy from existing source).

* The specialised reducer's proof is even smaller:
  * `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge hc_pos hc_lt_one ?_`
    + `intro a b K paper`.
  * `obtain` the new witness bundle.
  * Construct the universal summability witness via the new domination
    lemma, then re-pack the sprint 011 witness bundle.
  Estimate: ≤ 25 lines of Lean.

* The candidate side lemmas are one line each.

* No new Mathlib lemmas needed beyond `Summable.of_nonneg_of_le`,
  `pow_le_pow_left₀`, `mul_le_mul_of_nonneg_left`, `pow_nonneg`. All of
  these are foundational Mathlib lemmas in the pinned toolchain
  (Lean 4 v4.28.0 / Mathlib v4.28.0) and are *already used* in
  `sigmaZeroMinus_monotone_of_summable` (verified at
  `Reduction.lean:1303-1342`).

* The new `sigmaZeroMinus_summable_of_summable_at_upper` shares essentially
  the same proof skeleton as the *first half* of
  `sigmaZeroMinus_monotone_of_summable`, so there is a concrete reference
  implementation to mirror. Risk of "Mathlib lemma name mismatch" is
  near-zero.

Why this beats the obvious alternatives I considered:

* **A: discharge an `IntervalIntegrable` premise via continuity of
  `paperLambda` over `[ρ₁, ρ₂]`.** Could derive
  `IntervalIntegrable (fun ρ' => 2ρ'³/Λ(c,ρ')) volume ρ₁ ρ₂` from
  `WangPaperSideConditions.paperLambda_pos` (already used at
  `Reduction.lean:1218`) plus a continuity statement. Modest novelty: it
  is mostly bookkeeping that translates a paper-side fact into a
  `MeasureTheory`-side fact, without opening a new analytical chain. The
  required continuity lemma — `paperLambda_continuous` or similar — may
  or may not be exposed cleanly in `WangPaperSideConditions`; the path
  there is uncertain. Demoted: less analytical novelty per session, and
  the integrability story is best handled in a separate later sprint
  when both `IntervalIntegrable` premises (`hIntLambdaZ`, `hIntLambda`)
  can be discharged together with a shared continuity argument.

* **B: parallel `sigmaPlus` disk-side bound via `eq3 + eq4` (without
  substituting `eq2`).** Build a second disk-side upper bound that goes
  through `sigmaPlus` instead of `sigmaZeroMinus`, using
  `eq3 : circleGap = sigmaPlus − r²·sigmaZeroMinus` and
  `eq4 : sigmaPlus r ≤ sigmaPlus c ≤ sigmaMinus c = c²·sigmaZeroMinus c`,
  *without* substituting `eq2` to eliminate `sigmaZeroMinus(r)`. Genuinely
  novel structural axis but **risky** for one Generator session: the
  resulting upper bound's coefficient signs need to be determined by
  hand (or in `Scratch/`), and there's no advance evidence that the
  resulting bound is non-trivial relative to sprint 003's
  `(2)+(3)+(4)` bound. Also: the `Z_r` term carries an unknown sign
  contribution in the integration, and separating it requires either
  monotonicity of `sigmaZeroMinus` on a sub-interval of `[0, c]`
  (which is *not* the same as sprint 011's monotonicity at points `s ≤ t`
  on `[c, 1]`) or an explicit closed-form integration step. Better to
  file as a future sprint after `Scratch/`-side numerical exploration.
  Demoted to "future / needs Scratch evidence first".

* **C: closed-form lower bound on `paperLambda(c, ρ)` via
  `paperLambda_le_of_witness`.** Same blocker as sprint 011 candidate A:
  `paperLambda_le_of_witness` lives in `WangCertificateCore`, **not on
  the workspace allowlist**. Would require a `Proposals/` entry to
  expand `[workspace_import_policy]`. Demoted because it requires a
  non-oracle trust expansion that is not approved.

* **D: branch-2 mirror of sprint 008** on `(branchSplit c, 1)`. Pure
  flavour-clone of sprint 008, exactly the "three flavours of the same
  chain" pattern the bulletin warns against. Demoted.

* **E: prove `Eq15ScalarBound` in Lean for `c = 0.3554` symbolically**
  to remove the `hEq15_seed_3554` axiom. Pure numerical push against the
  existing chain — exactly what the bulletin de-prioritises.

* **F: a quantitative refinement of sprint 011 that lower-bounds
  `sigmaZeroMinus(t) - sigmaZeroMinus(s)` by a coefficient-side gap
  term.** Genuinely novel series-side, but speculative — no immediate
  consumer in the existing reducer chain. The current sprint 011 reducer
  uses *only* the qualitative inequality `Z_ρ₁ ≤ Z_ρ'`, not a
  quantitative gap. Demoted to "future / needs concrete consumer first".

Compared to A–F, candidate G (this sprint, with G1 = summability-
domination lemma + G2 = uniform-summable left-edge reducer) maximises
analytical novelty per bounded Generator session: it produces the
*workspace's second series-level lemma* about `sigmaZeroMinus`,
collapses a ∀-quantified premise from sprint 011's reducer to a single
point premise (and therefore directly supports the next `c`-push), and
uses *only existing trusted modules* + pinned Mathlib. No proposal needed.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `sigmaZeroMinus_summable_of_summable_at_upper` matching the shape
    above. The proof body must:

    1. Abbreviate the two summands

       ```text
       fs k = if PaperAxioms.n2Pred a b k then
                 PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
               else 0
       ft k = if PaperAxioms.n2Pred a b k then
                 PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
               else 0
       ```

    2. Show termwise non-negativity `0 ≤ fs k` for every `k`. Two cases:

       * **`h : n2Pred a b k`**: from `n2Pred a b k = (0 < k ∧ ‖a k‖ <
         ‖b k‖)` derive `0 ≤ coeffMinusGap a b k = ‖b k‖² − ‖a k‖²` via
         `pow_le_pow_left₀ (norm_nonneg _) hk.2.le 2` followed by
         `unfold PaperAxioms.coeffMinusGap; linarith`. Combine with
         `pow_nonneg hs_nonneg _` and `mul_nonneg`.
       * **`h : ¬ n2Pred a b k`**: `simp [fs, hk]` reduces to `0 ≤ 0`.

       This step is **literally the second `have h_nonneg_s : ∀ k, 0 ≤ fs k`
       block** at `Reduction.lean:1324-1339` of sprint 011's lemma. The
       Generator can copy-paste-adapt.

    3. Show termwise domination `fs k ≤ ft k` for every `k`. Two cases:

       * **`h : n2Pred a b k`**: derive `0 ≤ coeffMinusGap a b k` as in
         step 2, then apply
         `pow_le_pow_left₀ hs_nonneg hst (2 * k - 2)` to get the pow
         comparison, then
         `mul_le_mul_of_nonneg_left h_pow_le h_gap_nn`.
       * **`h : ¬ n2Pred a b k`**: `simp [fs, ft, hk]` reduces to `0 ≤ 0`.

       This step is **literally the first `have h_pointwise : ∀ k, fs k ≤ ft k`
       block** at `Reduction.lean:1303-1322` of sprint 011's lemma. The
       Generator can copy-paste-adapt.

    4. Apply `Summable.of_nonneg_of_le h_nonneg h_pointwise hSummable_t`
       and conclude `Summable fs`. The conclusion's expected shape is
       exactly `Summable (fun k => if PaperAxioms.n2Pred a b k then
       PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2) else 0)`, which
       is `Summable fs` after re-folding the `set` abbreviation.

       This step is **literally the** `have hSummable_s : Summable fs := …`
       block** at `Reduction.lean:1340-1342`** of sprint 011's lemma. The
       Generator can copy-paste-adapt.

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 012's `sigmaZeroMinus_summable_of_summable_at_upper`
    is the workspace's **second series-level lemma about `sigmaZeroMinus`**
    — a comparison-test summability-transfer result that complements
    sprint 011's value-level monotonicity. Together they form a
    coordinated pair that lets sprint 011's universal-summability premise
    be discharged from a *single point* convergence statement at the
    upper edge `ρ₂` (see
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
    below).

  * Add the new generic theorem
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
    matching the shape above. The proof body must:

    1. `refine valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge
        hc_pos hc_lt_one ?_; intro a b K paper`.
    2. `obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one,
        hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda, hSummable_top,
        hKernel⟩ := h_witness paper`.
    3. Construct the universal summability witness:

       ```lean
       have hSummable_uniform :
           ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
             Summable (fun k : ℕ =>
               if PaperAxioms.n2Pred a b k then
                 PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
               else 0) := by
         intro ρ' hρ'
         have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
         have hρ'_nonneg : 0 ≤ ρ' :=
           le_of_lt (lt_trans hc_pos
             (lt_of_lt_of_le hcρ₁ (Set.mem_Icc.mp hρ').1))
         exact sigmaZeroMinus_summable_of_summable_at_upper
                 hρ'_nonneg hρ'_le_ρ₂ hSummable_top
       ```
    4. Re-pack sprint 011's witness bundle:

       ```lean
       exact ⟨ρ₁, ρ₂, hcρ₁, hρ₁_branch, hρ₁₂, hρ₂_lt_one, hIntDisk,
         hIntCircle, hIntLambdaZ, hIntLambda, hSummable_uniform, hKernel⟩
       ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 012's
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
    is the workspace's first reducer that consumes a **single point
    summability premise** `Summable …` at the upper edge `ρ₂` in place
    of sprint 011's universal `∀ ρ' ∈ Icc ρ₁ ρ₂, Summable …`. The
    universal summability is reconstructed in-house from
    `sigmaZeroMinus_summable_of_summable_at_upper`, and the resulting
    witness bundle replaces a ∀-quantified family of convergence
    statements with a single point convergence statement — strictly
    cleaner shape, suitable for direct discharge by Cauchy/ratio/
    geometric-tail comparison on `ρ₂ < 1` in a future sprint.

  * The body of `sigmaZeroMinus_summable_of_summable_at_upper` MAY invoke
    `PaperAxioms.n2Pred`, `PaperAxioms.coeffMinusGap`,
    `Summable.of_nonneg_of_le`, `mul_le_mul_of_nonneg_left`,
    `pow_le_pow_left₀`, `pow_nonneg`, `mul_nonneg`, and standard `simp`
    lemmas. The body must NOT mention any `paper.eq*_*` (this lemma is
    **independent of `Section2Assumptions`** — it's a pure series-side
    convergence-transfer property), nor any of the existing
    `valid_of_*`, `circleGap_*`, `diskExcess_*`, `annulusExcess_*`, or
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. The body MAY mention
    `sigmaZeroMinus_monotone_of_summable` only if doing so simplifies
    the proof; in practice the most natural proof does not need it
    (the comparison-test step is self-contained).

  * The body of
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
    MAY invoke *only*
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` (sprint 011)
    and `sigmaZeroMinus_summable_of_summable_at_upper` (the new sprint
    012 lemma). The body must NOT mention `paper.eq2_`, `paper.eq3_`,
    `paper.eq4_`, `paper.eq5_`, `paper.eq6_`, `paper.eq7_paperK_formula`,
    `paper.eq8_`, `paper.eq9_`, `paper.eq10_`, `paper.eq11_`,
    `paper.eq12_`, `paper.eq13_`, `paper.eq14_combined`, `paper.eq15_`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
    `Korenblum.scalarIntegrand2`, `valid_of_eq15`, `valid_of_eq12_eq13`,
    `valid_of_eq2_eq3_eq4_annulus_budget`,
    `valid_of_eq10_subinterval_branch1`,
    `valid_of_collapsed_disk_eq8_eq9_lower` (sprint 009),
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free` (sprint 010 — sprint
    012 only talks to sprint 011, not sprint 010 directly),
    `eq15_implies_disk_le_annulus`,
    `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
    `circleGap_outer_lower_bound_of_eq8_eq9`,
    `annulusExcess_lower_bound_of_eq8_eq9`,
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    `sigmaZeroMinus_nonneg_of_pos`,
    `sigmaZeroMinus_monotone_of_summable`. The intent is that sprint
    012's reducer is a **pure refinement on top of sprint 011** — it
    reaches sprint 011 through
    `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` and nothing
    else, plus the new summability-domination lemma to build the
    universal summability witness.

* `ProofRefinement/Korenblum/Candidates/V12.lean`:

  * `-- @parent V11`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V11).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly
    as in V1–V11; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).

  * Prove the final sink theorem via `valid_of_eq15` (so the score does
    not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    summability-domination lemma against an abstract single-point
    summability hypothesis:

    ```lean
    theorem v12_sigmaZeroMinus_summable_of_summable_at_upper_compiles
        (a b : ℕ → ℂ)
        (s t : ℝ)
        (hs_nonneg : 0 ≤ s)
        (hst : s ≤ t)
        (hSummable_t :
          Summable (fun k : ℕ =>
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k * t ^ (2 * k - 2)
            else 0)) :
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * s ^ (2 * k - 2)
          else 0) :=
      sigmaZeroMinus_summable_of_summable_at_upper hs_nonneg hst hSummable_t
    ```

  * Additionally, prove a *verifying* side lemma exercising the new
    uniform-summable left-edge reducer at the seed `c_value` against an
    abstract witness/integrability/single-summability bundle:

    ```lean
    theorem v12_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable_chain_compiles
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
                Summable (fun k : ℕ =>
                  if PaperAxioms.n2Pred a b k then
                    PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                  else 0) ∧
                (c_value ^ 6 / 6) / (ρ₁ ^ 2 - c_value ^ 2)
                  ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable
        c_value_pos c_value_lt_one h_witness
    ```

    Both side lemmas must NOT be `axiom`-ed and must NOT call the seed
    axiom. They exist purely to verify that the new lemmas typecheck at
    the seed `c_value`.

  * Additionally, prove a tiny structural witness lemma confirming the
    geometric scaffolding `c_value < ρ₁ ≤ ρ₂ < 1` and `3ρ₁² ≤ 4·c_value²`
    is non-vacuous at the seed (identical to V11's
    `v11_window_witness_at_seed`, simply renamed):

    ```lean
    theorem v12_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ 3 * ρ₁ ^ 2 ≤ 4 * c_value ^ 2 ∧
            ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨4 / 10, 5 / 10, ?_, ?_, ?_, ?_⟩ <;>
        norm_num [c_value]
    ```

* No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V11.lean`,
  no edits to `Sprint_Contracts/sprint_001…sprint_011`.

### Note on the choice "summability at `ρ₂` dominates summability on `[ρ₁, ρ₂]`"

For any `ρ' ∈ [ρ₁, ρ₂]` we have `0 ≤ ρ' ≤ ρ₂`, so `(ρ')^(2k-2) ≤ ρ₂^(2k-2)`
for every `k ≥ 1` (and at `k = 0`, the `n2Pred` branch is unreachable so
the `if` makes the term vacuous — the same observation already exploited
in sprint 011). Combined with `coeffMinusGap a b k ≥ 0` (in the active
branch) we get termwise domination `fs(ρ') k ≤ fs(ρ₂) k`, and
`Summable.of_nonneg_of_le` transfers convergence from the dominating
series at `ρ₂` to the dominated series at `ρ'`. The pattern is
*identical* to sprint 011's monotonicity proof, with the roles of `s, t`
played by `ρ', ρ₂`.

### Note on why we dominate by the *upper* edge, not the lower edge

Each summand is non-negative and *increasing* in the base (because the
exponent `2k-2 ≥ 0` and the base is non-negative). So summability at the
upper edge `ρ₂` *implies* summability at every `ρ' ≤ ρ₂`. The reverse
direction (summability at `ρ₁` implying summability at `ρ' > ρ₁`) is
*false* in general — a series whose terms grow as the base increases
does not become more summable at larger bases. This is why the natural
domination is "by the upper edge".

### Note on the geometric heuristic for the upper-edge summability

For any `ρ₂ < 1` and any sequence `(a_k, b_k)` with `‖b_k‖ ≤ M` for some
`M < ∞`, we have `coeffMinusGap a b k = ‖b_k‖² − ‖a_k‖² ≤ M²`, so the
`ρ₂`-series is bounded termwise by `M² · ρ₂^(2k-2)`, which is a
geometric series in `ρ₂² < 1` and hence converges. This is the standard
heuristic that makes the single-point summability premise at `ρ₂`
*concretely dischargeable* in a future sprint from a mild boundedness
assumption on `(a_k, b_k)` plus the ambient bounded-analytic-function
context. Sprint 012 does **not** discharge this — it only sets up the
shape of the premise so a future sprint can supply the boundedness
argument.

### Note on the small generality difference: domination at any `s ≤ t`, not just on `[ρ₁, ρ₂]`

The summability-domination lemma is stated for arbitrary `0 ≤ s ≤ t`,
not specifically for the window `[ρ₁, ρ₂]`. This generality is free —
the proof uses only `0 ≤ s` and `s ≤ t`, no window-specific data — and
it makes the lemma reusable in any future sprint that needs to dominate
a `sigmaZeroMinus`-series convergence statement by a different
convergence statement at a larger argument.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V12.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V12.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V12 scores `≥` V11 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V12.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'sigmaZeroMinus_summable_of_summable_at_upper' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least two matches: one definition site, plus at least one
   call site inside
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`.
   The body of the definition contains:
   * exactly one use of `Summable.of_nonneg_of_le` (or
     `summable_of_nonneg_of_le` if Lean's name resolution prefers that
     alias),
   * at least one use of `pow_le_pow_left₀` (matching sprint 011's
     existing usage at `Reduction.lean:1310,1315,1330`),
   * no reference to `paper.eq*_*`, no reference to any existing
     `valid_of_*` or `circleGap_*` or `diskExcess_*` or
     `annulusExcess_*` lemma.
6. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site. The body of that theorem contains:
   * exactly one use of
     `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`
     (sprint 011),
   * at least one use of `sigmaZeroMinus_summable_of_summable_at_upper`
     (the new sprint 012 lemma).
7. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable\|sigmaZeroMinus_summable_of_summable_at_upper' korenblum/ProofRefinement/Korenblum/Candidates/V12.lean`
   returns at least two distinct matches (V12 actually invokes both new
   lemmas in its body, inside
   `v12_sigmaZeroMinus_summable_of_summable_at_upper_compiles` and
   `v12_valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable_chain_compiles`).
8. The body of `sigmaZeroMinus_summable_of_summable_at_upper` does NOT
   mention any of the following forbidden references (verify via
   `grep -nE` against the substring of the theorem body):
   `paper.eq`, `Section2Assumptions`,
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
   paper-side hypothesis** — it is a pure series-convergence-transfer
   result.
9. The body of
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
   does NOT mention any of the forbidden references listed in "Concrete
   edits expected" beyond the two allowed
   (`valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge` and
   `sigmaZeroMinus_summable_of_summable_at_upper`). Verify via
   `grep -nE` against the substring of the theorem body.
10. `grep -n 'v12_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V12.lean`
    returns exactly one definition site.
11. The new `sigmaZeroMinus_summable_of_summable_at_upper` lemma's
    signature does NOT take any `Section2Assumptions` argument — verify
    by inspecting the signature (it should take only `(a b : ℕ → ℂ)`,
    `(s t : ℝ)`, `0 ≤ s`, `s ≤ t`, and the `Summable` hypothesis at `t`).
    This is the structural marker that the lemma is genuinely series-side
    and independent of any paper-faithful axiom.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V11.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Discharging *any* of the explicit premises in the new
  `_uniformSummable` reducer's `h_witness`: the two integrability
  premises (`hIntLambdaZ`, `hIntLambda`), the single-point summability
  premise (`hSummable_top`), or the kernel inequality premise
  (`hKernel`). They are intentionally taken as explicit premises packed
  into `h_witness`. Deriving any of them in-house from
  `Section2Assumptions` is the subject of separate future sprints.
* Discharging the kernel inequality
  `(c^6/6)/(ρ₁^2 − c^2) ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 / paperLambda K c ρ' dρ'`
  itself. That is the explicit subject of a future sprint (numerical
  oracle, closed-form `paperLambda` envelope substitution after a
  trust-base proposal, or symbolic antiderivative).
* Discharging the single-point summability premise `Summable (… ρ₂^(2k-2)
  …)`. The natural follow-up is to derive it from a uniform bound on
  `(b_k - a_k)` plus `ρ₂² < 1` (geometric tail). That bound argument is
  left for a separate sprint, possibly via an ambient
  bounded-analytic-function hypothesis.
* Choosing any concrete `(ρ₁, ρ₂)` pair beyond the V12 witness lemma
  `v12_window_witness_at_seed`. The free parameters must remain
  `forall`-quantified inside `h_witness`.
* Adding a *lower-edge*-summability reducer variant (i.e., dominating
  by `Summable …` at `ρ' = ρ₁` instead of `ρ' = ρ₂`). As noted above,
  this would require an *anti*-monotonicity statement on the termwise
  series, which is false (each summand is non-decreasing in the base
  with non-negative exponent). The lower-edge specialisation is not a
  useful reducer.
* Refactoring or simplifying sprints 001–011. Their lemmas are consumed
  verbatim (sprint 012 only *adds* one new theorem and one new
  reducer).
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new `_uniformSummable` reducer. That requires
  discharging the kernel inequality, the integrability premises, and the
  single-point summability premise at the seed `c_value`, which is the
  subject of multiple future sprints.
* Pushing `c_value` upward in this sprint — the goal is the structural
  summability-domination lemma plus uniform-summable reducer
  specialisation, not a numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/`. Sprint 012 is purely structural —
  numerical work belongs in a separate sprint that follows.
* Refactoring sprint 011's `sigmaZeroMinus_monotone_of_summable` to
  *internally invoke* the new `sigmaZeroMinus_summable_of_summable_at_upper`.
  The sprint 011 lemma's body already contains the same comparison-test
  step inline (at `Reduction.lean:1340-1342`); refactoring it to call
  the new lemma would be a stylistic improvement but is out of scope
  for this sprint. (A future cleanup sprint may do so.)

## Time budget

≤ 30 minutes runtime. The new summability-domination lemma is ~25 lines
of Lean, and most of those lines can be lifted directly from sprint
011's existing `sigmaZeroMinus_monotone_of_summable` body (the
`h_pointwise`, `h_nonneg_s`, and `hSummable_s` blocks). The new reducer
is ~25 lines (refine + obtain + uniform-summability construction +
re-pack). The candidate side lemmas are one line each. The structural
witness lemma is ≤ 5 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `Summable.of_nonneg_of_le` does not exist as named — it is *already*
  used at `Reduction.lean:1342` in sprint 011's
  `sigmaZeroMinus_monotone_of_summable`, so this is known to work in
  the pinned Mathlib. If for some reason the alias differs in the new
  context, mirror the existing call site verbatim.
* `pow_le_pow_left₀` requires `0 ≤ s` as an explicit argument — the
  signature in the pinned Mathlib is
  `pow_le_pow_left₀ (h : 0 ≤ s) (hst : s ≤ t) (n : ℕ) : s^n ≤ t^n`, and
  is *already* used at `Reduction.lean:1310,1315,1330` in sprint 011's
  lemma. Make sure to pass `hs_nonneg` as the first argument.
* The proof of `0 ≤ coeffMinusGap a b k` from `n2Pred a b k` requires
  `‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2`. From `‖a k‖ < ‖b k‖` and `0 ≤ ‖a k‖`, this
  is `pow_le_pow_left₀ (norm_nonneg _) hk.2.le 2` followed by
  `unfold PaperAxioms.coeffMinusGap; linarith`. This pattern is
  *already* used at `Reduction.lean:1307-1313,1327-1333`.
* The repackaging step in
  `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`
  requires matching the exact existential-shape of sprint 011's
  `h_witness` (10 conjuncts plus an `∀`-statement plus a final
  inequality, see `Reduction.lean:1369-1388`). Re-read sprint 011's
  signature and re-pack the bundle in the **exact** order. The order in
  this contract mirrors sprint 011's; if Lean disagrees, follow Lean.
* The `intro ρ' hρ'` step for the universal-summability discharge
  requires the `∀ ρ' ∈ Set.Icc ρ₁ ρ₂, …` shape rather than `∀ ρ', ρ' ∈ … → …`.
  `intro ρ' hρ'` in Lean 4 may parse the membership as either; if
  there's a unification failure, try `intro ρ'; intro hρ'` or unfold
  `Set.mem_Icc` first. The pattern is *already* used at
  `Reduction.lean:1403-1404` in sprint 011's reducer.
* Any of acceptance criteria 4, 5, 6, 7, 8, 9, 10, 11 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in acceptance
  criteria 8 or 9: `STATUS=BLOCKED` — that would defeat the
  series-side independence of this sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
* The structural witness lemma `v12_window_witness_at_seed` fails to
  close with `norm_num [c_value]`: try `decide`, `nlinarith`, or pick a
  slightly different `(ρ₁, ρ₂)` pair. The pair `(4/10, 5/10)` is
  known to satisfy all four conjuncts at `c_value = 0.3554` — it works
  in V11's `v11_window_witness_at_seed`.
