# Sprint 017: Cauchy L² coefficient estimate + outer-annulus cross-function bridge

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V16.lean`
**Target file**: `Candidates/V17.lean`
**Direction**: section2-proof / scaffolding-for-c-push (the **missing
single-coefficient L² Cauchy estimate** plus its **cross-function
outer-annulus specialization**. This is the smallest sprint that exposes
a *coefficient-level* lower bound on `circleMeanSq f r` from a single
Cauchy coefficient, and — paired with outer pointwise dominance — gives a
clean cross-function comparison `‖a_k‖² · r^(2k) ≤ circleMeanSq g r / (2π)`
for every `r ∈ (c, 1)` and every `k`. It is the natural "single-summand
≤ tsum" Hardy primitive on top of sprint 010's canonical-witness Parseval,
the outer pointwise → outer circle-mean lift currently buried inline in
sprint 005, and the conjugate building block to sprint 016's three-circles
for any future Hayman / extremal-function c-push attempt.)

## Goal

Ship one new derived module `Proof/CauchyL2Estimate.lean` that pins three
public lemmas in Lean:

```lean
-- (1) Single-coefficient Cauchy L² estimate.
-- For analytic f on UnitDisk and any r ∈ (0, 1), the squared norm of
-- each Cauchy power-series coefficient times r^(2k) is bounded by the
-- normalized circle mean.
theorem cauchyPowerSeries_normSq_pow_le_circleMeanSq
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < 1) (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ circleMeanSq f r
```

```lean
-- (2) Outer-annulus circle-mean dominance from outer pointwise dominance.
-- A clean restatement of the outer-half radial step currently buried in
-- sprint 005's `validKorenblum_of_innerCircleMean_dom`. Public so future
-- consumers don't have to re-derive it.
theorem outer_circleMeanSq_dom_of_pointwise_dom
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {r : ℝ} (hr_gt_c : c < r) (hr_lt : r < 1) :
    circleMeanSq f r ≤ circleMeanSq g r
```

```lean
-- (3) Cross-function corollary: pairing (1) at f with (2) gives an upper
-- bound on f's k-th Cauchy coefficient at any outer radius r ∈ (c, 1) in
-- terms of circleMeanSq g r.
theorem cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    {r : ℝ} (hr_gt_c : c < r) (hr_lt : r < 1) (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k)
      ≤ circleMeanSq g r
```

The proof of (1) is a direct **single-summand ≤ tsum** bound on sprint
010's canonical-witness identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`:
`circleMeanSq f r = 2π · ∑' j, ‖a_j‖² · r^(2j)`. Each summand is
non-negative; therefore each individual term, including the `j = k` term,
is `≤` the tsum. Mathlib primitive: `Summable.le_tsum` (or its
specialization for non-negative summands). The summability hypothesis
is the same `summable_coeff_sq_pow` already exercised in sprint 016 (and
earlier, via private helpers in `BergmanParseval.lean` /
`AnnulusBergmanParseval.lean`); a re-derivation in the new file follows
the exact `FormalMultilinearSeries.summable_norm_mul_pow` pattern from
those files.

The proof of (2) is the outer-half radial step from sprint 005's
`validKorenblum_of_innerCircleMean_dom` proof, restated as a standalone
lemma. For each `r ∈ (c, 1)`, the per-θ comparison
`‖f (polarCoord.symm (r, θ))‖² ≤ ‖g (polarCoord.symm (r, θ))‖²` follows
from outer pointwise dominance applied to
`z := polarCoord.symm (r, θ) ∈ UnitDisk` (since `‖z‖ = r > c`), via
`pow_le_pow_left₀` on `‖·‖`. Then `setIntegral_mono_on` on the θ-interval
gives `circleMeanSq f r ≤ circleMeanSq g r`.

The proof of (3) is a one-line composition: chain (1) at `f` with (2),
both at the same `r`.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move builds a self-contained
per-candidate partial formalization on top of Mathlib (Cauchy L² coefficient
estimate plus outer-annulus circle-mean dominance), derived directly from
sprint 010's canonical-witness Parseval and sprint 005's outer-half radial
step (lifted to a public lemma). The only fixed target is the final theorem
shape.

## Why

- **It is the smallest sprint that exposes a coefficient-level lower bound
  on `circleMeanSq`.** Every existing scaffolding theorem in the workspace
  goes the other way: from coefficient norms to `circleMeanSq` (sprint 010,
  the canonical-witness Parseval) or from `circleMeanSq` to integrated
  Bergman (sprints 003, 011, 015). The Cauchy L² estimate is the first
  *converse* primitive: it bounds each individual Cauchy coefficient (times
  the right power of `r`) from above by `circleMeanSq f r`. This is the
  natural single-summand-vs-tsum inequality — and the building block for
  any future cross-function extremal-coefficient argument.

- **It is genuinely useful for c-push.** Pairing (1) with (2) gives the
  cross-function corollary (3): under outer pointwise dominance,
  `‖a_k‖² · r^(2k) ≤ circleMeanSq g r / (2π)` for every `r ∈ (c, 1)` and
  every `k`. Taking `r → c⁺` (via continuity of `circleMeanSq g r` from
  sprint 010's radial monotonicity, which is itself proved via the
  canonical Parseval) gives `‖a_k‖² · c^(2k) ≤ circleMeanSq g c / (2π)`.
  This is the single-radius coefficient bound needed to attack the
  inner-disk `bergmanNormSq` comparison via the half-disc Parseval
  expansion of sprint 015. (The full c-push still requires more — see
  *Out of scope* below — but this is one of the natural primitives any
  such argument must factor through.)

- **It exposes the buried outer-half radial step as a public lemma.**
  Sprint 005's `validKorenblum_of_innerCircleMean_dom` proof has the outer
  pointwise → outer circleMean dominance step buried inline. Sprints 013
  and 014 inherit this via the conditional reduction chain. But the
  outer step itself is never a public theorem. Pinning it as
  `outer_circleMeanSq_dom_of_pointwise_dom` is a small but useful
  refactoring: future c-push consumers can chain it with sprint 010's
  canonical Parseval, sprint 015's half-disc Parseval, sprint 016's
  three-circles, or the new (1) without re-deriving the same five-step
  pointwise → integrated argument.

- **The proof is bounded.** Sprint 010 already ships the canonical-witness
  Parseval `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
  which is what (1) reduces against. The summability of
  `‖a_k‖² · r^(2k)` is already exercised by sprint 016's `summable_coeff_sq_pow`
  (private), so the same pattern is available. The `tsum_ge_one_term`
  / `Summable.le_tsum` Mathlib primitive is one line. The proof of (2) is
  the same five-step outer-half radial pattern that already appears
  inline in sprint 005, and which the generator has shipped multiple
  times. ~150–250 lines total.

- **Falsifiable in one Generator session.** Each of the three theorems
  has a clean, well-documented Mathlib API shape:
  - (1) is `Summable.le_tsum` on the sprint 010 identity.
  - (2) is `setIntegral_mono_on` on the per-θ pointwise comparison.
  - (3) is one-line composition of (1) and (2).
  No new Mathlib API is needed beyond what sprints 005, 010, 011, 015,
  and 016 have already exercised. The generator has shipped each of
  these patterns separately; this sprint composes them.

- **Why not pursue the cross-function inner-radial dominance directly.**
  The full inner-radial dominance (i.e., the inner-half analogue of
  `outer_circleMeanSq_dom_of_pointwise_dom` — which is the heart of
  Wang's intermediate and would close the c-push without an axiom) is
  *false in general* without an additional analyticity-driven argument.
  The counterexample documented in sprint 011's notes (`f = z, g = 1`)
  shows that pointwise outer dominance does NOT imply pointwise inner
  dominance, and cannot easily transfer to circleMeanSq dominance on the
  inner half without subharmonic / Möbius / Hayman extremal-function
  arguments. This sprint pins the *one-side* (outer) of the comparison
  as a public lemma plus the natural Cauchy L² coefficient lower bound;
  the full inner-half comparison remains a separate, structurally larger
  question.

- **Why not pursue the half-disc Bergman comparison directly.** Sprint
  015's `innerDisk_bergmanNormSq_termwise_mono` already gives the
  inner-half Bergman comparison *given coefficient-norm dominance*
  `‖a_k‖ ≤ ‖b_k‖`. The current sprint does NOT provide that termwise
  bound — it provides a single-coefficient/circleMeanSq bound, not a
  cross-coefficient termwise one. The two are complementary: a future
  c-push consumer could combine them (e.g., bound `f`'s coefficients
  using (3), then chain through sprint 015's termwise machinery), but
  the cross-coefficient termwise bound from outer pointwise data is
  *not* a tautology and is structurally larger.

- **Why not pursue subharmonicity of `‖f‖²` directly.** The mean-value
  bound `‖f(z₀)‖² ≤ (1/πR²) ∫_{B(z₀, R)} ‖f‖² dA` for `R < 1 - ‖z₀‖`
  applies on a ball that for `z₀ ∈ innerDisk c` straddles the
  inner/outer split — so the mean-value bound alone does not separate
  the inner and outer contributions cleanly. (To make subharmonic
  mean-value useful for c-push, one needs a Möbius / Carleman boundary
  argument, which requires Mathlib API not currently exposed.) The
  Cauchy L² estimate of this sprint is the natural pointwise-coefficient
  primitive that does not require such a Möbius bridge.

- **Why not pursue proposal_001 trust-reduction.**
  `proposal_001_replace_seed_with_inner_radial_dominance.md` is `pending`
  and gates the V_trust trust-reduction sprint. Until human approval,
  that direction is blocked. This sprint advances goal #1 (c-push
  scaffolding) instead and is independent of the proposal's status. If
  the proposal is approved during this sprint's run, the next sprint
  can be the trust-reduction one (renumbered to match).

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"Parseval / boundary L² expansions on analytic functions"*, *"termwise
  summability and `tsum`-level rearrangements"*, *"bridging pointwise
  modulus inequalities to boundary integrals"*. Theorem (1) is precisely
  a `tsum` rearrangement (single summand ≤ tsum). Theorem (2) is
  precisely a pointwise → boundary-integral bridge. Theorem (3) is a
  one-line composition. The generator has shipped sprints 010/011/015/016
  on the same `tsum` machinery; this sprint is bounded between them in
  derivation cost.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CauchyL2Estimate.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.RadialBergman`, `Proof.AnalyticParseval`,
    `Proof.CircleMeanRadial`, `Proof.CircleExpBridge` (the same module
    set as `Proof.CircleMeanLogConvex`, since the proof reuses the
    canonical-witness Parseval and the polar-symm point bridge).

  - exposes the three headline theorems above:
    - `cauchyPowerSeries_normSq_pow_le_circleMeanSq`,
    - `outer_circleMeanSq_dom_of_pointwise_dom`,
    - `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq`.

  - **Implementation sketch for (1)
    `cauchyPowerSeries_normSq_pow_le_circleMeanSq`:**
    1. Apply
       `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
       (sprint 010) at the chosen `R`. This gives
       `circleMeanSq f r = 2π · ∑' j, ‖a_j‖² · r^(2j)`.
       Note: the canonical-witness identity in sprint 010 takes
       `r ∈ [0, 1)` (i.e., `0 ≤ r ∧ r < 1`); for `0 < r` the bound is
       a strict subset.
    2. Re-derive per-`r` summability of `‖a_j‖² · r^(2j)` by the same
       `FormalMultilinearSeries.summable_norm_mul_pow` route used in
       sprint 016's `summable_coeff_sq_pow` (private, so cannot be
       reused as-is). This is ~50 lines of standard
       `R'(r) := ⟨(r+1)/2, _⟩` plus
       `Summable.of_norm_bounded_eventually_nat` plus
       `cauchyPowerSeries_coeff_norm_radius_invariant` (sprint 011).
    3. Apply `Summable.le_tsum (Summable.of_nonneg_of_le ...) k (fun n _
       => ...)` (or the equivalent
       `single_le_tsum`-style lemma) to extract the `k`-th summand
       `‖a_k‖² · r^(2k) ≤ ∑' j, ‖a_j‖² · r^(2j)`.
       Mathlib name candidates: `Summable.le_tsum`,
       `Summable.tsum_ge_of_eventually_ge`, or
       `tsum_ge_of_summable_of_eventually_ge`. The cleanest spelling
       is likely `Summable.le_tsum hsum k (fun n hn => ...)` with
       `hn : n ≠ k`, demanding non-negativity of the off-diagonal
       summands (`‖a_n‖² · r^(2n) ≥ 0`).
    4. Multiply through by `2π` (which is positive) and rearrange via
       `mul_comm` / `ring` to match the headline.

  - **Implementation sketch for (2)
    `outer_circleMeanSq_dom_of_pointwise_dom`:**
    1. Unfold `circleMeanSq f r =
       ∫ θ in Ioo (-π) π, ‖f (polarCoord.symm (r, θ))‖²` and similarly
       for `g`.
    2. Apply `setIntegral_mono_on` (with measurability of the integrands
       via `ContinuousOn.measurable` / `Measurable.pow_const`, or
       `Continuous.measurable` after composing
       `polarCoord_symm_eq_exp` from sprint 006) and the per-θ
       comparison
       `‖f (polarCoord.symm (r, θ))‖² ≤ ‖g (polarCoord.symm (r, θ))‖²`.
    3. The per-θ comparison comes from outer pointwise dominance applied
       to `z := polarCoord.symm (r, θ)`. The membership conditions:
       - `z ∈ UnitDisk` because `‖z‖ = r < 1` (via
         `Complex.norm_polarCoord_symm` plus `abs_of_pos hr_pos`).
       - `c < ‖z‖` because `‖z‖ = r > c`.
       Then `pow_le_pow_left₀` on `‖f z‖ ≤ ‖g z‖` lifts to squared norms.
    4. Integrability of the per-θ integrand on `Ioo (-π) π` follows from
       continuity (via `polarCoord_symm_eq_exp` from sprint 006) plus
       `Continuous.integrableOn_Ioc.mono_set Ioo_subset_Ioc_self` (the
       same trick used in sprint 008).

  - **Implementation sketch for (3)
    `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq`:**
    Chain (1) at `f` with (2). For `r ∈ (c, 1)`:
    - (1) gives
      `(2π) · ‖a_k‖² · r^(2k) ≤ circleMeanSq f r`.
    - (2) gives `circleMeanSq f r ≤ circleMeanSq g r`.
    - Transitivity by `le_trans` closes the goal.

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must genuinely call sprint 010's
    `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
    not bypass via re-derivation.

- `ProofRefinement/Korenblum/Candidates/V17.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V17`, marked
  `-- @parent V16`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V16),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V16,
  - imports the same module set as V16 plus
    `ProofRefinement.Korenblum.Proof.CauchyL2Estimate`, so that the new
    module is part of V17's compile graph and is exercised by the
    build. No structural use of the new theorems in V17 itself is
    required (the consumer is a future c-push sprint).

- No edits to `lemma.toml`. No edits to V0/.../V16 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V17` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V17.lean` succeeds (the
   evaluator accepts V17 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V16; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/CauchyL2Estimate.lean`
   contains at least the three `theorem`s (or `lemma`s) listed above:
   - `cauchyPowerSeries_normSq_pow_le_circleMeanSq` (single-coefficient
     L² estimate),
   - `outer_circleMeanSq_dom_of_pointwise_dom` (outer-half radial
     comparison from outer pointwise dominance),
   - `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` (cross-function
     corollary).
   All three must be `theorem` / `lemma`, never `axiom`, with no
   `sorry`. The proofs must genuinely call sprint 010's
   `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
   (for theorem (1)) and a Mathlib `setIntegral_mono` primitive (for
   theorem (2)) — not bypass via direct re-derivation.

4. The new module `Proof.CauchyL2Estimate` must be **used**, even
   trivially, somewhere in V17's transitive compile graph (importing it
   from V17 is sufficient — it forces the module to compile as part of
   V17's build).

5. The headline theorem statements must be **internally consistent**
   with the sprint 010 / 011 / 015 / 016 stack. In particular,
   summing `cauchyPowerSeries_normSq_pow_le_circleMeanSq` over all `k`
   (after dividing by `(2π)`) should reproduce sprint 010's Parseval
   identity at `r` (modulo non-negativity); the sprint does *not*
   need to ship this consistency check as a theorem, but the headline
   shape must be such that this consistency holds.

## Out of scope

- Edit older candidates (`V0.lean` through `V16.lean`) or the existing
  `Proof/*.lean` files. In particular, do **not** lift the inline outer
  pointwise → outer circleMean step out of `Proof/RadialSplit.lean`'s
  `validKorenblum_of_innerCircleMean_dom`: ship the new public lemma in
  the new file `Proof/CauchyL2Estimate.lean` and let any future consumer
  switch to the public lemma. Refactoring sprint 005 in place is a
  separate concern.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms, no `hWang_inner_radial_dominance_3554`). If the
  proof is genuinely blocked on a missing Mathlib API, the Generator
  must `STATUS=BLOCKED` with the precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the Cauchy L² coefficient estimate plus
  outer-annulus circle-mean dominance primitive that future c-push
  consumers will factor through.

- Edit `lemma.toml` (no policy expansion in this sprint; the
  proposal_001 trust-reduction edit is gated on human approval).

- Pursue the **inner-half** analogue of (2): there is no clean
  cross-function inner-half circle-mean dominance from outer pointwise
  dominance alone. Attempting to ship one would require either a
  Möbius / pseudohyperbolic disk argument (Mathlib API absent) or a
  Hayman-style extremal-function argument (structurally large). The
  current sprint pins only the **outer** direction plus the
  single-coefficient L² estimate; the inner-half comparison is the
  genuine Korenblum content and is deferred.

- Pursue a **uniform termwise coefficient bound** `‖a_k‖ ≤ ‖b_k‖` from
  outer pointwise dominance. As documented in sprint 011, this
  cross-function termwise bound is *false in general* (counterexample
  `f = z, g = 1`). The current sprint deliberately ships only the
  single-radius coefficient/circleMean bound, which is true and
  composable with sprint 015's termwise consumers when paired with an
  additional argument the future c-push must supply.

- Take the limit `r → c⁺` in (3) to extract a `‖a_k‖² · c^(2k) ≤
  circleMeanSq g c / (2π)` boundary form. This requires continuity of
  `circleMeanSq g r` at `r = c` (which follows from sprint 010's radial
  monotonicity and the canonical Parseval, but adding this corollary
  pushes the sprint beyond a single-session bound). Defer to a follow-up.

## Time budget

≤ 90 minutes runtime. (The proof of (1) is comparable in shape to
sprint 016's per-`r` summability re-derivation plus a one-line
`Summable.le_tsum` extraction; the proof of (2) is the five-step
outer-half radial pattern from sprint 005, lifted to a public lemma; the
proof of (3) is a one-line `le_trans` composition. Each is ~50–100 lines.
Total ~150–250 lines. The same Mathlib API surface as sprints 010, 011,
015, 016.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. the `Summable.le_tsum`-style Mathlib lemma
  is not callable in the expected shape, or the per-`r` summability
  re-derivation requires more bookkeeping than the time budget admits,
  or the `polarCoord.symm` continuity / measurability for theorem (2)'s
  `setIntegral_mono_on` produces an unexpected friction):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (`Summable.le_tsum` vs `tsum_ge_of_summable_of_eventually_ge`
  vs `single_le_tsum` for theorem (1); `setIntegral_mono_on` vs
  `setIntegral_mono_ae_restrict` for theorem (2)).

  **Fallback form A** (if all three theorems are too ambitious in one
  session): the Generator may instead ship only theorem (1)
  `cauchyPowerSeries_normSq_pow_le_circleMeanSq`, deferring (2) and (3)
  to a follow-up sprint. The fallback is acceptable if and only if the
  Generator records in `Experience.md` why (2)/(3) were deferred, and
  theorem (1) is genuinely Lean-pinned (no `sorry`, no `axiom`).

  **Fallback form B** (if even theorem (1) is materially blocked on the
  `Summable.le_tsum` step): the Generator may instead ship the
  **finite-sum form**

  ```lean
  theorem cauchyPowerSeries_normSq_pow_partial_le_circleMeanSq
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
      {r : ℝ} (hr_pos : 0 < r) (hr_lt : r < 1) (N : ℕ) :
      (2 * Real.pi) *
        (∑ k ∈ Finset.range N, ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * r ^ (2 * k))
        ≤ circleMeanSq f r
  ```

  i.e., the Cauchy L² estimate at the level of partial sums of the
  Parseval expansion, before passing to the `tsum` limit. The
  `tsum`-level passage to the limit is then deferred to a follow-up
  sprint. The fallback is acceptable if and only if the Generator
  records in `Experience.md` why the `tsum`-level form was deferred.

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
