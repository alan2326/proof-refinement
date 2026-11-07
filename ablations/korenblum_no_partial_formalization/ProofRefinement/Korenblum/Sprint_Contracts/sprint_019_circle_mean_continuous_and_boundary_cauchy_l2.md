# Sprint 019: continuity of `circleMeanSq f r` + boundary `r → c` Cauchy L² coefficient bound

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V18.lean`
**Target file**: `Candidates/V19.lean`
**Direction**: section2-proof / scaffolding-for-c-push (the **deferred boundary
extension** named in sprint 017's *Out of scope*. Sprint 017 explicitly
deferred *"the limit `r → c⁺` in (3) to extract a `‖a_k‖² · c^(2k) ≤
circleMeanSq g c / (2π)` boundary form"* on the grounds that it requires
continuity of `circleMeanSq g r` at `r = c`. This sprint pins both: (a) the
continuity of `r ↦ circleMeanSq f r` for `f` analytic on `UnitDisk` on the
half-open ray `[0, 1)`, and (b) the boundary form of sprint 017's
cross-function Cauchy L² estimate. The boundary form is the natural
*coefficient-level* bound at the inner-disk-boundary radius `c`, the seed
of any future Hayman-style extremal-function argument: it gives a uniform
upper bound on every Cauchy coefficient `‖a_k(f)‖² · c^(2k)` of the
"smaller" function `f` in terms of `circleMeanSq g c`, the circle mean of
the "larger" function evaluated at the critical inner radius.)

## Goal

Ship one new derived module `Proof/CircleMeanContinuous.lean` that pins
two public theorems in Lean:

```lean
-- (1) Continuity of `r ↦ circleMeanSq f r` on `[0, 1)`.
-- For f analytic on UnitDisk and any compact subinterval `[0, ρ]` with
-- ρ < 1, `r ↦ circleMeanSq f r` is continuous on `[0, ρ]`.
-- The cleanest universal form is continuity at every r₀ ∈ [0, 1).
theorem continuousAt_circleMeanSq_of_analyticOn_unitDisk
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀_lt : r₀ < 1) :
    ContinuousAt (fun r : ℝ => circleMeanSq f r) r₀
```

```lean
-- (2) Boundary `r → c⁺` form of sprint 017's cross-function Cauchy L²
-- coefficient estimate.
-- For `f, g` analytic and A²-integrable on UnitDisk with outer pointwise
-- dominance `‖f‖ ≤ ‖g‖` on `c < ‖z‖ < 1`, every Cauchy coefficient of f
-- at the boundary radius `c` is bounded:
--   (2π) · ‖a_k(f)‖² · c^(2k) ≤ circleMeanSq g c.
-- The coefficient is the canonical-witness one: `(cauchyPowerSeries f 0 R).coeff k`
-- for any chosen `R ∈ (c, 1)`.
theorem cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq
    {f g : ℂ → ℂ}
    (hf_an : AnalyticOn ℂ f UnitDisk) (hg_an : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_outer : ∀ z ∈ UnitDisk, c < ‖z‖ → ‖f z‖ ≤ ‖g z‖)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (k : ℕ) :
    (2 * Real.pi) * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2 * c ^ (2 * k)
      ≤ circleMeanSq g c
```

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move builds a self-contained per-candidate
partial formalization on top of Mathlib (continuity of `circleMeanSq` on
`[0, 1)` plus the boundary coefficient bound), derived directly from sprint
010's canonical-witness Parseval and sprint 017's outer-half cross-function
estimate. The only fixed target is the final theorem shape.

## Why

- **It is the smallest sprint that exposes a coefficient-level upper bound
  at `r = c`.** Sprint 017's cross-function corollary
  `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` gives
  `(2π) ‖a_k(f)‖² · r^(2k) ≤ circleMeanSq g r` only for **strictly outer**
  `r ∈ (c, 1)`. The boundary radius `r = c` is precisely where any
  inner-half / outer-half Korenblum chain meets. Without a bound at `r = c`
  itself, every downstream consumer that wants to integrate against an
  inner weight (e.g., the inner-disk Bergman Parseval expansion `∑'
  (π/(k+1)) c^(2k+2) ‖a_k(f)‖²` of sprint 015) has to add a continuity /
  limit argument inline. Pinning the boundary bound as a public lemma is
  the natural primitive for every such consumer.

- **It pins continuity of `circleMeanSq f r` as a standalone lemma.**
  Sprint 010's `circleMeanSq_radial_mono` already gives **monotonicity**
  on `[0, 1)`, which combined with continuity gives sequential limit
  access (`Filter.Tendsto.le_of_le`). Continuity itself is a stronger
  primitive: it gives access to *any* limit, not just monotone ones, and
  is the right primitive for any future "`r ↘ c`" or "`r ↗ c`" passage.
  The route through Weierstrass M-test on the canonical-witness Parseval
  is well-trodden and within the generator's declared scope.

- **The proof is bounded.** Theorem (1) is uniform-on-compacts convergence
  of `2π ∑' k ‖a_k‖² · r^(2k)` plus continuity of each summand
  `r ↦ ‖a_k‖² · r^(2k)`. The summability of `‖a_k‖² · ρ^(2k)` for any
  `ρ < 1` is the same fact already exercised by sprint 016
  (`summable_coeff_sq_pow`, private) and by sprints 011/015/017/018 (each
  re-derives inline via `FormalMultilinearSeries.summable_norm_mul_pow`
  plus `Summable.of_norm_bounded_eventually_nat`). The Mathlib API for
  uniform-on-compacts continuity of a tsum from a Weierstrass M-bound is
  one of `tendstoUniformlyOn_tsum`, `Continuous.tsum_of_summable_norm`,
  or `tendstoUniformlyOn_of_tendstoUniformly_of_summable`. ~200–300 lines.

- **Theorem (2) is theorem (1) plus a one-line sequential limit.** With
  continuity of `circleMeanSq g` at `r = c` in hand, sprint 017's
  cross-function bound `(2π) ‖a_k(f)‖² · r^(2k) ≤ circleMeanSq g r` for
  `r ∈ (c, 1)` passes to the limit `r ↘ c`. Mathlib API: pick a sequence
  `r_n := c + 1/(n+1)` (or `r_n := (c + 1)/2 - (1 - c)/(2(n+1))`),
  apply sprint 017's bound at each `r_n`, take `limsup`. The `r_n` LHS
  tends to `(2π) ‖a_k(f)‖² · c^(2k)` by continuity of `r ↦ r^(2k)`; the
  RHS tends to `circleMeanSq g c` by theorem (1). One use of
  `Filter.Tendsto.le_of_le` closes it. ~50–80 lines.

- **Falsifiable in one Generator session.** Both theorems have clean
  Mathlib API shapes. Theorem (1)'s Weierstrass M-test is a canonical
  proof pattern; Mathlib has `tendstoUniformlyOn_tsum` (which gives
  uniform convergence of partial sums from M-summability) plus
  `Continuous.continuousOn` for the `tsum` from uniform convergence of
  continuous partial sums. Theorem (2)'s sequential limit argument is a
  canonical `Filter.Tendsto.le_of_le` plus `Filter.Tendsto.const_mul`
  composition. The generator has shipped sprint 016's `tsum`-level
  Hadamard inequality, which exercises the same level of summability
  bookkeeping; this sprint is bounded between sprint 016 and sprint 017
  in derivation cost.

- **Why not pursue Möbius / pseudohyperbolic disk machinery.** The Möbius
  automorphism `φ_a(z) = (z-a)/(1-conj(a)·z)` and Bergman A² conformal
  invariance are the heaviest analytic toolkit Hayman / Korenblum / Wang
  use, and would unlock the cleanest c-push path — but that is a
  structurally large derivation (multi-sprint). The boundary Cauchy L²
  bound of this sprint is the *next* primitive, strictly inside the
  area-Cauchy / Parseval toolkit, that the workspace's existing
  infrastructure supports in one session.

- **Why not pursue the deferred general-interior-point sub-mean-value
  (sprint 018 Fallback A) instead.** Theorem (2) of sprint 018
  (`normSq_pointwise_le_ball_integral`) is a translation/scaling of
  sprint 018's theorem (1), and pins outer→pointwise transport at
  arbitrary interior points. It is a useful primitive but is essentially
  *transformation* of an existing primitive, not a new analytical chain.
  By contrast, this sprint's theorem (2) opens the *coefficient-level
  boundary* chain, which is genuinely new content for the Hayman
  extremal-function direction. If the planner had to choose, the
  boundary bound is strictly higher analytic novelty per session. (The
  general-interior-point sub-mean-value remains a worthy follow-up
  direction; it can be picked up in sprint 020+.)

- **Why not attempt the full c-push directly.** The c-push attempt itself
  (combining boundary Cauchy L² bounds with inner-disk Bergman Parseval,
  bounding `∫_{innerDisk c} ‖f‖²` against `∫_{innerDisk c} ‖g‖²`) is
  structurally larger and requires careful summability bookkeeping at the
  boundary radius. Pinning continuity and the boundary form first as
  public lemmas allows the next sprint to attack the c-push without
  re-deriving these inline. This is the single-session bound.

- **Why not pursue right-continuity of `circleMeanSq` only at `r = c`.**
  Continuity at every `r₀ ∈ [0, 1)` is essentially the same proof effort
  as right-continuity at one point: both factor through Weierstrass
  M-test on a compact subinterval `[0, ρ]` with `ρ ∈ (r₀, 1)` (or
  `ρ ∈ (c, 1)` in the one-point case). The universal form is a stronger
  public lemma at no additional cost. Future consumers may need
  continuity at radii other than `c` (e.g., for sprint 017's continuity-
  based corollary at any `r > c`), so the universal form is preferred.

- **Why not pursue proposal_001 trust-reduction.**
  `proposal_001_replace_seed_with_inner_radial_dominance.md` is `pending`
  and gates the trust-reduction sprint. Until human approval, that
  direction is blocked. This sprint advances goal #1 (c-push scaffolding)
  instead and is independent of the proposal's status.

- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Parseval
  / boundary L² expansions on analytic functions"*, *"termwise summability
  and `tsum`-level rearrangements"*, *"bridging pointwise modulus
  inequalities to boundary integrals"*, *"`nlinarith` / `polyrith` /
  `field_simp` / `ring` chains hundreds of lines long"*. Theorem (1) is
  precisely a uniform-on-compacts `tsum`-level rearrangement (the
  Weierstrass M-test at the level of `Summable`). Theorem (2) is precisely
  a sequential limit on a Mathlib `Filter.Tendsto` chain. The generator
  has shipped sprints 010, 011, 015, 016, 017, 018 on the same `tsum`
  machinery; this sprint composes them with continuity-from-uniform-
  convergence.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleMeanContinuous.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.RadialBergman`, `Proof.AnalyticParseval`, `Proof.CircleMeanRadial`,
    `Proof.BergmanParseval`, `Proof.CauchyL2Estimate` (the same module set
    as `Proof.CauchyL2Estimate` plus a dependency on `Proof.CauchyL2Estimate`
    itself, since theorem (2)'s proof routes through sprint 017's cross-
    function Cauchy L² estimate).

  - exposes the two headline theorems above:
    - `continuousAt_circleMeanSq_of_analyticOn_unitDisk` (continuity),
    - `cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq` (boundary
      coefficient bound).

  - **Implementation sketch for (1)
    `continuousAt_circleMeanSq_of_analyticOn_unitDisk`:**

    1. Pick `R := ⟨(r₀ + 1) / 2, _⟩ : ℝ≥0` so that `r₀ < (R : ℝ) < 1`.
       (The exact choice `R := ⟨(r₀ + 1) / 2, _⟩` is what sprints 010, 011,
       015, 016 use.)
    2. Pick `ρ := (r₀ + R) / 2` so that `0 ≤ r₀ < ρ < (R : ℝ)`. This is
       the compact-set radius for the M-test.
    3. By sprint 010's
       `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
       for any `r ∈ [0, ρ]`,
       `circleMeanSq f r = ∑' k, (2π · r^(2k)) · ‖a_k‖²`
       where `a_k := (cauchyPowerSeries f 0 R).coeff k`.
    4. By the `FormalMultilinearSeries.summable_norm_mul_pow` route used
       by sprints 011, 015, 016, 017, 018, the M-bound
       `‖a_k‖² · ρ^(2k)` is summable. (Re-derive inline; the existing
       helpers like `summable_coeff_sq_pow` are `private`.)
    5. Each summand `r ↦ (2π · r^(2k)) · ‖a_k‖²` is continuous in `r`.
    6. By Mathlib's M-test API (one of `tendstoUniformlyOn_tsum`,
       `tendstoUniformlyOn_of_summable_nnnorm`,
       `Summable.tendstoUniformlyOn_of_norm_le`, or
       `continuousOn_tsum_of_summable`), the partial sums converge
       uniformly on `[0, ρ]` to `circleMeanSq f r`.
    7. Uniform convergence of continuous partial sums ⇒ the limit is
       continuous on `[0, ρ]` (Mathlib: `TendstoUniformlyOn.continuousOn`
       or `ContinuousOn.tsum_of_summable_norm`).
    8. Continuity on `[0, ρ]` plus `r₀ ∈ Set.Ico 0 ρ` (the open subset)
       gives `ContinuousAt` at `r₀` (Mathlib:
       `ContinuousOn.continuousAt` with `IsOpen` membership).

    A potentially cleaner route: prove continuity directly via the
    `Continuous.tsum` API if Mathlib exposes a version that takes
    `Summable F` for `F : ι → α →ᵤ β` (uniform convergence of bounded
    continuous functions on a compact). The generator picks whichever
    Mathlib API gives the shortest proof.

    A **third route** routes through `HasFPowerSeriesOnBall.continuousOn`
    indirectly: the sum `∑ ‖a_k‖² · t^k` (with `t = r²`) is the diagonal
    Parseval power series, which is continuous on its domain of
    convergence by general analytic-function continuity. This is shorter
    if Mathlib's API exposes `continuousOn` for a `tsum` of the form
    `∑' k, c_k · t^k` directly. The generator should investigate but is
    not required to use this route.

  - **Implementation sketch for (2)
    `cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq`:**

    1. Define a sequence `r_n := c + (1 - c)/(n + 2) : ℝ` so that
       `r_n ∈ Ioo c 1` for every `n` and `r_n ↘ c`.
       Verify: `0 < c < r_n < 1` via `add_pos` / arithmetic, `r_n ↘ c`
       via `Filter.Tendsto.const_add` plus
       `Filter.Tendsto.div_atTop_const`.
    2. Apply sprint 017's
       `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` at each
       `r_n`:
       `(2π) · ‖a_k(f)‖² · r_n^(2k) ≤ circleMeanSq g r_n`.
    3. By theorem (1) above (continuity of `circleMeanSq g` at `r = c`),
       `circleMeanSq g r_n → circleMeanSq g c` as `n → ∞`.
    4. The LHS `(2π) · ‖a_k(f)‖² · r_n^(2k) → (2π) · ‖a_k(f)‖² · c^(2k)`
       by continuity of `r ↦ r^(2k)` (`Filter.Tendsto.pow`).
    5. By `Filter.Tendsto.le_of_le` (or `le_of_tendsto_of_tendsto`),
       `(2π) · ‖a_k(f)‖² · c^(2k) ≤ circleMeanSq g c`.
    6. Rearrange via `mul_assoc` / `mul_comm` to match the headline.

    A potential pitfall: `Filter.Tendsto.le_of_le` requires both sides to
    have a limit and an eventual `≤`. The `eventually` form is one of
    `Filter.eventually_of_forall` (since the bound holds for *every* `n`,
    not just eventually). Mathlib name: `le_of_tendsto_of_tendsto'` or
    `Tendsto.le_of_le` (variants exist).

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must genuinely call sprint 010's
    `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` (for
    the tsum identity that powers the M-test in (1)) and sprint 017's
    `cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` (for the
    cross-function bound at outer radii in (2)) — not bypass via direct
    re-derivation.

- `ProofRefinement/Korenblum/Candidates/V19.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V19`, marked
  `-- @parent V18`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V18),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V18,
  - imports the same module set as V18 plus
    `ProofRefinement.Korenblum.Proof.CircleMeanContinuous`, so that the
    new module is part of V19's compile graph and is exercised by the
    build. No structural use of the new theorems in V19 itself is
    required (the consumer is a future c-push sprint).

- No edits to `lemma.toml`. No edits to V0/.../V18 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V19` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V19.lean` succeeds (the
   evaluator accepts V19 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V18; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/CircleMeanContinuous.lean`
   contains **at least theorem (1)** as a `theorem` (not `lemma`,
   not `axiom`, no `sorry`):
   - `continuousAt_circleMeanSq_of_analyticOn_unitDisk`.
   The proof must genuinely call sprint 010's
   `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
   for the Parseval tsum identity, and exercise a Mathlib uniform-
   convergence / M-test API (e.g., `tendstoUniformlyOn_tsum`,
   `Continuous.tsum_of_summable_norm`, or
   `ContinuousOn.tsum_of_summable_norm`) — not bypass via direct
   computation.

4. The file ideally also contains theorem (2)
   `cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq`. **Fallback
   A** below specifies what to ship if the sequential-limit step in
   theorem (2) hits a Mathlib-API friction.

5. The new module `Proof.CircleMeanContinuous` must be **used**, even
   trivially, somewhere in V19's transitive compile graph (importing it
   from V19 is sufficient — it forces the module to compile as part of
   V19's build).

6. The headline theorem statements must be **internally consistent**
   with the sprint 010 / 015 / 017 stack. In particular:
   - Theorem (1) at `f := constant function c` gives
     `circleMeanSq (const c) r = 2π · ‖c‖²`, which is a constant function
     of `r` and hence continuous everywhere. (Sanity check; no theorem
     to ship.)
   - Theorem (1) at `f := z` gives `circleMeanSq (id) r = 2π · r²`,
     which is continuous in `r`. (Sanity check; no theorem to ship.)
   - Theorem (2) at `r₀ = c` is an extension of sprint 017's (3)
     by sequential limit: at any `r > c`, sprint 017's (3) applies; at
     `r = c`, theorem (2) of this sprint applies. (Internal consistency
     check; no theorem to ship.)

## Out of scope

- Edit older candidates (`V0.lean` through `V18.lean`) or the existing
  `Proof/*.lean` files. In particular, do **not** lift any private helper
  from `Proof/CircleMeanRadial.lean`, `Proof/BergmanParseval.lean`,
  `Proof/CircleMeanLogConvex.lean`, or `Proof/SubMeanValue.lean` —
  re-derive inline if needed.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`,
  no new analytic axioms). If the proof is genuinely blocked on a
  missing Mathlib API, the Generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the continuity + boundary coefficient
  bound primitives that future c-push consumers will factor through.

- Edit `lemma.toml` (no policy expansion in this sprint; the
  proposal_001 trust-reduction edit is gated on human approval).

- **Pursue the c-push attempt directly via boundary coefficient bound +
  inner-disk Bergman Parseval expansion + summation.** That is the
  structurally larger follow-up sprint that consumes this primitive.
  Attempting both in one session would blow the time budget.

- **Pursue the full continuity of `r ↦ circleMeanSq f r` on the closed
  interval `[0, 1]` (or even on the closed interval `[0, ρ]` with
  `ρ < 1`).** Closed-interval continuity requires extending the canonical-
  witness Parseval to `r = R` (the radius itself), which is structurally
  larger (boundary behavior of power series). Half-open continuity on
  `[0, 1)` is sufficient for all downstream consumers and is what this
  sprint pins.

- **Pursue the deferred general-interior-point sub-mean-value (sprint
  018 Fallback A).** That is a useful follow-up direction but is
  orthogonal to this sprint's content and would push the time budget.

- **Pursue derivative / smoothness of `r ↦ circleMeanSq f r`.** The
  function is real-analytic on `[0, 1)` by the same M-test argument
  applied to derivatives, but the boundary form (2) does not need
  smoothness; only continuity. Smoothness is deferred to a future
  sprint if it becomes useful.

## Time budget

≤ 90 minutes runtime. (Theorem (1) is a uniform-on-compacts continuity
proof from a Weierstrass M-test on the canonical-witness Parseval, ~150–
250 lines. Theorem (2) is a one-line sequential-limit composition of
theorem (1) with sprint 017's (3), ~50–80 lines. Total ~200–330 lines.
The same Mathlib API surface as sprints 010, 011, 015, 016, 017, 018.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. Mathlib's M-test / uniform-convergence API
  has an unexpected shape, or the M-bound summability re-derivation
  requires more bookkeeping than the time budget admits, or theorem (2)'s
  sequential-limit `Filter.Tendsto.le_of_le` produces an unexpected
  friction): `STATUS=BLOCKED` with a precise note in `Experience.md`
  recording which Mathlib lemma was the obstruction and which approaches
  were tried (`tendstoUniformlyOn_tsum` vs `Continuous.tsum_of_summable_norm`
  vs `ContinuousOn.tsum_of_summable_norm` for theorem (1);
  `Filter.Tendsto.le_of_le` vs `le_of_tendsto_of_tendsto'` vs sequential
  `Tendsto.const_mul` vs the diagonal Parseval power-series route for
  theorem (2)).

  **Fallback A** (theorem (2) is too ambitious in one session): the
  Generator may instead ship only theorem (1)
  `continuousAt_circleMeanSq_of_analyticOn_unitDisk`, deferring (2) to a
  follow-up sprint. The fallback is acceptable if and only if the
  Generator records in `Experience.md` why (2) was deferred (e.g. which
  sequential-limit primitive was the obstruction and which alternative
  routes — `Filter.Tendsto.le_of_le`, `le_of_tendsto_of_tendsto'`, direct
  `liminf` argument — were tried).

  **Fallback B** (theorem (1) is materially blocked on the Weierstrass
  M-test API form, e.g. the `tendstoUniformlyOn_tsum` shape does not
  unify with the canonical-witness Parseval): the Generator may instead
  ship a strictly weaker **`ContinuousOn` form** restricted to a chosen
  compact subinterval `[0, ρ]` for any single `ρ < 1`:

  ```lean
  theorem continuousOn_circleMeanSq_of_analyticOn_unitDisk_compact
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
      ContinuousOn (fun r : ℝ => circleMeanSq f r) (Set.Icc 0 ρ)
  ```

  The fallback is acceptable if and only if the Generator records in
  `Experience.md` why the universal `ContinuousAt` form was deferred
  and the `ContinuousOn` form is genuinely Lean-pinned. (Note: theorem
  (2) of this sprint can still be derived from the `ContinuousOn` form
  by picking `ρ ∈ (c, 1)` and noting `c ∈ [0, ρ]`, so this fallback
  does not cascade into Fallback A.)

  **Fallback C** (both theorem (1) and theorem (2) are materially
  blocked, e.g. on the per-`r` summability re-derivation): the
  Generator may instead ship **only the partial-sum form** of the
  uniform-convergence step:

  ```lean
  theorem partial_sum_circleMeanSq_uniform_bound
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
      {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_lt_R : ρ < (R : ℝ))
      (N : ℕ) :
      ∀ r ∈ Set.Icc 0 ρ,
        |circleMeanSq f r
            - ∑ k ∈ Finset.range N,
                (2 * Real.pi * r ^ (2 * k))
                  * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2|
          ≤ ∑' k : ℕ, if k < N then 0 else
              (2 * Real.pi * ρ ^ (2 * k))
                * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
  ```

  i.e., the M-test bound *before* extracting continuity. The
  `tsum`-level continuity passage is then deferred. The fallback is
  acceptable if and only if the Generator records in `Experience.md`
  why the continuity form was deferred. (This is a weaker fallback;
  prefer Fallback A or B.)

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change, or a Mathlib
  primitive that requires a workspace-import-policy edit):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
