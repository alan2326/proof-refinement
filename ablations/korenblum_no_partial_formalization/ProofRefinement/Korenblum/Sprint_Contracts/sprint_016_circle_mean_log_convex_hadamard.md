# Sprint 016: log-convexity of `r ↦ circleMeanSq f r` (Hadamard three-circles for A²)

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V15.lean`
**Target file**: `Candidates/V16.lean`
**Direction**: section2-proof / scaffolding-for-c-push (Hardy / Bergman
log-convexity primitive: `circleMeanSq f r` is log-convex in `log r` on
`(0, 1)`. This is the Hadamard three-circles theorem specialised to the
A² circle mean of an analytic function on the unit disk. It is the
single-function Hardy-class tool that any future Korenblum-style
cross-radius transport argument must factor through.)

## Goal

Ship one new derived module `Proof/CircleMeanLogConvex.lean` that pins,
in Lean, the **multiplicative form** of Hadamard's three-circles theorem
for `circleMeanSq` of an analytic function:

```lean
theorem circleMeanSq_geometric_mean_le
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 < r₂) (hr₂' : r₂ < 1) :
    circleMeanSq f (Real.sqrt (r₁ * r₂)) ^ 2
      ≤ circleMeanSq f r₁ * circleMeanSq f r₂
```

(Equivalently in `log` form: `log circleMeanSq f` is convex in `log r` on
`(0, 1)` — but the multiplicative form above is what the Lean proof
ships, since it avoids `log circleMeanSq f r` being `-∞` when
`circleMeanSq f r = 0` for `f ≡ 0`.)

The proof is a direct **Cauchy–Schwarz on the Parseval `tsum`** of
sprint 010's `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`:

```
circleMeanSq f r = 2π ∑' k, ‖a_k‖² · r^(2k)
```

Setting `r = √(r₁ r₂)` so `r^(2k) = (r₁ r₂)^k = r₁^k · r₂^k`, the bound is

```
(2π ∑' k, ‖a_k‖² r₁^k · r₂^k)²
   ≤ (2π ∑' k, ‖a_k‖² r₁^(2k)) · (2π ∑' k, ‖a_k‖² r₂^(2k))
```

via Cauchy–Schwarz on `tsum`s with `u_k := ‖a_k‖ · r₁^k` and
`v_k := ‖a_k‖ · r₂^k`:
`(∑' u_k v_k)² ≤ (∑' u_k²) · (∑' v_k²)`. The Mathlib name for this is
`MeasureTheory.inner_mul_le_norm_mul_norm` on the counting measure, or
more directly `inner_mul_le_norm_mul_norm` for `lp 2`, or — most
elementary — the discrete Cauchy–Schwarz
`Finset.inner_mul_le_norm_mul_norm` paired with the partial-sum-≤-tsum
limit.

We also expose the **log-additive form** for the symmetric three-circles
inequality `r₃ = r₁^a · r₂^(1-a)`:

```lean
theorem circleMeanSq_log_convex
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                 (hr₂ : 0 < r₂) (hr₂' : r₂ < 1)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    circleMeanSq f (r₁ ^ a * r₂ ^ (1 - a))
      ≤ circleMeanSq f r₁ ^ a * circleMeanSq f r₂ ^ (1 - a)
```

via Hölder's inequality on the same Parseval `tsum`:
`u_k := (‖a_k‖² r₁^(2k))^a`, `v_k := (‖a_k‖² r₂^(2k))^(1-a)` with
exponents `1/a` and `1/(1-a)` (degenerate cases `a = 0, 1` handled by
direct evaluation).

The Hölder form (`circleMeanSq_log_convex`) is the headline; the
geometric-mean form (`circleMeanSq_geometric_mean_le`) is the special
case `a = 1/2`, exposed as a corollary because Cauchy–Schwarz is the
shorter Lean proof and may be derived first.

In this no-partial-formalization arm there is no `(15)` reduction or
Wang Section 2 hypothesis bundle. The move builds a self-contained
per-candidate partial formalization on top of Mathlib (Hadamard's
three-circles for the A² circle mean), derived directly from sprint 010's
canonical-witness `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
plus Mathlib's discrete Hölder / Cauchy–Schwarz inequality.

## Why

- **The smallest sprint that exposes a cross-radius analytic primitive.**
  Every existing scaffolding theorem either fixes a single radius
  (`circleMeanSq f r`, `circleMeanSq_eq_tsum_cauchyPowerSeries`) or
  composes radii additively (`bergmanNormSq_eq_tsum_cauchyPowerSeries`,
  half-disc Parseval). Hadamard's three-circles is the first
  *multiplicative* / *log-convex* relation between `circleMeanSq` at
  three different radii. It is the natural next Hardy-class primitive
  and the only one that gives a non-trivial bound on `circleMeanSq f r`
  for `r` in the *interior* of an interval given the values at the
  endpoints.

- **It is genuinely useful for c-push.** The c-push goal of AGENT_BRIEF
  (#1) requires comparing inner-half `circleMeanSq` of `f` and `g`
  given outer-half pointwise dominance. As documented in sprint 015,
  this comparison is *not* a tautology — the radial transport from
  outer to inner is genuinely false in general (counterexample
  `f(z) = z, g(z) = √0.1 + z²`: `circleMeanSq f r = 2π r²`,
  `circleMeanSq g r = 2π (0.1 + r⁴)`; outer-radial dominance holds for
  `r` near 1 but fails for `r ≤ √(1/3) ≈ 0.577`). Hadamard's
  three-circles bounds the *worst case* of this radial transport via
  log-convexity: at the geometric-mean radius `r = √(r₁ r₂)`,
  `circleMeanSq f r` cannot exceed the geometric mean of the values at
  `r₁, r₂`. This bound is *not* enough on its own to push `c`; but
  combined with a future Hayman-style coefficient-level extremal
  argument (which is the genuine Korenblum content), it is one of the
  natural composable primitives.

- **Mathematically grounded.** The result is classical: for `f`
  analytic on the disk, `M_2(f, r) := circleMeanSq f r = 2π ∑ ‖a_k‖² r^(2k)`
  is a power series in `r²` with non-negative coefficients, hence
  `log M_2(f, r)` is convex in `log r`. (More generally, `log M_p(f, r)`
  is convex in `log r` for any `p ≥ 1`; the case `p = 2` is the
  cleanest because Parseval is exact.) The classical reference is
  Hardy 1915 / Hardy–Littlewood 1932; in the modern Bergman literature
  it is Hadamard's three-circles for the A² norm, and the proof is
  Cauchy–Schwarz on the `tsum` (or Hölder for general `a ∈ (0,1)`).

- **The proof is bounded.** Sprint 010 already ships
  `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
  the canonical-witness Parseval. The new module:
  1. unfolds both sides via sprint 010's identity at a chosen
     `R := ⟨(max r₁ r₂ + 1)/2, _⟩` (which serves all three radii
     `r₁, r₂, √(r₁ r₂)` since the geometric mean is `≤ max`),
  2. applies Cauchy–Schwarz / Hölder on the `tsum` (Mathlib name:
     `inner_mul_le_norm_mul_norm` for the `ℓ²` shape, or
     `Real.inner_mul_le_norm_mul_norm`, or the elementary
     `Finset.inner_mul_le_norm_mul_norm` paired with
     `Summable.tsum_le_tsum` partial-sum limit),
  3. closes with `mul_pow`, `sqrt_mul_self`, and `ring_nf` for the
     final algebraic massage.

  No new Mathlib API is needed beyond what sprint 010 / sprint 011
  already exercised (sprint 011's
  `cauchyPowerSeries_coeff_norm_radius_invariant` may be re-used to
  align the three radii's coefficient norms to the chosen `R`, exactly
  as in sprint 015's
  `outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`).

- **Falsifiable in one Generator session.** The proof has the same
  shape as sprint 011 / sprint 015's per-radius `tsum` manipulations,
  with one new Mathlib primitive (`inner_mul_le_norm_mul_norm` for
  `lp 2` over `ℕ`, or the equivalent `Real.tsum_mul_le_sqrt_mul_sqrt`
  for the geometric-mean form). The Generator has shipped sprint 010's
  Parseval and sprint 015's half-disc Parseval; this sprint is bounded
  between them in derivation cost. ~200–400 lines of Lean.

- **Why not pursue a direct c-push.** As documented in sprint 015,
  pushing `c` past `0.3554` requires either Möbius / pseudohyperbolic
  disk machinery (huge Mathlib infrastructure absent) or a Hayman-style
  extremal-function argument (also huge). Neither is single-session
  Generator work. This sprint pins the Hardy log-convexity primitive
  that any composable approach must factor through.

- **Why not the half-disc termwise consumer follow-up.** Sprint 015
  shipped both halves of the Parseval expansion plus the termwise
  comparison consumers. Those consumers compare `f` vs `g` *given
  coefficient-norm dominance*, but the contract gives outer-annulus
  *pointwise* dominance — which (as sprint 015's "next step" note
  documents) is not equivalent to coefficient-norm dominance. Pinning
  log-convexity is the next non-trivial analytic primitive on the
  *single-function* side; the cross-function bridge from pointwise
  dominance to coefficient dominance is structurally larger and is
  deferred.

- **Why not pursue the proposal_001 trust-reduction.**
  `proposal_001_replace_seed_with_inner_radial_dominance.md` is
  `pending` and gates the trust-reduction sprint. Until human approval,
  that direction is blocked. This sprint advances goal #1 (c-push
  scaffolding) instead and is independent of the proposal's status.

- **Why not pursue subharmonicity of `‖f z‖²`.** Subharmonicity
  (`Δ ‖f z‖² ≥ 0`) gives the radial monotonicity `r ↦ circleMeanSq f r`
  is non-decreasing, which sprint 010 already proves
  (`circleMeanSq_radial_mono`) via the Parseval expansion directly,
  bypassing subharmonicity. Hadamard's three-circles is a strictly
  stronger statement (log-convex implies non-decreasing for series with
  nonneg coefficients in `r²`), so this sprint subsumes the radial
  monotonicity in spirit; it is the natural next strengthening.

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"Cauchy–Schwarz on boundary integrals"*, *"Parseval / boundary L²
  expansions on analytic functions"*, *"termwise summability and
  `tsum`-level rearrangements"*. The sprint is precisely Cauchy–Schwarz
  on a Parseval `tsum`. The Generator has shipped sprint 008's
  `circleMeanInner` sesquilinearity (which uses the same
  `setIntegral_congr_fun` plus algebraic-rearrangement pattern) and
  sprint 010 / 011 / 015's `tsum` comparisons. This sprint is bounded
  in derivation cost.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleMeanLogConvex.lean`: **new
  file**, in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.RadialBergman`, `Proof.AnalyticParseval`,
    `Proof.CircleMeanRadial`, `Proof.BergmanParseval` (the same module
    set as `Proof.AnnulusBergmanParseval`, since the proof reuses the
    canonical-witness Parseval and the radius-invariance lemma).

  - exposes the two headline theorems above:
    - `circleMeanSq_geometric_mean_le` — the Cauchy–Schwarz / `a = 1/2`
      special case,
    - `circleMeanSq_log_convex` — the full Hölder / general
      `a ∈ [0, 1]` form.

  - The general form `circleMeanSq_log_convex` may take more lines to
    discharge the two endpoint cases `a = 0` and `a = 1` (which collapse
    by `r^0 = 1, r^1 = r, x^0 = 1, x^1 = x` — handled by `by_cases`
    plus `simp`). The Generator may choose to ship only the
    geometric-mean form `circleMeanSq_geometric_mean_le` if Hölder
    proves materially harder than Cauchy–Schwarz on `tsum`s. (See
    fallback form in *Stop conditions*.)

  - **Implementation sketch for `circleMeanSq_geometric_mean_le`:**
    1. Set `R := ⟨(max r₁ r₂ + 1) / 2, _⟩ : ℝ≥0` and verify
       `0 < R, R < 1, r₁ < R, r₂ < R, √(r₁ r₂) < R` (the last via
       `√(r₁ r₂) ≤ max r₁ r₂` from
       `Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ... )` plus
       `Real.sqrt_sq` if needed).
    2. Apply
       `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
       (sprint 010) at all three radii `r₁`, `r₂`, `√(r₁ r₂)` with the
       same `R`. Each gives
       `circleMeanSq f r = 2π ∑' k, ‖a_k‖² r^(2k)` where
       `a_k := (cauchyPowerSeries f 0 R).coeff k`.
       (No `cauchyPowerSeries_coeff_norm_radius_invariant` adjustment is
       needed because all three identities use the same `R`.)
    3. Substitute `r^(2k) = (r²)^k` for `r ∈ {r₁, r₂}`, and
       `(√(r₁ r₂))^(2k) = (r₁ r₂)^k = r₁^k r₂^k` for the geometric
       mean. The substitutions go through `Real.sq_sqrt
       (mul_nonneg hr₁.le hr₂.le)` plus `pow_mul` and `mul_pow`.
    4. Apply Cauchy–Schwarz on `tsum`: `(∑' k, u_k * v_k)² ≤
       (∑' k, u_k²) * (∑' k, v_k²)` with `u_k := ‖a_k‖ * r₁^k`,
       `v_k := ‖a_k‖ * r₂^k`.
       The Mathlib primitive is
       `inner_mul_le_norm_mul_norm` for `lp 2` (probably the cleanest)
       or — failing that —
       `Real.inner_mul_le_norm_mul_norm` on the counting measure, or
       the elementary route:
       `Finset.inner_mul_le_norm_mul_norm` (the discrete
       Cauchy–Schwarz on a finite sum) paired with the partial-sum-≤-tsum
       limit in three places (one for the LHS, two for the RHS).
       The elementary route is the most likely to work cleanly because
       all three `tsum`s are over `ℕ` with non-negative real-valued
       summands; `lp 2` may require additional `MemLp` hypotheses that
       are awkward to discharge.
    5. Multiply through by the `(2π)²` factor on the LHS and `(2π)(2π)`
       on the RHS; close via `ring`.

  - **Implementation sketch for `circleMeanSq_log_convex`:** same shape,
    with Hölder in step 4 instead of Cauchy–Schwarz. The Mathlib
    primitive is `Real.inner_mul_le_norm_mul_norm` with general
    exponents `p, q` such that `1/p + 1/q = 1`, or the elementary
    discrete form
    `Finset.inner_mul_le_Lp_mul_Lq_of_norm_le` (or similar). The
    Generator should pick whichever has the cleanest API surface; if
    Hölder turns out materially harder, ship only the Cauchy–Schwarz
    form.

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must genuinely reuse sprint 010's
    `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
    not bypass via a re-derivation.

- `ProofRefinement/Korenblum/Candidates/V16.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V16`, marked
  `-- @parent V15`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V15),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V15,
  - imports the same module set as V15 plus
    `ProofRefinement.Korenblum.Proof.CircleMeanLogConvex`, so that the
    new module is part of V16's compile graph and is exercised by the
    build. No structural use of the new theorems in V16 itself is
    required (the consumer is a future c-push sprint).

- No edits to `lemma.toml`. No edits to V0/.../V15 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V16` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V16.lean` succeeds (the
   evaluator accepts V16 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V15; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/CircleMeanLogConvex.lean`
   contains at least the geometric-mean form
   `circleMeanSq_geometric_mean_le` as a `theorem` (or `lemma`) with the
   shape listed above. The proof must genuinely call sprint 010's
   `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` and a
   Mathlib Cauchy–Schwarz / Hölder primitive — not bypass via direct
   re-derivation. Ideally the file also contains the general Hölder form
   `circleMeanSq_log_convex`; see *Stop conditions* for the fallback.

4. The new module `Proof.CircleMeanLogConvex` must be **used**, even
   trivially, somewhere in V16's transitive compile graph (importing it
   from V16 is sufficient — it forces the module to compile as part of
   V16's build).

5. The headline theorem statement must be **internally consistent** with
   sprint 010's radial monotonicity `circleMeanSq_radial_mono`: setting
   `r₁ = r, r₂ = r' ≥ r ` in `circleMeanSq_geometric_mean_le` gives
   `circleMeanSq f (√(r·r'))² ≤ circleMeanSq f r · circleMeanSq f r'`,
   which combined with the radial monotonicity at the geometric mean
   recovers a (slightly weaker) form of monotonicity. The sprint does
   *not* need to ship this consistency check as a theorem, but the
   theorem statement must be such that this consistency holds.

## Out of scope

- Edit older candidates (`V0.lean` through `V15.lean`) or the existing
  `Proof/*.lean` files.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms, no `hWang_inner_radial_dominance_3554`). If the
  proof is genuinely blocked on a missing Mathlib API, the Generator
  must `STATUS=BLOCKED` with the precise obstruction, **not**
  axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the Hadamard three-circles primitive that
  composes with future cross-function arguments.

- Edit `lemma.toml` (no policy expansion in this sprint; the
  proposal_001 trust-reduction edit is a separate sprint, gated on
  human approval).

- Pursue Hardy's convexity for general `M_p` with `p ≠ 2`. Only `p = 2`
  is in scope (Parseval is exact in this case).

- Attempt the cross-function comparison from outer-annulus pointwise
  dominance to inner-disk Bergman dominance. That is the genuine
  Korenblum content and is structurally large (Möbius / pseudohyperbolic
  / Hayman extremal-function machinery). Out of scope here.

- Generalize to `circleMeanSq f r` for `r ≥ 1` or `r ≤ 0` (the
  unit-disk hypothesis is essential; outside `(0, 1)` the canonical
  Parseval witness does not apply).

## Time budget

≤ 90 minutes runtime. (This is comparable to sprint 011's whole-disc
Parseval and sprint 015's half-disc Parseval — both shipped in single
bounded sessions. The new analytic content is the discrete
Cauchy–Schwarz / Hölder application on a `tsum`, with the rest of the
proof structure mirroring sprint 010 / sprint 011's Parseval `tsum`
manipulations.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. the Mathlib `tsum`-level Cauchy–Schwarz
  primitive is not callable in the expected shape, or the
  partial-sum-≤-tsum limit step requires more summability bookkeeping
  than the time budget admits): `STATUS=BLOCKED` with a precise note
  in `Experience.md` recording which Mathlib lemma was the obstruction
  and which approaches were tried (`inner_mul_le_norm_mul_norm` for
  `lp 2` over `ℕ` vs `Real.inner_mul_le_norm_mul_norm` on the counting
  measure vs the elementary
  `Finset.inner_mul_le_norm_mul_norm` + partial-sum-tsum limit).

  **Fallback form A** (if the general Hölder form
  `circleMeanSq_log_convex` is materially harder than the
  Cauchy–Schwarz form): the Generator may instead ship only the
  geometric-mean special case `circleMeanSq_geometric_mean_le` (the
  `a = 1/2` case of Hölder, equivalent to discrete Cauchy–Schwarz on
  the Parseval `tsum`). The general form is then deferred to a
  follow-up sprint. The fallback is acceptable if and only if the
  Generator records in `Experience.md` why the general form was
  deferred, and the geometric-mean form is genuinely Lean-pinned (no
  `sorry`, no `axiom`).

  **Fallback form B** (if even the geometric-mean form is materially
  blocked on the `tsum`-level Cauchy–Schwarz step): the Generator may
  instead ship the **finite-sum form**

  ```lean
  theorem circleMeanSq_geometric_mean_partial_le
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁' : r₁ < 1)
                   (hr₂ : 0 < r₂) (hr₂' : r₂ < 1) (N : ℕ) :
      (∑ k ∈ Finset.range N, ‖a_k‖² · (r₁ * r₂)^k)^2
        ≤ (∑ k ∈ Finset.range N, ‖a_k‖² · r₁^(2k))
          · (∑ k ∈ Finset.range N, ‖a_k‖² · r₂^(2k))
  ```

  i.e., the Cauchy–Schwarz inequality at the level of partial sums of
  the Parseval expansion, before passing to the `tsum` limit. This is
  pure `Finset.inner_mul_le_norm_mul_norm` (which exists in Mathlib
  and is well-tested). The `tsum`-level passage to the limit is then
  deferred to a follow-up sprint. The fallback is acceptable if and
  only if the Generator records in `Experience.md` why the
  `tsum`-level form was deferred.

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
