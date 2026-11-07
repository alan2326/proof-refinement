# Sprint 018: Bergman A² sub-mean-value inequality (area Cauchy-style pointwise bound)

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V17.lean`
**Target file**: `Candidates/V18.lean`
**Direction**: section2-proof / scaffolding-for-c-push (the **missing
analytic primitive** that bridges *outer-region integral domination* to
*inner-region pointwise* / circle-mean information. This is the standard
area-Cauchy / sub-mean-value inequality for `‖f‖²`, derived directly
against sprint 011's whole-disk Bergman A² Parseval identity, and is the
single most important missing primitive for any future c-push: it is the
mechanism by which `∫_{outerAnnulus} ‖f‖² ≤ ∫_{outerAnnulus} ‖g‖²`
information can be transported to a pointwise upper bound on `‖f(z₀)‖²`
for `z₀` near the outer annulus, and from there — paired with sprint
017's Cauchy L² estimate and sprint 016's three-circles — into inner
circle-mean and inner Bergman comparisons.)

## Goal

Ship one new derived module `Proof/SubMeanValue.lean` that pins two
public theorems in Lean:

```lean
-- (1) Sub-mean-value inequality at the origin.
-- For f analytic and A²-integrable on UnitDisk, the squared modulus of
-- f at the origin is bounded by π⁻¹ times the Bergman A² norm:
--   π · ‖f(0)‖² ≤ bergmanNormSq f.
-- Equivalently, this is the area-Cauchy point-evaluation bound at 0.
theorem normSq_zero_le_bergmanNormSq_div_pi
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    Real.pi * ‖f 0‖ ^ 2 ≤ bergmanNormSq f
```

```lean
-- (2) Sub-mean-value inequality at an arbitrary interior point.
-- For f analytic on UnitDisk and B(z₀, R) ⊆ UnitDisk (i.e. R ≤ 1 - ‖z₀‖),
-- the squared modulus of f at z₀ is bounded by (πR²)⁻¹ times the area
-- integral of ‖f‖² over the ball B(z₀, R):
--   π · R² · ‖f(z₀)‖²
--     ≤ ∫ z in Metric.ball z₀ R, ‖f z‖² dA(z).
theorem normSq_pointwise_le_ball_integral
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {z₀ : ℂ} (hz₀ : z₀ ∈ UnitDisk) {R : ℝ} (hR_pos : 0 < R)
    (hR_le : R + ‖z₀‖ < 1)
    (hf_polar_translate : <integrability of the translated polar pullback>) :
    Real.pi * R ^ 2 * ‖f z₀‖ ^ 2 ≤
      ∫ z in Metric.ball z₀ R, ‖f z‖ ^ 2 ∂(volume : Measure ℂ)
```

The exact integrability hypothesis on (2) — whether it is the original
`hf_polar` (translated by `z ↦ z + z₀` and re-rationalized to the polar
rectangle around `z₀`), or whether it is freshly stated in terms of the
ball `Metric.ball z₀ R`, or whether it is derived from `AnalyticOn ℂ f
UnitDisk` plus continuity-on-compact-subset — is left to the Generator.
The natural form is "f is integrable in `‖·‖²` over the closed ball
`closedBall z₀ R ⊆ UnitDisk`", which follows from continuity (via
analyticity) on the compact closed ball. **Fallback A** below describes
a strictly weaker (but still useful) version of (2) that ducks the
translation-integrability bookkeeping entirely by specializing to balls
centered at the origin.

## Proof outline

**Theorem (1) `normSq_zero_le_bergmanNormSq_div_pi` proof:**

1. By sprint 011's `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
   at any chosen `R ∈ (0, 1)` (e.g. `R := 1/2 : ℝ≥0`):
   `bergmanNormSq f = ∑' k, (π/(k+1)) · ‖a_k‖²` with `a_k :=
   (cauchyPowerSeries f 0 R).coeff k`.
2. The `k = 0` summand is `π · ‖a_0‖² = π · ‖f(0)‖²` (since
   `a_0 = f(0)` for any Cauchy power series at `0`; this is
   `cauchyPowerSeries_apply_zero` or follows from
   `(cauchyPowerSeries f 0 R).coeff 0 = f 0` via
   `HasFPowerSeriesAt.coeff_zero` / `FormalMultilinearSeries.apply_zero`).
3. All summands are non-negative.
4. By `Summable.le_tsum` (the same Mathlib primitive sprint 017
   exercised), the `k = 0` summand is `≤` the tsum:
   `π · ‖f(0)‖² ≤ ∑' k, (π/(k+1)) · ‖a_k‖² = bergmanNormSq f`.

The summability of `fun k => (π/(k+1)) · ‖a_k‖²` is part of sprint
011's identity (the tsum exists, and `Summable` is extracted via
`summable_canonical_parseval_terms` private helper or re-derived inline
via the `FormalMultilinearSeries.summable_norm_mul_pow` route from
sprints 011/015/016/017).

**Theorem (2) `normSq_pointwise_le_ball_integral` proof:**

1. Define the translated function `f_z₀ : ℂ → ℂ := fun w => f (w + z₀)`.
   `f_z₀` is analytic on `Metric.ball 0 R` (which equals the
   pre-image of `Metric.ball z₀ R` under `w ↦ w + z₀`, and is contained
   in `UnitDisk` by `hR_le`).
2. By a rescaling and translation of theorem (1) — applied to `f_z₀`
   on the ball `Metric.ball 0 R` instead of `UnitDisk` — we get
   `π · R² · ‖f_z₀(0)‖² ≤ ∫ w in Metric.ball 0 R, ‖f_z₀ w‖² dA(w)`.
3. `f_z₀(0) = f(z₀)`, so the LHS is `π · R² · ‖f(z₀)‖²`.
4. Translation-invariance of the area integral (Mathlib:
   `MeasureTheory.integral_add_right_eq_self` or
   `Measure.map_add_right`) converts
   `∫ w in Metric.ball 0 R, ‖f_z₀ w‖² dA(w) = ∫ z in Metric.ball z₀ R, ‖f z‖² dA(z)`.

The rescaling step (R from `1` to general `R < 1`) requires a small
extension of theorem (1)'s "unit-disk" version to general radius.
**Two routes are available:**

  - **Route 2A (rescaling).** Rescale by `R`: define `f_R w := f(R · w)`,
    apply theorem (1) to `f_R` on `UnitDisk` (since `f_R` is analytic
    on `Metric.ball 0 (1/R)` ⊇ `UnitDisk`), and rescale the resulting
    Bergman integral via change-of-variables `z = R · w`. The Jacobian is
    `R²`. This route reuses theorem (1) verbatim and threads the
    `R²`-Jacobian through the integral.

  - **Route 2B (direct generalization).** Generalize theorem (1) to
    arbitrary radius `R < 1` first as an intermediate lemma, then apply
    via translation. This is essentially the same content as 2A but
    structured as a generalization. The cost is that the per-radius
    Bergman Parseval is needed at radius `R`, not just `1`.

The Generator picks whichever is shorter; **Route 2A is recommended**
since it composes existing infrastructure (theorem (1) at `UnitDisk`
plus a `R²`-Jacobian change-of-variables).

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move builds a self-contained
per-candidate partial formalization on top of Mathlib (the area Cauchy /
sub-mean-value inequality for `‖f‖²` analytic), derived directly from
sprint 011's whole-disk Bergman Parseval identity. The only fixed
target is the final theorem shape.

## Why

- **It is the smallest sprint that exposes outer→pointwise transport.**
  All existing scaffolding in the workspace goes from coefficient norms
  to circle-means (sprint 010), from circle-means to Bergman (sprint 003,
  011, 015), or from outer pointwise dominance to outer circle-mean
  dominance (sprint 017). The sub-mean-value inequality is the **first
  primitive that gives a pointwise upper bound on `‖f(z₀)‖²` from an
  integrated bound on `‖f‖²` over a ball**. Paired with the workspace's
  outer Bergman comparison machinery, it is the natural mechanism by
  which outer-region integral information (where `‖f‖² ≤ ‖g‖²`
  pointwise) transfers to pointwise upper bounds on `‖f‖²` near the
  outer-annulus boundary — and from there into inner circle-means via
  sprint 010's monotonicity or sprint 016's three-circles.

- **It is genuinely useful for c-push.** Wang's published proof of
  Korenblum at `c = 0.3554` (and Hayman's earlier extremal-function
  arguments at smaller `c`) factor through some form of area Cauchy /
  sub-mean-value bound: pointwise control on `‖f‖²` from integrated
  control on `‖f‖²` over a small disk that lies in the outer annulus.
  Without this primitive in Lean, the c-push *cannot* attack
  outer→inner transfer at all; with this primitive, the chain becomes:
  - sub-mean-value bound on a small disk centered at `z₀ ∈ outerAnnulus`
    plus outer pointwise dominance ⇒ `‖f(z₀)‖² ≤ (πR²)⁻¹ ∫_{B(z₀,R)} ‖g‖²`
  - integrate `z₀` over a thin ring near the outer-annulus inner
    boundary (via Fubini) ⇒ a `circleMeanSq` upper bound on `f` at
    radii close to `c` from the outside.
  - apply sprint 016's three-circles or sprint 010's radial monotonicity
    to extend the bound inward to inner radii.
  Any one of these chains needs sub-mean-value as the **first** step;
  this sprint pins it.

- **The proof is bounded.** Theorem (1) is a one-line `Summable.le_tsum`
  on sprint 011's existing Parseval identity, plus the `a_0 = f(0)`
  identification. The summability comes from sprint 011's existing
  infrastructure (or a re-derivation via sprint 017's pattern). Theorem
  (2) is theorem (1) plus translation-invariance of Lebesgue measure on
  ℂ (Mathlib: `MeasureTheory.integral_add_right_eq_self`) plus an
  `R²`-Jacobian rescaling. Each is ~50–100 lines. Total ~150–250 lines.

- **Falsifiable in one Generator session.** Each theorem has a clean,
  well-documented Mathlib API shape:
  - (1) is `Summable.le_tsum` on the sprint 011 identity. The
    `a_0 = f(0)` identification is one of: `cauchyPowerSeries_apply_zero`,
    `FormalMultilinearSeries.apply_zero`, or `(cauchyPowerSeries f 0 R).coeff 0
    = f 0` derived from `HasFPowerSeriesAt.eq_zero` / power-series
    constant-term identity.
  - (2) is (1) plus translation/scaling. Translation-invariance of
    Lebesgue area measure is `Measure.map_add_right_eq_self` (or
    `MeasureTheory.integral_add_right_eq_self` directly on the integral
    side). Rescaling is via `Complex.integral_comp_mul_left` or
    `MeasureTheory.Measure.map_smul`.
  No new Mathlib API is needed beyond what sprints 011, 012, and 017
  have already exercised.

- **Why not pursue continuity of `circleMeanSq f r` directly.** Sprint
  017 explicitly defers the `r → c⁺` boundary form of theorem (3) (the
  cross-function bound) on the grounds that it requires continuity of
  `r ↦ circleMeanSq g r` at `r = c`. That continuity *is* a clean
  Lean-derivation primitive (it follows from sprint 010's canonical
  Parseval plus `tsum`-continuity). But continuity alone does NOT
  unlock the c-push: it just sharpens an existing bound by passing
  to a closed limit. Sub-mean-value, by contrast, opens a new
  outer→inner transport mechanism. If the planner had to choose, sub-
  mean-value is strictly higher analytic novelty per session.

- **Why not pursue Möbius / pseudohyperbolic disk machinery.** The
  Möbius automorphism `φ_a(z) = (z-a)/(1-conj(a)·z)` and Bergman A²
  conformal-invariance are the heaviest analytic toolkit Hayman /
  Korenblum / Wang use, and would unlock the cleanest c-push path —
  but that's a structurally large derivation (multi-sprint). Sub-mean-
  value is the *next* primitive, strictly inside the area-Cauchy
  toolkit, that the workspace's existing Parseval infrastructure
  supports in one session.

- **Why not pursue subharmonicity of `‖f‖²` via `MeanValue` lemmas in
  Mathlib.** Mathlib has `Subharmonic.mean_value` and related, but
  they're stated for general subharmonic functions on Lebesgue
  measure, with their own integrability bookkeeping. The translation-
  via-Parseval route (this sprint) is shorter and tighter for the
  specific case of `‖f‖²` analytic — it factors through identities
  the workspace already pins, rather than depending on a Mathlib
  hierarchy that may require additional API plumbing.

- **Why not pursue full `‖f(z₀)‖² ≤ (πR²)⁻¹ ∫_{B(z₀,R)} ‖f‖²` and a
  c-push to `c' > 0.3554` in the same sprint.** The c-push attempt
  itself (combining sub-mean-value with outer dominance, integrating
  `z₀` over a thin ring, applying three-circles) is structurally
  larger and requires careful interval / Fubini bookkeeping at the
  c-boundary. Pinning sub-mean-value first as a public lemma allows
  the next sprint to attack the c-push without re-deriving the
  sub-mean-value bound inline. This is the single-session bound.

- **Why not pursue proposal_001 trust-reduction.**
  `proposal_001_replace_seed_with_inner_radial_dominance.md` is `pending`
  and gates the trust-reduction sprint. Until human approval, that
  direction is blocked. This sprint advances goal #1 (c-push
  scaffolding) instead and is independent of the proposal's status.

- **Generator's declared scope covers this.** AGENT_BRIEF lists
  *"Parseval / boundary L² expansions on analytic functions"*, *"termwise
  summability and `tsum`-level rearrangements"*, *"bridging pointwise
  modulus inequalities to boundary integrals"*, *"subharmonicity /
  mean-value arguments for `|f|²`"*. Theorem (1) is precisely a
  `tsum`-level extraction of the `k=0` summand (the same
  `Summable.le_tsum` pattern as sprint 017). Theorem (2) is precisely
  a translation/scaling of theorem (1) — squarely in the
  *"subharmonicity / mean-value arguments for `|f|²`"* declared scope.
  The generator has shipped sprints 011, 015, 016, 017 on the same
  `tsum` machinery; this sprint composes them with a translation
  argument.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/SubMeanValue.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.RadialBergman`, `Proof.AnalyticParseval`,
    `Proof.CircleMeanRadial`, `Proof.BergmanParseval`,
    `Proof.PolarIntegrability`, `Proof.CircleExpBridge` (the same
    module set as `Proof.CauchyL2Estimate` plus `Proof.BergmanParseval`,
    since theorem (1)'s proof routes through the whole-disk Parseval).

  - exposes the two headline theorems above:
    - `normSq_zero_le_bergmanNormSq_div_pi` (origin form),
    - `normSq_pointwise_le_ball_integral` (general interior point).

  - **Implementation sketch for (1)
    `normSq_zero_le_bergmanNormSq_div_pi`:**
    1. Pick `R := (1/2 : ℝ≥0)` (any `R ∈ (0, 1)` will do).
    2. Apply `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
       hf hR_pos hR_lt hf_polar` to get
       `bergmanNormSq f = ∑' k, (π/(k+1)) · ‖a_k‖²`.
    3. Identify `(cauchyPowerSeries f 0 R).coeff 0 = f 0`. The Mathlib
       lemma is one of:
       - `cauchyPowerSeries_apply_zero` (gives the `apply 0 = f 0` form
         on the multilinear map),
       - `(cauchyPowerSeries f 0 R).coeff_zero` — note **caution**:
         `FormalMultilinearSeries.coeff` may not directly equal `apply 0`.
         The standard identity is
         `(cauchyPowerSeries f 0 R).coeff 0 =
           (cauchyPowerSeries f 0 R) 0 fun _ => 1` or similar; double-
         check the precise name. The cleanest spelling may be a custom
         derivation: `coeff k := p k (fun _ => 1)`, and at `k = 0` this
         is `p 0 ![]` which equals `f 0` by the definition of
         `cauchyPowerSeries f 0 R 0` as a constant function evaluated at
         `0`. The Generator should use whatever Mathlib name is fastest.
       - Alternative: route through `HasFPowerSeriesOnBall.eq_zero` /
         `HasFPowerSeriesAt.coeff_zero` (the analytic-`f`-at-`0` version
         gives `coeff 0 = f 0` directly).
    4. Per-summand non-negativity (each term is `(π/(k+1)) · ‖a_k‖² ≥ 0`).
    5. Summability of `fun k => (π/(k+1)) · ‖a_k‖²`: re-extract via the
       same private-helper pattern from sprint 011 / 017
       (`summable_canonical_parseval_terms`, `summable_coeff_sq_pow`),
       i.e., `FormalMultilinearSeries.summable_norm_mul_pow` plus
       `Summable.of_norm_bounded_eventually_nat`. Or alternatively, the
       summability is implicit in sprint 011's identity (the tsum
       exists), so for the `Summable.le_tsum` step the Generator can
       use `tsum_le_of_sum_range_le` against the partial-sum form.
       Actually, since `bergmanNormSq f` is a finite real number (from
       `hf_polar`), summability of the non-negative tsum follows from
       `summable_iff_not_tendsto_nat_atTop_of_nonneg` or just
       `Summable.of_nonneg_of_le` against the tsum bound.
    6. By `Summable.le_tsum` extract the `k = 0` summand:
       `(π/(0+1)) · ‖a_0‖² = π · ‖f(0)‖² ≤ ∑' k, (π/(k+1)) · ‖a_k‖² =
       bergmanNormSq f`.
    7. Rearrange to match the goal `Real.pi * ‖f 0‖^2 ≤ bergmanNormSq f`.

  - **Implementation sketch for (2)
    `normSq_pointwise_le_ball_integral`:**

    The sprint contract leaves the precise integrability hypothesis
    open; the natural choice is "f is integrable in `‖·‖²` on
    `closedBall z₀ R`", which follows from continuity of
    `‖f‖²` on `closedBall z₀ R ⊆ UnitDisk` (from analyticity of `f` on
    the open disk and `closedBall z₀ R ⊆ UnitDisk`) plus compactness.

    Then the proof:
    1. Define `g w := f (R • w + z₀)` for `w ∈ UnitDisk`. Alternative
       formulation: `g w := f (R · w + z₀)` interpreting `R · w` via
       `(R : ℂ) * w` (with `R : ℝ` coerced to `ℂ`).
    2. `g` is analytic on `UnitDisk` (composition of analytic `f` with
       affine `w ↦ R · w + z₀`, with image `Metric.ball z₀ R ⊆
       UnitDisk` by `hR_le : R + ‖z₀‖ < 1`).
    3. `g(0) = f(z₀)`.
    4. The polar integrability hypothesis for `g` is needed (i.e., the
       polar pullback of `g` on `Ioo 0 1 × Ioo (-π) π`). This is one
       of:
       - **Recommended:** Derive it from `AnalyticOn ℂ g UnitDisk` via
         `polar_integrableOn_of_analyticOn_of_bergmanIntegrable`
         (sprint 012). For this, we need `Integrable (‖g‖²) (volume.restrict
         UnitDisk)`. Continuity-on-compact is the cleanest route:
         `g` is continuous on `closedBall 0 1 ⊇ UnitDisk` (since
         analyticity extends to a neighborhood of the closed ball
         under `R + ‖z₀‖ < 1`). Continuity on a compact set gives
         integrability on `UnitDisk` (a bounded open subset of the
         compact closed ball).
       - Alternative: take it as a hypothesis. Cleaner and avoids the
         continuity-on-compact bookkeeping.
    5. Apply theorem (1) to `g`:
       `π · ‖g(0)‖² ≤ bergmanNormSq g`.
    6. Substitute `g(0) = f(z₀)`:
       `π · ‖f(z₀)‖² ≤ bergmanNormSq g = ∫ w in UnitDisk, ‖g w‖² dA(w)
       = ∫ w in UnitDisk, ‖f(R · w + z₀)‖² dA(w)`.
    7. Change of variables `z = R · w + z₀` (linear, with Jacobian
       `R²`): the integral becomes
       `R⁻² · ∫ z in Metric.ball z₀ R, ‖f z‖² dA(z)`.
       (Mathlib: `MeasureTheory.Measure.map_add_right` for the
       translation, `MeasureTheory.Measure.map_smul` /
       `Complex.integral_comp_mul_left` for the scaling.)
    8. Multiply through by `R²`:
       `π · R² · ‖f(z₀)‖² ≤ ∫ z in Metric.ball z₀ R, ‖f z‖² dA(z)`.

    The change-of-variables step (7) is the trickiest. Mathlib's
    `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
    (or `integral_comp_smul_left` for the homothety case) is the
    relevant primitive; the Generator may also exploit
    `Complex.integral_comp_polarCoord_symm`-style affine-invariance
    via the polar-pullback factorisation (less clean, but composes
    with the existing workspace).

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must genuinely call sprint 011's
    `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
    not bypass via re-derivation of Bergman Parseval.

- `ProofRefinement/Korenblum/Candidates/V18.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V18`, marked
  `-- @parent V17`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V17),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V17,
  - imports the same module set as V17 plus
    `ProofRefinement.Korenblum.Proof.SubMeanValue`, so that the new
    module is part of V18's compile graph and is exercised by the
    build. No structural use of the new theorems in V18 itself is
    required (the consumer is a future c-push sprint).

- No edits to `lemma.toml`. No edits to V0/.../V17 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V18` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V18.lean` succeeds (the
   evaluator accepts V18 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V17; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/SubMeanValue.lean`
   contains **at least theorem (1)** as a `theorem` (not `lemma`,
   not `axiom`, no `sorry`):
   - `normSq_zero_le_bergmanNormSq_div_pi`.
   The proof must genuinely call sprint 011's
   `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
   for the Bergman → tsum reduction and a Mathlib `Summable.le_tsum`
   primitive for the single-summand extraction — not bypass via direct
   re-derivation.

4. The file ideally also contains theorem (2)
   `normSq_pointwise_le_ball_integral`. **Fallback A** below specifies
   what to ship if the change-of-variables step in theorem (2) hits a
   Mathlib-API friction.

5. The new module `Proof.SubMeanValue` must be **used**, even
   trivially, somewhere in V18's transitive compile graph (importing
   it from V18 is sufficient — it forces the module to compile as
   part of V18's build).

6. The headline theorem statements must be **internally consistent**
   with the sprint 011 / 015 / 017 stack. In particular:
   - Theorem (1) at `f := constant function c` gives `π · ‖c‖² ≤
     bergmanNormSq (const c) = ∫_𝔻 ‖c‖² dA = π · ‖c‖²` — equality at
     constants, as expected.
   - Theorem (1) at `f := z` gives `π · ‖0‖² = 0 ≤ bergmanNormSq z =
     π/2` — strict inequality, as expected.
   The sprint does *not* need to ship these consistency checks as
   theorems, but the headline shape must be such that they hold.

## Out of scope

- Edit older candidates (`V0.lean` through `V17.lean`) or the existing
  `Proof/*.lean` files. In particular, do **not** lift any
  helper from `Proof/BergmanParseval.lean`'s private helpers (e.g.,
  `summable_canonical_parseval_terms`) — re-derive inline if needed.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`,
  no new analytic axioms). If the proof is genuinely blocked on a
  missing Mathlib API, the Generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the area Cauchy / sub-mean-value
  primitive that future c-push consumers will factor through.

- Edit `lemma.toml` (no policy expansion; the proposal_001 trust-
  reduction edit is gated on human approval).

- **Pursue the c-push attempt directly via sub-mean-value + outer
  pointwise dominance + integration.** That is the structurally larger
  follow-up sprint that consumes this primitive. Attempting both in
  one session would blow the time budget.

- **Generalize theorem (2) to balls that are NOT contained in
  `UnitDisk`.** The hypothesis `R + ‖z₀‖ < 1` (equivalently
  `closedBall z₀ R ⊆ UnitDisk`) is essential for the analyticity of `g`
  on `UnitDisk` in the rescaled problem.

- **Pursue the closed-ball form `R + ‖z₀‖ ≤ 1`** (instead of strict
  `<`). The strict form is sufficient for all downstream consumers,
  and the closed form requires additional limit-passing.

- **Ship the area Cauchy integral formula `f(z₀) = (πR²)⁻¹ ∫_{B(z₀,R)}
  f dA`** (the equality at the level of `f` itself, not `‖f‖²`). That
  is a distinct and stronger primitive (requires complex-valued area
  integrals and the Cauchy integral formula) and is not needed for
  the c-push direction.

## Time budget

≤ 90 minutes runtime. (Theorem (1) is comparable in shape to sprint
017's theorem (1) — a `Summable.le_tsum` extraction on an existing
Parseval identity — except routing through sprint 011's whole-disk
Bergman Parseval rather than sprint 010's circle-mean Parseval. The
`a_0 = f(0)` identification is one Mathlib-name lookup. Theorem (2) is
~50–100 lines of translation-and-scaling bookkeeping on top of (1).
Total ~150–250 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. the `(cauchyPowerSeries f 0 R).coeff 0 =
  f 0` Mathlib identification has an unexpected shape, or the change-
  of-variables step in theorem (2) requires more bookkeeping than
  the time budget admits): `STATUS=BLOCKED` with a precise note in
  `Experience.md` recording which Mathlib lemma was the obstruction
  and which approaches were tried.

  **Fallback A** (theorem (2) is too ambitious in one session):
  the Generator may instead ship only theorem (1)
  `normSq_zero_le_bergmanNormSq_div_pi`, deferring (2) to a follow-up
  sprint. The fallback is acceptable if and only if the Generator
  records in `Experience.md` why (2) was deferred (e.g. which
  Mathlib change-of-variables primitive was the obstruction and
  which alternative routes — `MeasureTheory.Measure.map_add_right`,
  `Complex.integral_comp_mul_left`,
  `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`,
  affine-invariance via polar-pullback factorisation — were tried).

  **Fallback B** (theorem (1) is materially blocked on the
  `(cauchyPowerSeries f 0 R).coeff 0 = f 0` identification):
  the Generator may instead ship the **partial-sum form**

  ```lean
  -- For all N : ℕ, the partial sum of the first N terms of the Bergman
  -- Parseval expansion is ≤ bergmanNormSq f. Specializing to N = 1
  -- gives π · ‖a_0‖² ≤ bergmanNormSq f, but the a_0 = f(0)
  -- identification is deferred.
  theorem partial_sum_bergmanParseval_le_bergmanNormSq
      {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
      {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
      (hf_polar : <as in sprint 011>)
      (N : ℕ) :
      (∑ k ∈ Finset.range N,
          (Real.pi / ((k : ℝ) + 1))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2)
        ≤ bergmanNormSq f
  ```

  This is a strictly weaker statement that does NOT require the
  `a_0 = f(0)` identification; it pins only the partial-sum
  bound on the Parseval expansion. The fallback is acceptable if and
  only if the Generator records in `Experience.md` why the `tsum`-level
  / `‖f(0)‖²`-form was deferred.

  **Fallback C** (theorem (1) is materially blocked on the
  `Summable.le_tsum` step itself, e.g. on summability):
  the Generator may instead ship a **finite-sum / partial-sum form**
  identical to fallback B. (The two fallbacks coincide; in practice
  it's hard to distinguish which sub-step is the obstruction. Either
  recording is acceptable.)

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change, or a Mathlib
  primitive that requires a workspace-import-policy edit):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
