# Sprint 011: Bergman A² Parseval identity for analytic functions

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V10.lean`
**Target file**: `Candidates/V11.lean`
**Direction**: section2-proof (Bergman scaffolding — radial integration of sprint 010's
canonical-witness pointwise-in-`r` Parseval identity into a coefficient-level
identity for `bergmanNormSq`, the explicitly-named follow-up of sprint 010)

## Goal

Lift sprint 010's canonical-witness pointwise-in-`r` Parseval identity

```
circleMeanSq f r
  = ∑' k, (2 * Real.pi * r ^ (2 * k))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
```

(for any chosen NNReal radius `R ∈ (0,1)`, valid on `r ∈ [0, R)`) to the
**Bergman A² level** by radial integration:

```
bergmanNormSq f
  = ∑' k, (Real.pi / (k + 1))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
```

for any `f : ℂ → ℂ` analytic on `UnitDisk` (and with the integrability
hypothesis on the polar pull-back required to invoke
`bergmanNormSq_radial_polar`), valid for any chosen NNReal radius `R` with
`0 < (R : ℝ) < 1`.

In a new file `Proof/BergmanParseval.lean`, expose:

1. `cauchyPowerSeries_coeff_norm_radius_invariant` — *the radius-independence
   of coefficient norms*. For `f : ℂ → ℂ` analytic on `UnitDisk` and any two
   NNReal radii `R₁, R₂` with `0 < (R_i : ℝ) < 1`,

   ```lean
   ∀ k : ℕ,
     ‖(cauchyPowerSeries f 0 R₁).coeff k‖
       = ‖(cauchyPowerSeries f 0 R₂).coeff k‖
   ```

   This is the bookkeeping that lets us compose sprint 010's identity at a
   fixed `R < 1` (which only covers `r < R`) with the radial integral on
   `(0, 1)` (which needs identity for *all* `r < 1`).

   *Implementation sketch.* The Cauchy-integral formula gives
   `(cauchyPowerSeries f 0 R).coeff k = (1 / k!) · iteratedFDeriv ℂ k f 0`
   when `f` is analytic on the closed ball of radius `R`, via Mathlib's
   `HasFPowerSeriesOnBall.coeff_eq_iteratedFDeriv` (or
   `cauchyPowerSeries_eq_iteratedFDeriv_div_factorial`, whichever Mathlib
   exposes). Both sides depend only on the iteratedFDeriv at `0`, hence
   are radius-independent. The *norm* equality is then trivial. If the
   underlying coefficient equality is brittle to derive, the lemma may
   weaken to `‖·‖ = ‖·‖` (the *norm* equality is what every downstream
   consumer needs and is strictly weaker). The generator picks whichever
   form compiles cleanly.

2. `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` — *the
   headline Bergman Parseval identity*. For `f : ℂ → ℂ` analytic on
   `UnitDisk`, any NNReal `R` with `0 < (R : ℝ) < 1`, and the polar
   integrability hypothesis required by `bergmanNormSq_radial_polar`,

   ```lean
   bergmanNormSq f
     = ∑' k : ℕ, (Real.pi / (k + 1))
                 * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
   ```

   The proof composes:
   - `bergmanNormSq_radial_polar` (sprint 003) to fold `bergmanNormSq f`
     into the radial integral `∫ r ∈ Ioo 0 1, circleMeanSq f r * r`,
   - sprint 010's canonical-witness identity at radius `r` (with witness
     `cauchyPowerSeries f 0 R'` for `R' := (r+1)/2 < 1`),
   - lemma (1) to identify `‖(cauchyPowerSeries f 0 R').coeff k‖` with
     `‖(cauchyPowerSeries f 0 R).coeff k‖`,
   - a `tsum`-vs-`∫` swap on `Ioo 0 1` against the nonneg integrand
     (Tonelli's theorem on nonneg measurable functions, or
     `MeasureTheory.integral_tsum` / `MeasureTheory.tsum_integral_eq_integral_tsum`
     when each summand is integrable),
   - the per-term integral `∫ r ∈ (0, 1), 2π · r^(2k+1) dr = π / (k+1)`
     via `intervalIntegral.integral_pow` (or `MeasureTheory.integral_pow`
     adapted to the `Ioo` shape) plus arithmetic.

3. `bergmanNormSq_termwise_mono` — *the Bergman-level coefficient consumer*.
   For two analytic functions `f, g : ℂ → ℂ` on `UnitDisk` with appropriate
   integrability hypotheses, if their Cauchy-power-series coefficient norms
   are pointwise dominated,

   ```lean
   ∀ k : ℕ,
     ‖(cauchyPowerSeries f 0 R).coeff k‖
       ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖,
   ```

   then `bergmanNormSq f ≤ bergmanNormSq g`.

   This is `tsum_le_tsum` of the per-term inequality
   `(π / (k+1)) ‖a_k‖² ≤ (π / (k+1)) ‖b_k‖²`, with summability of both
   sides supplied by (2) (each side is a real number, hence the implicit
   `Summable`).

V11 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V10
and the only seed axiom is still `hKorenblum_published_3554`. The
contribution is the new derived module that finally pins, in Lean, the
**Bergman-A² level** Parseval identity: `bergmanNormSq f` is a coefficient-
level `tsum` against the canonical Cauchy power series, with weight
`π / (k+1)`. With this identity in place, every future c-push consumer
can compare `bergmanNormSq` at the coefficient level — the same way
`circleMeanSq_termwise_mono` (sprint 010) compares the circle-mean.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound c_value`
directly against Mathlib (function-level Bergman A² Korenblum max principle),
or build a self-contained per-candidate partial formalization on top of
Mathlib. The only fixed target is the final theorem shape.

## Why

- **It is the explicitly named follow-up of sprint 010.** Sprint 010's
  *Out of scope* paragraph says: *"Prove the **full Bergman Parseval
  identity** `bergmanNormSq f = ∑' k, π / (k + 1) * ‖a k‖²` (a single
  radial integration `∫_0^1 r · circleMeanSq f r dr` against the radial
  measure). Useful as the next sprint after this one, but not required by
  the three items above."* Sprint 011 is exactly that next sprint.

- **It is the canonical Bergman-side coefficient identity.** Every honest
  Korenblum-style argument that compares `bergmanNormSq f` to `bergmanNormSq g`
  passes through *some* coefficient-level Bergman identity. Wang's paper
  uses this Parseval expansion implicitly throughout Section 2; classical
  Korenblum proofs (Korenblum 1991, Hayman–Korenblum 1995, Hedenmalm–Jakobsson–Shimorin)
  use it explicitly. Without a Lean-side `bergmanNormSq f = ∑' k, π/(k+1)
  ‖a_k‖²`, no honest c-push can compose against the existing
  circle-mean Parseval scaffolding (sprints 008–010) without rebuilding
  the radial integration from scratch.

- **The proof outline is bounded, with one genuinely uncertain step.**
  Each step is one Mathlib lemma, but the `tsum`-vs-`∫` swap is the
  pivotal piece:
  - **(1)** From `AnalyticOn ℂ f UnitDisk`, both `cauchyPowerSeries f 0 R₁`
    and `cauchyPowerSeries f 0 R₂` represent `f` on the corresponding
    closed balls (since both `R_i < 1`). By `HasFPowerSeriesOnBall`
    uniqueness (Mathlib: `HasFPowerSeriesOnBall.unique` or
    `HasFPowerSeriesAt.eq_formalMultilinearSeries` — the radius-of-
    convergence-of-the-Taylor-series-at-0 is well-defined and the
    coefficients of any valid power-series witness must agree) the two
    power series are equal *as formal series*, so all coefficients are
    equal, hence the norms are equal. Mathlib name to investigate:
    `HasFPowerSeriesAt.eq_formalMultilinearSeries` /
    `HasFPowerSeriesAt.unique` / `HasFPowerSeriesOnBall.eq_formalMultilinearSeries`.
  - **(2)** Bergman Parseval identity. The `tsum`-vs-`∫` swap is the
    pivotal step. The integrand
    `r ↦ ∑' k, (2π · r^(2k)) · ‖a_k‖² · r = ∑' k, (2π · r^(2k+1)) · ‖a_k‖²`
    has each per-term integrand `(2π · r^(2k+1)) · ‖a_k‖² ≥ 0` for
    `r ∈ (0, 1)`. The Mathlib swap lemma is one of:
    - `MeasureTheory.integral_tsum` (requires per-summand integrability
      and summability of the tsum-of-norms),
    - `MeasureTheory.tsum_integral_eq_integral_tsum` (the dual),
    - `MeasureTheory.lintegral_tsum` (for `ℝ≥0∞`-valued, via Tonelli)
      with a `toReal` post-step,
    - `MeasureTheory.hasSum_integral_of_dominated_convergence` (via
      partial sums plus a uniform integrable bound).
    The cleanest route depends on which Mathlib API is exposed; the
    nonneg-integrand form via Tonelli is the most robust, since
    nonneg-`tsum` is automatically a `lintegral` under `ENNReal.ofReal`.
  - **(2)** Per-term integral. `∫ r ∈ Ioo 0 1, (2π · r^(2k+1)) dr =
    2π · ∫_{(0,1)} r^(2k+1) dr = 2π · 1/(2k+2) = π/(k+1)`. Reachable via
    `intervalIntegral.integral_pow` (which gives `∫ r in 0..1, r^n dr =
    1/(n+1)`) plus the conversion `intervalIntegral` ↔
    `MeasureTheory.integral` over `Ioc` / `Ioo` (the Mathlib convention is
    that `intervalIntegral` is defined via `∫ ∂ Ioc`, which equals
    `∫ ∂ Ioo` when the boundary has measure zero — which is true for
    Lebesgue on `ℝ`). The conversion lemma is one of
    `intervalIntegral.integral_of_le` / `Real.volume_Ioc_eq_volume_Ioo`-
    style boundary-measure-zero argument.
  - **(3)** Direct `tsum_le_tsum` of the per-term inequality
    `(π / (k+1)) ‖a_k‖² ≤ (π / (k+1)) ‖b_k‖²` from `‖a_k‖ ≤ ‖b_k‖`,
    with summability on both sides inherited from the Bergman-Parseval
    identity (2) (each side equals a real number).

- **Falsifiable in one Generator session.** Each step above is one
  Mathlib lemma (or a short composition). The genuinely uncertain step
  is the `tsum`-vs-`∫` swap: which of Mathlib's three or four swap APIs
  is the cleanest? The generator must record in `Experience.md` which
  one was tried and what the obstruction was if the chosen API does not
  unify with the Parseval form. The radius-independence (1) is a more
  routine bookkeeping step and should not be a blocker.

- **The `r = 0` corner.** At `r = 0` (the lower endpoint of the radial
  integral), `circleMeanSq f 0 = 2π · ‖f 0‖²` is a constant; the
  integrand `circleMeanSq f r * r` vanishes at `r = 0` because of the
  `r` factor, so the corner contributes nothing. No extra branch
  bookkeeping is required because the integral is over the open
  interval `Ioo 0 1` (not `Icc 0 1`).

- **The `r = 1` corner.** The radial integral is over `Ioo 0 1`, not
  `Ioc 0 1`. The `r → 1⁻` limit of `circleMeanSq f r` may diverge for
  `f` analytic on the *open* disk (e.g. `f = 1/(1-z)`), but the
  divergence is integrable against the radial measure `r dr` for
  Bergman-A²-integrable `f`. The Bergman integrability hypothesis on
  `f` (i.e. `bergmanNormSq f < ∞`) is what guarantees integrability of
  the radial integrand. This is *exactly* the hypothesis chain that
  `bergmanNormSq_radial_polar` already threads through `hf_polar`; no
  new integrability hypothesis is needed here.

- **Why not also push c.** Outer-annulus pointwise dominance
  `∀ z ∈ outerAnnulus c, ‖f z‖ ≤ ‖g z‖` does **not** imply
  coefficient-level dominance `∀ k, ‖a_k‖ ≤ ‖b_k‖`. (Counterexample:
  `f = z`, `g = 1` — coefficient[0] of `f` is 0 ≤ 1 = coefficient[0]
  of `g`, but coefficient[1] of `f` is 1 ≰ 0 = coefficient[1] of `g`,
  yet outer-annulus dominance for some `c ∈ (0, 1)` is plausible.) So
  the Bergman Parseval identity (3) `bergmanNormSq_termwise_mono` is
  *not directly chainable* with the contract hypothesis. The genuine
  c-push requires a different ingredient: a circle-mean / boundary-L²
  comparison that *does* follow from outer-annulus pointwise dominance,
  via subharmonic mean-value or pseudohyperbolic / Möbius-distance
  arguments. That is the actual mathematical content of Korenblum and
  is not the target of this sprint. Pinning the Bergman Parseval
  identity as scaffolding-only isolates the radial-integration content
  cleanly and keeps the sprint acceptance criterion falsifiable in one
  Generator session.

- **Why not bundle into a numerical-budget push.** The workspace
  currently has zero Bergman-side coefficient identities. Without one,
  no honest c-push can compile against the circle-mean Parseval
  scaffolding (sprints 008–010) without rebuilding the radial
  integration from scratch. Filing a "push c from 0.3554 to 0.36 via
  direct Mathlib argument" sprint at this stage would be premature —
  the Bergman Parseval identity is the prerequisite, not the inverse.

- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Parseval
  / boundary L² expansions on analytic functions"*, *"termwise
  summability and `tsum`-level rearrangements"*, *"Lebesgue-integral
  monotonicity on annulus regions"*, and *"`nlinarith` / `polyrith` /
  `field_simp` / `ring` chains hundreds of lines long"* as in scope.
  The radial integration of a `tsum` of nonneg terms is exactly one
  such chain, sitting at the intersection of measure-theory and
  power-series APIs.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/BergmanParseval.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.RadialBergman`, `Proof.AnalyticParseval`,
    `Proof.CircleMeanRadial` (and **only** those workspace-side imports),

  - exposes (1) `cauchyPowerSeries_coeff_norm_radius_invariant`. Statement
    (or equivalent — the exact strength is at the generator's
    discretion as long as the norm equality is delivered):

    ```lean
    theorem cauchyPowerSeries_coeff_norm_radius_invariant
        {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        {R₁ R₂ : ℝ≥0}
        (hR₁_pos : 0 < (R₁ : ℝ)) (hR₁_lt : (R₁ : ℝ) < 1)
        (hR₂_pos : 0 < (R₂ : ℝ)) (hR₂_lt : (R₂ : ℝ) < 1) :
        ∀ k : ℕ,
          ‖(cauchyPowerSeries f 0 R₁).coeff k‖
            = ‖(cauchyPowerSeries f 0 R₂).coeff k‖
    ```

    Proof outline: From `AnalyticOn ℂ f UnitDisk` and `(R_i : ℝ) < 1`,
    derive `HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R_i) 0 (R_i : ℝ≥0∞)`
    as in sprint 010 / sprint 009. Both witnesses represent `f` at `0`,
    so by Mathlib's `HasFPowerSeriesAt` uniqueness
    (`HasFPowerSeriesOnBall.unique` /
    `HasFPowerSeriesAt.eq_formalMultilinearSeries`), the two formal
    series are equal, hence each coefficient (and its norm) agrees.

    *Fallback*: if the coefficient equality is too brittle and only the
    *norm equality* unifies cleanly, the generator may state and prove
    only the norm version. The norm version is what the downstream
    consumer (2) actually needs.

  - exposes (2) `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`.
    Statement (or equivalent):

    ```lean
    theorem bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk
        {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
        (hf_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume)) :
        bergmanNormSq f
          = ∑' k : ℕ,
              (Real.pi / ((k : ℝ) + 1))
                * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
    ```

    Proof outline:
    - **Step A**: rewrite `bergmanNormSq f` via `bergmanNormSq_radial_polar
      hf_polar` into `∫ r ∈ Ioo 0 1, circleMeanSq f r * r`.
    - **Step B**: pointwise on the integrand, apply sprint 010's canonical-
      witness identity at radius `r` with `R' := ⟨(r+1)/2, _⟩` (so
      `r < (R' : ℝ) < 1`), then apply (1) to identify
      `‖(cauchyPowerSeries f 0 R').coeff k‖ = ‖(cauchyPowerSeries f 0 R).coeff k‖`.
      The integrand becomes
      `(∑' k, (2π · r^(2k)) · ‖a_k‖²) · r = ∑' k, (2π · r^(2k+1)) · ‖a_k‖²`
      where `a_k := (cauchyPowerSeries f 0 R).coeff k`. The `tsum * r` to
      `tsum (· * r)` is `tsum_mul_right` (Mathlib name).
    - **Step C**: swap `∫` and `∑'`. The cleanest route is the nonneg-
      integrand Tonelli swap via `MeasureTheory.lintegral_tsum`:
      cast the nonneg `(2π · r^(2k+1)) · ‖a_k‖²` to `ℝ≥0∞` via
      `ENNReal.ofReal`, swap, then cast back. Alternatively
      `MeasureTheory.integral_tsum` with per-summand integrability
      (each summand is `(2π · ‖a_k‖²) · r^(2k+1)`, a polynomial in `r`,
      trivially integrable on `Ioo 0 1`). The generator picks whichever
      compiles cleanly. After the swap:
      `∫ r ∈ Ioo 0 1, ∑' k, (2π · r^(2k+1)) · ‖a_k‖²
       = ∑' k, ∫ r ∈ Ioo 0 1, (2π · r^(2k+1)) · ‖a_k‖²
       = ∑' k, (2π · ‖a_k‖²) · ∫ r ∈ Ioo 0 1, r^(2k+1)`
      via `MeasureTheory.integral_const_mul`.
    - **Step D**: per-term integral. `∫ r ∈ Ioo 0 1, r^(2k+1) dr =
      1 / (2k + 2)`. Mathlib path: convert `∫ ∂ Ioo` to
      `intervalIntegral` via `intervalIntegral.integral_of_le` plus
      `Real.volume_Ioc` boundary-measure-zero (or directly via
      `MeasureTheory.integral_pow` if it has an `Ioo` form), then
      `intervalIntegral.integral_pow 0 1 (2k+1)`. The closed form is
      `(1^(2k+2) - 0^(2k+2)) / (2k+2) = 1/(2k+2)` for `k ≥ 0`.
    - **Step E**: arithmetic. `(2π · ‖a_k‖²) · (1/(2k+2)) =
      π / (k+1) · ‖a_k‖²`. Each side is a real, the per-term
      identity is `field_simp` + `ring` (using `(k : ℝ) + 1 ≠ 0`).
    - **Step F**: rewrite the final `tsum` to match the headline form.
      The generator may consolidate Steps C–E into a single `tsum_congr`
      if cleaner.

    The generator is free to consolidate steps or to use a different
    Mathlib path (e.g. `MeasureTheory.integral_tsum_of_summable_norm`
    or `MeasureTheory.hasSum_integral_of_summable`) as long as the
    conclusion is unchanged and the proof is a `theorem` (no `axiom`,
    no `sorry`).

  - exposes (3) `bergmanNormSq_termwise_mono`. Statement (or equivalent):

    ```lean
    theorem bergmanNormSq_termwise_mono
        {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
        (hg : AnalyticOn ℂ g UnitDisk)
        {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
        (hf_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        (hg_polar : IntegrableOn
            (fun p : ℝ × ℝ => p.1 * ‖g (Complex.polarCoord.symm p)‖ ^ 2)
            (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
            ((volume : Measure ℝ).prod volume))
        (h_coeff : ∀ k : ℕ,
            ‖(cauchyPowerSeries f 0 R).coeff k‖
              ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
        bergmanNormSq f ≤ bergmanNormSq g
    ```

    Proof outline: rewrite both sides via (2). Apply `tsum_le_tsum` on
    the per-term inequality `(π/(k+1)) ‖a_k‖² ≤ (π/(k+1)) ‖b_k‖²`,
    using `pow_le_pow_left₀` (squaring is monotone on nonneg) plus
    `mul_le_mul_of_nonneg_left` (multiply by the nonneg constant
    `π/(k+1)`). Per-side summability is immediate from (2) (each side
    equals a real number, hence the implicit `Summable`).

  - All three items must be `theorem`/`lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as long
    as the conclusion is unchanged.

- `ProofRefinement/Korenblum/Candidates/V11.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V11`, marked
  `-- @parent V10`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V10),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V10,
  - imports `ProofRefinement.Korenblum.Proof.CandidateContract`,
    `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`,
    `ProofRefinement.Korenblum.Proof.CircleExpBridge`,
    `ProofRefinement.Korenblum.Proof.CircleInnerProduct`,
    `ProofRefinement.Korenblum.Proof.CirclePolynomialParseval`,
    `ProofRefinement.Korenblum.Proof.AnalyticParseval`,
    `ProofRefinement.Korenblum.Proof.CircleMeanRadial`,
    and the new
    `ProofRefinement.Korenblum.Proof.BergmanParseval` so that the new
    module is part of V11's compile graph and is exercised by the build.
    No structural use of the new lemmas in V11 itself is required.
- No edits to `lemma.toml`. No edits to V0/.../V10 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V11` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V11.lean` succeeds (the evaluator
   accepts V11 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V10; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/BergmanParseval.lean`
   contains:
   - one `theorem` (or `lemma`) named
     `cauchyPowerSeries_coeff_norm_radius_invariant`
     (or equivalently named) whose conclusion is the equality of
     `‖(cauchyPowerSeries f 0 R₁).coeff k‖` and
     `‖(cauchyPowerSeries f 0 R₂).coeff k‖` for any two NNReal radii
     `R₁, R₂` with `0 < (R_i : ℝ) < 1`, for `f` analytic on `UnitDisk`;
   - one `theorem` (or `lemma`) named
     `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
     (or equivalently named) whose conclusion is
     `bergmanNormSq f = ∑' k, (π / ((k : ℝ) + 1)) *
                          ‖(cauchyPowerSeries f 0 R).coeff k‖²`
     for `f` analytic on `UnitDisk`, NNReal `R` with `0 < (R : ℝ) < 1`,
     and the polar integrability hypothesis required by
     `bergmanNormSq_radial_polar`;
   - one `theorem` (or `lemma`) named `bergmanNormSq_termwise_mono`
     (or equivalently named) whose conclusion is `bergmanNormSq f ≤
     bergmanNormSq g` from `‖a_k‖ ≤ ‖b_k‖` pointwise on the canonical
     Cauchy-power-series coefficients (and the polar integrability
     hypotheses for both `f` and `g`).
   All three must be `theorem` / `lemma`, never `axiom`, with no `sorry`.
   The proof of (2) (Bergman Parseval identity) must genuinely *use* both
   `bergmanNormSq_radial_polar` (sprint 003) and
   `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
   (sprint 010) — not bypass via a parallel direct argument — so that
   the chain through radial-polar-form + canonical-witness Parseval is
   the one actually exercised by the build.
4. The new module `Proof.BergmanParseval` must be **used**, even
   trivially, somewhere in V11's transitive compile graph (importing it
   from V11 is sufficient — it forces the module to compile as part of
   V11's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V10.lean`) or the existing
  `Proof/*.lean` files. The downstream consumers built on top of (1)–(3)
  are the next sprint's job, not this one's.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If any of the three lemmas is genuinely blocked
  on a missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- **Attempt to prove that outer-annulus pointwise dominance implies
  coefficient-level dominance.** It does not (counterexample above), so
  any attempt would be mathematically wrong. This sprint pins the
  Bergman Parseval identity *unconditionally*; the bridge from outer-
  annulus pointwise dominance to coefficient-level dominance is the
  actual content of Korenblum and is at least one full follow-up sprint
  (more likely several), via subharmonic mean-value or pseudohyperbolic
  / Möbius-distance arguments.
- Bridge `bergmanNormSq` to Mathlib's classical Bergman-space API
  (`Bergman` / `BergmanSpace` / `weightedHardy`). Useful long-term but
  not required here.
- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the Bergman-Parseval coefficient identity
  that any future c-push must consume.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. the Mathlib uniqueness lemma for
  `HasFPowerSeriesOnBall` is not `HasFPowerSeriesOnBall.unique` but a
  different name and the alternative path is brittle, or
  `MeasureTheory.integral_tsum` requires a per-summand integrability or
  summable-norm hypothesis the generator cannot discharge cleanly from
  the polynomial form `(2π · ‖a_k‖²) · r^(2k+1)`, or the conversion
  between `∫ ∂ Ioo` and `intervalIntegral.integral` introduces a
  measure-zero-boundary obstruction that does not unify, or the
  per-term integral `∫_0^1 r^(2k+1) dr = 1/(2k+2)` requires a Mathlib
  `intervalIntegral.integral_pow` variant the generator cannot find):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (e.g. whether the generator tried `MeasureTheory.integral_tsum`
  versus `MeasureTheory.lintegral_tsum` plus `ENNReal.ofReal` casting
  versus `MeasureTheory.hasSum_integral_of_dominated_convergence`;
  whether the radius-independence in (1) went through
  `HasFPowerSeriesOnBall.unique` versus
  `HasFPowerSeriesAt.eq_formalMultilinearSeries` versus a manual
  `iteratedFDeriv` / `cauchyPowerSeries_def` rewrite; whether the
  per-term integral went through `intervalIntegral.integral_pow`
  versus `MeasureTheory.integral_pow` versus a manual antiderivative
  argument).

  **Fallback form** (if the canonical-witness `cauchyPowerSeries`
  formulation in (2) is too brittle): the generator may instead expose
  (2) as a *witnessed* identity — pick *any* `R : ℝ≥0` with
  `0 < (R : ℝ) < 1` and state the identity for that `R`, and prove
  the radius-independence (1) only for the *norm* (not the
  coefficient itself). This is strictly weaker but still strong
  enough for (3) to drop out: `bergmanNormSq_termwise_mono` only
  consumes the norm equality from (1) and the identity (2) at the
  chosen `R`. The fallback is acceptable if and only if the generator
  records in `Experience.md` why the stronger form was infeasible.

  **Second fallback** (if the `tsum`-vs-`∫` swap in (2) is too
  brittle in any form): the generator may instead deliver only (1) and
  (3) as a *direct chain* not through (2):
  - (1) as stated, and
  - (3') `bergmanNormSq_termwise_mono`'s conclusion proved
    *without* the intermediate `bergmanNormSq = ∑' k, …` identity —
    instead, by `bergmanNormSq_radial_polar` plus
    `circleMeanSq_termwise_mono` (sprint 010) integrated radially
    via `setIntegral_mono_on` on `Ioo 0 1`.
  This bypasses the `tsum`-vs-`∫` swap entirely. If the generator
  takes this fallback, (2) is filed as `STATUS=BLOCKED` with the
  obstruction recorded in `Experience.md`, and the sprint partial-
  passes by shipping (1) and (3') only. Any future c-push consumer
  prefers (3) over (3') because it makes the coefficient-level
  comparison explicit, but (3') is a strictly weaker but still-useful
  stand-in.
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
