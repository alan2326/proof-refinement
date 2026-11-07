# Experience — Korenblum refinement notebook (noPF arm)

Append-only narrative notes from generators and planners.

Conventions:

- `### YYYY-MM-DD sprint_<NNN>`
- one short paragraph per entry
- describe changes and observations, not pass/fail

_Initial state — no entries yet._

### 2026-05-07 sprint_001

Built `Proof/PolarBergman.lean` against Mathlib: a `bergmanNormSq_polar`
theorem rewriting `∫_𝔻 ‖f‖² dA` as the iterated polar integral
`∫ r ∈ (0,1), ∫ θ ∈ (-π,π), ‖f (polarCoord.symm (r,θ))‖² · r`. The proof
chains six steps: indicator rewrite (`integral_indicator`), reverse polar
substitution (`Complex.integral_comp_polarCoord_symm`), domain shrinkage
from `Ioi 0 ×ˢ Ioo (-π) π` to `Ioo 0 1 ×ˢ Ioo (-π) π` via
`setIntegral_eq_of_subset_of_forall_diff_eq_zero` (using that the unit
disk indicator vanishes for `r ≥ 1`), pointwise indicator unfolding inside
the smaller box (`setIntegral_congr_fun`), Fubini (`setIntegral_prod`),
and a final `mul_comm` cleanup. The integrability hypothesis was threaded
through as `IntegrableOn (fun p => p.1 * ‖f (polarCoord.symm p)‖²)
(Ioo 0 1 ×ˢ Ioo (-π) π) (volume.prod volume)`; future sprints will derive
this from analyticity / boundedness of `f` on the disk. V1 ships with
`c = 3554/10000` unchanged from V0; the contribution is the new derived
module that any non-trivial follow-up will consume.

### 2026-05-07 sprint_003

Built `Proof/RadialBergman.lean` against Mathlib, bridging the polar
pull-back of the whole disk (`Proof.PolarBergman`) and the inner / outer
set-integral split (`Proof.AnnulusBergman`). Pinned the canonical
`circleMeanSq f r := ∫ θ in Ioo (-π) π, ‖f (polarCoord.symm (r,θ))‖²`
(no `1/(2π)` normalisation) and shipped three radial polar-form lemmas:
(a) `bergmanNormSq_radial_polar` — folds the iterated polar form of the
whole disk into a single `r`-integral of `circleMeanSq f r * r` over
`Ioo 0 1`, derived from `bergmanNormSq_polar` by a `setIntegral_congr_fun`
plus `integral_mul_const`; (b) `outerAnnulus_norm_sq_polar` over
`Ioo c 1` and (c) `innerDisk_norm_sq_polar` over `Ioc 0 c`. The two
halves were proved by independently mirroring `bergmanNormSq_polar`'s
six-step shape (indicator rewrite, `Complex.integral_comp_polarCoord_symm`,
domain shrinkage via `setIntegral_eq_of_subset_of_forall_diff_eq_zero`,
indicator unfold via `setIntegral_congr_fun`, Fubini via `setIntegral_prod`,
and a final `integral_const_mul` + `mul_comm` to refold the inner
θ-integral as `circleMeanSq f r * r`). Boundary handling at `r = c` was
sidestepped by choosing `Ioo c 1` for the outer half (open on both ends,
`outerAnnulus c = {z | c < ‖z‖ < 1}`) and `Ioc 0 c` for the inner half
(half-open at 0, closed at c, matching `innerDisk c = {z | ‖z‖ ≤ c ∧
‖z‖ < 1}` modulo the origin which has measure zero). One subtle wart:
`Ioi 0` membership did not directly defeq into `0 < p.1` for the
`abs_of_pos` rewrite, so I introduced an explicit `hr_pos_real : 0 < p.1
:= hr_pos` projection in both `h_diff_zero` blocks. A second wart:
`integral_mul_const` (∫ f * c = ∫ f * c) does not match a goal of shape
`∫ c * f = c * ∫ f`, so the inner-θ refolding uses `integral_const_mul`
followed by `mul_comm` rather than a single `integral_mul_const`. V3
ships with `c = 3554/10000` unchanged from V2; the contribution is the
new derived module that bridges polar and annulus scaffolding and pins
the exact `circleMeanSq` API every subsequent monotone-mean / subharmonic
argument must consume.

### 2026-05-07 sprint_006

Built `Proof/CircleExpBridge.lean` against Mathlib. Five theorems shipped,
all `theorem`s, no `axiom`, no `sorry`. (1) `polarCoord_symm_eq_exp`: the
`Complex.polarCoord_symm_apply` unfold gives the polar-symm point as
`r * (Real.cos θ + Real.sin θ * I)` (Real cos / sin coerced to ℂ); a single
`rw` chain through `Complex.exp_mul_I`, `Complex.ofReal_cos`,
`Complex.ofReal_sin` rewrites this to `r * Complex.exp (θ * I)`. The Mathlib
names are `Complex.ofReal_cos`/`Complex.ofReal_sin` — *not*
`Complex.cos_ofReal` (the latter is `(cos x).im = 0`, not the coercion
identity). The `(r,θ).1` / `(r,θ).2` projections collapse cleanly through
the rewrite chain without an explicit `simp [Prod.fst, Prod.snd]`. (2)
`norm_polarCoord_symm_pow`: `norm_pow` plus `Complex.norm_polarCoord_symm`
reduces the goal to `|r|^n^2 = r^(2n)`; then `abs_of_nonneg hr` removes the
absolute value, `← pow_mul` flattens nested powers, and `ring_nf` closes
the exponent arithmetic `n * 2 = 2 * n`. (3) `circleMeanSq_monomial`:
`setIntegral_congr_fun measurableSet_Ioo` rewrites the integrand pointwise
via (2) into the constant `r^(2n)`, then `setIntegral_const` plus
`Real.volume_real_Ioo_of_le` (the `.real` form, not `Real.volume_Ioo`
which gives `ENNReal.ofReal (b - a)`) gives `(π - -π) • r^(2n)`, closed
with `smul_eq_mul` and `ring`. (4) `circleMeanSq_const`: the integrand is
already constant, so `setIntegral_const` + `Real.volume_real_Ioo_of_le` +
`smul_eq_mul` + `ring` closes it directly. (5) `circleMeanSq_smul`:
`norm_mul` + `mul_pow` rewrite the integrand pointwise to
`‖c‖² · ‖f(...)‖²`; `integral_const_mul` (which is the `r * f` direction,
not `f * r` — `integral_mul_const` is the wrong direction here) pulls the
scalar out. V6 ships with `c = 3554/10000` unchanged from V5; the
contribution is the new derived module that bridges
`Complex.polarCoord.symm` to `Complex.exp` and exposes the seed
monomial / constant / scaling identities for `circleMeanSq`. This is the
first mathlib-API gateway opened in the workspace toward
Bergman-Parseval / monomial-decomposition arguments — every honest analytic
chain past `c = 0.3554` will compose through some identity of this kind.

### 2026-05-07 sprint_008

Built `Proof/CirclePolynomialParseval.lean` against Mathlib. Eight theorems
shipped, all `theorem`s, no `axiom`, no `sorry`. (1) The four sesquilinearity
handles (`circleMeanInner_add_left`, `_add_right`, `_smul_left`,
`_smul_right`) reduce to `setIntegral_congr_fun` pointwise plus
`MeasureTheory.integral_add` (with per-summand integrability hypotheses on
the conjugate-product integrand) or `MeasureTheory.integral_const_mul` (no
integrability hypothesis). The `_smul_left` rewrite needs `(starRingEnd ℂ)`
to distribute through `*`, which is `map_mul`, then a `ring` inside the
pointwise rewrite reorders the constants. (2) The two Finset-sum-shape
consumers (`circleMeanInner_finset_sum_monomial_left`,
`circleMeanInner_finset_sum_monomial_right`, both specialised to monomial
coefficients `∑ k ∈ s, a k * z^k`) bypass the binary-induction route entirely:
expand the integrand pointwise via `map_sum` plus `Finset.sum_mul`, then
swap `∫` and `∑` directly via `MeasureTheory.integral_finset_sum` (each
per-summand integrand is integrable, since each is a constant `a k` times
the integrable `conj(P^k) * g`). This is the cleanest path; it avoids the
integrability bookkeeping of induction-on-sums entirely. (3)
`circleMeanInner_polynomial_self`: the proof outline from the contract
fired correctly: apply (2) `_finset_sum_monomial_left`, then (2)
`_finset_sum_monomial_right` inside each `circleMeanInner (z^m) (∑ a_n z^n) r`,
distribute conj(a m) into the inner sum to get
`∑ m ∑ n, conj(a m) * a n * circleMeanInner (z^m) (z^n) r`, then per-term
case-split via `by_cases h : n = k`: off-diagonal vanishes by
`circleMeanInner_monomial_diff` (sprint 007), diagonal collapses by
`circleMeanInner_monomial_same` (sprint 007) and rewrite of
`conj(a k) * a k = (Complex.normSq (a k) : ℂ) = ((‖a k‖² : ℝ) : ℂ)`. The
inner-sum collapse goes through `Finset.sum_ite_eq'` after a
`b := fun _ : ℕ => C` reshuffle (the diagonal value depends on the outer
index `k`, not on the inner summation index `n`, so `b` is a constant
function — `Finset.sum_ite_eq'` requires `b : ι → M`, but a constant
function fits). (4) `circleMeanSq_polynomial`: bridge to `circleMeanInner`
via `circleMeanSq_eq_re_circleMeanInner_self` (sprint 007), apply (3),
then `Complex.re_sum` distributes `.re` past the finite sum, then per-term
`Complex.ofReal_re` collapses the coerced real to its real part. The
integrability lemmas for the per-summand integrands are pinned by two
private `Continuous.integrableOn_Ioc.mono_set Ioo_subset_Ioc_self` proofs
(`Continuous.integrableOn_Ioo` does **not** exist as a Mathlib name —
`Ioo` integrability is reached by the `Ioc → Ioo` set restriction). The
continuity of `θ ↦ Complex.polarCoord.symm (r, θ) : ℂ` is reached by
`Continuous.congr` to `r * Complex.exp (θ * I)` via the workspace's
`polarCoord_symm_eq_exp` (sprint 006); there is no
`Complex.continuous_polarCoord_symm` in Mathlib (the unprefixed
`continuous_polarCoord_symm` is for the real `polarCoord` map on `ℝ × ℝ`).
V8 ships with `c = 3554/10000` unchanged from V7; the contribution is the
new derived module that finally pins, in Lean, the algebraic equation at
the heart of every honest Korenblum proof: the `A²` circle-mean of a
polynomial is a coefficient-level termwise sum
`circleMeanSq (∑ a_k z^k) r = ∑ k, (2π · r^(2k)) * ‖a k‖²`. With this
identity in place, the inner-half radial dominance hypothesis of sprint 005
(`validKorenblum_of_innerCircleMean_dom`) becomes attackable for polynomial
`f, g` as a coefficient-level inequality — the natural next sprint.

### 2026-05-07 sprint_002

Built `Proof/AnnulusBergman.lean` against Mathlib. Defined
`outerAnnulus c = {z | c < ‖z‖ ∧ ‖z‖ < 1}` and
`innerDisk c = {z | ‖z‖ ≤ c ∧ ‖z‖ < 1}` directly (rather than via Mathlib
`Metric.ball/closedBall`); each measurability proof is one
`measurableSet_lt`/`measurableSet_le` of `continuous_norm.measurable`
against a constant. The disjoint-union of `UnitDisk` is handled by a
direct `by_cases ‖z‖ ≤ c` rather than a sphere-measure-zero argument: the
inner disk is closed-on-the-norm (`‖z‖ ≤ c`) and the outer annulus is
open-on-the-norm (`c < ‖z‖`), so they cleanly partition the unit disk
without any null-set bookkeeping. `bergmanNormSq_split` then drops out of
`setIntegral_union` once we shuttle the integrability hypothesis through
`integrableOn_union.mp`. The outer-annulus monotonicity lemma
`outerAnnulus_norm_sq_mono` follows from `setIntegral_mono_on` plus
`pow_le_pow_left₀` (the Mathlib name for the squaring monotonicity on
non-negatives — the un-suffixed `pow_le_pow_left` does not exist in this
toolchain). V2 ships with `c = 3554/10000` unchanged; the score is the
same as V1 but the build graph now exercises both `Proof.PolarBergman`
and the new `Proof.AnnulusBergman`. The two scaffolding modules are
independent and together cover the next-smallest reusable Bergman
handles for any future Korenblum-style argument: polar pull-back of the
`A²` norm, plus the inner/outer split with the easy outer half closed by
direct integral monotonicity.


### 2026-05-07 sprint_010

Built `Proof/CircleMeanRadial.lean` against Mathlib and the existing
`Proof/AnalyticParseval.lean` (sprint 009). Three theorems:
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` —
canonical-witness analytic Bergman-Parseval identity (strengthens sprint
009's existential to fix the witness as `cauchyPowerSeries f 0 R` for an
explicit NNReal `R`); `circleMeanSq_termwise_mono` — termwise comparison
of `circleMeanSq` from coefficient-norm domination; and the headline
`circleMeanSq_radial_mono` — `r ↦ circleMeanSq f r` is non-decreasing
on `[0, 1)` for any `f` analytic on `UnitDisk`. The radial-monotonicity
proof picks `R := ⟨(r₂ + 1)/2, _⟩`, applies the canonical-witness
identity at both `r₁` and `r₂` with the *same* `R`, then closes via
`Summable.tsum_le_tsum` over the per-term inequality `r₁^(2k) ≤ r₂^(2k)`
(produced by `pow_le_pow_left₀`) times the nonneg coefficient-square
constant. The summability hypothesis came from a private helper
`summable_parseval_cauchy` that re-runs sprint 009's uniform-convergence
+ dominated-convergence pipeline to extract a `HasSum` (rather than a
plain `tsum`) — the Parseval identity from sprint 009 only exposes the
`tsum` value, but `Summable` is needed for the comparison lemma.
The re-derivation is verbatim from sprint 009 except for two
adaptations: (a) `convert h_uniform using 1` replaces the
`rw [← h_eq2]` rewrite for the `f (0 + y) = f y` cleanup, since the
direct rewrite would also descend into `cauchyPowerSeries f 0 R` (now a
visible term in the goal) and corrupt the formal series; (b) the
partial-sum unfold `(cauchyPowerSeries f 0 R).partialSum N z =
∑ k ∈ range N, p.coeff k * z^k` is done as a standalone
`have h_ps_eq` before the `setIntegral_congr_fun` rather than inline
inside `congr 1`, since the inline `congr 1` form did not unify with
the wrapped `‖·‖²` form. V10 ships with `c_value = 3554/10000`
unchanged from V9; the sprint is scaffolding-only and adds the
canonical building block that any future inner-half c-push must consume
for radial transport of `circleMeanSq` data across radii.

### 2026-05-07 sprint_011

Built `Proof/BergmanParseval.lean` against Mathlib and the existing
`Proof/CircleMeanRadial.lean` (sprint 010). Three theorems shipped, all
`theorem`s, no `axiom`, no `sorry`. (1)
`cauchyPowerSeries_coeff_norm_radius_invariant` — radius-independence of
Cauchy power-series coefficient norms for `f` analytic on `UnitDisk`. The
proof goes through `HasFPowerSeriesAt.eq_formalMultilinearSeries` (Mathlib
`Mathlib/Analysis/Analytic/Uniqueness.lean`): both `cauchyPowerSeries f 0 R₁`
and `cauchyPowerSeries f 0 R₂` are valid power-series witnesses for `f` at
`0` (extracted via `DifferentiableOn.hasFPowerSeriesOnBall` then
`HasFPowerSeriesOnBall.hasFPowerSeriesAt`), so the formal series themselves
agree (not just their norms). (2)
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` — the
Bergman A² Parseval identity: `bergmanNormSq f = ∑' k, π/(k+1) * ‖a_k‖²`
where `a_k = (cauchyPowerSeries f 0 R).coeff k` for any chosen NNReal
`R ∈ (0, 1)`. The proof composes (a) `bergmanNormSq_radial_polar`
(sprint 003) to fold into `∫ r ∈ Ioo 0 1, circleMeanSq f r * r`,
(b) per-`r` canonical-witness identity at `R'(r) := ⟨(r+1)/2, _⟩` plus
(1) to canonicalise coefficient norms to the chosen `R`,
(c) `MeasureTheory.integral_tsum_of_summable_integral_norm` to swap `∫`
and `∑'` (with summability of `fun k => π/(k+1) * ‖a_k‖²` proved via
`summable_of_sum_range_le` against the bound `bergmanNormSq f`,
through partial-sum-≤-tsum + `setIntegral_mono_on`),
(d) per-term integral `∫ r ∈ Ioo 0 1, (2π · ‖a_k‖²) · r^(2k+1) dr =
π/(k+1) * ‖a_k‖²` via `integral_const_mul`, `integral_Ioc_eq_integral_Ioo`,
`intervalIntegral.integral_of_le`, and `intervalIntegral.integral_pow`.
(3) `bergmanNormSq_termwise_mono` — coefficient-level Bergman comparison
consumer: applies (2) to both sides, then `tsum_le_tsum` over the per-term
inequality `(π/(k+1)) ‖a_k‖² ≤ (π/(k+1)) ‖b_k‖²` from `‖a_k‖ ≤ ‖b_k‖`.

Three Mathlib-name notes for future planners. (a) `Continuous.integrableOn_Ioo`
does not exist; the integrability of a continuous function on `Ioo` is reached
by `Continuous.integrableOn_Ioc` followed by `Set.Ioo_subset_Ioc_self`
restriction (same wart already documented in sprint 008). (b) `tsum_mul_right`
is the form `∑' x, f x * a = (∑' x, f x) * a`; we want the other direction
to push `* r` inside, so we use `← tsum_mul_right`. (c) The partial-sum bound
`Summable.sum_le_tsum (range N) ...` is namespaced under `Summable`, not
top-level `sum_le_tsum`. The three together make this style of proof land
about three-times longer than expected on first attempt.

A genuinely tricky step was the per-`r` summability of
`fun k => parsevalRadialTerm a k r` for the partial-sum-≤-tsum argument.
The existing `summable_parseval_cauchy` in `CircleMeanRadial.lean` is
`private` and so unreachable; rather than duplicate its 100+ line
uniform-convergence proof, we take a completely different (and shorter)
route via `FormalMultilinearSeries.summable_norm_mul_pow`: for `r < R'(r)`,
the Cauchy power series at `R'(r)` has radius ≥ `R'(r) > r`, so
`Summable (fun n => ‖p n‖ * r^n)`. The summands then tend to `0`, so
eventually `(‖p n‖ * r^n)² ≤ ‖p n‖ * r^n`, and squaring summability is
secured via `Summable.of_norm_bounded_eventually_nat`. Coefficient-norm
radius-independence (1) transfers from `R'(r)` to the chosen `R`. The
upshot is a much more compact summability lemma than the dominated-
convergence approach in sprint 010.

The integrability of `r ↦ circleMeanSq f r * r` on `Ioo 0 1` (needed for
`setIntegral_mono_on`) is derived from the polar integrability hypothesis
`hf_polar` via `Measure.prod_restrict` (to convert `IntegrableOn ... (·×ˢ·)`
to `Integrable ... (μ.prod ν)` over restricted measures) plus
`Integrable.integral_prod_left`. The inner-integral congruence `∫ θ, r * X
= (∫ θ, X) * r` needs an explicit `change` (the linter rejects `show` for
this) and an `integral_const_mul + mul_comm`.

V11 ships with `c_value = 3554/10000` unchanged from V10; the sprint is
scaffolding-only and adds the canonical Bergman A² Parseval identity in
`Proof/BergmanParseval.lean`. With this identity in place, every future
c-push consumer can compare `bergmanNormSq` at the coefficient level — the
direct Bergman analogue of `circleMeanSq_termwise_mono` from sprint 010.
The genuine c-push still requires bridging outer-annulus pointwise
dominance to coefficient-level dominance (which is *not* a tautology —
counterexample: `f = z, g = 1`); that bridge, via subharmonic mean-value
or pseudohyperbolic / Möbius-distance arguments, remains the actual
mathematical content of Korenblum and is the next sprint's job.

### 2026-05-07 sprint_012

Built `Proof/PolarIntegrability.lean` against Mathlib via Path 1 from the
contract (the `lintegral` form of polar substitution): two theorems
shipped, all `theorem`s, no `axiom`, no `sorry`. (1)
`polar_integrableOn_of_bergmanIntegrable` — for `Measurable f` and
`Integrable (fun z => ‖f z‖²) (volume.restrict UnitDisk)`, the polar
pullback `(r, θ) ↦ r · ‖f (polarCoord.symm (r,θ))‖²` is `IntegrableOn`
on `Ioo 0 1 ×ˢ Ioo (-π) π` against `volume.prod volume`. (2)
`polar_integrableOn_of_analyticOn_of_bergmanIntegrable` — the analytic-
`f` specialisation, deriving polar-composition AE strong measurability
from `AnalyticOn ℂ f UnitDisk` via `ContinuousOn.aestronglyMeasurable`
on the polar rectangle (after composing `AnalyticOn.continuousOn` with
`Continuous Complex.polarCoord.symm`).

The proof structure (shared between the two): apply
`Complex.lintegral_comp_polarCoord_symm` with
`g z := UnitDisk.indicator (fun w => ENNReal.ofReal (‖f w‖²)) z`. The RHS
`∫⁻ z, g z = ∫⁻ z in UnitDisk, ENNReal.ofReal (‖f z‖²)` is finite by
`hf_int.hasFiniteIntegral` plus `hasFiniteIntegral_iff_ofReal`. On the
rectangle `Ioo 0 1 ×ˢ Ioo (-π) π` (which is a subset of
`Complex.polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`), the indicator unfolds
to `ENNReal.ofReal (‖f (symm p)‖²)` since `r ∈ Ioo 0 1` maps to
`UnitDisk` via `polarCoord_symm_mem_unitDisk_iff` (sprint 001).
`lintegral_mono_set` then bounds the polar `lintegral` over the rectangle
by the polar `lintegral` over `polarTarget`, which equals the unit-disk
`lintegral` and is finite. `HasFiniteIntegral` then follows from
`Real.enorm_eq_ofReal` (the polar pullback is nonneg on the rectangle).

Three Mathlib-name notes for future planners. (a) The `pow 2` version of
`Measurable.pow` does not have an inferred `c` for `c = 2`; the correct
spelling is `Measurable.pow_const` (and similarly `AEMeasurable.pow_const`).
The unsuffixed `Measurable.pow` takes a measurable exponent. (b) The
parser treats `set g : ℂ → ℝ≥0∞ := ...` as ill-formed — the `≥0∞` after
`→` does not parse cleanly. The workaround is to write `set g : ℂ →
ENNReal := ...` (the underlying type) or to write `set g : (ℂ → ℝ≥0∞)
:= ...` with explicit grouping. (c) The `< ∞` notation for `ENNReal`
requires `open scoped ENNReal`; the unprefixed `< ∞` parses as
`LT.lt _ (OnePoint.infty : ?)` (from `Topology.Compactification.OnePoint`
which scopes `∞` to `OnePoint.infty`).

A subtle wart: `(0 : ℝ) ≤ᵐ[μ] fun z => ‖f z‖²` does not unify with
`hasFiniteIntegral_iff_ofReal h`'s expected hypothesis
`0 ≤ᵐ[μ] f` (where `f : α → ℝ` is the integrand and `0` should auto-coerce
to a constant function). The fix is to spell out the constant function
explicitly: `(fun _ : ℂ => (0 : ℝ)) ≤ᵐ[μ] fun z => ‖f z‖²`.

Another wart: `convert h_polar_sub using 1` followed by `lintegral_congr`
already closed the goal because `ENNReal.ofReal r • x` and `ENNReal.ofReal
r * x` are definitionally equal in `ENNReal`. The cleaner spelling is
`simp only [smul_eq_mul] at h_polar_sub; exact h_polar_sub` rather than
the `convert + lintegral_congr` chain.

Measurability hypothesis design choice: the basic theorem takes
`Measurable f` rather than `AEStronglyMeasurable f volume`. The reason is
that `AEStronglyMeasurable.comp_measurable` requires the measurability
of `f` against `Measure.map polarCoord.symm volume`, not `volume`
directly — and the polar map is *not* measure-preserving (it has the `r`
Jacobian). With `Measurable f`, the composition `f ∘ polarCoord.symm` is
trivially measurable via `Measurable.comp` against the continuity-derived
`Measurable polarCoord.symm`. The downstream consumer (analytic `f`)
sidesteps this entirely by deriving AE strong measurability of `f ∘
polarCoord.symm` directly on the rectangle from `ContinuousOn`, so the
basic-theorem hypothesis form is not the bottleneck for that path.

V12 ships with `c_value = 3554/10000` unchanged from V11; the sprint is
scaffolding-only and adds the polar-pullback integrability bridge that
every existing scaffolding consumer (`bergmanNormSq_polar`,
`bergmanNormSq_radial_polar`, `outerAnnulus_norm_sq_polar`,
`innerDisk_norm_sq_polar`, `validKorenblum_of_innerCircleMean_dom`,
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
`bergmanNormSq_termwise_mono`) takes as an opaque hypothesis. Future
c-push sprints can now consume the contract's `Integrable (‖f z‖²)
(volume.restrict UnitDisk)` directly, threading it through this bridge
to any of the existing Bergman / radial scaffolding without ad hoc
re-derivation. The genuine c-push (subharmonic mean-value or
pseudohyperbolic / Möbius-distance arguments) remains the next sprint's
content.

### 2026-05-07 sprint_013

Built `Proof/RadialIntegrability.lean` and `Proof/CleanConditional.lean`
against Mathlib. Five theorems shipped, all `theorem`s, no `axiom`, no
`sorry`. The contribution closes the last plumbing gap between sprint 012
(polar-pullback bridge from contract Bergman integrability) and sprint
005 (conditional Korenblum reduction `validKorenblum_of_innerCircleMean_dom`).

`Proof/RadialIntegrability.lean` exposes three Fubini-Tonelli derivations
from the polar-pullback `IntegrableOn` hypothesis:
(a) `radial_integrableOn_r_mul_circleMeanSq_Ioo_zero_one` — the radial
marginal `r ↦ r * circleMeanSq f r` is integrable on `Ioo 0 1`. The
proof routes through `Measure.prod_restrict` (to convert
`IntegrableOn ... (s ×ˢ t) (volume.prod volume)` into `Integrable ... over
the restricted prod measure`), then `Integrable.integral_prod_left` to
project out the radial marginal, then `integral_const_mul` to refold the
inner θ-integral as `r * circleMeanSq f r`.
(b/c) `radial_integrableOn_circleMeanSq_mul_r_Ioc` and
`radial_integrableOn_circleMeanSq_mul_r_Ioo` — restrict the marginal to
the inner half `Ioc 0 c` and outer half `Ioo c 1` via `IntegrableOn.mono_set`,
then swap the multiplication order via `mul_comm` to match the consumer's
`circleMeanSq f r * r` integrand. The set-restriction `Ioc 0 c ⊆ Ioo 0 1`
takes `0 < r ≤ c < 1`; the boundary at `r = c` does not complicate
measurability since `Ioc` is the `Ioo`-relevant left-open form already.
(d) `circle_integrableOn_normSq_polar_Ioo_ae` — per-radius circle
integrability in `∀ᵐ` form. Via `Integrable.prod_right_ae` on the
restricted prod measure, the slice `θ ↦ r * ‖f (symm (r,θ))‖²` is
integrable on `Ioo (-π) π` for almost every `r ∈ Ioo 0 1`.
`ae_restrict_of_ae_restrict_of_subset` shrinks the `∀ᵐ` to `Ioo c 1 ⊆
Ioo 0 1`; for `r ∈ Ioo c 1`, `r > c > 0` and `r ≠ 0`, so
`integrable_fun_smul_iff` divides through by the `r`-prefactor (after
rewriting `r * x = r • x` via `smul_eq_mul`) to extract the slice
integrability of `θ ↦ ‖f (symm (r,θ))‖²`.

The per-radius circle integrability comes out in `∀ᵐ` form rather than
pointwise. The cause is structural: `Integrable.prod_right_ae` only
commits to almost-every-r slice integrability — there is no pointwise
counterpart. Both routes were considered; the `∀ᵐ` route is the only one
Mathlib gives directly without an additional analyticity argument.

`Proof/CleanConditional.lean` exposes two theorems:
(a) `validKorenblum_of_innerCircleMean_dom_ae` — the `∀ᵐ`-variant of
sprint 005's conditional reduction. Same statement and proof structure
except the outer half closes via `setIntegral_mono_ae_restrict` (taking
`f ≤ᵐ[μ.restrict s] g`) rather than `setIntegral_mono_on` (taking
`∀ x ∈ s, f x ≤ g x`). The `≤ᵐ[μ.restrict s]` is constructed via
`filter_upwards [hf_circle_ae, hg_circle_ae, ae_restrict_mem
measurableSet_Ioo]` followed by the same per-r dominance step
(`circleMeanSq_le_of_outerAnnulus_dom` plus `mul_le_mul_of_nonneg_right`)
that the original used pointwise. The original
`validKorenblum_of_innerCircleMean_dom` in `Proof/RadialSplit.lean` is
not edited; the `_ae`-variant lives in `Proof/CleanConditional.lean`.
(b) `validKorenblum_of_inner_outer_dom_of_analyticOn` — the headline
clean conditional Korenblum reduction with `ValidKorenblumBound`-contract-
shaped hypotheses (`AnalyticOn`, `Integrable (‖·‖²) (volume.restrict
UnitDisk)`, `h_inner` for inner-half radial dominance, `h_outer` for
outer-annulus pointwise dominance). The proof composes
`polar_integrableOn_of_analyticOn_of_bergmanIntegrable` (sprint 012)
twice (once for `f`, once for `g`), the four radial integrability bridges
(a)/(b)/(c) twice, the two `∀ᵐ`-form per-radius circle integrability
bridges (d) twice, and finally `validKorenblum_of_innerCircleMean_dom_ae`.

One Mathlib-name note for future planners. (a) `integral_mul_left` does
not exist; the right-direction lemma is `integral_const_mul`, with
statement `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ`. (b) `setIntegral_mono_on_ae`
takes `∀ᵐ x ∂μ, x ∈ s → f x ≤ g x` (without the `restrict`), which
unifies awkwardly with `∀ᵐ x ∂(μ.restrict s)` after `filter_upwards`
through `ae_restrict_mem`. The cleaner route is
`setIntegral_mono_ae_restrict`, which takes the `≤ᵐ[μ.restrict s]` form
directly and pairs naturally with `filter_upwards` over the restricted
ae filter. (c) The `r * x = r • x` for real `x` rewrite uses `smul_eq_mul
(a := r) (b := _)` (with `(b := _)`); the bare `smul_eq_mul` does not
unify the implicit `b`.

V13 ships with `c_value = 3554/10000` unchanged from V12; the sprint is
scaffolding-only and adds the radial / per-θ integrability bridges plus
the headline clean conditional Korenblum reduction. After this sprint,
every remaining gap to a c-push attempt is *mathematical content*, not
Lean plumbing. The genuine c-push (the inner-half radial dominance
hypothesis `h_inner`, which is the Korenblum/Hayman/Wang extremal-function
chain) remains the next sprint's content.

### 2026-05-07 sprint_015

Built `Proof/AnnulusBergmanParseval.lean` against Mathlib and the existing
`Proof/RadialBergman.lean` (sprint 003), `Proof/CircleMeanRadial.lean`
(sprint 010), and `Proof/BergmanParseval.lean` (sprint 011). Four theorems
shipped, all `theorem`s, no `axiom`, no `sorry`. (1)
`outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries` — the outer-annulus
Bergman A² Parseval expansion: `∫ z in outerAnnulus c, ‖f‖² = ∑' k,
(π/(k+1)) (1 - c^(2k+2)) ‖a_k‖²`. (2)
`innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries` — the inner-disk
analogue: `∫ z in innerDisk c, ‖f‖² = ∑' k, (π/(k+1)) c^(2k+2) ‖a_k‖²`.
(3) `outerAnnulus_bergmanNormSq_termwise_mono` and (4)
`innerDisk_bergmanNormSq_termwise_mono` — the two cross-function
half-disc termwise comparison consumers, applying the corresponding
Parseval expansion to both sides and concluding via `tsum_le_tsum`.

The proof structure mirrors sprint 011's whole-disc Parseval identity
exactly, with two surface deltas: (a) replace `bergmanNormSq_radial_polar`
(sprint 003 whole-disc) with `outerAnnulus_norm_sq_polar` /
`innerDisk_norm_sq_polar` (sprint 003 half-disc), and (b) replace the
per-term integral `∫ r ∈ Ioo 0 1, r^(2k+1) dr = 1/(2k+2)` with the
half-interval evaluations `∫ r ∈ Ioo c 1, r^(2k+1) dr =
(1 - c^(2k+2))/(2k+2)` and `∫ r ∈ Ioc 0 c, r^(2k+1) dr = c^(2k+2)/(2k+2)`.
Both half-interval integrals are obtained via `integral_Ioc_eq_integral_Ioo`
(or directly `Ioc`), `intervalIntegral.integral_of_le`, and
`intervalIntegral.integral_pow`, followed by `push_cast; field_simp; ring`
to collapse `1/(2k+2)` against the `2π` prefactor into `π/(k+1)`.

Three Mathlib-name notes for future planners. (a) The pointwise identity
`c ^ (2*k+1+1) = c ^ (2*k+2)` is `rfl` (the two ℕ exponents are
definitionally equal). The earlier attempt `congr 1; ring` produces
"No goals to be solved" because `congr 1` already closes via `rfl`.
(b) `MeasureTheory.Measure.restrict_Ioo_eq_restrict_Ioc` is the wrong
namespace; the actual name is `MeasureTheory.restrict_Ioo_eq_restrict_Ioc`
(no `.Measure`), and it lives in
`Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean`. (c) For the
inner half, the contract specifies the polar integrability hypothesis on
`Ioo 0 c ×ˢ Ioo (-π) π` (open form) but `innerDisk_norm_sq_polar` (sprint
003) takes the hypothesis on `Ioc 0 c ×ˢ Ioo (-π) π` (half-open). The
bridge is `Measure.restrict_Ioo_eq_restrict_Ioc` (the boundary point
`r = c` has measure zero), threaded through `Measure.prod_restrict` to
push the rewrite from the 1D restrict to the 2D product.

A genuinely tricky step was the per-`r` summability of `halfRadialTerm a k r`
for the partial-sum-≤-tsum bound. Sprint 011's `summable_canonical_parseval_terms`
is `private`, so we re-derive directly via the same shorter
`FormalMultilinearSeries.summable_norm_mul_pow` route: pick `R'(r) :=
⟨(r+1)/2, _⟩`, get `Summable (fun n => ‖p n‖ * r^n)` from radius
convergence, square via `Summable.of_norm_bounded_eventually_nat` (eventually
the summand is ≤ 1 so squared ≤ unsquared), and canonicalise coefficient
norms via `cauchyPowerSeries_coeff_norm_radius_invariant` (sprint 011's (1)).

The integrability of `r ↦ circleMeanSq f r * r` on `Ioo c 1` (outer) and
`Ioc 0 c` (inner) comes from polar integrability via `Measure.prod_restrict`
plus `Integrable.integral_prod_left`, paralleling sprint 011's
`integrableOn_circleMeanSq_mul_radius` but with the radial domain
restricted. For the inner half, the `Ioo 0 c → Ioc 0 c` bridge happens
inside this lemma.

V15 ships with `c_value = 3554/10000` unchanged from V14; the sprint is
scaffolding-only and adds the half-disc Bergman A² Parseval expansions in
`Proof/AnnulusBergmanParseval.lean`. With these in place, every future
c-push consumer can compare half-disc Bergman norms at the
*c-dependent* coefficient level — the missing primitive that sprint 011's
whole-disc Parseval (which loses `c`-dependence by definition) does not
provide. The four theorem statements are internally consistent with
sprint 011's whole-disc identity via `(1 - c^(2k+2)) + c^(2k+2) = 1`
termwise: their `tsum`s sum to sprint 011's whole-disc `tsum`, matching
the `setIntegral_union` of sprint 002 (`bergmanNormSq_split`).

Note on the c-push next step. The inner-half termwise consumer
(`innerDisk_bergmanNormSq_termwise_mono`) provides a *c-dependent
weighted termwise* path from coefficient-norm dominance to inner-disk
Bergman dominance, with weights `(π/(k+1)) c^(2k+2)`. The genuine c-push
still requires bridging the contract's outer-annulus pointwise dominance
to coefficient-norm dominance. As documented in sprint 011, this is
*not* a tautology (counterexample `f = z, g = 1`), so the bridge needs
either subharmonic mean-value arguments, a Carleman / Hardy-style
boundary-integral refinement, or a Möbius / pseudohyperbolic
construction. None of these is shipped here; this sprint pins the
half-disc Parseval primitive every such bridge must factor through.

### 2026-05-07 sprint_016

Built `Proof/CircleMeanLogConvex.lean` against Mathlib: pinned the
**Hadamard three-circles theorem** for the A² circle mean of an analytic
function on the unit disk, in two forms.

(1) `circleMeanSq_geometric_mean_le` (the headline, Cauchy–Schwarz / `a = 1/2`
case): for `f : ℂ → ℂ` analytic on `UnitDisk` and `r₁, r₂ ∈ (0, 1)`,
`circleMeanSq f (√(r₁ r₂))^2 ≤ circleMeanSq f r₁ · circleMeanSq f r₂`.

(2) `circleMeanSq_log_convex` (the general Hölder / `a ∈ [0, 1]` form):
for `f : ℂ → ℂ` analytic on `UnitDisk`, `r₁, r₂ ∈ (0, 1)`, and `a ∈ [0, 1]`,
`circleMeanSq f (r₁^a · r₂^(1-a)) ≤ circleMeanSq f r₁ ^ a · circleMeanSq f r₂ ^ (1-a)`.
Endpoint cases `a = 0` and `a = 1` were handled with a direct `rcases
eq_or_lt_of_le` plus `Real.rpow_zero`/`Real.rpow_one`/`one_mul`/`mul_one`
collapse.

Both forms factor through sprint 010's canonical-witness Parseval identity
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` to expand
each radius's `circleMeanSq` as `2π · ∑' k, ‖a_k‖² · r^(2k)`, then apply
Mathlib's `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` for the discrete Hölder
inequality on the counting measure. The Cauchy–Schwarz case uses
`Real.HolderConjugate.two_two`; the general Hölder case constructs
`Real.HolderConjugate (1/a) (1/(1-a))` via `Real.holderConjugate_iff`,
`one_lt_inv₀`, and an inverse-arithmetic computation.

The summability of `‖(cauchyPowerSeries f 0 R).coeff k‖² · r^(2k)` was
re-derived inline in this file (mirroring `summable_halfRadialTerm_at`
from `AnnulusBergmanParseval.lean`, which is `private`): from radius
convergence get `Summable (fun n => ‖p n‖ · r^n)` via
`FormalMultilinearSeries.summable_norm_mul_pow`, square via
`Summable.of_norm_bounded_eventually_nat` (eventually the summand is ≤ 1
so squared ≤ unsquared), and canonicalise coefficient norms via sprint
011's `cauchyPowerSeries_coeff_norm_radius_invariant`. The same
helper was also used to discharge summability at the geometric-mean
radius `√(r₁ r₂)` — the canonical-witness lemma's hypothesis only
requires `√(r₁ r₂) < (R : ℝ)`, which follows from
`Real.sqrt_le_sqrt (mul_le_mul ...)` plus `Real.sqrt_sq` for
`r₁ r₂ ≤ (max r₁ r₂)²`.

Two minor pitfalls: (a) `Real.rpow_two` rewrites `x ^ (2 : ℝ) = x ^ 2`,
but `pow_le_pow_left₀` takes a `Nat`-power argument, so the squared
Hölder inequality's RHS `((u_sum)^(1/2) * (v_sum)^(1/2))^2` had to be
collapsed via `rpow_natCast` plus `← Real.rpow_mul` to get
`(u_sum)^((1/2)*2) = u_sum`. (b) The general Hölder form's tsum-shape
identity `(‖a_k‖² · r₁^(2k))^a · (‖a_k‖² · r₂^(2k))^(1-a)
  = ‖a_k‖² · (r₁^a · r₂^(1-a))^(2k)` requires a precise interleaving of
`Real.mul_rpow`, `Real.rpow_natCast`, and `Real.rpow_mul`; the
`(2k : ℕ)` casts to `ℝ` get juggled across `Real.rpow_natCast`. Solved
by collecting the per-side rpow identities first, then a single `ring`
to commute the four terms before applying the `(‖a‖²)^a · (‖a‖²)^(1-a) =
‖a‖²` collapse.

The proof did *not* rely on any single-function radial-monotonicity
results from sprint 010 (`circleMeanSq_radial_mono`), nor on the
half-disc Parseval expansions from sprint 015 — both forms are
self-contained against sprint 010's canonical-witness identity plus
Mathlib's tsum-level Hölder. The geometric-mean form is internally
consistent with `circleMeanSq_radial_mono`: setting `r₁ = r, r₂ = r' ≥ r`
gives `circleMeanSq f (√(r·r'))² ≤ circleMeanSq f r · circleMeanSq f r'`,
and combined with monotonicity at the geometric mean recovers a slightly
weaker form of monotonicity (the consistency check is not shipped as a
theorem but is structurally enforced).

V16 ships with `c_value = 3554/10000` unchanged from V15; the sprint is
scaffolding-only and adds the Hadamard three-circles primitive in
`Proof/CircleMeanLogConvex.lean`. With this in place, any future
c-push consumer that wants to bound `circleMeanSq f` at an interior
radius `r` from values at `r₁ < r < r₂` (e.g., a Hayman-style extremal-
function argument bounding the worst-case radial transport from outer
to inner half-disc) can factor through the Hadamard inequality, which
is the natural single-function Hardy-class primitive. This is
the strongest single-function, multi-radius bound Mathlib pins for
analytic Bergman A².

### 2026-05-07 sprint_018

Built `Proof/SubMeanValue.lean` against Mathlib and the existing
sprint 011 / 010 stack: the Bergman A² **sub-mean-value inequality at
the origin**, `π · ‖f(0)‖² ≤ bergmanNormSq f` for `f` analytic and
A²-integrable on `UnitDisk`. Proof follows the contract's outline
verbatim: at helper radius `R := 1/2`, sprint 011's
`bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
rewrites `bergmanNormSq f = ∑' k, (π/(k+1)) · ‖a_k‖²`; the `k = 0`
summand `π · ‖a_0‖²` is extracted via `Summable.le_tsum` against the
non-negative termwise bound; and the `a_0 = f 0` identification is
discharged by unfolding `FormalMultilinearSeries.coeff` to
`p 0 (fun _ => 1)` and applying `HasFPowerSeriesAt.coeff_zero`
(`hf_diff.hasFPowerSeriesOnBall hR_pos |>.hasFPowerSeriesAt`), which
gives `p 0 v = f 0` for any `v : Fin 0 → ℂ`. The whole derivation runs
in roughly ~480 lines.

Summability of `fun k => (π/(k+1)) · ‖(cps R).coeff k‖²` was the only
non-trivial sub-step. The sprint 011 identity gives `bergmanNormSq f
= ∑' k, ...` but this is a `=`, and Mathlib's tsum convention returns
0 for non-summable series, so the equality alone does not let one
conclude summability. Resolved by `summable_of_sum_range_le` against
bound `bergmanNormSq f`, with the per-`N` partial-sum bound
`∑ k ∈ range N, (π/(k+1)) ‖a k‖² ≤ bergmanNormSq f` re-derived inline.
The inline proof mirrors the structure of sprint 011's
`bergmanNormSq_termwise_mono` (which was inaccessible via private
helpers): rewrite the partial sum as `∫ r, ∑ k ∈ range N, (2π · ‖a k‖²)
r^(2k+1) dr`, factor `r` outside, bound the inner partial sum by the
tsum (which equals `circleMeanSq f r` by sprint 010's per-`r`
identity, with radius-invariance of coefficient norms bridging the
helper radius `R'(r) := (r+1)/2` back to `R`), then integrate against
`bergmanNormSq_radial_polar`. Per-`r` summability was re-derived
inline via `FormalMultilinearSeries.summable_norm_mul_pow`,
`Summable.of_norm_bounded_eventually_nat`, and the radius-invariance
identity. (This re-derivation is allowed: sprint 011's helper
`summable_canonical_parseval_terms` is `private` to that module.)

Two pitfalls discovered. (a) `bergmanNormSq f = ∑' k, ...` from
sprint 011 plus `Summable.sum_le_tsum` requires summability *as a
hypothesis* — Mathlib's tsum convention sets non-summable tsums to 0,
so the identity itself does not certify summability. The contract
sketch via `Summable.of_nonneg_of_le` against the tsum bound is
circular; a partial-sum bound argument is the only honest route. (b)
The `(cauchyPowerSeries f 0 R).coeff 0 = f 0` identification has a
small definitional unfolding step: `coeff 0 := p 0 1` unfolds to `p 0
(fun _ => (1 : ℂ))`, which is then `HasFPowerSeriesAt.coeff_zero`'s
conclusion at any `v : Fin 0 → ℂ`. Just `change` to expose the form.

**Theorem (2) `normSq_pointwise_le_ball_integral` — deferred per
Fallback A.** Theorem (1) shipped clean. Theorem (2) (the general-
interior-point form) was deferred. The sprint contract permits this
fallback and explicitly notes the change-of-variables step (Jacobian
`R²` plus translation invariance) as the trickiest part. Concretely,
the bookkeeping for theorem (2) requires:

  (i) Define `g w := f (R • w + z₀)` for `w ∈ UnitDisk` and verify
  `AnalyticOn ℂ g UnitDisk` via composition (`hf.comp` with the
  affine map's analyticity, plus a subset hypothesis from
  `R + ‖z₀‖ < 1`).

  (ii) Polar-integrability of `g` (i.e., `IntegrableOn (fun p => p.1 *
  ‖g (polarCoord.symm p)‖²) (Ioo 0 1 ×ˢ Ioo (-π) π) (vol.prod vol)`).
  The cleanest path is via continuity-on-compact, but the workspace
  has no clean primitive `polar_integrableOn_of_analyticOn_of_…`.

  (iii) Apply theorem (1) to `g` to get `π · ‖g 0‖² ≤ bergmanNormSq g`.

  (iv) Push `bergmanNormSq g` through the affine change-of-variables
  to `R⁻² · ∫ z in ball z₀ R, ‖f z‖²`. The Jacobian is `R²`. Mathlib
  primitives in scope: `MeasureTheory.Measure.map_add_right` for the
  translation, `MeasureTheory.Measure.map_smul` /
  `Complex.integral_comp_mul_left` for the scaling. The composition
  is non-trivial (multiple measure manipulations on `ℂ`'s
  Lebesgue-on-ℝ² structure) and was assessed as ~150 additional
  lines, blowing the time budget.

The deferral is per-contract (Fallback A) and is recorded here for the
follow-up sprint planner.

**Why theorem (1) is the right scaffolding to ship now.** Theorem (1)
(origin form) is the analytic primitive: pointwise control on `‖f(z)‖²`
from integrated control on `‖f‖²` in a neighborhood. Theorem (2) (general
interior point) is just translation+scaling of theorem (1). Future
c-push consumers will need both, but the analytic content is in (1) —
a follow-up sprint can ship (2) by composing theorem (1) with the
change-of-variables step now that (1) is pinned and reusable.

V18 ships with `c_value = 3554/10000` unchanged from V17. Score
unchanged; the sprint is scaffolding-only.

### 2026-05-07 sprint_019

Built `Proof/CircleMeanContinuous.lean` against Mathlib and the existing
sprint 010 / 011 / 017 stack. Two theorems shipped, all `theorem`s, no
`axiom`, no `sorry`. (1) `continuousAt_circleMeanSq_of_analyticOn_unitDisk`
— for `f` analytic on `UnitDisk` and any `r₀ ∈ [0, 1)`, the function
`r ↦ circleMeanSq f r` is continuous at `r₀`. (2)
`cauchyPowerSeries_normSq_pow_at_boundary_le_circleMeanSq` — boundary form
of sprint 017's cross-function Cauchy L² estimate at the inner-disk-boundary
radius `r = c`.

Theorem (1) routes through sprint 010's
`circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`, picking
helper Cauchy-radius `R := ⟨(r₀+1)/2, _⟩` and M-test compact-set radius
`ρ := (r₀ + Rval)/2`. The Weierstrass M-bound is `‖a_k‖² · ρ^(2k)`,
summable by `summable_coeff_sq_pow_of_lt_one` (re-derived inline since
`summable_coeff_sq_pow` in `Proof/CauchyL2Estimate.lean` is private).
Mathlib's `continuousOn_tsum` (in
`Mathlib/Analysis/Normed/Group/FunctionSeries.lean`) then gives
`ContinuousOn g (Set.Icc 0 ρ)` for the tsum function `g r := ∑' k, (2π ·
r^(2k)) · ‖a_k‖²`. The bridge `circleMeanSq f r = g r` for `r ∈ [0, ρ]`
is the Parseval identity itself.

Two cases handled separately:

- **For `r₀ > 0`**: pick the open neighborhood `Set.Ioo (r₀/2) ρ ⊆
  Set.Icc 0 ρ`. On this open set, `circleMeanSq f =ᶠ[𝓝 r₀] g`, so
  `ContinuousAt circleMeanSq f r₀ ↔ ContinuousAt g r₀` via Mathlib's
  `continuousAt_congr`. The latter follows from `ContinuousOn.continuousAt`
  with the open subset's membership in `𝓝 r₀`.

- **For `r₀ = 0`**: this is the boundary case where `Set.Icc 0 ρ` is not
  a 𝓝-neighborhood of `0` in ℝ. Resolved by proving the symmetry
  `circleMeanSq f r = circleMeanSq f |r|` via a private lemma
  `circleMeanSq_neg`. The proof uses (a) the polar identity
  `polarCoord.symm (-r, θ) = polarCoord.symm (r, θ + π)` (from
  `Complex.exp_pi_mul_I = -1` and the `polarCoord_symm_eq_exp` bridge of
  sprint 006), (b) the `intervalIntegral` substitution
  `intervalIntegral.integral_comp_add_right` to shift the integration
  variable by π, and (c) `Function.Periodic.intervalIntegral_add_eq` on
  the `2π`-periodic integrand `θ ↦ ‖f(polarCoord.symm (r, θ))‖²` to slide
  the integration interval from `[0, 2π]` back to `[-π, π]`. With
  symmetry in hand, continuity at 0 reduces to right-continuity at 0
  (which `ContinuousOn (Set.Icc 0 ρ)` provides) plus continuity of `|·|`.

Theorem (2) is a sequential-limit composition. Pick `r_n := c + (1 - c)
/(n + 2)`, prove `r_n ∈ Ioo c 1` and `r_n → c` (the latter via
`tendsto_natCast_atTop_atTop.atTop_add` and `Tendsto.inv_tendsto_atTop`,
then `Tendsto.const_mul`). At each `r_n`, sprint 017's
`cauchyPowerSeries_normSq_pow_le_outer_circleMeanSq` gives `(2π) · ‖a_k‖²
· r_n^(2k) ≤ circleMeanSq g r_n`. Pass to the limit: LHS tends to `(2π)
· ‖a_k‖² · c^(2k)` via `Tendsto.pow` then `Tendsto.const_mul`; RHS tends
to `circleMeanSq g c` via theorem (1) above (continuity at `c`).
`le_of_tendsto_of_tendsto'` closes the inequality at the limit.

Two Mathlib-name notes for future planners. (a) `continuousOn_tsum` lives
in `Mathlib/Analysis/Normed/Group/FunctionSeries.lean` (not the older
`NormedSpace/FunctionSeries.lean` which is now a deprecated shim). It
takes the standard Weierstrass M-bound `∀ n x, x ∈ s → ‖f n x‖ ≤ u n`
plus `Summable u`, and concludes `ContinuousOn (fun x => ∑' n, f n x) s`.
(b) `continuousAt_congr` in `Mathlib/Topology/Continuous.lean` is the
right name for the EventuallyEq-bridge (not
`Filter.EventuallyEq.continuousAt_iff`, which does not exist as a direct
lemma).

Three pitfalls discovered. (a) `Complex.exp_add` only fires when the
argument is *literally* `?x + ?y`; `(θ + π) * I` does not match unless
the multiplication is distributed first. Resolved with an explicit
`have h_split : ((θ + π) * I) = (θ * I) + (π * I) := by ring` rewrite
before the `exp_add` rewrite. (b) `intervalIntegral.integral_comp_add_right
g π` produces bounds `(-π + π)..(π + π)`, which Lean simplifies to
`0..(π * 2)` (not `2 * π`). The fix is to keep the bounds in their
unsimplified form via local `have h_bound1 : -π + π = 0` and
`h_bound2 : π + π = 2 * π` rewrites, then re-apply periodicity in the
right direction. (c) The Mathlib search hit on `le_or_lt` is not in
this toolchain; the correct name is `le_or_gt` (the `gt` form).

Three pitfalls in the second theorem. (a) `Tendsto.inv_tendsto_atTop` is
the right name for `(n : ℝ) + 2 → ∞` ⇒ `((n : ℝ) + 2)⁻¹ → 0`, not
`Filter.Tendsto.div_atTop_const` from the contract sketch. (b)
`tendsto_natCast_atTop_atTop` is the right form for the `ℕ → ℝ` cast,
giving `Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop`. (c) The
`le_of_tendsto_of_tendsto'` consumer (with the `≤` for *every* `n`, not
just eventually) is the cleanest closer; the `Filter.Tendsto.le_of_le`
variant requires a `Filter.Eventually` hypothesis.

V19 ships with `c_value = 3554/10000` unchanged from V18; the sprint is
scaffolding-only and adds the **boundary coefficient bound** primitive in
`Proof/CircleMeanContinuous.lean`. With this in place, every future
c-push consumer can compare a Cauchy coefficient `‖a_k(f)‖² · c^(2k)`
against the boundary circle mean `circleMeanSq g c` of the larger
function — the missing primitive that sprint 017's outer-radius bound
(strictly inside `(c, 1)`) does not provide. The continuity primitive
`continuousAt_circleMeanSq_of_analyticOn_unitDisk` is itself reusable
for any future "`r ↘ c`" or "`r ↗ c`" passage, beyond the boundary
Cauchy L² consumer.

### 2026-05-07 sprint_020

Built `Proof/MobiusDisk.lean` pinning the five core algebraic / analytic
primitives for the unit-disk Möbius automorphism
`φ_a(z) = (a - z) / (1 - conj(a) · z)` against the workspace's set-level
`UnitDisk : Set ℂ`: (1) denominator non-vanishing on the closed unit disk
for interior `a` via reverse triangle inequality; (2) the Schwarz–Pick
algebraic identity `1 - ‖φ_a z‖² = (1 - ‖a‖²)(1 - ‖z‖²) / ‖1 - conj(a)z‖²`
via `Complex.normSq_sub` expansion plus a `field_simp` / `ring` chain;
(3) `φ_a : UnitDisk → UnitDisk` self-map as a strict consequence of (2);
(4) `φ_a ∘ φ_a = id` involution via explicit numerator/denominator
re-expression over the inner `D = 1 - conj(a) z`, then
`div_div_div_cancel_right₀` to cancel `D`; (5) `AnalyticOn ℂ (mobiusDisk a)
UnitDisk` via `AnalyticOn.div` of the polynomial numerator and denominator,
with non-vanishing from (1).

Three pitfalls. (a) Inside the file the bare identifier `conj` is unknown
because the workspace's other modules use the elaborated `(starRingEnd ℂ)`
spelling and don't open the `Complex` `conj` namespace globally — one
either has to `open Complex` for `conj`, or use `(starRingEnd ℂ)`
uniformly. The file uses `(starRingEnd ℂ)` to match the existing
workspace convention. (b) After `Complex.normSq_sub` expansion of
`normSq (1 - conj(a) z)` and `normSq (a - z)`, `field_simp` clears the
fraction over `normSq D` but the resulting goal still references
`normSq D` (because `D` was introduced by `set`); the fix is to rewrite
`normSq D` via the expanded form `1 + normSq a · normSq z - 2 (a · conj z).re`
**before** running `field_simp`, so that `ring` finishes the algebra over
already-expanded forms. (c) For the involution, plain `field_simp` after
`unfold mobiusDisk` does *not* close the goal because it cannot simplify
the outer denominator `1 - conj(a) · ((a-z)/D)` to `(D - conj(a)(a-z))/D`
without the cancellation step being explicit. The fix is to manually
re-express numerator and denominator as fractions over `D`, then apply
`div_div_div_cancel_right₀ hD_ne` to cancel the inner `D`, then expand
`aD - (a-z) = z(1 - a · conj(a))` and `D - conj(a)(a-z) = 1 - a · conj(a)`
via `ring`, then close with `mul_div_cancel_right₀` using the auxiliary
`(1 - a · conj(a)) ≠ 0` (which itself follows from `‖a‖² < 1` via
`Complex.sq_norm` and `normSq_eq_conj_mul_self`).

V20 ships with `c_value = 3554/10000` unchanged from V19; the sprint is
scaffolding-only and adds the Möbius unit-disk automorphism primitives.
The five theorems are the natural minimum surface for any downstream
Schwarz–Pick / pseudohyperbolic-distance / Bergman-A² conformal-invariance
argument. The next natural sprint is the Jacobian identity
`|φ_a'(z)|² = (1 - ‖a‖²)² / ‖1 - conj(a)z‖^4` (which together with
change-of-variables yields Bergman A² conformal invariance), or the
maximum-modulus-principle-based Schwarz–Pick lemma on top of these
primitives.

### 2026-05-07 sprint_021

Built `Proof/MobiusDeriv.lean` against Mathlib + sprint 020's
`Proof/MobiusDisk.lean`: three theorems pinning the analytic derivative
of the Möbius automorphism `φ_a` plus its modulus identity (the positive
real Jacobian factor for any Bergman A² change-of-variables under `φ_a`).
(1) `hasDerivAt_mobiusDisk` is a direct quotient-rule application:
`HasDerivAt (fun w => a - w) (-1) z` (via `(hasDerivAt_id z).const_sub a`),
`HasDerivAt (fun w => 1 - conj(a) * w) (-(conj(a))) z` (via
`(hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)` then `.const_sub 1`),
plus sprint 020's `mobiusDisk_denom_ne_zero` for non-vanishing, then
`HasDerivAt.div`. The quotient-rule output
`((-1)·D - (a-z)·(-conj(a))) / D²` simplifies to
`-(1 - conj(a)·a) / D²` via `field_simp` + `ring` (on the explicit
equality of derivative values, not via `convert`). (2)
`norm_sq_deriv_mobiusDisk` reduces the modulus identity to a positive
real arithmetic identity via `Complex.mul_conj` (`a * conj a =
↑(normSq a)`, applied with `mul_comm` to get `conj a * a`),
`Complex.sq_norm` (`normSq a = ‖a‖²`), `Complex.norm_real` +
`abs_of_nonneg` (since `1 - ‖a‖² ≥ 0` from `‖a‖ < 1`), then `norm_div`
+ `norm_pow` + `div_pow` to push `‖num/denom²‖²` through to
`‖num‖²/‖denom‖⁴`. (3) `deriv_mobiusDisk` is a one-liner via
`HasDerivAt.deriv`. Friction-free build: the planner's first-pass spec
worked without falling back to Fallbacks A/B/C. Useful primitive APIs
discovered: `(hasDerivAt_id z).const_sub a` and
`(hasDerivAt_id z).const_mul c` need a `simpa` to reshape the resulting
function from `fun w => a - id w` to `fun w => a - w`, and
`Complex.mul_conj` returns `a * conj a = ↑(normSq a)` (the `mul_comm`
direction is the natural one for the identity `conj a * a = ‖a‖²`).

V21 ships with `c_value = 3554/10000` unchanged from V20; the sprint is
scaffolding-only and adds the Möbius derivative + Jacobian-modulus
primitives. The next natural sprint is the measure-theoretic
change-of-variables on `φ_a` (Bergman A² conformal invariance:
`bergmanNormSq (f ∘ φ_a) = bergmanNormSq f` via
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` plus
sprint 020's `mobiusDisk_involution` + `mobiusDisk_mapsTo` to identify
`φ_a '' UnitDisk = UnitDisk`), which directly composes this sprint's
output with the existing involution/maps-to primitives.
