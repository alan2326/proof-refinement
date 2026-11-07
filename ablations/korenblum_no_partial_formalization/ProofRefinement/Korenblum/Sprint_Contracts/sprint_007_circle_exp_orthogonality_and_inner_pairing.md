# Sprint 007: `Complex.exp(ikθ)` orthogonality + monomial circle-mean inner-product pairing

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V6.lean`
**Target file**: `Candidates/V7.lean`
**Direction**: section2-proof (Bergman scaffolding — first off-diagonal piece of Bergman-Parseval)

## Goal

Open the door to **Bergman-A² Parseval / monomial decomposition** by proving
the missing off-diagonal ingredient that sprint 006 deferred: the
`Complex.exp(ikθ)` orthogonality identity on `Ioo (-π) π`, and use it to
build the monomial circle-mean cross-pairing identities. Concretely, in a
new file `Proof/CircleInnerProduct.lean`, expose:

1. **`integral_exp_int_mul_theta_zero`** — for any nonzero `k : ℤ`,

   ```
   ∫ θ in Ioo (-Real.pi) Real.pi,
       Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) = 0
   ```

2. **`integral_exp_int_mul_theta_eq_two_pi`** — for `k = 0` (or as a
   `k = 0`-case companion to (1)),

   ```
   ∫ θ in Ioo (-Real.pi) Real.pi,
       Complex.exp ((0 : ℂ) * (θ : ℂ) * Complex.I) = (2 * Real.pi : ℂ)
   ```

3. **`circleMeanInner` definition** — a `ℂ`-valued sesquilinear circle
   pairing,

   ```
   noncomputable def circleMeanInner (f g : ℂ → ℂ) (r : ℝ) : ℂ :=
     ∫ θ in Ioo (-Real.pi) Real.pi,
       starRingEnd ℂ (f (Complex.polarCoord.symm (r, θ)))
         * g (Complex.polarCoord.symm (r, θ))
   ```

   (the convention is conjugate-linear in `f`, linear in `g`; either
   convention is acceptable as long as it is consistent through the
   sprint's lemmas.)

4. **`circleMeanInner_monomial_diff`** — for `m, n : ℕ` with `m ≠ n` and
   any `r : ℝ`,

   ```
   circleMeanInner (fun z => z ^ m) (fun z => z ^ n) r = 0
   ```

   The headline orthogonality identity. Proof outline: use
   `polarCoord_symm_eq_exp` (sprint 006) to rewrite
   `polarCoord.symm (r,θ) = r · exp(iθ)`; expand
   `conj(z^m) · z^n = r^{m+n} · exp(i(n-m)θ)`; pull `r^{m+n}` out via
   `integral_const_mul`; close via (1) with `k = (n : ℤ) - (m : ℤ) ≠ 0`.

5. **`circleMeanInner_monomial_same`** — for `n : ℕ` and `r : ℝ`,

   ```
   circleMeanInner (fun z => z ^ n) (fun z => z ^ n) r
     = ((2 * Real.pi : ℝ) * (r ^ (2 * n) : ℝ) : ℂ)
   ```

   The diagonal companion. Proof outline: as in (4), but with
   `m = n` so the `exp` exponent vanishes and the integrand reduces to
   the constant `r^(2n)`; close via (2) (or directly via
   `setIntegral_const` + `Real.volume_real_Ioo_of_le`).

6. **`circleMeanSq_eq_re_circleMeanInner_self`** — the bridge tying the
   new `ℂ`-valued pairing to the existing `ℝ`-valued `circleMeanSq`:

   ```
   ∀ (f : ℂ → ℂ) (r : ℝ),
     circleMeanSq f r = (circleMeanInner f f r).re
   ```

   (or an equivalent form; e.g. `circleMeanSq f r = ((...).re : ℝ)`
   modulo coercion plumbing). Proof outline: pointwise
   `conj(z) · z = ‖z‖²` (via `Complex.mul_conj` or
   `Complex.normSq_eq_abs`-family lemmas), then `.re` of a real-valued
   complex integrand commutes with the integral (via
   `Complex.re_integral` / `MeasureTheory.integral_re`).

V7 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V6
and the only seed axiom is still `hKorenblum_published_3554`. The
contribution is the new derived module, which finally gives the workspace
**both diagonal and off-diagonal** monomial circle-mean identities. After
this sprint, the polynomial Parseval identity (`circleMeanSq (∑_k a_k
z^k) r = 2π · ∑_k ‖a_k‖² · r^(2k)`) becomes a single follow-up sprint:
expand `‖∑ a_k z^k‖² = (∑ conj(a_m) z^m)(∑ a_n z^n) = ∑ conj(a_m) a_n
z^m conj(z)^n`, integrate termwise, kill cross terms via (4), keep
diagonal via (5) and (6).

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- After sprints 001–006, the radial scaffolding is complete at the
  bookkeeping level (polar pull-back, set split, radial polar form on
  each half, outer-annulus circle-mean comparison, radial integral
  split, conditional Korenblum reduction) and the **diagonal** monomial
  circle-mean identity is in place (`circleMeanSq_monomial`,
  `circleMeanSq_const`, `circleMeanSq_smul`). The single missing
  scaffolding piece is the **off-diagonal** identity: the cross-pairing
  `circleMeanInner (z^m) (z^n) = 0` for `m ≠ n`.
- **Why this is the canonical next stone, not an inner-half attack.**
  Sprint 006 spelled out the obstruction explicitly (recorded in its
  `Why`): the inner-half radial dominance hypothesis taken by
  `validKorenblum_of_innerCircleMean_dom` (sprint 005) is **strictly
  stronger** than what Korenblum guarantees, so it cannot be proved
  pointwise from analyticity alone. The honest route forward is the
  Bergman-Parseval / monomial-decomposition direction, where
  `circleMeanSq f r` is exposed as `2π · ∑_k ‖a_k‖² · r^(2k)` for
  Taylor-decomposable `f`, after which the Korenblum inequality reduces
  to a coefficient-level termwise comparison. Sprint 006 provided the
  diagonal seed; sprint 007 provides the off-diagonal seed; the two
  together unlock the polynomial Parseval identity in one further
  sprint, and the `tsum`-level Parseval one sprint after that.
- **Why this and not the polynomial Parseval directly.** The polynomial
  Parseval `circleMeanSq (∑_{k≤N} a_k z^k) r = 2π ∑_{k≤N} ‖a_k‖² r^(2k)`
  is a four-stage Lean proof: (i) expand `‖∑ a_k z^k‖² = ∑∑ conj(a_m)
  a_n z^m (conj z)^n`, (ii) commute integration with `Finset.sum`, (iii)
  apply orthogonality `∫ ...= 0` for `m ≠ n`, (iv) collect diagonal
  terms. Stage (iii) requires the **off-diagonal orthogonality identity
  this sprint produces**. Without it, stage (iii) becomes a black box
  inside the polynomial Parseval sprint; with it pinned in
  `Proof/CircleInnerProduct.lean`, the polynomial Parseval sprint is a
  single Generator session of straight algebraic bookkeeping.
- **Mathlib has the right primitives.** Items (1)–(2) are essentially
  applications of `intervalIntegral.integral_exp` (when `c = (k : ℂ) *
  I` with `k ≠ 0`, the antiderivative is `exp(c·x)/c`, evaluated at
  `±π`, gives `(exp(ikπ) - exp(-ikπ))/(ik)`; for `k ∈ ℤ`,
  `exp(ikπ) = (-1)^k = exp(-ikπ)`, so the difference is zero). For the
  `Ioo`-vs-interval-integral bridge: `intervalIntegral.integral_of_le`
  plus `intervalIntegral.integral_Ioc` (or
  `MeasureTheory.integral_Ioc_eq_integral_Ioo` on the open vs
  half-open distinction; the integrand is continuous, so any of the
  `Ioo`/`Ioc`/`Icc`/`uIoc` shapes are interchangeable). Items (4)–(5)
  reduce to (1)–(2) plus `polarCoord_symm_eq_exp` (sprint 006) plus the
  identity `conj (r · exp(iθ))^m = r^m · exp(-imθ)` (one
  `Complex.exp_neg`/`star_exp`/`Complex.conj_exp` rewrite). Item (6) is
  pointwise `conj z · z = ‖z‖²` (Mathlib's `Complex.mul_conj`) plus
  `MeasureTheory.integral_re` to commute `.re` with the integral.
- **The proofs sit comfortably in the generator's declared scope.**
  Each item is a single chain of Mathlib rewrites with one or two
  algebraic gluing steps. No new analytic content is introduced; this
  is a Lean-side derivation of identities that are mathematically
  elementary. The hardest step is plumbing `Ioo` ↔ `intervalIntegral`
  for items (1)–(2); this is the same kind of plumbing the generator
  has already executed in sprints 003 and 006.
- **Falsifiable bottleneck.** If item (1) cannot be discharged because
  Mathlib does not expose `intervalIntegral.integral_exp` with a clean
  endpoint evaluation at `±π` for `k ∈ ℤ`, or because the bridge from
  `Ioo (-π) π` to `intervalIntegral` requires a measurability or
  integrability hypothesis the generator cannot produce, the
  `STATUS=BLOCKED` log will record exactly which Mathlib lemma is the
  obstruction. That bottleneck is the same one any future
  Bergman-Parseval attack would face, so the failure mode is
  informative.
- **Why this sprint and not a numerical-budget push at higher `c`.**
  The workspace has zero off-diagonal monomial identities. Without
  them, no polynomial Parseval can be assembled; without polynomial
  Parseval, no honest analytic attack on the inner half can compose.
  Filing a "push `c` from 0.3554 to 0.36" sprint at this stage would
  be premature — the analytic content does not yet exist in the Lean
  trust surface, and any direct attempt would need to either inline
  this orthogonality identity or postulate it.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleInnerProduct.lean`: **new file**,
  in the `ProofRefinement.Korenblum` namespace,
  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.RadialBergman`,
    `Proof.CircleExpBridge` (and **only** those workspace-side imports),
  - exposes (1) `integral_exp_int_mul_theta_zero`. Statement (or
    equivalent):

    ```lean
    theorem integral_exp_int_mul_theta_zero {k : ℤ} (hk : k ≠ 0) :
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)) = 0
    ```

    Proof outline: bridge `Ioo (-π) π` to `intervalIntegral` via
    `MeasureTheory.integral_Ioc_eq_integral_Ioo` (or directly via
    `intervalIntegral.integral_of_le`, since the integrand is
    continuous and the `Ioo`/`Ioc`/`Icc` integrals agree on
    continuous integrands); apply `intervalIntegral.integral_exp`
    (or its complex-coefficient companion) with `c = (k : ℂ) * I ≠ 0`
    (the nonzero hypothesis follows from `hk` and `Complex.I_ne_zero`);
    evaluate the antiderivative at `π` and `-π`; close via
    `Complex.exp_int_mul_pi_mul_I_eq_pow_neg_one` (or by using
    `Complex.exp_eq_one_iff` on `exp(2πik) = 1` with the difference
    being a multiple of `2πi`). The exact Mathlib lemma name is at
    the generator's discretion.

  - exposes (2) `integral_exp_int_mul_theta_eq_two_pi`. Statement (or
    equivalent):

    ```lean
    theorem integral_exp_int_mul_theta_eq_two_pi :
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
            Complex.exp ((0 : ℂ) * (θ : ℂ) * Complex.I))
          = (2 * Real.pi : ℂ)
    ```

    Proof outline: the integrand simplifies pointwise to `exp(0) = 1`
    via `zero_mul`, `Complex.exp_zero`; then `setIntegral_const` plus
    `Real.volume_real_Ioo_of_le` gives `(π - (-π)) • 1 = 2π`. Identical
    in structure to `circleMeanSq_const` from sprint 006.

  - exposes (3) `circleMeanInner` as a `noncomputable def`. Definition
    (or equivalent — the conjugate convention is at the generator's
    discretion as long as it is consistent across (4), (5), (6)):

    ```lean
    noncomputable def circleMeanInner (f g : ℂ → ℂ) (r : ℝ) : ℂ :=
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (starRingEnd ℂ) (f (Complex.polarCoord.symm (r, θ)))
          * g (Complex.polarCoord.symm (r, θ))
    ```

  - exposes (4) `circleMeanInner_monomial_diff`. Statement (or
    equivalent):

    ```lean
    theorem circleMeanInner_monomial_diff
        (m n : ℕ) (hmn : m ≠ n) (r : ℝ) :
        circleMeanInner (fun z => z ^ m) (fun z => z ^ n) r = 0
    ```

    Proof outline:
    - unfold `circleMeanInner`,
    - rewrite the integrand pointwise using `polarCoord_symm_eq_exp`
      (sprint 006); the integrand becomes
      `conj((r · exp(iθ))^m) · (r · exp(iθ))^n
        = r^(m+n) · exp(-imθ) · exp(inθ)
        = (r^(m+n) : ℂ) · exp((n - m : ℤ) · θ · I)`,
    - pull the `(r^(m+n) : ℂ)` constant out of the integral via
      `integral_const_mul`,
    - apply (1) with `k = (n : ℤ) - (m : ℤ)` (which is nonzero from
      `hmn`),
    - close with `mul_zero`.
    The conjugate-of-power and product-of-exp manipulations may need
    `mul_pow`, `Complex.exp_add`, `Complex.exp_neg`,
    `star_pow` / `Complex.conj_pow`, and a few `ring` / `ring_nf` calls
    to align exponents.

  - exposes (5) `circleMeanInner_monomial_same`. Statement (or
    equivalent):

    ```lean
    theorem circleMeanInner_monomial_same (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
        circleMeanInner (fun z => z ^ n) (fun z => z ^ n) r
          = ((2 * Real.pi * r ^ (2 * n) : ℝ) : ℂ)
    ```

    Proof outline: same setup as (4) with `m = n`; the exponent of
    `exp` collapses to `exp(0) = 1`; the integrand becomes the constant
    `(r^(2n) : ℂ)`; close via `setIntegral_const` and
    `Real.volume_real_Ioo_of_le` (mirroring `circleMeanSq_monomial`
    from sprint 006). The `0 ≤ r` hypothesis is for handling
    `‖r · exp(iθ)‖ = r`; depending on the Mathlib API used, it may be
    redundant.

  - exposes (6) `circleMeanSq_eq_re_circleMeanInner_self`. Statement
    (or equivalent):

    ```lean
    theorem circleMeanSq_eq_re_circleMeanInner_self (f : ℂ → ℂ) (r : ℝ) :
        circleMeanSq f r = (circleMeanInner f f r).re
    ```

    Proof outline:
    - unfold both `circleMeanSq` and `circleMeanInner`,
    - the LHS integrand is `‖f(...)‖² : ℝ`,
    - the RHS is `.re` of a `ℂ`-valued integral whose integrand is
      `conj(f(...)) · f(...)`,
    - pointwise `conj z · z = ‖z‖²` (via `Complex.mul_conj` or
      `Complex.conj_mul_self_eq_normSq`, plus `Complex.sq_abs` /
      `Complex.normSq_eq_abs`),
    - commute `.re` with the integral via `MeasureTheory.integral_re`
      (or `Complex.re_integral`),
    - close with `setIntegral_congr_fun` on the now-aligned integrands.

  - All six items must be `theorem`/`lemma`/`def`, never `axiom`, with
    no `sorry`. Names are guidelines; equivalent names are accepted as
    long as the conclusion of each is unchanged. The conjugate-vs-linear
    convention on `circleMeanInner` is at the generator's discretion;
    if the alternative `f g ↦ ∫ f · conj g` is chosen instead, items
    (4)–(6) must be restated coherently with that convention.

- `ProofRefinement/Korenblum/Candidates/V7.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V7`, marked
  `-- @parent V6`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V6),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V6,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`,
    `ProofRefinement.Korenblum.Proof.CircleExpBridge`, and the new
    `ProofRefinement.Korenblum.Proof.CircleInnerProduct` so that the
    new module is part of V7's compile graph and is exercised by the
    build. No structural use of the new lemmas is required in V7
    itself.
- No edits to `lemma.toml`. No edits to V0/V1/V2/V3/V4/V5/V6 or to the
  existing `Proof/*.lean` files. No new axioms beyond the
  already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V7` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V7.lean` succeeds (the evaluator
   accepts V7 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V6; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/CircleInnerProduct.lean`
   contains:
   - one `theorem` (or `lemma`) whose conclusion is the integral of
     `Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)` over `Ioo (-π) π`
     equals `0` for `k ∈ ℤ`, `k ≠ 0`;
   - one `theorem` (or `lemma`) computing the same integral at `k = 0`
     as `(2 * Real.pi : ℂ)` (or as the corresponding ℂ constant);
   - one `noncomputable def` of the `ℂ`-valued circle mean pairing on
     `(f g : ℂ → ℂ)` and `r : ℝ`;
   - one `theorem` giving `circleMeanInner (z^m) (z^n) r = 0` for
     `m ≠ n`;
   - one `theorem` giving the diagonal `circleMeanInner (z^n) (z^n) r
     = (2 π r^(2n) : ℂ)` (or an equivalent form, possibly with `0 ≤ r`
     hypothesis);
   - one `theorem` bridging `circleMeanSq` to `(circleMeanInner f f
     r).re`.
   None may be `axiom`; none may contain `sorry`.
4. The new module `Proof.CircleInnerProduct` must be **used**, even
   trivially, somewhere in V7's transitive compile graph (importing
   `Proof.CircleInnerProduct` from V7 is sufficient — it forces the
   module to compile as part of V7's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V6.lean`) or the existing
  `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`, `Proof/CircleMeanCompare.lean`,
  `Proof/RadialSplit.lean`, `Proof/CircleExpBridge.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If any of (1)–(6) is genuinely blocked on a
  missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- Prove the polynomial Parseval identity `circleMeanSq (∑_{k≤N} a_k
  z^k) r = 2π ∑_{k≤N} ‖a_k‖² r^(2k)` for general polynomial `f`. That
  is the next sprint, built on top of (1)–(6).
- Prove sesquilinearity of `circleMeanInner` (`circleMeanInner_add_left`,
  `circleMeanInner_add_right`, `circleMeanInner_smul_left`,
  `circleMeanInner_smul_right`). Useful, and each is one-line via
  `integral_add` / `integral_const_mul`, but they belong to the
  follow-up Parseval sprint where they are actually consumed; including
  them here inflates the sprint past one Generator session and obscures
  the headline orthogonality identity.
- Prove the `tsum`-level Parseval identity for analytic `f` on the
  open unit disk. Multiple sprints away.
- Bridge `circleMeanInner` to Mathlib's
  `Mathlib.Analysis.InnerProductSpace.PiL2` /
  `Mathlib.MeasureTheory.Function.LpSpace` `L²` inner product. Useful
  long-term but not required by (1)–(6).
- Push `c_value` above `3554/10000`. That is multiple follow-up sprints
  away.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `intervalIntegral.integral_exp` does not
  give the clean antiderivative shape required for item (1) at
  `c = ik · I`, or the bridge `Ioo (-π) π` ↔ `intervalIntegral` requires
  a measurability/integrability hypothesis the generator cannot
  produce, or `Complex.exp_int_mul_pi_mul_I` is not the available
  Mathlib name and no equivalent identity collapses
  `exp(ikπ) - exp(-ikπ) = 0` for `k ∈ ℤ`, or `MeasureTheory.integral_re`
  / `Complex.re_integral` is not the canonical Mathlib name for
  commuting `.re` with the integral required for item (6)):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (e.g. whether the generator tried `intervalIntegral.integral_exp`
  versus `intervalIntegral.integral_cos` + `intervalIntegral.integral_sin`
  separately on real and imaginary parts; whether
  `Complex.exp_int_mul_two_pi_mul_I = 1` was used or
  `Complex.exp_int_mul_pi_mul_I_eq_pow_neg_one`; whether the conjugate
  convention was chosen as `conj f * g` or `f * conj g`).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
