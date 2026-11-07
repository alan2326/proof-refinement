# Sprint 008: polynomial Bergman-Parseval circle-mean identity

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V7.lean`
**Target file**: `Candidates/V8.lean`
**Direction**: section2-proof (Bergman scaffolding — polynomial Parseval, the
direct consumer of sprints 006 and 007)

## Goal

Assemble the **polynomial circle-mean Parseval identity** by combining the
diagonal monomial seeds (`circleMeanSq_monomial`, sprint 006) with the
off-diagonal orthogonality (`circleMeanInner_monomial_diff`, sprint 007).
Expose, in a new file `Proof/CirclePolynomialParseval.lean`:

1. **Sesquilinearity of `circleMeanInner`** — the four standard linearity
   handles consumed by the polynomial expansion:

   - `circleMeanInner_add_left`,
   - `circleMeanInner_add_right`,
   - `circleMeanInner_smul_left`  (conjugate-linear in the first slot),
   - `circleMeanInner_smul_right` (linear in the second slot).

   These are one-line each from `MeasureTheory.integral_add` plus
   `MeasureTheory.integral_const_mul` (or `integral_mul_const`), with
   appropriate integrability hypotheses on the conjugate-product
   integrand. Convention is fixed by sprint 007: conjugate-linear in `f`,
   linear in `g`.

2. **Finset-sum versions** — the Finset.sum-shaped consumers used in the
   polynomial expansion:

   - `circleMeanInner_finset_sum_left`:

     ```lean
     circleMeanInner (fun z => ∑ k ∈ s, a k * fk k z) g r
       = ∑ k ∈ s, (starRingEnd ℂ) (a k) * circleMeanInner (fk k) g r
     ```

     (or its specialised monomial-coefficient form)

   - `circleMeanInner_finset_sum_right`:

     ```lean
     circleMeanInner f (fun z => ∑ k ∈ s, b k * gk k z) r
       = ∑ k ∈ s, b k * circleMeanInner f (gk k) r
     ```

   These follow by `Finset.induction_on` from item (1). The exact shape
   is at the generator's discretion; the **headline polynomial Parseval
   identity** in (4) only needs the specialisation to monomials, so a
   pair of monomial-only lemmas

   ```lean
   circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k) g r
     = ∑ k ∈ s, (starRingEnd ℂ) (a k) * circleMeanInner (fun z => z ^ k) g r
   ```

   plus its right-slot dual is also acceptable.

3. **Diagonal `circleMeanInner` of polynomials** —

   ```lean
   theorem circleMeanInner_polynomial_self
       (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
       circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k)
                       (fun z => ∑ k ∈ s, a k * z ^ k) r
         = ∑ k ∈ s, ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ) * ‖a k‖ ^ 2
   ```

   (or with `‖a k‖²` written via `Complex.normSq` / `(starRingEnd ℂ) (a k) * a k`,
   modulo coercions). Proof outline: expand both sides using item (2)
   to reduce to a double sum over `Finset s ×ˢ Finset s` of
   `conj(a m) * a n * circleMeanInner (z^m) (z^n) r`; split the sum by
   `m = n` vs `m ≠ n`; the `m ≠ n` cross terms vanish via
   `circleMeanInner_monomial_diff` (sprint 007); the diagonal `m = n`
   terms collapse to `‖a k‖² · (2π · r^(2k))` via
   `circleMeanInner_monomial_same` (sprint 007).

4. **The headline polynomial Parseval identity** —

   ```lean
   theorem circleMeanSq_polynomial
       (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
       circleMeanSq (fun z => ∑ k ∈ s, a k * z ^ k) r
         = ∑ k ∈ s, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
   ```

   (or with `(2 * Real.pi) * ∑ k ∈ s, r^(2k) * ‖a k‖²` factored, modulo
   `Finset.mul_sum` / `mul_comm`). Proof outline: combine
   `circleMeanSq_eq_re_circleMeanInner_self` (sprint 007) with
   `circleMeanInner_polynomial_self` (item 3); take `.re` of the RHS,
   noting the RHS is real-valued (each term `((2π r^(2k) : ℝ) : ℂ) * ‖a k‖²`
   has zero imaginary part), and rewrite via `Complex.ofReal_re`.

V8 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V7
and the only seed axiom is still `hKorenblum_published_3554`. The
contribution is the new derived module that finally pins, in Lean, the
algebraic equation at the heart of every honest Korenblum proof:
*the `A²` circle-mean of a polynomial is a coefficient-level termwise
sum*. With this in place, the inner-half radial dominance hypothesis
of sprint 005 (`validKorenblum_of_innerCircleMean_dom`) becomes
attackable for polynomial `f, g` as a coefficient-level inequality —
the natural next sprint.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- **This is the explicitly named follow-up.** Sprint 007's `Why` paragraph
  states: *"the polynomial Parseval identity becomes a single follow-up
  sprint: expand `‖∑ a_k z^k‖² = (∑ conj(a_m) z^m)(∑ a_n z^n)`, integrate
  termwise, kill cross terms via (4), keep diagonal via (5) and (6)."*
  Sprint 007 also explicitly *excluded* sesquilinearity from its scope
  with the rationale *"they belong to the follow-up Parseval sprint where
  they are actually consumed"*. Sprint 008 is exactly that follow-up.
- **All required pieces are in place.** Sprint 006 gives the diagonal
  seed `circleMeanSq_monomial` and the polar→exp bridge
  `polarCoord_symm_eq_exp`. Sprint 007 gives the `ℂ`-valued circle inner
  product `circleMeanInner`, its off-diagonal orthogonality
  `circleMeanInner_monomial_diff`, its diagonal companion
  `circleMeanInner_monomial_same`, and the bridge
  `circleMeanSq_eq_re_circleMeanInner_self`. The polynomial Parseval is
  now a pure algebraic-bookkeeping derivation: expand the double sum,
  cancel the off-diagonal, collect the diagonal.
- **Why this is the canonical next stone, not a `c`-push.** The honest
  Korenblum proof at any radius `c > 0.3554` must, at some stage,
  reduce the function-level `‖f‖_{A²}` ≤ `‖g‖_{A²}` inequality to a
  coefficient-level termwise comparison. The polynomial Parseval is
  the *sole* algebraic identity that performs this reduction; it cannot
  be skipped or replaced. Without it, the inner-half radial dominance
  hypothesis taken by `validKorenblum_of_innerCircleMean_dom`
  (sprint 005) remains unattackable. With it, the next sprint can
  attempt the polynomial inner-half dominance as a coefficient-level
  inequality (or, more honestly, recognise that the inner-half
  dominance is *false* pointwise and that a more delicate argument
  e.g. summation-by-parts on the radial weights `r^(2k)`, is needed —
  but at least the question moves into the coefficient world where it
  is concrete).
- **Why this and not the `tsum`-level Parseval directly.** The infinite
  series version requires bridging `AnalyticOn ℂ f UnitDisk` to a
  formal-power-series representation in Mathlib (`HasFPowerSeriesOnBall`,
  radius-of-convergence bounds, dominated convergence over θ on
  `Ioo (-π) π`). All of those steps stack on top of the polynomial
  case, which is the limit-target. Doing the polynomial case first
  isolates the *algebraic* content of Parseval from the *limit-passing*
  content; doing them simultaneously inflates the sprint past one
  Generator session and obscures both bottlenecks.
- **Mathlib has the right primitives.** Sesquilinearity (item 1)
  follows from `MeasureTheory.integral_add` (with integrability
  hypotheses on each summand) plus `MeasureTheory.integral_const_mul`.
  Finset-sum versions (item 2) are `Finset.induction_on` chains
  composing the binary additivity. Item (3) is a `Finset.sum_product`
  / `Finset.sum_comm` rearrangement of the double sum, splitting on
  diagonal vs. off-diagonal via
  `Finset.sum_filter` + `Finset.sum_filter_eq` (or by the standard
  `Finset.sum_eq_sum_diag_add_sum_off_diag` pattern, which Mathlib
  exposes via `Finset.sum_product` plus `if h : m = n then ... else ...`).
  Item (4) is a `.re` of item (3) plus `Complex.ofReal_re`.
- **The proofs sit comfortably in the generator's declared scope.**
  AGENT_BRIEF lists "termwise summability and `tsum`-level
  rearrangements" as in scope; the polynomial (Finset) case is
  strictly easier than `tsum`. Each item is a chain of Mathlib
  rewrites plus a `Finset.induction_on` or a `Finset.sum_product`
  rearrangement. No new analytic content is introduced.
- **Falsifiable bottleneck.** If the cross-term cancellation cannot be
  cleanly executed because the double-sum split is awkward in Mathlib's
  current `Finset.sum_product` API (e.g. requires too much explicit
  index-manipulation in the `if h : m = n` branch), the
  `STATUS=BLOCKED` log will record exactly which Mathlib lemma was the
  obstruction. That bottleneck is the same one any future polynomial
  Bergman-coefficient attack would face, so the failure mode is
  informative.
- **Why not bundle into a c-push attempt directly.** The polynomial
  Parseval identity *cannot* by itself raise `c_value`: the
  function-level Korenblum hypothesis admits arbitrary analytic
  `f, g`, not polynomials, and even at the polynomial level the
  inner-half dominance is non-trivial. Bundling Parseval with a
  `c`-push would tie the sprint's pass criterion to an as-yet-unwritten
  coefficient-level inequality. Pinning Parseval as scaffolding-only
  isolates the algebraic content cleanly and keeps the sprint
  acceptance criterion falsifiable in one Generator session.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CirclePolynomialParseval.lean`:
  **new file**, in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.RadialBergman`,
    `Proof.CircleExpBridge`, `Proof.CircleInnerProduct` (and **only**
    those workspace-side imports),

  - exposes (1) the four sesquilinearity handles. Statement (or
    equivalent — integrability hypotheses are at the generator's
    discretion as long as the conclusion is unchanged):

    ```lean
    theorem circleMeanInner_add_left
        (f₁ f₂ g : ℂ → ℂ) (r : ℝ)
        (hf₁ : IntegrableOn (fun θ =>
            (starRingEnd ℂ) (f₁ (Complex.polarCoord.symm (r, θ)))
              * g (Complex.polarCoord.symm (r, θ)))
          (Set.Ioo (-Real.pi) Real.pi) volume)
        (hf₂ : IntegrableOn (fun θ =>
            (starRingEnd ℂ) (f₂ (Complex.polarCoord.symm (r, θ)))
              * g (Complex.polarCoord.symm (r, θ)))
          (Set.Ioo (-Real.pi) Real.pi) volume) :
        circleMeanInner (fun z => f₁ z + f₂ z) g r
          = circleMeanInner f₁ g r + circleMeanInner f₂ g r

    theorem circleMeanInner_add_right
        (f g₁ g₂ : ℂ → ℂ) (r : ℝ)
        (hg₁ : IntegrableOn ... volume)
        (hg₂ : IntegrableOn ... volume) :
        circleMeanInner f (fun z => g₁ z + g₂ z) r
          = circleMeanInner f g₁ r + circleMeanInner f g₂ r

    theorem circleMeanInner_smul_left
        (c : ℂ) (f g : ℂ → ℂ) (r : ℝ) :
        circleMeanInner (fun z => c * f z) g r
          = (starRingEnd ℂ) c * circleMeanInner f g r

    theorem circleMeanInner_smul_right
        (c : ℂ) (f g : ℂ → ℂ) (r : ℝ) :
        circleMeanInner f (fun z => c * g z) r
          = c * circleMeanInner f g r
    ```

    Proofs: unfold `circleMeanInner`, apply `MeasureTheory.integral_add`
    on the integrable-sum form for additivity, or
    `MeasureTheory.integral_const_mul` for scalar multiplication; for
    `_smul_left`, use `(starRingEnd ℂ).map_mul` (i.e.
    `map_mul (starRingEnd ℂ) c (f _)`) to pull the conjugated scalar
    out of the conjugate-product integrand, then
    `integral_const_mul`. The smul lemmas should not need
    integrability hypotheses (Mathlib's `integral_const_mul` does not
    require them: when not integrable, both sides are zero by
    convention).

  - exposes (2) the two Finset-sum handles. Statement (or equivalent —
    the monomial-only specialisation is acceptable if the generator
    finds the general form awkward):

    ```lean
    theorem circleMeanInner_finset_sum_monomial_left
        (s : Finset ℕ) (a : ℕ → ℂ) (g : ℂ → ℂ) (r : ℝ) :
        circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k) g r
          = ∑ k ∈ s,
              (starRingEnd ℂ) (a k)
                * circleMeanInner (fun z => z ^ k) g r

    theorem circleMeanInner_finset_sum_monomial_right
        (s : Finset ℕ) (b : ℕ → ℂ) (f : ℂ → ℂ) (r : ℝ) :
        circleMeanInner f (fun z => ∑ k ∈ s, b k * z ^ k) r
          = ∑ k ∈ s, b k * circleMeanInner f (fun z => z ^ k) r
    ```

    Proof outline: `Finset.induction_on s`. Empty case: both sides are
    `0` (LHS uses `Finset.sum_empty` to reduce to `circleMeanInner
    (fun _ => 0) g r = 0`, which follows from a pointwise integrand =
    0 plus `MeasureTheory.integral_zero`). Cons case: split via
    `Finset.sum_insert` and apply (1) `_add_left` plus `_smul_left`.
    A typeclass / integrability nuisance: the `_add_left` lemma needs
    an integrability hypothesis on each summand. The cleanest way is
    to assume integrability of each `(fun θ => conj((a k * z^k) at
    polarCoord(r,θ)) * g(polarCoord(r,θ)))` for `k ∈ s`, threaded
    through the induction. If the integrability bookkeeping balloons,
    the generator may instead specialise to the case where `g` is also
    a polynomial (item 3 only needs that case), or strengthen the
    hypothesis to a Finset-uniform integrability bound — at the
    generator's discretion, recorded in `Experience.md`.

  - exposes (3) `circleMeanInner_polynomial_self`. Statement (or
    equivalent):

    ```lean
    theorem circleMeanInner_polynomial_self
        (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
        circleMeanInner (fun z => ∑ k ∈ s, a k * z ^ k)
                        (fun z => ∑ k ∈ s, a k * z ^ k) r
          = ∑ k ∈ s,
              ((2 * Real.pi * r ^ (2 * k) : ℝ) : ℂ) * ‖a k‖ ^ 2
    ```

    Proof outline:
    - apply (2) `_finset_sum_monomial_left` to expand the left slot;
    - apply (2) `_finset_sum_monomial_right` inside each
      `circleMeanInner (z^m) (∑ a_n z^n)`; this gives
      `∑ m ∈ s, conj(a m) * ∑ n ∈ s, a n * circleMeanInner (z^m) (z^n) r`;
    - rewrite as a double sum via `Finset.mul_sum` and
      `Finset.sum_product` (or `Finset.sum_comm`);
    - split the double sum into `m = n` and `m ≠ n` parts. The
      cleanest pattern is `Finset.sum_eq_sum_diag_add_sum_off_diag`
      if available; otherwise `Finset.sum_filter` plus
      `Finset.sum_filter_eq`, or `Finset.sum_ite` with
      `decide_eq_or_decide_neq`. If none of these are clean, fall
      back to nested `Finset.sum_congr` plus a manual case-split;
    - off-diagonal vanishes via `circleMeanInner_monomial_diff` (sprint 007);
    - diagonal collapses via `circleMeanInner_monomial_same` (sprint 007),
      giving `conj(a k) * a k * (2π r^(2k) : ℂ)
      = (2π r^(2k) : ℂ) * ‖a k‖²` (using `Complex.mul_conj` /
      `Complex.normSq_eq_conj_mul_self` plus `Complex.normSq_eq_norm_sq`).

  - exposes (4) `circleMeanSq_polynomial`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_polynomial
        (s : Finset ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
        circleMeanSq (fun z => ∑ k ∈ s, a k * z ^ k) r
          = ∑ k ∈ s, (2 * Real.pi * r ^ (2 * k)) * ‖a k‖ ^ 2
    ```

    Proof outline:
    - apply `circleMeanSq_eq_re_circleMeanInner_self` (sprint 007) to
      rewrite the LHS as `(circleMeanInner (∑) (∑) r).re`;
    - apply `circleMeanInner_polynomial_self` (item 3) to evaluate the
      inner;
    - the resulting `.re` of `∑ k, ((2π r^(2k) : ℝ) : ℂ) * ‖a k‖²`
      equals `∑ k, (2π r^(2k)) * ‖a k‖²` via `Complex.re_sum`
      (or `Finset.sum_re`) plus `Complex.ofReal_re` plus the fact
      that `‖a k‖² : ℝ` coerces to a real `ℂ` whose `.re` is itself.

  - All four items must be `theorem`/`lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as
    long as the conclusion is unchanged. The exact integrability
    hypotheses on the sesquilinearity lemmas are at the generator's
    discretion.

- `ProofRefinement/Korenblum/Candidates/V8.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V8`, marked
  `-- @parent V7`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V7),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V7,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`,
    `ProofRefinement.Korenblum.Proof.CircleExpBridge`,
    `ProofRefinement.Korenblum.Proof.CircleInnerProduct`, and the new
    `ProofRefinement.Korenblum.Proof.CirclePolynomialParseval` so that
    the new module is part of V8's compile graph and is exercised by
    the build. No structural use of the new lemmas in V8 itself is
    required.
- No edits to `lemma.toml`. No edits to V0/.../V7 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V8` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V8.lean` succeeds (the evaluator
   accepts V8 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V7; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/CirclePolynomialParseval.lean`
   contains:
   - a sesquilinearity handle for additivity in the left slot of
     `circleMeanInner` (and a matching right-slot lemma);
   - a sesquilinearity handle for scalar multiplication in the left
     slot of `circleMeanInner` (conjugate-linear; pulls
     `(starRingEnd ℂ) c` out) and a matching right-slot lemma (linear;
     pulls `c` out);
   - a Finset.sum-shaped consumer for monomial-coefficient
     polynomials in each slot of `circleMeanInner`;
   - a `theorem` giving `circleMeanInner (∑ a_k z^k) (∑ a_k z^k) r =
     ∑ k, ((2π r^(2k) : ℝ) : ℂ) * ‖a k‖²` (or an equivalent form);
   - a `theorem` giving the headline `circleMeanSq (∑ a_k z^k) r =
     ∑ k, (2π · r^(2k)) * ‖a k‖²` (or an equivalent form).
   None may be `axiom`; none may contain `sorry`.
4. The new module `Proof.CirclePolynomialParseval` must be **used**,
   even trivially, somewhere in V8's transitive compile graph (importing
   it from V8 is sufficient — it forces the module to compile as part
   of V8's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V7.lean`) or the existing
  `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`, `Proof/CircleMeanCompare.lean`,
  `Proof/RadialSplit.lean`, `Proof/CircleExpBridge.lean`,
  `Proof/CircleInnerProduct.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If any of (1)–(4) is genuinely blocked on a
  missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- Prove the `tsum`-level Parseval identity for analytic `f` on the
  open unit disk, i.e.
  `circleMeanSq f r = 2π · ∑' k, ‖a k‖² · r^(2k)`
  for `f` with formal power series `(a, R)`. This is the next sprint,
  built on top of (1)–(4) plus a Mathlib bridge through
  `HasFPowerSeriesOnBall` and a dominated-convergence-on-θ argument.
- Bridge `circleMeanInner` to Mathlib's
  `Mathlib.Analysis.InnerProductSpace.PiL2` /
  `Mathlib.MeasureTheory.Function.LpSpace` `L²` inner product. Useful
  long-term but not required by (1)–(4).
- Push `c_value` above `3554/10000`. Multiple follow-up sprints away.
- Attempt the inner-half radial dominance hypothesis of
  `validKorenblum_of_innerCircleMean_dom` (sprint 005) at polynomial
  level. That requires (1)–(4) **plus** a coefficient-level Korenblum
  inequality — which is itself non-trivial and not provable by
  algebraic bookkeeping alone. Multiple follow-up sprints.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. the integrability bookkeeping for the
  Finset-induction sesquilinearity sum lemmas (item 2) cannot be
  threaded cleanly because Mathlib's `MeasureTheory.integral_finset_sum`
  variant requires a hypothesis the generator cannot produce, or
  `Finset.sum_eq_sum_diag_add_sum_off_diag` (or its equivalent) is not
  the available Mathlib name and the explicit `Finset.sum_product` +
  `if h : m = n then ... else ...` rewrite is too brittle, or
  `Complex.normSq_eq_conj_mul_self` does not give `conj a * a = ‖a‖²`
  in the form needed for the diagonal collapse, or
  `Complex.ofReal_re` / `Complex.re_sum` / `Finset.sum_re` is not the
  available Mathlib name for commuting `.re` past a finite sum):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (e.g. whether the generator tried
  `Finset.sum_eq_sum_diag_add_sum_off_diag` versus
  `Finset.sum_filter_ne_self`; whether the integrability hypothesis was
  threaded as a Finset-uniform bound or as a per-summand bound;
  whether `Complex.normSq_eq_conj_mul_self` was used or
  `Complex.mul_conj` plus an explicit cast to `‖a‖²`).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
