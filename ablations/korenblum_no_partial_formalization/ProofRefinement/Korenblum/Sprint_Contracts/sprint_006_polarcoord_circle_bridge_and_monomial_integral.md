# Sprint 006: `polarCoord.symm` ↔ `Complex.exp` bridge + monomial circle integrals

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V5.lean`
**Target file**: `Candidates/V6.lean`
**Direction**: section2-proof (Bergman scaffolding — bridge to `Complex.exp` parametrisation and the first Parseval / Bergman-monomial ingredients)

## Goal

Open the door to Mathlib's `Complex.exp`-based circle / Hardy / Bergman
machinery by building a thin bridge from our polar-coordinate parametrisation
to the canonical exponential parametrisation, and use that bridge to prove
the seed orthogonality identities for `circleMeanSq` of complex monomials.

Concretely, in a new file `Proof/CircleExpBridge.lean`, expose:

1. **`polarCoord_symm_eq_exp`** — the pointwise identity

   ```
   (Complex.polarCoord.symm (r, θ) : ℂ) = r * Complex.exp (θ * Complex.I)
   ```

   for any `r : ℝ`, `θ : ℝ` (no positivity hypothesis required: both sides
   agree even at `r = 0`).

2. **`norm_polarCoord_symm_pow`** — for `n : ℕ` and `r ≥ 0`,

   ```
   ‖(Complex.polarCoord.symm (r, θ) : ℂ) ^ n‖ ^ 2 = r ^ (2 * n)
   ```

   Direct corollary of (1) plus `Complex.norm_exp_ofReal_mul_I = 1` and
   `‖r‖ = r` for `r ≥ 0`.

3. **`circleMeanSq_monomial`** — for `n : ℕ` and `r : ℝ` with `0 ≤ r`,

   ```
   circleMeanSq (fun z => z ^ n) r = 2 * Real.pi * r ^ (2 * n)
   ```

   Proof: rewrite the integrand pointwise via (2) into the constant
   `r^(2n)`, then `∫_{Ioo (-π) π} (r^(2n)) dθ = 2π * r^(2n)`.

4. **`circleMeanSq_const`** — for `c : ℂ` and `r : ℝ`,

   ```
   circleMeanSq (fun _ => c) r = 2 * Real.pi * ‖c‖ ^ 2
   ```

   Special case (or independent direct integration on the constant
   integrand). The two forms `circleMeanSq (fun _ => c) r` and
   `‖c‖² · circleMeanSq (fun _ => 1) r` should both be derivable; the
   exact statement form is at the generator's discretion as long as the
   conclusion captures the constant-circle-mean identity.

5. **`circleMeanSq_smul`** — for `c : ℂ`, `f : ℂ → ℂ`, `r : ℝ`,

   ```
   circleMeanSq (fun z => c * f z) r = ‖c‖ ^ 2 * circleMeanSq f r
   ```

   Pointwise norm-square multiplicativity plus `integral_const_mul`.

V6 is **scaffolding-only**: `c_value = 3554/10000` is unchanged from V5
and the only seed axiom is still `hKorenblum_published_3554`. The
contribution is the new derived module, which is the **first** stone in
the Bergman-Parseval / monomial-decomposition direction. Every honest
analytic chain that pushes `c` above `0.3554` factors through some
identity of this kind (Bergman A² Parseval `bergmanNormSq f = π · ∑_n
|a_n|² / (n+1)`, or its annular versions).

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move must prove `ValidKorenblumBound
c_value` directly against Mathlib (function-level Bergman A² Korenblum max
principle), or build a self-contained per-candidate partial formalization
on top of Mathlib. The only fixed target is the final theorem shape.

## Why

- After sprints 001–005, the radial scaffolding chain is closed at the
  bookkeeping level: polar pull-back, inner / outer set split, radial
  polar form on each half, outer-annulus circle-mean comparison, radial
  integral split, and a conditional Korenblum reduction
  (`validKorenblum_of_innerCircleMean_dom`). What is **missing** is any
  bridge from our `polarCoord.symm`-based `circleMeanSq` to Mathlib's
  `Complex.exp`-based / `circleMap`-based circle integrals.
- Without this bridge, no Mathlib API in
  `Mathlib.Analysis.Complex.CauchyIntegral`,
  `Mathlib.MeasureTheory.Integral.CircleIntegral`,
  `Mathlib.Analysis.SpecialFunctions.Complex.Circle`, or any future
  Hardy / Bergman / `Real.circleAverage` lemma can be invoked on
  `circleMeanSq`. Every analytic move past sprint 005 — Parseval, Cauchy
  representation, subharmonicity of `‖f‖²`, mean-value monotonicity —
  needs the `Complex.exp` parametrisation. This sprint produces it.
- A separate observation about sprint 005 motivates **not** using its
  conditional reduction as the next analytical target. The
  `validKorenblum_of_innerCircleMean_dom` lemma takes as hypothesis
  `∀ r ∈ Ioc 0 c, circleMeanSq f r ≤ circleMeanSq g r`. Korenblum's
  actual statement gives only outer-annulus pointwise dominance, plus
  analyticity. The inner-half pointwise circle-mean dominance is
  **stronger** than what Korenblum guarantees — for general
  Korenblum-admissible analytic `(f, g)` the integrated inner-half
  inequality holds while the pointwise circle-mean inner-half
  inequality may fail (this is exactly why `c = 0.3554`, not `c = 0`).
  Therefore the natural next move is **not** to attempt the
  inner-half pointwise circle-mean dominance directly. The natural next
  move is to build the Bergman-Parseval / monomial scaffolding that
  exposes `circleMeanSq f r` as `2π · ∑_n |a_n|² · r^(2n)` for
  Taylor-series-decomposable `f`, after which the Korenblum inequality
  reduces to a coefficient-level termwise comparison.
- The four monomial / scaling identities (1)–(5) are precisely the seed
  building blocks for that decomposition. They are mathematically
  elementary and sit comfortably in the generator's declared scope:
  - (1) is `Complex.exp_mul_I` plus `Complex.cos_ofReal`,
    `Complex.sin_ofReal`, plus `Complex.ofReal_mul`. Our
    `polarCoord.symm (r, θ) = ⟨r * cos θ, r * sin θ⟩` (a `ℝ × ℝ`-pair
    coerced to `ℂ`) and Euler's formula immediately give
    `r * (cos θ + sin θ · I) = r · exp (θ I)`.
  - (2) follows from (1), `Complex.norm_exp_ofReal_mul_I = 1`,
    `norm_mul`, `Complex.norm_real`, and `pow_two`. The `n`-th power
    distributes over `r * exp(θI)` via `mul_pow`.
  - (3) substitutes (2) into the integrand of `circleMeanSq`. The
    integrand becomes the constant `r^(2n)` (independent of `θ`), and
    `∫_{Ioo (-π) π} c dθ = 2π · c` follows from `MeasureTheory.integral_const`
    plus `Real.volume_Ioo` (which gives `volume (Ioo (-π) π) = 2π`).
  - (4) is the case `n = 0` or a direct constant-integrand integration.
  - (5) is `‖c · f‖² = ‖c‖² · ‖f‖²` plus `integral_const_mul`.
- After this sprint, the next sprint (007) becomes credible: prove the
  full Bergman-Parseval identity for finite sums of monomials, and
  expose `circleMeanSq` as a polynomial in `r²` for polynomial `f`.
  That polynomial-level statement is the inductive seed for the full
  Parseval `tsum` later. Without sprint 006, that follow-up cannot be
  attempted: it would have to re-prove the bridge inline.
- Falsifiable bottleneck: if (1) cannot be discharged because Mathlib's
  `Complex.polarCoord` definition does not unfold to
  `⟨r · Real.cos θ, r · Real.sin θ⟩` cleanly, or because the coercion
  `(⟨a, b⟩ : ℝ × ℝ) → (a + b · I : ℂ)` is not the right form, the
  generator records the exact obstruction in `Experience.md`. That is
  the same plumbing obstruction every future Mathlib-API-based attack
  on `circleMeanSq` would face, so the failure mode is informative.
- Why this sprint and not a numerical-budget push at higher `c`: the
  workspace currently has zero monomial / Parseval-style identities on
  `circleMeanSq`. Without one, no honest analytic attack on the inner
  half can compose. Filing a "push `c` from `0.3554` to `0.36`" sprint
  would be premature — the analytic content does not yet exist in the
  Lean trust surface.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/CircleExpBridge.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,
  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.RadialBergman`
    (and **only** those workspace-side imports),
  - exposes (1) `polarCoord_symm_eq_exp`. Statement (or equivalent):

    ```lean
    theorem polarCoord_symm_eq_exp (r θ : ℝ) :
        (Complex.polarCoord.symm (r, θ) : ℂ)
          = (r : ℂ) * Complex.exp (θ * Complex.I)
    ```

    Proof outline: unfold `Complex.polarCoord.symm` to
    `⟨r * Real.cos θ, r * Real.sin θ⟩` (a `ℝ × ℝ` pair, coerced to `ℂ`
    as `r * cos θ + (r * sin θ) * I`); rewrite via
    `Complex.exp_mul_I` (which gives `Complex.exp (θ * I) = Complex.cos
    θ + Complex.sin θ * I`); reduce `Complex.cos (θ : ℂ)` to
    `(Real.cos θ : ℂ)` and similarly for `sin`. The exact `Complex.ofReal`
    plumbing is at the generator's discretion; the conclusion is fixed.
  - exposes (2) `norm_polarCoord_symm_pow`. Statement (or equivalent):

    ```lean
    theorem norm_polarCoord_symm_pow {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (n : ℕ) :
        ‖(Complex.polarCoord.symm (r, θ) : ℂ) ^ n‖ ^ 2 = r ^ (2 * n)
    ```

    Proof outline: rewrite via (1); `mul_pow` to distribute the `n`-th
    power; `norm_mul`, `norm_pow`, `Complex.norm_exp_ofReal_mul_I = 1`,
    `Complex.norm_real`, `Real.norm_eq_abs`, `abs_of_nonneg hr`; then
    `(r^n)^2 = r^(2n)` via `pow_mul` or `mul_comm` + `pow_mul_comm'`.
    A couple of `ring` / `ring_nf` calls may be needed to close.
  - exposes (3) `circleMeanSq_monomial`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_monomial {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
        circleMeanSq (fun z => z ^ n) r = 2 * Real.pi * r ^ (2 * n)
    ```

    Proof outline: unfold `circleMeanSq`. `setIntegral_congr_fun
    measurableSet_Ioo` to rewrite the integrand pointwise via (2)
    into the constant `r^(2n)`. Then `integral_const` plus
    `Real.volume_Ioo` (or `Real.volume_real_Ioo`) gives `2π * r^(2n)`.
    Adjust constants by `ring` if needed (the form `Real.pi - (-Real.pi)
    = 2 * Real.pi` needs one `ring` / `linarith` step).
  - exposes (4) `circleMeanSq_const`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_const (c : ℂ) (r : ℝ) :
        circleMeanSq (fun _ => c) r = 2 * Real.pi * ‖c‖ ^ 2
    ```

    Proof outline: identical to (3) at `n = 0`, or direct
    constant-integrand integration via `integral_const`.
  - exposes (5) `circleMeanSq_smul`. Statement (or equivalent):

    ```lean
    theorem circleMeanSq_smul (c : ℂ) (f : ℂ → ℂ) (r : ℝ) :
        circleMeanSq (fun z => c * f z) r
          = ‖c‖ ^ 2 * circleMeanSq f r
    ```

    Proof outline: unfold `circleMeanSq`. Pointwise rewrite the
    integrand via `norm_mul`, `mul_pow`. Pull `‖c‖²` out via
    `integral_const_mul`. (The integrability sidecondition for
    `integral_const_mul` does not arise — it is unconditional in
    `MeasureTheory`.)
  - All five must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. Names are guidelines; equivalent names are accepted as
    long as the conclusion is unchanged.
- `ProofRefinement/Korenblum/Candidates/V6.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V6`, marked
  `-- @parent V5`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V5),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V5,
  - imports `ProofRefinement.Korenblum.Proof.PolarBergman`,
    `ProofRefinement.Korenblum.Proof.AnnulusBergman`,
    `ProofRefinement.Korenblum.Proof.RadialBergman`,
    `ProofRefinement.Korenblum.Proof.CircleMeanCompare`,
    `ProofRefinement.Korenblum.Proof.RadialSplit`, and the new
    `ProofRefinement.Korenblum.Proof.CircleExpBridge` so that the new
    module is part of V6's compile graph and is exercised by the build.
    No structural use of the new lemmas is required in V6 itself.
- No edits to `lemma.toml`. No edits to V0/V1/V2/V3/V4/V5 or to the
  existing `Proof/*.lean` files. No new axioms beyond the
  already-allowed `hKorenblum_published_3554`. No proposals filed.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V6` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V6.lean` succeeds (the evaluator
   accepts V6 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V5; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/CircleExpBridge.lean`
   contains five `theorem` (or `lemma`) declarations with conclusions
   matching items (1)–(5) above (signatures may vary; conclusions are
   the contract). At a minimum:
   - one statement of the bridge identity
     `(Complex.polarCoord.symm (r, θ) : ℂ) = r * Complex.exp (θ * I)`;
   - one statement giving the squared norm of `(polarCoord.symm)^n` as
     `r^(2n)` (for `r ≥ 0`);
   - one statement computing `circleMeanSq (z ↦ z^n) r` as
     `2π · r^(2n)` (for `r ≥ 0`);
   - one statement computing `circleMeanSq (z ↦ c) r` as
     `2π · ‖c‖²` (or an equivalent constant-circle-mean identity);
   - one statement giving the multiplicative-scalar identity
     `circleMeanSq (z ↦ c · f z) r = ‖c‖² · circleMeanSq f r`.
   None may be `axiom`; none may contain `sorry`.
4. The new module `Proof.CircleExpBridge` must be **used**, even
   trivially, somewhere in V6's transitive compile graph (importing
   `Proof.CircleExpBridge` from V6 is sufficient — it forces the module
   to compile as part of V6's build).

## Out of scope

- Edit older candidates (`V0.lean` through `V5.lean`) or the existing
  `Proof/PolarBergman.lean`, `Proof/AnnulusBergman.lean`,
  `Proof/RadialBergman.lean`, `Proof/CircleMeanCompare.lean`,
  `Proof/RadialSplit.lean`.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms). If any of (1)–(5) is genuinely blocked on a
  missing Mathlib API, the generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.
- Prove Bergman-A² Parseval `bergmanNormSq f = π · ∑_n |a_n|² / (n+1)`
  for general analytic `f`. That is its own follow-up sprint built on
  top of (1)–(5).
- Prove circle-orthogonality of distinct monomials
  `∫_{Ioo (-π) π} conj(z^m) · z^n dθ = 0` for `m ≠ n`. Useful, but a
  separate next sprint; (1)–(5) above already form a single coherent
  unit and sufficient deliverable.
- Bridge `circleMeanSq` to Mathlib's `Real.circleAverage` (which uses
  `circleMap` and a normalisation factor `1 / (2π)`). The
  `polarCoord.symm ↔ circleMap` bridge is naturally a same-direction
  follow-up sprint, but it is not required by (1)–(5). Keeping this
  sprint focused on the `Complex.exp` parametrisation only is what
  keeps it single-session-sized.
- Compute `circleMeanSq f r` for sums of monomials (the polynomial
  Parseval identity). Follow-up sprint, building on (3) and a
  monomial-orthogonality lemma.
- Push `c_value` above `3554/10000`. That is multiple follow-up
  sprints away.
- Edit `lemma.toml` (no policy expansion needed; the
  `ProofRefinement.Korenblum.Proof` prefix is already admitted).

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope (e.g. `Complex.polarCoord.symm` does not unfold
  cleanly to `⟨r · Real.cos θ, r · Real.sin θ⟩`, or `Complex.exp_mul_I`
  is not the right form to bridge `cos θ + sin θ · I` to
  `Complex.exp (θ · I)`, or `Real.volume_Ioo` does not give
  `volume (Ioo (-π) π) = 2π` in the `ENNReal` / `ℝ≥0∞` / `ℝ` shape
  required by `integral_const`): `STATUS=BLOCKED` with a precise note
  in `Experience.md` recording which Mathlib lemma was the obstruction
  and which approaches were tried (e.g. whether the generator tried
  `Complex.polarCoord_symm_apply` versus an unfold via `simp [Complex.polarCoord]`,
  whether `Complex.exp_mul_I` versus `Complex.exp_eq_cos_add_sin_mul_I`
  was used, whether `MeasureTheory.integral_const` versus
  `MeasureTheory.setIntegral_const` was the right form for the constant
  `θ`-integral on `Ioo (-π) π`).
- Needs human trust expansion (e.g. a genuinely missing analytic
  ingredient that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
