# Sprint 021: Möbius disk automorphism derivative + Jacobian modulus identity

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V20.lean`
**Target file**: `Candidates/V21.lean`
**Direction**: section2-proof / scaffolding-for-c-push (the next link in the
Möbius / pseudohyperbolic chain after sprint 020. Sprint 020's contract
explicitly named this as the natural follow-up: *"The next natural sprint
is the Jacobian identity `|φ_a'(z)|² = (1 - ‖a‖²)² / ‖1 - conj(a)z‖^4`
(which together with change-of-variables yields Bergman A² conformal
invariance), or the maximum-modulus-principle-based Schwarz–Pick lemma on
top of these primitives."* This sprint pins the **derivative form** —
the prerequisite for both Bergman A² conformal invariance and any
pseudohyperbolic / Schwarz–Pick lemma that needs the Möbius pushforward
metric. Without it the entire Möbius chain stalls.)

## Goal

Ship one new derived module `Proof/MobiusDeriv.lean` that pins the
derivative of the unit-disk Möbius automorphism `mobiusDisk a` (sprint
020's `Proof/MobiusDisk.lean`) and the **modulus** of that derivative,
which is the Jacobian factor for any change-of-variables on the disk
under `φ_a`.

Three headline theorems:

```lean
-- (1) Pointwise derivative formula:
-- (mobiusDisk a)'(z) = -(1 - conj(a) * a) / (1 - conj(a) * z)^2
-- = -(1 - ‖a‖²) / (1 - conj(a) z)^2     (Complex form, no `Real` cast)
-- This is the exact analytic derivative — the "complex Jacobian" of φ_a.
theorem hasDerivAt_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    HasDerivAt (mobiusDisk a)
      (-(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2) z
```

```lean
-- (2) Modulus identity (the real Jacobian factor):
-- ‖(mobiusDisk a)'(z)‖² = (1 - ‖a‖²)² / ‖1 - conj(a) z‖^4
-- This is the explicit positive real Jacobian factor that appears in any
-- Bergman A² change-of-variables `∫ ‖f(φ_a w)‖² · J dA(w) = ∫ ‖f(z)‖² dA(z)`.
theorem norm_sq_deriv_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    ‖-(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2‖ ^ 2
      = (1 - ‖a‖ ^ 2) ^ 2 / ‖1 - (starRingEnd ℂ) a * z‖ ^ 4
```

```lean
-- (3) `deriv` form of (1), packaged for downstream consumers that work
-- with `deriv` rather than `HasDerivAt`:
-- deriv (mobiusDisk a) z = -(1 - conj(a) * a) / (1 - conj(a) z)^2
-- Direct corollary of (1) via `HasDerivAt.deriv`.
theorem deriv_mobiusDisk
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    deriv (mobiusDisk a) z
      = -(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2
```

In this no-partial-formalization arm there is no `(15)` reduction or
Wang Section 2 hypothesis bundle. The move builds a self-contained
per-candidate Lean derivation on top of Mathlib (the Möbius derivative +
its Jacobian-modulus identity), composing Mathlib's standard
`HasDerivAt.div` / `HasDerivAt.const_sub` / `HasDerivAt.const_mul`
calculus chain plus a `field_simp` / `ring` / `Complex.normSq` algebra
chain. The only fixed target is the final theorem shape.

## Why

- **It is the smallest sprint that unlocks Bergman A² conformal
  invariance.** Bergman A² conformal invariance under `φ_a`
  (`bergmanNormSq (f ∘ φ_a) = bergmanNormSq f`) is the heaviest
  analytic toolkit Hayman / Korenblum / Wang use, and is the cleanest
  c-push route: it lets one Möbius-translate the inner-half radial
  dominance hypothesis at radius `c` to a translated inner-half at any
  point in `UnitDisk`, which in turn lets one bound the Bergman norm
  difference at the coefficient level. The full conformal-invariance
  result requires (a) the Möbius algebra primitives (sprint 020,
  done), (b) the Möbius derivative + Jacobian modulus (this sprint),
  and (c) a measure-theoretic change-of-variables `MeasureTheory.
  integral_image_eq_integral_abs_det_fderiv_smul` or
  `Complex.integral_comp_polarCoord_symm`-style transformation
  (follow-up sprint). This sprint pins (b), the missing analytic
  link.

- **The proofs are bounded and well-trodden.**
  - **(1) `hasDerivAt_mobiusDisk`.** `mobiusDisk a z = (a - z) / (1 -
    conj(a) z)`. Numerator `a - z` has derivative `-1` (via
    `HasDerivAt.const_sub` applied to `hasDerivAt_id`). Denominator
    `1 - conj(a) z` has derivative `-conj(a)` (via `HasDerivAt.
    const_sub` applied to `(hasDerivAt_id z).const_mul (conj a)`).
    Apply `HasDerivAt.div` with the non-vanishing hypothesis from
    sprint 020's `mobiusDisk_denom_ne_zero` (specialised to
    `‖z‖ < 1 ⇒ ‖z‖ ≤ 1` via `le_of_lt`). The quotient rule yields
    `((-1) * (1 - conj(a) z) - (a - z) * (-conj(a))) / (1 - conj(a) z)^2`,
    which simplifies algebraically (via `ring`) to
    `-(1 - conj(a) a) / (1 - conj(a) z)^2`. Mathlib API:
    `HasDerivAt.div`, `HasDerivAt.const_sub`, `HasDerivAt.const_mul`,
    `hasDerivAt_id`. ~80–120 lines.
  - **(2) `norm_sq_deriv_mobiusDisk`.** `‖-(1 - conj(a) a)‖² =
    ‖1 - conj(a) a‖² = ‖1 - ‖a‖²‖²` (since `conj(a) a = (‖a‖² : ℂ)`
    is a real number for `a : ℂ`, via `Complex.mul_conj` /
    `Complex.normSq_eq_conj_mul_self`). Then `‖1 - ‖a‖²‖² = (1 -
    ‖a‖²)²` since `1 - ‖a‖² ≥ 0` (because `‖a‖ < 1`). The denominator
    `‖(1 - conj(a) z)^2‖² = ‖1 - conj(a) z‖^4` via `norm_pow` plus
    `pow_pow_eq_pow_mul`. Combining:
    `‖num/denom‖² = ‖num‖² / ‖denom‖² = (1-‖a‖²)² / ‖1-conj(a)z‖^4`.
    Mathlib API: `norm_div`, `norm_neg`, `norm_pow`,
    `Complex.mul_conj`, `Complex.normSq_eq_conj_mul_self`,
    `Complex.norm_real`, `abs_of_nonneg`. ~80–150 lines.
  - **(3) `deriv_mobiusDisk`.** Direct corollary: apply
    `HasDerivAt.deriv` to (1). ~5 lines.

  **Total estimated line count: 200–350 lines.** Well within one
  Generator session.

- **All three are falsifiable in one Generator session.** The proofs
  use Mathlib's standard differential calculus and complex-norm
  algebra API. The generator has shipped sprint 016's `tsum`-level
  Hadamard, sprint 018's `HasFPowerSeriesAt.coeff_zero` identification,
  sprint 019's continuity-from-uniform-convergence proof, and sprint
  020's involution `field_simp`/`ring` chain — each exercises the same
  level of bookkeeping.

- **Mathlib API surface verified to exist** (planner spot-checked):
  - `HasDerivAt.div` —
    `Mathlib/Analysis/Calculus/Deriv/Inv.lean:171`,
    statement `(hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (hx : d x ≠ 0) → HasDerivAt (c/d) ((c'*d x - c x*d')/(d x)^2) x`.
  - `HasDerivAt.const_sub` —
    `Mathlib/Analysis/Calculus/Deriv/Add.lean:429`.
  - `HasDerivAt.const_mul` —
    `Mathlib/Analysis/Calculus/Deriv/Mul.lean:343`.
  - `AnalyticAt.deriv` —
    `Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:457` (for the
    upgrade from `HasDerivAt` to `deriv` if needed).

- **Why not pursue Bergman A² conformal invariance directly.** That
  requires (a) the Jacobian (this sprint) plus (b) the
  measure-theoretic change-of-variables on conformal maps. The
  change-of-variables step in Lean is non-trivial: it requires
  `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
  (which works on `ℝⁿ` with `fderiv`, not directly on `ℂ` with `deriv`),
  plus the bridge `‖(mobiusDisk a)'(z)‖² = |Jacobian of φ_a as a real
  map ℝ²→ℝ²|`, plus `MapsTo.image` reasoning to identify
  `(mobiusDisk a) '' UnitDisk = UnitDisk` (using sprint 020's
  involution + maps-to). Estimated 400–800 additional lines. Pinning
  the analytic Jacobian (this sprint) first lets the change-of-
  variables sprint be a clean composition.

- **Why not pursue Schwarz–Pick directly.** Schwarz–Pick needs the
  maximum modulus principle on UnitDisk plus a careful application
  of sprint 020's modulus identity. While elegant, the maximum
  modulus principle on the open unit disk is itself a non-trivial
  Mathlib API surface (`Complex.norm_le_norm_max_on_closure` or
  `Complex.disk_norm_le`), and Schwarz–Pick adds another algebraic
  layer on top. The Jacobian path is shorter and unlocks the larger
  c-push direction (Bergman A² conformal invariance).

- **Why not pursue the deferred general-interior-point sub-mean-value
  (sprint 018 Fallback A) instead.** That is independent and useful,
  but the Möbius chain is the higher-leverage direction: Bergman A²
  conformal invariance lets one Möbius-transport the entire `c =
  0.3554` baseline to any reference point, which directly attacks
  the c-push numerator (the inner-half radial dominance content).
  The sub-mean-value at general interior points is a one-point-
  pointwise primitive; conformal invariance is a global structural
  primitive.

- **Why not pursue the c-push attempt directly.** The c-push requires
  (a) a method for transferring outer-annulus pointwise dominance to
  coefficient-level dominance (the genuinely missing math), or (b) a
  Möbius transport argument that sidesteps the coefficient bridge.
  Both require infrastructure not yet in the workspace. Möbius
  Jacobian + future conformal invariance is option (b) infrastructure;
  this sprint is the next bounded step.

- **Why not pursue the sprint 014 trust-reduction proposal_001
  approval.** `proposal_001_replace_seed_with_inner_radial_dominance.md`
  is `pending` and gates that sprint. Until human approval, that
  direction is blocked. This sprint advances goal #1 (c-push
  scaffolding) instead and is independent of the proposal's status.

- **Generator's declared scope covers this.** `AGENT_BRIEF.md` lists
  *"`nlinarith` / `polyrith` / `field_simp` / `ring` chains hundreds
  of lines long"* and *"bridging pointwise modulus inequalities to
  boundary integrals"* and *"subharmonicity / mean-value arguments
  for `|f|²`"*. Theorem (1) is exactly a `HasDerivAt.div` plus
  `ring` chain. Theorem (2) is exactly a complex-norm algebra chain
  using `Complex.mul_conj`, `norm_pow`, and `pow_two_nonneg`-style
  arithmetic. Theorem (3) is a one-liner.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/MobiusDeriv.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,
  - imports `Mathlib`, `Proof.CandidateContract` (for `UnitDisk`),
    `Proof.MobiusDisk` (for `mobiusDisk` and
    `mobiusDisk_denom_ne_zero`).
  - exposes the three headline theorems (1) `hasDerivAt_mobiusDisk`,
    (2) `norm_sq_deriv_mobiusDisk`, (3) `deriv_mobiusDisk`.
  - All theorems must be `theorem` / `lemma`, never `axiom`, with
    no `sorry`. The proofs must be standalone against Mathlib (plus
    the two workspace imports above); they must not introduce any
    new workspace dependency.

  - **Implementation sketch for (1) `hasDerivAt_mobiusDisk`.**

    ```lean
    -- 1. HasDerivAt (fun z => a - z) (-1) z via
    --      HasDerivAt.const_sub a hasDerivAt_id.
    -- 2. HasDerivAt (fun z => 1 - (starRingEnd ℂ) a * z) (-(starRingEnd ℂ) a) z
    --    via HasDerivAt.const_sub 1 (hasDerivAt_id.const_mul (...)).
    -- 3. (1 - (starRingEnd ℂ) a * z) ≠ 0 by sprint 020's
    --    mobiusDisk_denom_ne_zero ha (le_of_lt hz).
    -- 4. Apply HasDerivAt.div with (1) and (2) and (3).
    -- 5. The quotient-rule output is
    --    ((-1) * (1 - conj(a) z) - (a - z) * (-conj(a))) / (1 - conj(a) z)^2.
    --    This simplifies (via `ring`) to
    --    -(1 - conj(a) a) / (1 - conj(a) z)^2.
    --    The simplification preserves the `HasDerivAt` shape via
    --    `convert`-with-`ring` or `HasDerivAt.congr_deriv` (the latter
    --    requires showing the two derivative values are equal).
    ```

  - **Implementation sketch for (2) `norm_sq_deriv_mobiusDisk`.**

    ```lean
    -- Goal: ‖-(1 - conj(a) a) / (1 - conj(a) z)^2‖² = (1-‖a‖²)²/‖1-conj(a)z‖^4
    -- Step 1: norm_div + norm_neg + norm_pow gives
    --   ‖num/denom^2‖² = (‖1-conj(a)a‖² · ‖1-conj(a)a‖²)/(‖1-conj(a)z‖²)^4
    --                  = ‖1-conj(a)a‖² · ‖1-conj(a)a‖² / ‖1-conj(a)z‖^4
    -- Wait, more precisely:
    --   ‖x/y^2‖² = (‖x‖/‖y^2‖)² = ‖x‖²/‖y^2‖² = ‖x‖²/(‖y‖²)² = ‖x‖²/‖y‖⁴.
    -- So we need ‖1 - conj(a)a‖² = (1-‖a‖²)².
    -- Step 2: conj(a) * a = ‖a‖² as a complex number.
    --   This is `Complex.mul_conj` (statement `(starRingEnd ℂ) a * a = (‖a‖² : ℂ)`)
    --   Wait, the actual Mathlib name is `Complex.normSq_eq_conj_mul_self`
    --   (statement `normSq a = (conj a * a).re`) or `Complex.mul_conj`
    --   (statement `a * conj a = ↑(normSq a)`). Use the right direction.
    -- Step 3: 1 - conj(a)*a = 1 - (‖a‖² : ℂ) = ((1 - ‖a‖²) : ℂ).
    -- Step 4: ‖((1 - ‖a‖²) : ℂ)‖ = |1 - ‖a‖²| = 1 - ‖a‖² (since ‖a‖ < 1).
    -- Step 5: ‖1 - conj(a)*a‖² = (1 - ‖a‖²)².
    -- Mathlib API: norm_div, norm_neg, norm_pow, Complex.mul_conj,
    -- Complex.norm_real (or `Complex.norm_of_real`), abs_of_nonneg.
    ```

  - **Implementation sketch for (3) `deriv_mobiusDisk`.**

    ```lean
    exact (hasDerivAt_mobiusDisk ha hz).deriv
    ```

- `ProofRefinement/Korenblum/Candidates/V21.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V21`, marked
  `-- @parent V20`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V20),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V20,
  - imports the same module set as V20 plus
    `ProofRefinement.Korenblum.Proof.MobiusDeriv`, so that the new
    module is part of V21's compile graph and is exercised by the
    build. No structural use of the new theorems in V21 itself is
    required (the consumer is a future c-push sprint).

- Update `ProofRefinement/Korenblum/lemma.toml`'s
  `[workspace_import_policy]` to admit
  `ProofRefinement.Korenblum.Proof.MobiusDeriv` from V21 (and from
  the new `Proof/MobiusDeriv.lean` itself, which imports
  `Proof.CandidateContract` and `Proof.MobiusDisk`). This is an
  in-scope policy edit to admit the newly created Lean-derived module
  — not a trust expansion (no new axiom or external library is added).

- No edits to V0/.../V20 or to existing `Proof/*.lean` files. No new
  axioms beyond the already-allowed `hKorenblum_published_3554`. No
  edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V21` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V21.lean` succeeds (the
   evaluator accepts V21 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V20; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/MobiusDeriv.lean`
   contains **at least theorems (1) and (2)** as `theorem`s (not
   `lemma`, not `axiom`, no `sorry`):
   - `hasDerivAt_mobiusDisk`,
   - `norm_sq_deriv_mobiusDisk`.

   Theorem (1)'s proof must genuinely call `HasDerivAt.div` (not
   sidestep via `AnalyticAt.deriv` plus an unfolded power-series
   expansion). Theorem (2)'s proof must genuinely call
   `Complex.mul_conj` (or `Complex.normSq_eq_conj_mul_self`) and
   reduce to a positive real arithmetic identity — not bypass the
   complex algebra.

4. The file ideally also contains theorem (3) `deriv_mobiusDisk`.
   **Fallback A** below specifies what to ship if (3) hits a
   `HasDerivAt.deriv` API friction (extremely unlikely; (3) is
   essentially a one-liner).

5. The new module `Proof.MobiusDeriv` must be **used**, even
   trivially, somewhere in V21's transitive compile graph (importing
   it from V21 is sufficient — it forces the module to compile as
   part of V21's build).

6. The headline theorem statements must be **internally consistent**
   with each other:
   - Theorem (3) follows from theorem (1) via `HasDerivAt.deriv`
     (standard composition).
   - Theorem (2) at `a = 0` reduces to `‖-1 / 1^2‖² = 1 = 1²/1` =
     `(1-0)²/1^4`, consistent.
   - Theorem (2) at `z = 0` reduces to `‖-(1 - conj(a)a)/1^2‖² =
     ‖1 - conj(a)a‖² = (1-‖a‖²)²`, consistent (this is the special
     case at the disk center).
   - Theorem (1) at `a = 0` reduces to `HasDerivAt (fun z => -z) (-1) z`
     since `mobiusDisk 0 z = -z` and the formula gives
     `-(1 - 0)/(1 - 0)² = -1`, consistent.

## Out of scope

- Edit older candidates (`V0.lean` through `V20.lean`) or the existing
  `Proof/*.lean` files (including `Proof/MobiusDisk.lean`).

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`,
  no new analytic axioms). If the proof is genuinely blocked on a
  missing Mathlib API, the Generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the Möbius derivative primitive that
  future c-push consumers will factor through.

- **Pursue Bergman A² conformal invariance.** That is the structurally
  larger follow-up sprint that consumes this primitive. Attempting
  both in one session would blow the time budget and require a
  measure-theoretic change-of-variables on `ℝ²` (treating `ℂ ≅ ℝ²`)
  that is itself a non-trivial Mathlib API surface.

- **Pursue Schwarz–Pick lemma.** Schwarz–Pick requires the maximum
  modulus principle on UnitDisk (a separate Mathlib API surface) and
  is a parallel direction to the Jacobian path. Pinning the Jacobian
  (this sprint) first leaves the Möbius chain in a strictly better
  state for either direction.

- **Pursue pseudohyperbolic distance.** Distance properties (symmetry,
  triangle inequality) follow from sprint 020's involution + a Schwarz
  -Pick bound — not from the Jacobian directly. They are a parallel
  follow-up.

- **Pursue the deferred general-interior-point sub-mean-value (sprint
  018 Fallback A).** Useful follow-up direction but orthogonal to
  this sprint's content.

## Time budget

≤ 75 minutes runtime. (Three theorems, ~200–350 lines total. Same
Mathlib API surface as sprint 020, with the addition of standard
differential-calculus lemmas (`HasDerivAt.div`, `HasDerivAt.const_sub`,
`HasDerivAt.const_mul`). The dominant cost is the algebraic
simplification in theorem (1)'s `convert ... using 1; ring` step and
the `Complex.mul_conj` algebra in theorem (2).)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. `HasDerivAt.div`'s output shape does not
  unify with the target form via `convert`/`ring`, or
  `Complex.mul_conj` rewrites in the wrong direction, or
  `Complex.norm_real`/`Complex.norm_ofReal` does not exist under that
  name): `STATUS=BLOCKED` with a precise note in `Experience.md`
  recording which Mathlib lemma was the obstruction and which
  approaches were tried (e.g. `HasDerivAt.div` direct vs
  `HasDerivAt.div_const` plus `HasDerivAt.const_div`, or
  `Complex.mul_conj` vs `Complex.normSq_eq_conj_mul_self`).

  **Fallback A** (theorem (3) `deriv_mobiusDisk` hits a
  `HasDerivAt.deriv` API friction — extremely unlikely): the Generator
  may instead ship only theorems (1) and (2), deferring (3) to a
  follow-up sprint. (Theorem (3) does not block any of the other two.)

  **Fallback B** (theorem (1) `hasDerivAt_mobiusDisk`'s `convert`-
  with-`ring` step fails because the `HasDerivAt.div` output algebra
  is more intricate than a single `ring` can close): the Generator
  may ship a strictly weaker **`HasDerivAt`-with-unsimplified-formula**
  form:

  ```lean
  theorem hasDerivAt_mobiusDisk_raw
      {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
      HasDerivAt (mobiusDisk a)
        (((-1) * (1 - (starRingEnd ℂ) a * z) - (a - z) * (-(starRingEnd ℂ) a))
          / (1 - (starRingEnd ℂ) a * z) ^ 2) z
  ```

  paired with an algebraic identity lemma:

  ```lean
  theorem mobiusDisk_deriv_simp
      {a z : ℂ} :
      ((-1) * (1 - (starRingEnd ℂ) a * z) - (a - z) * (-(starRingEnd ℂ) a))
        / (1 - (starRingEnd ℂ) a * z) ^ 2
      = -(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2
  ```

  proved by `field_simp` + `ring` (or just `ring` if the denominator
  cancels). The fallback is acceptable if the Generator records why
  the direct `convert`+`ring` form did not work in `Experience.md`.

  **Fallback C** (theorem (2) `norm_sq_deriv_mobiusDisk` hits a
  `Complex.mul_conj` direction friction): the Generator may instead
  ship a **`Complex.normSq` form**:

  ```lean
  theorem normSq_deriv_mobiusDisk
      {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
      Complex.normSq (-(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z)^2)
        = (1 - Complex.normSq a) ^ 2 / (Complex.normSq (1 - (starRingEnd ℂ) a * z)) ^ 2
  ```

  (which uses `Complex.normSq` throughout instead of `‖·‖²`). The
  fallback is acceptable if the Generator records in `Experience.md`
  why the `‖·‖²` form was deferred. Future consumers can bridge
  `Complex.normSq` to `‖·‖²` via `Complex.sq_abs` or
  `Complex.normSq_eq_norm_sq` (whichever Mathlib name is current).

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  — extremely unlikely for differential calculus on `ℂ`):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
