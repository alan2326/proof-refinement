# Sprint 020: Möbius disk automorphism `φ_a` — analyticity, self-map, involution, Schwarz–Pick modulus identity

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V19.lean`
**Target file**: `Candidates/V20.lean`
**Direction**: section2-proof / scaffolding-for-c-push (Möbius / pseudohyperbolic
primitive — the next analytic chain beyond the Bergman / Cauchy L² /
Hadamard / continuity stack of sprints 010–019. Sprint 019's contract
explicitly flagged this as the natural next direction: *"The Möbius
automorphism φ_a(z) = (z-a)/(1-conj(a)·z) and Bergman A² conformal
invariance are the heaviest analytic toolkit Hayman / Korenblum / Wang
use, and would unlock the cleanest c-push path — but that is a
structurally large derivation (multi-sprint)."* This sprint pins the
**first** Möbius primitive: the four core algebraic / analytic
properties of `φ_a` that every downstream Möbius / Schwarz–Pick /
pseudohyperbolic-distance result will factor through.)

## Goal

Ship one new derived module `Proof/MobiusDisk.lean` that pins a small
public surface for the unit-disk Möbius automorphism

```
φ_a(z) := (a - z) / (1 - conj(a) * z)
```

against `UnitDisk : Set ℂ` (the workspace's set-level disk, not Mathlib's
`Complex.UnitDisc` Subtype). The four headline theorems are:

```lean
-- (1) The denominator is non-vanishing on the closed unit disk for `a ∈ UnitDisk`.
-- This is the analytic gateway: every subsequent statement uses this to
-- justify division.
theorem mobiusDisk_denom_ne_zero
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0
```

```lean
-- (2) The key Schwarz–Pick algebraic / modulus identity:
-- `1 - ‖φ_a z‖² = (1 - ‖a‖²)(1 - ‖z‖²) / ‖1 - conj(a) z‖²`.
-- This is THE algebraic identity at the heart of every Möbius / pseudo-
-- hyperbolic argument on the unit disk. Direct consequence: `φ_a` maps
-- `UnitDisk` into `UnitDisk` (theorem (3) below).
theorem mobiusDisk_one_sub_normSq
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : ‖z‖ < 1) :
    1 - ‖mobiusDisk a z‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - (starRingEnd ℂ) a * z‖ ^ 2
```

```lean
-- (3) `φ_a` maps `UnitDisk` into `UnitDisk`. Direct consequence of (2).
theorem mobiusDisk_mapsTo
    {a : ℂ} (ha : a ∈ UnitDisk) :
    Set.MapsTo (mobiusDisk a) UnitDisk UnitDisk
```

```lean
-- (4) Involution: `φ_a (φ_a z) = z` for `z ∈ UnitDisk`. This is the
-- involution property that makes `φ_a` an automorphism (specifically
-- self-inverse) of the unit disk.
theorem mobiusDisk_involution
    {a z : ℂ} (ha : a ∈ UnitDisk) (hz : z ∈ UnitDisk) :
    mobiusDisk a (mobiusDisk a z) = z
```

```lean
-- (5) `φ_a` is analytic on `UnitDisk`. (Holomorphic-on-the-disk form.)
theorem mobiusDisk_analyticOn
    {a : ℂ} (ha : a ∈ UnitDisk) :
    AnalyticOn ℂ (mobiusDisk a) UnitDisk
```

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move builds a self-contained
per-candidate partial formalization on top of Mathlib (the Möbius unit-
disk automorphism's algebraic / analytic primitives), derived directly
from Mathlib's complex-analysis and analyticity APIs. The only fixed
target is the final theorem shape.

## Why

- **It is the smallest sprint that opens the Möbius / pseudohyperbolic
  chain.** Every Korenblum-style c-push argument in the literature
  (Hayman 1983, Korenblum 1982, Wang 2025) factors through Bergman A²
  conformal invariance under the Möbius automorphism `φ_a`. The
  workspace's existing 19 sprints have built up the Bergman A² /
  Cauchy L² / Hadamard / continuity toolkit, but **no Möbius primitive
  exists in this workspace**. Sprint 019's contract explicitly flagged
  Möbius / pseudohyperbolic machinery as the natural next direction
  beyond the Cauchy L² boundary bound. Without a Möbius primitive,
  every subharmonic / extremal-function argument has to re-derive the
  Schwarz–Pick algebraic identity inline, which is wasteful and
  obstructs c-push attempts. Pinning the four core properties as
  public lemmas is the natural single-session primitive.

- **The four properties are the *minimum* surface every downstream
  consumer needs.** A Schwarz–Pick lemma (`‖f(z₁) - f(z₂)‖ /
  ‖1 - conj(f(z₁))·f(z₂)‖ ≤ ‖z₁ - z₂‖ / ‖1 - conj(z₁)·z₂‖`) needs
  property (2). A pseudohyperbolic-distance triangle inequality needs
  property (4). A Bergman A² conformal-invariance proof needs
  properties (3) and (5). The four together are the natural Möbius
  primitive set; building them in one sprint avoids fragmenting the
  module.

- **The proofs are bounded and well-trodden.**
  - **(1) Denominator non-vanishing.** For `‖a‖ < 1` and `‖z‖ ≤ 1`,
    `‖conj(a) * z‖ = ‖a‖ * ‖z‖ ≤ ‖a‖ < 1`, so `1 - conj(a)*z ≠ 0` by
    `‖1 - conj(a)*z‖ ≥ 1 - ‖conj(a)*z‖ ≥ 1 - ‖a‖ > 0` (reverse
    triangle inequality + arithmetic). Mathlib API:
    `norm_sub_norm_le`, `Complex.norm_eq_abs`, `RCLike.norm_conj` (or
    `Complex.norm_conj`). ~20–40 lines.
  - **(2) Modulus identity.** Direct algebraic computation:
    `‖φ_a z‖² = ‖a-z‖² / ‖1-conj(a)z‖²`, then
    `‖a-z‖² = ‖a‖² - 2 Re(conj(a)z) + ‖z‖²` (via `Complex.normSq_sub`),
    `‖1-conj(a)z‖² = 1 - 2 Re(conj(a)z) + ‖a‖² ‖z‖²` (via
    `Complex.normSq_sub` and `‖conj(a)z‖² = ‖a‖²‖z‖²`). Then `1 -
    ‖φ_a z‖² = (‖1-conj(a)z‖² - ‖a-z‖²) / ‖1-conj(a)z‖²`, and the
    numerator simplifies algebraically to `(1-‖a‖²)(1-‖z‖²)` via
    `ring`. The whole computation is `Complex.normSq_sub` / `field_simp`
    / `ring`. ~80–150 lines (algebraic gymnastics).
  - **(3) Self-map.** From (2): for `‖a‖, ‖z‖ < 1`, the RHS is positive
    (positive numerator / positive denominator), so `1 - ‖φ_a z‖² > 0`,
    so `‖φ_a z‖ < 1`, i.e. `φ_a z ∈ UnitDisk`. ~30–50 lines.
  - **(4) Involution.** Direct algebraic:
    `φ_a(φ_a z) = (a - φ_a z) / (1 - conj(a) φ_a z)`,
    substitute `φ_a z = (a-z)/(1-conj(a)z)`, multiply numerator and
    denominator through by `(1 - conj(a)z)`, and simplify via
    `field_simp` / `ring`. The substitution requires (1) at both `z`
    and `φ_a z` to justify the division. ~80–120 lines (algebra).
  - **(5) Analyticity.** `mobiusDisk a` is a rational function whose
    denominator is non-vanishing on `UnitDisk` by (1). Mathlib API:
    `AnalyticOn.div` (or `analyticAt_inv`) plus the analyticity of
    polynomials in `z`. The denominator non-vanishing comes from (1)
    extended to `‖z‖ < 1` (which is a strict subset of `‖z‖ ≤ 1`).
    ~40–60 lines.

  **Total estimated line count: 250–420 lines.** Well within one
  Generator session.

- **Falsifiable in one Generator session.** All five proofs use
  Mathlib's standard complex-analysis API (`Complex.normSq_sub`,
  `Complex.norm_conj`, `RCLike.norm_conj`, `AnalyticOn.div`,
  `field_simp`, `ring`, `nlinarith`). The generator has shipped sprint
  016's tsum-level Hadamard, sprint 018's `HasFPowerSeriesAt.coeff_zero`
  identification, and sprint 019's continuity-from-uniform-convergence
  proof — each exercises the same level of algebraic / analytic
  bookkeeping as this sprint's targets. The expected line count is on
  the same order as sprints 015–019 (each landed at 300–600 lines).

- **Why not pursue the deferred general-interior-point sub-mean-value
  (sprint 018 Fallback A) instead.** That deferral is "transformation
  of an existing primitive, not a new analytical chain" (cf sprint
  019's *Why not pursue this*). The Möbius primitive is genuinely new
  analytical content. It is the natural next sprint after sprint 019's
  boundary Cauchy L² bound.

- **Why not pursue Schwarz–Pick directly.** The full Schwarz–Pick lemma
  on `UnitDisk` (`f : ℂ → ℂ` analytic with `‖f‖ < 1` on UnitDisk
  ⇒ `‖φ_{f(z)}(f(w))‖ ≤ ‖φ_z(w)‖`) requires the *maximum modulus
  principle* on UnitDisk (Mathlib: `Complex.norm_le_norm_max_on_closure`
  or `Complex.eq_const_of_disconnectedSet_of_le_const`). That is itself
  a non-trivial Mathlib API surface, plus the Möbius framework. The
  cleanest decomposition is: pin Möbius primitives (this sprint), then
  pin Schwarz–Pick on top in a follow-up sprint. Trying both in one
  session would blow the time budget.

- **Why not pursue Bergman A² conformal invariance directly.** That
  result (`bergmanNormSq (f ∘ φ_a) = bergmanNormSq f`) requires the
  full Möbius framework + change-of-variables on conformal maps + the
  Jacobian computation `|φ_a'(z)|² = (1-‖a‖²)² / ‖1-conj(a)z‖^4` +
  `MeasureTheory.integral_map_of_invertible` plumbing. Estimated
  multi-sprint. Sprint 020 pins the algebraic Möbius primitives;
  sprint 021+ pins the Jacobian and change-of-variables.

- **Why not pursue the c-push attempt directly via boundary Cauchy L²
  + inner-disk Bergman Parseval summation.** Sprint 019's contract
  flagged this as "structurally larger and requires careful summability
  bookkeeping at the boundary radius." A direct attempt without Möbius
  machinery runs into the same divergence the planner ultrathought
  through (the term `c²/(2(k+1)) · circleMeanSq g c` summed over k
  diverges). Möbius is the route that makes the c-push tractable.

- **Why not pursue the sprint 014 trust-reduction proposal_001
  approval.** `proposal_001_replace_seed_with_inner_radial_dominance.md`
  is `pending` and gates that sprint. Until human approval, that
  direction is blocked. This sprint advances goal #1 (c-push
  scaffolding) instead and is independent of the proposal's status.

- **Why not bridge to Mathlib's `Complex.UnitDisc` Subtype.** Mathlib's
  `Complex.UnitDisc` (in `Mathlib.Analysis.Complex.UnitDisc.Basic`)
  is a Subtype of `ℂ` with its own Möbius / Schwarz–Pick API. Bridging
  the workspace's `UnitDisk : Set ℂ` to that Subtype would give wholesale
  access to Mathlib's pre-built results, but is plumbing-heavy and
  produces lemmas at the Subtype level — every downstream consumer
  (which uses `f : ℂ → ℂ` on `UnitDisk : Set ℂ`) would have to bridge
  back. Building Möbius lemmas directly on `ℂ → ℂ` with `UnitDisk : Set ℂ`
  hypotheses produces the exact form downstream consumers will want.
  Mathlib's UnitDisc Subtype API can still be consumed inside the
  proofs (e.g., to source the Schwarz–Pick algebraic identity if it's
  pre-built), but the public surface is `Set`-level. This is the same
  design choice every prior `Proof/*.lean` module made.

- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Cauchy–
  Schwarz on boundary integrals"*, *"Parseval / boundary L²
  expansions"*, *"`nlinarith` / `polyrith` / `field_simp` / `ring`
  chains hundreds of lines long"*. The Möbius algebraic identity (2)
  is exactly a `field_simp` / `ring` chain a few hundred lines long.
  The analyticity (5) is exactly `AnalyticOn.div` composition. The
  involution (4) is exactly a `field_simp` / `ring` after substitution.
  The generator has shipped sprint 016's `tsum`-level Hadamard, sprint
  018's `HasFPowerSeriesAt.coeff_zero` identification, and sprint
  019's continuity-from-uniform-convergence proof — each exercises the
  same level of algebraic / analytic bookkeeping as this sprint's
  targets.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/MobiusDisk.lean`: **new file**, in
  the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract` (for `UnitDisk`).
    No other workspace imports are required (the sprint is
    independent of all the Bergman / circleMeanSq scaffolding).

  - exposes the definition

    ```lean
    /-- The Möbius unit-disk automorphism centered at `a ∈ UnitDisk`:
    `φ_a(z) = (a - z) / (1 - conj(a) * z)`. Self-inverse, holomorphic
    on `UnitDisk`, sends `UnitDisk` to `UnitDisk`. -/
    noncomputable def mobiusDisk (a z : ℂ) : ℂ :=
      (a - z) / (1 - (starRingEnd ℂ) a * z)
    ```

  - exposes the five headline theorems:
    1. `mobiusDisk_denom_ne_zero` (denominator non-vanishing on closed
       unit disk for interior `a`),
    2. `mobiusDisk_one_sub_normSq` (the Schwarz–Pick algebraic
       identity),
    3. `mobiusDisk_mapsTo` (`φ_a` is a self-map of `UnitDisk`),
    4. `mobiusDisk_involution` (`φ_a ∘ φ_a = id` on `UnitDisk`),
    5. `mobiusDisk_analyticOn` (`φ_a` is analytic on `UnitDisk`).

  - **Implementation sketch for (1) `mobiusDisk_denom_ne_zero`:**

    ```lean
    -- ‖conj(a) * z‖ = ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 = ‖a‖ < 1
    -- so 1 - conj(a)*z ≠ 0 by reverse triangle inequality:
    -- ‖1 - conj(a)*z‖ ≥ 1 - ‖conj(a)*z‖ > 0.
    intro h
    have h_norm : ‖(starRingEnd ℂ) a * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      have ha_lt : ‖a‖ < 1 := (mem_unitDisk_iff_norm_lt_one).mp ha
      calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by gcongr
        _ = ‖a‖ := mul_one _
        _ < 1 := ha_lt
    -- Now h says 1 - conj(a)*z = 0, so conj(a)*z = 1, but ‖conj(a)*z‖ = 1, contradiction.
    have : ‖(starRingEnd ℂ) a * z‖ = 1 := by
      rw [show (starRingEnd ℂ) a * z = 1 from by linear_combination -h]
      exact norm_one
    linarith
    ```

    A potentially shorter route: `sub_ne_zero.mpr` plus a direct
    proof that `(starRingEnd ℂ) a * z ≠ 1` via norm comparison.

  - **Implementation sketch for (2) `mobiusDisk_one_sub_normSq`:**

    ```lean
    -- Goal: 1 - ‖φ_a z‖² = (1-‖a‖²)(1-‖z‖²) / ‖1 - conj(a)z‖²
    -- Let D := 1 - conj(a)z. Then ‖D‖ ≠ 0 by (1).
    -- ‖φ_a z‖² = ‖a-z‖² / ‖D‖² = normSq(a-z) / normSq(D)
    -- So 1 - ‖φ_a z‖² = (normSq(D) - normSq(a-z)) / normSq(D).
    -- Compute:
    --   normSq(a-z) = normSq(a) - 2 Re(conj(a) z) + normSq(z)  (Complex.normSq_sub)
    --   normSq(D) = normSq(1) - 2 Re(conj(1) (conj(a) z)) + normSq(conj(a) z)
    --             = 1 - 2 Re(conj(a) z) + normSq(a) normSq(z)  (since normSq(conj(a)) = normSq(a))
    -- Subtracting:
    --   normSq(D) - normSq(a-z) = (1 - 2 Re(conj(a)z) + normSq(a) normSq(z))
    --                           - (normSq(a) - 2 Re(conj(a)z) + normSq(z))
    --                           = 1 - normSq(a) + normSq(a) normSq(z) - normSq(z)
    --                           = 1 - normSq(a) - normSq(z)(1 - normSq(a))
    --                           = (1 - normSq(a)) (1 - normSq(z))
    -- So 1 - ‖φ_a z‖² = (1 - normSq(a))(1 - normSq(z)) / normSq(D)
    --                 = (1 - ‖a‖²)(1 - ‖z‖²) / ‖D‖²    (Complex.sq_abs / norm_eq_sqrt_normSq)
    -- The whole thing is a `field_simp` + `ring` after the algebraic
    -- expansions are pinned.
    ```

    Key Mathlib API: `Complex.normSq_sub`, `Complex.normSq_eq_abs`
    (or `Complex.sq_abs : Complex.abs z ^ 2 = Complex.normSq z`),
    `Complex.norm_eq_abs`, `Complex.normSq_conj`, `Complex.normSq_mul`.

  - **Implementation sketch for (3) `mobiusDisk_mapsTo`:**

    ```lean
    -- For z ∈ UnitDisk, ‖z‖ < 1.
    -- By (2), 1 - ‖φ_a z‖² = (1-‖a‖²)(1-‖z‖²) / ‖1 - conj(a)z‖² > 0
    -- (numerator and denominator both positive).
    -- So ‖φ_a z‖² < 1, hence ‖φ_a z‖ < 1, hence φ_a z ∈ UnitDisk.
    ```

  - **Implementation sketch for (4) `mobiusDisk_involution`:**

    ```lean
    -- Compute φ_a(φ_a z):
    --   φ_a(φ_a z) = (a - φ_a z) / (1 - conj(a) φ_a z)
    -- Substitute φ_a z = (a-z) / D where D = 1 - conj(a)z:
    --   numerator: a - (a-z)/D = (aD - (a-z)) / D = (a - conj(a)z·a - a + z) / D
    --                          = (z - conj(a)za) / D = z(1 - conj(a)a) / D
    --   denominator: 1 - conj(a) · (a-z)/D = (D - conj(a)(a-z)) / D
    --                = (1 - conj(a)z - conj(a)a + conj(a)z) / D
    --                = (1 - conj(a)a) / D
    -- So φ_a(φ_a z) = z(1 - conj(a)a) / (1 - conj(a)a) = z.
    -- The whole proof is `field_simp` / `ring` after the `mobiusDisk`
    -- unfold, with denominator non-vanishing from (1) at both `z` and
    -- `φ_a z`.
    ```

    Key Mathlib API: `field_simp [mobiusDisk_denom_ne_zero ha _]` then
    `ring`.

  - **Implementation sketch for (5) `mobiusDisk_analyticOn`:**

    ```lean
    -- mobiusDisk a z = (a - z) / (1 - conj(a) * z) is a rational function.
    -- Numerator: AnalyticOn ℂ (fun z => a - z) UnitDisk via
    --   AnalyticOn.sub (analyticOn_const) (analyticOn_id)
    -- Denominator: AnalyticOn ℂ (fun z => 1 - conj(a) * z) UnitDisk via
    --   AnalyticOn.sub (analyticOn_const) (analyticOn_const.mul analyticOn_id)
    -- Denominator non-vanishing: by (1) extended to ‖z‖ < 1
    --   (which is the membership in UnitDisk).
    -- Apply AnalyticOn.div.
    ```

    Key Mathlib API: `AnalyticOn.sub`, `AnalyticOn.mul`, `AnalyticOn.div`,
    `analyticOn_const`, `analyticOn_id`. The `AnalyticOn.div` signature
    typically takes a non-vanishing hypothesis pointwise on the set.

  - **Auxiliary `private` helper recommended.** The membership bridge
    `mem_unitDisk_iff_norm_lt_one` from
    `Proof/InnerRadialReduction.lean` is `private` to that module.
    Re-derive inline as a private helper in `Proof/MobiusDisk.lean`:

    ```lean
    private theorem mem_unitDisk_iff_norm_lt_one {z : ℂ} :
        z ∈ UnitDisk ↔ ‖z‖ < 1 := by
      unfold UnitDisk
      rw [Metric.mem_ball, dist_zero_right]
    ```

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must be standalone against Mathlib (plus
    `Proof.CandidateContract`'s `UnitDisk` definition); they must
    not introduce any new workspace dependency.

- `ProofRefinement/Korenblum/Candidates/V20.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V20`, marked
  `-- @parent V19`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V19),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V19,
  - imports the same module set as V19 plus
    `ProofRefinement.Korenblum.Proof.MobiusDisk`, so that the new
    module is part of V20's compile graph and is exercised by the
    build. No structural use of the new theorems in V20 itself is
    required (the consumer is a future c-push sprint).

- No edits to `lemma.toml`. No edits to V0/.../V19 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V20` succeeds with
   no `sorry`, no `axiom` other than `hKorenblum_published_3554` plus
   the standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.

2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V20.lean` succeeds (the
   evaluator accepts V20 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V19; this is expected
   and not a failure of the sprint, but it must be reported truthfully
   in the run.

3. The file `ProofRefinement/Korenblum/Proof/MobiusDisk.lean`
   contains the noncomputable `def mobiusDisk` (with the precise body
   `(a - z) / (1 - (starRingEnd ℂ) a * z)`) and **at least theorems
   (1), (2), (3), (5)** as `theorem`s (not `lemma`, not `axiom`, no
   `sorry`):

   - `mobiusDisk_denom_ne_zero`
   - `mobiusDisk_one_sub_normSq`
   - `mobiusDisk_mapsTo`
   - `mobiusDisk_analyticOn`

   The proof of (2) must genuinely call `Complex.normSq_sub` (or
   `Complex.normSq_apply` / `Complex.norm_sub` / equivalent normSq
   API) and a `field_simp` + `ring` chain — not bypass via direct
   computation or via `nlinarith` on opaque terms.

4. The file ideally also contains theorem (4)
   `mobiusDisk_involution`. **Fallback A** below specifies what to
   ship if the involution algebra hits a friction.

5. The new module `Proof.MobiusDisk` must be **used**, even
   trivially, somewhere in V20's transitive compile graph (importing
   it from V20 is sufficient — it forces the module to compile as part
   of V20's build).

6. The headline theorem statements must be **internally consistent**
   with each other and with the workspace:
   - Theorem (3) at `a = 0` reduces to: `mobiusDisk 0 z = -z` (since
     `(0 - z)/(1 - 0) = -z`), and `‖-z‖ = ‖z‖ < 1` for `z ∈ UnitDisk`,
     which is consistent. (Sanity check; no theorem to ship.)
   - Theorem (4) at `a = 0` reduces to `mobiusDisk 0 (mobiusDisk 0 z) =
     mobiusDisk 0 (-z) = z`, consistent. (Sanity check; no theorem to
     ship.)
   - Theorem (2) at `a = 0` reduces to `1 - ‖z‖² = 1 · (1-‖z‖²) / 1 =
     1 - ‖z‖²`, consistent. (Sanity check; no theorem to ship.)
   - Theorem (3) is a strict consequence of theorem (2) (positive
     RHS ⇒ `‖φ_a z‖ < 1`), and the proof must factor through (2).
     This is enforced by the proof structure, not by an additional
     theorem.

## Out of scope

- Edit older candidates (`V0.lean` through `V19.lean`) or the existing
  `Proof/*.lean` files. In particular, do **not** lift the `private`
  `mem_unitDisk_iff_norm_lt_one` from `Proof/InnerRadialReduction.lean`
  — re-derive inline as a private helper.

- Change the final theorem statement or `c_value`.

- Add a free-floating new axiom (no second `hKorenblum_published_X`,
  no new analytic axioms). If the proof is genuinely blocked on a
  missing Mathlib API, the Generator must `STATUS=BLOCKED` with the
  precise obstruction, **not** axiomatize.

- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the Möbius primitive that future c-push
  consumers will factor through.

- Edit `lemma.toml` (no policy expansion in this sprint; the
  proposal_001 trust-reduction edit is gated on human approval).

- **Pursue Schwarz–Pick lemma** (`f` analytic with `‖f‖ < 1` on
  UnitDisk ⇒ `‖φ_{f(z)}(f(w))‖ ≤ ‖φ_z(w)‖`). That is a strictly
  larger result requiring the maximum modulus principle on UnitDisk.
  Sprint 020 pins the algebraic Möbius primitives; Schwarz–Pick is a
  follow-up sprint.

- **Pursue pseudohyperbolic distance** (`ρ(a, b) := ‖φ_a b‖`) and its
  triangle inequality. That follows easily from theorem (4)
  (involution) plus a Schwarz–Pick bound, but is structurally a
  follow-up.

- **Pursue Bergman A² conformal invariance** (`bergmanNormSq (f ∘ φ_a)
  = bergmanNormSq f`). That requires the Jacobian identity
  `|φ_a'(z)|² = (1-‖a‖²)² / ‖1-conj(a)z‖^4` plus the change-of-
  variables on `MeasureTheory`, which is structurally a follow-up
  sprint.

- **Pursue the c-push attempt directly via Möbius transport.** That is
  the structurally larger follow-up sprint that consumes this
  primitive. Attempting both in one session would blow the time
  budget.

- **Pursue the deferred general-interior-point sub-mean-value (sprint
  018 Fallback A).** That is a useful follow-up direction but is
  orthogonal to this sprint's content and would push the time budget.

## Time budget

≤ 90 minutes runtime. (Five theorems on a Möbius unit-disk
automorphism, ~250–420 lines total. The same Mathlib API surface as
sprints 015–019. The dominant cost is the algebraic computation in
theorem (2), which is a ~80–150 line `field_simp`/`ring` chain after
the `Complex.normSq_sub` expansion.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.

- Blocked within scope (e.g. Mathlib's `AnalyticOn.div` has an
  unexpected hypothesis form, or `Complex.normSq_sub` does not unify
  with the expected algebraic shape, or the involution `field_simp`
  hits a denominator-non-vanishing friction at the second `φ_a`
  application): `STATUS=BLOCKED` with a precise note in
  `Experience.md` recording which Mathlib lemma was the obstruction
  and which approaches were tried (`AnalyticOn.div` vs `analyticAt_inv`
  vs explicit power-series expansion for theorem (5);
  `Complex.normSq_sub` vs `Complex.norm_sub_sq` for theorem (2)).

  **Fallback A** (theorem (4) involution is too algebraically intricate
  in one session): the Generator may instead ship only theorems (1),
  (2), (3), (5), deferring (4) to a follow-up sprint. The fallback is
  acceptable if and only if the Generator records in `Experience.md`
  why (4) was deferred (e.g. which `field_simp` step had the unexpected
  shape, whether the issue was the denominator non-vanishing or the
  numerator simplification). Note: theorem (4) does not block any of
  the other four, so this is a clean partial fallback.

  **Fallback B** (theorem (2) modulus identity hits a `Complex.normSq`
  / `Complex.norm` mismatch that does not resolve via `Complex.sq_abs`
  / `Complex.norm_eq_abs`): the Generator may instead ship a strictly
  weaker **`< 1` form** of theorem (2):

  ```lean
  theorem mobiusDisk_norm_lt_one
      {a z : ℂ} (ha : a ∈ UnitDisk) (hz : z ∈ UnitDisk) :
      ‖mobiusDisk a z‖ < 1
  ```

  proved via the algebraic comparison `‖a-z‖ < ‖1 - conj(a) z‖` (which
  is the strict form of the modulus identity). The fallback is
  acceptable if and only if the Generator records in `Experience.md`
  why the full identity was deferred. (Note: theorem (3) of this
  sprint is identical in content to this fallback theorem, so this
  fallback collapses (2) into (3); theorems (1), (4), (5) are
  unaffected.)

  **Fallback C** (theorem (5) analyticity hits a Mathlib `AnalyticOn`
  composition friction, e.g. `AnalyticOn.div` does not exist or has
  an unexpected hypothesis form): the Generator may instead ship a
  strictly weaker **`DifferentiableOn` form**:

  ```lean
  theorem mobiusDisk_differentiableOn
      {a : ℂ} (ha : a ∈ UnitDisk) :
      DifferentiableOn ℂ (mobiusDisk a) UnitDisk
  ```

  via `DifferentiableOn.div`. The fallback is acceptable if and only
  if the Generator records in `Experience.md` why the `AnalyticOn`
  form was deferred and the `DifferentiableOn` form is genuinely
  Lean-pinned. (Future c-push consumers can bridge `DifferentiableOn`
  to `AnalyticOn` on open sets via `DifferentiableOn.analyticOn` if
  needed.)

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change, or a Mathlib
  primitive that requires a workspace-import-policy edit):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
