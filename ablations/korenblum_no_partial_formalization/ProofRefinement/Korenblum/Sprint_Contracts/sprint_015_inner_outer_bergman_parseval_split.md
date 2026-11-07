# Sprint 015: inner-disk / outer-annulus Bergman A² Parseval expansions

**Created**: 2026-05-07 by Planner
**Parent candidate**: `Candidates/V14.lean`
**Target file**: `Candidates/V15.lean`
**Direction**: section2-proof / scaffolding-for-c-push (Lean-derive the
**half-disc** Bergman Parseval expansions: separate, coefficient-level
`tsum` identities for `∫_{innerDisk c} ‖f‖² dA` and
`∫_{outerAnnulus c} ‖f‖² dA`. This is the smallest sprint that exposes a
**`c`-dependent** coefficient-level handle on the contract's two halves —
the missing analytic primitive every honest c-push consumer must factor
through, and a strict refinement of sprint 011's whole-disc Parseval
identity.)

## Goal

Lift sprint 011's whole-disc Bergman Parseval identity
`bergmanNormSq f = ∑' k, (π/(k+1)) * ‖a_k‖²` to the **two halves of the
inner/outer annulus split** at radius `c`:

```lean
theorem outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo c 1 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in outerAnnulus c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * (1 - c ^ (2 * k + 2))
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2

theorem innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn
        (fun p : ℝ × ℝ => p.1 * ‖f (Complex.polarCoord.symm p)‖ ^ 2)
        (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod volume)) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      = ∑' k : ℕ,
          (Real.pi / ((k : ℝ) + 1)) * c ^ (2 * k + 2)
            * ‖(cauchyPowerSeries f 0 R).coeff k‖ ^ 2
```

In a new file `Proof/AnnulusBergmanParseval.lean`. The proof structure is a
direct mirror of sprint 011's `bergmanNormSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`,
but with the radial integration restricted to the half-interval `Ioo c 1`
(outer) or `Ioc 0 c` (inner). Concretely: replace
`bergmanNormSq_radial_polar` with sprint 003's
`outerAnnulus_norm_sq_polar` / `innerDisk_norm_sq_polar`, and replace the
per-term radial integral
`∫ r in Ioo 0 1, (2π · ‖a_k‖²) · r^(2k+1) dr = π/(k+1) · ‖a_k‖²`
with the half-interval evaluations

```
∫ r in Ioo c 1, r^(2k+1) dr = (1 - c^(2k+2)) / (2k + 2)
∫ r in Ioc 0 c, r^(2k+1) dr = c^(2k+2) / (2k + 2)
```

both via `intervalIntegral.integral_pow`. Multiplied by the `2π · ‖a_k‖²`
prefactor, these collapse to the headline
`(π/(k+1)) (1 - c^(2k+2)) ‖a_k‖²` and `(π/(k+1)) c^(2k+2) ‖a_k‖²`.

We also expose a **termwise comparison consumer** for the inner half:

```lean
theorem innerDisk_bergmanNormSq_termwise_mono
    {f g : ℂ → ℂ} (hf : AnalyticOn ℂ f UnitDisk) (hg : AnalyticOn ℂ g UnitDisk)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {R : ℝ≥0} (hR_pos : 0 < (R : ℝ)) (hR_lt : (R : ℝ) < 1)
    (hf_polar : IntegrableOn ... (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi) ...)
    (hg_polar : IntegrableOn ... (Set.Ioo (0 : ℝ) c ×ˢ Set.Ioo (-Real.pi) Real.pi) ...)
    (h_coeff : ∀ k : ℕ,
        ‖(cauchyPowerSeries f 0 R).coeff k‖
          ≤ ‖(cauchyPowerSeries g 0 R).coeff k‖) :
    (∫ z in innerDisk c, ‖f z‖ ^ 2 ∂(volume : Measure ℂ))
      ≤ ∫ z in innerDisk c, ‖g z‖ ^ 2 ∂(volume : Measure ℂ)
```

via `tsum_le_tsum` over the per-term inequality
`(π/(k+1)) c^(2k+2) ‖a_k‖² ≤ (π/(k+1)) c^(2k+2) ‖b_k‖²` (each multiplier
nonnegative).

The same shape `outerAnnulus_bergmanNormSq_termwise_mono` is exposed
symmetrically; both consumers are direct analogues of sprint 011's
`bergmanNormSq_termwise_mono`.

V15 ships with `c_value = 3554/10000` unchanged from V14 and the same seed
axiom `hKorenblum_published_3554`. The new theorems are included in V15's
build graph via import, and provide the missing analytic primitive for
every coefficient-level c-push consumer.

In this no-partial-formalization arm there is no `(15)` reduction or Wang
Section 2 hypothesis bundle. The move builds a self-contained per-candidate
partial formalization on top of Mathlib (the inner/outer Bergman Parseval
expansion, derived directly from sprint 003's polar pullback halves, sprint
010's circle-mean Parseval, and sprint 011's whole-disc Parseval). The only
fixed target is the final theorem shape.

## Why

- **It is the smallest sprint that exposes a c-dependent coefficient-level
  handle.** Sprint 011's whole-disc Bergman Parseval identity loses the
  `c` parameter (every term gets weight `π/(k+1)` with no `c`-dependence).
  The c-push goal of AGENT_BRIEF (#1) requires comparing the inner half
  `bergmanNormSq` of `f` and `g` *as a function of `c`*. The half-disc
  expansions of this sprint are the natural ground form: each term is
  weighted `(π/(k+1)) · c^(2k+2)` (inner) or `(π/(k+1)) · (1 - c^(2k+2))`
  (outer), with explicit `c`-dependence that any c-push must consume.

- **It is a strict refinement of sprint 011, not a parallel re-derivation.**
  The whole-disc identity factors through the inner+outer split:
  `(π/(k+1)) c^(2k+2) + (π/(k+1)) (1 - c^(2k+2)) = π/(k+1)`, term by term.
  This sprint's two theorems should sum to sprint 011's identity (via
  `setIntegral_union` plus `tsum_add`, both already shipped or trivially
  available); the `c → 1⁻` and `c → 0⁺` boundary cases are sanity checks.

- **The proof is bounded.** The radial pullback halves
  `outerAnnulus_norm_sq_polar` and `innerDisk_norm_sq_polar` (sprint 003)
  already convert the half-disc integrals to `∫ r ∈ Ioo c 1, circleMeanSq f r * r`
  and `∫ r ∈ Ioc 0 c, circleMeanSq f r * r`. Sprint 010's
  `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk` gives
  the canonical per-`r` Parseval. Sprint 011's swap-`∫`-and-`∑'` machinery
  (`MeasureTheory.integral_tsum_of_summable_integral_norm`) carries
  through verbatim with the half-interval restriction. The only delta
  versus sprint 011 is the per-term integral evaluation:
  `∫ r in Ioo c 1, r^(2k+1) dr = (1 - c^(2k+2))/(2k+2)` and
  `∫ r in Ioc 0 c, r^(2k+1) dr = c^(2k+2)/(2k+2)`, both via
  `intervalIntegral.integral_pow` plus
  `intervalIntegral.integral_of_le` and `integral_Ioc_eq_integral_Ioo`
  (the conversions between `Ioc` and `Ioo` integrals on a measure-zero
  endpoint, already exercised in sprint 011's proof).

- **It is genuinely useful for c-push.** Once the half-disc expansions
  are pinned, the inner-half Bergman comparison
  `bergmanNormSq_innerDisk f c ≤ bergmanNormSq_innerDisk g c` reduces to
  a *weighted termwise inequality* over the Cauchy-coefficient norms,
  with weights `(π/(k+1)) c^(2k+2)` that decay rapidly as `k → ∞`. This
  opens the direct route Korenblum-style: a c-push at the function level
  becomes a `c`-dependent termwise inequality at the coefficient level.
  The sprint does **not** attempt this c-push; it pins the primitive
  every c-push must factor through.

- **Falsifiable in one Generator session.** Sprint 011 shipped the harder
  whole-disc analogue in one session and is well-documented in
  `Experience.md`. This sprint is mechanically the same proof structure
  with two surface changes (radial domain `Ioo 0 1 → Ioo c 1` / `Ioc 0 c`
  and per-term integral evaluation). The generator has the full
  vocabulary of `intervalIntegral.integral_pow`,
  `MeasureTheory.integral_tsum_of_summable_integral_norm`, and
  `setIntegral_mono_on` already exercised across sprints 011–013. No
  new Mathlib API is required.

- **Why not pursue a direct c-push.** Pushing `c` past `0.3554` requires
  a *new analytical chain* — specifically a coefficient-level inequality
  that holds for the contract's hypothesis class. This chain is not yet
  available even at the algebraic level (the contract gives outer-annulus
  pointwise dominance, which is not sufficient for coefficient-norm
  domination — counterexample `f = z, g = 1` documented in sprint 011).
  Without the half-disc Parseval expansion, no c-push has a coefficient
  scaffold to reach for. This sprint pins that scaffold.

- **Why not Hardy's convexity (log-convexity of `circleMeanSq f r`).**
  Hardy's convexity is a single-function tool that bounds growth of one
  function's circle mean. The Korenblum statement is *cross-function*
  (`f` vs `g`), and Hardy's convexity does not directly produce a
  cross-function comparison. The half-disc Parseval expansion of this
  sprint is also single-function but is *cross-function-ready*: the
  coefficient-level termwise comparison consumer
  `innerDisk_bergmanNormSq_termwise_mono` is the natural cross-function
  shape. Hardy's convexity is a plausible later sprint, after the
  half-disc expansion is pinned.

- **Why not pursue proposal_001 follow-up.**
  `proposal_001_replace_seed_with_inner_radial_dominance.md` is `pending`
  and gates the V15 trust-reduction sprint. Until human approval, the
  trust-reduction direction is blocked. This sprint advances goal #1
  (c-push scaffolding) instead, and is independent of the proposal's
  status. If the proposal is approved during this sprint's run, the
  *next* sprint can be the trust-reduction one (renumbered to match).

- **Generator's declared scope covers this.** AGENT_BRIEF lists *"Lebesgue-
  integral monotonicity on annulus regions"*, *"termwise summability and
  `tsum`-level rearrangements"*, and *"Parseval / boundary L² expansions
  on analytic functions"*. The sprint is precisely a Bergman A²
  Parseval expansion on annulus regions. The generator has shipped sprint
  011 (the whole-disc case) and sprint 014 (the contract-shape lift); this
  sprint is bounded between them in derivation cost.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/AnnulusBergmanParseval.lean`: **new
  file**, in the `ProofRefinement.Korenblum` namespace,

  - imports `Mathlib`, `Proof.CandidateContract`, `Proof.PolarBergman`,
    `Proof.AnnulusBergman`, `Proof.RadialBergman`, `Proof.AnalyticParseval`,
    `Proof.CircleMeanRadial`, `Proof.BergmanParseval` (the same module set
    as `Proof.BergmanParseval`, plus that file itself, since the new
    file's per-term integral evaluation may reuse / parallel sprint 011's
    `parsevalRadialTerm` private machinery in spirit, though the Mathlib
    primitives are sufficient and the new file may stand alone),

  - exposes the four headline theorems above:
    - `outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`,
    - `innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries`,
    - `outerAnnulus_bergmanNormSq_termwise_mono`,
    - `innerDisk_bergmanNormSq_termwise_mono`.

  - **Implementation sketch (mirror of sprint 011 with two surface deltas):**
    For the outer half (the inner half is symmetric):
    1. Apply `outerAnnulus_norm_sq_polar` (sprint 003) to fold into
       `∫ r in Ioo c 1, circleMeanSq f r * r`.
    2. For each `r ∈ Ioo c 1`, apply
       `circleMeanSq_eq_tsum_cauchyPowerSeries_of_analyticOn_unitDisk`
       (sprint 010) at `R'(r) := ⟨(r+1)/2, _⟩`, then
       `cauchyPowerSeries_coeff_norm_radius_invariant` (sprint 011's (1))
       to canonicalise to the chosen `R`.
    3. Use `MeasureTheory.integral_tsum_of_summable_integral_norm` to
       swap `∫` and `∑'` over the half-interval `Ioo c 1` (the same
       lemma as sprint 011, with the swap domain restricted; summability
       of `fun k => (π/(k+1)) * (1 - c^(2k+2)) * ‖a_k‖²` follows from
       sprint 011's whole-disc summability via the bound
       `(π/(k+1)) * (1 - c^(2k+2)) ≤ (π/(k+1))`, plus
       `Summable.of_nonneg_of_le`).
    4. The per-term integral is
       `∫ r in Ioo c 1, (2π · ‖a_k‖²) * r^(2k+1) dr
          = (2π · ‖a_k‖²) * ∫ r in Ioo c 1, r^(2k+1) dr
          = (2π · ‖a_k‖²) * ((1 - c^(2k+2)) / (2k + 2))
          = (π/(k+1)) * (1 - c^(2k+2)) * ‖a_k‖²`,
       via `integral_const_mul`, `integral_Ioc_eq_integral_Ioo`,
       `intervalIntegral.integral_of_le` (or `intervalIntegral.integral_pow`
       directly with the bounds `c ≤ 1`), and final algebraic cleanup
       through `field_simp` + `ring` (note that `2k+2 = 2(k+1)` so the
       `1/(2k+2)` cancels with `2` to leave `1/(k+1)`; this `ring`
       closure is sprint 011's pattern).

    For the inner half, replace `Ioo c 1` with `Ioc 0 c` everywhere, and
    `(1 - c^(2k+2))` with `c^(2k+2)`. The radial pullback for the inner
    half is `innerDisk_norm_sq_polar` (sprint 003), which integrates over
    `Ioo 0 c`. Note: the Lean form of `innerDisk_norm_sq_polar` integrates
    over `Ioo 0 c` (open), not `Ioc 0 c` (half-open), per sprint 003's
    statement — the boundary at `r = c` is measure-zero. The sprint may
    use `Ioo 0 c` throughout the inner-half proof for cleanliness.
    `circleMeanSq f c` is included in the inner half by
    `outerAnnulus_norm_sq_polar`'s `Ioo c 1` boundary at `r = c` being
    excluded, so the inner+outer split is exact.

  - All theorems must be `theorem` / `lemma`, never `axiom`, with no
    `sorry`. The proofs must genuinely reuse sprint 003 / sprint 010 /
    sprint 011's public theorems — *not* bypass via re-derivation.

- `ProofRefinement/Korenblum/Candidates/V15.lean`: **new file** in
  namespace `ProofRefinement.Korenblum.Candidates.V15`, marked
  `-- @parent V14`,
  - `def c_value : ℝ := 3554 / 10000` (unchanged from V14),
  - re-declares `axiom hKorenblum_published_3554 : ValidKorenblumBound
    ((3554 : ℝ) / 10000)` (the only allowed seed axiom),
  - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
    proved via the seed axiom exactly as in V14,
  - imports the same module set as V14 plus
    `ProofRefinement.Korenblum.Proof.AnnulusBergmanParseval`, so that the
    new module is part of V15's compile graph and is exercised by the
    build. No structural use of the new theorems in V15 itself is
    required.

- No edits to `lemma.toml`. No edits to V0/.../V14 or to existing
  `Proof/*.lean` files. No new axioms beyond the already-allowed
  `hKorenblum_published_3554`. No edit to `Proposals/`.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V15` succeeds with no
   `sorry`, no `axiom` other than `hKorenblum_published_3554` plus the
   standard Lean / `Classical.choice` / `propext` / `Quot.sound` /
   `Lean.ofReduceBool` / `Lean.trustCompiler` axioms.
2. `bash scripts/korenblum_eval_candidate.sh
   ProofRefinement/Korenblum/Candidates/V15.lean` succeeds (the evaluator
   accepts V15 as a well-formed candidate). The score
   `c_value = 3554/10000` is **unchanged** from V14; this is expected and
   not a failure of the sprint, but it must be reported truthfully in
   the run.
3. The file `ProofRefinement/Korenblum/Proof/AnnulusBergmanParseval.lean`
   contains four `theorem`s (or `lemma`s) with the names and shapes
   listed above — the two Parseval expansions and the two termwise
   comparison consumers. All four must be `theorem` / `lemma`, never
   `axiom`, with no `sorry`. The proofs must genuinely call sprint 003's
   `outerAnnulus_norm_sq_polar` / `innerDisk_norm_sq_polar` and sprint
   010 / sprint 011's existing identities — not bypass via direct
   re-derivation of those identities.
4. The new module `Proof.AnnulusBergmanParseval` must be **used**, even
   trivially, somewhere in V15's transitive compile graph (importing
   it from V15 is sufficient — it forces the module to compile as part
   of V15's build).
5. The four theorem statements must be **internally consistent** with
   sprint 011's whole-disc Parseval identity: i.e., for every
   `c ∈ (0, 1)` and every `f` satisfying the relevant hypotheses,
   `outerAnnulus_bergmanNormSq f c + innerDisk_bergmanNormSq f c =
   bergmanNormSq f` (which is `setIntegral_union` of sprint 002, already
   shipped). The sprint does *not* need to ship the explicit
   `setIntegral_union` consistency check as a theorem, but the four
   theorem statements must be such that this identity holds *up to*
   `tsum_add` / `tsum_distrib` (the algebra
   `(1 - c^(2k+2)) + c^(2k+2) = 1` makes this trivial when both
   `tsum`s exist).

## Out of scope

- Edit older candidates (`V0.lean` through `V14.lean`) or the existing
  `Proof/*.lean` files.
- Change the final theorem statement or `c_value`.
- Add a free-floating new axiom (no second `hKorenblum_published_X`, no
  new analytic axioms, no `hWang_inner_radial_dominance_3554`). If the
  proof is genuinely blocked on a missing Mathlib API, the generator
  must `STATUS=BLOCKED` with the precise obstruction, **not**
  axiomatize.
- Push `c_value` above `3554/10000`. This sprint does not touch the
  numerical bound; it builds the half-disc Parseval primitive that
  every future c-push consumer will factor through.
- Edit `lemma.toml` (no policy expansion in this sprint; the
  proposal_001 trust-reduction edit is the next sprint's job, gated on
  human approval of the proposal).
- Pursue Hardy's convexity / log-convexity of `circleMeanSq`. That is
  a plausible follow-up sprint after the half-disc Parseval is pinned;
  it is **not** part of this sprint.
- Attempt the cross-function inner-radial dominance derivation. This
  sprint is *single-function* (each theorem is parametric in one `f`,
  with the comparison consumer specializing to two functions sharing a
  coefficient-norm bound). Cross-function inner-radial dominance from
  outer-annulus pointwise domination is the genuine Korenblum content
  and is **not** in scope here.

## Time budget

≤ 90 minutes runtime. (This is comparable to sprint 011, which shipped the
whole-disc Parseval identity in one bounded session. The half-disc shape
is materially simpler in some places — no `R'(r) := (r+1)/2` interior
boundary needed for the outer half, since `r > c > 0` already — and
identical in others.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`

- Blocked within scope (e.g. the half-interval `intervalIntegral.integral_pow`
  evaluation produces an algebraic form the generator cannot collapse to
  `(1 - c^(2k+2))/(2k+2)`, or the `MeasureTheory.integral_tsum_of_summable_integral_norm`
  swap on the half-interval `Ioo c 1` requires an extra summability
  hypothesis the generator cannot discharge — most likely the per-term
  integrability of `fun r => (2π · ‖a_k‖²) * r^(2k+1)` on `Ioo c 1`,
  which should follow from sprint 011's `parsevalRadialTerm_integrable`
  via `IntegrableOn.mono_set Set.Ioo_subset_Ioo` — but the generator
  may need to expose a non-`private` analogue of the sprint 011 helper
  if the `private` keyword blocks reuse):
  `STATUS=BLOCKED` with a precise note in `Experience.md` recording
  which Mathlib lemma was the obstruction and which approaches were
  tried (`intervalIntegral.integral_pow` vs `integral_Ioc_eq_integral_Ioo`
  + `intervalIntegral.integral_of_le` vs manual `setIntegral_congr_fun`
  to a known antiderivative).

  **Fallback form** (if the four-theorem ship is too ambitious in one
  session): the generator may instead ship only the two **Parseval
  expansions** (`outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`
  and `innerDisk_bergmanNormSq_eq_tsum_cauchyPowerSeries`), deferring
  the two `_termwise_mono` consumers to a follow-up sprint. The fallback
  is acceptable if and only if the generator records in `Experience.md`
  why the consumers were deferred, and the two Parseval expansions are
  still genuinely Lean-pinned (no `sorry`, no `axiom`).

  **Second fallback form** (if even the two Parseval expansions are too
  ambitious): the generator may ship just the **outer half**
  (`outerAnnulus_bergmanNormSq_eq_tsum_cauchyPowerSeries`), since the
  outer half has cleaner algebra (`r > c > 0` everywhere on the
  integration domain, no boundary-at-0 wart). The inner half is then
  deferred to a follow-up sprint. Same `Experience.md` recording rule
  applies.

- Needs human trust expansion (e.g. a genuinely missing Mathlib lemma
  that justifies a new axiom or import-policy change):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
