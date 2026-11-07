# Sprint 070: Ship the series-level bridge `liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ` (under `α² < 1` and per-mode summability) as a per-candidate derived-theorem file `Candidates/V55/LiftSeriesBridge.lean`, then ship V55 tied to V54 with the new theorem exercised in a side lemma — the natural composition of V54's per-`k` lift identity into the series-level workspace structure

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V54.lean` (current high-water mark, `c_value = 7129/20000 = 0.35645` via the literal-(15) HP oracle channel; first per-candidate derived-theorem `Candidates/V53/ThetaStep.lean` shipped sprint 068; second per-candidate derived-theorem `Candidates/V54/LiftIdentity.lean` shipped sprint 069 — pure complex algebra on `ℕ → ℂ` sequences, paper-axiom-free)
**Target file**: `Candidates/V55.lean` PLUS supporting per-candidate derived-theorem file `Candidates/V55/LiftSeriesBridge.lean`
**Direction**: section2-proof + analytic-Lean derivation — the FIRST attempt to lift V54's per-`k` identity into the workspace's series-level objects (`liftGapSeries`, `circleGapSeries` from `KorenblumPaper.PaperAxioms`); no prior sprint has connected V54's per-`k` algebra to the workspace's `tsum`-level structure

## Goal

Ship the series-level identity

```text
liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ
                                              (LIFT_SERIES_BRIDGE)
```

valid for every `(a, b : ℕ → ℂ)`, every real `α` with `α² < 1`, every `ρ ≥ 0`,
and per-mode summability hypotheses (the four series whose differences we
take must each be summable — these are surfaced as explicit hypotheses to
the theorem, mirroring the sprint 068 institutional pattern of surfacing
side conditions rather than bundling them as axioms),
as a Lean `theorem` (not an `axiom`) in a per-candidate derived-theorem file
`Candidates/V55/LiftSeriesBridge.lean`. The derivation chains
**only**:

- `Candidates.V54.LiftIdentity.lift_identity_per_k` (sprint 069's headline
  identity, paper-axiom-free, depends only on `Mathlib.Analysis.Complex.Norm`),
- `tsum_sub` / `tsum_div` / `tsum_eq_tsum_of_ne_zero_bij` and friends from
  `Mathlib.Topology.Algebra.InfiniteSum.*`,
- the unfolding of `liftGapSeries` (PaperAxioms line 105) and
  `circleGapSeries` (PaperAxioms line 82–83).

**No new axiom. No oracle. No edit to `KorenblumPaper/`. No edit to
`Reduction.lean`. No edit to `lemma.toml`** beyond a one-line
`[import_policy].allowed_exact` extension mirroring sprint 068/069's
pattern for the new module path
`ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`.

Then ship `Candidates/V55.lean` as a V54-tied candidate (same
`c_value = 7129/20000`, same `valid_of_eq15`-via-
`hEq15_oracle_certified_hp_35645` discharge) that imports
`Candidates/V55/LiftSeriesBridge.lean` and exercises the new theorem in a
side lemma `v55_lift_series_bridge_compiles_at_seed_witness`. This forces
the elaborator to verify the new theorem is non-vacuous and reusable, and
continues the sprint 068/069 institutional pattern.

The fixed quantitative target is `c_value = 7129/20000 = 0.35645` (V54's
ceiling). This sprint deliberately does NOT push `c`; it pursues the
**structural** advance of materializing a new analytical bridge —
specifically, the THIRD per-candidate Lean theorem in the
attempt-first-toward-c-push lineage — by lifting V54's per-`k` identity
into the workspace's `tsum`-level series objects. This is the third
per-candidate derived-theorem file in the workspace; the institutional
pattern is now exercised three times across three structurally distinct
registers (paper-equation chain → pure complex algebra →
`tsum`-level series rearrangement).

## Why

The brief at `AGENT_BRIEF.md` lines 137–141 explicitly names three
un-numbered Wang intermediate algebraic steps as candidate per-candidate
derived-theorem files:

> - the lift identity `(1 − a²)(|b_k|² − |a_k|²) = |b_k − a·a_k|² − |a_k − a·b_k|²`,
> - per-`k` cross-coupling positivity from Wang's `|f| ≤ |g|` boundary hypothesis,
> - boundary L² comparison from `|f| ≤ |g|` via Wang Lemma 2.

Sprint 068 shipped THETA_STEP (paper-equation chain). Sprint 069 shipped
the per-`k` lift identity (pure complex algebra on `ℕ → ℂ` sequences). The
brief's two remaining named candidates (per-`k` cross-coupling positivity
and Wang Lemma 2's boundary `L²` expansion) are both **consumers** of a
series-level structure that no current per-candidate file exposes — and
that the `Section2Assumptions` fields touch only abstractly via the
opaque `liftGap : ℝ → ℝ` field (which is parametric in the paper's
contraction-lift function `α(ρ)` but is bundled as a single abstract
function by `Section2Objects.liftGap`).

The MISSING bridge between V54's per-`k` identity and the brief's two
remaining named candidates is exactly **LIFT_SERIES_BRIDGE**:

```text
liftGapSeries a b α ρ − liftGapSeries b a α ρ = circleGapSeries a b ρ
```

which is the termwise consequence of V54's lift identity summed against
the geometric weight `ρ^{2k}` and divided by `(1 − α²)`. This bridge is
**paper-axiom-free** and connects V54's per-`k` content directly to the
workspace's series-level circle-gap object — the same `circleGapSeries`
that all of sprint 027, sprint 042, sprint 043, sprint 044, sprint 046,
sprint 047 already manipulate at the `tsum` level.

Why LIFT_SERIES_BRIDGE is the right next building block:

1. **It is the natural composition of sprint 068 and sprint 069.** Sprint
   068 shipped a paper-equation chain (`eq8 + eq9 + eq3 + sprint 005 →
   THETA_STEP`); sprint 069 shipped a pure complex-algebra identity on
   `ℕ → ℂ` sequences. Neither sprint has yet **lifted** the per-`k`
   identity into the workspace's `tsum`-level structure. Doing so makes
   the per-`k` content composable with the existing series-level
   reducers in `Reduction.lean` — sprint 027's
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`, sprint
   042's `diskExcess_eq_tsum_via_termwise_integration`, sprint 044's
   `diskExcess_upper_bound_via_tsum_partition_drop_N2`, etc.

2. **It exposes `circleGapSeries` as a difference of two non-negative
   `liftGapSeries`.** Both `liftGapSeries a b α ρ` and `liftGapSeries
   b a α ρ` are `tsum`s of squared norms divided by `(1 − α²) > 0` —
   manifestly non-negative termwise (assuming `α² < 1` so the division
   does not flip sign). LIFT_SERIES_BRIDGE therefore expresses
   `circleGapSeries a b ρ` as `(non-negative) − (non-negative)`. This is
   precisely the structural shape Wang's published derivation uses to
   extract per-`k` cross-coupling positivity: the two halves of
   `circleGap` (the `n1Pred` part and the `n2Pred` part) inherit
   non-negativity from the LiftGap half they correspond to. The next
   per-candidate sprint (per-`k` cross-coupling positivity) becomes
   substantially shorter once LIFT_SERIES_BRIDGE is in place.

3. **It is paper-axiom-free at the trust-surface level.** The proof
   draws on:
   - `Candidates.V54.LiftIdentity.lift_identity_per_k` (paper-axiom-free,
     proved sprint 069 from `Mathlib.Analysis.Complex.Norm` only),
   - `Mathlib.Topology.Algebra.InfiniteSum.*` for `tsum_sub`,
     `tsum_const_smul`, etc.,
   - the `def`-level unfolding of `liftGapSeries` and `circleGapSeries`
     from `KorenblumPaper.PaperAxioms`.

   No `Section2Assumptions` field is invoked — these definitions are
   `def`s exposed by `KorenblumPaper.PaperAxioms` independently of any
   `paper : Section2Assumptions a b K c` instance. Strictly smaller
   trust footprint than sprint 068's THETA_STEP (which depends on
   `paper.{eq3, eq8, eq9}` plus sprint 005); strictly LARGER than sprint
   069's lift identity (which used only `Mathlib.Analysis.Complex.Norm`)
   because LIFT_SERIES_BRIDGE additionally consumes V54's lift identity
   and the workspace's `liftGapSeries` / `circleGapSeries` definitions.

4. **It is feasible within one Generator session.** The proof is a
   `tsum`-level rearrangement: termwise apply V54's `lift_identity_per_k`
   to get `‖b k − α·a k‖² − ‖a k − α·b k‖² = (1 − α²)·(‖b k‖² − ‖a k‖²)`
   per `k`, then divide by `(1 − α²) ≠ 0` (using `α² < 1`), then sum
   over `k` weighted by `ρ^{2k}` and apply `tsum_sub` (under the
   summability hypotheses surfaced as theorem arguments). The
   `circleGapSeries`-side rearrangement uses
   `coeffPlusGap a b k = ‖a k‖² − ‖b k‖² = −(‖b k‖² − ‖a k‖²)`. The
   summability hypotheses are essentially "each of the four series
   `∑ ‖b k − α·a k‖²·ρ^{2k}`, `∑ ‖a k − α·b k‖²·ρ^{2k}`,
   `∑ ‖b k‖²·ρ^{2k}`, `∑ ‖a k‖²·ρ^{2k}` is summable" — surfaced as
   hypotheses to the theorem, mirroring the sprint 068 pattern.

   The generator's competence with `tsum`-level work is
   well-established: sprint 011, 012, 027, 042, 043, 044, 046, 047 all
   ship `tsum`-level identities. Estimated proof length: **80–150
   lines** of Lean (substantially longer than sprint 069's lift identity
   because of the summability bookkeeping, but still well within
   single-session scope per `AGENT_BRIEF.md` lines 154–171).

5. **It satisfies the brief lines 192–195 default disposition.** "If a
   derived theorem is genuinely useful across multiple future candidates,
   propose hoisting it." The brief explicitly normalises shipping
   per-candidate first; hoisting is a separate sprint contract. After
   sprint 070 lands, a hoist-sprint could lift LIFT_SERIES_BRIDGE,
   THETA_STEP, and LIFT_IDENTITY together into a shared `Proof/`
   module — but that's not this sprint.

6. **It is a sensible third exercise of the institutional pattern.**
   Sprint 068 was the first per-candidate derived-theorem file (paper-
   equation chain). Sprint 069 was the second (pure complex algebra).
   Sprint 070 is the third, in a structurally distinct register
   (`tsum`-level rearrangement that **bridges** the per-`k` algebraic
   content of sprint 069 to the series-level structure the workspace
   uses for closing reducers). Three files across three registers
   demonstrates the pattern generalises across the full analytical
   hierarchy needed for Wang's published proof.

## Roadmap to `c > 0.3554`

> *(Bulletin Step 1 mandates this section even for c-tying sprints.)*

1. **Which existing closing reducer is the cheapest path to `c > 0.3554`?**
   None of the existing closing reducers in `Reduction.lean` admits a
   discharge above `c ≈ 0.35635` without a structural input that is not
   currently in `Section2Assumptions` (per sprints 048/050/051/065/066/067/068
   cumulative evidence; sprint 069 left this picture unchanged). The cheapest
   path *through Lean* is to keep accumulating per-candidate Lean theorems
   realizing Wang's un-numbered intermediate algebraic steps, until enough
   is accumulated to derive a per-`k` strict drop bound that the existing
   sprint 045 closing reducer can consume. Sprint 070 contributes the third
   such theorem, the series-level bridge needed for the next two
   brief-named candidates (per-`k` cross-coupling positivity, Wang Lemma 2's
   boundary `L²` expansion) to be expressible cleanly at the `tsum` level.

2. **What is the numerical kernel?** None — LIFT_SERIES_BRIDGE is an
   algebraic/analytic identity, not a numerical kernel.

3. **Does the kernel hold with margin at some `c > 0.3554`?** N/A
   (algebraic/analytic identity, not a numerical kernel).

4. **What is the trust gap between the Scratch witness and a Lean proof?**
   Zero. The identity holds termwise (V54's lift identity per `k`,
   divided by `1 − α² > 0`) and lifts to a `tsum` identity under the
   summability hypotheses surfaced explicitly. No oracle, no
   `Numerical_Library`, no Scratch.

5. **Decide between two routes per gap, for each non-closed-form cell.**
   No cells: pure Lean theorem.

6. **What does the c-pushing candidate look like?** This sprint does NOT
   push `c`. V55 ships at `c_value = 7129/20000 = 0.35645` (ties V54).
   The c-pushing candidate beyond V54 remains deferred. Sprint 070
   contributes the third of (≥ three) per-brief-named per-candidate Lean
   theorems that together would unblock a paper-axiom-free per-`k` strict
   drop bound of the kind proposal_003 was about.

## Three candidate sprint shapes considered (per Planner ultrathink rule)

The Planner enumerated several structurally distinct sprint shapes before
choosing this one. Three of them, with strongest objections:

1. **Re-derive `paper.eq8` (the `Σ⁻ ≤ liftGap` bound) as a Lean theorem
   from V54's lift identity plus a chosen lift coefficient `α(ρ)`.**
   Strongest objection: `Section2Objects.liftGap` is a free `ℝ → ℝ`
   function that the paper bundles as an abstract opaque object whose
   only properties come from the `Eq8SigmaToLiftGap` and
   `Eq9LiftGapToCircleGap` field signatures. Trying to *replace*
   `paper.eq8_sigma_to_liftGap` with a derived theorem requires knowing
   the relationship between the abstract `paper.liftGap : ℝ → ℝ` and
   the concrete `liftGapSeries a b α ρ` — that relationship is **not**
   in `Section2Assumptions` (the paper bundles them separately). Without
   that bridge, we cannot derive `Σ⁻(ρ) ≤ paper.liftGap ρ` from V54;
   we can only derive `Σ⁻(ρ) ≤ liftGapSeries a b α ρ` for a chosen `α`,
   which is a *different* theorem. Demoted: this is a useful adjacent
   direction but it's strictly larger than LIFT_SERIES_BRIDGE and
   prerequisites it.

2. **Ship the per-`k` cross-coupling positivity from `|f| ≤ |g|`
   (brief's second named candidate).** Strongest objection: the boundary
   `|f| ≤ |g|` hypothesis is not exposed by `Section2Assumptions` as a
   field — `Section2Assumptions` exposes only the paper's downstream
   consequences (`eq2..eq14`), not the upstream Hardy-class boundary
   inequality. Producing a Lean theorem of the form "given
   `Section2Assumptions a b K c`, ∀ k, ‖a k‖² ≥ ‖b k‖² with `n1Pred`
   characterization" requires either (a) bridging through the boundary
   hypothesis (Wang Lemma 2; large Mathlib gap, see candidate 3 below)
   or (b) cleverly extracting it from `eq2..eq14`. Path (b) is plausible
   per the brief's "the generator is competent at multi-hundred-line
   Lean proofs" but it is **not** the natural composition of V54 — it
   requires also a series-level handle on the `Σ⁺/Σ⁻` decomposition that
   only LIFT_SERIES_BRIDGE provides. Demoted: this candidate is
   downstream of LIFT_SERIES_BRIDGE and should be queued AFTER sprint 070.

3. **Ship LIFT_SERIES_BRIDGE as a per-candidate derived theorem.**
   **Chosen.** Reasoning above. Crucially, this is the FIRST sprint
   to bridge V54's per-`k` identity to a `tsum`-level workspace object;
   it is **strictly necessary** for any future sprint that wants to
   express Wang's cross-coupling content at the same series level the
   workspace's closing reducers operate on. The proof is feasible in
   one Generator session (80–150 lines of Lean), strictly within the
   `tsum`-level competence the brief asserts and that sprints
   011/012/027/042/043/044/046/047 already exercise. Trust-base
   footprint: zero new axioms, zero oracle, one-line `lemma.toml` edit
   for the new module path.

## Concrete edits expected

### Phase A (deliverable, must succeed)

1. **NEW**: `ProofRefinement/Korenblum/Candidates/V55/LiftSeriesBridge.lean`.

   Contains theorems (no axioms, no new `Section2Assumptions` fields):

   a. The headline series-level bridge:
      ```lean
      theorem liftSeriesBridge_main
          (a b : ℕ → ℂ) (α ρ : ℝ)
          (hα_sq_lt_one : α ^ 2 < 1)
          (hρ_nonneg : 0 ≤ ρ)
          (hSum_b_minus_αa :
            Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)))
          (hSum_a_minus_αb :
            Summable (fun k : ℕ => ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)))
          (hSum_a_norm :
            Summable (fun k : ℕ => ‖a k‖ ^ 2 * ρ ^ (2 * k)))
          (hSum_b_norm :
            Summable (fun k : ℕ => ‖b k‖ ^ 2 * ρ ^ (2 * k))) :
          PaperAxioms.liftGapSeries a b (fun _ => α) ρ
            - PaperAxioms.liftGapSeries b a (fun _ => α) ρ
              = PaperAxioms.circleGapSeries a b ρ
      ```

      *Honest disclosure on the `(scale : ℝ → ℝ)` argument*: PaperAxioms
      `liftGapSeries` takes a *function-valued* scale (line 105–109),
      because in Wang's paper the lift coefficient `α(ρ)` is itself a
      function of `ρ`. For LIFT_SERIES_BRIDGE we instantiate at the
      *constant* function `fun _ => α` because the series-level bridge
      is fundamentally a per-`α` identity — the `α` inside the `tsum`
      is the same scalar at every `k`. If the generator finds the
      `fun _ => α` instantiation awkward (e.g. because of how
      `liftGapSeries`'s `scale ρ` argument is destructured in its
      definition), the equivalent form
      ```lean
      (∑' k : ℕ, ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)) / (1 - α ^ 2)
        - (∑' k : ℕ, ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)) / (1 - α ^ 2)
        = PaperAxioms.circleGapSeries a b ρ
      ```
      may be substituted as an intermediate (then unfolded to
      `liftGapSeries` via the `def`). Either form is acceptable.

      Proof outline (~80–150 lines):

      - Apply V54's `lift_identity_per_k` per `k` to get
        `(1 − α²) · (‖b k‖² − ‖a k‖²) = ‖b k − (α : ℂ)·a k‖² − ‖a k −
        (α : ℂ)·b k‖²`, equivalently
        `‖b k‖² − ‖a k‖² = (‖b k − α·a k‖² − ‖a k − α·b k‖²) / (1 − α²)`
        (using `1 − α² > 0`).
      - Multiply termwise by `ρ^{2k}` and apply `tsum_sub` plus
        `tsum_div_const` (or the `tsum`-friendly form `tsum_smul`)
        under the four summability hypotheses to lift the per-`k`
        identity to a `tsum`-level identity:
        ```text
        ∑' k, (‖b k‖² − ‖a k‖²) · ρ^{2k}
          = (∑' k, ‖b k − α·a k‖² · ρ^{2k}
              − ∑' k, ‖a k − α·b k‖² · ρ^{2k}) / (1 − α²)
        ```
      - Identify the LHS with `−circleGapSeries a b ρ` via
        `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`:
        `∑' k, (‖b k‖² − ‖a k‖²) · ρ^{2k} = −∑' k, coeffPlusGap a b k · ρ^{2k}
        = −circleGapSeries a b ρ`.
      - Identify the RHS with `liftGapSeries a b α ρ − liftGapSeries
        b a α ρ` via `liftGapSeries`'s `def`:
        `liftGapSeries a b α ρ = (∑' k, ‖b k − (α : ℂ)·a k‖² · ρ^{2k}) /
        (1 − α²)` (note: PaperAxioms uses `‖b k - scale ρ * a k‖² *
        ρ^{2k} / (1 − scale ρ ²)` per term — confirm the term-level
        form factors out the constant `(1 − α²)` denominator; the
        `def` has `‖b k − …‖²·ρ^{2k} / (1 − α²)` per term, which
        equals `(‖b k − …‖²·ρ^{2k}) / (1 − α²)` and `tsum_div_const`
        applies).
      - Combine: rearrange signs to get the headline form (the swap
        `liftGapSeries a b α ρ − liftGapSeries b a α ρ`, which
        introduces the sign flip that matches `circleGapSeries a b ρ`).

      *Honest tactical disclosure*: the most delicate step is
      `tsum_sub` under the four summability hypotheses. Mathlib's
      `tsum_sub` requires both summands to be `Summable`; our four
      hypotheses cover this. If the generator finds the standard
      `tsum_sub` lemma's signature awkward (e.g. it expects
      `Summable f` and `Summable g` with the goal `∑' (f − g) = ∑' f
      − ∑' g`), the alternative `tsum_sub_of_summable` or manually
      `Summable.tsum_sub` may be more ergonomic.

   b. (OPTIONAL) A non-negativity corollary, useful for downstream
      consumers. With `α² < 1` and `ρ ≥ 0`, each term of `liftGapSeries`
      is non-negative (it's `‖_‖² · ρ^{2k} / (1 − α²) ≥ 0`):
      ```lean
      theorem liftGapSeries_nonneg
          (a b : ℕ → ℂ) (α ρ : ℝ)
          (hα_sq_lt_one : α ^ 2 < 1)
          (hρ_nonneg : 0 ≤ ρ)
          (hSum_b_minus_αa :
            Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k))) :
          0 ≤ PaperAxioms.liftGapSeries a b (fun _ => α) ρ
      ```
      Proof: `tsum_nonneg` applied termwise after dividing by
      `1 − α² > 0`. ~10 lines. Optional — include if the proof of (a)
      naturally factors through it; otherwise skip.

   c. (OPTIONAL) A `circleGap` non-positivity corollary derived
      directly from (a) plus (b): given `liftGapSeries a b α ρ ≤
      liftGapSeries b a α ρ` (the regime where `f` is "smaller" than
      `g` per Wang's `|f| ≤ |g|`), conclude
      `circleGapSeries a b ρ ≤ 0`. Skip unless the generator finds it
      naturally available; the next sprint can request it.

2. **NEW**: `ProofRefinement/Korenblum/Candidates/V55.lean`.

   Imports `ProofRefinement.Korenblum.Proof.Main` plus
   `ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`. Defines:

   - `c_value : ℝ := 35645 / 100000` (same as V54/V53/V52).
   - `c_value_pos`, `c_value_lt_one`: identical to V54.
   - `eq15_lower_bound : ℝ := 1`: identical to V54.
   - `axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value`:
     identical to V54's. Same registered oracle (`eq15_certified_at_hp_35645`
     in `[[oracles]]`) covers the V55 namespace by bare-name match (per
     sprint 069's empirical confirmation that `[[oracles]]`'s `axiom`
     field is bare in `lemma.toml`).
   - A side lemma `v55_lift_series_bridge_compiles_at_seed_witness`
     instantiating `LiftSeriesBridge.liftSeriesBridge_main` at concrete
     arguments to force elaboration:
     ```lean
     theorem v55_lift_series_bridge_compiles_at_seed_witness
         (a b : ℕ → ℂ) (α ρ : ℝ)
         (hα_sq_lt_one : α ^ 2 < 1)
         (hρ_nonneg : 0 ≤ ρ)
         (hS1 : Summable (fun k : ℕ => ‖b k - (α : ℂ) * a k‖ ^ 2 * ρ ^ (2 * k)))
         (hS2 : Summable (fun k : ℕ => ‖a k - (α : ℂ) * b k‖ ^ 2 * ρ ^ (2 * k)))
         (hS3 : Summable (fun k : ℕ => ‖a k‖ ^ 2 * ρ ^ (2 * k)))
         (hS4 : Summable (fun k : ℕ => ‖b k‖ ^ 2 * ρ ^ (2 * k))) :
         PaperAxioms.liftGapSeries a b (fun _ => α) ρ
           - PaperAxioms.liftGapSeries b a (fun _ => α) ρ
             = PaperAxioms.circleGapSeries a b ρ :=
       LiftSeriesBridge.liftSeriesBridge_main
         a b α ρ hα_sq_lt_one hρ_nonneg hS1 hS2 hS3 hS4
     ```
     Statement-level non-vacuity check; the elaborator's acceptance
     confirms `LiftSeriesBridge` is non-vacuous and reusable.
   - `theorem korenblum_constant_search : ValidKorenblumBound c_value`,
     proved via `valid_of_eq15 c_value_pos c_value_lt_one
     (fun {K} => hEq15_oracle_certified_hp_35645 K)`. Identical
     discharge to V54.

3. **`lemma.toml`**: ONE-LINE edit. Add
   `"ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge"` to
   `[import_policy].allowed_exact` (mirroring sprint 068/069's pattern).
   **No new `[seed_axioms].allowed` entry. No new `[[oracles]]` entry.**
   The same `hEq15_oracle_certified_hp_35645` axiom V54 declares is
   re-declared in the V55 namespace; the existing
   `eq15_certified_at_hp_35645` oracle row in `[[oracles]]` covers both
   declarations by bare-name match (sprint 069 confirmed this
   empirically).

4. **`Bulletin.md`**: append one `## Recent events` row recording
   sprint 070's outcome.

5. **`Experience.md`**: append one entry per the Bulletin honesty rules
   (lines 139–161): what was attempted, dead ends if any, current
   obstacle, next move, trust-surface accounting.

### No Phase B

Sprint 070 has **no Phase B** (no closing-reducer composition attempt).
LIFT_SERIES_BRIDGE by itself does not compose into a closing reducer —
Wang's published derivation needs LIFT_SERIES_BRIDGE **plus** the per-`k`
cross-coupling positivity (the brief's second named candidate) **plus**
the boundary `L²` comparison from `|f| ≤ |g|` (the brief's third named
candidate). Those two are deferred to future sprints (sprint 071 and
sprint 072 by the natural lineage).

Per the bulletin's three-sprint exhaustion synthesis (sprints 065/066/067)
plus sprint 068's Phase B falsification, `(a, b)`-independent closing-reducer
composition is exhausted; advancing `c` further requires per-`k` content
that this sprint contributes the third building block toward but does not
by itself realize.

## Acceptance criteria

### Outcome A — Phase A succeeds, V55 ships at V54's c

1. `lake build ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge`
   succeeds. The file contains `theorem liftSeriesBridge_main` (and
   optionally `theorem liftGapSeries_nonneg` and/or further companions)
   as `theorem`s (no `axiom`s, no `sorry`s).
2. `lake build ProofRefinement.Korenblum.Candidates.V55` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V55.lean` succeeds with
   `pass: true`.
4. The evaluator's `axioms_used` for V55 is `⊆ {seed} ∪
   {hEq15_oracle_certified_hp_35645}`, byte-for-byte identical to V54's
   axiom envelope. **No new free-floating axioms. No new oracles.** The
   only `lemma.toml` edit is the import-policy line for the new
   `LiftSeriesBridge` module path.
5. The evaluator's `score` is exactly `7129/20000` (NOT a c-push;
   acceptance under Outcome A requires the score-tie justification is
   the LIFT_SERIES_BRIDGE advance, recorded in `Experience.md` per the
   Bulletin honesty rules).
6. The LIFT_SERIES_BRIDGE theorem's axiom closure (verifiable separately
   via `#print axioms LiftSeriesBridge.liftSeriesBridge_main` if needed)
   is `⊆ {seed}`. **No `eq15` oracle leakage** into the
   LIFT_SERIES_BRIDGE theorem closure (the theorem is
   paper-axiom-free in the same sense sprint 069's lift identity is —
   it depends on V54's lift identity plus `Mathlib.Topology.Algebra.InfiniteSum.*`
   plus `KorenblumPaper.PaperAxioms`'s `def`s of `liftGapSeries` /
   `circleGapSeries`, none of which contribute to the axiom closure).
7. The side lemma `v55_lift_series_bridge_compiles_at_seed_witness` in
   `Candidates/V55.lean` elaborates and confirms non-vacuity.

### Outcome B — Phase A blocks (LIFT_SERIES_BRIDGE cannot be derived)

If the generator cannot complete Phase A in a reasonable budget (e.g.
the `tsum_sub` lemma signature is awkward against the `liftGapSeries`'s
embedded `(1 − scale ρ ²)` denominator, or the four summability
hypotheses cannot be threaded through `tsum_div_const` in the order
needed):

1. Write `Scratch/sprint_070_obstruction.md` documenting:
   - Which exact intermediate goal blocked the proof (e.g. "after
     applying `lift_identity_per_k` per `k` and `tsum_sub` against the
     four `Summable` hypotheses, the residual goal contains
     `liftGapSeries a b (fun _ => α) ρ` which the elaborator does not
     normalise to `(∑' k, ‖b k − (α : ℂ)·a k‖² · ρ^{2k}) / (1 − α²)`
     without an explicit `unfold liftGapSeries`/`show` rewrite, and the
     resulting goal then loses the `(1 − α²)` factoring under
     `tsum_div_const`").
   - The Lean tactic transcript at the blocking goal.
   - Whether the obstruction is missing-Mathlib-API (legitimate
     request for a successor sprint to import a different Mathlib
     module family, e.g. `Mathlib.Analysis.NormedSpace.lpSpace` or
     `Mathlib.Topology.Algebra.InfiniteSum.Basic` extensions) or
     unfamiliar-tactic-chain (gap-in-attack — record as a request for
     a successor sprint to retry with a different proof strategy, e.g.
     proving the per-term identity first as a pointwise function
     equality and then applying `tsum_congr`).
   - A closed-form algebraic identity confirming the obstruction is
     a tactic-level issue, NOT a mathematical issue. The series-level
     identity follows termwise from V54's lift identity plus
     `tsum_sub`; if the generator cannot find a proof, the obstruction
     MUST be tactical or an API gap, not a mathematical falsification.
   - A recommendation to the next planner: which Mathlib lemma family
     to try next (`tsum_eq_tsum_of_ne_zero_bij`, `Summable.hasSum`,
     `tsum_bij`, etc.).

2. Do NOT ship `Candidates/V55.lean`. Do NOT edit `lemma.toml`. Do NOT
   register any oracle. Do NOT modify `KorenblumPaper/`.

3. Append a Bulletin row recording the BLOCK and a forward-looking
   Experience.md entry naming the next sprint's recommended attack.

### Outcome C — Phase A succeeds with a strictly smaller theorem set

If the generator succeeds at `liftSeriesBridge_main` but the optional
companion lemmas (b, c) prove harder than budgeted, ship just (a) plus
the `Candidates/V55.lean` exercising it. Acceptance criteria 1–7 of
Outcome A apply with the smaller theorem set. The next planner can
request the companions in a successor sprint.

## Out of scope

- Edit older candidates (`V0..V54`).
- Change the final theorem statement (`korenblum_constant_search :
  ValidKorenblumBound c_value`).
- Add a free-floating new axiom (the only axiom V55 declares is the same
  `hEq15_oracle_certified_hp_35645` shape V54 declares; this is
  permitted by the existing oracle registration, NOT a new axiom).
- Edit `KorenblumPaper/` (the paper surface is read-only for the
  generator). In particular, do not rewrite or re-define
  `liftGapSeries` or `circleGapSeries` — those `def`s are PaperAxioms
  content; LIFT_SERIES_BRIDGE consumes them as-is.
- Hoist `Candidates/V53/ThetaStep.lean` or `Candidates/V54/LiftIdentity.lean`
  to `Proof/`. The brief lines 192–195 require a separate sprint
  contract for hoists.
- File a new `Proposals/proposal_004_*.md`. The four-condition guide in
  the planner agent definition is not satisfied: LIFT_SERIES_BRIDGE is
  Lean-derivable in 80–150 lines from V54's lift identity plus standard
  Mathlib `tsum` lemmas (not "thousands of lines"), so the default
  disposition is "prove it in Lean," not "file a proposal." Sprint 070
  IS the prove-it-in-Lean sprint.
- Compose LIFT_SERIES_BRIDGE with the brief's remaining two named
  candidates (per-`k` cross-coupling positivity, Wang Lemma 2's
  boundary `L²` expansion). Those are FUTURE per-candidate
  derived-theorem files; sprint 070 ships only LIFT_SERIES_BRIDGE.
- Push `c` above `7129/20000`. This is a c-tying sprint by design (per
  the bulletin's three-sprint exhaustion synthesis plus sprint 068's
  Phase B falsification: the closed-form `(a, b)`-independent kernel
  space is exhausted; advancing `c` further requires per-`k` content
  that this sprint contributes a building block toward but does not by
  itself realize).
- Re-derive `paper.eq8` from V54 (i.e. the candidate sprint shape #1
  enumerated above). That direction is downstream of LIFT_SERIES_BRIDGE
  and a separate sprint contract; trying to combine it into sprint 070
  would introduce abstraction-bridge complexity (`paper.liftGap` vs
  `liftGapSeries`) that LIFT_SERIES_BRIDGE itself does not need.

## Time budget

≤ 90 minutes runtime for Phase A.

The proof of `liftSeriesBridge_main` is a `tsum`-level rearrangement
chaining V54's `lift_identity_per_k` (per-`k`) with `tsum_sub` /
`tsum_div_const` under the four summability hypotheses. Mathlib provides
the necessary `tsum_sub` / `tsum_div_const` / `Summable.div_const`
infrastructure; the generator picks whichever variant is most ergonomic
for the goal shape. If 60 minutes pass without successful closure, the
generator pivots to a different `tsum`-API family rather than continuing
to chip away. The identity is true and provable termwise from V54's
identity; the question is which `tsum`-API unlocks the shortest proof.

## Stop conditions

- Acceptance criteria for Outcome A or Outcome C met: `STATUS=READY_FOR_EVALUATION`
- Acceptance criteria for Outcome B met (obstruction note shipped, no
  Lean candidate): `STATUS=BLOCKED`
- Generator cannot complete the obstruction note within the time budget:
  `STATUS=BLOCKED_NEEDS_HUMAN`
