# Sprint 084: per-mode m-window τ-partition reducer (general `m`, ties V64)

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V64.lean`
**Target file**: `Candidates/V65.lean` (new) +
new theorem `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` in
`Proof/Reduction.lean`
**Direction**: section2-proof (analytic Lean derivation generalizing the
existing m=2 reducer to arbitrary `m`; preparatory for the +1.2e-2 c-push
along V38's seven-window route)

## Goal

Add a **single new closing reducer** in `Proof/Reduction.lean` that
generalizes `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
(the m=2 reducer at `Reduction.lean:7770-8217` shipped by sprint 078)
to an arbitrary number of `Fin m`-indexed per-mode τ-windows. The new
reducer takes a finite sequence of `(ρStart_i, ρStop_i, j_i)` triples
with the same per-window τ-bound polynomial inequalities as the m=2
case, an adjacency chain `ρStop_i = ρStart_{i+1}` for `i < m - 1`, the
shared summability/integrability witnesses, the joint-mass hypothesis
`1 ≤ Σ_{i : Fin m} ∫_{ρStart_i..ρStop_i} ModeBridge.scalarIntegrand …`,
and concludes `ValidKorenblumBound c`.

Ship `Candidates/V65.lean` that **specializes the new general reducer
at `m = 2` and re-derives V64 byte-for-byte** (same `c_value =
35646/100000`, same endpoints, same oracle, same three free axioms,
same V63 derived-theorem files). V65 ties V64 at `score = 35646/100000`
with a byte-for-byte axiom envelope; this confirms the new reducer
strictly subsumes the old m=2 reducer.

The new reducer **directly unlocks Sprint C of the Bulletin's
three-sprint chain** (the V38 seven-window c-push at `c =
356401/1000000`, +1.2e-2 above V64). Sprint 085+ will build the Wang
eq(5) Branch.one fallback adapter on top of this reducer; sprint 086+
will Phase-0-verify the seven-window joint mass; sprint 087+ will
ship V66 at V38's `c`. None of those downstream sprints can run until
this reducer exists.

## Why

### Why generalize m=2 to arbitrary m

The Bulletin's 2026-05-04 EXPLICIT V38 REFERENCE directive lays out
**three sprints** to reach V38's `c = 356401/1000000`:

  * **Sprint A** (m=1 single window) — shipped at sprint 071 as
    `valid_of_perMode_tau_window_eq8_eq9` at `Reduction.lean:7454`.
  * **Sprint B** (m=2 two-window) — shipped at sprint 078 as
    `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` at
    `Reduction.lean:7770`, then consumed by V64 in sprint 083 for the
    first c-push past V52 (`+1e-5`).
  * **Sprint C** (m=4 four mode windows + m=3 fallback windows = 7
    windows total) — **NOT YET SHIPPED**. This is V38's actual route,
    closing at `c = 356401/1000000` with margin `+1.2381e-5` per V38's
    audit notes inlined in the Bulletin (the "concrete numerics" block
    at the top of `Bulletin.md`).

The +1.2e-2 c-push from V64 to V38's `c` is **two and a half orders of
magnitude larger** than the +1e-5 V52 → V64 push. It is the prize the
Bulletin has been pointing at since sprint 071.

But Sprint C as a single mega-sprint is structurally too large for one
generator session — the V64 path took **five** sprints to ship after
the m=2 reducer (sprints 079, 080, 081, 082, 083 for oracle, three
derived-theorem files, candidate). Sprint C requires:

  1. A general m-window reducer (this sprint, 084).
  2. A Wang-eq(5) Branch.one fallback adapter that produces a
     `mass · innerExcess ≤ slice` premise on a fallback box (sprint
     085).
  3. Phase 0 sweep + numerical oracle for the seven-window joint mass
     at `c = 356401/1000000` (sprint 086).
  4. Wang-eq(5) Branch.one box endpoint construction in a per-candidate
     file (sprint 087, possibly merged with #3).
  5. V66 at V38's `c` composing all of the above (sprint 088).

This sprint executes #1 — the cheapest, most reusable, and structurally
foundational piece. **Without it the other four cannot land.**

### Why this is not a numerical sprint in disguise

The planner brief's "ultrathink" gate explicitly warns against queueing
numerical c-pushes when an analytic Lean derivation is available. The
two natural numerical alternatives are:

  * **Sibling c-push at `c = 35647/100000`** (margin `+1.67e-3` per
    sprint 078's Phase 0 sweep at rational endpoints) — re-pin the
    sprint 083 sqrt-endpoint wrapper at the new `c`, re-verify, ship
    V65 at +1e-5 above V64. Strictly numerical; copy-paste-and-edit
    of sprint 083. **Demoted** because it consumes m=2 axis headroom
    that caps at `c ≈ 0.35654` (margin 4.2e-5, sprint 078 row 9), so
    even the most aggressive m=2 c-push yields at most another ~+8e-5
    versus V64. The +1.2e-2 V38 prize requires the m-window reducer
    regardless.

  * **Sibling c-push at `c = 35650/100000`** (margin `+9.7e-4`,
    just below the wrapper's 1e-3 strict-margin floor) — a slightly
    more aggressive numerical push. Same demotion: still numerical,
    still capped by the m=2 ceiling, still requires the m-window
    reducer to reach V38's `c`.

  * **Sibling c-push at `c = 35654/100000`** (margin `+4.2e-5`, at
    the m=2 ceiling) — risky, possibly fails sqrt-endpoint margin
    re-verification at higher `dps`. **Demoted** for the same reason
    plus margin uncertainty.

  * **Sprint C as one mega-sprint** (m-window reducer + fallback
    adapter + Phase 0 + V38 candidate, all at once) — exceeds the
    bounded-session budget per the brief. **Demoted.**

  * **Hoist V53/V54 derived theorems into `Proof/`** — clean-up; no
    c-push, no analytic novelty, doesn't unlock V38. **Demoted.**

  * **File `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64`
    into `Section2Assumptions` fields** — structurally cleaner trust
    surface but does not push `c` and does not unlock V38. The
    AGENT_BRIEF's four-condition guide for proposal-filing is not
    satisfied: there is no "tried hard and failed" attempt sprint
    behind it; the H² source has not yet been attacked in Lean.
    **Demoted** as parallel work for sprint 088+.

The general m-window reducer is the **sole non-numerical option that
materially advances the path to V38's `c`**. It is exactly the analytic
Lean derivation the planner brief endorses.

### Why this is bounded for one session

The new reducer's body is **structurally identical** to the existing
m=2 reducer at `Reduction.lean:7770-8217` (~447 lines), with a single
substitution: replace explicit 2-fold pattern matching (`hStart₁`,
`hStart₂`, `mass₁ + mass₂`, etc.) with `Finset.sum` over `Fin m`.
Concretely, the proof body decomposes as:

  * Step 1 (sigmaPlus ≤ sigmaMinus via eq4 at `(0, c)`): unchanged,
    one application; ~10 lines.
  * Step 2 (per-mode pointwise bound on each `Set.Icc ρStart_i ρStop_i`):
    universally quantified over `i : Fin m`; one application of
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    inside a `forall`-elimination; ~30 lines.
  * Step 3 (per-window scalar non-negativity and mass non-negativity):
    universally quantified `i : Fin m`; ~25 lines.
  * Step 4 (per-window `mass_mul_le_annulusSlice_of_integral_bound`):
    universally quantified `i : Fin m`; ~30 lines.
  * Step 5 (Adjacency-glue sum-of-slices = single big slice): an
    induction over `Fin m` chaining `annulusSlice_add_adjacent`
    `(m - 1)` times. **This is the only structurally new step** vs.
    the m=2 case which had a single `annulusSlice_add_adjacent`
    application; the inductive form is ~40 lines using either
    `Finset.induction_on` over `Fin m`'s underlying `Finset.range m`
    or a manual `Nat.rec`. The Bulletin's Sprint C plan suggests
    using the existing `AnnulusIntegralReduction.innerExcess_le_of_window_bounds`
    instead, which already takes a finite-sum form — ~20 lines if so.
  * Step 6 (Sum mass-bounds + apply `1 ≤ Σ mass_i`): linear-arithmetic
    chain over the sum, ~20 lines.
  * Step 7 (Side-slice non-negativity for `(c, ρStart_0)` and
    `(ρStop_{m-1}, 1)`): ~30 lines, identical to m=2 case.
  * Step 8 (Final calc chain): ~10 lines.

Total estimated body: ~200-300 lines of Lean. Plus the theorem
statement: ~80 lines (the `h_witness` predicate has the same shape as
m=2 but with universal quantifiers over `Fin m` for endpoints/τ-bounds/
integrabilities, and a `Finset.sum` for the joint-mass cell). Total
~280-380 lines, comparable to the existing m=2 reducer.

V65 itself is ~100 lines (just specialize the new reducer at `m = 2`
and supply the same `h_witness` data V64 already constructs). The
generator's burden is small for V65 — it imports V64's already-shipped
derived-theorem files plus the new reducer.

### Why use `Finset.sum` over `Fin m` rather than `List`

The Bulletin's V38 reference notes that
`AnnulusIntegralReduction.innerExcess_le_of_window_bounds` (the V38
gluing theorem) takes a `Finset` index set and a `mass : ι → ℝ`
function. Using `Fin m` aligns with that theorem and avoids a
`List`-indexed adjacency chain. The downside is that `Finset.sum` over
`Fin m` requires the proof to thread the index ordering correctly
through `Finset.sum_range_succ`, but this is standard Mathlib idiom.

If the generator finds the `Fin m` form unwieldy, the alternative is
to take a **`List (ℝ × ℝ × ℕ)`** of `(ρStart, ρStop, j)` triples plus
ordering hypotheses (`List.Sorted`, `List.Adjacent`-style). Either is
acceptable; the contract does not pin the form.

### Why V65 ties V64 byte-for-byte

V65's job is to **confirm the new reducer subsumes the old one**.
Concretely:

  1. V65 instantiates the new general reducer at `m = 2` with the
     same two windows V64 used (`(ρStart₁_sqrt, ρ_meet_sqrt, j=2)`
     and `(ρ_meet_sqrt, 999999/1000000, j=1)` at `c = 35646/100000`).
  2. V65's `h_witness` predicate is **the same data V64 already
     constructs**, just re-shaped from a 2-tuple destructuring into a
     `Fin 2`-indexed collection.
  3. V65's `axioms_used` set is byte-for-byte identical to V64's:
     `{propext, Classical.choice, Quot.sound, hH2_v64, hCircleGapInt_v64,
     h_two_window_mass_certified_at_35646_sqrt}`. **No new axioms, no
     new oracles.**
  4. V65's score is `35646/100000` (ties V64). The Evaluator records
     the tie; the Refinement_Log row carries `axioms_used` matching
     V64's row.

This is a **non-vacuity check** for the new reducer: if V65 compiles
and ties V64, the new reducer is at least as strong as the old one.
The general-m form is then immediately available for sprint 085+.

## Concrete edits expected

### 1. New theorem in `Proof/Reduction.lean`

Add `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` immediately
after `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` (around line
8217). Suggested signature shape:

```lean
theorem valid_of_perMode_multiWindow_tau_partition_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    {m : ℕ}
    (hm_pos : 1 ≤ m)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart ρStop : Fin m → ℝ) (j : Fin m → ℕ),
          -- per-window endpoint and mode constraints:
          c < ρStart ⟨0, hm_pos⟩ ∧
          (∀ i : Fin m, ρStart i ≤ ρStop i) ∧
          (∀ i : Fin m, 1 ≤ j i) ∧
          -- adjacency: ρStop i = ρStart (i+1) for i+1 < m
          (∀ i : Fin m, (h : i.val + 1 < m) →
            ρStop i = ρStart ⟨i.val + 1, h⟩) ∧
          ρStop ⟨m - 1, …⟩ < 1 ∧
          -- per-window τ-bounds:
          (∀ i : Fin m,
            OneModeTail.tau (j i - 1) ≤ c ^ 2 / ρStop i ^ 2 ∧
            c ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau (j i)) ∧
          -- shared summability hypotheses (same six as the m=2 case):
          Summable (fun n => OneModePaperBridge.plusSeq a b n *
                              c ^ (2*n+2) / (n+1 : ℝ)) ∧
          Summable (fun n => OneModePaperBridge.plusSeq a b n * c^(2*n)) ∧
          Summable (fun n => OneModePaperBridge.minusSeq a b n *
                              c ^ (2*n+2) / (n+1 : ℝ)) ∧
          Summable (fun n => OneModePaperBridge.minusSeq a b n * c^(2*n)) ∧
          Summable (fun n => OneModePaperBridge.minusSeq a b n *
                              OneModeKernel.weight c n) ∧
          (∀ ⦃ρ⦄, c < ρ → ρ < 1 →
            Summable (fun n => OneModePaperBridge.minusSeq a b n * ρ^(2*n))) ∧
          -- circleGap integrability on (c, 1):
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1 ∧
          -- per-window scalar integrand integrability:
          (∀ i : Fin m,
            IntervalIntegrable
              (fun ρ => ModeBridge.scalarIntegrand c (j i)
                         (WangOuter.paperLambda K c) ρ)
              volume (ρStart i) (ρStop i)) ∧
          -- diskExcess ≤ innerSeriesExcess:
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            OneModePaperBridge.innerSeriesExcess a b c ∧
          -- joint multi-window mass:
          (1 : ℝ) ≤ ∑ i : Fin m,
            ∫ ρ in (ρStart i)..(ρStop i),
              ModeBridge.scalarIntegrand c (j i)
                (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  …
```

Proof body proceeds as outlined in §"Why this is bounded for one
session" above. Two acceptable structural choices:

  * **Option α (preferred): induction over `m`.** Use a helper lemma
    proving the `Fin m`-indexed version by recursion: for `m = 1`
    delegate directly to sprint 071's
    `valid_of_perMode_tau_window_eq8_eq9`; for `m → m + 1` peel off
    the last window via `Fin.lastCases` plus `annulusSlice_add_adjacent`.
    This keeps the proof local and avoids the `Fin m`-Finset bridging
    overhead.

  * **Option β: direct call to `innerExcess_le_of_window_bounds`.**
    Per the V38 directive in the Bulletin, the gluing theorem
    `AnnulusIntegralReduction.innerExcess_le_of_window_bounds` already
    takes the `Finset.sum`-form and is the V38 plan's suggested
    closer. If the generator finds it cleaner to invoke that theorem
    directly (which avoids the induction entirely), do so.

The generator picks Option α or β based on which Mathlib API makes the
proof cleanest. The contract does not pin the choice.

### 2. New `Candidates/V65.lean`

Structure mirrors V64. Major points:

  * Module imports: `Proof.Main`, `Proof.Reduction`,
    `Candidates.V63.Integrability`, `Candidates.V63.Summability`,
    `Candidates.V63.DiskInnerSeriesBridge`,
    `Candidates.V64.TauWindowEndpoints`.

  * Re-export V64's three free axioms (`hH2_v64`, `hCircleGapInt_v64`)
    and the existing oracle axiom
    `h_two_window_mass_certified_at_35646_sqrt` either by direct
    re-import (preferred, no new axioms in V65's own namespace) or by
    structurally identical re-declaration (acceptable fallback if the
    re-export pattern bumps the axiom audit).

  * `def c_value : ℝ := 35646 / 100000` (same as V64).

  * Theorem `korenblum_constant_search : ValidKorenblumBound c_value`
    proved by:

    ```lean
    valid_of_perMode_multiWindow_tau_partition_eq8_eq9
      (m := 2) (hm_pos := …) c_value_pos c_value_lt_one
      (h_witness := fun {a b K} paper => by
        refine ⟨fun i => …, fun i => …, fun i => …, ?_, ?_, ?_, ?_, …⟩
        -- For i = 0: ρStart = ρStart₁_sqrt, ρStop = ρ_meet_sqrt, j = 2
        -- For i = 1: ρStart = ρ_meet_sqrt, ρStop = 999999/1000000, j = 1
        -- All discharge via V64's data, restated through `Fin 2`.
        …
      )
    ```

  * Side lemma `v65_ties_v64`: `(35646 : ℝ) / 100000 = c_value` to
    confirm tie.

  * **No new axioms.** V65's `axioms_used` set must equal V64's
    byte-for-byte.

### 3. `lemma.toml`

Add `"ProofRefinement.Korenblum.Candidates.V65"` to
`[import_policy].allowed_exact` if the existing wildcard rule
`ProofRefinement.Korenblum.*` does not already cover it. (Recent
candidates like V64 have explicit per-module entries; check first.)

**No new `[seed_axioms]` entries, no new `[[oracles]]` rows, no new
`[workspace_import_policy]` entries.**

### 4. Bulletin and Experience append

Append one row each documenting:

  * the new general reducer
    `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` shipped in
    `Proof/Reduction.lean`,
  * V65 as an m=2 specialization that ties V64 byte-for-byte (proves
    the new reducer subsumes the m=2 reducer),
  * forward direction: sprint 085 builds the Wang-eq(5) Branch.one
    fallback adapter on top of this reducer, sprint 086 Phase-0
    verifies seven-window joint mass at `c = 356401/1000000`, sprint
    087+ ships V66 at V38's `c` (the +1.2e-2 c-push, two and a half
    orders of magnitude above the V64 push).

### NO edits to

  * `KorenblumPaper/` (read-only paper surface).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Existing `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` body
    (still load-bearing for V64; do not refactor it).
  * Any V0–V64 candidate file.
  * Any V63/V64 per-candidate derived-theorem file.
  * `Numerical_Library/` (no new wrappers; V65 reuses V64's oracle
    byte-for-byte).
  * `Proposals/` (no proposal filed this sprint).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
2. `lake build ProofRefinement.Korenblum.Candidates.V65` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V65.lean` reports `pass: true`.
4. Evaluator records `score (maximize) = 35646/100000` (ties V64;
   the c-push is preparatory, not numerical).
5. Evaluator's axiom audit reports
   `axioms_used ⊆ {propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt,
   ProofRefinement.Korenblum.Candidates.V64.hH2_v64,
   ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64}`
   — **byte-for-byte identical to V64's audit**, modulo the V64
   namespace prefix (or V65's, if re-declaration was used; either
   acceptable).
6. The new theorem
   `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` exists in
   `Proof/Reduction.lean` with the signature shape outlined above
   (parameter names may vary).
7. The new theorem's body contains **only `theorem`/`lemma`-level
   constructs** — no new `axiom` declarations, no `sorry`, no
   `Section2Assumptions` field extensions.
8. V65's body invokes `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
   with `m := 2` (not `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`)
   — this confirms the new reducer is load-bearing for V65.
9. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern, naming the new general reducer and the
   forward direction toward V38's `c`.

## Out of scope

  * Push c past `35646/100000`. V65 ties V64; pushing c is sprint
    087+'s job once the seven-window machinery is in place.
  * Build the Wang-eq(5) Branch.one fallback adapter. That's sprint
    085's job.
  * Phase-0-verify seven-window joint mass at `c = 356401/1000000`.
    That's sprint 086's job.
  * Edit the existing m=2 reducer. It stays in place as a closed
    sprint 078 deliverable; V64 still uses it directly. (V65 uses the
    new general reducer; the two reducers coexist.)
  * Edit V63's three derived-theorem files or V64's
    `TauWindowEndpoints.lean`. They are reused as-is.
  * File `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64` into
    `Section2Assumptions`. Deferred to sprint 088+ as a parallel
    structural cleanup.
  * Add new oracles or new wrappers. V65 reuses V64's oracle
    byte-for-byte.

## Time budget

≤ 120 minutes runtime (the new reducer is ~200-300 lines of Lean
following the m=2 reducer's exact shape; V65 is ~100 lines re-using
V64's data; the only structurally new piece is the `Fin m` adjacency
induction, which is a standard Mathlib idiom).

## Stop conditions

  * **All 9 acceptance criteria met**: `STATUS=READY_FOR_EVALUATION`.
    The new general reducer ships, V65 ties V64, the harness is one
    sprint closer to V38's `c`.

  * **Adjacency induction over `Fin m` hits a Mathlib API mismatch**
    (`Finset.sum_range_succ`, `Fin.lastCases`, or `induction'`-style
    pattern doesn't compose cleanly with `annulusSlice_add_adjacent`):
    fall back to **Option β** (direct call to
    `AnnulusIntegralReduction.innerExcess_le_of_window_bounds`).
    Document the API mismatch at `Scratch/sprint_084_obstruction.md`
    if even Option β stalls.

  * **The `h_witness` predicate's `Fin m`-quantifier shape causes
    universe-polymorphism unification failure** when V65 specializes
    at `m = 2`: degrade gracefully — define an explicit `m = 2` adapter
    `valid_of_perMode_multiWindow_tau_partition_eq8_eq9_m2` that
    invokes the general reducer at `m = 2` with concrete `Fin 2`
    indices, and have V65 invoke the adapter. Document at
    `Scratch/sprint_084_obstruction.md`.

  * **Both Option α and Option β stall on a structural Mathlib API
    gap that requires a new `[workspace_import_policy]` entry**: do
    not silently expand the policy. `STATUS=BLOCKED` with a precise
    note at `Scratch/sprint_084_obstruction.md` naming the missing
    Mathlib lemma and the policy expansion required. The next planner
    decides whether to proposal-file the policy expansion or pivot to
    Option β (or to a list-indexed form that avoids `Fin m`).

  * **Generator session exceeds 120 minutes on the reducer body**:
    ship a partial deliverable — the reducer **statement** (with
    `sorry` in the body, then immediately replace with `admit` + a
    `#print axioms` exclusion) is **not acceptable** because `sorryAx`
    is a hard Evaluator fail. Instead: ship V65 as a V64-tie via the
    existing m=2 reducer (i.e. revert to the V64 discharge route),
    and document the new reducer's partial proof state at
    `Scratch/sprint_084_partial_proof.lean`. `STATUS=BLOCKED` with the
    obstruction and the partial proof for the next planner to pick up.
    This preserves the harness's V64-tie progress without polluting the
    candidate set with a `sorry`-bearing reducer.

  * **A new free-floating axiom or trust-base expansion would be
    required beyond the existing V64 envelope**: do not ship it.
    Document at `Scratch/sprint_084_obstruction.md` and
    `STATUS=BLOCKED_NEEDS_HUMAN`.

## Notes for the generator

  * **Read first**: the existing m=2 reducer at
    `Proof/Reduction.lean:7770-8217` (220 lines, your structural
    template); the gluing theorem
    `AnnulusIntegralReduction.innerExcess_le_of_window_bounds` (search
    `KorenblumPaper/AnnulusIntegralReduction.lean` for its exact
    signature — the Bulletin describes its shape at lines ~245-253);
    sprint 071's m=1 reducer at `Proof/Reduction.lean:7454`; V64's
    body at `Candidates/V64.lean` for the m=2 instantiation pattern
    your V65 mirrors.

  * **`Fin m`-indexed adjacency template**. The sequence of windows
    `(ρStart i, ρStop i)` for `i : Fin m` with adjacency `ρStop i =
    ρStart (i + 1)` (where `i + 1 < m`) is the standard
    `IntervalIntegrable.sum_pair_adjacent` family in Mathlib. If
    Option α is taken, the inductive step for `m → m + 1` uses
    `Fin.snoc` to append the new window, then a single
    `annulusSlice_add_adjacent` to glue the existing
    `[ρStart 0, ρStop (m-1)]` slice to the new
    `[ρStart m, ρStop m]` slice.

  * **`innerExcess_le_of_window_bounds` shape**. Per Bulletin
    lines ~245-253, the V38 gluing theorem takes:
    ```lean
    theorem innerExcess_le_of_window_bounds
        {ι : Type} (s : Finset ι)
        (mass annulusTerm : ι → ℝ) {innerExcess annulusExcess : ℝ}
        (hWindow : ∀ i ∈ s, mass i * innerExcess ≤ annulusTerm i)
        (hTotal : (1 : ℝ) ≤ Finset.sum s (fun i => mass i))
        (hAnnulus : Finset.sum s (fun i => annulusTerm i) ≤ annulusExcess)
        (hAnnulusNonneg : ∀ i ∈ s, 0 ≤ annulusTerm i) :
        innerExcess ≤ annulusExcess
    ```
    This is exactly the closing lemma your reducer needs after Step 4.
    Step 5 (annulusTerm-sum-bound) is then a separate lemma proving
    `Σ_i annulusSlice ρStart_i ρStop_i ≤ annulusSlice c 1` via repeated
    `annulusSlice_add_adjacent` and the side-slice non-negativity for
    `(c, ρStart 0)` and `(ρStop (m-1), 1)`.

  * **Fallback Option β template** (if Option α stalls):
    1. Build per-window `mass_i := ∫ ρ in (ρStart i)..(ρStop i),
       ModeBridge.scalarIntegrand …` and `annulusTerm_i :=
       AnnulusIntegralReduction.annulusSlice paper.circleGap
       (ρStart i) (ρStop i)`.
    2. Per-window `mass_i * innerExcess ≤ annulusTerm_i` from
       `mass_mul_le_annulusSlice_of_integral_bound`.
    3. `Σ_i annulusTerm_i ≤ annulusExcess` via repeated adjacency-glue
       + side-slice non-negativity.
    4. Close with `innerExcess_le_of_window_bounds` over the `Finset
       (Fin m) := Finset.univ`.

  * **V65's `h_witness` construction**. The `Fin 2`-indexed witness
    is built by `fun i => Fin.cases <case 0> <case 1>` style, or
    via `match i with | 0 => … | 1 => … end`. Each branch supplies
    V64's existing data unchanged. The summability cells, integrability
    cells, and `diskExcess ≤ innerSeriesExcess` cell are universally
    quantified in `m`, so they re-use V64's witnesses verbatim.

  * **Generator capability budget**. The reducer body is mechanically
    similar to the m=2 reducer; the main novelty is the `Fin m` /
    `Finset.sum` indexing. If you find yourself writing more than ~50
    lines of new tactic code that doesn't have a direct counterpart in
    the m=2 reducer, you are probably overcomplicating; step back and
    consider Option β.

  * **No new files under `Candidates/V65/`**. V65 is a thin specializer;
    its `h_witness` data comes from V63's three derived-theorem files
    plus V64's `TauWindowEndpoints.lean`. No new per-candidate
    derived-theorem file is needed.

  * **Optional optimization**. If the generator notices that the m=2
    reducer's body can be **mechanically rewritten** as a special case
    of the new general reducer (i.e. `valid_of_perMode_twoWindow_…`
    becomes a one-line corollary of `valid_of_perMode_multiWindow_…`
    at `m = 2`), that's a nice cleanup but **out of scope for this
    sprint**. Keep both reducers; the m=2 form's existing dependents
    (V64) should not need any edits. A future sprint can hoist V64's
    invocation of the m=2 reducer to the m-window form once the
    general form is established.
