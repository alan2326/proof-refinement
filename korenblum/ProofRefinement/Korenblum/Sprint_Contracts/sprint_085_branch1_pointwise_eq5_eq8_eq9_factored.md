# Sprint 085: factor Branch.one pointwise bound `(5)+(8)+(9) ⇒ scalarIntegrand1 · innerExcess ≤ annulusDensity` as a standalone theorem

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V65.lean`
**Target file**: no new candidate this sprint; new theorem added in
`Proof/Reduction.lean` (and reused inside `valid_of_eq5_eq8_eq9_subinterval_branch1`)
**Direction**: section2-proof (analytic Lean refactor that exposes a missing
structural building block; preparatory for the V38 seven-window c-push)

## Goal

Add **one new standalone theorem** in `Proof/Reduction.lean` that proves the
Branch.one analogue of `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`:

```lean
theorem pointwise_branch1_on_Icc_eq5_eq8_eq9
    {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hcρ₁ : c < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hρ₂_split : ρ₂ ≤ PaperAxioms.branchSplit c)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c) :
    ∀ ρ ∈ Set.Icc ρ₁ ρ₂,
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ
```

(Parameter names may vary; the contract fixes the signature shape, not the
identifier spelling. The theorem may be stated for `Set.Ioo` and lifted to
`Icc` separately, or stated directly for `Icc` — generator's choice.)

The body is **the existing inline derivation at
`Proof/Reduction.lean:2606-2652`** inside `valid_of_eq5_eq8_eq9_subinterval_branch1`
(sprint 010), pulled out as a reusable lemma. The chain is:

  1. Apply `PaperAxioms.eq10_of_eq5_eq8_eq9 paper.eq5_branch1_sigmaReduction
     paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap` to obtain
     `branch1PointwiseFactor c (paperLambda K c) ρ * innerExcess ≤ circleGap ρ`.
  2. Multiply by `2ρ ≥ 0`.
  3. Use the algebraic identity
     `2 * ρ * branch1PointwiseFactor c (paperLambda K c) ρ =
      Korenblum.scalarIntegrand1 c (paperLambda K c) ρ`
     (already discharged at lines 2639-2647 by `field_simp` + `ring` after
     unfolding both definitions).

After the theorem ships, **refactor `valid_of_eq5_eq8_eq9_subinterval_branch1`'s
body** (lines 2513-2763) to invoke the new theorem on `Set.Icc ρ₁ ρ₂` where the
inline `Set.Ioo` derivation currently lives (lines 2608-2652). This is a pure
DRY refactor: the resulting `valid_of_eq5_eq8_eq9_subinterval_branch1` must
still type-check and produce the same conclusion via the same a.e./Icc lift
argument.

No candidate file is shipped this sprint.

## Why

### Why this is the right next sprint

The Bulletin's 2026-05-04 EXPLICIT V38 REFERENCE directive lays out a
three-sprint chain to reach `c = 356401/1000000` (+1.2e-2 above V64's
`c = 35646/100000`):

  * Sprint 084 (shipped) — general-`m` per-mode τ-partition reducer
    `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
    (`Proof/Reduction.lean:8382`). Subsumed the m=2 reducer; V65 ties V64.
  * **Sprint 085 (this) — Branch.one pointwise bound, factored.** Establishes
    the missing structural building block for fallback windows in V38's
    seven-window split.
  * Sprint 086+ — mixed-window closing reducer (per-mode + Branch.one), a
    Wang-eq(5) Branch.one fallback adapter shape that consumes this sprint's
    pointwise theorem.
  * Sprint 087+ — Numerical_Library fallback-box mass wrapper at V38's `c`,
    plus a candidate-side oracle row.
  * Sprint 088+ — V66 at `c = 356401/1000000` composing four mode windows
    (j=4,3,2,1) and three fallback boxes via the mixed reducer.

V38's seven-window route splits `(c, 1)` into 4 per-mode windows
(j*=4, j*=3, j*=2, j*=1) **interleaved** with 3 Branch.one fallback boxes
(in the deep `c < ρ < √(4/3)·c` band where Wang's eq(5) singular factor
`1/(ρ²-c²)` is unbeatable). The general-`m` reducer shipped in sprint 084 is
**uniformly per-mode**: every window must consume `ModeBridge.scalarIntegrand
c (j i) (paperLambda K c)` and a τ-bound discharge. There is no provision
for a Branch.one fallback window inside that reducer. To enable mixed
windows, sprint 086+ will need a **Branch.one analogue of
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`**
that produces the matching `mass_mul_le_annulusSlice_of_integral_bound` shape
on a fallback window — i.e. exactly this sprint's deliverable.

### Why this is bounded for one session

The pointwise Branch.one bound **already exists inline** at
`Proof/Reduction.lean:2606-2652` (sprint 010's derivation, reused by sprint
041 to internalize the eq10 paper field via `eq10_of_eq5_eq8_eq9`). This
sprint's job is to **lift it out as a reusable theorem** with no new
mathematical content. The body is a verbatim copy from the existing
derivation; the refactor of `valid_of_eq5_eq8_eq9_subinterval_branch1` to
consume the new theorem is a single substitution at lines 2608-2652 (40
lines of inline tactic replaced by one `pointwise_branch1_on_Icc_eq5_eq8_eq9
hc_pos hSplit_lt_one hcρ₁ hρ₁₂ hρ₂_split paper` call).

Estimated lines:

  * New theorem statement + body in `Proof/Reduction.lean`: ~60-80 lines
    (the `Ioo`-flavoured inline derivation is ~45 lines; the optional
    `Icc` lift via `Ioo_ae_eq_Icc` adds ~10-15 lines if stated for `Icc`
    directly).
  * Refactor of `valid_of_eq5_eq8_eq9_subinterval_branch1`: net ~−30 lines
    (replaces 40-line inline derivation with one theorem call).
  * Optional: lift the new theorem to a clean `Icc` statement separately.

Total session work: ~80-120 lines of Lean, with **zero new mathematical
content** — pure DRY refactoring backed by an existing proof. The trust
surface is unchanged.

### Why this is not a numerical c-push in disguise

This sprint ships **no `c_value` improvement and no new candidate**. The
score after sprint 085 is unchanged at `35646/100000`. The "ultrathink"
guard against numerical-headroom-only sprints is satisfied trivially — there
is no numerical claim. The value is purely structural: it unblocks sprint
086+'s mixed reducer and the V38 seven-window c-push.

The brief explicitly endorses analytic Lean derivations that prepare a
future c-push — see `AGENT_BRIEF.md` "High-value directions" rule 3 ("Prove
a stronger direct reduction than the current seed bridge") and the planner
agent definition's description of preparing "a precise oracle-backed
subclaim that directly supports a future increase in `c_value`."

### Three distinct directions considered (and why this one wins)

The planner brief requires enumerating at least three distinct sprint
shapes pursuing different analytical chains, with the strongest objection to
each, before settling.

1. **Direction A (this sprint): factor Branch.one pointwise bound from the
   inline sprint-010 derivation.** Cleanest size; reuses an already-proved
   chain; produces a reusable structural piece. Strongest objection: it is
   a refactor with zero mathematical novelty, so it does not directly
   advance `c_value`. Counter: sprint 084's reducer was also c-tying, and
   the harness budget allows preparatory bounded sessions when the
   downstream payoff is the +1.2e-2 V38 push. This is exactly the kind of
   bounded session the brief's "preparatory subclaim" clause endorses.

2. **Direction B: ship the full mixed-window closing reducer
   `valid_of_mixedKernel_multiWindow_tau_partition_eq8_eq9` in one sprint,
   accepting both per-mode and Branch.one windows.** Strongest objection:
   the existing per-mode-only reducer at `Reduction.lean:8382` is ~250
   lines (excluding its 9-line statement); a mixed-kernel version
   essentially doubles its body to handle two-case dispatch on each window's
   kernel kind, plus the new Branch.one pointwise step (which would then
   need to be inlined again — duplicate work versus Direction A). Estimated
   size: ~500-700 lines, well above one bounded session. **Demoted in
   favor of building the structural piece first (Direction A) and then
   composing the mixed reducer in sprint 086.**

3. **Direction C: a sibling c-push along the m=2 axis at `c =
   35647/100000` or `35650/100000`.** Strongest objection: this is exactly
   the numerical-headroom-only push the brief warns against. The m=2 axis
   ceiling per sprint 078's Phase 0 sweep is `c ≈ 0.35654` (margin 4.2e-5),
   so even the most aggressive m=2 push yields at most another ~+8e-5
   versus V64. The +1.2e-2 V38 prize requires the m-window mixed reducer
   regardless; spending a session on m=2 sibling pushes consumes budget
   without advancing the structural path to V38's `c`. **Demoted as
   numerical-only.**

4. **Direction D: Phase 0 seven-window numerical sweep at `c =
   356401/1000000` to verify V38's audited mass before committing to the
   Lean adapter architecture.** Strongest objection: the Bulletin already
   inlines V38's audited numbers (`c = 0.356401 → total mass =
   1.000012381570`), so a confirmation script duplicates a known-good
   result with zero Lean output. The numerical sweep belongs in sprint 087
   alongside the oracle wrapper, not as a standalone sprint. **Demoted as
   pure numerical preparation that can be folded into a later sprint.**

5. **Direction E: hoist V53/V54/V55/V57/V58/V60 derived theorems into
   `Proof/`.** Strongest objection: pure cleanup, no analytic novelty, no
   path to V38's `c`. **Demoted as deferrable cleanup.**

6. **Direction F: file `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64`
   into `Section2Assumptions`.** Strongest objection: the AGENT_BRIEF's
   four-condition guide for proposal-filing is **not** satisfied — H² has
   not been attacked in Lean (no "tried hard and failed" attempt sprint),
   and the migration does not push `c_value`. **Demoted; would not improve
   the score even if approved.**

Direction A wins on **expected analytical novelty per bounded-Generator-
session**: it is the smallest piece that materially unblocks the V38
seven-window c-push (Sprint C of the Bulletin's three-sprint chain), it has
a known-good proof body to lift verbatim from sprint 010's derivation, and
its acceptance criteria are concretely falsifiable in one session.

### Why the new theorem fits the
`mass_mul_le_annulusSlice_of_integral_bound` shape

`AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound` (used
by sprint 078's m=2 reducer and sprint 084's general-`m` reducer) requires:

  * `hPointwise : ∀ ρ ∈ Icc a b,
      modeIntegrand ρ * innerExcess ≤ annulusDensity circleGap ρ`,
  * `hMass : mass ≤ ∫ ρ in a..b, modeIntegrand ρ`,
  * `hMassNonneg : 0 ≤ mass`,
  * `hModeInt`, `hAnnInt` integrability witnesses,
  * `hAnnNonneg : ∀ ρ ∈ Icc a b, 0 ≤ annulusDensity circleGap ρ`.

The new theorem produces exactly the `hPointwise` premise on a Branch.one
fallback window with `modeIntegrand := Korenblum.scalarIntegrand1 c
(WangOuter.paperLambda K c)`. The other premises (mass nonneg,
integrability of `scalarIntegrand1` on `[ρ₁, ρ₂]` via
`WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
annulusDensity nonneg via `annulusDensity_nonneg_of_lt`, integrability of
annulusDensity on the sub-interval via `mono_set` from a global
`[c, 1]`-integrability premise) all already exist in the workspace.
**Sprint 086 will thread these together to prove
`mass_w · innerExcess ≤ annulusSlice ρ_{w-1} ρ_w` on each Branch.one window**;
this sprint's deliverable is the missing `hPointwise` premise.

## Concrete edits expected

### 1. New theorem in `Proof/Reduction.lean`

Add `pointwise_branch1_on_Icc_eq5_eq8_eq9` near the top of
`Proof/Reduction.lean`, immediately before
`valid_of_eq5_eq8_eq9_subinterval_branch1` (around line 2510 — i.e. inside
the same comment block region) **or** at the top of the file alongside
the other `private`/`public` helpers. The theorem may be `private` if it
is only used inside `Proof/Reduction.lean`, or `public` if a future
sprint's mixed reducer will live in a separate file. Generator's choice.

Suggested signature (parameter names may vary):

```lean
theorem pointwise_branch1_on_Icc_eq5_eq8_eq9
    {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    (hcρ₁ : c < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hρ₂_split : ρ₂ ≤ PaperAxioms.branchSplit c)
    {a b : ℕ → ℂ}
    {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c) :
    ∀ ρ ∈ Set.Icc ρ₁ ρ₂,
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ
```

Two acceptable structural choices for the body:

  * **Option α (preferred): direct `Icc` statement.** State the conclusion
    on `Set.Icc ρ₁ ρ₂` and prove it pointwise. The boundary points `ρ = ρ₁`
    and `ρ = ρ₂` need `c ≤ ρ ≤ branchSplit c` (closed inclusions); these
    are derivable from the hypotheses via `lt_of_lt_of_le hcρ₁ hρ.1` and
    `lt_of_le_of_lt hρ.2 hSplit_lt_one`. The chain `eq10_of_eq5_eq8_eq9`
    consumes `c < ρ` and `ρ < branchSplit c` (strict inclusions on both
    ends); to discharge the right end at the closed boundary, weaken the
    sprint-010 inline `Set.Ioo`-form to also work at `ρ = branchSplit c`
    via `lt_of_le_of_lt hρ.2 hSplit_lt_one` → `ρ < branchSplit c` when
    `hρ.2 : ρ ≤ ρ₂` and `hρ₂_split : ρ₂ ≤ branchSplit c` and
    `hSplit_lt_one : branchSplit c < 1`. Wait — actually we have
    `ρ ≤ ρ₂ ≤ branchSplit c`, so `ρ ≤ branchSplit c`, not `ρ <
    branchSplit c`. To match the strict `<` consumed by `eq10_branch1_pointwise`,
    we need either `ρ₂ < branchSplit c` (strict) as a hypothesis or to
    state the conclusion on `Set.Ico ρ₁ ρ₂` with a separate boundary
    argument. **Generator's choice**: either tighten `hρ₂_split : ρ₂ <
    branchSplit c` (strict, matching the inline derivation) or split the
    `Icc` proof at the right boundary via the existing
    `Ioo_ae_eq_Icc` measure-theory pattern (which is what the inline
    derivation already does at lines 2655-2668). If choosing the
    `Ioo`-form below, this is moot.

  * **Option β: `Ioo` statement, then `Icc` lift via measure theory.**
    State the new theorem on `Set.Ioo ρ₁ ρ₂` (matching the strict-`<`
    chain in `eq10_branch1_pointwise`), and have `valid_of_eq5_eq8_eq9_
    subinterval_branch1` lift to a.e.-Icc as it currently does at lines
    2655-2668. The new theorem statement then reads
    `∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ...` and consumes `hρ₂_split : ρ₂ ≤
    branchSplit c` as in the current inline derivation (where `ρ ∈ Ioo
    ρ₁ ρ₂` gives `ρ < ρ₂ ≤ branchSplit c` so `ρ < branchSplit c` strict).
    **Option β is preferred** because it matches the existing inline
    derivation byte-for-byte; the `Icc` lift stays inside the consumer
    (`valid_of_eq5_eq8_eq9_subinterval_branch1`) where it currently lives.
    Sprint 086's mixed reducer will likewise lift to a.e.-Icc when
    composing its windows.

The body of the new theorem is the existing `Reduction.lean:2608-2652`
inline derivation, copied verbatim. Specifically, given `ρ ∈ Set.Ioo ρ₁ ρ₂`:

  1. `hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le`
  2. `hρ_split : ρ < PaperAxioms.branchSplit c := lt_of_lt_of_le hρ.2 hρ₂_split`
  3. Build `h10Derived` once (this can be a `let`-binding outside the
     `∀ ρ` quantifier, since it doesn't depend on `ρ`):
     ```lean
     have h10Derived :=
       PaperAxioms.eq10_of_eq5_eq8_eq9
         (sigmaMinus := PaperAxioms.sigmaMinus a b)
         (liftGap := paper.liftGap)
         hc_pos hSplit_lt_one
         paper.eq5_branch1_sigmaReduction
         paper.eq8_sigma_to_liftGap
         paper.eq9_liftGap_to_circleGap
     ```
  4. `h10 := h10Derived hcρ hρ_split` gives
     `branch1PointwiseFactor c (paperLambda K c) ρ * diskExcess ≤
      circleGap a b ρ`.
  5. Multiply both sides by `2ρ ≥ 0` (`mul_le_mul_of_nonneg_left`).
  6. Use the algebraic identity at `Reduction.lean:2639-2647` to rewrite
     `2 * ρ * branch1PointwiseFactor c (paperLambda K c) ρ` as
     `Korenblum.scalarIntegrand1 c (paperLambda K c) ρ` (`field_simp` +
     `ring`).
  7. Use `rfl` to identify `2 * ρ * paper.circleGap ρ` with
     `AnnulusIntegralReduction.annulusDensity paper.circleGap ρ`.

### 2. Refactor `valid_of_eq5_eq8_eq9_subinterval_branch1` body

Replace the inline `hPointwiseIoo` derivation at
`Proof/Reduction.lean:2608-2652` with a single application of the new
theorem:

```lean
have hPointwiseIoo :
    ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
      Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ
          * PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        AnnulusIntegralReduction.annulusDensity paper.circleGap ρ := by
  intro ρ hρ
  exact pointwise_branch1_on_Icc_eq5_eq8_eq9
    hc_pos hSplit_lt_one hcρ₁ hρ₁₂ hρ₂_split paper ρ
    -- weaken Set.Ioo to Set.Icc (or Set.Ioo if the new theorem is
    -- Ioo-shaped) via the appropriate inclusion
    (by
      refine ⟨le_of_lt hρ.1, ?_⟩
      exact le_of_lt hρ.2)
```

(Generator's choice on `Icc` vs `Ioo` shape per Option α/β above.)

The rest of `valid_of_eq5_eq8_eq9_subinterval_branch1` (lines 2533-2607
and 2654-2763) is unchanged.

### 3. NO edits to

  * `KorenblumPaper/` (read-only paper surface).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Any V0-V65 candidate file (no candidate ships this sprint).
  * Any per-candidate derived-theorem file under `Candidates/V<N>/`.
  * `Numerical_Library/` (no new wrappers).
  * `Proposals/` (no proposal filed this sprint).
  * `lemma.toml` (no new oracles, no new seed axioms, no new import-policy
    rows; the new theorem lives in already-allowed `Proof/Reduction.lean`).
  * `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` body (sprint 084's
    deliverable; untouched this sprint).

### 4. Bulletin and Experience append

Append one row each documenting:

  * The new theorem `pointwise_branch1_on_Icc_eq5_eq8_eq9` in
    `Proof/Reduction.lean` and its role as the missing structural building
    block for V38's seven-window c-push.
  * The refactor of `valid_of_eq5_eq8_eq9_subinterval_branch1` to consume
    the new theorem, confirming non-vacuity (the existing single-window
    Branch.one closing reducer still works).
  * Forward direction: sprint 086 builds the mixed-kernel multi-window
    closing reducer composing per-mode (sprint 084) and Branch.one (sprint
    085) windows; sprint 087 ships the Numerical_Library wrapper for
    fallback-box mass and the matching oracle row; sprint 088 ships V66
    at `c = 356401/1000000` (the +1.2e-2 V38 c-push).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
2. The new theorem `pointwise_branch1_on_Icc_eq5_eq8_eq9` exists in
   `Proof/Reduction.lean` with the signature shape outlined above
   (parameter names may vary; `Icc` or `Ioo` form acceptable).
3. The new theorem's body contains **only `theorem`/`lemma`-level
   constructs** — no new `axiom` declarations, no `sorry`, no
   `Section2Assumptions` field extensions.
4. The body of `valid_of_eq5_eq8_eq9_subinterval_branch1` invokes the new
   theorem at the location where the inline derivation at lines 2608-2652
   currently lives (verifiable by `grep` for the new theorem name inside
   the body of `valid_of_eq5_eq8_eq9_subinterval_branch1`).
5. `lake build ProofRefinement.Korenblum.Candidates.V65` still succeeds
   (the existing V65 candidate is downstream of `Proof/Reduction.lean`;
   confirming it still compiles verifies the refactor did not break the
   existing m=2 chain).
6. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V65.lean` reports `pass: true`
   with `score = 35646/100000` (V65's existing score is preserved).
7. V65's `axioms_used` set is **byte-for-byte identical** to its previous
   audit:
   `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V65.h_two_window_mass_certified_at_35646_sqrt,
   ProofRefinement.Korenblum.Candidates.V65.hH2_v64,
   ProofRefinement.Korenblum.Candidates.V65.hCircleGapInt_v64}`
   (or the V64-namespaced equivalents if V65 re-exports rather than
   re-declares; either acceptable).
8. `Bulletin.md` and `Experience.md` each gain one row per the standard
   pattern, naming the new theorem and the forward direction toward
   sprint 086+'s mixed-kernel reducer.

## Out of scope

  * Build the mixed-kernel multi-window closing reducer combining per-mode
    and Branch.one windows. That's sprint 086's job.
  * Push `c` past `35646/100000`. No new candidate ships this sprint.
  * Phase-0-verify the seven-window joint mass at `c = 356401/1000000`.
    That's sprint 087's job (Numerical_Library wrapper + Scratch witness).
  * Edit the existing per-mode reducer
    `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`. It stays as
    sprint 084's deliverable.
  * Edit other Branch.one-flavored reducers (e.g.
    `valid_of_eq10_subinterval_branch1` at `Reduction.lean:833`,
    `valid_of_eq10_eq11_straddling_window` at `Reduction.lean:2778`) to
    use the new theorem. The contract requires only one consumer
    (`valid_of_eq5_eq8_eq9_subinterval_branch1`) be updated as the
    non-vacuity check; further refactors are deferrable cleanup.
  * File `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64` into
    `Section2Assumptions`. Deferred.
  * Add new oracles or new `Numerical_Library/` wrappers. None needed for
    this sprint.

## Time budget

≤ 60 minutes runtime. The new theorem body is ~45 lines copied verbatim
from the existing inline derivation; the refactor of
`valid_of_eq5_eq8_eq9_subinterval_branch1` is one substitution at lines
2608-2652. Total Lean diff: ~80-120 lines added, ~40 lines deleted.

## Stop conditions

  * **All 8 acceptance criteria met**: `STATUS=READY_FOR_EVALUATION`. The
    new theorem ships, the existing single-Branch.one reducer still works,
    V65 still passes the evaluator, the harness is one structural
    sprint closer to the V38 seven-window c-push.

  * **The strict-vs-closed boundary issue (`ρ < branchSplit c` vs
    `ρ ≤ branchSplit c`) blocks the `Icc` form.** Fall back to **Option β**:
    state the theorem on `Set.Ioo ρ₁ ρ₂`, keep the `Icc`/a.e. lift inside
    the consumer where it currently lives (lines 2655-2668). This matches
    the existing inline derivation byte-for-byte. Document at
    `Scratch/sprint_085_obstruction.md` if even Option β stalls.

  * **The `eq10_of_eq5_eq8_eq9` chain produces a dependency-ordering issue**
    (e.g. `liftGap` field needs to be threaded through the new theorem's
    universe-polymorphic typeclass resolution): degrade gracefully — copy
    the inline `h10Derived` `let`-binding and the ordering side-conditions
    verbatim from the existing derivation; the new theorem is then a thin
    wrapper that fixes universe-instantiations. Document at
    `Scratch/sprint_085_obstruction.md`.

  * **A new free-floating axiom or trust-base expansion would be required**:
    do not ship it. Document at `Scratch/sprint_085_obstruction.md` and
    `STATUS=BLOCKED_NEEDS_HUMAN`. (This stop condition is highly unlikely
    given the new theorem is a pure refactor of an already-passing inline
    chain.)

  * **Generator session exceeds 60 minutes on the refactor**: ship the new
    theorem alone (acceptance criterion 2-3) without refactoring
    `valid_of_eq5_eq8_eq9_subinterval_branch1` (acceptance criterion 4).
    The refactor verification is the non-vacuity check, but a
    standalone theorem with the correct signature still discharges the
    structural-piece role for sprint 086+. Document the deferred refactor
    at `Scratch/sprint_085_partial.md` and `STATUS=BLOCKED` — the
    next planner decides whether to queue a one-line refactor follow-up
    or fold it into sprint 086.

## Notes for the generator

  * **Read first**: the existing inline derivation at
    `Proof/Reduction.lean:2606-2652` (your byte-for-byte template); the
    `eq10_of_eq5_eq8_eq9` theorem at
    `KorenblumPaper/PaperAxioms.lean:391-440` (the chain you'll invoke
    for `h10Derived`); the existing per-mode pointwise template
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    at `KorenblumPaper/OneModePaperBridge.lean:306` (the *shape* you're
    matching for sprint 086's mixed reducer); the consumer
    `valid_of_eq5_eq8_eq9_subinterval_branch1` at
    `Proof/Reduction.lean:2513-2763` (the existing reducer whose body
    you'll refactor).

  * **`paperScalarIntegrand1_intervalIntegrable`**. The integrability
    of `Korenblum.scalarIntegrand1` on `[ρ₁, ρ₂] ⊂ [c, branchSplit c]`
    is already proved by
    `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
    (used at `Reduction.lean:2603-2605` inside the existing reducer).
    Sprint 086 will need to invoke this for fallback-window
    integrability premises; this sprint does not directly need it
    inside the new theorem (the new theorem consumes the pointwise
    bound, not integrability).

  * **`Set.Icc` vs `Set.Ioo` choice**. The existing inline derivation
    at lines 2606-2652 uses `Set.Ioo ρ₁ ρ₂` (strict on both ends), then
    lifts to a.e.-Icc via `Ioo_ae_eq_Icc` at lines 2655-2668 inside the
    consumer. Mirroring this `Ioo` form (Option β) is the safest path
    for the new theorem; Option α is a stretch goal. If Option β is
    chosen, the consumer's `Icc`-lift code at lines 2655-2668 is
    unchanged.

  * **`liftGap` field threading**. The `eq10_of_eq5_eq8_eq9` chain
    consumes `paper.liftGap` (a field of `Section2Objects`). The new
    theorem's body will pass `paper.liftGap` explicitly via
    `(liftGap := paper.liftGap)`, matching the inline derivation at
    `Reduction.lean:2553-2559`.

  * **Don't break the m=2 chain**. After the refactor,
    `valid_of_eq5_eq8_eq9_subinterval_branch1` must still close
    `ValidKorenblumBound c` for any consumer that calls it. The existing
    candidate set does not currently invoke this reducer (V64/V65 use
    the per-mode m=2 reducer), but the reducer's compilation itself is a
    regression check. Verify by `lake build ProofRefinement.Korenblum.Proof.Reduction`
    (acceptance criterion 1) and `lake build ProofRefinement.Korenblum.Candidates.V65`
    (acceptance criterion 5).

  * **No new files this sprint**. Do not create per-candidate
    derived-theorem files under `Candidates/V65/` or `Candidates/V66/`;
    no candidate ships. Do not edit
    `lemma.toml`. The diff is contained to `Proof/Reduction.lean`,
    `Bulletin.md`, and `Experience.md`.

  * **Sprint 086 preview** (for context, not for action this sprint):
    sprint 086 will build a new closing reducer
    `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
    accepting a per-window `kind : Fin (n+1) → KernelKind` tag where
    `KernelKind = ModeJ Nat | Branch1`. On `ModeJ j`-tagged windows it
    invokes
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    (sprint 084's discharge); on `Branch1`-tagged windows it invokes
    this sprint's `pointwise_branch1_on_Icc_eq5_eq8_eq9`. The structure
    mirrors sprint 084's general-`m` reducer but with case-dispatch on
    `kind i` per window. Estimated size: ~400-500 lines including the
    per-window setup. Sprint 087 supplies the matching numerical wrapper
    and oracle row at `c = 356401/1000000`; sprint 088 ships V66.
