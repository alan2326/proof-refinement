# Sprint 086: mixed-kernel multi-window τ-partition closing reducer (per-mode + Branch.one fallback)

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V65.lean`
**Target file**: no required new candidate this sprint; new theorem
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` in
`Proof/Reduction.lean`. Optional `Candidates/V66.lean` as a
non-vacuity tie-with-V65 specializer (see Stop conditions).
**Direction**: section2-proof (analytic Lean derivation generalizing sprint
084's per-mode m-window reducer to mixed per-mode + Branch.one fallback
windows; the missing structural piece for V38's seven-window c-push to
`c = 356401/1000000`)

## Goal

Add a **single new closing reducer** in `Proof/Reduction.lean` that
generalizes `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` (sprint
084, at `Reduction.lean:8424`) to admit **two kinds of windows** within a
single τ-partition of `(c, 1)`:

  * **Per-mode windows** (`ModeJ j` for `j ≥ 1`) — discharged by
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`,
    same as sprint 084.
  * **Branch.one fallback windows** (`Branch1`) — discharged by
    `pointwise_branch1_on_Ioo_eq5_eq8_eq9` (sprint 085's standalone
    theorem at `Reduction.lean:2522`), with the existing `Ioo`-shaped
    output lifted to a.e.-`Icc` via `Ioo_ae_eq_Icc` so the per-window
    closing step can use `mass_mul_le_annulusSlice_of_integral_bound_ae`
    (already used by `valid_of_eq5_eq8_eq9_subinterval_branch1`).

The reducer accepts a per-window kind tag

```lean
inductive KernelKind where
  | modeJ (j : ℕ) : KernelKind
  | branch1 : KernelKind
```

(or an equivalent `Sum ℕ Unit` / `ℕ`-with-sentinel encoding — the contract
fixes the *shape*, not the spelling), threads kind dispatch through the
per-window steps, and concludes `ValidKorenblumBound c` from the same
joint-mass hypothesis as sprint 084 with the kind-dependent
`modeIntegrand_w` per window.

The new reducer **directly unlocks Sprint C of the Bulletin's V38
three-sprint chain** (the +1.2e-2 c-push from V64's `35646/100000` to
V38's `356401/1000000`). Sprint 087 will ship the
`Numerical_Library` fallback-box mass wrapper and oracle row at
V38's `c`; sprint 088 will ship V66 at V38's `c` composing four mode
windows (j*=4,3,2,1) and three fallback boxes via this sprint's mixed
reducer. Neither downstream sprint can run until this reducer exists.

## Why

### Why this is the right next sprint

The Bulletin's 2026-05-04 EXPLICIT V38 REFERENCE directive (lines 17–419)
inlines V38's seven-window split at `c = 356401/1000000`:

    fallbackA   Branch.one box-sum (boxes 0000..0003)   eq(5)
    mode4       per-mode j*=4                            H_4
    fallbackB   Branch.one box (box 0006)                eq(5)
    mode3       per-mode j*=3                            H_3
    fallbackC   Branch.one box (box 0012)                eq(5)
    mode2       per-mode j*=2                            H_2
    mode1       per-mode j*=1                            H_1 [= eq (6)]

**No reducer in `Proof/Reduction.lean` currently admits a τ-partition
that mixes per-mode and Branch.one windows.** Sprint 084's general-`m`
reducer is uniformly per-mode (every window discharges via
`ModeBridge.scalarIntegrand c (j i)`); there is no provision for a
Branch.one fallback window inside it. Sprint 085 produced the Branch.one
*pointwise* theorem (the missing per-window discharge ingredient), but
no closing reducer yet composes the two pointwise families.

The chain V38 traverses is:

  * **Sprint 084 (shipped)** — general-`m` per-mode reducer, exists at
    `Reduction.lean:8424`. Subsumed sprint 078's m=2 reducer; V65 ties
    V64 byte-for-byte.
  * **Sprint 085 (shipped)** — standalone Branch.one pointwise theorem
    `pointwise_branch1_on_Ioo_eq5_eq8_eq9` at `Reduction.lean:2522`.
    Pure refactor; V65 unchanged.
  * **Sprint 086 (this) — mixed-kernel multi-window reducer.** Composes
    sprint 084's per-mode discharge with sprint 085's Branch.one
    discharge under a per-window `kind` dispatch.
  * Sprint 087+ — `Numerical_Library.export_mode_hybrid_boxes` Phase 0
    sweep at V38's `c`, plus a fallback-box-mass certified-rational
    oracle row.
  * Sprint 088+ — V66 at `c = 356401/1000000` composing four mode
    windows + three fallback boxes via this sprint's mixed reducer.

**The +1.2e-2 V64 → V38 c-push is two and a half orders of magnitude
larger than the +1e-5 V52 → V64 push.** It is the Bulletin's standing
prize. The mixed reducer is the structural piece on which it depends.

### Why this is bounded for one session

Sprint 084's per-mode general reducer is ~400 lines of body
(`Reduction.lean:8424-8825`). The mixed-kernel reducer differs in three
places:

  * **Per-window pointwise step (Step 2 in sprint 084).** Replace the
    uniform call to
    `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    with a per-window match on `kind i`:
    - `kind i = .modeJ (j i)` → unchanged, sprint 084's call.
    - `kind i = .branch1` → call `pointwise_branch1_on_Ioo_eq5_eq8_eq9`
      with the window's `(ρStart i, ρStop i)`, then lift `Ioo → a.e.-Icc`.
    Estimated +50 lines.

  * **Per-window mode integrand and integrability (Step 5 + Step 6 in
    sprint 084).** Define a kind-dispatched `modeIntegrand` per window:
    - `kind i = .modeJ (j i)` → `ModeBridge.scalarIntegrand c (j i)
      (paperLambda K c) ρ`.
    - `kind i = .branch1` → `Korenblum.scalarIntegrand1 c (paperLambda K c) ρ`.
    The per-window mass is then `∫ ρ in (ρStart i)..(ρStop i),
    modeIntegrand_w ρ` for the kind-appropriate integrand. The
    integrability witness for `scalarIntegrand1` already exists as
    `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
    (used in `valid_of_eq5_eq8_eq9_subinterval_branch1`). Estimated
    +30 lines.

  * **Per-window mass-bound step (Step 6 in sprint 084).** For per-mode
    windows, sprint 084's `mass_mul_le_annulusSlice_of_integral_bound`
    works directly because the pointwise step is `Icc`-shaped. For
    Branch.one windows, the pointwise step is `Ioo`-shaped, so use
    `mass_mul_le_annulusSlice_of_integral_bound_ae` (with the
    `Ioo_ae_eq_Icc` measure-theory premise discharged exactly as in
    `valid_of_eq5_eq8_eq9_subinterval_branch1`). The case split on
    `kind i` selects the appropriate variant. Estimated +30 lines.

  * **All other steps (1, 3, 4, 7, 8, 9, 10, 11) are unchanged.**
    Adjacency-glue, `innerExcess_le_of_window_bounds` final closer,
    side-slice non-negativity for `(c, ρStart 0)` and `(ρStop n, 1)`,
    and the `1 ≤ Σ mass_w` finale all carry over verbatim from sprint
    084.

Estimated total body: ~500-550 lines, ~30% larger than sprint 084's
~400-line body. The signature gains:
  * one new field `kind : Fin (n+1) → KernelKind` (and the
    `KernelKind` inductive itself — ~5 lines outside the theorem),
  * the τ-bound conjunct relaxed from
    `(∀ i, OneModeTail.tau (j i - 1) ≤ c²/ρStop i² ∧ c²/ρStart i² ≤ OneModeTail.tau (j i))`
    to a kind-dispatched form
    `(∀ i, kind i = .modeJ (j i) → τ-bounds; kind i = .branch1 → ρStop i ≤ branchSplit c)`,
  * the integrability witness conjunct relaxed similarly to a
    kind-dispatched `IntervalIntegrable …`,
  * the joint-mass hypothesis relaxed to a kind-dispatched sum.

The signature itself grows by ~30-40 lines.

**Total session work**: ~550 lines added (theorem + body + `KernelKind`
definition). This is comparable to the largest one-session deliverables
the harness has shipped (sprint 084 = ~400 lines; sprint 014 = ~290
lines). It is bounded for one Generator session given the per-step
templates from sprint 084 and the Branch.one pointwise theorem from
sprint 085.

### Why this is not a numerical c-push in disguise

This sprint ships **no `c_value` improvement**. The new reducer is purely
a structural composition; the joint-mass hypothesis is parametric, with
no numerical instantiation in this sprint. V66 (if shipped this sprint)
ties V65 by specializing the new mixed reducer at `kind = .modeJ` for
all windows, recovering sprint 084's m=2 chain byte-for-byte.

The `c_value` push happens in sprint 088 (V66 at `c = 356401/1000000`,
the +1.2e-2 V38 prize), supported by sprint 087's numerical oracle.
**This sprint is the analytic Lean derivation that unlocks sprint 088.**

The brief explicitly endorses analytic Lean derivations preparing a
future c-push — see `AGENT_BRIEF.md` "High-value directions" rule 3
("Prove a stronger direct reduction than the current seed bridge") and
the planner-agent definition's description of preparing "a precise
oracle-backed subclaim that directly supports a future increase in
`c_value`."

### Three (and more) distinct directions considered (and why this one wins)

The planner brief requires enumerating at least three distinct sprint
shapes pursuing different analytical chains, with the strongest objection
to each, before settling.

1. **Direction A (this sprint): mixed-kernel multi-window reducer
   composing sprint 084's per-mode discharge and sprint 085's Branch.one
   discharge.** Strongest objection: this is the largest one-session
   deliverable (~550 lines) the harness has attempted, with a real risk
   of overrun. Counter: the per-step structure is fully templated by
   sprint 084 (the `KernelKind` dispatch is mechanical case-splitting,
   not new mathematics); the Branch.one pointwise theorem is already
   shipped; the `Ioo → a.e.-Icc` lift is already templated by
   `valid_of_eq5_eq8_eq9_subinterval_branch1`. The risk is mitigated by
   a partial-deliverable stop condition (Stop conditions §3 below).

2. **Direction B: Branch.one-only multi-window τ-partition reducer
   (mirror of sprint 084 with all windows Branch.one).** Strongest
   objection: this still leaves the actual mixed dispatch unbuilt;
   V38's seven-window split *interleaves* per-mode and Branch.one
   windows, so a Branch.one-only reducer doesn't close the chain.
   **Demoted as a detour** that produces no V38 unblocking by itself.

3. **Direction C: a sibling c-push along the m=2 axis at
   `c = 35647/100000` or `c = 35650/100000`.** Numerical-only, capped
   at +8e-5 above V64 by sprint 078's m=2 ceiling at `c ≈ 0.35654`
   (margin 4.2e-5). **Demoted as numerical headroom** that consumes
   one session of budget for ≪1% of the V38 prize.

4. **Direction D: Phase 0 seven-window numerical sweep at
   `c = 356401/1000000` to verify V38's audited mass before committing
   to the Lean adapter architecture.** Strongest objection: the
   Bulletin already inlines V38's audited numbers
   (`c = 0.356401 → total mass = 1.000012381570`); the sweep just
   reproduces a known-good result. Useful as a sanity check inside
   sprint 087 (where the oracle wrapper lives), but not as a standalone
   sprint that occupies session budget. **Demoted; folded into sprint
   087.**

5. **Direction E: split sprint 086 into 086a (KernelKind + per-window
   integrand definition + Branch.one a.e.-Icc lift wrapper) and 086b
   (the full mixed reducer).** Strongest objection: the split adds one
   extra c-tying sprint to the chain; given that sprint 085 already
   pre-built the Branch.one pointwise piece, the wrapper is only ~30
   lines and folds naturally into the reducer body. **Demoted as
   over-fragmenting.** Falls back automatically via Stop conditions §3
   if the full reducer overruns the session.

6. **Direction F: hoist V53/V54/V55/V57/V58/V60 derived theorems into
   `Proof/`.** Pure cleanup, no analytic novelty, no path to V38's `c`.
   **Demoted as deferrable cleanup.**

7. **Direction G: file `proposal_004` to migrate `hH2_v64`/
   `hCircleGapInt_v64` into `Section2Assumptions` fields.** The
   AGENT_BRIEF's four-condition guide for proposal-filing is **not**
   satisfied: there is no "tried hard and failed" attempt sprint behind
   it; the H² source has not been attacked in Lean; the migration does
   not push `c`. **Demoted; would not improve the score even if
   approved.** Defer to sprint 089+.

8. **Direction H: file proposal for the `KernelKind` inductive type as
   a trust-base expansion.** Not needed — `inductive KernelKind` is a
   pure Lean inductive in user-space (`Proof/Reduction.lean`), neither
   a paper-axiom nor a Mathlib-import expansion. No proposal required.

Direction A wins on **expected analytical novelty per bounded-Generator-
session**: it is the smallest piece that materially unblocks the V38
seven-window c-push (Sprint C of the Bulletin's chain), it has fully
templated per-step structure from sprints 084 + 085, and its acceptance
criteria are concretely falsifiable in one session.

### Why the new reducer fits the V38 architecture

The Bulletin (lines 226–253) inlines V38's three gluing theorems already
in `KorenblumPaper.AnnulusIntegralReduction`:
  * `annulusSlice_add_adjacent` (existing, used by sprint 084).
  * `mass_mul_le_annulusSlice_of_integral_bound` (`Icc` form) and
    `mass_mul_le_annulusSlice_of_integral_bound_ae` (a.e.-`Icc` form,
    used by sprint 010's branch.one closing reducer).
  * `innerExcess_le_of_window_bounds` (Finset-indexed final closer,
    used by sprint 084).

The mixed reducer's body is exactly: per-window discharge → per-window
mass·innerExcess ≤ slice → adjacency-glue → final
`innerExcess_le_of_window_bounds` over `Finset.univ : Finset (Fin (n+1))`,
with the only differences from sprint 084 being kind-dispatched
discharge and integrand. The architecture is unchanged.

## Concrete edits expected

### 1. `KernelKind` inductive in `Proof/Reduction.lean`

Add immediately above the new theorem (or near the top of the file
alongside other helpers). Suggested shape:

```lean
inductive KernelKind where
  | modeJ (j : ℕ) : KernelKind
  | branch1 : KernelKind
  deriving DecidableEq, Repr
```

The `DecidableEq` and `Repr` derivations are convenience for the proof
body's case splits and any error messages; both are routine.

The generator may use a `Sum ℕ Unit` or `Option ℕ` encoding instead if
it makes the proof body cleaner; the contract fixes the *behavior*
(per-window discharge selector with two cases), not the spelling.

### 2. New theorem in `Proof/Reduction.lean`

Add `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
immediately after `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
(around line 8825). Suggested signature shape (parameter names may vary):

```lean
theorem valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSplit_lt_one : PaperAxioms.branchSplit c < 1)
    {n : ℕ}
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ (ρStart ρStop : Fin (n + 1) → ℝ)
          (kind : Fin (n + 1) → KernelKind),
          (∀ i : Fin (n + 1), c < ρStart i) ∧
          (∀ i : Fin (n + 1), ρStart i ≤ ρStop i) ∧
          (∀ i : Fin (n + 1), ρStop i < 1) ∧
          (∀ i : Fin n, ρStop i.castSucc = ρStart i.succ) ∧
          -- Per-mode windows: τ-bounds with mode `j`.
          (∀ i : Fin (n + 1), ∀ j : ℕ,
            kind i = KernelKind.modeJ j →
              1 ≤ j ∧
              OneModeTail.tau (j - 1) ≤ c ^ 2 / ρStop i ^ 2 ∧
              c ^ 2 / ρStart i ^ 2 ≤ OneModeTail.tau j) ∧
          -- Branch.one fallback windows: ρStop i ≤ branchSplit c.
          (∀ i : Fin (n + 1),
            kind i = KernelKind.branch1 →
              ρStop i ≤ PaperAxioms.branchSplit c) ∧
          -- Shared summability cells (same six as sprint 084).
          Summable (fun n' => OneModePaperBridge.plusSeq a b n' *
                                c ^ (2*n'+2) / (n'+1 : ℝ)) ∧
          Summable (fun n' => OneModePaperBridge.plusSeq a b n' * c^(2*n')) ∧
          Summable (fun n' => OneModePaperBridge.minusSeq a b n' *
                                c ^ (2*n'+2) / (n'+1 : ℝ)) ∧
          Summable (fun n' => OneModePaperBridge.minusSeq a b n' * c^(2*n')) ∧
          Summable (fun n' => OneModePaperBridge.minusSeq a b n' *
                                OneModeKernel.weight c n') ∧
          (∀ ⦃ρ⦄, c < ρ → ρ < 1 →
            Summable (fun n' => OneModePaperBridge.minusSeq a b n' * ρ^(2*n'))) ∧
          -- circleGap integrability on (c, 1).
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1 ∧
          -- Per-window kind-dispatched scalar-integrand integrability.
          (∀ i : Fin (n + 1),
            (∀ j : ℕ, kind i = KernelKind.modeJ j →
              IntervalIntegrable
                (fun ρ => ModeBridge.scalarIntegrand c j
                          (WangOuter.paperLambda K c) ρ)
                volume (ρStart i) (ρStop i)) ∧
            (kind i = KernelKind.branch1 →
              IntervalIntegrable
                (fun ρ => Korenblum.scalarIntegrand1 c
                          (WangOuter.paperLambda K c) ρ)
                volume (ρStart i) (ρStop i))) ∧
          -- diskExcess ≤ innerSeriesExcess.
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
            OneModePaperBridge.innerSeriesExcess a b c ∧
          -- Joint multi-window kind-dispatched mass.
          (1 : ℝ) ≤
            ∑ i : Fin (n + 1),
              match kind i with
              | KernelKind.modeJ j =>
                ∫ ρ in (ρStart i)..(ρStop i),
                  ModeBridge.scalarIntegrand c j
                    (WangOuter.paperLambda K c) ρ
              | KernelKind.branch1 =>
                ∫ ρ in (ρStart i)..(ρStop i),
                  Korenblum.scalarIntegrand1 c
                    (WangOuter.paperLambda K c) ρ) :
    ValidKorenblumBound c := by
  …
```

(The `match` inside the joint-mass cell may need an auxiliary `let
modeIntegrand : Fin (n+1) → ℝ → ℝ` to keep the term well-formed; the
generator picks the cleanest encoding.)

Proof body proceeds as outlined in §"Why this is bounded for one session"
above. Two acceptable structural options:

  * **Option α (preferred): kind-dispatched per-window steps with
    uniform `mass_mul_le_annulusSlice_of_integral_bound_ae` closer.**
    Use the a.e. variant of the per-window closer for *both* per-mode
    and Branch.one windows; the per-mode pointwise step (which is
    naturally `Icc`-shaped) is trivially upgraded to a.e.-`Icc` via
    `Filter.eventually_of_forall`. This unifies the per-window closing
    chain at the cost of slight redundancy on per-mode windows. Cleanest
    body.

  * **Option β: kind-dispatched per-window closer.** Use
    `mass_mul_le_annulusSlice_of_integral_bound` (`Icc` form) on
    per-mode windows and `..._ae` on Branch.one windows. Slightly more
    code but more faithful to each chain's natural shape.

The generator picks Option α or β. The contract does not pin the choice.

### 3. Optional: `Candidates/V66.lean` (non-vacuity tie-with-V65)

If the new reducer body comes in well under the time budget (acceptance
criterion 1+2 met with ≥ 30 minutes remaining), ship a thin
specializer `Candidates/V66.lean` that **invokes the new mixed reducer
at `m = 2` with `kind = fun _ => KernelKind.modeJ …`** (i.e. all per-mode,
no Branch.one) and recovers V65's discharge byte-for-byte. Goals:

  * `c_value = 35646/100000` (same as V65, no c-push).
  * Module imports: same as V65 (`Proof.Main`, `Proof.Reduction`,
    `Candidates.V63.{Integrability,Summability,DiskInnerSeriesBridge}`,
    `Candidates.V64.TauWindowEndpoints`).
  * Re-export V64's three free axioms (`hH2_v64`,
    `hCircleGapInt_v64`, `h_two_window_mass_certified_at_35646_sqrt`)
    or re-import them; either acceptable.
  * `axioms_used` byte-for-byte identical to V65.
  * V66's body invokes
    `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` with
    `kind = fun _ => KernelKind.modeJ (j := 2 or 1)` per window.

V66's purpose is to prove the new mixed reducer **strictly subsumes** the
per-mode-only reducer at the m=2 specialization. If the generator is
short on time, **the V66 candidate is optional**; only the new theorem
is required. See Stop conditions §2.

### 4. NO edits to

  * `KorenblumPaper/` (read-only paper surface).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Existing `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` body
    (sprint 084's deliverable; do not refactor).
  * Existing `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` body
    (sprint 078's deliverable; load-bearing for V64).
  * Existing `valid_of_eq5_eq8_eq9_subinterval_branch1` body (sprint
    019/085's deliverable).
  * `pointwise_branch1_on_Ioo_eq5_eq8_eq9` body (sprint 085's
    deliverable; reused as-is).
  * Any V0-V65 candidate file. V65 still uses sprint 084's per-mode-only
    reducer; do not migrate it to the new mixed reducer this sprint.
  * Per-candidate derived-theorem files under `Candidates/V<N>/`.
  * `Numerical_Library/` (no new wrappers; oracle work belongs in
    sprint 087).
  * `Proposals/` (no proposal filed this sprint).
  * `lemma.toml` `[seed_axioms]`, `[[oracles]]`, or
    `[workspace_import_policy]` (no new oracles, no new seed axioms,
    no new import-policy rows; the new theorem and `KernelKind`
    inductive live in already-allowed `Proof/Reduction.lean`).
    The new V66 candidate (if shipped) requires
    `"ProofRefinement.Korenblum.Candidates.V66"` in `[import_policy]`
    if it is not already covered by a wildcard rule (check first).

### 5. Bulletin and Experience append

Append one row each documenting:

  * The new theorem
    `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` and the
    new `KernelKind` inductive in `Proof/Reduction.lean`, naming sprint
    084 (per-mode discharge) and sprint 085 (Branch.one pointwise
    discharge) as the two analytical inputs composed by this reducer.
  * Confirmation that V65 still passes (the existing per-mode-only
    chain is undisturbed) and V66 (if shipped) ties V65 by specializing
    the new mixed reducer at `kind = fun _ => .modeJ`.
  * Forward direction: sprint 087 ships the
    `Numerical_Library.export_mode_hybrid_boxes` Phase 0 sweep + a
    fallback-box-mass certified-rational oracle row at
    `c = 356401/1000000`; sprint 088 ships V66 (or V67) at
    V38's `c` composing four mode windows + three fallback boxes via
    this sprint's mixed reducer (the +1.2e-2 V38 prize).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
2. The new `KernelKind` inductive (or equivalent encoding) exists in
   `Proof/Reduction.lean` with the two-constructor shape outlined above.
3. The new theorem
   `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` exists
   in `Proof/Reduction.lean` with the signature shape outlined above
   (parameter names may vary; the per-window kind-dispatch and
   joint-mass cell shapes are required).
4. The new theorem's body contains **only `theorem`/`lemma`-level
   constructs** — no new `axiom` declarations, no `sorry`, no new
   `Section2Assumptions` field extensions. Per-window discharge invokes
   `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
   on `kind i = .modeJ j` and `pointwise_branch1_on_Ioo_eq5_eq8_eq9`
   on `kind i = .branch1` (verifiable by `grep` for both names inside
   the new theorem's body).
5. `lake build ProofRefinement.Korenblum.Candidates.V65` still succeeds
   (V65 uses sprint 084's per-mode-only reducer; verifying it still
   compiles confirms the new reducer addition did not break the
   existing chain).
6. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V65.lean` reports `pass: true`
   with `score = 35646/100000` and `axioms_used` byte-for-byte
   identical to V65's previous audit (regression check; V65 is
   undisturbed).
7. **Optional (only if V66 is shipped this sprint)**:
   `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds;
   evaluator reports `pass: true` with `score = 35646/100000` (ties
   V65; the c-push is sprint 088's job); V66's `axioms_used` is
   byte-for-byte identical to V65's audit; V66's body invokes
   `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
   with `kind = fun _ => KernelKind.modeJ …` (verifiable by `grep`
   for the new theorem name in V66 source).
8. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern, naming the new mixed reducer, `KernelKind`, the
   composition pattern (sprint 084 + sprint 085), and the forward
   direction toward V38's `c` via sprints 087-088.

## Out of scope

  * Push `c` past `35646/100000`. V66 (if shipped) ties V65; pushing
    `c` to V38's `356401/1000000` is sprint 088's job, after sprint
    087's numerical oracle is in place.
  * Phase-0-verify seven-window joint mass at `c = 356401/1000000`.
    That's sprint 087's job.
  * Build the `Numerical_Library.export_mode_hybrid_boxes` wrapper or
    any oracle row at V38's `c`. That's sprint 087's job.
  * Build a Wang-eq(5) Branch.one **box-sum** mass certifier (V38's
    `fallbackA` is a box-sum of four boxes 0000..0003; this requires a
    `WangBoxQ.totalMassQ Branch.one cQ boxes` mass extractor that is
    not yet in the workspace). The mixed reducer treats each fallback
    box as a single Branch.one window; sprint 087 will compose
    box-sums via `WangBoxQ.totalMassQ` if that adapter is needed for
    V38's `fallbackA`.
  * Edit existing reducers (`valid_of_perMode_twoWindow…`,
    `valid_of_perMode_multiWindow…`, `valid_of_eq5_eq8_eq9_subinterval_branch1`).
    They stay in place as load-bearing dependents.
  * Edit V0–V65 candidate files. None migrate to the new mixed reducer
    this sprint.
  * File `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64` into
    `Section2Assumptions`. Deferred to sprint 089+.
  * Hoist V53/V54/V55/V57/V58/V60 derived theorems into `Proof/`.
    Deferred cleanup.

## Time budget

≤ 150 minutes runtime. The new theorem is ~500-550 lines of Lean
following sprint 084's body verbatim with three localized substitutions
(per-window discharge, per-window integrand, per-window closing step);
the `KernelKind` inductive is ~5 lines. V66 (if shipped) is ~100 lines
mirroring V65's specialization pattern.

## Stop conditions

  * **All acceptance criteria 1-6 + 8 met (V66 shipped or skipped per
    §"Optional")**: `STATUS=READY_FOR_EVALUATION`. The new mixed reducer
    ships, V65 still passes, the harness is one structural sprint
    closer to V38's `c`.

  * **The reducer ships under the time budget but V66 is not shipped**:
    acceptance criterion 7 is skipped (it is explicitly optional).
    Acceptance is achieved on criteria 1-6 + 8. The next planner queues
    sprint 087 (Numerical_Library oracle) and the V66 specializer can
    fold into sprint 088. `STATUS=READY_FOR_EVALUATION` (the evaluator
    is run on V65 for the regression check per criterion 6, not on a
    new V66; this is consistent with sprint 085's
    `STATUS=READY_FOR_EVALUATION` shape with V65 as the regression
    candidate).

  * **The mixed-kernel proof body exceeds 100 minutes on a single
    proof step** (e.g. the `match`-pattern in the joint-mass cell
    causes term-rewriting issues, or the Branch.one a.e.-Icc lift
    inside the reducer body fails to type-check uniformly): **degrade
    gracefully** by falling back to **Direction E** of the planner's
    enumeration — split the deliverable. Ship only:
    - the `KernelKind` inductive,
    - a thin Branch.one `Icc`-form wrapper theorem
      `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae` that lifts sprint
      085's `Ioo`-form output to a.e.-`Icc` (~30 lines, verbatim of
      the lift code in `valid_of_eq5_eq8_eq9_subinterval_branch1`'s
      body),
    - the new theorem's **statement** with the body deferred to a
      `Scratch/sprint_086_partial_proof.lean` file (do **NOT** ship a
      `sorry`-bearing theorem in `Proof/Reduction.lean` — `sorryAx` is
      a hard Evaluator fail).
    `STATUS=BLOCKED` with an obstruction note at
    `Scratch/sprint_086_obstruction.md` precisely naming the failing
    proof step. Sprint 087 then queues with a partial-state pickup
    contract.

  * **A new free-floating axiom or trust-base expansion would be
    required**: do not ship it. Document at
    `Scratch/sprint_086_obstruction.md` and `STATUS=BLOCKED_NEEDS_HUMAN`.
    (Highly unlikely — the `KernelKind` inductive and
    `mass_mul_le_annulusSlice_of_integral_bound_ae` already exist.)

  * **V66 is shipped but ties V65 with a non-byte-for-byte axiom audit**
    (e.g. a stray `Decidable` instance leaks an extra axiom from the
    `KernelKind` `DecidableEq` derivation): re-attempt with `Sum ℕ Unit`
    encoding instead of `inductive KernelKind`. If still failing,
    document at `Scratch/sprint_086_v66_axiom_drift.md` and
    `STATUS=BLOCKED` — the next planner decides whether to suppress
    the derivation or accept the drift as a one-axiom expansion of the
    audit.

## Notes for the generator

  * **Read first**:
    - sprint 084's per-mode reducer at `Proof/Reduction.lean:8424-8825`
      (your structural template — your reducer is a kind-dispatched
      generalization);
    - sprint 085's standalone Branch.one pointwise theorem at
      `Proof/Reduction.lean:2522-2584` (your Branch.one discharge
      ingredient);
    - the existing branch-1 closing reducer
      `valid_of_eq5_eq8_eq9_subinterval_branch1` at
      `Proof/Reduction.lean:2607-2763` for the `Ioo → a.e.-Icc` lift
      pattern via `Ioo_ae_eq_Icc` (your template for handling Branch.one
      windows inside the mixed reducer);
    - `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
      (used by sprint 084 — the per-mode discharge).

  * **Per-window integrand kind dispatch.** Define a single
    `let modeIntegrand : Fin (n+1) → ℝ → ℝ := fun i ρ =>
       match kind i with
       | KernelKind.modeJ j =>
         ModeBridge.scalarIntegrand c j (paperLambda K c) ρ
       | KernelKind.branch1 =>
         Korenblum.scalarIntegrand1 c (paperLambda K c) ρ`
    binding once at the top of the proof, and use it uniformly in the
    per-window mass cell, integrability cell, and pointwise step.

  * **Per-window pointwise step kind dispatch.** Inside Step 2 (sprint
    084's pointwise step), case-split on `kind i`:
    ```lean
    rcases hKind : kind i with j | _
    · -- kind i = .modeJ j: invoke sprint 084's per-mode discharge
      ...
    · -- kind i = .branch1: invoke sprint 085 + Ioo_ae_eq_Icc lift
      ...
    ```

  * **Branch.one a.e.-Icc lift.** The `pointwise_branch1_on_Ioo_eq5_eq8_eq9`
    theorem returns on `Set.Ioo ρ₁ ρ₂`. To match the
    `mass_mul_le_annulusSlice_of_integral_bound_ae` premise (which
    requires an a.e.-`Icc` pointwise hypothesis), wrap with:
    ```lean
    have hPointwiseAe :
        ∀ᵐ ρ ∂(volume.restrict (Set.Icc ρ₁ ρ₂)),
          modeIntegrand_branch1 ρ * innerExcess ≤ annulusDensity ρ := by
      have hIooSub : Set.Ioo ρ₁ ρ₂ ⊆ Set.Icc ρ₁ ρ₂ := Set.Ioo_subset_Icc_self
      filter_upwards [Ioo_ae_eq_Icc] with ρ hρ_in_Ioo
      exact pointwise_branch1_on_Ioo_eq5_eq8_eq9 hc_pos hSplit_lt_one
        (hStartLt i) (hBranch1_split i hKind) paper ρ hρ_in_Ioo
    ```
    (The exact `Ioo_ae_eq_Icc` invocation is templated by
    `valid_of_eq5_eq8_eq9_subinterval_branch1`'s body — copy that
    pattern.)

  * **Per-window closing step.** For Option α (uniform a.e.-Icc),
    invoke `mass_mul_le_annulusSlice_of_integral_bound_ae` for both
    kinds; the per-mode pointwise hypothesis on `Icc` is trivially
    upgraded to a.e.-`Icc` via `Filter.eventually_of_forall`. For
    Option β, invoke `mass_mul_le_annulusSlice_of_integral_bound`
    on per-mode and `..._ae` on Branch.one. Either is acceptable.

  * **Adjacency-glue and final closer (Steps 7-11).** **Unchanged**
    from sprint 084. Copy the existing `sum_annulusSlice_collapse_adjacent`
    invocation, the side-slice non-negativity for `(c, ρStart 0)` and
    `(ρStop n, 1)`, and the final `innerExcess_le_of_window_bounds`
    call verbatim.

  * **Step 8 (joint mass)** uses the kind-dispatched `modeIntegrand`
    binding from Step 0. Each per-window integral is well-typed via
    the `match`/`let`-binding; the `1 ≤ Σ_i ∫ modeIntegrand_i` premise
    in `h_witness` is the joint-mass hypothesis.

  * **`mass_mul_le_annulusSlice_of_integral_bound_ae` exists** in
    `KorenblumPaper.AnnulusIntegralReduction` (used by
    `valid_of_eq5_eq8_eq9_subinterval_branch1` at
    `Reduction.lean:2654-2762`). Confirm its exact signature before
    starting; the contract assumes it takes the same shape as the
    `Icc` version with an `∀ᵐ`-quantified pointwise premise.

  * **Generator capability budget.** The reducer body is mechanically
    similar to sprint 084's body with localized kind-dispatch
    additions. If you find yourself writing more than ~80 lines of
    new tactic code that doesn't have a direct counterpart in sprint
    084's body or sprint 085's pointwise theorem, you are probably
    overcomplicating; step back and consider Option α (uniform a.e.
    closer) which collapses the per-window closing chain to a single
    code path.

  * **No new files this sprint** (unless V66 is shipped). The new
    theorem and `KernelKind` inductive both live inside the existing
    `Proof/Reduction.lean`. No per-candidate `Candidates/V66/` files;
    if V66 is shipped, it imports V63's three derived-theorem files
    plus V64's `TauWindowEndpoints.lean` (same as V65).

  * **V66 specialization** (if shipped). The kind function for the
    two-window m=2 case is
    `kind := fun i => if i.val = 0 then KernelKind.modeJ 2 else KernelKind.modeJ 1`
    (or `Fin.cases (KernelKind.modeJ 2) (fun _ => KernelKind.modeJ 1)`,
    or any equivalent encoding). V66's `h_witness` re-supplies V64/V65's
    data with the new kind function.

  * **Sprint 087 preview** (for context, not for action this sprint):
    sprint 087 will (a) write
    `Numerical_Library.export_mode_hybrid_boxes.py` re-running V38's
    box-export logic, (b) verify in `Scratch/sprint_087_v38_mass_sweep.{py,txt}`
    that total mass ≥ 1 at `c = 356401/1000000`, (c) register
    `[[oracles]] hMixedTotalMass_oracle_certified_at_356401` in
    `lemma.toml`, (d) write the matching Lean axiom statement in
    `Proof/Reduction.lean` or a new file. Sprint 088 ships V66 (or V67)
    at V38's `c` composing four mode windows + three fallback boxes
    via this sprint's mixed reducer.
