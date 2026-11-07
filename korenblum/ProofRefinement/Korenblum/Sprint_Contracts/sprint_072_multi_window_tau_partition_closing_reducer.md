# Sprint 072: Multi-window τ-partition closing reducer chaining `m` instances of `valid_of_perMode_tau_window_eq8_eq9` via `annulusSlice` additivity and `innerExcess_le_of_window_bounds`, with Phase 0 numerical witness over the canonical τ-partition of `(c, 1)` — attempt-first c-push

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V56.lean` (current high-water mark; `c_value = 7129/20000 = 0.35645`; first per-mode τ-window closing reducer `valid_of_perMode_tau_window_eq8_eq9` shipped in `Proof/Reduction.lean` by sprint 071)
**Target file**: NEW closing reducer in `Proof/Reduction.lean` named `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`, plus `Candidates/V57.lean` exercising it (V56-tied if Phase 0 NO-GO; V57-c-pushed if Phase 0 reports total mass ≥ 1 at some `c > 7129/20000`)
**Direction**: section2-proof + analytic-Lean derivation (multi-window closing reducer construction) + attempt-first c-push numerical witness gated by Phase 0

## Goal

Ship a NEW closing reducer in `Proof/Reduction.lean`, name suggested
`valid_of_perMode_multiWindow_tau_partition_eq8_eq9`, that takes a
`Section2Assumptions a b K c` instance plus a finite indexed family
`(start_w, stop_w, j*_w) : Fin m → ℝ × ℝ × ℕ` of τ-windows covering a
sub-arc of `(c, 1)` (with `start_0 = c`, `stop_(m-1) = 1`, and
`stop_w = start_(w+1)` for adjacency), with τ-membership hypotheses
asserting that each window's dominant mode `j*_w` satisfies
`OneModeTail.tau (j*_w - 1) ≤ c²/stop_w²` and `c²/start_w² ≤ OneModeTail.tau j*_w`,
the standard summability hypotheses required by
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`,
and the **multi-window mass-1 kernel hypothesis**

```text
KERNEL_72(c, m, {(start_w, stop_w, j*_w)}_{w<m}) :
  1 ≤ Σ_{w=0}^{m-1} ∫_{start_w..stop_w}
        ModeBridge.scalarIntegrand c j*_w (WangOuter.paperLambda K c) ρ dρ.
```

The reducer concludes `ValidKorenblumBound c` by:

1. invoking sprint 071's
   `valid_of_perMode_tau_window_eq8_eq9`-style body **per window** to
   obtain `mass_w · innerExcess ≤ annulusSlice circleGap start_w stop_w`
   where `mass_w := ∫_{start_w..stop_w} ModeBridge.scalarIntegrand … dρ`;
2. summing those `m` window inequalities and using
   `AnnulusIntegralReduction.innerExcess_le_of_window_bounds`
   (already proved in `KorenblumPaper/AnnulusIntegralReduction.lean:155`)
   to conclude `innerExcess ≤ Σ_w annulusSlice circleGap start_w stop_w`;
3. chaining `annulusSlice_add_adjacent` over the `m`-window partition
   to fold the sum into `annulusSlice circleGap start_0 stop_(m-1) =
   annulusSlice circleGap c 1 = annulusExcess circleGap c`.

This is the **first multi-window closing reducer** in `Reduction.lean`
and the structurally promised successor to sprint 071. Sprint 071's
single-window reducer `valid_of_perMode_tau_window_eq8_eq9` is the
*per-window worker*; sprint 072's deliverable is the *multi-window
chainer* that consumes it `m` times.

The fixed quantitative target depends on Phase 0:

- **If Phase 0 witness shows `KERNEL_72` total mass ≥ 1 at some
  `c > 7129/20000` over a canonical τ-partition with `m ≤ 8` windows**
  → V57 ships at that `c` as a real c-push. The candidate-side discharge
  is the new multi-window reducer, NO new oracle (the integrals are
  rationals in `(c, ρ_endpoints)` discharged at the candidate level by
  `norm_num`/`polyrith`/`Polyrith`/exact-rational arithmetic, OR — if
  the integrals are too costly to discharge symbolically — by a single
  numerical-integration oracle entry registered inline in `lemma.toml`
  per the Bulletin's pre-approved channel; see "Optional oracle" below).
- **If Phase 0 witness shows `KERNEL_72` total mass < 1 at every
  tested `c ∈ {0.357, 0.358, …, 0.40}` over the canonical τ-partition
  with `m` up to 8 windows** → V57 ties V56 at `c = 7129/20000` via
  `valid_of_eq15` discharged by `hEq15_oracle_certified_hp_35645`; the
  structural advance is the new multi-window reducer in
  `Reduction.lean`, available for future sprints to compose with
  per-`k` cross-coupling bounds (proposal_003 territory) when the
  per-mode kernel family is replaced by a per-`k` family that does
  not divide by `paperLambda`.

Either way, the new reducer ships. This sprint is **structurally
novel** (first multi-window per-mode reducer in `Reduction.lean`,
register-distinct from sprint 071's single-window reducer), and is
a **genuine c-push attempt** (Phase 0 establishes whether the
multi-window total mass clears 1 anywhere above V56).

## Why

The Bulletin's current priority block (2026-05-04 directive) closes
with the structural directive to **build a closing reducer that pays
per-mode rather than uniformly**, then **split `(c, 1)` into a small
number of windows where one fixed `j` is known to dominate**. Sprint
071 shipped the per-window worker; sprint 072 ships the partition
chainer.

Sprint 071's Experience.md note (lines 2891–2918) explicitly
identifies this sprint as the natural successor and provides the
critical Phase 0 forecast: summing `j*=2,3,4,5` per-mode masses at
`c = 0.357` over the canonical τ-windows gives `0.00491 + 0.000475 +
0.000103 + 3.3e-5 ≈ 0.00552`, three orders of magnitude below the
`mass = 1` target. With the j=1 window included (`(c·2/√3, 1)` where
`τ ∈ [0, 3/4]` and mode-1 dominates), sprint 048's data on the
related `c⁴ ≤ ∫ 2ρ³/Λ` kernel suggests an additional `~0.005` to
`0.01` mass contribution, for a multi-window total of `~0.01–0.015`.
**Phase 0 is forecast NO-GO**, but the sprint contract designs Phase 0
to verify this explicitly across a wider c grid, verify the j=1 mass
inclusion not covered by sprint 071's data, and either falsify the
forecast (c-push lands) or confirm it (definitive numerical
exhaustion of the per-mode kernel family across `m`-window
partitions).

Even at PASS-tie, the structural advance has three concrete values:

1. **Institutional validation of `innerExcess_le_of_window_bounds`**
   over per-mode τ-windows. The Mathlib finite-bookkeeping lemma is
   already proved (`KorenblumPaper/AnnulusIntegralReduction.lean:155`)
   but no closing reducer in `Reduction.lean` currently consumes it.
   Sprint 072's reducer is the workspace's first consumer.

2. **A reusable `m`-window chainer** that future per-`k`
   cross-coupling sprints (proposal_003-derived, post-Lemma-2-ship)
   can compose with a non-Λ-dividing pointwise bound to discharge
   multi-window per-`k` integrals.

3. **Definitive Phase 0 evidence** that the per-mode kernel family
   (mode-fixed scalar integrand divided by `paperLambda`) does not
   admit a multi-window discharge above V56. This complements the
   sprint 048/050/065/066/067/068/071 cumulative exhaustion data
   for the closed-form `(a, b)`-independent kernel space, and
   strengthens the case for shifting the next non-tying sprint
   to a structurally novel register (Wang Lemma 2 boundary L²
   expansion → per-`k` cross-coupling axis).

The Lean derivation is bounded:

- The per-window body is sprint 071's
  `valid_of_perMode_tau_window_eq8_eq9` proof, copy-adapted to take
  `mass_w` (the per-window scalar integral) instead of the constant
  `1` mass; that is, drop `mass_w`'s name from the witness existential
  and lift it to a per-window scalar.
- The Finset bookkeeping is a direct application of
  `innerExcess_le_of_window_bounds` over `Finset.range m` with
  `mass i := mass_(i.val)` and
  `annulusTerm i := annulusSlice circleGap start_(i.val) stop_(i.val)`.
- The annulus-side fold-up is an `m`-fold application of
  `AnnulusIntegralReduction.annulusSlice_add_adjacent` (already
  consumed by sprints 023/041/045/046/047 and by sprint 071 itself).

Estimated proof length: **150–250 lines** of Lean, comparable to
sprint 071's reducer (~250 lines) since the per-window body is the
same and the Finset bookkeeping is `Finset.induction_on`-style with
the existing helper.

## Phase 0 — pre-Lean numerical witness (gates Phase A)

**Phase 0 deliverable**: `Scratch/sprint_072_multi_window_kernel_witness.{py,txt}`
mpmath script (dps=50, n_trunc=200) computing the multi-window total
mass

```text
total_mass(c, m) := Σ_{w=0}^{m-1} ∫_{start_w..stop_w}
                      2 ρ / (OneModeKernel.term c ρ j*_w · paperLambda K c ρ) dρ
```

over the **canonical τ-partition** of `(c, 1)`:

- Window 0 (mode `j*=1`): `[c·2/√3, 1]` (τ ∈ [c², 3/4]; mode-1 is
  dominant on the entire window since `tau 0 = 0 ≤ c² ≤ 3/4 = tau 1`).
- Window 1 (mode `j*=2`): `[c·3/(2√2), c·2/√3]` (τ ∈ [3/4, 8/9]).
- Window 2 (mode `j*=3`): `[c·4/(3√(15/16)·...), c·3/(2√2)]` —
  endpoint formulas: `start_w = c·(j*_w + 1)/√(j*_w · (j*_w + 2))`,
  `stop_w = c·j*_w/√((j*_w - 1)·(j*_w + 1))` for `j*_w ≥ 2`, derived
  from `tau j = 1 - 1/(j+1)²` and `c²/ρ² = tau j*_w` ⇒ `ρ = c/√(tau j*_w)`.
- Continue for `m ≤ 8` windows (covers `c²/ρ² ∈ [0, tau 8 = 80/81]`,
  i.e. `ρ ∈ [c·9/√80, 1]` for the last positive-mode window).

**Phase 0 sweep parameters**:

- `c ∈ {7129/20000, 0.357, 0.358, 0.36, 0.37, 0.38, 0.40, 0.45}` (mirrors
  sprint 071's grid, includes V56 seed and one point comfortably below
  the `(15)` crossover for sanity).
- `m ∈ {2, 3, 4, 5, 6, 7, 8}` (test progressively finer partitions).
- For each `(c, m)`, report `total_mass(c, m)` and the per-window
  contributions `mass_w` for `w ∈ {0, 1, …, m-1}`.
- Spot-check that on the canonical τ-window, `OneModeKernel.term c ρ j*_w
  = OneModeSup.supKernel c ρ` pointwise, so the per-window mass equals
  the integrated sup-kernel on the same window (sanity check; sprint
  071 verified this at single-window granularity).

**Phase 0 decision gate**:

- **Phase 0 GO**: there exists `(c, m)` with `c > 7129/20000` and
  `total_mass(c, m) ≥ 1 + ε` (ε = 1e-3 for a strict-margin cushion).
  Phase A proceeds with that `(c, m)` as the witness.
- **Phase 0 NO-GO**: for every tested `(c, m)`, `total_mass(c, m) < 1`.
  Phase A still runs (the multi-window reducer ships), but V57 ties V56.

## Phase A — Lean construction (always runs)

Regardless of Phase 0 outcome, the multi-window reducer
`valid_of_perMode_multiWindow_tau_partition_eq8_eq9` is shipped in
`Proof/Reduction.lean`. The reducer's signature uses the Finset-indexed
family form so it admits any `m ≥ 1` window count. Phase A proof
sketch:

1. Destructure the witness existential into `m, windows : Fin m → ℝ × ℝ × ℕ`,
   the adjacency hypothesis chain `start_0 = c`, `stop_(m-1) = 1`,
   `∀ w < m-1, stop_w = start_(w+1)`, the per-window τ-membership
   pair, and the per-window summability hypotheses.

2. **Per-window body** (factored as a private `have` named
   `hWindow_w`): for each `w ∈ Fin m`, replay sprint 071's
   `valid_of_perMode_tau_window_eq8_eq9` argument:
   - Discharge `paper.eq4_sigmaPlus_bound` at `r = 0` to get
     `sigmaPlus a b c ≤ sigmaMinus a b c` (one-time, factored out
     of the per-window loop).
   - Invoke
     `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
     on `Icc start_w stop_w` to get the pointwise bound
     `ModeBridge.scalarIntegrand c j*_w … ρ · diskExcess ≤ 2ρ · circleGap ρ`.
   - Apply `mass_mul_le_annulusSlice_of_integral_bound` with
     `mass = mass_w := ∫_{start_w..stop_w} ModeBridge.scalarIntegrand …`
     to get `mass_w · diskExcess ≤ annulusSlice circleGap start_w stop_w`.

3. **Finset bookkeeping**: package the per-window inequalities into
   `Finset.range m` and apply
   `AnnulusIntegralReduction.innerExcess_le_of_window_bounds` with
   `s = Finset.range m`,
   `mass i := mass_(i.val)`,
   `annulusTerm i := annulusSlice circleGap start_(i.val) stop_(i.val)`,
   `hTotal : 1 ≤ Σ_w mass_w` (the `KERNEL_72` hypothesis),
   `hAnnulusNonneg : 0 ≤ annulusTerm i` for each `w` (from
   `circleGap_nonneg_of_eq8_eq9` on `(c, 1)`).
   Conclusion: `diskExcess ≤ Σ_w annulusSlice circleGap start_w stop_w`.

4. **Annulus fold-up**: chain `annulusSlice_add_adjacent` `m-1` times
   over the adjacency hypothesis chain to collapse
   `Σ_w annulusSlice circleGap start_w stop_w =
    annulusSlice circleGap start_0 stop_(m-1) =
    annulusSlice circleGap c 1 =
    annulusExcess circleGap c`.

5. Final calc: `diskExcess ≤ annulusExcess`.

The proof body composes **sprint 071's per-window worker** and
**existing Mathlib/`KorenblumPaper` helpers** (`innerExcess_le_of_window_bounds`,
`annulusSlice_add_adjacent`, `circleGap_nonneg_of_eq8_eq9`); no new
helper lemmas are required.

## Concrete edits expected

- `Proof/Reduction.lean`: append `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`
  at the end (~150–250 lines). The reducer's signature uses
  `Fin m → ℝ × ℝ × ℕ` indexing for windows; per-window summability and
  τ-membership hypotheses are universally quantified over `w : Fin m`.
  The mass-1 kernel hypothesis is the single scalar
  `1 ≤ ∑ w, ∫_{start w..stop w} ModeBridge.scalarIntegrand c (mode w) (paperLambda K c) ρ dρ`.
- `Candidates/V57.lean`: ships the candidate. If Phase 0 GO, picks the
  witnessed `(c, m, windows)` and discharges
  `valid_of_perMode_multiWindow_tau_partition_eq8_eq9`. If Phase 0 NO-GO,
  ships at `c_value = 7129/20000 = 0.35645` (V56-tied) via `valid_of_eq15`
  discharged by `hEq15_oracle_certified_hp_35645`, with side lemma
  `v57_multi_window_reducer_compiles_at_witness` exercising the new
  reducer's signature against an arbitrary `Section2Assumptions` instance
  (statement-level non-vacuity check, mirrors sprint 071's
  `v56_perMode_reducer_compiles_at_witness`).
- `Candidates/V57/` (only if Phase 0 GO and a per-candidate derived
  helper is needed for the Phase A discharge — e.g. closed-form
  evaluation of a per-window integral): create per-candidate
  derived-theorem files under `Candidates/V57/` per
  `AGENT_BRIEF.md` lines 154–204. **Default: no per-candidate file
  is needed**; the witness existential pre-stages the integral
  values as scalar hypotheses discharged by `norm_num` /
  `polyrith` / direct rational arithmetic at the candidate level.
- `Scratch/sprint_072_multi_window_kernel_witness.{py,txt}`: Phase 0
  mpmath sweep over the canonical τ-partition.
- `lemma.toml`: at most a one-line `[import_policy].allowed_exact`
  extension for `Candidates/V57/<file>` if a per-candidate file is
  shipped (Phase 0 GO branch only). **No new axioms, no new oracles**
  unless Phase 0 GO and the integral is too costly to discharge
  symbolically (in which case register a numerical-integration oracle
  per the "Optional oracle" channel below — a pre-approved channel
  that does not require a new `Proposals/` filing per `AGENT_BRIEF.md`
  §"Numerical tooling").

### Optional oracle (Phase 0 GO branch only)

**This sub-section applies ONLY if Phase 0 reports a feasible witness
`(c, m, windows)` AND the per-window integrals
`∫_{start_w..stop_w} ModeBridge.scalarIntegrand c (mode w) (paperLambda K c) ρ dρ`
are not closed-form rationals discharged at the candidate level.**

If Phase 0 GO and at least one per-window integral is not
closed-form-discharged, register a numerical-integration oracle
inline:

- **Numerical_Library wrapper**: `rigorous_scalar.certify_modeIntegrand_integral_at_<c_value>_<m>_<window_index>`
  (or a parametric `certify_modeIntegrand_integral` if mpmath supports
  parametric arguments through the harness's evaluator schema).
- **`lemma.toml` `[[oracles]]` row**: maps each per-window axiom name
  to its mpmath wrapper.
- **Lean-facing axiom**: `axiom hModeIntegrand_oracle_<c_value>_<m>_<window_index>
  : <mpmath-asserted scalar inequality>`.
- **Pre-Lean Scratch verification**: `Scratch/sprint_072_oracle_preverify.{py,txt}`
  must report wrapper acceptance with margin ≥ 1e-3 at the chosen
  envelope (mpmath dps, n_trunc) BEFORE the Lean `axiom` is written
  (per Bulletin lines 99 + sprint 056's pattern).

**Default (Phase 0 NO-GO branch): no oracle registration. The
multi-window reducer ships with no new axiom, no new oracle, no
`lemma.toml` edit beyond `[import_policy]`.**

## Acceptance criteria

1. **Phase 0 script runs.** `Scratch/sprint_072_multi_window_kernel_witness.py`
   produces a `.txt` decision-block reporting `total_mass(c, m)` for
   each `(c, m)` in the sweep grid plus a final GO/NO-GO line. The
   script must spot-check that on each canonical τ-window,
   `OneModeKernel.term c ρ j*_w = supKernel c ρ` pointwise (sanity
   check verified to ≤ 1e-9 relative error at three sample
   `(c, ρ, j*)` triples).
2. **Lean build succeeds.** `lake build ProofRefinement.Korenblum.Candidates.V57`
   succeeds; `lake build ProofRefinement.Korenblum.Proof.Reduction`
   succeeds with the new reducer in place; the new reducer's body
   uses no `axiom` and no `sorry`.
3. **Evaluator passes.** `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V57.lean`
   reports `pass: true`. The score satisfies one of:
   - **Phase 0 GO**: `score > 7129/20000` (real c-push to the witnessed
     `c`), with `axioms_used ⊆ {seed} ∪ {hEq15_oracle_certified_hp_35645}`
     (if the candidate uses the existing oracle for an unrelated
     discharge step) ∪ `{any_new_oracle_registered_inline}` (Phase 0
     GO branch only). The new reducer produces the discharge directly,
     so `axioms_used` ⊆ `{seed}` is the typical Phase 0 GO case.
   - **Phase 0 NO-GO**: `score = 7129/20000` (V56-tied), with
     `axioms_used ⊆ {seed} ∪ {hEq15_oracle_certified_hp_35645}`
     (byte-for-byte identical to V56's envelope).
4. **Structural advance.** The new reducer
   `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` is the
   workspace's first multi-window per-mode closing reducer in
   `Reduction.lean`, and the workspace's first consumer of
   `AnnulusIntegralReduction.innerExcess_le_of_window_bounds` (the
   finite Finset-bookkeeping helper from
   `KorenblumPaper/AnnulusIntegralReduction.lean:155`).
5. **No new paper axioms or `KorenblumPaper/` edits.** The reducer's
   body cites only existing `Section2Assumptions` fields and
   existing `KorenblumPaper.*` lemmas already covered by
   `lemma.toml:[workspace_import_policy]`.
6. **No new `Proposals/`.** Phase 0 NO-GO is documented inline (in
   the Phase 0 `.txt` artefact and in `Experience.md` per the
   honesty rules); successor proposal-filing is the next planner's
   deliverable, not this sprint's.
7. **Phase 0 honesty.** The Phase 0 `.txt` artefact must explicitly
   tabulate per-window masses `mass_w` for each tested `(c, m)`,
   not just the total `total_mass(c, m)`. This forces the artefact
   to record which windows contribute most/least and whether
   adding finer windows monotonically increases the total (a
   sanity check on the τ-partition's correctness).

## Out of scope

- Edit older candidates (`Candidates/V0..V56.lean`, `Candidates/V53/*`,
  `Candidates/V54/*`, `Candidates/V55/*`).
- Change the final theorem statement (`korenblum_constant_search :
  ValidKorenblumBound c_value`).
- Edit `KorenblumPaper/*.lean` (read-only paper surface).
- Edit `Reduction.lean`'s existing reducers or definitions; only the
  *append* of the new reducer is in scope.
- Hoist V53/V54/V55 derived theorems into `Proof/`. (Hoisting is a
  separate sprint's deliverable; out of scope here per the brief's
  one-sprint-one-derivation-chain rule.)
- File `proposal_004` or any further `Proposals/` entry. Successor
  proposals are the next planner's deliverable.
- Construct a Λ-free per-mode bridge in `KorenblumPaper/`. Out of
  scope (the existing `pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
  bridge bakes in eq8+eq9, which introduces `paperLambda`; replacing
  this is a separate proposal-territory question).
- Ship Wang Lemma 2's L² boundary expansion as a per-candidate
  derived-theorem file. (This is the brief-named alternative
  direction; out of scope here, queueable as a successor sprint.)
- Add new `Section2Assumptions` fields, new free-floating axioms, or
  new seed axioms.

## Time budget

≤ 90 minutes runtime (Phase 0 mpmath sweep at dps=50, n_trunc=200,
`8 × 7 = 56` `(c, m)` data points with `m ≤ 8` per-window integrals
each is well under 30 minutes; Lean derivation 30–60 minutes; total
fits comfortably).

## Stop conditions

- **Phase 0 GO + Phase A succeeds + V57 c-pushes**: `STATUS=READY_FOR_EVALUATION`.
- **Phase 0 NO-GO + Phase A succeeds + V57 ties V56**: `STATUS=READY_FOR_EVALUATION`
  (per the contract's PASS-tie-with-structural-advance Outcome).
- **Phase A blocks on a Lean obstacle within scope** (e.g. the
  `Finset.range m`-induction bookkeeping doesn't typecheck cleanly
  against `innerExcess_le_of_window_bounds`'s signature, or the
  per-window summability hypotheses don't compose without
  duplication): `STATUS=BLOCKED` with a concrete
  `Scratch/sprint_072_obstruction.md` documenting the precise
  Lean signature mismatch and the next-sprint move.
- **Phase A requires a trust-base expansion** (Mathlib lemma not
  available, `KorenblumPaper/` edit needed, etc.): `STATUS=BLOCKED_NEEDS_HUMAN`
  with a concrete obstruction note (this is forecast extremely
  unlikely — the multi-window chainer composes only existing
  workspace machinery).

## Sign-correction acknowledgements (carried over from sprint 071)

Sprint 071's Experience.md flagged two contract-level sign issues in
sprint 071's planner output. This contract incorporates both
corrections from the start:

1. **KERNEL mass = 1, not c²**. The closing reducer's mass hypothesis
   is `1 ≤ Σ_w ∫ ModeBridge.scalarIntegrand`, matching
   `Eq15ScalarBound`'s `1 ≤ scalarCriterion` form, NOT `c² ≤ ∫`. The
   `mass_mul_le_annulusSlice_of_integral_bound` machinery in
   `KorenblumPaper/AnnulusIntegralReduction.lean` only closes to
   `diskExcess ≤ annulusSlice` when `mass = 1`; any other mass
   value fails to compose with the diskExcess-≤-annulusExcess
   target.

2. **Route A direction (sprint 071's Phase 0 mistake)**.
   `paperLambda ≥ 2` ⇒ `1/Λ ≤ 1/2` ⇒ `2ρ/(term·Λ) ≤ ρ/term`, so any
   "lower bound" derived from `paperLambda ≥ 2` is in fact an UPPER
   bound on the kernel integrand. Phase 0 in this sprint computes
   the actual KERNEL_72 RHS directly (Route B in sprint 071's
   parlance) and does not attempt a closed-form lower bound via
   Route A. The Phase 0 `.txt` artefact must NOT report a "Route A"
   column.
