# Sprint 080: First partition step toward V63 c-push — per-candidate Integrability.lean

**Created**: 2026-05-05 02:14 by Planner
**Parent candidate**: `Candidates/V62.lean`
**Target file**: `Candidates/V63.lean` + `Candidates/V63/Integrability.lean`
**Direction**: section2-proof (per-candidate analytic Lean derivation that
unblocks a future c-push)

## Goal

Ship the **first** of the three per-candidate derived-theorem files
identified by sprint 079's obstruction note as prerequisites for the V63
c-push at `c = 35646/100000`: **`Candidates/V63/Integrability.lean`**,
containing the two integrability hypotheses required by the
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's `h_witness`
predicate.

V63 itself ships as a **V62-tie** at `c_value = 35645/100000`.

The c-push to `c = 35646/100000` is deferred to a later sprint (V64+)
that will compose the three per-candidate files (this sprint's
Integrability.lean, plus a future Summability.lean and a future
DiskInnerSeriesBridge.lean) into the full `h_witness` construction.

This sprint targets the **structurally cleanest and smallest** of the
three required derived-theorem files (~300 Lean lines per the obstruction
note's estimate, against ~1200 for Summability and ~700 for the
DiskInnerSeriesBridge).

## Why

Sprint 079's obstruction note partitioned the V63 candidate-side
`h_witness` discharge into ~2000 lines of derived-theorem files spread
across three concerns:

1. **Summability** (~1200 lines, six summability hypotheses universally
   quantified over `(a, b)`),
2. **Integrability** (~300 lines, two `IntervalIntegrable` hypotheses on
   `circleGap a b` and `ModeBridge.scalarIntegrand`),
3. **DiskInnerSeriesBridge** (~700 lines, `diskExcess ≤ innerSeriesExcess`).

Per the user's directive ("If the full V63 c-push is too large for one
sprint, the partitioned approach is preferred over a deferred c-push")
and the AGENT_BRIEF's per-candidate-derived-theorem-file discipline,
sprint 080 ships **only** the Integrability file — the smallest of the
three concerns and the one with the cleanest existing template
(`KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`,
which is structurally identical to the j-mode case of the new file's
deliverables).

Two reasons to start with Integrability rather than Summability or the
DiskInnerSeriesBridge:

- **Lowest risk of structural surprise.** The obstruction note's
  ~80-line-per-shape estimate for `ModeBridge.scalarIntegrand`-shaped
  integrability mirrors the existing `paperScalarIntegrand{1,2}` proofs
  almost verbatim; the `2 * ρ * circleGap` integrability uses `eq8 +
  eq9` to reduce circleGap to a continuous function on `(c, 1)`. Both
  follow Mathlib measurability + bounded-by-constant patterns the
  workspace has previously used.
- **Smallest deliverable that strictly progresses the V63 work.** A V63
  PASS-tie that ships an Integrability file is a strict structural
  advance over V62: future c-push sprints can `import
  ProofRefinement.Korenblum.Candidates.V63.Integrability` (or whatever
  hoisted name), so the Integrability discharge is removed from the
  candidate-side `h_witness` budget and the next sprint can focus on
  Summability or the DiskInnerSeriesBridge in isolation.

The user's framing also sets the precedent: V63 is **not** required to
push c in this sprint — but it is required to ship an **independently
useful** derived-theorem file that materially reduces the residual
budget for the V64+ c-push.

## Concrete edits expected

- `Candidates/V63/Integrability.lean` (new file): contains three
  theorems in the `ProofRefinement.Korenblum.Candidates.V63.Integrability`
  namespace.

  1. `circleGap_two_rho_intervalIntegrable_on_unit`:

     ```
     theorem circleGap_two_rho_intervalIntegrable_on_unit
         {a b : ℕ → ℂ}
         {K : ℝ → ℝ → ℝ}
         {c : ℝ}
         (paper : PaperAxioms.Section2Assumptions a b K c)
         (hc_pos : 0 < c)
         (hc_lt_one : c < 1) :
       IntervalIntegrable
         (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
         volume c 1
     ```

     The proof should reduce `circleGap a b ρ` to a continuous function
     on `(c, 1)` via `paper.eq8_sigma_to_liftGap` +
     `paper.eq9_liftGap_to_circleGap` (which together express
     `circleGap = sigmaPlus(ρ) - sigmaMinus(ρ)` modulo the `liftGap`
     bridge), and then bound the integrand `2*ρ*circleGap` by a
     constant times the integrable boundary-norm series.

     The fallback construction, if the eq8/eq9 chain proves too large,
     is to consume an existing reducer's integrability output: sprint
     071's `valid_of_perMode_tau_window_eq8_eq9` already requires the
     same hypothesis on a sub-window; the same proof pattern (or a
     direct delegation) yields the full-window integrability.

  2. `modeScalarIntegrand_intervalIntegrable`:

     ```
     theorem modeScalarIntegrand_intervalIntegrable
         {K : ℝ → ℝ → ℝ}
         {c a b : ℝ}
         {j : ℕ}
         (hj : 1 ≤ j)
         (hc : 0 < c)
         (hab : a ≤ b)
         (hca : c ≤ a)
         (hb1 : b ≤ 1)
         (hPaperK : WangKernelExact.PaperKFormula K c) :
       IntervalIntegrable
         (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
         volume a b
     ```

     The proof models on
     `KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
     (j = 1 case) and `paperScalarIntegrand2_intervalIntegrable` (j = 2
     case), but at general `j ≥ 1`. Use
     `ModeBridge.scalarIntegrand_eq` (already in
     `KorenblumPaper.ModeBridge`) to rewrite the integrand as `((2 *
     (j+1)/j) * ρ^(2j+1)) / (c^(2j+2) * Λ ρ)`, then apply the same
     measurability + AE-bounded-by-constant pattern the existing
     `paperScalarIntegrand1/2` proofs use. The constant bound is
     `((2 * (j+1)/j) / c^(2j+2)) * 2` (the `2` factor coming from
     `1/Λ ≤ 2` via `paperLambda_ge_half`); concretely
     `2 * (j+1) / (j * c^(2j+2))` works for `ρ ≤ 1` since `ρ^(2j+1) ≤
     1`.

  3. (Optional consolidation theorem)
     `mode_two_and_one_scalarIntegrand_intervalIntegrable`:

     ```
     theorem mode_two_and_one_scalarIntegrand_intervalIntegrable
         {K : ℝ → ℝ → ℝ}
         {c ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ}
         (hc : 0 < c)
         (hcStart₁ : c ≤ ρStart₁)
         (hStart₁LeStop₁ : ρStart₁ ≤ ρStop₁)
         (hStart₂LeStop₂ : ρStart₂ ≤ ρStop₂)
         (hStop₂_le_one : ρStop₂ ≤ 1)
         (hStart₁_le_Start₂ : ρStart₁ ≤ ρStart₂)
         (hPaperK : WangKernelExact.PaperKFormula K c) :
       IntervalIntegrable
         (fun ρ => ModeBridge.scalarIntegrand c 2 (WangOuter.paperLambda K c) ρ)
         volume ρStart₁ ρStop₁ ∧
       IntervalIntegrable
         (fun ρ => ModeBridge.scalarIntegrand c 1 (WangOuter.paperLambda K c) ρ)
         volume ρStart₂ ρStop₂
     ```

     Two direct invocations of `modeScalarIntegrand_intervalIntegrable`
     at `j = 2` and `j = 1`. This packages the two integrability
     hypotheses required by the reducer's `h_witness` as a single
     consumable theorem at the exact (j₁, j₂) = (2, 1) shape sprint
     079's wrapper pins.

- `Candidates/V63.lean` (new file): a V62-tie at `c_value = 35645/100000`.

  Discharge of `korenblum_constant_search` is identical to V62 (via
  `valid_of_eq15` + `hEq15_oracle_certified_hp_35645`). The candidate's
  structural contribution is a side-lemma block that exercises the new
  `Candidates/V63/Integrability.lean` theorems on a representative
  (`a, b, K, c`) configuration to confirm Lean syntax acceptance and
  preserve the theorem statements for the V64+ composition sprint.

  At minimum, the side lemma should:
  - import `Candidates.V63.Integrability` (the new derived-theorem
    file),
  - re-state `circleGap_two_rho_intervalIntegrable_on_unit` and
    `mode_two_and_one_scalarIntegrand_intervalIntegrable` in V63's
    namespace,
  - discharge each by direct invocation,
  - assert non-vacuity (no `axiom` invocations beyond V62's V61-tie
    envelope).

- (No edits to `KorenblumPaper/`, `Proof/`, `Numerical_Library/`,
  `lemma.toml`, or any V0–V62 file.)

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V63.Integrability`
   succeeds.
2. `lake build ProofRefinement.Korenblum.Candidates.V63` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V63.lean` reports `status: PASS`
   with `score (maximize): 7129/20000` (V62-tie).
4. V63's `axioms_used` is byte-for-byte identical to V62's V61-tie
   envelope: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V63.hEq15_oracle_certified_hp_35645}`
   (with the Lean `Lean.ofReduceBool, Lean.trustCompiler` compiler
   axioms in the seed set as usual).
5. The new file `Candidates/V63/Integrability.lean` contains **only
   `theorem`s and `lemma`s** — no new `axiom` declarations, no `sorry`,
   no `Section2Assumptions` field extensions.
6. The two main theorems
   (`circleGap_two_rho_intervalIntegrable_on_unit` and
   `modeScalarIntegrand_intervalIntegrable`) compile against the
   workspace's existing `[workspace_import_policy]` allowlist (no new
   imports outside `KorenblumPaper.*`, `ProofRefinement.Korenblum.*`,
   `Mathlib.*`); if a Mathlib subpath is needed that the workspace
   hasn't yet imported, add the import to the new derived-theorem file
   only — do **not** edit `lemma.toml`.
7. `Bulletin.md` and `Experience.md` each gain one row documenting:
   - which integrability shapes were proved,
   - the line count of `Candidates/V63/Integrability.lean`,
   - which existing theorem was used as the proof template
     (`paperScalarIntegrand1_intervalIntegrable` and/or
     `paperScalarIntegrand2_intervalIntegrable` is expected),
   - the next-sprint forward direction (which of Summability or
     DiskInnerSeriesBridge to ship next).

## Out of scope

- **Do not** push `c_value` past `35645/100000` in this sprint. V63
  must tie V62 at the V61-tie envelope. Pushing c requires also
  shipping Summability + DiskInnerSeriesBridge + the candidate-side
  `h_witness` construction; that is a multi-sprint effort and this
  sprint is the first partition step.
- **Do not** edit `Proof/Reduction.lean`, `KorenblumPaper/`,
  `lemma.toml`, `Numerical_Library/`, or any V0–V62 candidate file.
- **Do not** ship a Summability.lean or DiskInnerSeriesBridge.lean
  derived-theorem file in this sprint, even if there is time.
  Single-concern per-sprint discipline keeps the partition recoverable
  if any sub-deliverable hits a structural snag.
- **Do not** file a `Proposals/` entry. The obstruction note's
  partition is the operative plan; proposal-filing is reserved for
  cases where an attempt sprint has explicitly returned BLOCKED on a
  named missing theorem and the four-condition gate of the planner
  brief is satisfied. None of those conditions is met here.
- **Do not** change the `ValidKorenblumBound` final theorem statement
  or the `c_value` def name.
- **Do not** introduce `Real.sqrt`-based endpoints in V63 itself.
  Endpoint choice (Route A in sprint 079's obstruction note) is part
  of the V64+ candidate-side `h_witness` construction, not part of
  this Integrability sprint. The integrability theorems in this
  sprint are stated for **arbitrary** `(a, b)` rationals or reals
  meeting `c ≤ a ≤ b ≤ 1`, so they accept either rational or
  `Real.sqrt`-based endpoints downstream.

## Stop conditions

- **Acceptance criteria 1–7 met**: `STATUS=READY_FOR_EVALUATION`.
  V63 ships as a V62-tie with the new Integrability.lean derived-
  theorem file shipped and Evaluator-PASS.
- **Acceptance criterion 1 (Integrability.lean compile) fails because
  the proof modelled on `paperScalarIntegrand1_intervalIntegrable` does
  not adapt cleanly to the `j ≥ 1` general case** (e.g., the constant
  bound `2 * (j+1) / (j * c^(2j+2))` doesn't fit Mathlib's `IntegrableOn.of_bound`
  shape for general `j`): document the obstruction at
  `Scratch/sprint_080_obstruction.md` with the exact failing tactic /
  goal state, ship V63 as a V62-tie **without** the Integrability.lean
  file, and `STATUS=BLOCKED`. The obstruction note must enumerate at
  least three alternative proof strategies that a future sprint could
  attempt (e.g., `IntervalIntegrable.continuousOn_mul`, direct AE-
  bound by `2*(j+1)/(j * c^(2j+2)) * 1`, or splitting the integrand
  shape).
- **Acceptance criterion 1 fails because
  `circleGap_two_rho_intervalIntegrable_on_unit` requires a Mathlib
  lemma family not currently imported by the workspace**: document
  the missing module at `Scratch/sprint_080_obstruction.md`, ship V63
  as a V62-tie with **only** the
  `modeScalarIntegrand_intervalIntegrable` and consolidation theorems
  (skipping the `circleGap` integrability), and
  `STATUS=READY_FOR_EVALUATION`. This is acceptable as a partial
  delivery because the future c-push will need the
  `circleGap_two_rho_intervalIntegrable_on_unit` theorem regardless —
  a partial delivery still strictly reduces the V64+ residual
  budget.
- **A new free-floating axiom or trust-base expansion would be
  required**: do not ship it. Document at
  `Scratch/sprint_080_obstruction.md` and `STATUS=BLOCKED_NEEDS_HUMAN`.

## Time budget

≤ 90 minutes runtime.

## Notes for the generator

- The obstruction note `Scratch/sprint_079_obstruction.md` contains
  the precise per-hypothesis Lean engineering breakdown; read it
  before starting.
- The Phase 0 numerical witness for the V64+ c-push is already shipped
  in `Scratch/sprint_079_endpoint_pinned_witness.txt` at margin
  +1.9001e-3; this sprint is **not** a Phase 0 sprint. No new
  `Scratch/` Python script is required (and none should be written —
  the deliverable here is purely Lean).
- The proof template
  `KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
  (lines 81–141 of `KorenblumPaper/WangPaperSideConditions.lean`) is
  the canonical reference. Read it carefully — its `IntegrableOn.of_bound`
  + AE-restricted-by-`measurableSet_Icc` pattern adapts directly to
  `ModeBridge.scalarIntegrand`'s `2ρ / (term · Λ)` shape via
  `ModeBridge.scalarIntegrand_eq`'s rewrite to `((2(j+1)/j) ρ^(2j+1))
  / (c^(2j+2) Λ)`.
- The `circleGap_two_rho_intervalIntegrable_on_unit` proof has two
  candidate strategies: (i) reduce `circleGap` to a continuous
  function via `eq8 + eq9` and apply
  `ContinuousOn.intervalIntegrable`; or (ii) use an existing reducer's
  integrability output (`Proof/Reduction.lean` line 908 uses
  `paperScalarIntegrand1_intervalIntegrable` in the same shape on
  sub-windows). Either is acceptable.
- If the generator produces a clean `Candidates/V63/Integrability.lean`
  in fewer than the obstruction note's ~300-line estimate, the leftover
  budget should **not** be spent on Summability or
  DiskInnerSeriesBridge — the per-sprint partition discipline is
  load-bearing for recovering from sub-deliverable surprises.
- V63's docstring should explicitly note that this is the **first
  partition step** toward V63's c-push and reference
  `Scratch/sprint_079_obstruction.md` for the multi-sprint plan.
