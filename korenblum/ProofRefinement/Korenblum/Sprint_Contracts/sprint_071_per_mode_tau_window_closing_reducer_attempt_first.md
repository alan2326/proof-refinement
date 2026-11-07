# Sprint 071: First per-mode τ-window closing reducer in `Proof/Reduction.lean`, consuming `KorenblumPaper.OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` (single mode `j*` fixed across `[start, stop]`) and integrating to a kernel `c² ≤ ∫_{start..stop} 2ρ / (term(c, ρ, j*) · paperLambda K c ρ) dρ` — attempt-first, with Phase 0 Scratch witness at a target `c > 7129/20000`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V55.lean` (current high-water mark; `c_value = 7129/20000 = 0.35645`, three per-candidate derived-theorem files shipped in registers paper-equation chain (V53/ThetaStep) → pure complex algebra (V54/LiftIdentity) → `tsum`-level series rearrangement (V55/LiftSeriesBridge))
**Target file**: NEW closing reducer in `Proof/Reduction.lean` PLUS `Candidates/V56.lean` exercising it (V55-tied or, if Phase 0 witness is positive, V56-c-pushed)
**Direction**: section2-proof + analytic-Lean derivation (closing reducer construction in `Reduction.lean`) + attempt-first c-push numerical witness in `Scratch/`

## Goal

Ship a NEW closing reducer in `Proof/Reduction.lean`, name suggested
`valid_of_perMode_tau_window_eq8_eq9`, with a roughly `valid_of_*`-shaped
signature taking a `Section2Assumptions a b K c` instance, a single τ-window
`[start, stop] ⊂ (c, 1)`, a fixed positive integer `mode = j*`, the
`τ`-membership hypotheses

```text
OneModeTail.tau (mode - 1) ≤ c² / stop²
c² / start² ≤ OneModeTail.tau mode
```

(asserting `j*` is the dominant mode on the entire window `[start, stop]`),
the standard summability hypotheses required by
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
(`hPlusDisk`, `hPlusSigma`, `hMinusDisk`, `hMinusSigmaC`, `hMinusWeight`,
`hMinusSigma`), the `eq4`-driven `sigmaPlus c ≤ sigmaMinus c` premise
(discharged from `paper.eq4_sigmaPlus_bound`), and the **mode-fixed scalar
kernel hypothesis**

```text
KERNEL_71(c, start, stop, j*) :
  c² ≤ ∫_{start..stop} 2 ρ /
        (OneModeKernel.term c ρ mode · WangOuter.paperLambda K c ρ) dρ.
```

The reducer concludes `ValidKorenblumBound c` by composing
`pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` with
`intervalIntegral.integral_mono_on` (or `setIntegral_mono`), the workspace's
existing annulus-slice machinery from `Proof.Reduction`, and the
`innerExcess`-to-`diskExcess` bridge already proven in sprints 042/043/044.

This is the **first per-mode closing reducer** in the workspace — every
existing reducer in `Reduction.lean` integrates the `(a, b)`-independent
`OneModeSupBridge.scalarIntegrand` (the supremum over all modes) or some
closed-form scalar simplification of it. The Bulletin priority block
(2026-05-04, lines 16–157) explicitly directs this construction, citing
`OneModePaperBridge.innerSeriesExcess_le_supKernel_mul_sigmaMinus` and
`pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` by name as
already-proved bridges that no current `Reduction.lean` reducer consumes.

The c-pushing potential of per-mode reducers comes from the strict
ordering `OneModeKernel.term c ρ j ≤ OneModeSup.supKernel c ρ` for every
`j` and the tight-on-only-one-`j*` saturation of `supKernel`: the
canonical `b_1 = 1` adversary saturates `supKernel` only at mode `j = 1`,
and on `[start, stop]` τ-windows where `c² / ρ² ∈ (tau (j*-1), tau j*)`
with `j* ≥ 2`, `OneModeKernel.term c ρ j* < OneModeSup.supKernel c ρ`
**strictly** — so `KERNEL_71` is strictly slacker than the eq15-equivalent
sup-kernel criterion on the corresponding window. **This is the analytic
basis for the c-push the Bulletin is asking for.** The witness for whether
`KERNEL_71` is actually slack enough at `c > 0.35635` is Phase 0
(see below).

The fixed quantitative target depends on Phase 0:

- **If Phase 0 witness shows `KERNEL_71` holds with positive margin at
  some single τ-window `[start, stop]` and mode `j* ≥ 2` at a chosen
  `c > 7129/20000`** → V56 ships at that `c` as a real c-push. The
  candidate-side discharge is the `valid_of_perMode_tau_window_eq8_eq9`
  reducer, NOT a new oracle. Optional: register a numerical-integration
  oracle in `lemma.toml:[[oracles]]` for the integral evaluation if the
  generator finds the integral too costly to discharge symbolically; the
  contract permits this inline (see "Optional oracle" below).
- **If Phase 0 witness shows `KERNEL_71` does not hold at any single
  τ-window with mode `j* ≥ 2` at any `c > 7129/20000`** → V56 ties V55
  (`c_value = 7129/20000`) and the structural advance is just the new
  `valid_of_perMode_tau_window_eq8_eq9` reducer in `Reduction.lean`,
  available for future sprints to compose with finer multi-window
  partitioning.

Either way, the new reducer ships. This sprint is **structurally novel**
(first per-mode reducer in `Reduction.lean`, register-distinct from
sprints 068/069/070 which all shipped per-candidate files), and is a
**genuine c-push attempt** (Phase 0 establishes whether per-mode is
quantitatively slack at `c > V52`).

## Why

The Bulletin's current priority block (2026-05-04 directive, lines 16–157)
is the strongest signal in the workspace right now:

> "Every closing reducer in `Proof/Reduction.lean` is 'single window,
> uniform-over-`(a, b)` scalar kernel': something of the form
> `f(c) ≤ ∫_{ρ₁..ρ₂} g(c, ρ) dρ` where the LHS does not see the
> coefficient sequence at all. That family bounds `innerExcess` *via
> a uniform envelope on the worst admissible adversary*. The single-mode
> E1 adversary `b_1 = 1` consistently lies on or near that envelope,
> which is why every sprint 065–068 kernel falsifies on it.
>
> There is a strictly stronger family of bounds that the trust surface
> already exposes but no reducer in `Reduction.lean` currently invokes:
> a **per-mode** disk-side bound of the shape
>
>     innerSeriesExcess(a, b, c) ≤ H(c, ρ) · sigmaMinus(a, b, ρ)
>
> where `H(c, ρ) = sup_{j ≥ 1} (j/(j+1)) · c^(2j+2) / ρ^(2j)`. Each
> coefficient mode pays its own per-`k` cost, and the sup is attained
> by a single mode `j*` on each `τ = c²/ρ²` window — which lets a
> proof split `(c, 1)` into a small number of windows where one
> fixed `j` is known to dominate, then bound each window by the
> closed-form `H_j(c, ρ) = (j/(j+1)) · c^(2j+2)/ρ^(2j)`."

Sprint 070's lift-series-bridge addressed the per-`k` algebraic
infrastructure on the lift-side; sprints 068/069 addressed paper-axiom
chains and pure complex algebra. None of them touched
`Proof/Reduction.lean`. The Bulletin priority is unambiguous: the
structural gap is in `Reduction.lean`, not in per-candidate files.

Why `pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` is the right
endpoint:

1. **It already does the per-mode work for us.** The endpoint takes a
   single τ-window `[start, stop]`, a fixed `mode ≥ 1`, the τ-membership
   hypotheses on the endpoints (`tau (mode-1) ≤ c²/stop²`, `c²/start² ≤
   tau mode`), and concludes
   ```text
   ∀ ρ ∈ [start, stop],
     ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ * innerExcess
       ≤ 2 ρ · circleGap ρ.
   ```
   The integrand on the LHS is exactly `2 ρ / (OneModeKernel.term c ρ
   mode · paperLambda K c ρ)` (per `ModeBridge.scalarIntegrand`'s
   definition). Integrating over `[start, stop]` and using
   `intervalIntegral.integral_mono_on` plus the existing
   `annulusSlice` definitions in `PaperAxioms`/`Proof` gives
   ```text
   (∫_{start..stop} ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ dρ)
     · innerExcess
       ≤ ∫_{start..stop} 2 ρ · circleGap ρ dρ.
   ```
   The RHS is a multiple of `annulusSlice circleGap start stop` (i.e.
   `annulusLeftExcess` or `annulusRightExcess` depending on the
   window's relation to `branchSplit c`), and the existing `valid_of_*`
   pattern closes via `Section2Assumptions.eq14_combined` or its
   single-branch siblings.

2. **It strictly tightens sprint 045's kernel.** Sprint 045's
   reducer `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9`
   integrates `OneModeSupBridge.scalarIntegrand`, which equals
   `2ρ / (supKernel c ρ · paperLambda K c ρ)`. On any τ-window where
   `mode = j* ≥ 2` is the dominating mode,
   `OneModeKernel.term c ρ j* = supKernel c ρ` (by
   `OneModeSup.supKernel_eq_term_of_tau_bounds` from
   `KorenblumPaper.OneModeSup`, used inside
   `supScalar_eq_modeScalar_of_tau_bounds`), so the per-mode and
   sup-kernel reducers agree pointwise on a τ-window. The c-pushing
   gain comes from the **multi-window partition**: if `[c, 1]` splits
   into `m` τ-windows each with its own dominant mode `j*_w`, the
   per-mode kernel is the **sum of per-window mode-fixed kernels**,
   each tighter than the global sup-kernel because the global sup
   takes the max over **all** modes, while each per-window mode-fixed
   kernel takes only the local dominant mode. This is what the
   Bulletin's "split `(c, 1)` into a small number of windows where one
   fixed `j` is known to dominate" sentence refers to.

3. **The single-window per-mode reducer is the structural prerequisite
   for the multi-window c-push.** This sprint targets ONE window only,
   establishing the per-mode reducer pattern. A successor sprint can
   chain `m` instances of `valid_of_perMode_tau_window_eq8_eq9` with
   `annulusSlice` additivity (already in `Proof.Reduction` from sprint
   041's work) to produce the full multi-window discharge. Bounded
   sprint scope: ONE window, ONE mode.

4. **Phase 0 establishes feasibility before any Lean is written.**
   Per the Bulletin honesty rules (lines 234–246, "Use `Scratch/` —
   it has been empty for 46 sprints"), the sprint includes a
   pre-Lean numerical witness checking whether `KERNEL_71` holds with
   positive margin at some `(c > 7129/20000, start, stop, j*)` triple.
   If positive: V56 is a real c-push. If negative: V56 ties V55,
   structural advance is the reducer.

5. **Generator capability matches.** AGENT_BRIEF.md lines 128–152
   explicitly names "termwise summability and `tsum`-level
   rearrangement arguments" and `intervalIntegral.integral_mono`
   chains as in-scope. The reducer's proof is a chain of
   `intervalIntegral.integral_mono_on` (the per-`ρ` pointwise
   bound from `pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
   integrates monotonically because the integrand is non-negative on
   `[start, stop]` — `scalarIntegrand` is `2ρ/(term · paperLambda) ≥ 0`
   for `ρ > c > 0`), followed by the existing `valid_of_eq14_combined`-
   style discharge in `Reduction.lean`. Estimated proof length:
   **150–300 lines** of Lean, comparable to sprint 014's
   `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` (~155 lines)
   and sprint 045's `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9`
   (~250 lines).

## Roadmap to `c > 0.3554`

> *(Bulletin Step 1 mandates this section.)*

1. **Which existing closing reducer is the cheapest path to `c > 0.3554`?**
   None. Every existing reducer integrates the `(a, b)`-independent
   sup-kernel `OneModeSupBridge.scalarIntegrand`, whose worst-case
   adversary (single-mode `b_1 = 1`) sits exactly on the kernel envelope
   for any `c ≥ 0.3554` — sprints 048/050/051/065/066/067 cumulative
   evidence. The cheapest path through Lean is to **introduce a per-mode
   reducer that pays per-`k` rather than uniformly**, so the worst
   single-mode adversary contributes only its own per-`k` term and the
   other modes pay strictly less.

2. **What is the numerical kernel?** The mode-fixed integrated kernel
   on a single τ-window, normalized to `c²`:
   ```text
   KERNEL_71(c, start, stop, j*) :
     c² ≤ ∫_{start..stop}
            (2 ρ * OneModeKernel.weight c j*) /
              (OneModeKernel.weight c j* + OneModeKernel.term c ρ j* · ...)
   ```
   *Honest disclosure*: the literal RHS form depends on the chosen
   `valid_of_eq14_combined` discharge route — the LHS `c²` may be
   replaced by `c⁴`, `1`, or another scalar, depending on which
   `Section2Assumptions.eq*` field the reducer normalizes through.
   The **algebraic content** is fixed: the integral of
   `ModeBridge.scalarIntegrand c j* (paperLambda K c) ρ` over
   `[start, stop]`, with the integrand asserting the per-mode kernel.
   Phase 0 below pins the literal form.

3. **Does the kernel hold with margin at some `c > 0.3554`?**
   **THIS IS PHASE 0**, see `## Concrete edits expected — Phase 0`.
   The sprint defers all Lean work until Phase 0 reports a positive
   margin. If Phase 0's sweep over `(c, start, stop, j*)` with
   `c ∈ {0.357, 0.36, 0.37, 0.40}` and `j* ∈ {2, 3, 4, 5}` reports
   `min margin > 0` at any quadruple, that quadruple becomes V56's
   target. Phase 0 also reports the **comparison against sprint 045's
   sup-kernel form at the same quadruple** — the per-mode form is
   **strictly slacker** if Phase 0 reports a positive per-mode margin
   where sprint 045's sup-kernel margin would be negative.

4. **What is the trust gap between the Scratch witness and a Lean proof?**
   - The integral `∫_{start..stop} 2 ρ / (term c ρ j* · paperLambda K c ρ)
     dρ` is a closed-form rational integral when `paperLambda K c` is
     replaced by its closed-form expression
     `2 / sqrt(1 - K(c, ρ)²)` (from `WangOuter.paperLambda`,
     `KorenblumPaper.OneModePaperBridge` line 67's definition). This
     is **NOT** closed-form rational — `sqrt` appears. **Two routes**:
     - **Route A (preferred)**: leave the integral symbolic and
       discharge via `intervalIntegral.integral_mono_on` against an
       upper-bounding closed-form rational integrand. Specifically,
       on `[start, stop] ⊂ (c, 1)`, `paperLambda K c ρ ≥ 2`
       (from `WangPaperSideConditions.paperLambda_pos` and the
       definition), so
       `2 ρ / (term · paperLambda) ≤ ρ / term`, and
       `∫ ρ / term c ρ j* dρ` IS a closed-form rational
       (`term c ρ j* = (j*/(j*+1)) · c^(2j*+2) / ρ^(2j*)`, so
       `ρ / term = (j*+1)/j* · ρ^(2j*+1) / c^(2j*+2)`, integrating
       to `(j*+1)/(j* · (2j*+2)) · (stop^(2j*+2) - start^(2j*+2)) /
       c^(2j*+2)`). Lean closes this by `polyrith` / `ring` /
       `intervalIntegral.integral_pow` plus the standard
       `paperLambda ≥ 2` lower bound.
     - **Route B (oracle, only if Route A's upper bound is too slack
       to push c)**: register a numerical-integration oracle in
       `lemma.toml:[[oracles]]` that certifies the integral's lower
       bound at the chosen `(c, start, stop, j*)`. The wrapper
       function name and the Lean-facing axiom must be specified in
       the oracle row inline; the agent brief permits this without a
       proposal as long as the contract names them.
   - Phase 0 reports both Route A's closed-form bound and Route B's
     numerical bound at each (c, start, stop, j*) quadruple, so the
     planner of sprint 071's outcome chooses Route A or Route B based
     on whether the closed-form Route A bound suffices for the c-push.
   - **Default Phase 0 expectation**: Route A's closed-form bound IS
     sufficient for a per-mode c-push, because Wang's published proof
     uses exactly the `paperLambda ≥ 2` bound to derive the headline
     `c = 0.36389…` constant; replacing the sup-kernel with the
     mode-fixed kernel on a τ-window is a **monotone tightening** that
     can only help.

5. **Decide between two routes per gap, for each non-closed-form cell.**
   See item 4 above. Phase 0 disambiguates.

6. **What does the c-pushing candidate look like?** Conditional on Phase 0:
   - **Outcome A (Phase 0 positive)**: V56 imports the new reducer and
     ships at `c_value = <Phase-0-witnessed-c>` (e.g. `36 / 100 = 0.36`,
     or `357/1000 = 0.357`, depending on Phase 0's largest witnessed c).
     Discharge: `valid_of_perMode_tau_window_eq8_eq9` instantiated at
     `(start, stop, j*)` from Phase 0, with the τ-membership hypotheses
     and summability hypotheses discharged inside V56 (the τ-membership
     ones are closed-form rational comparisons closed by `norm_num`;
     the summability ones are `Summable`-of-eventually-zero-sequence-
     style or `Summable.smul`-style standard Mathlib API). If Route B
     (numerical oracle) is needed, V56 declares an axiom matching the
     registered oracle's `bound_field` and `oracle_fn`.
   - **Outcome B (Phase 0 negative)**: V56 ties V55 with `c_value =
     7129/20000`, identical eq15-discharge envelope (same axiom
     `hEq15_oracle_certified_hp_35645`), but imports the new
     `valid_of_perMode_tau_window_eq8_eq9` reducer in a side lemma
     `v56_perMode_reducer_compiles_at_witness` to confirm
     non-vacuity / Lean-checkability.
   - **Outcome C (Phase A blocks)**: see § Outcome C below.

## Three candidate sprint shapes considered (per Planner ultrathink rule)

The Planner enumerated three structurally distinct sprint shapes before
choosing this one. Each with strongest objection:

1. **Per-`k` cross-coupling positivity from `|f| ≤ |g|` (brief's
   second named candidate).** Strongest objection: the boundary
   `|f| ≤ |g|` hypothesis is NOT exposed by `Section2Assumptions` as a
   field — `Section2Assumptions` exposes only the paper's downstream
   consequences (`eq2..eq14`), not the upstream Hardy-class boundary
   inequality. A Lean theorem of the form "given `Section2Assumptions
   a b K c`, ∀ k, ‖a k‖² ≥ ‖b k‖² with `n1Pred` characterization"
   requires either (a) bridging through the boundary hypothesis (Wang
   Lemma 2; large Mathlib gap on `MeasureTheory.Integral` /
   `MeasureTheory.PoissonKernel`) or (b) cleverly extracting it from
   `eq2..eq14`. Path (a) is genuinely a multi-thousand-line Mathlib
   gap (the boundary `L²` ↔ Bergman coefficient identity is not in
   Mathlib at the level needed). Path (b) is mathematically false: the
   `tsum`-level `eq4` does NOT entail per-`k` dominance. Demoted: this
   is either a proposal target (path (a)) or mathematically incorrect
   (path (b)).

2. **Wang Lemma 2's boundary `L²` expansion (brief's third named
   candidate).** Strongest objection: same as path (a) above.
   `MeasureTheory.IntegralOnCircle` Parseval-style identity for
   holomorphic boundary values exists in Mathlib only fragmentarily;
   building it requires Hardy space coefficient extraction, which is
   ~thousands of lines of Mathlib infrastructure. **This IS a
   proposal target by the four-condition guide** (large derivation
   cost, mathematically correct, unclear translation to c-push at
   sprint level — needs to compose with per-`k` cross-coupling to
   help). Demoted: do not file the proposal in this sprint per
   "Choose freely" instruction; reserve for future planner session
   if per-mode reducer route is exhausted.

3. **Per-mode τ-window closing reducer in `Proof/Reduction.lean`.**
   **Chosen.** Reasoning above. The Bulletin priority block names this
   route explicitly with concrete trust-surface citations
   (`pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` is
   already proved in `KorenblumPaper.OneModePaperBridge`). The proof
   is a `intervalIntegral.integral_mono_on` chain bounded at 150–300
   lines of Lean, well within Generator capability per AGENT_BRIEF.md
   lines 128–152. Phase 0 establishes whether per-mode actually
   pushes c numerically before any Lean is written, so the sprint is
   genuinely attempt-first. Trust footprint: zero new axioms (Route A),
   one new optional oracle (Route B), no proposal, no edit to
   `KorenblumPaper/`. Register-distinct from sprints 068/069/070 (this
   is the FIRST modification of `Proof/Reduction.lean` since sprint
   047, and the FIRST per-mode reducer ever). Sprint 070's three-
   register validation generalizes to a fourth: `Reduction.lean`
   per-mode integration.

## Concrete edits expected

### Phase 0 (PRE-LEAN; must run first; gates Phases A and B)

1. **NEW**: `Scratch/sprint_071_per_mode_kernel_witness.py`.

   Content: A Python/mpmath script that sweeps the four-tuple
   `(c, start, stop, j*)` over

   - `c ∈ {0.357, 0.358, 0.36, 0.37, 0.38, 0.40, 0.45}`
   - `j* ∈ {2, 3, 4, 5}`
   - For each `(c, j*)`, set `start = c · sqrt(1 / tau(j*))` (the
     left endpoint where `c²/start² = tau(j*)`, i.e. mode-`j*` is
     just-becoming-active) and `stop = c · sqrt(1 / tau(j* - 1))`
     (the right endpoint where `c²/stop² = tau(j*-1)`, i.e.
     mode-`j*` just-became-dominant). Per `KorenblumPaper.OneModeTail`
     line 14, `tau(j) = j(j+2)/(j+1)²`, so `tau(1) = 3/4`,
     `tau(2) = 8/9`, `tau(3) = 15/16`, etc.
   - Optionally also `start, stop ∈ {c·1.01, c·1.05, c·1.1, ...}`
     manually chosen to maximize the per-mode τ-window margin.

   For each quadruple, the script computes:
   - **LHS**: `c²`.
   - **RHS_routeA**: `∫_{start..stop} ρ / (term c ρ j*) dρ` (the
     `paperLambda ≥ 2` upper-bounding integrand integrated
     symbolically — a closed-form rational in `(c, start, stop, j*)`,
     verified by mpmath at `dps = 50`). This is the `paperLambda ≥ 2`
     **lower bound** on the actual integrated kernel.
   - **RHS_routeB**: `∫_{start..stop} 2 ρ / (term c ρ j* · paperLambda
     K(c, ρ) c ρ) dρ` (using the actual `paperLambda` definition and
     mpmath quad). This is the **actual** integrated kernel.
   - **RHS_supKernel_comparison**: `∫_{start..stop} 2 ρ /
     (supKernel c ρ · paperLambda c ρ) dρ` (sprint 045's kernel),
     reported as the **strict comparison**: per-mode RHS_routeB
     should be `≥` sup-kernel RHS, with strict inequality on
     τ-windows where `j* ≥ 2`.

   Output: a table with columns `(c, j*, start, stop, RHS_routeA -
   c², RHS_routeB - c², RHS_supKernel - c², per_mode_minus_supKernel)`.
   The sprint's go/no-go gate:

   - **Phase 0 GO**: at least one quadruple with `RHS_routeA - c² > 0`
     **AND** `c > 7129/20000`. This means Route A's closed-form bound
     suffices and a c-push is achievable in pure Lean.
   - **Phase 0 GO-with-oracle**: at least one quadruple with
     `RHS_routeB - c² > 0` **AND** `c > 7129/20000`, but Route A's
     `RHS_routeA - c² ≤ 0` at that quadruple. Means the closed-form
     bound is insufficient but the actual integral suffices; the
     reducer needs Route B's oracle.
   - **Phase 0 NO-GO**: every quadruple `RHS_routeB - c² ≤ 0` for all
     `c > 7129/20000`. Means single-window per-mode does not push c;
     V56 ties V55, structural advance is just the reducer.

2. **NEW**: `Scratch/sprint_071_per_mode_kernel_witness.txt`.

   Plain-text dump of the table from step 1, with go/no-go decision
   recorded at the top.

The Phase 0 numerical witness is the **first quantitative test in the
workspace of whether per-mode actually beats sup-kernel at c-push
margins** above V52. Phase 0 budget: ≤ 20 minutes runtime.

### Phase A (LEAN, conditional on Phase 0 GO or NO-GO; both proceed)

1. **MODIFIED**: `ProofRefinement/Korenblum/Proof/Reduction.lean`. Append
   the new closing reducer:

   ```lean
   /--
   Sprint 071, Phase A — first per-mode τ-window closing reducer in the
   workspace. Consumes `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
   (the per-mode pointwise bound on a `[start, stop]` τ-window),
   integrates it over the window via `intervalIntegral.integral_mono_on`,
   and closes via the standard `Section2Assumptions`/`annulusSlice`
   machinery to produce a `ValidKorenblumBound c`.
   -/
   theorem valid_of_perMode_tau_window_eq8_eq9
       (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1)
       (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
       (paper : Section2Assumptions a b K c)
       {start stop : ℝ}
       (hStart_lower : c < start)
       (hStart_le_stop : start ≤ stop)
       (hStop_upper : stop < 1)
       {mode : ℕ}
       (hMode : 1 ≤ mode)
       (hLower : OneModeTail.tau (mode - 1) ≤ c ^ 2 / stop ^ 2)
       (hUpper : c ^ 2 / start ^ 2 ≤ OneModeTail.tau mode)
       -- Summability hypotheses required by the per-mode endpoint:
       (hPlusDisk : Summable (fun n : ℕ =>
         OneModePaperBridge.plusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
       (hPlusSigma : Summable (fun n : ℕ =>
         OneModePaperBridge.plusSeq a b n * c ^ (2 * n)))
       (hMinusDisk : Summable (fun n : ℕ =>
         OneModePaperBridge.minusSeq a b n * c ^ (2 * n + 2) / (n + 1 : ℝ)))
       (hMinusSigmaC : Summable (fun n : ℕ =>
         OneModePaperBridge.minusSeq a b n * c ^ (2 * n)))
       (hMinusWeight : Summable (fun n : ℕ =>
         OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n))
       (hMinusSigma : ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
         Summable (fun n : ℕ =>
           OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n)))
       -- The mode-fixed scalar kernel hypothesis (KERNEL_71):
       (hKernel :
         c ^ 2 ≤ ∫ ρ in start..stop,
           ModeBridge.scalarIntegrand c mode (WangOuter.paperLambda K c) ρ) :
       ValidKorenblumBound c
   ```

   Proof outline (~150–300 lines):

   - **Step 1**: from `paper.eq3, paper.eq4`, deduce
     `OneModePaperBridge.sigmaPlus_le_sigmaMinus_of_eq4` to obtain
     `paper.sigmaPlus c ≤ paper.sigmaMinus c`.
   - **Step 2**: define `innerExcess := paper.diskExcess` (or extract
     it from the existing reducer pattern in
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`; the
     definition matches sprint 014's pattern).
   - **Step 3**: apply
     `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
     with the supplied summability and τ-membership hypotheses,
     producing
     ```text
     ∀ ρ ∈ [start, stop],
       ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ * innerExcess
         ≤ 2 ρ * (PaperAxioms.circleGap a b) ρ.
     ```
   - **Step 4**: integrate over `[start, stop]` via
     `intervalIntegral.integral_mono_on` (the integrand
     `ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ * innerExcess`
     is a continuous non-negative function on `[start, stop]`, since
     `ModeBridge.scalarIntegrand_eq` shows it's `2ρ/(term·paperLambda)
     ≥ 0`):
     ```text
     (∫ ρ in start..stop,
        ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ) · innerExcess
       ≤ ∫ ρ in start..stop, 2 ρ · (PaperAxioms.circleGap a b) ρ.
     ```
   - **Step 5**: by `hKernel` (KERNEL_71),
     ```text
     c² · innerExcess ≤
       ∫ ρ in start..stop, 2 ρ · (PaperAxioms.circleGap a b) ρ.
     ```
   - **Step 6**: identify `∫ ρ in start..stop, 2 ρ · circleGap ρ` as
     `2 · annulusSlice circleGap start stop` (via the existing
     `AnnulusIntegralReduction.annulusSlice` definition in
     `KorenblumPaper.PaperAxioms` line 254, but recall
     `annulusSlice f a b := ∫ ρ in a..b, 2 ρ * f ρ` per
     `Proof.Reduction` lines 200–250 area — confirm by inspection).
   - **Step 7**: close by composing with the existing
     `valid_of_eq14_combined`-shaped reducer in
     `Reduction.lean` (or its sub-component the
     `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`-shaped reducer
     that consumes `c² · innerExcess ≤ <annulusSlice·multiple>`). The
     existing reducers' `c²·innerExcess ≤ 2·annulusSlice` pattern
     matches Step 5's conclusion structurally.

   *Honest tactical disclosure*: The integrand
   `ModeBridge.scalarIntegrand c mode (paperLambda K c) ρ` is not
   obviously continuous on `[start, stop]` from Mathlib's standpoint
   without `paper.K_continuous` or similar. **The generator MUST
   inspect** whether `Section2Assumptions` provides a continuity
   hypothesis on `K`, or whether the `intervalIntegral` form in step
   4 needs `IntegrableOn` / `Continuous` hypotheses surfaced as
   theorem arguments. If continuity is needed and not in
   `Section2Assumptions`, surface it as an additional hypothesis
   (e.g. `hCont : Continuous (fun ρ => K c ρ)` or `hIntegrable :
   IntervalIntegrable (fun ρ => ModeBridge.scalarIntegrand c mode
   (WangOuter.paperLambda K c) ρ) MeasureSpace.volume start stop`).
   Mirror the pattern of sprint 014/045's existing reducers — they
   surface analogous integrability hypotheses for the
   `OneModeSupBridge.scalarIntegrand` form.

2. **NEW**: `ProofRefinement/Korenblum/Candidates/V56.lean`.

   Imports `ProofRefinement.Korenblum.Proof.Main` (which transitively
   pulls `Proof.Reduction`). Defines:

   - `c_value : ℝ`. **Phase 0 GO**: `c_value` is set to the largest
     `c` from Phase 0's GO table; e.g. `360 / 1000 = 0.36`. **Phase 0
     NO-GO**: `c_value = 7129 / 20000` (ties V55).
   - `c_value_pos`, `c_value_lt_one`: closed-form rational lemmas
     proved by `norm_num`.
   - **Phase 0 GO** path: a side lemma exercising
     `valid_of_perMode_tau_window_eq8_eq9` instantiated at
     `(start, stop, j*)` from Phase 0, with summability hypotheses
     discharged inline (the `plusSeq`/`minusSeq` summabilities for any
     fixed `(a, b)` instance follow from
     `WangPaperSideConditions.coeffSeq_summable` in
     `KorenblumPaper`, which is registered in
     `[workspace_import_policy]`-exact's transitive closure via the
     `OneModePaperBridge` re-export). The τ-membership hypotheses
     (`hLower, hUpper`) are closed-form rational comparisons closed
     by `norm_num` using `OneModeTail.tau`'s closed-form definition.
     The `hKernel` hypothesis is closed:
     - **Route A path**: by Lean (closed-form rational integral
       evaluation via `intervalIntegral.integral_pow` + `polyrith` /
       `nlinarith`).
     - **Route B path**: by an axiom matching a registered oracle
       (the oracle row added to `lemma.toml:[[oracles]]` in the
       same sprint).
   - `theorem korenblum_constant_search : ValidKorenblumBound c_value`
     proved via `valid_of_perMode_tau_window_eq8_eq9` (Phase 0 GO) or
     via `valid_of_eq15` discharged by
     `hEq15_oracle_certified_hp_35645` (Phase 0 NO-GO, identical to
     V55's discharge).

3. **`lemma.toml`**: edits depend on Phase 0 outcome:
   - **Phase 0 NO-GO** OR **Phase 0 GO Route A**: zero new axioms
     declared, zero new oracles registered. The
     `[import_policy].allowed_exact` is unchanged (no new candidate
     submodule).
   - **Phase 0 GO Route B**: register one new `[[oracles]]` row
     pinning `Numerical_Library.rigorous_scalar.<wrapper_function>`
     at the chosen `(c, start, stop, j*)`. The wrapper function
     name, the Lean-facing axiom name, and the oracle row are
     specified inline in this contract. (The wrapper function
     itself is implemented in
     `Numerical_Library/rigorous_scalar.py` as a sibling sprint
     edit; the per-mode integral is computed via mpmath quad with
     interval-arithmetic margin > strict-margin threshold.)

4. **`Bulletin.md`**: append one `## Recent events` row recording
   sprint 071's outcome and Phase 0's GO/NO-GO decision.

5. **`Experience.md`**: append one entry per the Bulletin honesty rules
   (lines 234–246, 281–298): what was attempted, dead ends if any
   (e.g. if Phase 0 went GO-with-oracle and then Route B's wrapper
   refused certification at the chosen quadruple, document that as a
   dead end on the way to the eventual c-push or NO-GO conclusion),
   current obstacle, next move (e.g. multi-window partition via
   sprint 072 if single window suffices marginally), trust-surface
   accounting.

### Phase B (no separate Phase B — Phase A is the structural advance, Phase 0 is the c-push gate)

This sprint deliberately has no Phase B. The structural advance is the
`valid_of_perMode_tau_window_eq8_eq9` reducer in `Reduction.lean`. The
c-push (Phase 0 GO) and the c-tie (Phase 0 NO-GO) are both Phase A
outcomes; no further phase is needed.

## Acceptance criteria

### Outcome A — Phase 0 GO + Phase A succeeds, V56 c-pushes

1. `Scratch/sprint_071_per_mode_kernel_witness.{py,txt}` exist and
   document at least one quadruple `(c, start, stop, j*)` with
   `RHS_routeA - c² > 0` (preferred) or `RHS_routeB - c² > 0` (fallback)
   AND `c > 7129/20000`.
2. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
   The new `valid_of_perMode_tau_window_eq8_eq9` theorem in
   `Reduction.lean` is a `theorem` (no `axiom`s, no `sorry`s).
3. `lake build ProofRefinement.Korenblum.Candidates.V56` succeeds.
4. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V56.lean` succeeds with
   `pass: true`.
5. The evaluator's `score` is **strictly greater than `7129/20000`**
   (Phase 0's GO `c` value as a rational).
6. The evaluator's `axioms_used` for V56 is `⊆ {seed} ∪ {oracle axioms
   referenced by V56}`. Specifically, **Route A: no new oracle, no new
   seed axiom**; **Route B: one new oracle row in
   `lemma.toml:[[oracles]]`** plus one new seed-axiom name in
   `lemma.toml:[seed_axioms].allowed`, both specified inline in this
   contract's edits.
7. The new reducer's axiom closure (verified by `#print axioms
   valid_of_perMode_tau_window_eq8_eq9` in a Scratch buffer if needed)
   is `⊆ {seed}`.

### Outcome B — Phase 0 NO-GO + Phase A succeeds, V56 ties V55

1. `Scratch/sprint_071_per_mode_kernel_witness.{py,txt}` exist and
   document the NO-GO conclusion (every probed quadruple has
   `RHS_routeB - c² ≤ 0` at every `c > 7129/20000`).
2. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
   The new `valid_of_perMode_tau_window_eq8_eq9` theorem ships in
   `Reduction.lean`.
3. `lake build ProofRefinement.Korenblum.Candidates.V56` succeeds.
4. Evaluator reports `pass: true`, `score = 7129/20000` (ties V55).
5. The new reducer's axiom closure is `⊆ {seed}`. V56's axiom envelope
   is byte-for-byte identical to V55's (`hEq15_oracle_certified_hp_35645`
   plus the seed axioms).
6. V56 contains a side lemma `v56_perMode_reducer_compiles_at_witness`
   that instantiates the new reducer at concrete `(start, stop, j*)`
   arguments (e.g. the largest-margin quadruple from Phase 0 even
   though it's negative-margin) to confirm the reducer is non-vacuous
   and Lean-checked.
7. `Experience.md` entry explicitly records the NO-GO conclusion as a
   dead end on the single-window per-mode route, naming the multi-
   window partition as the recommended next-sprint direction.

### Outcome C — Phase A blocks (the new reducer's proof cannot be completed)

If the generator cannot complete the `valid_of_perMode_tau_window_eq8_eq9`
proof in the time budget (e.g. the `intervalIntegral.integral_mono_on`
chain hits a measure-theory / continuity gap that requires surfacing
`Continuous K` or `IntervalIntegrable` hypotheses the contract did
not anticipate, or the existing `valid_of_eq14_combined` discharge
pattern doesn't compose cleanly with the per-mode integrand):

1. Write `Scratch/sprint_071_obstruction.md` documenting:
   - Which exact intermediate goal blocked the proof (e.g. "after
     `intervalIntegral.integral_mono_on`, the residual goal requires
     `IntervalIntegrable (fun ρ => ModeBridge.scalarIntegrand c mode
     (paperLambda K c) ρ) volume start stop`, but
     `Section2Assumptions` does not surface a `Continuous K`
     hypothesis, and `paperLambda K c ρ` is built from `K(c, ρ)` via a
     square root and a quotient — it requires `K`-continuity
     hypotheses").
   - The Lean tactic transcript at the blocking goal.
   - Whether the obstruction is missing-Mathlib-API (e.g. the
     specific `intervalIntegral.integral_mono_on` variant the
     workspace needs, naming the Mathlib module that should provide
     it), unfamiliar-tactic-chain (gap-in-attack), or a
     `Section2Assumptions` field gap (in which case file a
     `Proposals/proposal_004_*.md` in the next planner session, NOT
     in this sprint's session per the four-condition guide — sprint
     071 is the attempt; the proposal is the future planner's
     deliverable).
   - A closed-form algebraic identity confirming the obstruction is a
     **tactic-level / Mathlib-API-level** issue, NOT a mathematical
     issue. The reducer's mathematical content is correct: it's just
     `intervalIntegral.integral_mono_on` of the per-mode pointwise
     bound, no new mathematics is asserted.
   - A recommendation to the next planner: which Mathlib lemma family
     to try next, or which `Section2Assumptions` field to surface as
     an additional hypothesis to the reducer.

2. **Phase 0 still ships** (the Scratch witness is independently
   useful for any future per-mode work). Acceptance for Outcome C:

   1. `Scratch/sprint_071_per_mode_kernel_witness.{py,txt}` exist
      with a complete table.
   2. `Scratch/sprint_071_obstruction.md` exists with the Lean
      transcript and the recommendation.
   3. **No edits to `Reduction.lean`** (do not ship a
      `theorem ... := sorry`-style stub); leave the file unchanged.
   4. **No `Candidates/V56.lean` shipped.**
   5. No edits to `lemma.toml`, no edits to `KorenblumPaper/`, no
      edits to `Numerical_Library/`.
   6. Append a Bulletin row recording the BLOCK and a forward-looking
      Experience.md entry naming the next sprint's recommended
      attack.

3. **STATUS=BLOCKED** under Outcome C. Per the planner agent's
   four-condition guide, this is the kind of attempt-first BLOCK that
   makes a future proposal_004 filing legitimate IF (and only if) the
   obstruction note documents a genuine `Section2Assumptions` field
   gap (not a tactic-level issue). The obstruction note's "is this
   missing-Mathlib-API or `Section2Assumptions`-field gap" disambiguation
   is the gate on future proposal eligibility.

## Out of scope

- Edit older candidates (`V0..V55`) or older `KorenblumPaper/` modules.
- Change the final theorem statement (`korenblum_constant_search :
  ValidKorenblumBound c_value`).
- Multi-window partition of `[c, 1]` into `m > 1` τ-windows. Sprint 071
  is **single window, single mode**. The multi-window c-push, if
  needed, is sprint 072's deliverable. Single window is the structural
  prerequisite.
- Hoist `Candidates/V53/ThetaStep.lean`, `Candidates/V54/LiftIdentity.lean`,
  or `Candidates/V55/LiftSeriesBridge.lean` into shared `Proof/`
  modules. Hoisting is its own sprint contract per AGENT_BRIEF.md
  lines 192–195.
- File `Proposals/proposal_004_*.md`. Per the four-condition guide,
  proposal-filing is appropriate only after a sprint returns BLOCKED
  with a precise `Section2Assumptions`-field-gap obstruction note. If
  Outcome C ships a tactic-level obstruction note, the next planner
  CAN file a proposal IF the note disambiguates as a genuine field
  gap; otherwise no proposal.
- Add a free-floating new axiom (the only axiom V56 may declare on
  Phase 0 GO Route B is one matching a registered numerical-integration
  oracle in `lemma.toml:[[oracles]]`; this is permitted by the agent
  brief without a proposal).
- Edit `KorenblumPaper/` (the paper surface is read-only for the
  generator).
- Re-derive theorems already in `OneModePaperBridge.lean` (e.g.
  `pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` — consume
  it as-is via `import KorenblumPaper.OneModePaperBridge`).
- Push c past the literal Wang-(15) crossover via this single-window
  reducer alone. The single-window per-mode c-push has a Phase-0-
  determined ceiling; sprint 072 (multi-window) is the route to
  larger c.

## Time budget

- **Phase 0**: ≤ 20 minutes runtime. Pure mpmath sweep, ~50 lines of
  Python.
- **Phase A**: ≤ 120 minutes runtime. The reducer proof is a
  `intervalIntegral.integral_mono_on` chain on top of
  `pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` plus the
  existing `valid_of_eq14_combined`-shaped discharge. If 90 minutes
  pass without successful closure of the `intervalIntegral` step, the
  generator pivots to a different `intervalIntegral`-API family
  (e.g. `MeasureTheory.setIntegral_mono_on` instead of
  `intervalIntegral.integral_mono_on`) rather than continuing to chip
  away.

Total budget: ≤ 140 minutes runtime.

## Stop conditions

- Acceptance criteria for Outcome A or Outcome B met:
  `STATUS=READY_FOR_EVALUATION`
- Acceptance criteria for Outcome C met (Phase 0 ships, Phase A blocks
  with obstruction note, no `Reduction.lean` / V56 edits):
  `STATUS=BLOCKED`
- Generator cannot complete Phase 0's Scratch witness within 20
  minutes (mpmath / scipy / interval-arithmetic infrastructure
  unavailable, etc.): `STATUS=BLOCKED_NEEDS_HUMAN`
