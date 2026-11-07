# Sprint 091: Phase 0 extended-architecture sweep for a c-ceiling above V67's `c = 89141/250000`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V67.lean` (V67 is the live ceiling at
`c = 89141/250000 = 356564/1000000`; no candidate ships this sprint).
**Target file**: no new `Candidates/V<N>.lean` this sprint. Concrete
artifacts:

  * `Scratch/sprint_091_extended_architecture_sweep.py` — high-precision
    Phase 0 numerical search extending sprint 089's adaptive sweep along
    three previously-untested architectural axes:
    (E1) `extra_mode_count ∈ {3, 4, 5, 6}` (mode index up to j ∈ {7, 8,
    9, 10}; sprint 089 capped at j ≤ 7);
    (E2) **non-canonical breakpoints**: split a canonical mode-`j`
    window `[c·sqrt((j+2)/(j+1)), c·sqrt((j+1)/j)]` into two sub-windows
    `[c·sqrt((j+2)/(j+1)), c·sqrt(τ̃)]` and `[c·sqrt(τ̃), c·sqrt((j+1)/j)]`
    at a non-canonical τ̃ ∈ (τ_{j-1}, τ_j) and use mode-`j` on the inner
    sub-window and mode-`j-1` on the outer (mode-`j-1` is a valid upper
    bound on the inner sub-window since `H_{j-1} ≤ H_j` holds whenever
    j-1 is below the canonical breakpoint, but the cross-saturation
    direction may still admit a sub-window where mode-`j-1` integrates
    slightly more than mode-`j`);
    (E3) **mixed Branch.one+per-mode at intermediate τ-bands**: replace
    a deep-band per-mode window `[c·sqrt((j+2)/(j+1)), c·sqrt((j+1)/j)]`
    with a hybrid pair (Branch.one inner sub-band + per-mode outer
    sub-band) at a fine-tuned breakpoint, on the speculation that
    Branch.one's `12ρ³(ρ²-c²)` factor is non-monotonic-in-the-right-
    direction relative to per-mode `2ρ/(H_j·Λ)` near the τ-breakpoint.
    Direction (E3) is expected to be NULL by the same "additive over
    sub-windows" argument that made sprint 089's direction (3) null,
    but is included so that the sprint's NO-GO outcome is *exhaustive*
    over the architectural surface, not just a partial scan.
  * `Scratch/sprint_091_extended_architecture_sweep.txt` — reproducibility
    log with full per-direction tables and a final `DECISION` line:
    **GO with `c_new`, `architecture_new`, and `margin_new ≥ 1e-4`**, or
    **NO-GO with explicit per-direction rationale and a quantified
    architectural-exhaustion claim**.
  * `Scratch/sprint_091_witness.txt` — if GO, a concise summary capturing
    the chosen c, the chosen architecture (window kinds, endpoints, mode
    indices), and the full-envelope margin at `(dps, n_trunc) = (80,
    300)`, suitable for sprint 092 to consume verbatim when authoring
    the next oracle wrapper.

**Direction**: oracle-support (Phase 0 numerical witness; no Lean
changes).

## Goal

Run a Phase 0 numerical sweep that extends sprint 089's adaptive
architecture exploration along three axes sprint 089 did NOT cover:

  1. **Mode index extended to j = 10** (sprint 089 capped at j = 7 via
     `extra_mode_count ≤ 3`). Test whether `extra_mode_count ∈ {4, 5,
     6}` (modes 8, 9, 10 added on top of 7) yields incremental margin
     uplift at V67's c, and whether the recovered margin permits a
     strict c-push above `89141/250000`.

  2. **Non-canonical sub-window splits** within a canonical mode-`j`
     band, with one sub-window using mode-`j+1` (the next-lower
     dominant index, valid as an upper bound only on the inner
     sub-window where `c²/ρ² ≤ τ_j`). The sub-window split point is
     swept over `τ̃ ∈ {τ_{j-1} + 0.1·(τ_j - τ_{j-1}), τ_{j-1} +
     0.5·(τ_j - τ_{j-1}), τ_{j-1} + 0.9·(τ_j - τ_{j-1})}`. By
     additivity-over-sub-windows this *should* be null, but the test
     confirms that mode-`j` is genuinely optimal everywhere on its
     canonical band rather than only on average.

  3. **Mixed Branch.one+per-mode at intermediate τ-bands** within the
     deep band `[c·(1+ε), c·sqrt(64/63)]`. Currently V67 uses a single
     Branch.one residual box on this band. The sweep tests whether
     splitting the box at intermediate ρ̃ ∈ {`c·sqrt(81/80)`,
     `c·sqrt(100/99)`, `c·sqrt(121/120)`}, with the inner sub-band
     using Branch.one and the outer using mode-8/9/10, recovers
     additional mass beyond what direction (1) gives.

The outcome is a single `DECISION` line:

  * **`Phase 0 GO`** if a `c_new > 89141/250000` is found with
    full-envelope margin `≥ 1e-4` under some architecture variant.
    Sprint 092 then writes the matching `Numerical_Library` wrapper,
    registers the `[[oracles]]` row, and ships V68 at `c_new`.

  * **`Phase 0 NO-GO`** if no `c > 89141/250000` admits margin `≥ 1e-4`
    under any tested architecture, including with `extra_mode_count`
    pushed to 6. The sprint records the largest margin achieved at each
    c above 356564 under the best architecture, **plus** a
    quantitative case-closing claim that the
    sprint 089 + sprint 091 union of architectural directions is
    exhaustive over the seven-window-and-its-extensions design surface,
    so future c-push attempts must come from a structurally different
    direction (per-k oracles, a strictly tighter coefficient-side
    bound, etc., not pure architecture).

This sprint **introduces no Lean changes**, **no `Numerical_Library`
wrappers**, **no `lemma.toml` rows**, **no `Proposals/` entries**, and
**no candidate files**. It is a pure numerical exploration sprint, in
keeping with the Bulletin's `Scratch/`-first guidance.

## Why

### Why this is the right next sprint, despite sprint 089 already running

Sprint 090 just shipped V67 at the c-ceiling sprint 089 located:
`c = 89141/250000 = 356564/1000000`, full-envelope margin +1.183e-4.
Sprint 089's `forward direction` for sprint 091 said: "the
seven-window architecture's c-ceiling is exhausted ... the next move is
per-k oracles, per-k cross-coupling, or a tightened H(c, ρ) envelope".
That directive is correct but **not yet supported by an exhaustive
architectural sweep**: sprint 089 capped `extra_mode_count` at 3 (mode
indices up to j = 7), did not test non-canonical sub-window splits,
and did not test mixed-kernel hybrids at intermediate τ-bands. The
user's prompt to this planner explicitly suggests:

> "Adaptive box-count/architecture sweep — sprint 089 explored 8
> windows; could 9, 10, 11 windows extract more headroom at higher c?"

Per the project's incremental discipline (`Bulletin.md` 2026-05-02
"Use `Scratch/` ... Lean is the certification layer, not the
exploration layer"), the cheapest way to either (a) ship a c-push
sprint at V68, or (b) authoritatively retire the architecture surface
as exhausted is to run the extended sweep. **Either outcome
materially helps the next planner**: GO unlocks a +2 to +5e-6 c-push at
modest cost; NO-GO with the union-exhaustive claim makes pivoting to
structural-advance directions (Wang Lemma 2 / Fourier orthogonality
in `Candidates/V67/` derived theorems, hoisting derived theorems to
`Proof/`, or other `Section2Assumptions`-only chains) the obvious next
step rather than a speculative pivot.

### Quantitative expectation per direction

  * **Direction (E1) extra_mode_count ∈ {4, 5, 6}**: per the geometric
    decline observed in sprint 089's k=1, 2, 3 sweep (mode5 mass at V66's
    c = 3.28e-5; mode6 = 1.30e-5; mode7 = 5.96e-6, factor ~0.4 per added
    mode), expected additional mass per mode beyond j=7:
    - mode8: ~2.4e-6 of mass (vs 4.09e-7 for the residual Branch.one box
      it would replace, a net gain of ~2e-6 of mass).
    - mode9: ~1.0e-6 of mass.
    - mode10: ~0.4e-6 of mass.
    - Cumulative gain at k=6 (modes 5-10 added): ~+3-5e-6 of mass over
      V67's architecture.

    Per sprint 089's c-derivative ~2.3e-5 of margin per +1e-6 of c, this
    +3-5e-6 of mass uplift translates to ~+0.13-0.22 micro-units of c.
    **At face value insufficient for a +1e-6 c-push, but margin from
    direction (E1) compounded with the non-vanishing Branch.one residual
    contribution at smaller residual boxes may admit a +1e-7 push that
    rounds to a strict-rational c above V67.**

  * **Direction (E2) non-canonical sub-window splits**: by additivity
    over sub-windows the integration over a canonical mode-`j` window
    is invariant to splitting if the same envelope is used on both
    sub-windows. The test is whether using mode-`j+1` on the inner
    sub-window (where `c²/ρ² ≤ τ_j`, so mode-`j+1` is valid as an upper
    bound, but is strictly tighter than mode-`j` ONLY on the inner
    sub-window where `c²/ρ² ≤ τ_j`) recovers any mass. Expected null
    by the same "the supremum is the optimal envelope" argument that
    governs sprint 089. The test is included as a **methodological
    verification** that the mode-`j` choice is genuinely point-wise
    optimal everywhere on its canonical band, not just on average.

  * **Direction (E3) mixed Branch.one+per-mode at intermediate
    τ-bands**: by additivity, this should also be null whenever the
    same envelope is used on a sub-band. The test is whether the
    Branch.one envelope (`12ρ³(ρ²-c²)/(c⁶·Λ)`) at the deep
    sub-sub-band `[c·(1+ε), c·sqrt(81/80)]` recovers more mass than
    the alternative mode-8 envelope on the same sub-sub-band. The
    Branch.one envelope vanishes at `ρ = c` while mode-8's
    `H_8 ≈ (8/9)c²` is finite at `ρ = c`, so mode-8 should win on
    the inner deep band — but mode-8 is only valid on `c²/ρ² ≤ τ_8 =
    80/81`, i.e., `ρ ≥ c·sqrt(81/80)`. So the strict comparison is
    whether splitting the residual box at `ρ̃ = c·sqrt(81/80)` and
    using Branch.one on `[c·(1+ε), c·sqrt(81/80)]` plus mode-8 on
    `[c·sqrt(81/80), c·sqrt(64/63)]` (which is direction E1 at k=4)
    versus using only Branch.one on the whole `[c·(1+ε),
    c·sqrt(64/63)]` (V67's choice) is faster. **Direction E3
    collapses into direction E1 at k=4 by this analysis**, but is
    listed separately so the sweep code's contiguous-additivity is
    sanity-checked once more, mirroring sprint 089's direction (3).

The expected combined outcome:

  * **Realistic range**: c-ceiling moves from 356564/1000000 to
    `[356564/1000000, 356571/1000000]` under the relaxed architecture.
    A push of `+1e-6` to `+7e-6` is plausible but not guaranteed; a
    push of `+10e-6` or more is unlikely per the geometric decline.
  * **Floor outcome**: c-ceiling stays at 356564/1000000. The sweep
    code's careful per-direction tabulation gives the next planner a
    quantitative floor on the architecture surface's headroom.

### Three (and more) distinct candidate sprint shapes considered

1. **This sprint (Phase 0 sweep at extended architecture, Scratch only)
   — chosen.** Pure numerical exploration; falsifiable; bounded in cost
   to a single generator session; either GO outcome (next planner ships
   V68 at c_new) or NO-GO outcome (next planner pivots to structural
   advance) is materially useful. **Strongest objection**: sprint 089
   already ran a sweep, and its forward-direction note suggested
   per-k / variable-α / tightened-envelope as the next move, not
   another sweep. **Counter**: sprint 089 *capped* at `extra_mode_count
   = 3` for purely structural (code-shape) reasons, not because k=4+
   was tested and rejected; the cap itself is the gap. Per the user's
   prompt explicitly listing 9, 10, 11 windows as a plausible
   direction, this is the right next sprint.

2. **Lean sprint to ship a 9-window candidate (V68) at c-ceiling = V67
   + δ for the smallest viable δ.** **Strongest objection**: a Lean
   sprint without a Phase 0 GO witness is the failure mode the
   Bulletin's `Scratch/`-first directive specifically prohibits. We do
   not yet know whether 9 windows admit ANY c above V67 with margin
   ≥ 1e-4. Writing Lean for an architecture that fails numerically is
   strictly worse than running the sweep first. **Demoted.**

3. **Trust-surface compaction**: derive `hH2_v67` and `hCircleGapInt_v67`
   from `Section2Assumptions`. **Strongest objection**: these are
   genuinely additional assumptions (`Summable (‖a n‖²)` and
   `IntervalIntegrable (2ρ·circleGap a b ρ)` on `(c, 1)`) that
   `Section2Assumptions` does not currently expose. Migrating them
   would require either (a) extending `Section2Assumptions` (a
   `Proposals/` action — forbidden by the directive prompt this
   sprint) or (b) deriving them from the existing fields of
   `Section2Assumptions` (impossible: the fields are pointwise
   inequalities, not summability/integrability statements). **Demoted
   as not actionable in this sprint.**

4. **Hoist V53/V54/V57/V58/V63/V67 derived theorems into `Proof/`**.
   **Strongest objection**: pure refactoring; does not move the
   score. Per the planner brief, "Score-push direction is preferred
   if any has a plausible path"; until direction 1's outcome is
   known, this is premature cleanup. **Demoted.**

5. **Wang Lemma 2 / Fourier orthogonality as a paper-axiom-free
   derived-theorem file.** **Strongest objection**: Wang Lemma 2's
   content (boundary `L²` expansion: `‖f‖²_{|z|=ρ} = Σ |a_n|² ρ^(2n)`)
   is **already absorbed** in `sigmaMinus`'s definition in
   `Section2Assumptions`. Re-deriving it as a Lean theorem would be a
   structural exercise whose result does not unblock a c-push (the
   workspace already uses `sigmaMinus` everywhere it would have used
   the Lemma 2 expansion). **Demoted as not advancing the score
   axis.**

6. **Variable-α cross-coupling Lean derivation** (sprint 077-style
   mathematical chain, but in Lean). **Strongest objection**: sprint
   077's Phase 0 sweep found NO contraction-regime witness above
   V52's `c = 7129/20000`. The mathematical content known to be
   numerically true at `c > V52` is in the non-contraction regime
   only, where the sign-flipping factor `(1 − α(k)²) < 0` makes the
   per-k integrated identity NOT lift to `annulusExcess(c) ≥
   diskExcess(c)`. Per sprint 077's honesty notes, this is "NOT
   automatic, and the structurally trivial nature of the sign flip is
   a strong red flag". Re-attempting in Lean without first re-running
   Phase 0 at a finer α-grid would be wasted work. **Demoted; if
   sprint 091 returns NO-GO, sprint 092 may queue a Phase 0 re-sweep
   at a finer variable-α grid as a sibling exploration.**

Direction 1 wins on **expected c-push per generator-session-budget**:
it lands a definitive answer (GO with concrete witness or NO-GO with
quantitative architectural-exhaustion claim) using ~1 hour of compute
and ~150 lines of Python, with the sprint 089 sweep code as a direct
template (~770 lines, ~75% reuse).

### Why Scratch-only is the right shape now

Per Bulletin priority:

> "Lean is the certification layer, not the exploration layer."

Sprint 089's success was a Scratch-only sprint that gated sprint 090's
Lean ship. Sprint 091 mirrors that pattern: explore the architecture
surface in Python before asking Lean to certify a candidate. The
~6-minute runtime at scan-envelope `(dps=40, n_trunc=120)` plus
~2-minute full-envelope re-verification at `(dps=80, n_trunc=300)`
is the same envelope sprint 089 used. Total wall-clock budget: ~30
minutes inside one generator session.

## Concrete edits expected

### 1. `Scratch/sprint_091_extended_architecture_sweep.py` (new file)

Templated on `Scratch/sprint_089_adaptive_seven_window_mass_sweep.py`
(~770 lines). Reuses `paper_factor`, `paper_lambda`,
`k_squared_at_rho`, `term_j`, `mode_window_mass`, `branch1_integrand`,
`branch1_window_mass`, `tau_j`, `fraction_to_mpf` helpers verbatim.

Extended logic:

  * `arch_endpoints(c, rho_top, delta_lo, extra_mode_count, splits)`:
    extend the existing helper to support `extra_mode_count ∈ {0, 1,
    …, 6}` (sprint 089 supported {0, 1, 2, 3}). Specifically:
    - `extra_mode_count = 4`: mode8 + mode7 + mode6 + mode5 added; the
      Branch.one residual box becomes `[c·(1+δ), c·sqrt(81/80)]` with
      mode8 immediately above on `[c·sqrt(81/80), c·sqrt(64/63)]`.
    - `extra_mode_count = 5`: mode9 added; residual box becomes
      `[c·(1+δ), c·sqrt(100/99)]` with mode9 on `[c·sqrt(100/99),
      c·sqrt(81/80)]`.
    - `extra_mode_count = 6`: mode10 added; residual box becomes
      `[c·(1+δ), c·sqrt(121/120)]` with mode10 on `[c·sqrt(121/120),
      c·sqrt(100/99)]`.
    - The τ-breakpoints are `τ_j = j(j+2)/(j+1)² = 1 - 1/(j+1)²`, so
      `c²/ρ² = τ_j` means `ρ = c·sqrt(1/τ_j) = c·sqrt((j+1)²/(j(j+2)))`.
      For j=8: `ρ = c·sqrt(81/80)`. For j=9: `c·sqrt(100/99)`. For
      j=10: `c·sqrt(121/120)`.

  * `direction_E1_sweep_at_v67_c(c)`: compute joint mass at V67's c
    for `extra_mode_count ∈ {3, 4, 5, 6}` with `(rho_top, delta_lo) =
    (1 - 10⁻⁹, 10⁻⁹)`. Tabulate per-window masses, total, margin, and
    Δ vs `extra_mode_count = 3`. Per the sprint 089 forward analysis,
    expected: k=4 adds ~+2e-6 mass; k=5 adds ~+1e-6; k=6 adds
    ~+0.4e-6.

  * `direction_E2_sweep(j_fixed, c)`: for j ∈ {2, 3, 4} (a few
    canonical mode bands), test sub-window splits at three τ̃ points
    interior to the canonical band. For each split, compute the
    integrated mass with mode-`j` on the inner sub-window and
    mode-`j-1` on the outer (NOTE: mode-`j-1` is NOT a valid upper
    bound on the outer sub-window where `c²/ρ² ≥ τ_{j-1}`; the test
    is whether the mass *as if* it were valid is larger than mode-`j`
    on the same sub-window — a methodological probe of whether the
    canonical breakpoint chooses optimally). Tabulate the gain or
    deficit per τ̃ choice. Expected: deficit at every split (sup
    over j is point-wise optimal).

  * `direction_E3_sweep(c)`: for each of ρ̃ ∈ {`c·sqrt(81/80)`,
    `c·sqrt(100/99)`, `c·sqrt(121/120)`}, compute the joint mass with
    Branch.one on `[c·(1+10⁻⁹), ρ̃]` and the corresponding mode-`j`
    on `[ρ̃, c·sqrt(64/63)]` (per the τ-breakpoint that contains ρ̃).
    Compare to V67's architecture (single Branch.one box on the whole
    deep band). **This is direction E1 at k=4 reframed**; included
    as a methodological cross-check (the two directions should give
    identical totals when the sub-architectures coincide, modulo
    floating-point noise). If a discrepancy > 1e-30 is observed, flag
    it as a sweep-code bug.

  * `combine_best_architecture_at_v67_c()`: identify the single
    architecture variant with the highest joint mass at V67's c.
    Re-verify at full envelope `(dps=80, n_trunc=300)`. Record the
    margin uplift relative to V67's `+1.183e-4`.

  * `c_sweep_at_best_architecture(c_min, c_max, c_step)`: sweep
    `c ∈ [89141/250000, c_max]` in `1e-6` steps under the best
    architecture (from above). For each c, compute joint mass and
    margin. Locate the largest c with margin ≥ 1e-4 at scan envelope
    `(dps=40, n_trunc=120)`. Re-verify the candidate c at full
    envelope `(dps=80, n_trunc=300)`. If the full-envelope margin
    remains ≥ 1e-4, declare GO; otherwise declare NO-GO and report
    the exact margin shortfall.

  * `decision_block()`: print the final `DECISION` line plus the
    chosen architecture summary. If GO, append `Scratch/sprint_091_witness.txt`
    with the architecture summary. If NO-GO, append a one-paragraph
    architectural-exhaustion claim citing the per-direction tables.

The Python script's signature should be runnable as:

```bash
env UV_CACHE_DIR=korenblum/.uv-cache uv run python \
    ProofRefinement/Korenblum/Scratch/sprint_091_extended_architecture_sweep.py \
    > ProofRefinement/Korenblum/Scratch/sprint_091_extended_architecture_sweep.txt
```

### 2. `Scratch/sprint_091_extended_architecture_sweep.txt` (new, generated)

The complete stdout from the script. Must include:

  * Per-direction tables (E1, E2, E3) with per-window mass, total
    mass, margin, and Δ vs V67 baseline.
  * The combined-best-architecture line specifying
    `(extra_mode_count, rho_top, delta_lo, splits)`.
  * The c-sweep table from `c = 356564` to `c = 356575` in 1e-6
    steps under the best architecture.
  * The full-envelope re-verification at the candidate c.
  * The `DECISION` line: `Phase 0 GO with c_new = ... margin = ...`
    or `Phase 0 NO-GO; max margin at c = 356565 is +X.XXe-Y`.

### 3. `Scratch/sprint_091_witness.txt` (new, generated only on GO)

If GO, produced verbatim in a sprint-089-witness shape:

```
Sprint 091 GO witness
=====================

c_new                 : <numerator>/<denominator>
architecture_new      :
  - rho_top           : <value>
  - delta_lo          : <value>
  - extra_mode_count  : <int in {3, 4, 5, 6}>
  - mode count total  : <int>
  - branch1 boxes     : 1
  - window kinds      : <list>
  - window endpoints  : <full table to 28 digits>
full-envelope margin  : <value>  (>= 1e-4)
verification envelope : (dps=80, n_trunc=300)
```

If NO-GO, this file is NOT produced. The `.txt` log instead contains a
NO-GO paragraph that future planners can quote when pivoting to
structural-advance directions.

### 4. `Bulletin.md` and `Experience.md` append

One row each per the standard pattern:

  * GO outcome: cite c_new, architecture_new, full-envelope margin, the
    pinned witness file, and forward direction (sprint 092 ships V68
    via mixed-kernel reducer at `n = extra_mode_count + 7`, templated on
    sprint 090).
  * NO-GO outcome: cite the maximum margin observed at c = 356565
    (i.e., V67 + 1e-6) under the best architecture, the per-direction
    headroom estimates, and the **architectural-exhaustion claim**
    that future c-push attempts must come from outside the seven-
    -window-and-its-extensions design surface (per-k oracles,
    variable-α with non-contraction handling, tightened
    `H(c, ρ)`-style envelopes). Sprint 092 then pivots to one of:
    (a) hoist V53/V54/V57/V58/V63/V64/V66/V67 derived theorems into
    `Proof/` for trust-surface cleanup;
    (b) Wang Lemma 2 / Fourier orthogonality derivation as a derived
    theorem file (structural advance with no immediate c-push but
    establishing infrastructure for later);
    (c) variable-α Phase 0 re-sweep at a finer grid (sprint 077
    revisited) as a complementary numerical exploration.

### 5. NOT modified

  * `KorenblumPaper/` (read-only).
  * `Proof/Reduction.lean`, `Proof/Main.lean`, `Proof/CandidateContract.lean`.
  * Any candidate file (V0–V67).
  * Any per-candidate derived-theorem file under `Candidates/V<N>/`.
  * `Numerical_Library/` (no new wrappers; this sprint is exploration
    only).
  * `lemma.toml` (no new oracles, axioms, or import-policy entries).
  * `Proposals/` (no new proposal files; per the directive prompt).
  * Sprint 089's `.py` / `.txt` (frozen as sprint 089's witness;
    sprint 091's helpers are inlined fresh by importing or copying as
    needed).

## Acceptance criteria

1. `Scratch/sprint_091_extended_architecture_sweep.py` exists, is
   syntactically valid Python, and runs to completion under
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run python ...`
   without raising.

2. `Scratch/sprint_091_extended_architecture_sweep.txt` exists,
   contains the complete stdout including per-direction tables and a
   final `DECISION` line.

3. The `DECISION` line is exactly one of:
   - `Phase 0 GO; c_new = <p>/<q>, full-envelope margin = +<value>e-<exp> (>= 1e-4)`
   - `Phase 0 NO-GO; max margin at c = 356565/1000000 under best architecture = <signed value>; architectural surface (sprint 089 directions ∪ sprint 091 directions E1/E2/E3) is exhausted.`

4. **If GO**: `Scratch/sprint_091_witness.txt` exists, contains the
   eight-or-more-window endpoint sequence to ≥ 28 digits, the chosen c
   as a fraction, and the verification envelope `(dps=80, n_trunc=300)`.
   The full-envelope margin `≥ 1e-4` is reproducible by running the
   sweep code's `re_verify_at_full_envelope(c_new, architecture_new)`
   helper.

5. **If NO-GO**: the `.txt` log contains an explicit one-paragraph
   architectural-exhaustion claim that names:
   - the maximum margin at c = 356565 under the best architecture (a
     specific signed scalar);
   - the per-direction (E1, E2, E3) headroom uplifts at V67's c;
   - the cumulative ceiling: best architecture's joint mass at c = V67
     vs at c = 356565, with the "1 micro-c costs ~Xe-Y of margin"
     ratio computed.

6. `lake build` and the Evaluator are NOT exercised in this sprint
   (no Lean changes).

7. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern (with the GO or NO-GO outcome explicitly cited,
   plus the forward direction).

8. The sweep's wall-clock runtime is bounded: scan envelope `(dps=40,
   n_trunc=120)` for the per-direction tables, full envelope
   `(dps=80, n_trunc=300)` only for the candidate c re-verification.
   Total runtime ≤ 30 minutes. If the runtime exceeds 30 minutes,
   reduce the c-sweep step count or the τ̃-grid count.

## Out of scope

  * Any Lean change. This sprint is Scratch-only. If a candidate would
    benefit from the GO outcome, sprint 092 ships it.
  * Any `Numerical_Library` wrapper. The certified-mass wrapper is a
    sprint 092 deliverable contingent on sprint 091's GO.
  * Any `lemma.toml` row. No oracle / axiom / import-policy changes.
  * Any `Proposals/` filing. Per the directive prompt.
  * Any edit to `Candidates/V<N>.lean` or per-candidate
    derived-theorem files. V67 is the live ceiling; it is not
    perturbed by this sprint.
  * Any edit to sprint 089's artifacts. Sprint 091's sweep code may
    `from sprint_089_adaptive_seven_window_mass_sweep import ...` if
    convenient, but should not modify sprint 089's `.py`.
  * Push c above 356575/1000000 in the c-sweep table. The expected
    upper bound on the c-ceiling under the best architecture is well
    below 356575; sweeping further is wasted compute.
  * Test `extra_mode_count = 7` or higher (modes 11+). The geometric
    decline (factor ~0.4 per mode) makes mode-11+ contributions
    < 1e-7 of mass each, well below the noise floor at scan envelope.
  * Test variable-α cross-coupling kernels (sprint 077's domain). If
    sprint 091 returns NO-GO, the next planner may queue a sprint
    077-style re-sweep as a complementary exploration.

## Time budget

≤ 60 minutes runtime.

  * `Scratch/sprint_091_extended_architecture_sweep.py` authoring:
    ~30 minutes (75% reuse of sprint 089's 770 lines; ~150 new lines
    for the E1 extension to k ∈ {4, 5, 6}, the E2 sub-window probe,
    and the E3 hybrid probe).
  * Sweep execution: ~15 minutes (scan envelope per-direction
    ~6 minutes, full-envelope re-verify ~2 minutes, c-sweep
    ~5 minutes).
  * `Scratch/sprint_091_witness.txt` (GO branch only) or NO-GO
    paragraph (in the `.txt` log): ~5 minutes.
  * `Bulletin.md`/`Experience.md` row appends: ~5 minutes.

Total: ~55 minutes. Well under the harness's standard sprint budget.

## Stop conditions

  * **The sweep runs to completion and the `DECISION` line is `Phase 0
    GO with c_new > 89141/250000` and full-envelope margin ≥ 1e-4**:
    `STATUS=READY_FOR_EVALUATION`. Sprint 092 inherits the witness
    file and ships V68 at `c_new` via the mixed-kernel reducer at
    `n = extra_mode_count + 7 - 1 = …` (templated on sprint 090).

  * **The sweep runs to completion and the `DECISION` line is `Phase 0
    NO-GO`**: `STATUS=READY_FOR_EVALUATION` (the sprint's deliverable is
    the NO-GO certification, which is also a valid sprint outcome —
    not all sprints push the score). Sprint 092 pivots to one of the
    three pivot directions named in the `Bulletin.md` / `Experience.md`
    forward direction.

  * **The sweep raises an exception or fails to run to completion**:
    diagnose the error, fix the script if the bug is in sprint 091's
    new code (E1/E2/E3 extension), and re-run. If the error is
    intrinsic to mpmath at the scan envelope (e.g., `mp.quad` failure
    at very deep bands), document the obstruction at
    `Scratch/sprint_091_obstruction.md` and reduce the integration
    precision until the sweep completes. `STATUS=READY_FOR_EVALUATION`
    if the sweep produces a valid DECISION line; `STATUS=BLOCKED`
    otherwise.

  * **A direction (E1, E2, or E3) produces a sub-architecture with
    NEGATIVE mass (i.e., a sweep-code bug)**: do not ship the GO
    branch on that sub-architecture. Document at
    `Scratch/sprint_091_obstruction.md`, fix the bug if it is in
    sprint 091's new helpers, and re-run. `STATUS=BLOCKED` if the bug
    is in sprint 089's frozen code (in which case sprint 092 fixes
    sprint 089's `.py` separately).

  * **A new free axiom would be required**: not applicable to this
    sprint (no Lean changes). If the generator believes a Lean change
    is needed in sprint 091, that is a contract violation; the
    generator must `STATUS=BLOCKED` and document at
    `Scratch/sprint_091_obstruction.md`. The next planner re-scopes.

## Notes for the generator

  * **Read first**:
    - `Scratch/sprint_089_adaptive_seven_window_mass_sweep.py` (~770
      lines; your direct template).
    - `Scratch/sprint_089_witness.txt` (the V67 architecture's
      verbatim witness).
    - `Scratch/sprint_089_adaptive_seven_window_mass_sweep.txt`
      (sprint 089's per-direction tables; useful baseline for the
      Δ-vs-V67-baseline columns in sprint 091's tables).
    - `Sprint_Contracts/sprint_089_adaptive_phase0_sweep_for_c_ceiling_above_v66.md`
      (sprint 089's contract; same structural shape).
    - `Sprint_Contracts/sprint_087_v38_seven_window_mass_sweep_phase0_and_wrapper.md`
      (the original Phase-0 mass-sweep contract; the methodology
      sprint 091 inherits).

  * **Reuse sprint 089's helpers**. Do `from
    sprint_089_adaptive_seven_window_mass_sweep import paper_factor,
    paper_lambda, k_squared_at_rho, term_j, mode_window_mass,
    branch1_integrand, branch1_window_mass, tau_j, fraction_to_mpf`
    at the top of sprint 091's script, OR copy the helper bodies
    verbatim if the import fails (likely fine, both files in the same
    directory).

  * **Run scan-envelope first, full-envelope only on candidates**.
    The scan envelope `(dps=40, n_trunc=120)` is fast (~30 seconds
    per arch variant). Use it for the per-direction tables and the
    initial c-sweep. Re-verify only the candidate c (the largest
    margin-≥-1e-4 c) at full envelope `(dps=80, n_trunc=300)`. Do
    not re-verify every architecture variant — that explodes runtime.

  * **The c-sweep step size is 1e-6**. At scan envelope, computing
    the joint mass takes ~10 seconds per c, so 12 c values takes
    ~2 minutes. Do not use a 1e-7 step (12× more c values, 20+
    minutes). If the candidate c lies between two 1e-6 steps,
    bisect at full envelope to nail it.

  * **The expected GO outcome is `c_new = 356566/1000000` or
    `356567/1000000`**, with `extra_mode_count = 5` or `6`. If the
    sweep's GO line names a c above 356575, double-check the
    mass calculation — that's outside the expected range.

  * **The expected NO-GO outcome** records the mass at c = 356565
    under the best architecture as ~+9.5e-5 to +1.0e-4 (i.e., near
    but slightly below 1e-4), with the per-direction E1/E2/E3
    headrooms documented as roughly +3-5e-6 / 0 / null.

  * **Do not modify sprint 089's `.py`**. Sprint 091's helpers are
    independent extensions; sprint 089's code is frozen as that
    sprint's witness.

  * **Wall-clock honesty**. Sprint 089 ran in ~6 minutes scan +
    ~2 minutes full-envelope. Sprint 091 should be similar; if the
    runtime exceeds 30 minutes, the sweep is mis-configured (e.g.,
    too many c-sweep points, full envelope used for scan).

  * **No Lean side**. This sprint produces ONLY Python and text
    files. The `lake build` and `Evaluator.py` invocations are
    skipped per the brief. The next planner consumes the sweep's
    DECISION line to choose between sprint 092's two routes (GO ⇒
    Lean V68 ship; NO-GO ⇒ structural-advance pivot).

  * **Forward direction for the planner of sprint 092** (for context,
    not for action this sprint):
    - On GO: sprint 092 ships V68 at c_new via the mixed-kernel
      reducer at `n = extra_mode_count + 7 - 1`. Templated on sprint
      090. New `Numerical_Library` wrapper, new `[[oracles]]` row,
      sibling `Candidates/V68/`-named derived theorem file with the
      additional τ-bounds for j=8/9/10 (mechanical extension of V67's
      EightWindowEndpoints). Estimated cost: 1 generator session
      (~2-3 hours).
    - On NO-GO: sprint 092 pivots to one of three structural-advance
      directions (hoist derived theorems / Wang Lemma 2 derivation /
      variable-α Phase 0 re-sweep). Each is a separate planner
      decision; the NO-GO log block in `Bulletin.md` / `Experience.md`
      gives the next planner the quantitative basis for choosing.
