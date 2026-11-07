# Sprint 101: Monotonicity-aware `Λ_upper` selection inside `_two_window_mass_window_lower_arb` — algorithmic tightening of sprint 099's frozen helper to unblock V66/V67/V68 oracle migrations

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V64.lean` (sprint 099's migration target — its
joint-mass oracle is the only existing consumer of
`_two_window_mass_window_lower_arb`; the live frontier remains V68 at
`c = 71313/200000`, whose oracle wrapper has not yet been migrated).
**Target file**: `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
(refines the body of the existing private helper
`_two_window_mass_window_lower_arb` — a Numerical_Library algorithmic
tightening, not a new wrapper, not a Lean change, not a trust-base
expansion).
**Direction**: oracle-support (structural / credibility — score-neutral
algorithmic tightening of one helper used by an already-shipped
arb-rigorous oracle wrapper, with the explicit downstream goal of
unblocking V66/V67/V68's oracle migrations under the same template).

## Goal

Replace the per-subinterval `Λ_upper` construction in
`_two_window_mass_window_lower_arb` (sprint 099's frozen helper at
`Numerical_Library/rigorous_scalar.py`) with a **monotonicity-aware
selection** that exploits the single-peakedness of `K(c, ρ)` at
`ρ = sqrt(c)` (Wang's t-distance structure, already implicitly used by
sprint 099 when it lists `clamp(sqrt(c), ρ_lo, ρ_hi)` as one of three
candidate evaluation points).

The current strategy on each subinterval `[ρ_lo, ρ_hi]` is

    K_box       = union(K(ρ_lo), K(ρ_hi),  K(sqrt(c))    if straddle)
    Lam_upper   = Λ(K_box)

which produces a per-subinterval radius proportional to the
subinterval *width*, and accumulates over the subdivision into an
`O(1/n_subdivisions)` loss on the integral lower bound. Sprint 100
diagnosed this exactly: at `n_subdivisions = 16384`, the dominant
radius source on V66 is `m_1.rad ≈ 9.8e-5` from a single wide window
`[c·sqrt(4/3), 0.999999]` of width `≈ 0.59`, and dps is irrelevant
(verified by sprint 100 across `dps ∈ {80, 200, 400}`).

The new strategy uses **rigorous arb-decided position** of the
subinterval relative to `sqrt(c)`:

    sqrt_c_arb = c_arb.sqrt()          # rigorous interval enclosure

    if (rho_hi <= sqrt_c_arb) is True:                # rigorous: rho_hi ≤ sqrt(c)
        # K is increasing on the entire subinterval; max at rho_hi.
        K_box = K(rho_hi)
    elif (sqrt_c_arb <= rho_lo) is True:              # rigorous: sqrt(c) ≤ rho_lo
        # K is decreasing on the entire subinterval; max at rho_lo.
        K_box = K(rho_lo)
    else:                                             # straddle or rigorously-undecided
        K_box = union(K(rho_lo), K(rho_hi), K(sqrt_c_arb))

    Lam_upper = Λ(K_box)

In the two well-separated branches the per-subinterval `K_box` is a
**point evaluation**, whose arb radius is governed by arb's internal
arithmetic precision (typically `≈ 10^(-50)` at `dps = 80`) rather
than by the subinterval width. The straddle case keeps the existing
three-candidate union for rigour. The integrand-product
`(2ρ_lo) / (H_j_upper · Lam_upper)` and the subdivision-summation
shape are unchanged.

The monotonicity claim — `K(c, ρ)` is single-peaked at `ρ = sqrt(c)`
on `(c, 1)` — is exactly the same fact sprint 099's helper already
encodes (it evaluates K at three candidate points
`{ρ_lo, ρ_hi, clamp(sqrt(c), ρ_lo, ρ_hi)}`); this sprint promotes
that implicit single-peakedness to an explicit dispatch on
rigorously-decided position. No new mathematical content is
introduced.

The wrapper-level external contract is preserved conjunct-for-conjunct:
- the helper signature is unchanged (`(c_arb, j, rho_start, rho_stop,
  n_trunc, n_subdivisions) -> arb`),
- callers (`certify_two_window_mass_at_35646_sqrt` from sprint 099)
  see no signature change,
- the registered `[[oracles]]` entry in `lemma.toml` (line 487) and
  the candidate-side axiom + use site in `Candidates/V64.lean:316`
  are byte-preserved,
- V64's `axioms_used` audit set is preserved set-theoretically,
- V64's evaluator score remains `35646/100000 = 17823/50000`.

## Why

Sprint 100 attempted the second `mp.quad → arb` migration (V66's
seven-window oracle wrapper `certify_seven_window_mass_at_356562_sqrt`)
and was BLOCKED at `n_subdivisions = 16384` with rigorous total-mass
enclosure `[1.000 +/- 1.43e-4]` (margin lower endpoint ≈ −1.43e-4),
unable to clear the strict-margin floor `1 + 10^(-30)`. Tree was
reverted byte-identical. The diagnosis (Bulletin sprint 100 entry,
`Scratch/sprint_100_obstruction.md`, Experience.md sprint 100 section)
is precise:

- Per-window arb radii at `n_subdivisions = 2048`: `m_a1 ≈ 3.17e-10,
  m_a2 ≈ 1.21e-10, m_a3 ≈ 4.48e-10, m_4 ≈ 1.13e-08, m_3 ≈ 6.67e-08,
  m_2 ≈ 9.34e-07, m_1 ≈ 7.83e-04`. Mode1 dominates by **three orders
  of magnitude**.
- The mode1 window is wide: `[c·sqrt(4/3), 999999/1000000] ≈ [0.4117,
  0.999999]`, width `≈ 0.59`.
- m_1.rad scales as `O(1/n_subdivisions)`: `7.83e-4 (n=2048) →
  3.92e-4 (n=4096) → 1.96e-4 (n=8192) → 9.80e-5 (n=16384)` — exactly
  halving with each n-doubling, consistent with a per-subinterval
  union radius of `O(width)/2 = O((rho_hi - rho_lo)/2)` summed over
  the subdivision.
- dps invariance verified at `dps ∈ {80, 200, 400}`: same
  `m_1.rad = 7.832e-4` at `n_subdivisions = 2048`. The radius is
  **not** from arb working precision; it is a consequence of the
  union's geometric extent.
- n_trunc invariance: the truncation tail `c^600 ≈ 10^(-261)` is
  negligible at `n_trunc = 300` (already used).

To clear V66's centered margin (`+1.20e-4`) under the existing helper
contract would require `n_subdivisions ≥ 32768 = 2 × cap`, i.e. raising
the contract cap. Sprint 100's option (2) (raise the V66 wrapper's
cap to 65536) is brute force, ~4× longer runtime, and **does not
retroactively tighten V64's bound or generalise to V67/V68**. Sprint
100's option (1) — this sprint — addresses the root cause:

> The single-point-of-evaluation case eliminates the O(width) union
> radius, dropping `m_1.rad` from O(1/n_subdivisions) to tight
> arb-arithmetic precision. Sprint 102 could then re-attempt the
> V66 migration with margin headroom to spare. The change to
> `_two_window_mass_window_lower_arb` is a refinement (no new
> oracle, same external contract); it would also retroactively
> tighten V64's bound from sprint 099.
>     — sprint 100 entry, Bulletin §sprint_100, Suggested follow-up

The user's recent planner-launch context reaffirms the same priority:

> Option 1 is the cleanest path forward — it unblocks V66/V67/V68
> migrations and tightens V64's bound.

After this sprint:
- Sprint 099's V64 `_two_window_mass_window_lower_arb` retroactively
  tightens its certified margin lower endpoint (was `+5.0556e-4` at
  `n_subdivisions = 2048`; under the monotonicity-aware Λ_upper, on
  V64's narrow mode1 window `[c·sqrt(4/3), 0.999999] ≈ [0.412,
  0.999999]` and mode2 window `[c·sqrt(9/8), c·sqrt(4/3)] ≈ [0.378,
  0.412]`, the radius drops by orders of magnitude — exact magnitude
  measured during the sprint).
- The next sprint (102) can re-attempt V66's seven-window oracle
  migration under the existing template with the same three helpers
  shipped by sprint 099 (now strengthened) plus the
  `_branch1_window_mass_lower_arb` helper that sprint 100 already
  implemented and verified locally on the boxA windows
  (~e-10 radius — three orders of magnitude tighter than needed).
  V66's centered margin `+1.20e-4` should clear the floor with
  margin headroom to spare.
- V67's eight-window and V68's eleven-window oracle migrations
  follow the same template at the same algorithmic cost.
- After all four mass-window oracles are arb-migrated (V64 done,
  V65 pending — rational-endpoint sibling, V66/V67/V68 to follow),
  Bulletin §B(3)'s "mp.quad, not interval arithmetic" caveat closes
  for the entire post-V52 score-push chain.

The strongest objections to choosing this direction over alternatives:

  (a) **"Why not Sprint 100's option (2) — raise n_subdivisions cap
      to 65536 in the V66 wrapper only?"** The brute-force option
      is more compute (≈80s vs ≈8s per sprint 099 measurement),
      doesn't retroactively help V64, and will likely need a
      further bump for V67/V68 (V67 is 8 windows including a wider
      span; V68 has 11). The algorithmic fix scales for free.
      Sprint 100 itself flagged option (1) as preferred.

  (b) **"Why not skip ahead to V66's wrapper migration directly,
      assuming the helper edit?"** The user's recent context puts
      the helper tightening as Sprint 101 and the V66 re-attempt
      as Sprint 102, deliberately splitting the work into two
      sessions: (1) tighten the helper and verify against V64's
      already-shipped wrapper as a regression test (since V64's
      same wrapper continues to clear with byte-preserved external
      behaviour); (2) re-port the V66 wrapper using the tightened
      helper plus sprint 100's already-designed
      `_branch1_window_mass_lower_arb`. Bundling both into one
      sprint risks a generator session that runs out of budget
      mid-V66-port and leaves a partial commit. One-helper-per-sprint
      is the discipline that has worked across sprints 086–099.

  (c) **"Why not hoist `Candidates/V66/Branch1Integrability.lean`
      to `Proof/`?"** Demoted by sprints 097, 098, and 099 as
      architecture-specific (only V67/V68 import it; same family).
      No third cross-architecture consumer has surfaced. Currently
      score-neutral structural cleanup with no immediate downstream
      payoff. Score-neutral but with **lower expected value than
      this sprint**, which has a concrete chain
      `Sprint 101 → Sprint 102 → Sprint 103 → Sprint 104` to
      complete the V66/V67/V68 oracle migration trio.

  (d) **"Why not Wang Lemma 2 / Fourier orthogonality as a derived
      theorem in `Proof/`?"** Demoted across four prior planners
      (sprints 096–099) as speculative infrastructure absent a
      Lean consumer. Same demotion still holds. Best queued *after*
      a sprint that explicitly needs the boundary-L² expansion as
      a load-bearing step; no current sprint chain demands it.

  (e) **"Why not push past V68's c = 71313/200000?"** Slacks 1, 3,
      5 falsified by sprints 093, 094, 095; Slack 2 settled by
      sprint 077; Slack 4 needs a trust expansion proposal. The
      score-push surface at the current trust surface is exhausted.
      A c-push sprint without a fresh structural insight
      recapitulates a falsified hypothesis.

  (f) **"Is this a numerical-budget push in disguise?"** No — it
      is an algorithmic precision improvement. The fix dispatches
      on a rigorously-decided position relative to `sqrt(c)` and
      uses point evaluation in the well-separated branches. No
      `n_subdivisions` cap raise. No `n_trunc` raise. No `dps`
      raise. The compute budget is **strictly lower** than the
      brute-force alternative because each subinterval's K_box
      becomes a single point evaluation (no union, no triple
      candidate evaluation) outside the sqrt(c) straddle case.

  (g) **"Is the monotonicity claim actually mathematically sound?"**
      Yes. `K(c, ρ) = sqrt(c) · t(ρ)` where `t(ρ) = (1 + c/ρ²) ·
      (1 + ρ²/c)^(-1) · ρ^(-1)`-shape (Wang's t-distance from
      the unit circle to `ρ` on the disk), and the maximum of
      `K(c, ρ)` on `(c, 1)` is attained at `ρ = sqrt(c)` by
      direct differentiation. Sprint 099's helper already encodes
      this implicitly (the third candidate evaluation point is
      `clamp(sqrt(c), ρ_lo, ρ_hi)`), so the math is not new —
      only the dispatch is. The straddle case retains a rigorous
      union, so even if the monotonicity claim were subtly wrong
      on some narrow corner case, the rigour of the lower bound
      is unaffected.

  (h) **"Is the acceptance criterion falsifiable in one Generator
      session?"** Yes. The fix is a 5-line if/elif/else inside an
      existing 100-line helper. The falsifiers are:
      (i) `lake build` of V64 (Lean side is byte-preserved, trivially
          passes),
      (ii) Evaluator on V64 with `pass: true`, `score = 17823/50000`,
           `axioms_used` set unchanged,
      (iii) the migrated `certify_two_window_mass_at_35646_sqrt`
            still returns `Fraction(1, 1)` and clears the
            `1 + 10^(-30)` floor — *with strictly tighter rigorous
            margin lower endpoint than sprint 099* (sprint 099's
            measurement was `+5.0556e-4` at `n_subdivisions = 2048`;
            the tightened helper should produce a margin reading at
            `n_subdivisions = 256` of comparable or larger
            magnitude),
      (iv) a Phase 0 witness script that reports per-window radii
           at `n_subdivisions ∈ {256, 512, 1024, 2048}` and
           confirms the m_1 radius is now governed by arb-arithmetic
           precision (≈ `10^(-30)` at `dps = 80`) rather than
           subdivision-width.
      All four are cheap, single-shot evaluator/python runs.

  (i) **"Does the closure depend on a Mathlib lemma that doesn't
      exist?"** No Lean change is involved. The whole sprint is a
      Numerical_Library python edit.

  (j) **"Is there a concrete witness it could succeed?"** Yes —
      sprint 099's per-window radii at `n_subdivisions = 2048`
      (mode1 at `m_1.rad ≈ 9.34e-7`, in V64's narrower mode1
      window) and sprint 100's measurement on V66's wider mode1
      window (`m_1.rad ≈ 7.83e-4`) jointly diagnose the union-radius
      `O(width)` scaling. Removing the union in the well-separated
      branches eliminates this scaling; the residual radius is from
      arb-arithmetic point-evaluation, which is `~10^(-50)` at
      `dps = 80`. Three orders of magnitude tighter than V66's
      target.

This is the cleanest path forward. It buys credibility for V64
*today* and credibility for V66/V67/V68 *tomorrow*, all under one
helper edit.

## Concrete edits expected

- **Edit** `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`,
  inside the body of `_two_window_mass_window_lower_arb` (the helper
  shipped by sprint 099):

  - **Compute `sqrt_c_arb` once outside the subdivision loop**:
        sqrt_c_arb = c_arb.sqrt()
    (rigorous arb interval enclosure of `sqrt(c)` at the helper's
    working precision).

  - **Inside the per-subinterval loop**, replace the existing
    `K_box = union(K(rho_lo), K(rho_hi), K(clamp(sqrt(c), rho_lo,
    rho_hi)))` construction with a three-way dispatch:

        if (rho_hi <= sqrt_c_arb) is True:
            # rigorously decided: subinterval is left of sqrt(c).
            # K(c, ρ) is increasing on (0, sqrt(c)); max at rho_hi.
            K_box = _two_window_mass_paper_K_arb(c_arb, rho_hi, n_trunc)
        elif (sqrt_c_arb <= rho_lo) is True:
            # rigorously decided: subinterval is right of sqrt(c).
            # K(c, ρ) is decreasing on (sqrt(c), 1); max at rho_lo.
            K_box = _two_window_mass_paper_K_arb(c_arb, rho_lo, n_trunc)
        else:
            # straddle case (or rigorously undecided): preserve the
            # existing three-candidate union for safety.
            K_box = (
                _two_window_mass_paper_K_arb(c_arb, rho_lo, n_trunc)
                .union(_two_window_mass_paper_K_arb(c_arb, rho_hi, n_trunc))
                .union(_two_window_mass_paper_K_arb(c_arb, sqrt_c_arb, n_trunc))
            )

    Then feed `K_box` through
    `_two_window_mass_paper_lambda_from_K_arb` exactly as before.
    All other lines of the helper (the H_j_upper computation at
    `rho_lo`, the `2 * rho_lo` lower bound, the integrand-product
    `(2*rho_lo) / (H_j_upper * Lam_upper)`, the subdivision-summation,
    and the K-cache structure) are byte-preserved.

  - **Preserve the helper signature** exactly:
    `_two_window_mass_window_lower_arb(c_arb, j, rho_start, rho_stop,
    n_trunc, n_subdivisions) -> arb`.

  - **Preserve the K-cache** that sprint 099 introduced (per the
    sprint 099 PASS note: *"K-cache halves the work by reusing
    K(ρ_endpoint) across adjacent sub-intervals"*). The two
    well-separated branches still hit the cache for `K(rho_lo)`
    and `K(rho_hi)`; the straddle case hits the cache for `K(rho_lo)`
    and `K(rho_hi)` plus a fresh evaluation at `sqrt_c_arb` (the
    sqrt(c) point doesn't fall on the subdivision grid in general,
    but only the straddle case touches it, and only for one
    subinterval per window — at most twice per `_two_window_mass_window_lower_arb`
    invocation, since `sqrt(c)` is a single point that sits in at
    most one subinterval per window).

  - **No edits** to other helpers. `_two_window_mass_paper_factor_arb`,
    `_two_window_mass_paper_lambda_arb`,
    `_two_window_mass_paper_K_arb`,
    `_two_window_mass_paper_lambda_from_K_arb` are byte-preserved
    (the dispatch reuses them all by name). The wrapper
    `certify_two_window_mass_at_35646_sqrt` is byte-preserved (it
    calls `_two_window_mass_window_lower_arb` with the same
    arguments).

  - **No edits** to the `mp.quad`-based legacy helpers
    (`_two_window_mass_paper_factor`, `_two_window_mass_paper_lambda`,
    `_two_window_mass_term_j`, `_two_window_mass_window`,
    `certify_two_window_mass`, `certify_two_window_mass_at_35646`).
    These remain consumed by the rational-endpoint sibling and by
    the seven/eight/eleven-window mass wrappers (V66/V67/V68's
    oracles, currently still on `mp.quad`).

- **No edits** to:
  - `lemma.toml`: the `[[oracles]]` entry at line 487 already
    points to `rigorous_scalar.certify_two_window_mass_at_35646_sqrt`;
    the helper edit is internal to that function's call chain.
    Byte-preserved.
  - `Candidates/V64.lean`: the candidate-side
    `axiom h_two_window_mass_certified_at_35646_sqrt` and its
    use site at line 316 are byte-preserved.
  - `Candidates/V65–V68.lean`: V65 uses the rational-endpoint
    sibling (`mp.quad`-backed); V66/V67/V68 use the seven/eight/
    eleven-window oracles (`mp.quad`-backed). None of them
    consume `_two_window_mass_window_lower_arb` directly.
  - `KorenblumPaper/`: read-only (forbidden by AGENT_BRIEF).
  - `Proof/`: unchanged.
  - `Numerical_Library/types.py`, `Numerical_Library/numerical_audit.py`:
    no schema changes.

- **Add** a Phase 0 sanity script at
  `Scratch/sprint_101_monotonic_lambda_witness.py`: a standalone
  python script that calls the migrated wrapper once at the
  pinned sqrt endpoints and prints, **at each of
  `n_subdivisions ∈ {256, 512, 1024, 2048}`**, the per-window
  radii `m_1.rad`, `m_2.rad` and the total margin lower endpoint.
  Document **before** vs **after** the helper edit (side-by-side
  table). The script may import a frozen-string copy of sprint
  099's pre-edit helper as a baseline for the comparison, or
  simply present the new readings alongside the table from
  `Scratch/sprint_100_obstruction.md`. Acceptance: the new
  per-window radii in V64's two windows are at least one order
  of magnitude tighter than the corresponding sprint-099 readings
  at the same `n_subdivisions` (extracted from sprint 099's
  arb_two_window_mass_witness or recomputed against a frozen
  baseline).

- **Re-evaluate V64** by running
  `bash scripts/korenblum_eval_candidate.sh Candidates/V64.lean`
  and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V64`
    succeeds (Lean side byte-preserved).
  - Evaluator returns `pass: true`, `score: 17823/50000` (=
    `35646/100000`, unchanged from sprint 099's evaluator
    score).
  - `axioms_used` set is **identical** (set-theoretically) to
    V64's pre-sprint-101 evaluator log entry's `axioms_used`
    set: exactly the six entries `propext`, `Classical.choice`,
    `Quot.sound`,
    `ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt`,
    `ProofRefinement.Korenblum.Candidates.V64.hH2_v64`,
    `ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64`.
  - `oracle_checks` table records exactly one entry with
    `axiom = h_two_window_mass_certified_at_35646_sqrt`,
    `bound_field = two_window_mass_lower`,
    `oracle_bound = 1`, `declared = 1`, `ok = true`.

- **Re-evaluate V68** by running
  `bash scripts/korenblum_eval_candidate.sh Candidates/V68.lean`
  and confirming `pass: true`, `score: 71313/200000`,
  `axioms_used` set unchanged (the live frontier is byte-
  preserved; V68 does not invoke `_two_window_mass_window_lower_arb`,
  but a falsifier on the live frontier is cheap and catches any
  unintended side effect of the rigorous_scalar.py edit).

- `Experience.md`: append a "Sprint 101 — monotonicity-aware
  Λ_upper inside `_two_window_mass_window_lower_arb`" subsection
  summarizing:
  - the per-subinterval dispatch shape (left of √c, right of √c,
    straddle),
  - the rigorous monotonicity claim used (K(c, ρ) single-peaked
    at ρ = sqrt(c)),
  - the per-window radii table before/after at
    `n_subdivisions ∈ {256, 512, 1024, 2048}`,
  - the V64 re-evaluation result (`pass: true`,
    `score: 17823/50000`, `axioms_used` unchanged),
  - the V68 re-evaluation result (`pass: true`,
    `score: 71313/200000`, `axioms_used` unchanged),
  - the forward implication for sprint 102 (V66's seven-window
    wrapper migration is now expected to clear `+1.20e-4` margin
    under the existing template; sprint 100's already-implemented
    `_branch1_window_mass_lower_arb` becomes the only new helper
    needed).

- `Bulletin.md`: append one row
  `sprint_101 PASS|FAIL: <title>` per the standard pattern.

No edits to:
- `KorenblumPaper/` (read-only).
- `Proposals/` (no proposal filed; the helper edit is a
  Numerical_Library algorithmic refinement that preserves the
  external contract conjunct-for-conjunct, not a trust-base
  expansion).
- The mathematical content of any candidate.
- Any candidate-side `axiom` declaration.
- The `[seed_axioms]`, `[[oracles]]`, `[import_policy]`, or
  `[workspace_import_policy]` blocks of `lemma.toml`.
- `Proof/Summability.lean`, `Proof/Integrability.lean`,
  `Proof/DiskInnerSeriesBridge.lean`, `Proof/Reduction.lean`,
  `Proof/Main.lean`, `Proof/CandidateContract.lean`.

## Acceptance criteria

1. The migrated `certify_two_window_mass_at_35646_sqrt`, called
   standalone (e.g.
   `python -c "from Numerical_Library.rigorous_scalar import
   certify_two_window_mass_at_35646_sqrt;
   print(certify_two_window_mass_at_35646_sqrt())"`), returns
   `Fraction(1, 1)` and does not raise.

2. The helper `_two_window_mass_window_lower_arb` body now
   dispatches on three branches (left-of-sqrt(c),
   right-of-sqrt(c), straddle) using rigorous `arb` comparisons
   `(... <= ...) is True`. The straddle branch preserves the
   existing three-candidate union (`K(rho_lo) ∪ K(rho_hi) ∪
   K(sqrt_c_arb)`); the two well-separated branches use a
   single point evaluation. The helper signature and external
   contract are unchanged.

3. `lake build ProofRefinement.Korenblum.Candidates.V64`
   succeeds.

4. `lake build ProofRefinement.Korenblum.Candidates.V68`
   succeeds.

5. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V64.lean` succeeds with
   `pass: true` and `score: "17823/50000"` (= `35646/100000`,
   unchanged from sprint 099's evaluator score).

6. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (unchanged from
   V68's pre-sprint score).

7. The post-sprint V64 evaluator log entry's `axioms_used`
   set is **identical** (set-theoretically, comparing the
   `name` field of each entry) to V64's pre-sprint log
   entry's `axioms_used` set: exactly the six entries listed
   under "Re-evaluate V64" above. No new axioms introduced.
   No old axioms removed.

8. The post-sprint V64 evaluator log entry's `oracle_checks`
   table contains exactly one entry with
   `axiom = "h_two_window_mass_certified_at_35646_sqrt"`,
   `bound_field = "two_window_mass_lower"`,
   `oracle_bound = "1"`, `declared = "1"`, `ok = true`.

9. The Phase 0 sanity script
   `Scratch/sprint_101_monotonic_lambda_witness.py` reports
   per-window radii `m_1.rad`, `m_2.rad` at
   `n_subdivisions ∈ {256, 512, 1024, 2048}` and confirms that
   on V64's mode1 window `[c·sqrt(4/3), 0.999999]` the **m_1
   radius at `n_subdivisions = 2048` is at least one order of
   magnitude smaller than sprint 099's reading at the same
   `n_subdivisions`** (sprint 099's m_1.rad on V64's mode1
   window is recorded in `Scratch/sprint_099_arb_two_window_mass_witness.py`'s
   output, or in sprint 100's table for V66's wider mode1
   window — V64's mode1 window is a strictly narrower subset
   of V66's, so the comparison at the same `n_subdivisions` is
   apples-to-apples). The expected reduction factor is
   `>>10×` (point evaluation vs union-of-three), so a 10×
   threshold leaves ample margin if the reading is partially
   limited by some other radius source.

10. The migrated wrapper completes within **~60 seconds** on
    a single invocation. (Sprint 099's `mp.quad → arb` migration
    completed in ~8 seconds at `n_subdivisions = 2048`; the
    helper edit may slightly reduce or slightly increase
    runtime depending on whether the dispatch elides a K
    evaluation — in practice the same or faster, since two
    of the three K evaluations are saved per non-straddle
    subinterval.)

11. `Experience.md` and `Bulletin.md` each gain one row per
    the standard pattern.

The sprint is **PASS** if all 11 criteria are met. The sprint is
**FAIL** if V64 or V68's evaluator score changes, the
`axioms_used` set diverges, the migrated wrapper raises
`RuntimeError` (i.e. the arb-rigorous bound fails to clear the
floor — almost certainly indicating a bug in the dispatch logic
or a sign/comparison-direction inversion), or the wrapper
exceeds the 60-second time ceiling.

## Out of scope

- **Re-attempt V66's seven-window oracle migration** under the
  tightened helper. That is the **explicit follow-up sprint
  (Sprint 102)**. Bundling it here risks a generator session
  that runs out of budget mid-V66-port and leaves a partial
  commit. Sprint 102 will reuse the
  `_branch1_window_mass_lower_arb` helper that sprint 100
  already implemented and verified locally on the boxA windows
  (~e-10 radius); sprint 102's contract will explicitly cite
  sprint 100's verified-correct shape.

- **Migrate V67's eight-window or V68's eleven-window oracle**.
  These follow the same template as V66's; they are sprints
  103 and 104 in the queue.

- **Migrate V65's `certify_two_window_mass_at_35646`** (the
  rational-endpoint sibling of sprint 099's wrapper). Its
  body is structurally similar but uses rational endpoints
  rather than `c·sqrt(4/3)` / `c·sqrt(9/8)`. Independent
  follow-up sprint.

- **Migrate any of the `certify_eq15_at_*` family** (5
  wrappers: seed, 3560, 3562, hp_3564, hp_35645). These are
  partially arb-equipped already (sprint 010 made
  `k_upper_on_interval` and `lambda_upper_on_interval`
  rigorous); the `mp.quad` quadrature inside them is the
  remaining dependency. Independent follow-up sprint or
  sprints.

- **Edit the helper to use a different precision strategy**
  (e.g. raise `dps`, raise `n_trunc`, raise `n_subdivisions`
  cap). The current strategy at `dps = 80` and `n_trunc = 200`
  is preserved; only the per-subinterval Λ_upper construction
  changes.

- **Edit `Candidates/V64.lean`, `Candidates/V65–V68.lean`, or
  any other Lean file**. The helper edit is a Python-side
  internal change to one wrapper's call chain; the
  candidate-side `axiom` declarations and their usages are
  byte-preserved.

- **Edit the `[[oracles]]` registration in `lemma.toml`**.
  The `oracle_fn` continues to point at the same wrapper
  name; the candidate axiom name is unchanged; the bound
  field is unchanged.

- **Add or remove free axioms**. The helper edit preserves
  the trust surface conjunct-for-conjunct.

- **File a `Proposals/` entry**. The change is a
  Numerical_Library algorithmic refinement that preserves the
  wrapper's external contract byte-for-byte. Per AGENT_BRIEF
  lines 80–86 (oracle-shaped additions/edits can be done
  inline as long as the contract names the wrapper, the
  lemma.toml entry, and the use site), this is an inline edit
  to an existing wrapper's internals.

- **Change the final theorem statement of any candidate**.

- **Hoist `Candidates/V66/Branch1Integrability.lean` to
  `Proof/`**. Demoted by sprints 097/098/099 as
  architecture-specific; no third cross-architecture consumer
  has surfaced.

- **Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`**.
  No current consumer; queueing it speculatively before
  establishing a Lean derivation chain that needs it would
  risk infrastructure-speculation work.

- **Run any Phase 0 numerical falsifier sweep** beyond the
  sanity-check witness script
  (`Scratch/sprint_101_monotonic_lambda_witness.py`). The edit
  is structural; the sanity script exists only to produce a
  human-readable per-window radius table and confirm the
  expected order-of-magnitude tightening.

- **Push past V68's `c = 71313/200000`**. The score-push
  surface at the existing trust surface remains exhausted
  (Slacks 1/3/5 falsified by sprints 093/094/095; Slack 2
  settled by sprint 077; Slack 4 needs a trust expansion).
  After this sprint, the live frontier remains V68 at
  `71313/200000`.

- **Discharge `hH2_v6×` or `hCircleGapInt_v6×`** from
  `Section2Assumptions` (Slack 4 / Bulletin §B(4)). Requires
  either a `KorenblumPaper/` edit (forbidden by AGENT_BRIEF)
  or a trust-base expansion proposal whose math is not pinned
  tightly enough yet — out of scope for an oracle-helper-
  tightening sprint.

## Time budget

≤ 60 minutes wall-clock:
  - Helper edit: ~5 minutes (a 10–20 line dispatch change
    inside an existing 100-line helper).
  - Migrated-wrapper standalone invocation: ~10 seconds at
    `n_subdivisions = 2048` (sprint 099 measured 8s; the
    dispatch saves two K evaluations per non-straddle
    subinterval, so likely faster).
  - V64 evaluator: ~3 minutes (typecheck + axiom scan +
    oracle invocation).
  - V68 evaluator: ~3 minutes (V68 does not invoke the
    helper; timing matches sprint 098/099 at ~2.5 minutes).
  - Phase 0 sanity script: ~30 seconds (single invocation
    sweeping `n_subdivisions ∈ {256, 512, 1024, 2048}`).
  - Witness updates to `Experience.md`, `Bulletin.md`:
    ~10 minutes.

≤ 1 generator session (~1.5–2 hours including the helper
dispatch (~20 lines), the Phase 0 sanity script (~80 lines
including the side-by-side table formatting), the two
evaluator runs (~6 minutes total wall-clock), and the
witness updates).

## Stop conditions

- All 11 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- The migrated wrapper raises `RuntimeError` because the
  rigorous arb-lower bound fails to clear `1 + 10^(-30)`
  even with the tightened helper at `n_subdivisions = 2048`:
  `STATUS=BLOCKED` with the arb-enclosure of the failing
  margin. Most likely cause: a sign-or-comparison-direction
  inversion in the dispatch (e.g. branch chosen as
  "left-of-sqrt(c)" when it should be "right-of-sqrt(c)"
  produces a strictly smaller — therefore no longer an
  upper-bound — Λ value, making the integrand-lower-bound
  divide by a too-small denominator, etc.). Verify by
  re-running on a known-good baseline: the straddle branch
  alone reproduces sprint 099's behaviour byte-for-byte (set
  the dispatch to always take the straddle branch as a
  regression test).

- V64's evaluator score changes from `17823/50000` after
  the helper edit: `STATUS=BLOCKED` with the diff in
  `axioms_used` and the new score. Most likely cause: an
  accidental edit to V64's body or to `lemma.toml`'s oracle
  entry. The edit is intended to be Lean-side and
  lemma.toml-side byte-preserving.

- The `axioms_used` set diverges from V64's pre-sprint set:
  `STATUS=BLOCKED` with the set-difference. The edit must
  be audit-envelope-preserving by construction; if it is
  not, something has gone wrong (e.g. an accidental new
  free-floating axiom in a Lean file).

- The Phase 0 sanity script reports `m_1.rad` at
  `n_subdivisions = 2048` that is **not** at least one order
  of magnitude smaller than sprint 099's reading at the same
  `n_subdivisions`: `STATUS=BLOCKED` with the per-window
  radii table. Most likely cause: the dispatch is being
  taken as "straddle" on every subinterval (e.g. because
  `sqrt_c_arb` is being recomputed at insufficient precision
  and the rigorous comparisons return `False`/uncertain on
  every subinterval, falling back to the union branch).
  Verify by printing `(rho_hi <= sqrt_c_arb) is True` and
  `(sqrt_c_arb <= rho_lo) is True` for a sample subinterval;
  at least one should be `True` for subintervals not
  containing `sqrt(c)`.

- A `flint`/`arb` API surface used by the dispatch turns
  out to be unavailable in the current `flint` version
  pinned by `pyproject.toml`/`uv.lock`:
  `STATUS=BLOCKED_NEEDS_HUMAN` with the unavailable API.
  Note: this should not occur — the existing
  `_two_window_mass_paper_K_arb`, `_two_window_mass_paper_lambda_from_K_arb`,
  `arb.sqrt`, `arb.__le__`, `arb.union`, `(... is True)`
  semantics are all already exercised by sprint 099's
  helper.

- Trust expansion needed (the helper edit unexpectedly
  requires a new `Numerical_Library` library or a new
  `lemma.toml` entry): `STATUS=BLOCKED_NEEDS_HUMAN`. Note:
  this should not occur — the edit reuses existing helpers
  and existing arb arithmetic exclusively.
