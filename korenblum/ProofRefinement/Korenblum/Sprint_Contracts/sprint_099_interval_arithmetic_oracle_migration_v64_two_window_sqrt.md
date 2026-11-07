# Sprint 099: Interval-arithmetic re-discharge of `certify_two_window_mass_at_35646_sqrt` (V64's smallest oracle wrapper) — first oracle migration in the workspace

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V64.lean` (the V64 candidate at `c = 7129/20000 = 0.35645`, the smallest registered post-V52 mass oracle in `lemma.toml`; chosen explicitly by the human directive in Bulletin §C 5: *"Choose the smallest one first (`certify_two_window_mass_at_35646_sqrt`, V64) so the migration is bounded."*)
**Target file**: `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py` (existing wrapper `certify_two_window_mass_at_35646_sqrt` is re-discharged via rigorous interval enclosures using the `flint`/`arb` infrastructure already imported at the top of the file)
**Direction**: oracle-support (structural / credibility — score-neutral migration of one `mp.quad`-backed wrapper to a rigorous interval-arithmetic backend, establishing the first `mp.quad → arb` template for the remaining six oracle wrappers in the workspace; the live frontier remains V68 at `c = 71313/200000` after this sprint)

## Goal

Replace the `mp.quad`-based numerical-quadrature implementation of
`certify_two_window_mass_at_35646_sqrt` (currently lines ~1330–1435 of
`Numerical_Library/rigorous_scalar.py`) with a rigorous interval-arithmetic
implementation built on `flint.arb` (already imported at line 8 of the
same file), preserving the wrapper's external contract:

  - **Same name and signature**: `certify_two_window_mass_at_35646_sqrt() -> Fraction`.
  - **Same return discipline**: returns `Fraction(1, 1)` iff the certified
    rigorous lower bound on the joint mass at the pinned sqrt endpoints
    exceeds `1 + 10^(-30)`; raises `RuntimeError` otherwise.
  - **Same registration**: the existing `[[oracles]]` entry in
    `lemma.toml` (line 487 — `axiom = "h_two_window_mass_certified_at_35646_sqrt"`,
    `oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646_sqrt"`,
    `bound_field = "two_window_mass_lower"`) is **unchanged**.
  - **Same Lean axiom**: `Candidates/V64.lean`'s
    `axiom h_two_window_mass_certified_at_35646_sqrt` and its consumer
    site at line 316 (`exact h_two_window_mass_certified_at_35646_sqrt K`)
    are **byte-preserved**.

The mathematical content of the certified inequality is identical:

    mass_total
      :=  ∫_{ρ_start_1..ρ_meet} 2ρ / (H_2(c, ρ) · Λ(c, ρ)) dρ
        + ∫_{ρ_meet..ρ_stop_2}  2ρ / (H_1(c, ρ) · Λ(c, ρ)) dρ
      ≥  1 + 10^(-30)

at

    c            = 35646/100000  =  0.35646
    ρ_start_1    = c · sqrt(9/8)   (= ρ_start_1² = c²/τ(2),  τ(2) = 8/9)
    ρ_meet       = c · sqrt(4/3)   (= ρ_meet²    = c²/τ(1),  τ(1) = 3/4)
    ρ_stop_2     = 999999/1000000
    H_j(c, ρ)    = (j/(j+1)) · c^(2j+2) / ρ^(2j)
    Λ(c, ρ)      = paper-truncated Wang lambda (`_two_window_mass_paper_lambda`)

with the Phase 0 witness from `Scratch/sprint_083_sqrt_endpoint_witness.txt`
reporting margin `+1.9001e-3` at the same endpoints under the existing
`mp.quad` backend (i.e. ~27 orders of magnitude above the strict-margin
floor — the rigorous interval bound only needs to certify `≥ 1 + 10^(-30)`,
which has effectively unlimited slack).

The move uses neither equation `(15)` nor any new oracle. It is a
backend swap inside one wrapper function.

## Why

The Bulletin §C 5 (2026-05-05 directive, lines ~254–260) explicitly
nominates this exact wrapper for the first interval-arithmetic
migration:

> **Encourage interval-arithmetic re-discharge of one oracle.**
> If a sprint window is otherwise idle, replace one of the
> `mp.quad`-backed wrappers with an `mpmath.iv` (interval) or
> `arb` rigorous-quadrature backend. **Choose the smallest one
> first (`certify_two_window_mass_at_35646_sqrt`, V64) so the
> migration is bounded.** The output type stays `Fraction(1, 1)`;
> only the internals change. **This buys credibility, not score.**

Bulletin §B(3) frames the same point under the audit caveat:

> *Caveat: oracles use `mp.quad`, not interval arithmetic.* The
> wrappers compute integrals via mpmath's adaptive quadrature at
> 80 digits, not via certified interval enclosures. The +1e-4
> joint-mass margin is many orders of magnitude larger than any
> plausible quadrature error at this precision, and the strict
> `1 + 10^(-30)` floor enforces non-trivial slack, but **this is
> not a formal proof of the integral inequality** — it is a
> trusted high-precision computation. … **A future sprint should
> consider migrating one wrapper to interval arithmetic** (e.g.
> `mpmath.iv` or `arb`) as a credibility improvement, even if it
> does not move the score.

Sprint 098's "Forward implication" tail (Experience.md, recent
update) re-affirms the same priority:

> Migrate one oracle wrapper to interval arithmetic
> (Bulletin §C 5). Score-neutral credibility advance, larger
> scope than a one-file hoist; queue after the V63 trio
> hoist sequence (i.e. after this sprint).

The V63 hoist sequence is now complete (sprints 096 + 097 + 098;
V68 score and `axioms_used` set preserved byte-for-byte three
times in a row). Sprint 099 is the next natural step in the
queue.

The migration is preferred over the four other candidate sprint
shapes considered:

  (a) **Hoist `Candidates/V66/Branch1Integrability.lean` to
      `Proof/Branch1Integrability.lean`**. Smaller scope (113
      lines, 2 theorems) and **two consumers** (V67, V68). But
      sprints 097 and 098 both explicitly demoted this:
      *"window-architecture-specific … queue for a future
      sprint after a cross-architecture demand surfaces."*
      Currently only the eight/eleven-window architecture
      family imports it; no third consumer has emerged. The V63
      trio hoist set was the natural first-pass; Branch1 hoist
      is correctly sequenced *after* a future architecture
      demonstrates cross-architecture demand. **Demoted**:
      explicitly demoted twice in a row by the prior planners;
      no new consumer signal since the demotion.

  (b) **Wang Lemma 2 / Fourier orthogonality derived theorem
      in `Proof/`**. Long-standing brief target. No current
      consumer — would build infrastructure that nothing
      immediately uses, risking speculative work. Sprints 096,
      097, 098 all explicitly demoted this for the same reason.
      Best queued *after* a sprint that establishes the
      consuming Lean derivation chain (e.g. a Slack 2 or Slack 5
      successor that needs the boundary-L² expansion as a
      load-bearing step). **Demoted**: speculative
      infrastructure absent a consumer; the same demotion that
      held for the prior three sprints holds here.

  (c) **Trust-surface compaction: discharge `hH2_v6×` from
      `Section2Assumptions` as a Lean theorem** (Slack 4 /
      Bulletin §B(4)). Score-neutral but structurally valuable
      target. **But** AGENT_BRIEF lines 188-190 forbid
      `KorenblumPaper/` edits, and the Experience.md tail
      explicitly notes the math is *"not pinned tightly enough
      yet"* for a proposal_004 entry. **Demoted**: not runnable
      as a sprint without a prior trust-base expansion proposal
      whose math is not yet ready; the planner role's
      proposal-filing checklist is not satisfied.

  (d) **Phase 0 c-grid sweep at finer granularity above V68's
      0.356565**. Sprint 091's adaptive sweep already pinned the
      eleven-window architectural ceiling at `c ≈ 0.356565` to
      `~10^(-6)` precision, with explicit per-mode mass figures
      (mode10 ≈ 9.95e-7, total margin ≈ 1.005e-4). Bulletin §B
      states: *"the next admissible c (`356568/1000000`) costs
      you `~7e-5` — the design is exhausted."* A finer grid
      would re-confirm a known-saturated ceiling without upside.
      **Demoted**: redundant.

  (e) **New analytical attempt at Slack 1, 3, or 5** (the convex
      relaxation, outer-paper-kernel `Λ`, or `Σ⁺`-direct
      bounds). Sprints 093, 094, 095 ran the corresponding
      Phase 0 falsifier sequence and **all three slacks were
      eliminated** (per the recent context: *"closing bookend
      Phase 0 falsifier sequence — Slacks 1, 3, 5 all
      eliminated"*). A re-attempt at any of them in Lean
      without a fresh mathematical idea recapitulates a
      falsified hypothesis. **Demoted**: known-failed direction;
      a fresh structural insight is required before retrying.

The strongest objection to the chosen direction (interval-arithmetic
migration) is **"is this really bounded enough for one generator
session?"** The answer is yes for four reasons:

  1. **The `arb` infrastructure already exists in the same file.**
     `Numerical_Library/rigorous_scalar.py` already imports
     `from flint import arb, ctx, fmpq` (line 8) and already
     uses `arb` for the rigorous `k_upper_on_interval`,
     `lambda_upper_on_interval`, and `certify_box` paths
     consumed by the eq(15) family of oracles. The migration
     reuses the existing `_arb_exact`, `_arb_box`, `_pow_cached`,
     `_k_factor_arb`, `_prefactor_arb` helpers verbatim. No new
     library is imported; no new infrastructure is introduced.

  2. **The integrand has a closed-form structure** —
     `2ρ / (H_j(c, ρ) · Λ(c, ρ))` with `H_j(c, ρ) = (j/(j+1))
     · c^(2j+2) / ρ^(2j)` and `Λ(c, ρ)` a finite truncation of
     a known absolutely-convergent infinite product. A rigorous
     lower bound on a definite integral of this shape is the
     standard textbook problem: split each window into `N` equal
     subintervals, on each subinterval compute an `arb` lower
     enclosure of the integrand's minimum, and sum
     `width · min_lower` over all subintervals. **The arb
     library does the interval rounding correctly by
     construction** — the only choice is how many subintervals
     to use to clear the `1 + 10^(-30)` floor. The Phase 0
     witness's margin of `+1.9001e-3` (~27 orders of magnitude
     above the floor) gives effectively unlimited room.

  3. **Falsifiable by a single evaluator run.** After the
     migration:
       - `lake build ProofRefinement.Korenblum.Candidates.V64`
         must still succeed (no Lean change → trivially passes).
       - `Evaluator.py --file Candidates/V64.lean` must still
         return `pass: true`, `score: "7129/20000"`, and the
         oracle-check table must still record
         `axiom = h_two_window_mass_certified_at_35646_sqrt,
          oracle_bound = 1, declared = 1, ok = true`.
       - The migrated wrapper, called standalone, must complete
         within ~30 seconds (the existing `mp.quad` version
         takes ~3 seconds; a 10× slowdown for arb-based
         monotonic-bracket quadrature is expected and
         acceptable).
     If any of these fail, the migration has either introduced
     a bug or chosen too coarse an interval partition. Both are
     locally fixable.

  4. **Establishes the template for the remaining six oracle
     wrappers**: `certify_eq15_at_*` (5 wrappers: seed, 3560,
     3562, hp_3564, hp_35645) and `certify_seven_window_mass_at_*`
     (3 wrappers: 356562_sqrt, 356564_modeJ7, 356565_modeJ10).
     The eq(15) family is partially arb-equipped already
     (`k_upper_on_interval` is rigorous); the mass-window family
     is not. Sprint 099 establishes the mass-window template
     once on the smallest wrapper; later sprints can replicate
     the pattern for `certify_seven_window_mass_at_356562_sqrt`,
     `certify_seven_window_mass_at_356564_modeJ7`, and
     `certify_seven_window_mass_at_356565_modeJ10` (V66, V67,
     V68's oracles) without re-doing the algorithmic design.

After this sprint, **the oracle that V64 depends on for its
score-push past V52 is rigorously interval-certified**, and the
trust class of V64's joint-mass claim shifts from "trusted
high-precision `mp.quad` computation" to "verified rigorous
lower bound via `flint.arb` interval enclosures." This is a
genuine credibility improvement, exactly as Bulletin §B(3)
describes.

## Concrete edits expected

- **Edit** `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`:

  - **Add three new private helpers** above
    `certify_two_window_mass_at_35646_sqrt`:

      - `def _two_window_mass_paper_factor_arb(c_arb, rho_lo, rho_hi, n) -> arb:`
        Computes a rigorous **upper** bound for the `n`-th paper
        factor

            (1 + ρ² c^(2n+1)) (1 + c^(2n+3)/ρ²) (1 + c^(2n+2))²
            / [(1 + ρ² c^(2n)) (1 + c^(2n+2)/ρ²) (1 + c^(2n+1))²]

        on `ρ ∈ [rho_lo, rho_hi]` using arb interval arithmetic.
        Both `c_arb : arb` and `rho_lo, rho_hi : arb` are
        passed; the result is an `arb` enclosure of the
        max-over-ρ. (Equivalently, evaluate the rational
        function with `rho_arb = arb` interval covering
        `[rho_lo, rho_hi]` and rely on arb's automatic
        worst-case rounding.) Uses the existing `_pow_cached`
        for `c` powers.

      - `def _two_window_mass_paper_lambda_arb(c_arb, rho_lo, rho_hi, n_trunc) -> arb:`
        Computes a rigorous upper bound for `Λ(c, ρ) =
        2ρ (1 + c/ρ²) · ∏_{n=0}^{n_trunc-1} factor_n` on
        `[rho_lo, rho_hi]` by multiplying the `n_trunc` factor
        upper bounds and the `2ρ (1 + c/ρ²)` upper bound. Then
        feed `K = paper_lambda_truncated` through the same
        `1 + (1/2)(sqrt((1+3K²)/(1-K²)) - 1)` transform via
        arb arithmetic (compare `lambda_upper_on_interval`'s
        existing pattern at lines ~248–266). Returns an `arb`
        upper bound on `Λ` over the ρ-subinterval.

      - `def _two_window_mass_window_lower_arb(c_arb, j, rho_start, rho_stop, n_trunc, n_subdivisions) -> arb:`
        Computes a rigorous **lower** bound for the integral

            ∫_{rho_start..rho_stop} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ

        where `H_j(c, ρ) = (j/(j+1)) c^(2j+2) / ρ^(2j)`. Splits
        `[rho_start, rho_stop]` into `n_subdivisions` equal
        sub-intervals; on each `[ρ_lo, ρ_hi]` sub-interval,
        computes:
          - upper bound for `Λ(c, ρ)` on the sub-interval via
            `_two_window_mass_paper_lambda_arb`,
          - upper bound for `H_j(c, ρ) = (j/(j+1)) c^(2j+2)/ρ^(2j)`
            on the sub-interval (max at `ρ = ρ_lo` since
            `H_j` is decreasing in `ρ` for `j ≥ 1`),
          - lower bound for `2ρ` (i.e. `2 · ρ_lo`),
          - lower bound on integrand: `(2 · ρ_lo) / (H_j_upper
            · Λ_upper)`,
          - sub-interval contribution lower bound:
            `(ρ_hi - ρ_lo) · integrand_lower`.
        Returns the `arb` sum of all sub-interval contributions
        — a rigorous lower bound on the joint integral.

  - **Replace the body of `certify_two_window_mass_at_35646_sqrt`**:
    keep the docstring (updated to reflect the arb backend),
    keep the structural ordering checks at the top, but replace
    the `with mp.workdps(int(dps)): ...` block (lines ~1397–1434)
    with:

      - Construct `c_arb = _arb_exact(Fraction(35646, 100000))`,
        `rt2_arb = _arb_exact(Fraction(999999, 1000000))`.
      - Construct sqrt-pinned arb endpoints:
          `rho_start_1_arb = c_arb * arb(fmpq(9, 8)).sqrt()` and
          `rho_meet_arb = c_arb * arb(fmpq(4, 3)).sqrt()`. (arb's
          `.sqrt()` returns a rigorous interval enclosure of
          the irrational square root.)
      - Verify ordering using `arb.__lt__` / `arb.__le__` (these
        return `bool` only when the strict comparison holds
        rigorously, i.e. when the intervals do not overlap;
        raise `RuntimeError` if any ordering check is
        rigorously-uncertain). At this c, the orderings are
        well-separated (gap `> 10^(-3)` between consecutive
        endpoints), so rigor is trivially achieved.
      - Pick `n_subdivisions = 256` and `n_trunc = 200` (the
        existing wrapper's `n_trunc`; the new `n_subdivisions`
        knob is the migration's added parameter — 256 is
        chosen so each sub-interval is `~10^(-4)` wide on the
        `[0.378, 0.412]` window, giving integrand-resolution
        well within the `10^(-30)` margin floor; if 256 turns
        out to be too coarse to clear the floor the generator
        increases it iteratively in powers of 2 up to a cap of
        `2^14 = 16384`).
      - Compute
          `m1_lower = _two_window_mass_window_lower_arb(
                        c_arb, 2, rho_start_1_arb, rho_meet_arb,
                        n_trunc=200, n_subdivisions=256)`
          `m2_lower = _two_window_mass_window_lower_arb(
                        c_arb, 1, rho_meet_arb, rt2_arb,
                        n_trunc=200, n_subdivisions=256)`
          `total_lower = m1_lower + m2_lower`.
      - Test `total_lower > arb(1) + arb(fmpq(1, 10))**30`. The
        `arb.__gt__` semantics: returns `True` only if the
        rigorous lower endpoint of the LHS arb interval
        strictly exceeds the upper endpoint of the RHS arb
        interval. If `False`, raise `RuntimeError` with a
        diagnostic identical in shape to the existing version
        but reporting the arb interval (e.g.
        `f"total_lower = {total_lower}"`) rather than the
        scalar mp value.
      - Return `Fraction(1, 1)` on success.

  - **No edits** to any other function in `rigorous_scalar.py`
    (the `_two_window_mass_paper_factor`, `_two_window_mass_paper_lambda`,
    `_two_window_mass_term_j`, `_two_window_mass_window`,
    `certify_two_window_mass`, `certify_two_window_mass_at_35646`,
    or any of the seven-window mass functions are all left
    byte-preserved). The `mp.quad`-based code is intentionally
    kept available for the rational-endpoint sibling and for
    future use; only the sqrt-endpoint shim is migrated.

- **No edits** to:
  - `lemma.toml`: the `[[oracles]]` entry at line 487 already
    points to `rigorous_scalar.certify_two_window_mass_at_35646_sqrt`;
    that line is byte-preserved.
  - `Candidates/V64.lean`: the candidate-side
    `axiom h_two_window_mass_certified_at_35646_sqrt` and its
    use site at line 316 are byte-preserved.
  - `KorenblumPaper/`: read-only (forbidden).
  - Any other `Candidates/V*.lean`: V64 is the only consumer
    of this oracle; V65 has its own oracle
    (`h_two_window_mass_certified_at_35646` — the rational-endpoint
    sibling, which is **not** migrated by this sprint), and
    V66/V67/V68 use the seven/eight/eleven-window oracles
    (also not migrated).
  - `Numerical_Library/types.py`, `Numerical_Library/numerical_audit.py`:
    no schema changes.

- **Add** a Phase 0 sanity script at
  `Scratch/sprint_099_arb_two_window_mass_witness.py`: a
  standalone python script that calls the migrated wrapper
  once and prints the certified margin (i.e. the arb
  enclosure of `total - 1`). This is not consumed by the
  evaluator; it serves as a human-readable witness that the
  arb backend reproduces sprint 083's `+1.9001e-3` margin to
  within ~10 digits, providing a sanity-check artifact in
  parallel to `Scratch/sprint_083_sqrt_endpoint_witness.txt`.

- **Re-evaluate V64** by running the candidate evaluator on
  `Candidates/V64.lean` and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V64`
    succeeds (Lean side is byte-preserved; trivially passes).
  - `Evaluator.py --file Candidates/V64.lean` succeeds with
    `pass: true` and `score: "7129/20000"` (= `0.35645`,
    unchanged from V64's pre-migration score).
  - The post-migration V64 evaluator log entry's `axioms_used`
    set is **identical** (set-theoretically) to the pre-migration
    log entry's `axioms_used` set — exactly the six entries
    `propext`, `Classical.choice`, `Quot.sound`,
    `ProofRefinement.Korenblum.Candidates.V64.h_two_window_mass_certified_at_35646_sqrt`,
    `ProofRefinement.Korenblum.Candidates.V64.hH2_v64`,
    `ProofRefinement.Korenblum.Candidates.V64.hCircleGapInt_v64`.
  - The `oracle_checks` table in the log entry records the
    same `axiom = h_two_window_mass_certified_at_35646_sqrt,
    bound_field = two_window_mass_lower, oracle_bound = 1,
    declared = 1, ok = true`. (The wrapper still returns
    `Fraction(1, 1)`; the evaluator's downstream check is
    unchanged.)

- **Re-evaluate V68** by running the candidate evaluator on
  `Candidates/V68.lean` and confirming `pass: true`,
  `score: "71313/200000"`, `axioms_used` set unchanged.
  (V68 does not depend on the migrated wrapper, but a
  second-level falsifier on the live frontier is cheap and
  catches any unintended side effect of the rigorous_scalar.py
  edit.)

- `Experience.md`: append a "Sprint 099 — arb-based migration
  of `certify_two_window_mass_at_35646_sqrt` (first oracle
  migration in the workspace)" subsection summarizing:
    - the wrapper migrated,
    - the arb infrastructure reused (existing `_arb_exact`,
      `_pow_cached`, etc.),
    - the algorithmic shape of `_two_window_mass_window_lower_arb`
      (subdivision-based rigorous integral lower bound, with
      `n_subdivisions = 256` chosen to clear the `10^(-30)`
      margin floor),
    - the certified arb-margin reproduced from sprint 083
      (e.g. arb-enclosure of margin to within ~10 decimal
      digits of `+1.9001e-3`),
    - the V64 re-evaluation result (`pass: true`,
      `score: 7129/20000`, `axioms_used` unchanged),
    - the V68 re-evaluation result (`pass: true`,
      `score: 71313/200000`, `axioms_used` unchanged),
    - the forward implication: the same template
      (`_two_window_mass_paper_factor_arb`,
      `_two_window_mass_paper_lambda_arb`,
      `_two_window_mass_window_lower_arb`) can be reused to
      migrate the other six oracle wrappers in subsequent
      sprints; `certify_seven_window_mass_at_356562_sqrt`
      (V66's oracle) is the natural next candidate after this
      sprint.

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_099 PASS|FAIL: …`).

No edits to:
- `KorenblumPaper/` (read-only).
- `Proposals/` (no proposal filed; the migration is a
  backend swap, not a trust-base expansion — the wrapper's
  external contract and the oracle's audit envelope are
  preserved conjunct-for-conjunct).
- The mathematical content of `Candidates/V64.lean` or
  `Candidates/V65–V68.lean`.
- Any candidate-side `axiom` declaration.
- The `[seed_axioms]`, `[[oracles]]`, `[import_policy]`, or
  `[workspace_import_policy]` blocks of `lemma.toml` (the
  oracle's `oracle_fn` line continues to point at the same
  wrapper name; no entry is added or removed).
- `Proof/Summability.lean` (sprint 098), `Proof/Integrability.lean`
  (sprint 097), `Proof/DiskInnerSeriesBridge.lean`
  (sprint 096), `Proof/Reduction.lean`, `Proof/Main.lean`,
  `Proof/CandidateContract.lean` (the entire `Proof/` tree
  is unchanged).

## Acceptance criteria

1. The migrated `certify_two_window_mass_at_35646_sqrt`, called
   standalone (e.g.
   `python -c "from Numerical_Library.rigorous_scalar import
   certify_two_window_mass_at_35646_sqrt; print(certify_two_window_mass_at_35646_sqrt())"`),
   returns `Fraction(1, 1)` and does not raise.

2. The migrated wrapper internally uses **only** `flint.arb`
   primitives (and the existing `arb`-tier helpers
   `_arb_exact`, `_pow_cached`, `_k_factor_arb`,
   `_prefactor_arb`, `_arb_box`, `ctx.workdps`, `arb.sqrt`,
   etc.) for the rigorous-bound computation. No `mp.quad`
   call remains in this wrapper's body. (The migration may
   internally call `mp.workdps` only as a context manager
   if `arb`-internal precision tuning requires it; the
   primary computation uses `arb` interval arithmetic.)

3. `lake build ProofRefinement.Korenblum.Candidates.V64`
   succeeds.

4. `lake build ProofRefinement.Korenblum.Candidates.V68`
   succeeds.

5. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V64.lean` succeeds with
   `pass: true` and `score: "7129/20000"` (= `0.35645`,
   unchanged from V64's pre-migration score).

6. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (= `0.356565`,
   unchanged from V68's pre-migration score).

7. The post-migration V64 evaluator log entry's `axioms_used`
   set is **identical** (set-theoretically, comparing the
   `name` field of each entry) to V64's pre-migration log
   entry's `axioms_used` set: exactly the six entries listed
   in "Concrete edits expected" above. No new axioms
   introduced. No old axioms removed.

8. The post-migration V64 evaluator log entry's `oracle_checks`
   table contains exactly one entry with
   `axiom = "h_two_window_mass_certified_at_35646_sqrt"`,
   `bound_field = "two_window_mass_lower"`, `oracle_bound = "1"`,
   `declared = "1"`, `ok = true`. (Unchanged from pre-migration.)

9. The Phase 0 sanity script
   `Scratch/sprint_099_arb_two_window_mass_witness.py`
   prints a certified arb-enclosure of `total - 1` whose
   lower endpoint exceeds `10^(-30)` (i.e. the strict-margin
   floor) and whose midpoint agrees with sprint 083's
   `+1.9001e-3` to within `10^(-6)` (~6 decimal digits — far
   tighter than required, just a sanity-of-implementation
   check).

10. The migrated wrapper completes within **~60 seconds** on
    a single invocation. (Existing `mp.quad` version: ~3
    seconds; arb-based subdivision quadrature with
    `n_subdivisions ≤ 16384` is expected to take 10–30s; a
    60s ceiling leaves headroom for a generator that
    iteratively raises `n_subdivisions` to clear the margin
    floor.)

11. `Experience.md` and `Bulletin.md` each gain one row per
    the standard pattern.

The sprint is **PASS** if all 11 criteria are met. The sprint is
**FAIL** if V64 or V68's evaluator score changes, the
`axioms_used` set diverges, the migrated wrapper raises
`RuntimeError` (i.e. the arb-rigorous lower bound fails to
clear the `10^(-30)` floor — almost certainly indicating
either a bug in the migration or `n_subdivisions` set too
coarse), or the wrapper exceeds the 60-second time ceiling.

## Out of scope

- Migrate any other oracle wrapper. This sprint scope is
  **exactly one wrapper** —
  `certify_two_window_mass_at_35646_sqrt`. The other six
  candidates for migration (`certify_eq15_at_seed`,
  `certify_eq15_at_3560`, `certify_eq15_at_3562`,
  `certify_eq15_at_hp_3564`, `certify_eq15_at_hp_35645`,
  `certify_two_window_mass_at_35646` (rational sibling),
  `certify_seven_window_mass_at_356562_sqrt`,
  `certify_seven_window_mass_at_356564_modeJ7`,
  `certify_seven_window_mass_at_356565_modeJ10`) are queued
  for follow-up sprints once this sprint's template is
  validated. The Bulletin §C 5 directive *"Choose the
  smallest one first"* is unambiguous.

- Edit `Candidates/V64.lean` or any other Lean file. The
  migration is a Python-side internal change to one wrapper;
  the candidate-side `axiom` declaration and its usage are
  byte-preserved.

- Edit the `[[oracles]]` registration in `lemma.toml`. The
  `oracle_fn` continues to point at the same wrapper name;
  the candidate axiom name is unchanged; the bound field is
  unchanged.

- Add or remove free axioms. The migration preserves the
  trust surface conjunct-for-conjunct.

- File a `Proposals/` entry. The migration is a Python-side
  backend swap inside one wrapper that already exists and
  is already registered. No trust-base expansion is involved
  — the wrapper's external contract (zero-arg shim returning
  `Fraction(1, 1)` iff the certified mass clears the
  `10^(-30)` floor) is preserved byte-for-byte; only the
  algorithmic backend (`mp.quad` → `arb`) changes. Per
  AGENT_BRIEF lines 80-86: *"oracle-shaped additions can be
  done inline as long as the sprint contract explicitly asks
  for the new `Numerical_Library` function, the matching
  `lemma.toml` entry, and the Lean-facing axiom/use site"* —
  this is a *modification* of an existing oracle's backend,
  not an addition, and follows the same inline pattern.

- Change the final theorem statement of any candidate.

- Hoist `Candidates/V66/Branch1Integrability.lean` to
  `Proof/`. Currently demoted as architecture-specific (only
  V67/V68 import it, both in the same eight/eleven-window
  family). Queue for a future sprint after a third
  cross-architecture consumer surfaces.

- Hoist V64's `TauWindowEndpoints.lean`, V66's
  `SevenWindowEndpoints.lean`, V67's
  `EightWindowEndpoints.lean`, or V68's
  `ElevenWindowEndpoints.lean`. These are window-architecture
  specific and not reused as broadly as the V63 trio.

- Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`.
  No current consumer; queueing it speculatively before
  establishing a Lean derivation chain that needs it would
  risk infrastructure-speculation work. Best queued *after*
  a sprint that explicitly needs the boundary-L² expansion
  as a load-bearing step.

- Run any Phase 0 numerical falsifier sweep beyond the
  sanity-check witness script
  (`Scratch/sprint_099_arb_two_window_mass_witness.py`). The
  migration is structural; the sanity script exists only to
  produce a human-readable margin reading, not to drive any
  decision.

- Push past V68's `c = 71313/200000`. The score-push surface
  at the existing trust surface remains exhausted (Slacks
  1/3/5 falsified by sprints 093/094/095; Slack 2 settled
  by sprint 077; Slack 4 needs a trust expansion). After
  this sprint, the live frontier remains V68 at
  `71313/200000`.

- Discharge `hH2_v6×` or `hCircleGapInt_v6×` from
  `Section2Assumptions` (Slack 4 / Bulletin §B(4)). This
  requires either a `KorenblumPaper/` edit (forbidden by
  AGENT_BRIEF lines 188-190) or a trust-base expansion
  proposal whose math is not pinned tightly enough yet —
  out of scope for an oracle-migration sprint.

## Time budget

≤ 60 minutes runtime:
  - Migrated-wrapper standalone invocation: ~30s (one-shot
    arb computation with `n_subdivisions = 256`).
  - V64 evaluator: ~3 minutes (typecheck + axiom scan +
    oracle invocation; the migrated wrapper now runs ~10×
    longer than the `mp.quad` predecessor, but well within
    the evaluator's wall-clock budget).
  - V68 evaluator: ~3 minutes (V68 does not invoke the
    migrated wrapper, so its timing is unchanged at
    ~2.5 minutes from sprint 098's measurement).
  - Phase 0 sanity script: ~30s.

≤ 1 generator session (~2.5–3.5 hours including the three
new private helper functions in `rigorous_scalar.py`
(~150 lines of arb arithmetic), the wrapper-body rewrite
(~50 lines), the Phase 0 sanity script (~30 lines), the
two evaluator runs (~6 minutes total wall-clock), and the
witness updates to `Experience.md` and `Bulletin.md`).

## Stop conditions

- All 11 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- The arb-rigorous lower bound on `total_lower` does not
  clear `1 + 10^(-30)` even at the maximum
  `n_subdivisions = 16384`: `STATUS=BLOCKED` with the
  arb-enclosure of the failing margin. Most likely cause:
  either (i) a bug in `_two_window_mass_paper_lambda_arb`
  or `_two_window_mass_window_lower_arb` (over-pessimistic
  upper bound on `Λ`, e.g. failing to use `c_arb` in
  exact-rational form); or (ii) the truncation `n_trunc =
  200` is too coarse to give a tight enough `Λ`-upper-bound
  at the canonical sqrt endpoints (raise `n_trunc` to 400
  or 800). Both are locally fixable; the sprint 083 witness
  recorded margin `+1.9001e-3` at `n_trunc = 200` under
  `mp.quad`, so a tightness gap of >27 orders of magnitude
  is the available headroom.

- The migrated wrapper exceeds the 60-second time ceiling:
  `STATUS=BLOCKED` with the wall-clock and the
  `n_subdivisions` value used. Resolution: lower
  `n_subdivisions` (the `+1.9e-3` margin allows extreme
  coarsening — even `n_subdivisions = 16` should clear the
  `10^(-30)` floor by a factor of ~`10^25`).

- V64's evaluator score changes from `7129/20000` after the
  migration: `STATUS=BLOCKED` with the diff in `axioms_used`
  and the new score. Most likely cause: an accidental edit
  to V64's body or to `lemma.toml`'s oracle entry. The
  migration is intended to be Lean-side and lemma.toml-side
  byte-preserving.

- The `axioms_used` set diverges from V64's pre-migration
  set: `STATUS=BLOCKED` with the set-difference. The
  migration must be audit-envelope-preserving by
  construction; if it is not, something has gone wrong
  (e.g. an accidental new free-floating axiom in a Lean
  file).

- The `oracle_checks` table reports `ok = false` for
  `h_two_window_mass_certified_at_35646_sqrt`:
  `STATUS=BLOCKED` with the wrapper's `RuntimeError`
  message. Most likely cause: the migrated wrapper raised
  `RuntimeError` because the arb-rigorous bound failed to
  clear the floor — the same diagnosis as the first stop
  condition above.

- A `flint`/`arb` API surface used by the migration turns
  out to be unavailable in the current `flint` version
  pinned by `pyproject.toml`/`uv.lock`:
  `STATUS=BLOCKED_NEEDS_HUMAN` with the unavailable API.
  Note: this should not occur — the existing
  `k_upper_on_interval` and `lambda_upper_on_interval` paths
  in `rigorous_scalar.py` already exercise `arb`,
  `arb.__mul__`, `arb.__add__`, `arb.sqrt`, `fmpq`,
  `arb.__lt__`, `ctx.workdps` — the migration uses no API
  surface beyond what is already exercised.

- Trust expansion needed (the migration unexpectedly
  requires a new `Numerical_Library` library or a new
  `lemma.toml` entry): `STATUS=BLOCKED_NEEDS_HUMAN`. Note:
  this should not occur — `flint.arb` is already imported
  and the wrapper name / oracle entry / candidate axiom are
  all byte-preserved.
