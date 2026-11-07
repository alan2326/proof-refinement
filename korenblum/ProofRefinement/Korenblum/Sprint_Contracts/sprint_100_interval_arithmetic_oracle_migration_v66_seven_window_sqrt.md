# Sprint 100: Interval-arithmetic re-discharge of `certify_seven_window_mass_at_356562_sqrt` (V66's oracle) — second `mp.quad → arb` migration, extending sprint 099's template to the seven-window architecture

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V66.lean` (the V66 candidate at `c = 178281/500000 = 356562/1000000`, the smallest un-migrated mass-window wrapper after sprint 099 cleared V64's two-window sqrt sibling; chosen explicitly per sprint 099's Forward implication tail in Experience.md and Bulletin §C5's repeated "smallest first" directive).
**Target file**: `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py` — the existing wrapper `certify_seven_window_mass_at_356562_sqrt` (lines ~1770–1886) is re-discharged via rigorous `flint.arb` interval enclosures; the existing `_branch1_window_mass` mp.quad helper is left byte-preserved (it remains consumed by the V67/V68 wrappers that are *not* migrated by this sprint).
**Direction**: oracle-support (structural / credibility — score-neutral migration of the second `mp.quad`-backed wrapper to a rigorous interval-arithmetic backend; the live frontier remains V68 at `c = 71313/200000` after this sprint).

## Goal

Replace the `mp.quad`-based numerical-quadrature implementation of
`certify_seven_window_mass_at_356562_sqrt` (currently lines ~1770–1886
of `Numerical_Library/rigorous_scalar.py`) with a rigorous interval-
arithmetic implementation built on `flint.arb`, **reusing sprint 099's
three already-shipped helpers verbatim** (`_two_window_mass_paper_K_arb`,
`_two_window_mass_paper_lambda_from_K_arb`, `_two_window_mass_paper_lambda_arb`,
`_two_window_mass_window_lower_arb`) and adding **one new helper**
`_branch1_window_mass_lower_arb` for the Branch.one integrand
`12 ρ³ (ρ² − c²) / (c⁶ · Λ(c, ρ))`. The wrapper's external contract is
preserved conjunct-for-conjunct:

  - **Same name and signature**: `certify_seven_window_mass_at_356562_sqrt() -> Fraction`.
  - **Same return discipline**: returns `Fraction(1, 1)` iff the certified
    rigorous lower bound on the joint mass at the seven sqrt-pinned and
    rational-pinned endpoints exceeds `1 + 10^(-30)`; raises `RuntimeError`
    otherwise.
  - **Same registration**: the existing `[[oracles]]` entry in
    `lemma.toml` (lines 537–540 — `axiom = "h_seven_window_mass_certified_at_356562_sqrt"`,
    `bound_field = "seven_window_mass_lower"`,
    `oracle_fn = "rigorous_scalar.certify_seven_window_mass_at_356562_sqrt"`)
    is **byte-preserved**.
  - **Same Lean axiom**: `Candidates/V66.lean`'s
    `axiom h_seven_window_mass_certified_at_356562_sqrt` and its
    consumer site at line 327 (`exact h_seven_window_mass_certified_at_356562_sqrt K`)
    are **byte-preserved**.

The mathematical content of the certified inequality is identical:

    mass_total
      :=  ∫_{c·(1+1e-6)..c·sqrt(50/49)}  12 ρ³ (ρ² − c²) / (c⁶ Λ(c, ρ)) dρ   (boxA1)
        + ∫_{c·sqrt(50/49)..c·sqrt(36/35)} 12 ρ³ (ρ² − c²) / (c⁶ Λ(c, ρ)) dρ (boxA2)
        + ∫_{c·sqrt(36/35)..c·sqrt(25/24)} 12 ρ³ (ρ² − c²) / (c⁶ Λ(c, ρ)) dρ (boxA3)
        + ∫_{c·sqrt(25/24)..c·sqrt(16/15)} 2ρ / (H_4(c, ρ) · Λ(c, ρ)) dρ      (mode4)
        + ∫_{c·sqrt(16/15)..c·sqrt(9/8)}   2ρ / (H_3(c, ρ) · Λ(c, ρ)) dρ      (mode3)
        + ∫_{c·sqrt(9/8)..c·sqrt(4/3)}     2ρ / (H_2(c, ρ) · Λ(c, ρ)) dρ      (mode2)
        + ∫_{c·sqrt(4/3)..999999/1000000}  2ρ / (H_1(c, ρ) · Λ(c, ρ)) dρ      (mode1)
      ≥  1 + 10^(-30)

at

    c            = 356562/1000000  =  178281/500000
    delta_lo     = 1e-6
    H_j(c, ρ)    = (j/(j+1)) · c^(2j+2) / ρ^(2j)
    Λ(c, ρ)      = paper-truncated Wang lambda (`_two_window_mass_paper_lambda`)

with the Phase 0 witness from
`Scratch/sprint_087_v38_seven_window_mass_sweep.txt` reporting
full-envelope margin `+1.19998e-4` at `(dps=80, n_trunc=300)` — about
~26 orders of magnitude above the strict-margin floor `10^(-30)`.

The move uses neither equation `(15)` nor any new oracle. It is a
backend swap inside one wrapper function.

## Why

The Bulletin §C5 directive (2026-05-05 audit) and sprint 099's Forward
implication tail explicitly nominate this exact wrapper as the natural
next migration after V64:

> Sprint 099 (Experience.md tail): *"the same template
> (`_two_window_mass_paper_factor_arb`, `_two_window_mass_paper_lambda_arb`,
> `_two_window_mass_window_lower_arb`, plus the iterative-power-of-2
> n_subdivisions doubling pattern) can be reused to migrate the other
> six `mp.quad`-backed oracle wrappers: ... `certify_seven_window_mass_at_356562_sqrt`
> (V66's oracle, **the natural next candidate** — the smallest of the
> un-migrated mass-window wrappers)."*

> Bulletin §B(3): *"oracles use mp.quad, not interval arithmetic ...
> A future sprint should consider migrating one wrapper to interval
> arithmetic (e.g. mpmath.iv or arb) as a credibility improvement,
> even if it does not move the score."*

> Bulletin §C5: *"Encourage interval-arithmetic re-discharge of one
> oracle. ... The output type stays Fraction(1, 1); only the internals
> change. This buys credibility, not score."*

Sprint 099 successfully shipped the first `mp.quad → arb` migration
(V64's two-window sqrt wrapper, the smallest registered mass oracle).
After this sprint, the trust class of V66's joint-mass claim shifts
from "trusted high-precision `mp.quad` computation" to "verified
rigorous lower bound via `flint.arb` interval enclosures" — fully
discharging the Bulletin §B(3) caveat for V66's c-push past V64.

The migration is preferred over the four other candidate sprint
shapes considered:

  (a) **Migrate `certify_two_window_mass_at_35646`** (V65's rational
      sibling — same two-window structure as V64's just with rational
      endpoints). Even simpler than V66's. **But**: V65 is V62-tied
      (same c-value as V62, was a sibling specializer in the tied
      crossover gauntlet); the credibility upgrade for V65 is largely
      *redundant* now that V64's sqrt sibling has been migrated, since
      V65's score is ≤ V64's and V65 is not on the live frontier.
      The recent context explicitly flags this as "(V65 is V62-tied
      and was a sibling specializer; might be redundant)". **Demoted**:
      no live-frontier credibility benefit; V66 sits strictly above
      V65 on the c-ladder and is the natural progression.

  (b) **Hoist `Candidates/V66/Branch1Integrability.lean` to
      `Proof/Branch1Integrability.lean`**. Sprints 097, 098, and 099
      all explicitly demoted this: *"window-architecture-specific —
      queue for a future sprint after a cross-architecture demand
      surfaces."* Currently only V67 and V68 import it, both in the
      same eight/eleven-window family; no third cross-architecture
      consumer has emerged. **Demoted three sprints in a row** with
      no new consumer signal.

  (c) **Wang Lemma 2 / Fourier orthogonality derived theorem in
      `Proof/`**. Long-standing brief target. Sprints 096–099 all
      demoted this: speculative infrastructure absent a consumer;
      best queued *after* a sprint that establishes the consuming
      Lean derivation chain. The score-push surface is currently
      exhausted (Slacks 1/3/5 falsified by sprints 093/094/095;
      Slack 2 effectively settled by sprint 077; Slack 4 requires
      a `KorenblumPaper/` edit forbidden by AGENT_BRIEF), so no
      consuming derivation chain is currently active. **Demoted**:
      speculative infrastructure absent a consumer; the same
      demotion that held for the prior four sprints holds here.

  (d) **Phase 0 c-grid sweep at finer granularity above V68's 0.356565**.
      Sprint 091's adaptive sweep already pinned the eleven-window
      architectural ceiling at `c ≈ 0.356565` to `~10^(-6)` precision.
      Bulletin §B states *"the next admissible c (`356568/1000000`)
      costs you `~7e-5` — the design is exhausted."* A finer grid
      would re-confirm a known-saturated ceiling without upside.
      **Demoted**: redundant numerical push.

  (e) **Re-attempt Slack 1, 3, or 5 in Lean.** Sprints 093/094/095
      ran the corresponding Phase 0 falsifier sequence and **all
      three slacks were eliminated** (closing-bookend Phase 0
      falsifier sequence). A re-attempt without a fresh mathematical
      idea recapitulates a falsified hypothesis. **Demoted**:
      known-failed direction.

The strongest objection to the chosen direction (interval-arithmetic
migration of V66's seven-window wrapper) is **"is the rigorous
lower-bound margin tight enough to clear the floor?"** The answer is
yes, with substantial margin, for four reasons:

  1. **Sprint 087's witness margin is `+1.19998e-4`** at the chosen c,
     ~26 orders of magnitude above the strict-margin floor `10^(-30)`.
     Sprint 099's left-Riemann lower-bound algorithm trails the
     centered estimate by O(width^1) per window. Even if the rigorous
     lower bound is a factor of ~10× looser than the centered
     estimate (worst-case O(c·width) for slow-varying integrands),
     the certified margin remains in the `10^(-5)` range — still
     ~25 orders of magnitude over the floor.

  2. **Sprint 099 demonstrated the algorithm clears the floor with
     ample headroom**: at `n_subdivisions = 2048` on V64's two-window
     wrapper, the rigorous lower-endpoint margin was `+5.0556e-4`
     (vs. centered estimate `+1.9001e-3`, i.e. ~3.7× tightness loss).
     Applied to V66 with centered margin `+1.19998e-4`, the same
     ~3.7× loss yields rigorous margin `~3.2e-5`, still ~25 orders of
     magnitude over the floor. The contract's `n_subdivisions` cap
     of `2^14 = 16384` provides further refinement headroom if the
     initial subdivision is too coarse.

  3. **Falsifiable by a single evaluator run.** After the migration:
       - `lake build ProofRefinement.Korenblum.Candidates.V66` must
         still succeed (Lean side is byte-preserved → trivially passes).
       - `Evaluator.py --file Candidates/V66.lean` must still return
         `pass: true`, `score: "178281/500000"` (= `0.356562`), and
         the oracle-check table must still record
         `axiom = h_seven_window_mass_certified_at_356562_sqrt,
          oracle_bound = 1, declared = 1, ok = true`.
       - V68's evaluator must still pass with `score: "71313/200000"`
         unchanged (V68 does not consume V66's oracle, but a
         second-level falsifier on the live frontier is cheap and
         catches any unintended side effect of the rigorous_scalar.py
         edit).
       - The migrated wrapper, called standalone, must complete
         within ~120 seconds (sprint 099's wrapper took ~8 s; this
         one has 7 windows vs. 2, so ~30–60 s is a reasonable
         expected wall-clock).
     If any of these fail, the migration has either introduced a
     bug or chosen too coarse an interval partition. Both are
     locally fixable.

  4. **Directly establishes the template for the remaining four
     mass-window wrappers**: `certify_seven_window_mass_at_356564_modeJ7`
     (V67's eight-window oracle) and `certify_seven_window_mass_at_356565_modeJ10`
     (V68's eleven-window oracle), plus the `certify_eq15_at_*`
     family (already partially arb-equipped via `k_upper_on_interval`
     and `lambda_upper_on_interval`). The new helper
     `_branch1_window_mass_lower_arb` is the only architectural
     extension needed; once shipped, V67 and V68's wrappers reuse
     this helper plus sprint 099's `_two_window_mass_window_lower_arb`
     in proportion to their kind dispatch (1 Branch.one + 7 modeJ
     for V67; 0 Branch.one + 11 modeJ — no, actually V68 uses
     11 modeJ + box0; check — see V68's oracle for exact dispatch
     count).

After this sprint:
  - V64's joint-mass claim (sprint 099) is rigorous-arb-certified.
  - V66's joint-mass claim (this sprint) is rigorous-arb-certified.
  - Five oracle wrappers remain on `mp.quad`:
    `certify_eq15_at_seed/3560/3562/hp_3564/hp_35645` (eq15 family,
    partially arb-equipped already via `k_upper_on_interval`;
    can be migrated in subsequent sprints by composing existing
    arb helpers without introducing new algorithmic shapes),
    `certify_two_window_mass_at_35646` (V65's rational sibling,
    redundant per (a) above),
    `certify_seven_window_mass_at_356564_modeJ7` (V67),
    `certify_seven_window_mass_at_356565_modeJ10` (V68).
  - The live frontier remains V68 at `71313/200000`; this sprint
    is **score-neutral**, exactly as Bulletin §C5 intends.

## Concrete edits expected

- **Edit** `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`:

  - **Add one new private helper** `_branch1_window_mass_lower_arb`
    immediately before `certify_seven_window_mass_at_356562_sqrt`
    (i.e. between the existing `_branch1_window_mass` mp.quad helper
    and the wrapper). The helper's algorithmic shape mirrors
    sprint 099's `_two_window_mass_window_lower_arb`:

        def _branch1_window_mass_lower_arb(
            c_arb,
            c_pows,
            rho_start,
            rho_stop,
            sqrt_c_arb,
            n_trunc: int,
            n_subdivisions: int,
        ) -> arb:
            """
            Sprint 100 helper: rigorous arb lower bound on

                ∫_{rho_start..rho_stop} 12 ρ³ (ρ² - c²) / (c⁶ · Λ(c, ρ)) dρ

            via subdivision-based left-Riemann lower sum. On each
            sub-interval [ρ_lo, ρ_hi]:

              - Λ_upper := upper bound on Λ via the same single-peaked
                argument as `_two_window_mass_window_lower_arb`
                (K candidates at {ρ_lo, ρ_hi, sqrt(c)} clipped to the
                sub-interval), reusing the K-cache.
              - For ρ ∈ [ρ_lo, ρ_hi], the integrand `12 ρ³ (ρ² - c²)`
                is a polynomial in ρ that is monotone-increasing on
                this band whenever ρ_lo > c (which holds for V66 since
                ρ_lo ≥ c·(1 + 1e-6) > c). The minimum of the numerator
                is therefore at ρ = ρ_lo:
                  numer_lower = 12 · ρ_lo³ · (ρ_lo² - c²).
                (Rigour: for sub-intervals where ρ_lo² - c² < 0 the
                helper raises RuntimeError; this should not occur at
                V66 where the entire integration band is strictly
                above c.)
              - integrand_lower := numer_lower / (c⁶ · Λ_upper).
              - sub-interval contribution := (ρ_hi - ρ_lo) · integrand_lower.

            The final sum is a strict left-Riemann lower bound on the
            integral, summed in arb arithmetic. K is evaluated at each
            subdivision endpoint exactly once and the K-cache halves
            the work via shared evaluations between adjacent
            sub-intervals (mirroring sprint 099's pattern).
            """

    Implementation guidance:
      - Pre-compute `c_pow_6 = c_pows[6]` (already available in the
        c-power cache used by sprint 099's helpers).
      - Pre-compute `c_sq = c_pows[2]`.
      - Build the Λ-upper enclosure by calling
        `_two_window_mass_paper_lambda_from_K_arb` on the per-endpoint
        K values (computed once via `_two_window_mass_paper_K_arb`
        and shared across adjacent sub-intervals as in sprint 099),
        then `.union()` the candidate Λ values to produce the
        sub-interval Λ-upper.
      - Sum subinterval contributions in arb; return the running
        total.

  - **Replace the body of `certify_seven_window_mass_at_356562_sqrt`**:
    keep the docstring (updated to flag the arb backend per the
    sprint 099 pattern), keep the structural ordering checks at the
    top (migrated to rigorous arb comparisons), but replace the
    `with mp.workdps(int(dps)): ...` block (lines ~1834–1885) with
    an arb iterative-subdivision driver of the same shape as
    sprint 099's wrapper:

      - Construct `c_arb = _arb_exact(Fraction(356562, 1000000))`,
        `rho_top_arb = _arb_exact(Fraction(999999, 1000000))`,
        `delta_lo_arb = _arb_exact(Fraction(1, 1_000_000))`.
      - Construct sqrt-pinned arb endpoints exactly as the existing
        wrapper does, but using `arb(fmpq(p, q)).sqrt()` for each
        irrational endpoint:
          `fallback_a_lo_arb = c_arb * (arb(1) + delta_lo_arb)`
          `rho_a1_split_arb  = c_arb * arb(fmpq(50, 49)).sqrt()`
          `rho_a2_split_arb  = c_arb * arb(fmpq(36, 35)).sqrt()`
          `rho_4_lo_arb      = c_arb * arb(fmpq(25, 24)).sqrt()`
          `rho_3_lo_arb      = c_arb * arb(fmpq(16, 15)).sqrt()`
          `rho_2_lo_arb      = c_arb * arb(fmpq(9,  8)).sqrt()`
          `rho_1_lo_arb      = c_arb * arb(fmpq(4,  3)).sqrt()`
          `sqrt_c_arb        = c_arb.sqrt()`.
      - Migrate the eight ordering checks to rigorous arb comparisons
        (`(c_arb < fallback_a_lo_arb) is True`, etc.); each gap is
        well-separated (`> 10^(-3)`) so the rigorous comparison
        succeeds trivially.
      - Pre-compute `c_pows = _pow_cached(c_arb, max_exp)` with
        `max_exp = 2 * n_trunc + 3`. (`n_trunc = 300` per the existing
        wrapper, dominating the H_j tail since `2*max(j) + 2 = 10`.)
      - Pick `n_subdivisions = 256` initially and iterate in powers
        of 2 up to `2^14 = 16384`, exactly mirroring sprint 099's
        driver pattern. On each iteration:
          `m_a1 = _branch1_window_mass_lower_arb(c_arb, c_pows,
                     fallback_a_lo_arb, rho_a1_split_arb,
                     sqrt_c_arb, n_trunc, n_subdivisions)`
          `m_a2 = _branch1_window_mass_lower_arb(c_arb, c_pows,
                     rho_a1_split_arb, rho_a2_split_arb,
                     sqrt_c_arb, n_trunc, n_subdivisions)`
          `m_a3 = _branch1_window_mass_lower_arb(c_arb, c_pows,
                     rho_a2_split_arb, rho_4_lo_arb,
                     sqrt_c_arb, n_trunc, n_subdivisions)`
          `m_4 = _two_window_mass_window_lower_arb(c_arb, c_pows, 4,
                    rho_4_lo_arb, rho_3_lo_arb, sqrt_c_arb, n_trunc,
                    n_subdivisions)`
          `m_3 = _two_window_mass_window_lower_arb(c_arb, c_pows, 3,
                    rho_3_lo_arb, rho_2_lo_arb, sqrt_c_arb, n_trunc,
                    n_subdivisions)`
          `m_2 = _two_window_mass_window_lower_arb(c_arb, c_pows, 2,
                    rho_2_lo_arb, rho_1_lo_arb, sqrt_c_arb, n_trunc,
                    n_subdivisions)`
          `m_1 = _two_window_mass_window_lower_arb(c_arb, c_pows, 1,
                    rho_1_lo_arb, rho_top_arb, sqrt_c_arb, n_trunc,
                    n_subdivisions)`
          `total_lower = m_a1 + m_a2 + m_a3 + m_4 + m_3 + m_2 + m_1`
        Stop as soon as `(total_lower > floor_arb) is True` (with
        `floor_arb = arb(1) + arb(fmpq(1, 10))**30`), exactly as
        sprint 099. If the cap is reached without clearing the
        floor, raise `RuntimeError` with the failing margin and the
        used `n_subdivisions`, byte-similar to sprint 099's failure
        diagnostic.
      - Return `Fraction(1, 1)` on success.

  - **No edits** to any other function in `rigorous_scalar.py`. In
    particular, the existing `mp.quad` helpers
    `_two_window_mass_paper_factor`, `_two_window_mass_paper_lambda`,
    `_two_window_mass_term_j`, `_two_window_mass_window`,
    `_branch1_window_mass`, `certify_two_window_mass`,
    `certify_two_window_mass_at_35646`, the seven/eight/eleven-window
    mass functions for V67/V68, and the eq15 family are all left
    byte-preserved. The `mp.quad`-based `_branch1_window_mass` helper
    in particular **must** be byte-preserved because it is consumed
    by the V67 and V68 wrappers (`certify_seven_window_mass_at_356564_modeJ7`
    and `certify_seven_window_mass_at_356565_modeJ10`), which are
    NOT migrated by this sprint. (Future sprints will migrate V67
    and V68's wrappers using `_branch1_window_mass_lower_arb` from
    this sprint plus sprint 099's `_two_window_mass_window_lower_arb`.)

- **No edits** to:
  - `lemma.toml`: the `[[oracles]]` entry at lines 537–540 already
    points to `rigorous_scalar.certify_seven_window_mass_at_356562_sqrt`;
    that block is byte-preserved.
  - `Candidates/V66.lean`: the candidate-side
    `axiom h_seven_window_mass_certified_at_356562_sqrt` and its use
    site at line 327 are byte-preserved.
  - `KorenblumPaper/`: read-only (forbidden).
  - Any other `Candidates/V*.lean`: V66 is the only consumer of this
    oracle; V64 has its own arb-migrated oracle, V65 has its
    rational-endpoint sibling (not migrated), V67/V68 use the
    eight/eleven-window oracles (not migrated by this sprint).
  - `Numerical_Library/types.py`, `Numerical_Library/numerical_audit.py`:
    no schema changes.
  - `Proof/`, `Proposals/`, `[seed_axioms]`, `[import_policy]`,
    `[workspace_import_policy]`: all unchanged.

- **Add** a Phase 0 sanity script at
  `Scratch/sprint_100_arb_seven_window_mass_witness.py`: a standalone
  python script that calls the migrated wrapper once and prints:
    - the certified margin (i.e. the arb enclosure of `total - 1`),
    - the per-window arb-margin contributions (`m_a1`, `m_a2`, `m_a3`,
      `m_4`, `m_3`, `m_2`, `m_1`),
    - the iterative `n_subdivisions` clearance schedule (which power
      of 2 cleared the floor),
    - a comparison to sprint 087's centered `mp.quad` reference
      `+1.19998e-4` (margin reading; the rigorous lower-bound margin
      is expected to be O(width)-tighter, in the `10^(-5)` range).
  This script is not consumed by the evaluator; it serves as a
  human-readable witness in parallel to
  `Scratch/sprint_099_arb_two_window_mass_witness.py`.

- **Re-evaluate V66** by running the candidate evaluator on
  `Candidates/V66.lean` and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds
    (Lean side is byte-preserved; trivially passes).
  - `Evaluator.py --file Candidates/V66.lean` succeeds with
    `pass: true` and `score: "178281/500000"` (= `0.356562`,
    unchanged from V66's pre-migration score).
  - The post-migration V66 evaluator log entry's `axioms_used`
    set is **identical** (set-theoretically) to the pre-migration
    log entry's `axioms_used` set.
  - The `oracle_checks` table in the log entry records the same
    `axiom = h_seven_window_mass_certified_at_356562_sqrt,
    bound_field = seven_window_mass_lower, oracle_bound = 1,
    declared = 1, ok = true`.

- **Re-evaluate V68** (the live frontier) by running the candidate
  evaluator on `Candidates/V68.lean` and confirming `pass: true`,
  `score: "71313/200000"`, `axioms_used` set unchanged. (V68 does
  not depend on the migrated wrapper, but a second-level falsifier
  on the live frontier is cheap and catches any unintended side
  effect of the rigorous_scalar.py edit. This was the same
  discipline followed by sprint 099.)

- `Experience.md`: append a "Sprint 100 — arb-based migration of
  `certify_seven_window_mass_at_356562_sqrt` (second oracle
  migration; first seven-window architecture)" subsection
  summarizing:
    - the wrapper migrated,
    - the new helper `_branch1_window_mass_lower_arb` and its
      monotonicity argument,
    - the algorithmic shape (subdivision-based left-Riemann lower
      sum, with `n_subdivisions = ?` chosen by the iterative driver
      to clear the `10^(-30)` margin floor),
    - the certified arb-margin (e.g. arb-enclosure of margin in
      the `10^(-5)` range, vs. sprint 087's centered `+1.19998e-4`),
    - the V66 re-evaluation result (`pass: true`,
      `score: 178281/500000`, `axioms_used` unchanged),
    - the V68 re-evaluation result (`pass: true`,
      `score: 71313/200000`, `axioms_used` unchanged),
    - the forward implication: V67 and V68's wrappers
      (`certify_seven_window_mass_at_356564_modeJ7` and
      `certify_seven_window_mass_at_356565_modeJ10`) can now be
      migrated in subsequent sprints by composing
      `_branch1_window_mass_lower_arb` (this sprint) with
      `_two_window_mass_window_lower_arb` (sprint 099) — the
      template is now complete for the entire post-V52 mass-window
      family.

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_100 PASS|FAIL: …`).

## Acceptance criteria

1. The migrated `certify_seven_window_mass_at_356562_sqrt`, called
   standalone (e.g.
   `python -c "from Numerical_Library.rigorous_scalar import certify_seven_window_mass_at_356562_sqrt; print(certify_seven_window_mass_at_356562_sqrt())"`),
   returns `Fraction(1, 1)` and does not raise.

2. The migrated wrapper internally uses **only** `flint.arb` primitives
   (and the existing `arb`-tier helpers `_arb_exact`, `_pow_cached`,
   `_two_window_mass_paper_K_arb`, `_two_window_mass_paper_lambda_from_K_arb`,
   `_two_window_mass_paper_lambda_arb`, `_two_window_mass_window_lower_arb`,
   plus the new `_branch1_window_mass_lower_arb`) for the
   rigorous-bound computation. **No `mp.quad` call remains in this
   wrapper's body** (the `mp.quad`-based `_branch1_window_mass` and
   `_two_window_mass_window` helpers are byte-preserved at file
   level for use by V67/V68's still-mp.quad wrappers, but are *not*
   called by the migrated `certify_seven_window_mass_at_356562_sqrt`
   body).

3. `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds.

4. `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds.

5. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V66.lean` succeeds with
   `pass: true` and `score: "178281/500000"` (= `0.356562`,
   unchanged from V66's pre-migration score).

6. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (= `0.356565`,
   unchanged from V68's pre-migration score).

7. The post-migration V66 evaluator log entry's `axioms_used` set
   is **identical** (set-theoretically, comparing the `name` field
   of each entry) to V66's pre-migration log entry's `axioms_used`
   set. No new axioms introduced. No old axioms removed. The
   pre-migration set is exactly six entries:
   `{propext, Classical.choice, Quot.sound,
    ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt,
    ProofRefinement.Korenblum.Candidates.V66.hH2_v66,
    ProofRefinement.Korenblum.Candidates.V66.hCircleGapInt_v66}`.
   (Audit per the most recent V66 log entry; if the actual axiom
   namespace prefix on the certify entry differs in the live log,
   match the live log set-theoretically — the binding invariant is
   "set-theoretically identical to pre-migration".)

8. The post-migration V66 evaluator log entry's `oracle_checks` table
   contains exactly one entry with
   `axiom = "h_seven_window_mass_certified_at_356562_sqrt"`,
   `bound_field = "seven_window_mass_lower"`, `oracle_bound = "1"`,
   `declared = "1"`, `ok = true`. (Unchanged from pre-migration.)

9. The Phase 0 sanity script
   `Scratch/sprint_100_arb_seven_window_mass_witness.py` prints a
   certified arb-enclosure of `total - 1` whose lower endpoint
   exceeds `10^(-30)` (i.e. the strict-margin floor). The
   per-window arb-margin contributions are also reported. The
   midpoint margin reading is expected to agree with sprint 087's
   centered `+1.19998e-4` to within an O(width)-discretisation
   error — not to within `10^(-6)` (sprint 099 demonstrated that
   strict left-Riemann lower-bound algorithms are not centered-
   estimate-faithful at that resolution). **The load-bearing
   relation is `margin.lower() > 10^(-30)`**, not centered-
   midpoint agreement.

10. The migrated wrapper completes within **~120 seconds** on a
    single invocation. (Existing `mp.quad` version: ~10 s for 7
    windows; arb-based subdivision quadrature with `n_subdivisions
    ≤ 16384` and 7 windows is expected to take ~30–60 s; a 120 s
    ceiling leaves ample headroom for a generator that iteratively
    raises `n_subdivisions` to clear the margin floor in the
    tighter `+1.20e-4` envelope.)

11. `Experience.md` and `Bulletin.md` each gain one row per the
    standard pattern.

The sprint is **PASS** if all 11 criteria are met. The sprint is
**FAIL** if V66 or V68's evaluator score changes, the `axioms_used`
set diverges, the migrated wrapper raises `RuntimeError` (i.e. the
arb-rigorous lower bound fails to clear the `10^(-30)` floor — most
likely cause is `n_subdivisions` set too coarse, or a bug in the new
`_branch1_window_mass_lower_arb` helper), or the wrapper exceeds the
120 s time ceiling.

## Out of scope

- Migrate any other oracle wrapper. This sprint scope is **exactly
  one wrapper** — `certify_seven_window_mass_at_356562_sqrt`. The
  remaining four un-migrated mass-window candidates
  (`certify_two_window_mass_at_35646` (V65 rational sibling),
  `certify_seven_window_mass_at_356564_modeJ7` (V67),
  `certify_seven_window_mass_at_356565_modeJ10` (V68)) and the five
  `certify_eq15_at_*` wrappers are queued for follow-up sprints
  once this sprint's seven-window template is validated.

- Edit `Candidates/V66.lean` or any other Lean file. The migration
  is a Python-side internal change to one wrapper; the candidate-
  side `axiom` declaration and its usage are byte-preserved.

- Edit the `[[oracles]]` registration in `lemma.toml`. The
  `oracle_fn` continues to point at the same wrapper name; the
  candidate axiom name is unchanged; the bound field is unchanged.

- Edit the existing `mp.quad`-based `_branch1_window_mass` helper
  in `rigorous_scalar.py`. It must remain byte-preserved because
  V67/V68's wrappers still consume it. The new arb helper is added
  alongside, not in place of.

- Add or remove free axioms. The migration preserves the trust
  surface conjunct-for-conjunct.

- File a `Proposals/` entry. The migration is a Python-side backend
  swap inside one wrapper that already exists and is already
  registered. No trust-base expansion is involved — the wrapper's
  external contract (zero-arg shim returning `Fraction(1, 1)` iff
  the certified mass clears the `10^(-30)` floor) is preserved
  byte-for-byte; only the algorithmic backend (`mp.quad` → `arb`)
  changes. Per AGENT_BRIEF lines 80–86: oracle-shaped
  *modifications* of an existing oracle's backend follow the same
  inline pattern as oracle-shaped additions and do not require a
  proposal.

- Change the final theorem statement of any candidate.

- Hoist `Candidates/V66/Branch1Integrability.lean` to `Proof/`.
  Currently demoted as architecture-specific (only V67/V68 import
  it, both in the same eight/eleven-window family). Queue for a
  future sprint after a third cross-architecture consumer surfaces.

- Hoist V66's `SevenWindowEndpoints.lean`, V67's
  `EightWindowEndpoints.lean`, or V68's `ElevenWindowEndpoints.lean`.
  These are window-architecture-specific and not reused as broadly
  as the V63 trio.

- Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`. No
  current consumer; queueing it speculatively before establishing
  a Lean derivation chain that needs it would risk
  infrastructure-speculation work.

- Run any Phase 0 numerical falsifier sweep beyond the
  sanity-check witness script
  (`Scratch/sprint_100_arb_seven_window_mass_witness.py`). The
  migration is structural; the sanity script exists only to
  produce a human-readable margin reading.

- Push past V68's `c = 71313/200000`. The score-push surface at
  the existing trust surface remains exhausted (Slacks 1/3/5
  falsified by sprints 093/094/095; Slack 2 settled by
  sprint 077; Slack 4 needs a trust expansion forbidden by
  AGENT_BRIEF line 188-190). After this sprint, the live frontier
  remains V68 at `71313/200000`.

- Discharge `hH2_v6×` or `hCircleGapInt_v6×` from
  `Section2Assumptions` (Slack 4 / Bulletin §B(4)). This requires
  either a `KorenblumPaper/` edit (forbidden) or a trust-base
  expansion proposal whose math is not pinned tightly enough yet.

## Time budget

≤ 90 minutes runtime:
  - Migrated-wrapper standalone invocation: ~30–60 s (one-shot
    arb computation; iterative driver may need n_subdivisions =
    4096 or 8192 to clear the tighter `+1.20e-4` envelope vs.
    sprint 099's `+1.9e-3`).
  - V66 evaluator: ~5 minutes (typecheck + axiom scan + oracle
    invocation; the migrated wrapper now runs ~3–6× longer than
    the `mp.quad` predecessor, but well within the evaluator's
    wall-clock budget).
  - V68 evaluator: ~3 minutes (V68 does not invoke the migrated
    wrapper, so its timing is unchanged).
  - Phase 0 sanity script: ~30–60 s.

≤ 1 generator session (~2.5–3.5 hours including the new private
helper function in `rigorous_scalar.py` (~80–100 lines of arb
arithmetic, the only new helper since sprint 099's three are
reused verbatim), the wrapper-body rewrite (~80 lines, larger
than sprint 099's wrapper because of the seven windows), the
Phase 0 sanity script (~50 lines), the two evaluator runs
(~8 minutes total wall-clock), and the witness updates to
`Experience.md` and `Bulletin.md`).

## Stop conditions

- All 11 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- The arb-rigorous lower bound on `total_lower` does not clear
  `1 + 10^(-30)` even at the maximum `n_subdivisions = 16384`:
  `STATUS=BLOCKED` with the arb-enclosure of the failing margin
  and the per-window margin contributions. Most likely causes:
  (i) a bug in the new `_branch1_window_mass_lower_arb` helper
  (e.g. wrong sign in the integrand monotonicity argument, or
  failure to cache K endpoints correctly across adjacent
  subintervals); (ii) the truncation `n_trunc = 300` is too
  coarse to give a tight enough `Λ`-upper-bound at the canonical
  sqrt endpoints (raise `n_trunc` to 600); or (iii) the
  +1.20e-4 envelope is genuinely tighter than expected after
  rigorous lower-bound discretisation, requiring n_trunc and
  n_subdivisions both at the cap. All three are locally fixable;
  sprint 087 recorded margin `+1.19998e-4` at `n_trunc = 300`
  under `mp.quad`, so a tightness gap of ~25 orders of
  magnitude over the floor is the available headroom.

- The migrated wrapper exceeds the 120 s time ceiling:
  `STATUS=BLOCKED` with the wall-clock and the `n_subdivisions`
  value used. Resolution: profile the K-cache reuse (sprint 099
  showed K-cache halving the work; the seven-window driver
  should be cache-symmetric), reduce `n_trunc` if the Λ
  truncation tail is tight enough to drop from 300 to 200, or
  parallelize the seven independent window-integrals (out of
  scope for this sprint, but a possible follow-up).

- V66's evaluator score changes from `178281/500000` after the
  migration: `STATUS=BLOCKED` with the diff in `axioms_used`
  and the new score. Most likely cause: an accidental edit to
  V66's body, to `lemma.toml`'s oracle entry, or to one of the
  helper functions still consumed by V66. The migration is
  intended to be Lean-side and lemma.toml-side byte-preserving.

- The `axioms_used` set diverges from V66's pre-migration set:
  `STATUS=BLOCKED` with the set-difference. The migration must
  be audit-envelope-preserving by construction; if it is not,
  something has gone wrong (e.g. an accidental new free-floating
  axiom in a Lean file, or a removed `byte-preserved` axiom).

- The `oracle_checks` table reports `ok = false` for
  `h_seven_window_mass_certified_at_356562_sqrt`:
  `STATUS=BLOCKED` with the wrapper's `RuntimeError` message.
  Most likely cause: the migrated wrapper raised `RuntimeError`
  because the arb-rigorous bound failed to clear the floor —
  same diagnosis as the first stop condition above.

- An accidental side-effect to V67 or V68's wrappers
  (`certify_seven_window_mass_at_356564_modeJ7` or
  `certify_seven_window_mass_at_356565_modeJ10`) shows up as a
  V67 or V68 evaluator failure: `STATUS=BLOCKED` with the
  failing wrapper's diagnostic. Most likely cause: an accidental
  edit to the byte-preserved `_branch1_window_mass` mp.quad
  helper that V67/V68 still consume. Resolution: revert the
  edit and ensure the new arb helper `_branch1_window_mass_lower_arb`
  is added alongside, not in place of, the mp.quad helper.

- A `flint`/`arb` API surface used by the migration turns out to
  be unavailable in the current `flint` version pinned by
  `pyproject.toml`/`uv.lock`: `STATUS=BLOCKED_NEEDS_HUMAN` with
  the unavailable API. Note: this should not occur — sprint 099
  already exercised the full surface (`arb`, `arb.__mul__`,
  `arb.__add__`, `arb.__pow__`, `arb.sqrt`, `arb.__lt__`,
  `arb.__le__`, `arb.__gt__`, `fmpq`, `arb.union`, `ctx.workdps`,
  `_arb_exact`, `_pow_cached`); the new helper uses no API
  surface beyond what sprint 099 used.

- Trust expansion needed (the migration unexpectedly requires a
  new `Numerical_Library` library, a new `lemma.toml` entry, or
  a new Lean axiom): `STATUS=BLOCKED_NEEDS_HUMAN`. Note: this
  should not occur — `flint.arb` is already imported and the
  wrapper name / oracle entry / candidate axiom are all
  byte-preserved.
