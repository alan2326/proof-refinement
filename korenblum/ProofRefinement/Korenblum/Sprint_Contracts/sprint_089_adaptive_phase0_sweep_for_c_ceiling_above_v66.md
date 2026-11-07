# Sprint 089: Adaptive Phase 0 sweep for a c-ceiling above V66's `c = 356562/1000000`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V66.lean` (V66 stays as the live ceiling at
`c = 356562/1000000`; no candidate ships this sprint)
**Target file**: no new `Candidates/V<N>.lean` this sprint. Concrete artifacts:

  * `Scratch/sprint_089_adaptive_seven_window_mass_sweep.py` (+ `.txt` output) —
    high-precision adaptive Phase 0 numerical search varying the architecture
    parameters that V66's `h_seven_window_mass_certified_at_356562_sqrt`
    bakes in (`ρ_top`, `δ_lo`, the deep-band box-split locations, and
    optionally the mode-window-count via extension to j=5/6/7/8/...) over a
    c-sweep upward from `356563/1000000`.
  * `Scratch/sprint_089_adaptive_seven_window_mass_sweep.txt` — reproducibility
    log with full per-c, per-architecture, per-window mass tables and a
    final `DECISION` line: **GO with `c_new`, `architecture_new`, and
    `margin_new ≥ 1e-4`**, or **NO-GO with explicit rationale**.
  * `Scratch/sprint_089_witness.txt` — if GO, a concise summary capturing
    the chosen c, the chosen architecture (window kinds, endpoints, mode
    indices), and the full-envelope margin at `(dps, n_trunc) = (80, 300)`,
    suitable for sprint 090 to consume verbatim when authoring the next
    oracle wrapper.

**Direction**: oracle-support (Phase 0 numerical witness; no Lean changes).

## Goal

Conduct a parameter-space numerical sweep extending sprint 087's Phase 0
methodology to determine whether the V38 seven-window architecture admits
a strictly larger valid `c` than V66's current `356562/1000000`, by
relaxing the architecture parameters that sprint 087 fixed at convenient
sqrt-pinned defaults. Concretely:

  1. **`ρ_top` sweep.** Sprint 087 pinned `ρ_top = 999999/1000000`. Push
     `ρ_top` toward `1`: try `ρ_top ∈ {1 - 10⁻⁶, 1 - 10⁻⁷, 1 - 10⁻⁸, …}`
     down to the largest value at which `paper_lambda(c, ρ_top, n_trunc)`
     stays finite (i.e., `K(c, ρ_top)² < 1`). Each `ρ_top` extension grows
     mode1's window (currently the dominant mass contributor at ~0.9946)
     and so should grow the joint mass.

  2. **`δ_lo` sweep.** Sprint 087 pinned `δ_lo = 10⁻⁶`. Push `δ_lo` toward
     0: try `δ_lo ∈ {10⁻⁶, 10⁻⁷, 10⁻⁸, 10⁻⁹}`. The Branch.one integrand
     `12 ρ³ (ρ² - c²) / (c⁶ Λ)` vanishes as `(ρ-c)·O(c) → 0`, so the gain
     is `O((δ_lo)²)` and small in absolute terms — but it costs nothing to
     measure and may add `~10⁻¹¹` per decade of `δ_lo` reduction. Cheap to
     sweep; report exact deltas.

  3. **Deep-band box-split sweep** (optional second-tier; report only if
     the `ρ_top`/`δ_lo` sweep yields ≥ 5e-5 incremental margin). Sprint 087
     placed the boxA1/A2 splits at `c·sqrt(50/49)` and `c·sqrt(36/35)`;
     these are *not load-bearing for joint mass* — the Branch.one integral
     over `[c·(1+δ), c·sqrt(25/24)]` is the same regardless of how it is
     subdivided, so changing the splits leaves total mass invariant.
     This direction should be **measured and confirmed equal** to sanity-
     check the sweep code (i.e., merging the three boxes into one or
     subdividing into five Branch.one boxes should yield identical totals
     up to numerical precision).

  4. **Extra-mode-window sweep** (optional third-tier; report only if
     directions 1 + 2 yield ≥ 5e-5 incremental margin AND the architectural
     extension is implementable in `Proof/Reduction.lean` without new
     paper-axiom expansions). Replace boxA3 (currently
     `[c·sqrt(36/35), c·sqrt(25/24)]`, Branch.one) with a `mode5`
     window (`τ_5 = 35/36`, dominating on `[c·sqrt(36/35), c·sqrt(25/24)]`).
     Replace boxA2 with `mode6` (`τ_6 = 48/49`,
     `[c·sqrt(49/48), c·sqrt(36/35)]`). Etc., up to `j ≤ 8`. Each extra
     mode window is a strictly tighter envelope than Branch.one on its
     τ-band (the per-mode kernel is sharp at the τ-breakpoints; Branch.one
     is the looser Wang eq(5) envelope on the same band). Report the per-c
     mass gain.

  5. **c-sweep over the architecture chosen as best by 1+2+(3 if needed)
     +(4 if needed).** For the best architecture, sweep `c` upward from
     `356563/1000000` in `1e-6` steps (and `1e-7` steps near the c-ceiling
     bracket) until margin drops below `1e-4`. Report the c-ceiling.

The outcome of the sprint is a single `DECISION` line:

  * **`Phase 0 GO`** if a `c_new > 356562/1000000` is found with full-
    envelope margin `≥ 1e-4` under some architecture variant. Sprint 090
    then writes the matching `Numerical_Library` wrapper, registers the
    `[[oracles]]` row, and ships V67 at `c_new`. The sprint's witness file
    `Scratch/sprint_089_witness.txt` records exactly the architecture
    sprint 090 must reproduce.

  * **`Phase 0 NO-GO`** if no `c > 356562/1000000` admits margin `≥ 1e-4`
    under any tested architecture. The sprint records the largest margin
    achieved at each c above 356562 and the architecture that achieved it,
    so future planners can quantify exactly how much headroom is on the
    table for further architectural innovation. Sprint 090+ then pivots
    to a different direction (trust-surface compaction, hoisting derived
    theorems, Wang Lemma 2 / Fourier orthogonality, etc.).

This sprint **introduces no Lean changes**, **no `Numerical_Library`
wrappers**, **no `lemma.toml` rows**, **no `Proposals/` entries**, and
**no candidate files**. It is a pure numerical exploration sprint, in
keeping with the Bulletin priority block's "Use `Scratch/`" guidance:
sprint a Scratch script before committing Lean work to a c-push that
might evaporate once the integration is run at full precision.

## Why

### Why this is the right next sprint

V66 just shipped at `c = 356562/1000000` with full-envelope margin
`+1.20e-4` over the V38 seven-window architecture sprint 087 pinned. The
oracle wrapper bakes in three architecture parameters — `ρ_top`,
`δ_lo`, and the box-split locations — at **convenient sqrt-pinned /
rational defaults** that were chosen for sprint-088 ergonomic structural
ease (sqrt-pinned matches the τ-breakpoint defaults, `ρ_top = 1 - 10⁻⁶`
is round, the box-split sqrt-ratios match the next two τ-breakpoints up).
**None of these defaults were chosen to maximize joint mass.** They are
load-bearing for the sprint 087 oracle row (because the wrapper hardcodes
them) but they are not load-bearing for the *next* oracle row sprint 090
will write — sprint 090 can pick whatever `(ρ_top, δ_lo, box_splits,
mode_count)` the sweep determines is optimal at the chosen c.

V66's margin is `+1.20e-4`. **At the same architecture**, c=356563 gives
margin `+9.7e-5`, c=356564 (not in the script's table but extrapolates
linearly) gives ~`+7.4e-5`, and so on. So the V66 architecture admits c
up to ~356567 before margin drops below `1e-4` (and the script's row at
356567 confirms `+4.0e-6`, which is *not* below 1e-4 in absolute value
... wait, the row reads `+4.0e-6` — that *is* below 1e-4 strictly). The
upper bracket of the V66 architecture's c-ceiling for margin ≥ 1e-4 is
`356567/1000000` (margin `+4.0e-6` < 1e-4 fails the GO floor; the actual
ceiling is between 356562 and 356563 at the 1e-4 floor). So **the V66
architecture's headroom above 356562 is at most ~5e-6**, which is too
small to justify shipping V67 at it — sprint 090 would inherit a
margin too tight to certify reliably under wrapper round-off.

The architectural relaxation directions (1)–(4) above each have a
quantifiable expected gain:

  * **(1) `ρ_top`**: at `c = 356562/1000000`, mode1 contributes 0.9946
    out of 1.000120 total. Mode1's integrand near `ρ = 1` is
    `2ρ / (H_1·Λ) = 4ρ³ / (c⁴·Λ(c, ρ))`. Λ(c, 1) is finite iff
    `K(c, 1)² < 1`. From the script's `paper_lambda` definition,
    `K(c, ρ) = 2ρ(1 + c/ρ²)·Π_n (1 + ρ² c^(2n+1))(1 + c^(2n+3)/ρ²)
    (1 + c^(2n+2))² / [(1 + ρ² c^(2n))(1 + c^(2n+2)/ρ²)(1 + c^(2n+1))²]`.
    At ρ → 1 the product converges; at c ≈ 0.3566, `K(c, 1)² ≈ ?` —
    the sweep script must compute this and report whether `K(c, 1)² < 1`
    so that `ρ_top → 1⁻` is feasible. **If feasible**, extending `ρ_top`
    from `1 - 10⁻⁶` to `1 - 10⁻⁹` adds the mass fragment
    `∫_{1-10⁻⁶}^{1-10⁻⁹} 4ρ³ / (c⁴·Λ(c,ρ)) dρ ≈ 4 / (c⁴·Λ(c,1))·10⁻⁶`
    which at c = 0.3566 and Λ ~ 1.5 (rough estimate) is ~`4/(0.0162·1.5)·
    10⁻⁶ ≈ 1.6e-4`. **That is potentially the entire V66 margin
    again**, pushing c-ceiling from 356562 to ~356575. This is the
    lead direction. If `K(c, 1)² ≥ 1` (Λ blows up before ρ = 1), the
    sweep instead finds the largest finite `ρ_top` and the gain is
    smaller but quantifiable.

  * **(2) `δ_lo`**: gain is `O(δ_lo²) ≈ 10⁻¹²` per decade. Negligible
    individually but free to measure.

  * **(3) box-split sweep**: must be measured equal up to integration
    precision; this is a sanity check on the sweep code, not a c-push.

  * **(4) extra-mode-window sweep**: strictly tighter envelope than
    Branch.one on `(c·sqrt(j+2)/(j+1), c·sqrt(j+1)/j)` for `j ≥ 5`.
    Per-window mass for mode `j` on `[ρ_lo, ρ_hi]` scales as
    `∫ 2ρ/(H_j·Λ) dρ ≈ (j+1)/(j·c^(2j+2)) · ∫ 2ρ^(2j+1)/Λ dρ`. As
    `j → ∞` and `ρ_lo, ρ_hi → c`, this is bounded but the integrand
    `2ρ^(2j+1)/Λ` peaks at `ρ_hi`. The Wang eq(5) Branch.one envelope
    is `12 ρ³(ρ²-c²)/(c⁶·Λ)` on the same band. Direct comparison at
    a band's right endpoint `ρ_hi = c·sqrt((j+2)/(j+1))`: per-mode
    integrand is `2 ρ_hi (j+1)/(j) · ρ_hi^(2j) / (c^(2j+2)·Λ)
    = 2 ρ_hi (j+1)/j / (c² Λ) · ((j+1)/(j+2))^j` whereas Branch.one
    integrand is `12 ρ_hi^3 (ρ_hi^2 - c²)/(c⁶ Λ)
    = 12 ρ_hi^3 · c²/(j+1) / (c⁶ Λ)
    = 12 ρ_hi^3 / ((j+1) c⁴ Λ)`. Ratio per-mode/Branch.one
    ~ `(j+1)²/(6j(j+2)) · ρ_hi^{2j-2} c^{2-2j} → 1/6` as
    `j → ∞`, so per-mode is **strictly smaller** than Branch.one
    asymptotically, meaning per-mode admits **larger** `2ρ/(H·Λ)`
    integration mass (since smaller H means larger mass density).
    This tier is concretely worth ~10⁻⁵ of joint mass per added mode
    window if direction (1) doesn't already saturate the gain.

The expected outcome (rough prior, to be confirmed by the script):

  * Direction (1) yields **+1e-4 incremental margin** if `K(c, 1)² < 1`
    at the relevant c; **+1e-5 to +5e-5** if Λ blows up at some
    `ρ* < 1` and `ρ_top` can only go up to `ρ* - ε`.
  * Directions (2)–(4) yield **<1e-5 each** individually.
  * Combined, the sweep should find a c-ceiling in
    `[356567/1000000, 356700/1000000]` with margin `≥ 1e-4` under the
    relaxed architecture — pushing the V66 frontier by `5e-6` to
    `1.4e-4` upward.

Even the **floor outcome (NO-GO)** is informative: it tells future
planners that the V38 seven-window architecture is exhausted at
356562/1000000 and that further c-push requires a structurally
different architecture (e.g. eight or nine windows, a different kernel
family, or a new oracle).

### Why a Scratch-only sprint is the right shape now

Per the Bulletin priority block:

> Lean is the certification layer, not the exploration layer. A failed
> sprint that burned an hour writing Lean for a chain that turned out
> to be algebraically wrong costs far more than a 10-minute SymPy
> script that would have caught it.

Sprints 088 (V66 at 356562/1000000) shipped Lean infrastructure for
exactly the architecture sprint 087 pre-certified. To push c further,
the planner can either:

  * Speculatively reuse the V66 architecture at a higher c with a new
    oracle row — but the V66 architecture's margin floor at c = 356563
    is already ~9.7e-5, well below the wrapper's reliability margin.
    This **WILL fail** at the strict-margin floor. (Direction sprint
    089b in the planner's pre-sprint candidate list — demoted.)

  * Speculatively reuse the V66 architecture at a higher c with a
    *relaxed* margin floor — but that pushes the wrapper margin into
    the precision-loss zone where 80-dps mpmath integration has
    floor-level uncertainty. **Brittle, not strictly defensible.**

  * Run an architecture-relaxing Phase 0 sweep first (this sprint),
    then ship the wrapper + oracle + V67 in sprint 090 only if the
    sweep finds a margin-robust higher c. **Falsifiable, low risk,
    high information yield.**

The sprint is bounded: it requires extending `Scratch/sprint_087_v38_seven_window_mass_sweep.py`
by ~150-300 lines (parameter sweep loops, an extra-mode-window
helper, a `K(c, 1)²` finite-feasibility check, and a richer
`DECISION` block). Estimated runtime: 15-45 minutes for the script
to execute (extrapolating from sprint 087's ~30-minute full sweep).

### Three (and more) distinct directions considered

Per the planner agent definition's "Think carefully" guidance:

1. **Direction A — this sprint: Scratch-only adaptive sweep.**
   Pure numerical Phase 0 search varying `(ρ_top, δ_lo, box_splits,
   mode_count)` to find the highest c above 356562 with margin ≥ 1e-4.
   Reports GO with witness or NO-GO with rationale. Zero Lean
   changes, zero oracle changes, zero `lemma.toml` changes.
   **Strongest objection:** if the sweep returns NO-GO, the harness
   gains no score in this sprint — the score stays at 356562/1000000.
   **Counter:** NO-GO is informative — it tells the planner the V38
   architecture is exhausted, redirecting future sprints toward
   structural changes (per-mode chain extension to j ≥ 5, alternative
   kernel families, trust-surface compaction). The cost of *not*
   running this sweep is that subsequent sprints would have to make
   architectural commitments without knowing whether the V38 shape
   has residual headroom. **Falsifiable, low-risk, low-cost — wins
   on expected information per session-budget.**

2. **Direction B — Direct adaptive ship: combine sweep + wrapper +
   oracle + V67 in one sprint.** **Strongest objection:** if the
   Phase 0 outcome is small (<5e-5 incremental margin), the sprint
   wastes the wrapper + oracle + V67 work, and the resulting V67
   ships with margin too thin to be wrapper-reliable. The sprint is
   also large (Scratch + Numerical_Library + lemma.toml +
   Reduction.lean axiom + V67 candidate body + V67 derived theorem
   files). **Demoted as higher-risk, lower-information than A.**
   The user's directive explicitly notes "Higher risk if Phase 0
   result is small."

3. **Direction C — Trust-surface compaction (replace `hH2_v6×` /
   `hCircleGapInt_v6×` per-candidate axioms with theorems consuming
   `Section2Assumptions` fields).** Structural cleanup; doesn't
   move the score. **Strongest objection:** doesn't push c. The
   current Bulletin priority is to advance score above 356562/1000000;
   this direction advances trust quality but not score. Per the
   AGENT_BRIEF "the score is `c_value`, larger is better", trust
   compaction at zero score gain is preparatory work, not a primary
   sprint. **Demoted.** Also, the user's directive explicitly noted
   "AGENT_BRIEF says proposals are deferred indefinitely; not
   preferred" — and this direction's natural target (`proposal_004`
   if `Section2Assumptions` cannot subsume the H² and circleGap
   integrability fields) would require a proposal, which is deferred.

4. **Direction D — Sibling c-push along m=2 axis** (extending V64's
   two-window perMode chain to higher c without the seven-window
   complexity). User noted "capped at +9e-5 above V64, lower than
   V66's +1.02e-4". **Strongest objection:** V66 already exceeds
   this ceiling; m=2 is structurally inferior at the current
   frontier. **Demoted.**

5. **Direction E — Hoist V53/V54/V55/V57/V58/V60 derived theorems
   into `Proof/`.** Tech-debt cleanup; doesn't move score.
   **Strongest objection:** mostly orthogonal to score. **Demoted.**

6. **Direction F — Wang Lemma 2 / Fourier orthogonality as a
   derived-theorem file.** Significant analytic Lean derivation; could
   eventually reduce free-axiom count by replacing `hH2_v6×` and
   `hCircleGapInt_v6×` with derivations. **Strongest objection:**
   doesn't move score directly; preparatory for a long-term
   trust-surface goal that is not currently the priority.
   **Demoted.**

7. **Direction G — `proposal_004` to add H² + circleGap integrability
   fields to `Section2Assumptions`.** **Strongest objection:** user's
   directive: "Do not file proposals." Also, per the planner
   four-condition guide (AGENT_BRIEF): no "tried hard and failed"
   attempt has been made on deriving these from the existing fields,
   no concrete c-push tied to it. **Hard-rejected by user directive.**

Direction A wins on **expected information per session-budget**:
it is the only direction that *answers the c-push question* with a
falsifiable Scratch experiment, and the cost is bounded (one
Generator session of pure Python). All other directions require
Lean commitments without the numerical evidence to back them.

### Bounded for one session

  * Read sprint 087's existing sweep script as the structural template
    (`Scratch/sprint_087_v38_seven_window_mass_sweep.py`, 510 lines).
  * Extend it by:
    - Adding an outer loop over `ρ_top ∈ {1 - 10⁻⁶, 1 - 10⁻⁷, ...}`,
      with a feasibility check `K(c, ρ_top)² < 1` (skip infeasible).
    - Adding an outer loop over `δ_lo ∈ {10⁻⁶, 10⁻⁷, 10⁻⁸, 10⁻⁹}`.
    - Adding a per-(ρ_top, δ_lo) c-sweep starting from `356563/1000000`
      upward with `1e-6` step, fine-tuned to `1e-7` near the ceiling.
    - Adding a sanity-check pass confirming box-split invariance.
    - Adding an extra-mode-window function `mode_j_window_mass` for
      `j ∈ {5, 6, 7, 8}` using the same integrand definition (already
      parametric in j in the sprint 087 script).
    - Emitting a final `DECISION` line in the `.txt` output.

Estimated extension: ~250 new lines on top of 510 existing.
Estimated runtime: 30-60 minutes for the full sweep.

## Concrete edits expected

### 1. `Scratch/sprint_089_adaptive_seven_window_mass_sweep.py` (new file)

Built on `Scratch/sprint_087_v38_seven_window_mass_sweep.py` (do not
modify the sprint 087 file; this is a *new* sweep with adapted
parameters). Required structure:

```python
"""
Sprint 089 / Phase 0 adaptive sweep — search for c-ceiling above V66.

V66 ships at c = 356562/1000000 with full-envelope margin +1.20e-4.
Sprint 087's sweep pinned (ρ_top, δ_lo, box_splits) at convenient
sqrt-pinned defaults that are NOT load-bearing for joint-mass sum.
This sweep relaxes those defaults and re-searches for the largest c
admitting margin ≥ 1e-4 over the relaxed architecture.

Direction (1): ρ_top sweep. Push toward 1 subject to K(c, ρ_top)² < 1.
Direction (2): δ_lo sweep. Push toward 0.
Direction (3): box-split sweep (sanity check, expected null effect).
Direction (4): extra-mode-window sweep. Replace boxA3/A2/A1 with
               mode5/mode6/mode7/... where the per-mode envelope is
               strictly tighter than Branch.one.

Final DECISION:
  - GO with c_new, architecture_new, margin_new ≥ 1e-4.
  - NO-GO with explicit per-direction rationale.
"""

# Standard imports + reuse of paper_factor/paper_lambda from sprint 087.
# (Either import the helpers from sprint_087 by path, or inline the
# definitions; inlining is cleaner and keeps Scratch files standalone.)

# ... (sprint 087's paper_factor, paper_lambda, term_j, mode_window_mass,
#      branch1_integrand, branch1_window_mass, fraction_to_mpf, ...)


def k_squared_at_rho_top(c_mp, rho_top_mp, n_trunc):
    """Returns K(c, ρ_top)² for the feasibility check Λ ∈ ℝ ⇔ K² < 1."""
    prod = mp.mpf(1)
    for n in range(0, n_trunc):
        prod *= paper_factor(c_mp, rho_top_mp, n)
    K = 2 * rho_top_mp * (1 + c_mp / rho_top_mp ** 2) * prod
    return K * K


def adaptive_seven_window_mass(
    c_mp, *, rho_top_mp, delta_lo, rho_a1_split_mp, rho_a2_split_mp,
    extra_mode_count, n_trunc,
):
    """
    Joint mass under the adaptive architecture. extra_mode_count = 0
    matches sprint 087's seven-window split. extra_mode_count ∈ {1, 2, 3}
    replaces boxA3, then boxA2, then boxA1 with mode5, mode6, mode7
    (covering the τ_5 = 35/36, τ_6 = 48/49, τ_7 = 63/64 bands).
    """
    # Implementation: build the windows list adaptively; for each
    # extra mode replaced, drop the corresponding boxA_k and insert
    # mode_(j+4) at the matching τ-band.
    ...


def feasibility_scan_rho_top(c_mp, rho_top_candidates, n_trunc):
    """
    For each ρ_top candidate, check K(c, ρ_top)² < 1. Returns the
    largest feasible ρ_top.
    """
    feasible = []
    for rho_top in rho_top_candidates:
        k_sq = k_squared_at_rho_top(c_mp, rho_top, n_trunc)
        feasible.append((rho_top, k_sq, k_sq < 1))
    return feasible


def main(argv) -> int:
    # Sweep envelope: scan_dps = 40, scan_n_trunc = 120 (matches
    # sprint 087); verify_dps = 80, verify_n_trunc = 300.

    # Step 1: rho_top feasibility at c = V66's c.
    # Step 2: rho_top sweep at c = V66's c, measure mass gain.
    # Step 3: delta_lo sweep, measure mass gain.
    # Step 4: box-split invariance sanity check.
    # Step 5: extra-mode-window sweep (j up to 8), measure mass gain.
    # Step 6: pick best architecture, sweep c upward from 356563.
    # Step 7: re-verify chosen c at full envelope.
    # Step 8: emit DECISION line.

    ...

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
```

The script must be self-contained (no imports from sprint 087's
script; copy the helpers or inline them). All sweeps run at
`scan_dps = 40, scan_n_trunc = 120`. The chosen architecture's
chosen c is re-verified at `verify_dps = 80, verify_n_trunc = 300`
before the `DECISION` line is emitted.

### 2. `Scratch/sprint_089_adaptive_seven_window_mass_sweep.txt` (new file)

The captured stdout of the Python script. Must contain, at minimum:

  * `Pinned envelope:` block (dps, n_trunc, sweep ranges).
  * `ρ_top feasibility table at c = 356562/1000000:` with
    `(rho_top, K_squared, feasible)` rows.
  * `Direction 1 (ρ_top sweep) at c = 356562/1000000:` with per-
    `ρ_top` total-mass and margin.
  * `Direction 2 (δ_lo sweep) at c = 356562/1000000:` per-`δ_lo`
    delta to baseline.
  * `Direction 3 (box-split sanity) at c = 356562/1000000:` showing
    invariance to within numerical precision.
  * `Direction 4 (extra-mode-window sweep) at c = 356562/1000000:`
    per-`extra_mode_count` total-mass and incremental margin.
  * `Best architecture identified:` block summarizing the parameter
    set chosen for the c-sweep.
  * `c-sweep table under best architecture:` with rows
    `(c, total, margin)`.
  * `Full-envelope re-verification at chosen c:` with per-window
    masses.
  * `DECISION:` line — either `Phase 0 GO` with c_new, architecture,
    full-envelope margin ≥ 1e-4, or `Phase 0 NO-GO` with explicit
    rationale (e.g., "no tested architecture admits c > 356562/1000000
    with margin ≥ 1e-4; largest margin found at c = 356563/1000000 was
    +X under architecture Y").

### 3. `Scratch/sprint_089_witness.txt` (new file, conditional on GO)

If the `DECISION` is GO, also write a concise witness file containing
just the load-bearing summary that sprint 090 will consume:

```
Sprint 089 GO witness
=====================

c_new                 : <numerator>/<denominator>
architecture_new      :
  - rho_top           : <value>  (was: 999999/1000000)
  - delta_lo          : <value>  (was: 1e-6)
  - extra_mode_count  : <0..3>
  - mode count total  : <7..10>
  - window kinds      : [<branch1|modeJ_j>, ...]
  - window endpoints  : [<lo, hi>, ...]
full-envelope margin  : <value>  (≥ 1e-4)
verification envelope : (dps=80, n_trunc=300)
```

If the `DECISION` is NO-GO, do not write `sprint_089_witness.txt`;
instead, append a `Forward direction` block to the `.txt` log
suggesting the next-best architectural angle to pursue.

### 4. NOT modified

  * `Scratch/sprint_087_*.{py,txt}` (sprint 087's witness; read-only).
  * Any `Candidates/V<N>.lean` (no candidate ships this sprint; V66
    stays at 356562/1000000).
  * `Numerical_Library/` (no new wrappers; sprint 090's job if GO).
  * `lemma.toml` (no new oracle rows; sprint 090's job if GO).
  * `Proof/Reduction.lean` (no new axiom declarations; sprint 090's
    job if GO).
  * Any `Candidates/V<N>/` derived-theorem file.
  * `KorenblumPaper/` (read-only).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * `Proposals/` (no proposal filed).
  * `Bulletin.md`, `Experience.md` — append one row each per the
    standard pattern naming the sprint, the GO/NO-GO outcome, the
    Scratch artifacts, and the forward direction.

## Acceptance criteria

1. `Scratch/sprint_089_adaptive_seven_window_mass_sweep.py` exists,
   runs to completion under `python3` (mpmath available), and emits
   the full table to stdout in deterministic order.

2. `Scratch/sprint_089_adaptive_seven_window_mass_sweep.txt` exists
   and contains the DECISION line as the last non-empty line of the
   file.

3. The DECISION line is one of:
   - **`Phase 0 GO`** with explicit `c_new ∈ ℚ` strictly greater than
     `356562/1000000`, an explicit architecture record (rho_top,
     delta_lo, box-split locations, extra_mode_count), and a
     full-envelope margin (re-verified at `(dps, n_trunc) = (80, 300)`)
     **strictly greater than `1e-4`**.
   - **`Phase 0 NO-GO`** with explicit rationale: for each of
     directions (1)-(4), the maximum incremental margin gain
     observed; for the c-sweep under the best architecture, the
     largest c with margin ≥ 1e-4 (which must equal `356562/1000000`
     for NO-GO to be the correct decision; if any tested architecture
     yields `c > 356562/1000000` at margin ≥ 1e-4, the decision must
     be GO).

4. If `DECISION = GO`, `Scratch/sprint_089_witness.txt` exists with
   the architecture summary; if `DECISION = NO-GO`, the witness file
   does not exist, and the `.txt` log instead carries a `Forward
   direction:` block at its end naming the next-best angle to
   investigate.

5. The `ρ_top` feasibility table includes K(c, ρ_top)² for at least
   four `ρ_top` values: `{1 - 10⁻⁶, 1 - 10⁻⁷, 1 - 10⁻⁸, 1 - 10⁻⁹}`.
   At least one of them must produce K² < 1 (numerically) — if all
   four are infeasible, the script must fall back to `ρ_top` values
   between V66's `1 - 10⁻⁶` and `1 - 10⁻³` to find the true
   feasibility frontier.

6. The box-split sanity check confirms invariance to within
   `< 10⁻¹⁵` of the joint-mass total, validating that the sweep code
   correctly handles the deep-band partition.

7. No Lean files are modified. `lake build
   ProofRefinement.Korenblum.Candidates.V66` continues to succeed
   (regression — should be a no-op since this sprint touches no Lean).

8. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern, naming the sprint, the GO/NO-GO outcome, the
   Scratch artifacts, the forward direction (sprint 090's tentative
   shape), and any architectural insights from the sweep.

## Out of scope

  * Push V66 by editing the live oracle row (the existing
    `h_seven_window_mass_certified_at_356562_sqrt` is reserved by
    the V66 candidate; do not touch it).
  * Write any Lean code (no new axioms, no new `Numerical_Library`
    wrappers, no `lemma.toml` rows, no `Proof/Reduction.lean` defs,
    no candidate files).
  * Ship V67. That is sprint 090's job, conditional on this sprint's
    DECISION = GO.
  * File `proposal_004` or any other proposal. The user directive
    explicitly says "Do not file proposals."
  * Trust-surface compaction (replacing `hH2_v6×` /
    `hCircleGapInt_v6×` axioms with theorems). Separate direction;
    will be revisited only after the c-push search converges.
  * Hoist V53/V54/V55/V57/V58/V60 derived theorems into `Proof/`.
    Separate direction.
  * Wang Lemma 2 / Fourier orthogonality derived theorem. Separate
    direction.
  * Touch the `lemma.toml:[seed_axioms]` registry, `[[oracles]]`
    registry, `[import_policy]`, or `[workspace_import_policy]`.
  * Touch the existing `Numerical_Library` wrappers (sprint 087's
    `certify_seven_window_mass_at_356562_sqrt` is the live oracle;
    do not modify it).
  * Run the script's verification at `(dps, n_trunc) ≠ (80, 300)`.
    The full-envelope re-verification must use `(80, 300)` to match
    the sprint 087 wrapper-target precision.

## Time budget

≤ 60 minutes runtime (Generator session); ≤ 60 minutes script
execution.

  * Read sprint 087's sweep script + sprint 087/088 contracts: 10 min.
  * Author the sprint 089 sweep script (~250 new lines on top of
    sprint 087's structure): 30 min.
  * Run the sweep at scan envelope (mp.dps = 40, n_trunc = 120): ~15
    min Python runtime (parameter sweep is wider than sprint 087's).
  * Run the full-envelope re-verification at the chosen c (mp.dps = 80,
    n_trunc = 300): ~10 min Python runtime (single c-point full
    integration).
  * Author the witness file (if GO) or the `Forward direction` block
    (if NO-GO): 5 min.
  * Append Bulletin/Experience rows: 5 min.

Total: ~75 min. Bounded for one Generator session.

## Stop conditions

  * **DECISION = GO with `c_new > 356562/1000000` and full-envelope
    margin ≥ 1e-4**: `STATUS=READY_FOR_EVALUATION`. The harness
    advances the c-ceiling search; sprint 090 picks up with the
    matching `Numerical_Library` wrapper, oracle row, and V67
    candidate.

  * **DECISION = NO-GO (no tested architecture admits `c > 356562/1000000`
    with margin ≥ 1e-4)**: `STATUS=READY_FOR_EVALUATION` (the sprint
    *succeeds* at producing a falsifiable witness, even though the
    score does not advance this sprint). The `Forward direction`
    block in the `.txt` log names the next-best angle (e.g.
    "trust-surface compaction" or "extend per-mode chain to j=8+
    structurally"). Sprint 090 picks up that direction.

  * **The script fails to run to completion** (e.g., mpmath
    convergence failure at the chosen envelope, infeasibility at all
    `ρ_top` values down to `1 - 10⁻³`, or numerical instability):
    record the obstruction at `Scratch/sprint_089_obstruction.md`
    with the exact failure point, and `STATUS=BLOCKED`. Sprint 090
    debugs the script or pivots direction.

  * **The sweep finds DECISION = GO but the full-envelope
    re-verification at `(dps, n_trunc) = (80, 300)` shows the margin
    drops below `1e-4`** (precision-loss zone): rerun the sweep at
    a higher envelope `(dps, n_trunc) = (120, 500)`; if the margin
    still drops below `1e-4`, treat as NO-GO and document the
    precision-loss zone in the `Forward direction` block.
    `STATUS=READY_FOR_EVALUATION` either way.

## Notes for the generator

  * **Read first**:
    - `Scratch/sprint_087_v38_seven_window_mass_sweep.py` (510 lines;
      this is your structural template).
    - `Scratch/sprint_087_v38_seven_window_mass_sweep.txt` (the
      table format you should mirror, including the per-window
      detail block and the DECISION line).
    - `Sprint_Contracts/sprint_087_v38_seven_window_mass_oracle_phase0_and_wrapper.md`
      (sprint 087 contract, for context on sprint 087's pinned
      defaults and why they were chosen).
    - `Sprint_Contracts/sprint_088_v66_seven_window_c_push_at_356562.md`
      (sprint 088 contract, for context on what V66 currently ships).
    - `Bulletin.md` lines 17-220 (the V38 architecture directive).
    - `Numerical_Library/rigorous_scalar.py` `certify_seven_window_mass_at_356562_sqrt`
      function (~190 lines, your reference for what the wrapper that
      sprint 090 will eventually write looks like; this sprint does
      *not* write the wrapper — it produces the parameter set that
      will go into it).

  * **Do NOT edit sprint 087's sweep script.** The file is sprint
    087's witness and should remain frozen. Copy the necessary
    helpers (paper_factor, paper_lambda, term_j, mode_window_mass,
    branch1_integrand, branch1_window_mass, fraction_to_mpf) into
    your new file and extend.

  * **Feasibility check is critical.** Before running the `ρ_top`
    sweep at any candidate value, check `K(c, ρ_top)² < 1`. If
    `K² ≥ 1`, `paper_lambda` returns `+inf`, and `mode_window_mass`
    silently returns 0 over that integration interval. The sweep
    must surface infeasibility explicitly with a "INFEASIBLE
    (K² ≥ 1)" annotation in the output table, not silently fall
    back to zero.

  * **Direction (3) is a sanity check, not a c-push.** Confirm the
    box-split invariance (deep-band joint mass is the same whether
    split into 1, 2, 3, or 5 Branch.one boxes). If the invariance
    fails, your sweep code has an integration bug, not a real result.
    Do not include direction (3) in the GO decision — it should be
    a dummy null direction whose passing confirms the sweep code
    is correct.

  * **Direction (4) requires care.** When replacing a boxA window
    with a mode_j window, ensure the mode_j window's `[ρ_lo, ρ_hi]`
    matches the τ_j-band exactly. The bands progress as
    `τ_j = 1 - 1/(j+1)²`:
        τ_5 = 35/36, j=5 dominates on [c·sqrt(36/35), c·sqrt(25/24)]
        τ_6 = 48/49, j=6 dominates on [c·sqrt(49/48), c·sqrt(36/35)]
        τ_7 = 63/64, j=7 dominates on [c·sqrt(64/63), c·sqrt(49/48)]
        τ_8 = 80/81, j=8 dominates on [c·sqrt(81/80), c·sqrt(64/63)]
    Direction (4) replaces boxA3 with mode5, then boxA2 with mode6,
    then a portion of boxA1 with mode7, then a smaller portion of
    boxA1 with mode8, etc.

  * **The c-sweep step size matters.** Use `1e-6` for the coarse
    sweep above 356562, then `1e-7` near the c-ceiling bracket to
    avoid skipping past the boundary. Use Python's `Fraction` for
    all c-arithmetic to avoid float drift; convert to `mp.mpf` only
    inside the integrand evaluation.

  * **Reproducibility is required.** The script must be deterministic
    (no random sampling, no nondeterministic mp routines). Pin
    `mp.mp.dps` explicitly at the start of each phase. Use
    `mp.quad` (default Gaussian quadrature) consistently — do not
    switch to `mp.quadgl` mid-sweep.

  * **If GO**: the witness file should be precise enough that sprint
    090's wrapper author can mechanically transcribe the architecture
    parameters into a new `Numerical_Library` wrapper without
    consulting the sweep script. List window endpoints as exact
    `Fraction` objects (e.g. `Fraction(999999999, 1000000000)`)
    where the wrapper will pin them as exact rationals; mark
    sqrt-pinned endpoints explicitly (e.g. `c·sqrt(25/24)`) so the
    wrapper can mirror sprint 087's sqrt-pinned style.

  * **If NO-GO**: the `Forward direction` block should name a
    concrete next sprint shape, not a vague "explore X" directive.
    Examples of acceptable forward directions:
      - "Sprint 090: extend per-mode chain to j ∈ {1, 2, 3, 4, 5, 6}
        (six-mode + zero-Branch1 architecture; no fallback band).
        Estimated headroom: <X> based on direction (4) results.
        Estimated implementation cost: 2 sessions
        (Phase 0 sweep + V67 ship)."
      - "Sprint 090: trust-surface compaction (replace `hH2_v66` and
        `hCircleGapInt_v66` with theorems consuming
        `Section2Assumptions` fields). No score push, but reduces
        V66's audit set by two free axioms."
      - "Sprint 090: hoist V53/V57/V58 derived theorems into
        `Proof/`. Tech debt; no score push."
    The Generator chooses one based on the sweep's quantitative
    findings, but does NOT spawn the sprint — that is the next
    planner's job.

  * **No new free axioms anywhere.** Per sprint scope: this is a
    pure Scratch sprint. The phrase "axiom" should not appear in
    any new file under this sprint's edits.

  * **`STATUS=READY_FOR_EVALUATION` for both GO and NO-GO outcomes.**
    A NO-GO is a *successful* sprint: it produces a falsifiable
    witness that the V38 architecture is exhausted. Do not exit
    `BLOCKED` for NO-GO — only for genuine script failures (mpmath
    crashes, infeasibility everywhere, etc.).
