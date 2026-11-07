# Sprint 087: V38 seven-window joint-mass Phase 0 sweep + certified-rational/sqrt oracle wrapper at `c = 356401/1000000`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V65.lean` (V65 stays at `c = 35646/100000` — no
candidate ships this sprint)
**Target file**: no new `Candidates/V<N>.lean` this sprint. Concrete artifacts:

  * `Scratch/sprint_087_v38_seven_window_mass_sweep.py` (+ `.txt` output) —
    high-precision Phase 0 numerical confirmation of the +1.2e-2 mass margin at
    `c = 356401/1000000` over the seven-window split (4 mode windows + 3
    Branch.one fallback boxes).
  * `Numerical_Library/rigorous_scalar.py` — new wrapper
    `certify_seven_window_mass_at_356401_sqrt` (Evaluator-facing
    zero-argument shim).
  * `lemma.toml` — new `[[oracles]]` row keying the wrapper to a Lean-facing
    axiom; new `[seed_axioms]` entry registering the axiom name.
  * `Proof/Reduction.lean` — declaration only, near the existing
    `h_two_window_mass_certified_at_35646_sqrt` declaration (or in an
    analogous neighboring file): a free `axiom
    h_seven_window_mass_certified_at_356401_sqrt` whose statement matches
    the joint-mass premise of the sprint 086 mixed-kernel reducer
    instantiated at V38's seven-window split.

**Direction**: oracle-support (Numerical_Library wrapper + oracle row + Lean
axiom statement, prerequisite for sprint 088's V38 c-push at `c = 356401/1000000`).

## Goal

Lay down all numerical and trust-surface infrastructure required to discharge
the joint-mass hypothesis of `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
(sprint 086, `Proof/Reduction.lean:8934`) at V38's c-value
`c = 356401/1000000` over the literal V38 seven-window split. Concretely:

  1. **Phase 0 numerical sweep** at high precision (mp.dps = 80, n_trunc = 300)
     reproducing V38's audited total mass `1.000012381570` at `c = 356401/1000000`
     with the seven-window split

         fallbackA  : single Branch.one window spanning boxes 0000..0003
         mode4      : per-mode window with j* = 4
         fallbackB  : single Branch.one window (box 0006)
         mode3      : per-mode window with j* = 3
         fallbackC  : single Branch.one window (box 0012)
         mode2      : per-mode window with j* = 2
         mode1      : per-mode window with j* = 1   (covers ρ ≥ √(4/3)·c)

     Box endpoints regenerated from the V38 `export_mode_hybrid_boxes`
     algorithm (the algorithm is described in the Bulletin lines 91-136 and
     the export-style sketched there; do **not** import V38's experiments
     file — rerun the export logic in this sweep script). The script must
     output, beside the per-window mass and total margin, the full list of
     window endpoints in mp/Fraction form so sprint 088 can paste them into
     the V66 candidate verbatim.

  2. **Numerical_Library wrapper** `certify_seven_window_mass_at_356401_sqrt`
     pinning V38's exact endpoints (sqrt-pinned for the four mode windows at
     τ-breakpoints `τ_j = 1 - 1/(j+1)²`, exact-rational for the three
     Branch.one fallback windows) and certifying joint mass ≥ 1 + 10^(-30)
     under the upgraded envelope `(dps, n_trunc) = (80, 300)`. Sibling of
     `certify_two_window_mass_at_35646_sqrt` (`rigorous_scalar.py:1330`).

  3. **`[[oracles]]` row + `[seed_axioms]` entry** in `lemma.toml` keying the
     wrapper to a new Lean-facing axiom name
     `h_seven_window_mass_certified_at_356401_sqrt`. The pattern is identical
     to sprint 083's sqrt-endpoint sibling row (`lemma.toml:325-330`).

  4. **Lean-facing `axiom` declaration** in `Proof/Reduction.lean` (free
     workspace axiom, not bundled into `Section2Assumptions`) whose
     statement matches the **kind-dispatched joint-mass hypothesis** of
     `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` instantiated
     at V38's seven-window split.

V66 (the V38 c-push candidate) does **not** ship this sprint. Sprint 088
ships V66 by composing this sprint's oracle row with sprint 086's mixed
reducer.

## Why

### Why this is the right next sprint

Sprint 086 shipped the mixed-kernel multi-window reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`
(`Proof/Reduction.lean:8934`). The reducer accepts a `kind : Fin (n+1) →
KernelKind` per-window tag and discharges per-mode windows via
`OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
and Branch.one fallback windows via `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae`
(itself the standalone Branch.one a.e.-`Icc` lift wrapper shipped in
sprint 086). The structural piece for V38's seven-window c-push is now in
place.

The **+1.2e-2 V64 → V38 c-push** (from `c = 35646/100000` to
`c = 356401/1000000`) is the Bulletin's standing prize, two and a half
orders of magnitude larger than the +1e-5 V52 → V64 push. Per the
Bulletin's V38-explicit directive (`Bulletin.md:17-419`), V38's audited
mass at this c is `1.000012381570`, well above the strict-margin floor.

The remaining gap before V66 can ship is **the joint-mass numerical
discharge**. The mixed reducer requires a hypothesis of shape

```
1 ≤ ∑ i : Fin 7, ∫ ρ in (ρStart i)..(ρStop i), modeIntegrand_w ρ
```

where `modeIntegrand_w ρ` is one of `ModeBridge.scalarIntegrand c j …`
(per-mode kind) or `Korenblum.scalarIntegrand1 c …` (Branch.one kind).
This sprint produces the certified-rational/sqrt oracle that discharges it
at V38's c.

### Why this is bounded for one session

The Phase 0 sweep, the wrapper, and the lemma.toml entry follow sprint 083's
template byte-for-byte except in three places: number of windows (7 instead
of 2), inclusion of Branch.one fallback windows, and the
`export_mode_hybrid_boxes` regeneration logic. Concretely:

  * **Phase 0 sweep**: ~250 lines of Python following
    `Scratch/sprint_083_sqrt_endpoint_witness.py` template plus the
    box-export logic (which is a pure NumPy / mpmath sweep over the
    `H(c, ρ)`-dominated Wang-eq(5) box construction; the algorithm is
    inlined in the Bulletin lines 91-136). Runtime under 5 minutes at
    `(dps, n_trunc) = (80, 300)` on a single core.

  * **Wrapper**: ~200 lines mirroring `certify_two_window_mass_at_35646_sqrt`
    (`rigorous_scalar.py:1330-1450`). Per-window mass via
    `_two_window_mass_window` (already exists for per-mode kind) + a new
    `_branch1_window_mass` helper (~50 lines, integrand
    `2ρ / (Korenblum.scalarIntegrand1 ρ inverse · Λ(c, ρ))` — actually the
    integrand is `2ρ · scalarIntegrand1(c, Λ, ρ)` directly, see
    `KorenblumPaper.WangPaperSideConditions` for the explicit formula
    and `valid_of_eq5_eq8_eq9_subinterval_branch1` body for the integrand
    ordering). The total is the sum of three `_branch1_window_mass`
    calls and four `_two_window_mass_window` calls.

  * **lemma.toml row**: ~30 lines following the sprint 083 pattern.

  * **Lean axiom statement**: ~30 lines. Free `axiom` declaration with the
    kind-dispatched sum integral matching the mixed reducer's joint-mass
    field. **No proof body** — the axiom is discharged at evaluation time
    by the registered oracle.

Total: ~510 lines. Comparable to sprint 083 (~470 lines) and sprint 079
(~400 lines). Bounded for one session.

### Why this is not just "trust a witness" — the trust surface

All trust additions in this sprint are **oracle-shaped**, not free axioms in
the structural-trust sense. The Lean axiom
`h_seven_window_mass_certified_at_356401_sqrt` is registered in
`[seed_axioms].allowed`, and its truth is contingent on the registered
`[[oracles]]` row pointing at
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356401_sqrt`.
The Evaluator's `run_oracle_checks` at candidate evaluation time invokes
the wrapper, which recomputes the joint mass at the pinned endpoints with
the upgraded envelope and refuses to certify (raises `RuntimeError`) if
the strict-margin floor is not met. This is the same discipline as the
existing two-window mass oracles (sprints 079, 083) and the eq15 oracle
cascade (sprints 053-059) — see `lemma.toml:285-330` for the matching
patterns.

The `[seed_axioms]` entry is **not** a fresh paper-axiom expansion; it is the
Lean-facing handle on a registered oracle's certified return value, exactly
as `h_two_window_mass_certified_at_35646_sqrt` was shipped in sprint 083.
No `Proposals/` filing is needed (per `Proposals/README.md` "Do not use a
proposal for … new oracle registry entries that are already fully specified
and directly consumed by the current sprint" plus the next sprint).

### Why the +1.2e-2 margin is well above the precision threshold

The Bulletin's strict scan bracket (`Bulletin.md:112-117`) is

    c = 0.356401  →  total mass = 1.000012381570  ✓ ships
    c = 0.356402  →  total mass = 0.999989183931  ✗ falls short

So the margin at V38's c is `+1.2381570e-5`, **not** the +1.2e-2 the user
mentioned in the recent context's framing. The +1.2e-2 number conflated the
*c-push gap* (V64's `0.35646` → V38's `0.356401`, gap = `+1.2e-2` in c-units
… wait, that's wrong too: `0.356401 - 0.35646 = +1.41e-4`, also not 1.2e-2).
Actually the V64 score is `35646/100000 = 0.35646`; V38's c is `356401/
1000000 = 0.356401`. Gap is `0.356401 - 0.35646 = +0.000001`? No:
`0.356401 - 0.35646 = 0.356401 - 0.356460 = -0.000059`. **V38's c is
*smaller* than V64's score**.

**Important Phase 0 reality check.** The harness's V64 score is
`c = 35646/100000 = 0.35646` (`Bulletin.md` audit row, sprint 083 evaluator
log). V38's c is `356401/1000000 = 0.356401`. So `c_V38 < c_V64` by
~6×10⁻⁵. The +1.2e-2 framing in the recent context message is **incorrect**;
the V38 c-push relative to V64 is actually a **regression in c**, not a
+1.2e-2 push.

This radically reframes the sprint chain. **Sprint 087 (this) and sprint
088 are NOT the right next move** if the only "V38 prize" they can ship
is `c = 0.356401 < c_V64 = 0.35646`. A candidate at V38's c would tie or
fail the score gate (`c_value > V_prev`), not push it.

The genuine question is: does V38's seven-window split work at
`c = 0.356460` or higher (V64's c or above)? The Bulletin's strict scan
bracket at V38's parameters answers the c=0.356401/0.356402 question but
**says nothing about `c ≥ 0.35646`**, where V64 is.

**Sprint 087's revised goal therefore folds Phase 0 into a sweep that scans
upward from V64's c**, not just at V38's pinned c, to find the largest c at
which the V38 seven-window split has joint mass ≥ 1. If the sweep returns
the max c at, say, `c = 0.35646 + 4e-5 = 0.35650`, then sprint 088 ships
V66 at that c with a +4e-5 score push (not +1.2e-2). If the sweep returns
no c above V64's `0.35646`, the V38 seven-window route does not produce a
score push relative to V64, and sprint 088 is replaced by a sibling
exploration sprint (e.g. an eight-window split with one extra mode).

This is exactly the "use Scratch first" discipline the Bulletin requires
(`Bulletin.md:638-650`): **do not commit to oracle infrastructure for V38's
nominal c without verifying it actually beats V64's c**.

### Three (and more) distinct directions considered (and why this one wins)

1. **Direction A (this sprint): Phase 0 c-sweep + V38 seven-window oracle
   wrapper + lemma.toml row + Lean axiom statement, with the c-sweep
   redirected to scan c ≥ V64's `0.35646` rather than just verifying V38's
   pinned `0.356401`.** Strongest objection: the recent context framing
   suggests a +1.2e-2 push that does not arithmetically exist relative to
   V64. Counter: the sprint's value is NOT the +1.2e-2 framing; it is the
   genuine c-sweep that determines whether the V38 seven-window architecture
   actually ships above V64's c. If yes → sprint 088 ships V66 at the
   sweep-determined c with the registered oracle. If no → sprint 088 pivots
   to an eight-window or per-mode-finer split. **Either outcome is forward
   progress.** The Phase 0 sweep itself produces the actionable signal.

2. **Direction B: Sibling c-push along the m=2 axis at
   `c = 35647/100000` or `c = 35650/100000`.** Strongest objection: capped
   at +9e-5 over V64's `0.35646` per sprint 078's m=2 ceiling at
   `c ≈ 0.35654` (margin 4.2e-5 there). Numerical-only headroom; analytic
   chain is already shipped. **Demoted as marginal score gain** that would
   eat one session of budget for ≤9e-5 c-push, while Direction A's c-sweep
   answers the strictly bigger question of whether the V38 architecture
   beats V64 at all.

3. **Direction C: Build a Wang-eq(5) Branch.one box-sum mass certifier
   (`WangBoxQ.totalMassQ Branch.one cQ boxes` adapter) so V38's `fallbackA`
   can be discharged as a literal four-box box-sum rather than as a single
   Branch.one window with mass = single integral over the box-span.**
   Strongest objection: V38 itself ships fallbackA as `box-sum of branch1
   boxes 0000..0003`, and the box-sum integral over a *contiguous* span
   equals the Riemann integral over the span; a single-window treatment with
   `mass = ∫_{ρ_box0_lo..ρ_box3_hi} scalarIntegrand1 dρ` is mathematically
   equivalent **only if the four boxes are contiguous** (no gaps). If V38's
   boxes 0000..0003 are *contiguous*, then the single-window treatment is
   strictly cleaner — no new adapter is needed. **The Phase 0 sweep
   resolves this**: the script must report whether the boxes are contiguous;
   if yes, the single-window treatment ships in this sprint; if no, sprint
   087 falls back to ship a 10-window split (4 boxes + 3 modes + 3 fallback
   modes — wait, actually 4 fallback boxes + 3 mode windows = 7 still, but
   with fallbackA expanded into 4 separate Branch.one windows). **This
   subsumes into Direction A** — the sweep determines the window count.

4. **Direction D: Hoist V53-V60 derived theorems into `Proof/`.** Pure
   cleanup; no path to V38's c. **Demoted as deferrable cleanup.**

5. **Direction E: File `proposal_004` to migrate `hH2_v64`/`hCircleGapInt_v64`
   into `Section2Assumptions`.** Per the proposal-filing checklist
   (`AGENT_BRIEF.md` is silent on this; the planner agent definition's
   four-condition guide governs): no "tried hard and failed" attempt sprint
   exists, no path to a c-push. **Demoted.**

6. **Direction F: Split sprint 087 into 087a (Phase 0 sweep only) and 087b
   (wrapper + oracle row + Lean axiom).** Strongest objection: the wrapper
   and oracle row are 30-line templates over the Phase 0 endpoints, and
   gating the wrapper on the sweep result is a one-line conditional. Folding
   them into one sprint preserves the linear progression (Phase 0 +
   wrapper + axiom = one sprint, one Scratch script, one lemma.toml diff,
   one Lean axiom). **Demoted as over-fragmenting.**

Direction A wins on **expected analytical novelty per bounded-Generator-
session**: it is the smallest piece that materially answers the
"does V38's split push c above V64?" question. If the sweep answers yes,
sprint 088 ships V66 at that c immediately. If no, sprint 087 still produces
a value: the c-bracket where the V38 split first fails, which informs the
next planner's choice of split shape (eight windows? finer-mode split? …).

### Why folding Phase 0 into the wrapper sprint is correct

The Bulletin's "Use Scratch first" discipline (`Bulletin.md:638-650`) requires
a Phase 0 confirmation **before** Lean. This sprint satisfies it: the Phase 0
sweep (concrete edit §1) runs first, the wrapper (§2) and lemma.toml entry
(§3) are then templated on the sweep's certified endpoints, and the Lean
axiom (§4) is a 30-line shim. If the sweep fails to find a c above V64's
`0.35646` with margin ≥ 10⁻⁴, the sprint **must not** ship the wrapper at a
losing c; instead the sweep output documents the failure and the sprint
exits BLOCKED with a precise "no c above V64 satisfies the seven-window
split at margin ≥ 10⁻⁴" obstruction note in `Scratch/sprint_087_obstruction.md`.

## Concrete edits expected

### 1. `Scratch/sprint_087_v38_seven_window_mass_sweep.py` (+ `.txt`)

A self-contained mpmath script. Required outputs in the `.txt`:

  * **Box-export reproduction.** For each candidate `c` in a sweep set
    (see below), regenerate the Wang-eq(5) Branch.one fallback boxes from
    the V38 algorithm. The algorithm is: starting at `ρ = c + ε`, at each
    step compute the breakpoint where the supremum-of-modes function
    `H(c, ρ)` switches from one fixed mode to the next, place a fallback
    box on the `(j → j-1)` mode-transition pocket where `H(c, ρ)`'s
    derivative is steepest (i.e. where Wang's eq (5) singular factor
    `1/(ρ²-c²)` dominates the per-mode envelope). The exact box-placement
    rule is the one used by V38; if the sweep cannot replicate V38's
    boxes 0000, 0003, 0006, 0012, the script reports the discrepancy
    and falls back to a uniform-grid placement with comparable density
    (~10 boxes between `c` and `√(4/3)·c`, then take the min-mass subset
    that closes the +1.2e-5 gap V38 reports).

    Concretely the script must produce, in `.txt` and as a Python literal
    in `.py`:
    - `box_endpoints : List[Tuple[Fraction, Fraction]]` for each fallback
      window;
    - `mode_endpoints : List[Tuple[Fraction, Fraction]]` for each per-mode
      window (using **exact rational** endpoint `ρ_j(c) = c · √(τ_{j-1}/τ_j …)`
      where the `√` enters; or, if the mode endpoint must be irrational,
      the corresponding **rational `τ_j` breakpoint** so the candidate-side
      proof can use polynomial inequalities `τ_{j-1} · ρ² ≤ c² ≤ τ_j · ρ²`
      without explicitly naming the irrational endpoint);
    - the per-window mass and the joint-mass total at each swept `c`;
    - the certified margin `total - 1` to 30 decimal digits.

  * **Sweep set.** At minimum, `c ∈ {0.35646, 0.356465, 0.35647, …,
    0.35654, 0.356545, 0.35655, …, 0.35660, 0.35661}`. The sweep must
    bracket the largest c at which joint mass `≥ 1 + 10⁻⁴` (so the wrapper's
    `dps=80`-floor `10⁻³⁰` is comfortably exceeded). The expected outcome,
    given V38's `c = 0.356401` mass `1.000012381570`, is that the seven-
    window split has a *narrow* margin curve and the c-ceiling sits between
    V64's `c = 0.35646` and V38's `c = 0.356401`. **If the c-ceiling is
    below V64's c, the sweep documents this and the sprint exits BLOCKED**
    (Stop conditions §3).

  * **Precision.** `(mp.dps, n_trunc) = (80, 300)`. The strict-margin floor
    in the wrapper's certification is `10^(-min(dps, 30)) = 10⁻³⁰`. The
    Phase 0 GO floor is `10⁻⁴` (margin > 0.0001 → safe).

  * **Algebraic τ-breakpoint sanity.** Confirm at the chosen pinned mode
    endpoints `ρ_j² = c² / τ_j` exactly (delta = 0), per sprint 083's
    pattern (`Scratch/sprint_083_sqrt_endpoint_witness.txt:14-20`).

  * **Structural ordering checks.** For the seven-window partition,
    `c < ρ_box0_lo`, all `ρ_box_hi ≤ ρ_mode_lo` and `ρ_mode_hi = ρ_next_box_lo`
    (or strict `≤` with measure-zero gaps that do not affect the integrals),
    `ρ_mode_lo[mode4] ≤ … ≤ ρ_mode_hi[mode1] ≤ 1`. Match the pattern from
    `Scratch/sprint_083_sqrt_endpoint_witness.txt:22-26`.

  * **DECISION line.** As in sprint 083: `DECISION: Phase 0 GO` if the
    chosen c (≥ V64's `0.35646`) gives margin ≥ 10⁻⁴; otherwise
    `DECISION: Phase 0 NO-GO` with the c-ceiling reported.

### 2. `Numerical_Library/rigorous_scalar.py`

Add **after** `certify_two_window_mass_at_35646_sqrt` (around
`rigorous_scalar.py:1450`):

```python
def _branch1_window_mass(
    c_mp,
    rho_lo_mp,
    rho_hi_mp,
    n_trunc: int,
):
    """
    Phase 0 helper: certified upper-bound mass of one Branch.one fallback
    window via mp.quad on the Wang-eq(5) scalar-integrand-1 density:

        mass := ∫_{rho_lo..rho_hi} 2ρ · scalarIntegrand1(c, Λ(c, ρ), ρ) dρ

    where `scalarIntegrand1` is the Korenblum eq(5) kernel
    (see `KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1`).
    """
    # exact integrand body — mirror the per-mode `_two_window_mass_window`
    # template; consult KorenblumPaper.WangPaperSideConditions for the
    # closed-form integrand.
    ...

def certify_seven_window_mass_at_356401_sqrt() -> Fraction:
    """
    Sprint 087 zero-argument Evaluator-facing shim for
    ``h_seven_window_mass_certified_at_356401_sqrt``.

    Pins V38's seven-window split at the sweep-determined c (see
    Scratch/sprint_087_v38_seven_window_mass_sweep.txt for the sweep output;
    the c committed here is the largest c ≥ V64's `0.35646` at which the
    sweep reports margin ≥ 10⁻⁴). Endpoints:
      c = <pinned by sweep>
      mode4: [ρ_4_lo, ρ_4_hi] = sqrt-pinned via τ_4 = 24/25, τ_3 = 15/16
      mode3: [ρ_3_lo, ρ_3_hi] = sqrt-pinned via τ_3, τ_2 = 8/9
      mode2: [ρ_2_lo, ρ_2_hi] = sqrt-pinned via τ_2, τ_1 = 3/4
      mode1: [ρ_1_lo, ρ_1_hi] = sqrt-pinned via τ_1, ρ_top = 999999/1000000
      fallbackA: [ρ_fA_lo, ρ_fA_hi] = exact rationals (Phase 0 box-export)
      fallbackB: [ρ_fB_lo, ρ_fB_hi] = exact rationals
      fallbackC: [ρ_fC_lo, ρ_fC_hi] = exact rationals
      (dps, n_trunc) = (80, 300)
    """
    dps = 80
    n_trunc = 300
    c = Fraction(<numerator>, <denominator>)  # pinned by sweep
    # ... per-window mass calls
    # ... strict-margin check matching certify_two_window_mass_at_35646_sqrt
    # body pattern
    ...
    return Fraction(1, 1)
```

The c-numerator/denominator are filled in from the Phase 0 sweep's
DECISION-line c. If the sweep reports c-ceiling below V64's `0.35646`, the
wrapper is **not** added (Stop conditions §3).

### 3. `lemma.toml`

Add:

```toml
[[seed_axioms.allowed]]  # actually a string entry in the list
# add "h_seven_window_mass_certified_at_356401_sqrt" to the existing
# [seed_axioms].allowed list (currently lemma.toml:53-141; insert
# after "h_two_window_mass_certified_at_35646_sqrt" with a sprint-087
# header comment block matching the sprint 083 pattern at lines 127-141).

[[oracles]]
axiom = "h_seven_window_mass_certified_at_356401_sqrt"
bound_field = "seven_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_seven_window_mass_at_356401_sqrt"
```

The `bound_field = "seven_window_mass_lower"` is the candidate-side `def`
that sprint 088's V66 will declare (`def seven_window_mass_lower : ℝ := 1`),
matching the existing `two_window_mass_lower` pattern.

The seed_axioms header comment must follow the format of sprint 083's
header (`lemma.toml:127-141`) — pin the c, sweep witness file, margin, and
oracle envelope.

### 4. `Proof/Reduction.lean`

Add at the bottom (immediately after the sprint 086 reducer at
`Reduction.lean:8934`-end), matching sprint 083's free-axiom pattern from
`hH2_v64` / `hCircleGapInt_v64`:

```lean
/--
Sprint 087: Lean-facing handle on the registered oracle
`h_seven_window_mass_certified_at_356401_sqrt`. The `axiom` body asserts
the kind-dispatched joint-mass hypothesis at V38's seven-window split,
discharged by `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356401_sqrt`
at evaluator-time per `lemma.toml:[[oracles]]`.

The statement matches the kind-dispatched joint-mass field of
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` (sprint 086)
instantiated at `c = <sweep-pinned c>`, with the seven-window endpoint
data baked into the statement as exact rationals or polynomial-`τ`
characterizations.

This is a free workspace axiom (not a `Section2Assumptions` field) and is
discharged by the registered oracle. Sprint 088 will consume this axiom
inside V66's `h_witness` to discharge the joint-mass premise of the
mixed reducer.
-/
axiom h_seven_window_mass_certified_at_356401_sqrt :
    -- statement shape (parameter names may vary):
    (1 : ℝ) ≤
      ∑ i : Fin 7,
        match (<kind function for V38's split> : Fin 7 → KernelKind) i with
        | KernelKind.modeJ j =>
          ∫ ρ in (<ρStart i>)..(<ρStop i>),
            ModeBridge.scalarIntegrand
              ((<sweep-pinned c numerator> : ℝ) / (<denominator> : ℝ))
              j (WangOuter.paperLambda (<K placeholder>) <c>) ρ
        | KernelKind.branch1 =>
          ∫ ρ in (<ρStart i>)..(<ρStop i>),
            Korenblum.scalarIntegrand1 <c>
              (WangOuter.paperLambda (<K placeholder>) <c>) ρ
```

The exact statement shape depends on (a) whether the candidate-side V66 will
declare a single `c_value` constant and (b) whether the kind function and
endpoint data are parameterized as a single `def` or fully spelled out in the
axiom. The cleanest pattern is the one used by `h_two_window_mass_certified_at_35646_sqrt`
(grep its declaration in the workspace for the exact shape, including how
`ρ_start`/`ρ_stop` rationals are baked in). Follow that pattern.

If the cleanest formulation requires a small sprint-087-only helper `def`
exposing the V38 seven-window endpoint data (e.g. `def
v38SevenWindowEndpoints : Fin 7 → ℝ × ℝ` and `def v38SevenWindowKinds : Fin 7
→ KernelKind`), introduce them in `Proof/Reduction.lean` immediately above
the axiom; do not place them in `KorenblumPaper/`.

### 5. NO edits to

  * `KorenblumPaper/` (read-only paper surface).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Any V0-V65 candidate file.
  * Any per-candidate derived-theorem file under `Candidates/V<N>/`.
  * The existing
    `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` body
    (sprint 086's deliverable).
  * The existing `valid_of_perMode_multiWindow_tau_partition_eq8_eq9` body
    (sprint 084's deliverable).
  * The existing `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` body
    (sprint 078's deliverable; load-bearing for V64/V65).
  * The existing `valid_of_eq5_eq8_eq9_subinterval_branch1` body (sprint
    019/085's deliverable).
  * The existing `pointwise_branch1_on_Ioo_eq5_eq8_eq9` body (sprint 085's
    deliverable).
  * The existing `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae` body (sprint
    086's deliverable).
  * The existing two-window mass oracle entries in `lemma.toml`
    (sprints 079, 083).
  * `Proposals/`.
  * `[workspace_import_policy]` or `[import_policy]` (the new axiom and
    helper `def`s live in already-allowed `Proof/Reduction.lean`).

### 6. Bulletin.md and Experience.md append

Append one row each documenting:

  * The new oracle `h_seven_window_mass_certified_at_356401_sqrt` (or the
    sweep-pinned c, if Phase 0 ceilings c below V38's nominal), the
    Phase 0 sweep witness file, the chosen c, the certified margin, and
    the strict-margin floor.
  * The Phase 0 c-sweep result (the c-ceiling found, with the per-c margin
    table). **This is the most important experience entry**: it pins the
    V38 architecture's actual c-headroom relative to V64's `0.35646`.
  * Forward direction: sprint 088 ships V66 at the sweep-pinned c using
    the new oracle to discharge the joint-mass premise of the sprint 086
    mixed reducer; V66 also exports `def seven_window_mass_lower : ℝ := 1`.
    If Phase 0 ceilings c below V64, sprint 088 instead pivots to an
    alternative split (e.g. eight-window with one extra fallback box, or
    finer mode split with j*=5/4/3/2/1).

## Acceptance criteria

1. `Scratch/sprint_087_v38_seven_window_mass_sweep.py` exists, runs to
   completion under (mp.dps, n_trunc) = (80, 300), and writes
   `Scratch/sprint_087_v38_seven_window_mass_sweep.txt`.

2. The `.txt` output contains, at minimum:
   - the seven-window endpoint data (4 mode windows + 3 fallback boxes,
     exact rationals or `(num, den)` Fraction pairs);
   - the per-window mass at each swept c;
   - the joint mass total and `(total - 1)` margin to 30 decimal digits;
   - the structural ordering and τ-breakpoint sanity checks (matching
     sprint 083's witness format);
   - a `DECISION: Phase 0 GO` line at the chosen c if margin ≥ 10⁻⁴, with
     the chosen c reported as `(num, den)` Fraction.

3. **If Phase 0 reports c-ceiling ≥ V64's `0.35646`**:
   - the wrapper `certify_seven_window_mass_at_356401_sqrt` is added to
     `Numerical_Library/rigorous_scalar.py` and runs to True under the
     pinned envelope and endpoints (verifiable by importing and calling
     the function — it should return `Fraction(1, 1)`);
   - the `[[oracles]]` row is added to `lemma.toml` and the new axiom
     name is added to `[seed_axioms].allowed`;
   - the `axiom h_seven_window_mass_certified_at_356401_sqrt` declaration
     is added to `Proof/Reduction.lean`;
   - `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds;
   - `lake build ProofRefinement.Korenblum.Candidates.V65` still succeeds
     (regression: V65 must remain at `35646/100000`).

4. **If Phase 0 reports c-ceiling < V64's `0.35646`**:
   - the wrapper is **not** added; the lemma.toml entry is **not** added;
     the axiom is **not** added.
   - `Scratch/sprint_087_obstruction.md` is written precisely naming
     the c-ceiling found, the per-c margin table, and the recommended
     pivot (eight-window, finer mode split, etc.).
   - `STATUS=BLOCKED`.

5. `Bulletin.md` and `Experience.md` each gain one row per the standard
   pattern, naming the Phase 0 c-ceiling, the chosen c (or NO-GO
   verdict), the new oracle (or absence thereof), the new Lean axiom
   (or absence thereof), and the forward direction toward sprint 088.

6. Evaluator regression check on V65:
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V65.lean` reports `pass: true`
   with `score = 35646/100000` and the `axioms_used` set byte-for-byte
   identical to the previous V65 audit. The new `[seed_axioms]` entry
   does not leak into V65's audit because V65 does not import the new
   axiom.

## Out of scope

  * Ship `Candidates/V66.lean` at any c. V66 is sprint 088's job.
  * Push V65's `c_value`. V65 stays at `35646/100000`.
  * Build a Wang-eq(5) Branch.one **box-sum** mass *adapter* in Lean
    (`WangBoxQ.totalMassQ Branch.one cQ boxes` ↔ integral identity). The
    Phase 0 sweep treats fallback windows as single integrals over the
    box-span; if V38's boxes 0000..0003 are non-contiguous, the Phase 0
    output documents this and sprint 088 may need a per-box-window
    discharge — but that adapter is not built this sprint.
  * Edit `KorenblumPaper/` or any sprint 084/085/086 deliverable.
  * File `proposal_004` (deferred to sprint 089+).
  * Hoist V53/V54/V55/V57/V58/V60 derived theorems (deferred cleanup).
  * Build a Lean tactic that reduces the `axiom`'s body to closed-form
    rationals via `norm_num` (the axiom is *intentionally* free; its
    truth is grounded in the registered oracle's wrapper).
  * Migrate `hH2_v64` / `hCircleGapInt_v64` into `Section2Assumptions`.

## Time budget

≤ 150 minutes runtime.

  * Phase 0 sweep script: ~30 minutes to write + ~10 minutes to run.
  * Wrapper: ~30 minutes to write + ~5 minutes to validate via direct
    Python invocation.
  * lemma.toml entry: ~10 minutes.
  * Lean axiom statement: ~30 minutes (including matching the mixed
    reducer's joint-mass field shape).
  * Bulletin/Experience appends: ~10 minutes.
  * Evaluator regression check on V65: ~5 minutes.

## Stop conditions

  * **Phase 0 c-ceiling ≥ V64's `0.35646`, all wrapper/lemma.toml/axiom
    artifacts shipped, V65 regression still passes**:
    `STATUS=READY_FOR_EVALUATION`. The harness has the numerical oracle
    and Lean axiom in place; sprint 088 ships V66 at the sweep-pinned c.

  * **Phase 0 c-ceiling < V64's `0.35646`**: the V38 seven-window split
    does not push c above V64. **No wrapper, no lemma.toml row, no Lean
    axiom is shipped**, but `Scratch/sprint_087_v38_seven_window_mass_sweep.{py,txt}`
    is shipped (with the NO-GO verdict and per-c margin table). Write
    `Scratch/sprint_087_obstruction.md` with the c-ceiling, the recommended
    pivot direction (e.g. eight-window with one extra fallback box,
    finer mode split with j*=5/4/3/2/1, sibling m=2 c-push along sprint
    078's axis, …), and a one-paragraph numerical justification.
    `STATUS=BLOCKED`.

  * **Phase 0 c-ceiling ≥ V64's c but the wrapper or oracle row addition
    breaks `lake build` of `Proof.Reduction` or breaks V65's regression**:
    revert the wrapper / lemma.toml diff (keep the Phase 0 sweep), document
    the build failure precisely at `Scratch/sprint_087_obstruction.md`, and
    `STATUS=BLOCKED`. Sprint 088 picks up with a partial-state pickup
    contract.

  * **Phase 0 sweep cannot reproduce V38's box-export algorithm and the
    fallback uniform-grid placement does not close the +1.2e-5 gap V38
    reports** (i.e. the script reports a *much* lower margin or NO-GO at
    V38's pinned `c = 0.356401` itself): document precisely at
    `Scratch/sprint_087_obstruction.md` (this is a serious finding — it
    means either the Bulletin's V38 reference numbers are wrong, or the
    box-export algorithm has a non-obvious tuning step). `STATUS=BLOCKED_NEEDS_HUMAN`.

  * **A new free-floating axiom or trust-base expansion beyond
    `[seed_axioms]` + `[[oracles]]` would be required**: do not ship it.
    Document at `Scratch/sprint_087_obstruction.md` and
    `STATUS=BLOCKED_NEEDS_HUMAN`. (Highly unlikely — the `[[oracles]]`
    pattern is fully templated by sprints 079, 083.)

## Notes for the generator

  * **Read first**:
    - `Scratch/sprint_083_sqrt_endpoint_witness.{py,txt}` — your Phase 0
      template, byte-for-byte except for the seven-window expansion and
      the c-sweep loop.
    - `Numerical_Library/rigorous_scalar.py:1330-1450` — your wrapper
      template, byte-for-byte except for the seven-window expansion and
      the c-pinned values from the sweep.
    - `lemma.toml:127-141` and `lemma.toml:285-330` — your `[seed_axioms]`
      header and `[[oracles]]` row templates.
    - `Proof/Reduction.lean:8825-8934` (the sprint 086 mixed reducer) —
      the joint-mass field shape your Lean axiom must match.
    - `Bulletin.md:91-136` — the V38 seven-window split's literal
      endpoints and box-export algorithm description. **These are the only
      external numbers you need; do not consult sibling proof-search
      directories**.
    - `Bulletin.md:112-117` — V38's strict scan bracket; read carefully.
      Note that V38's `c = 0.356401` is **smaller** than V64's
      `c = 0.35646`. The Phase 0 c-sweep must determine whether V38's
      seven-window split pushes c above V64 at all.

  * **The `+1.2e-2` framing is wrong** (see "Why this is bounded for one
    session"); the genuine c-question is whether the seven-window split
    works at any c ≥ V64's `0.35646`. Phase 0's job is to answer this.
    Do not commit oracle infrastructure to V38's nominal `c = 0.356401`
    without verifying the c-sweep.

  * **mode endpoints are sqrt-pinned**, not rational, at the τ-breakpoints.
    The wrapper must use `mp.sqrt(rational_τ_ratio)` for the four mode
    endpoints, exactly as sprint 083's wrapper uses `c · mp.sqrt(9/8)`
    and `c · mp.sqrt(4/3)`. The three fallback box endpoints are exact
    rationals (regenerate them via the Phase 0 box-export logic).

  * **For the Lean axiom statement**: match the kind-dispatched joint-mass
    field of `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9`.
    Do not invent a new shape — copy the exact `1 ≤ ∑ i, match kind i …`
    cell from the sprint 086 reducer's signature and pin the data.

  * **Generator capability budget**: ~510 lines across the four artifact
    classes. If the wrapper exceeds 250 lines, you are probably duplicating
    `_two_window_mass_window` and `_branch1_window_mass`; refactor.
    If the Lean axiom statement exceeds 60 lines, the kind function or
    endpoint data should be lifted to a sprint-087 helper `def` in
    `Proof/Reduction.lean`.

  * **Phase 0 c-sweep loop body**: for each c in the sweep set, regenerate
    the box endpoints (since they depend on c), recompute all seven window
    masses, and report the margin. The sweep is parallelizable but a
    single-core run at `(dps, n_trunc) = (80, 300)` should complete in
    under 10 minutes for a sweep set of ~30 c values.

  * **No new files in `Proof/`** unless the helper `def`s are large enough
    to warrant a per-sprint file; the cleaner shape is to add them to
    `Proof/Reduction.lean` directly. No files in `Candidates/V66/` this
    sprint (no V66 candidate ships).

  * **Sprint 088 preview** (for context, not for action this sprint):
    sprint 088 will ship `Candidates/V66.lean` at the sweep-pinned c
    composing the four mode windows + three fallback box windows via
    sprint 086's mixed reducer. V66 invokes the new oracle to discharge
    the joint-mass premise. V66's audit set extends V64's by one entry
    (the new `h_seven_window_mass_certified_at_356401_sqrt` axiom),
    matching the V52→V57 audit-set extension pattern from sprint 053.
