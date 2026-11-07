# Sprint 092: V68 eleven-window c-push at `c = 71313/200000` via the mixed-kernel reducer at `n = 10`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V67.lean` (V67 is the live ceiling at
`89141/250000 = 356564/1000000`; V68 inherits V67's `h_witness` shape
extended for three additional per-mode windows j ∈ {8, 9, 10}).
**Target file**: `Candidates/V68.lean` plus a per-candidate
derived-theorem file `Candidates/V68/ElevenWindowEndpoints.lean`, plus
oracle infrastructure in `Proof/Reduction.lean`,
`Numerical_Library/rigorous_scalar.py`, and `lemma.toml`.
**Direction**: raise-c

## Goal

Ship `Candidates/V68.lean` proving `ValidKorenblumBound (71313/200000)`
by invoking sprint 086's mixed-kernel multi-window reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` with
`n = 10` (i.e. `Fin 11` windows) over the eleven-window split
sprint 091's adaptive sweep pinned (`Scratch/sprint_091_witness.txt`):

| i  | kind        | ρStart                              | ρStop                               |
|----|-------------|-------------------------------------|-------------------------------------|
| 0  | `branch1`   | `c · (1 + 1/1000000000)`            | `c · sqrt(121/120)`                 |
| 1  | `modeJ 10`  | `c · sqrt(121/120)`                 | `c · sqrt(100/99)`                  |
| 2  | `modeJ 9`   | `c · sqrt(100/99)`                  | `c · sqrt(81/80)`                   |
| 3  | `modeJ 8`   | `c · sqrt(81/80)`                   | `c · sqrt(64/63)`                   |
| 4  | `modeJ 7`   | `c · sqrt(64/63)`                   | `c · sqrt(49/48)`                   |
| 5  | `modeJ 6`   | `c · sqrt(49/48)`                   | `c · sqrt(36/35)`                   |
| 6  | `modeJ 5`   | `c · sqrt(36/35)`                   | `c · sqrt(25/24)`                   |
| 7  | `modeJ 4`   | `c · sqrt(25/24)`                   | `c · sqrt(16/15)`                   |
| 8  | `modeJ 3`   | `c · sqrt(16/15)`                   | `c · sqrt(9/8)`                     |
| 9  | `modeJ 2`   | `c · sqrt(9/8)`                     | `c · sqrt(4/3)`                     |
| 10 | `modeJ 1`   | `c · sqrt(4/3)`                     | `1 - 1/1000000000`                  |

with `c = v68CValue = 71313/200000 = 356565/1000000` (i.e.
`c_value_v68 = 71313/200000`, the canonical-rational reduction of
`356565/1000000`).

The τ-band ratios pinned by sprint 091's witness (extending V67's seven
to ten):

```
mode10:  τ_9  = 1 - 1/100 = 99/100   ↔  ρ² = c² · 100/99
mode9 :  τ_8  = 1 - 1/81  = 80/81    ↔  ρ² = c² · 81/80
mode8 :  τ_7  = 1 - 1/64  = 63/64    ↔  ρ² = c² · 64/63
mode7 :  τ_6  = 1 - 1/49  = 48/49    ↔  ρ² = c² · 49/48
…  (j = 6, 5, 4, 3, 2, 1 identical to V67's ratios)
```

Branch.one residual box `[c · (1 + 1e-9), c · sqrt(121/120)]` retains
the `τ_10 = 120/121` upper edge; this is the only Branch.one window in
the partition. The deep-band residual is **strictly smaller** than V67's
`[c·(1+1e-9), c·sqrt(64/63)]` because three more per-mode windows
(j = 10, 9, 8) sit between `c·sqrt(121/120)` and `c·sqrt(64/63)`.

The joint-mass cell is discharged by a **new oracle axiom**
`h_eleven_window_mass_certified_at_356565_modeJ10` (added in this
sprint), backed by a new wrapper
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10`
(name reused from the user prompt for naming-lineage continuity with
sprint 090's `_seven_window_*_modeJ7`; despite the `seven_window` name
prefix the wrapper actually pins the eleven-window architecture).
Live margin per sprint 091: **+1.0048e-4** at `(dps, n_trunc) = (80,
300)`.

The `c_value` constant on V68's candidate side is
`71313/200000 = 356565/1000000`, strictly above V67's
`89141/250000 = 356564/1000000` by `+1/1000000 ≈ +1e-6`.

## Why

Sprint 091's extended-architecture Phase-0 sweep delivered a complete
witness for an eleven-window architecture (one Branch.one residual box +
ten per-mode windows for `j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}`) at the
c-ceiling `c = 71313/200000` with full-envelope margin **+1.0048e-4**
(comfortably above the 1e-4 floor by 4.75% of the threshold). The
`+1e-6` push above V67 is the smallest c-push in the project's history
but **strictly positive** and **full-envelope-margin-robust**.

The sprint is heavily templated on already-shipped sprints:

  * Sprint 087 / sprint 090 (oracle wrapper + helper defs in
    `Proof/Reduction.lean` + oracle row in `lemma.toml` for the seven-
    and eight-window architectures, respectively).
  * Sprint 088 / sprint 090 (V66 / V67 candidate body composing the
    mixed reducer over `Fin 7` / `Fin 8`, plus
    `Candidates/V66/SevenWindowEndpoints.lean` /
    `Candidates/V67/EightWindowEndpoints.lean`).

The structural delta from V67 to V68 is:

  1. **Eleven windows instead of eight**: one Branch.one box (vs one in
     V67) + ten per-mode windows for `j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2,
     1}` (vs seven for `j ∈ {7, 6, 5, 4, 3, 2, 1}` in V67). Net +3
     windows total.

  2. **Three additional mode τ-bound discharge pairs**:
     `tau_seven_le_c_sq_div_stop_mode8` /
     `c_sq_div_start_mode8_le_tau_eight` for j=8;
     `tau_eight_le_c_sq_div_stop_mode9` /
     `c_sq_div_start_mode9_le_tau_nine` for j=9;
     `tau_nine_le_c_sq_div_stop_mode10` /
     `c_sq_div_start_mode10_le_tau_ten` for j=10.
     V67 already covers j=1, …, 7 in `EightWindowEndpoints.lean`. The
     V63 parametric `modeScalarIntegrand_intervalIntegrable` is already
     universally quantified in `j ≥ 1`, so it covers j=8, 9, 10 with
     no new file.

  3. **The Branch.one residual box is shorter**: its upper endpoint
     becomes `c · sqrt(121/120)` (vs V67's `c · sqrt(64/63)`). The box
     is parametric in `[a, b]` so `Candidates/V66/Branch1Integrability.lean`
     applies as-is to the new endpoints — exactly as in sprint 090.

  4. **`OneModeTail.tau k` for k ∈ {7, 8, 9} is exercised for the first
     time in the workspace**: V67's deepest k was 7 (i.e. `tau 7 = 63/64`).
     V68 invokes `OneModeTail.tau 7`, `OneModeTail.tau 8`, and
     `OneModeTail.tau 9` for the lower-τ-bound side of mode8/9/10's
     window. These follow the same algebraic shape as V67's
     `OneModeTail.tau 7 = 63/64` discharge: `field_simp + norm_num`
     against `tau k = k(k+2)/(k+1)²`.

  5. **`c_value` literal change**: `89141/250000 → 71313/200000`. All
     `norm_num` discharges in V68's namespace use the new literal. The
     reduced `Fraction` form is `71313/200000`, which equals
     `356565/1000000` (the unreduced form is not the canonical Lean
     form; use `71313 / 200000` exactly as the witness file does).

The c-push is small (+1e-6) but the work is **almost entirely
mechanical reuse**:

  * **Reuses 100% of V63 derived files** (Integrability, Summability,
    DiskInnerSeriesBridge) — universally `j`-parametric and `c`-parametric.
  * **Reuses 100% of V66/Branch1Integrability.lean** — parametric in
    `[a, b]`.
  * **Endpoints file** is V67/EightWindowEndpoints.lean +3 mode τ-bound
    theorem pairs (j=8, 9, 10) and the corresponding `OneModeTail.tau k`
    discharges for k ∈ {7, 8, 9}, +3 entries in the geometric ordering
    chain, plus an updated `Fin 11` `fin_cases` body in
    `v68_modeJ_tau_bounds`.
  * **Wrapper** is sprint 090's wrapper +3 mode-window helper calls
    (`_two_window_mass_window(c, j, ρ_a, ρ_b, n_trunc)` for j ∈ {10, 9,
    8}) and a deeper Branch.one residual box upper endpoint.
  * **V68 candidate body** is V67's body with `Fin 11` instead of
    `Fin 8` and three additional `fin_cases` branches in
    `hModeJ` and `hIntKind`.

### Three (and more) distinct directions considered

1. **Direction A — this sprint: ship V68 in one session via the
   prior planner's recommendation.** Single sprint composing V63 derived
   files + V66/Branch1Integrability + new V68/ElevenWindowEndpoints +
   new wrapper + new oracle row + helper defs in `Proof/Reduction.lean`
   + new free axiom `h_eleven_window_mass_certified_at_356565_modeJ10`
   + `hH2_v68` / `hCircleGapInt_v68` inline seed axioms + thin V68
   candidate. **Strongest objection**: scope risk —
   ~4 deliverables (wrapper, helper-defs+axiom, endpoints file, V68
   candidate) plus seed-axiom registry edits in one session, plus
   first-time exercise of `OneModeTail.tau` at k = 7, 8, 9.
   **Counter**: sprint 090 successfully shipped exactly the same
   pattern in one session (V67 with `Fin 8` and first-time `tau k = 7`
   exercise); sprint 088 shipped V66 with `Fin 7` and three new files
   in one session. V68's net delta from V67 is +3 mode τ-bound theorem
   pairs (mechanical extension) + 3 more `fin_cases` branches
   (mechanical extension). The new `tau k` discharges at k = 7, 8, 9
   are the same shape as V67's `tau 7` discharge: `field_simp +
   norm_num`. The user prompt itself names this as the planned shape.
   **Chosen.**

2. **Direction B — partition: sprint 092a ships only the wrapper +
   oracle row + helper defs + free axiom in `Proof/Reduction.lean` (no
   candidate, V67-tie). Sprint 092b ships V68.** **Strongest objection**:
   pure-infrastructure sprint with no candidate ship leaves the score
   unchanged for a sprint. The user prompt explicitly says "Prefer the
   direct attempt." The work is structurally bounded for one session
   (sprint 090 was bigger and shipped). **Demoted** in favor of
   Direction A; if Direction A blocks at the candidate level, the
   BLOCKED stop condition documents the partial delivery and sprint 093
   finishes V68 (functionally equivalent to the partition).

3. **Direction C — abandon V68 in favor of trust-surface compaction**:
   replace `hH2_v6×` / `hCircleGapInt_v6×` per-candidate axioms with
   theorems consuming `Section2Assumptions`. **Strongest objection**:
   doesn't push c, and the migration is impossible per sprint 089's
   prior analysis (the `Section2Assumptions` fields are pointwise
   inequalities, not summability/integrability statements). The
   genuine c-push is queued and ready (Direction A, witness file
   pinned), so trust-surface compaction must wait. **Demoted.**

4. **Direction D — re-run sprint 091's adaptive sweep at finer
   precision (1e-7 step)**, on the hypothesis that the c-ceiling at
   `71313/200000` missed sub-micro-c headroom. **Strongest objection**:
   sprint 091's `Honesty notes` already document this as out of scope
   per its contract's "don't sweep beyond 356575/1000000" directive;
   the next planner *may* queue it as a sprint 092a sibling but it
   does not unblock the V68 ship that the witness file already
   supports. **Demoted; the V68 ship and a finer-grid re-sweep are
   independent — taking V68 first is strictly better because the
   witness is already in hand.**

5. **Direction E — analytic-Lean sprint to derive a tighter version of
   equation (5)'s envelope on the deep band** (per-k cross-coupling).
   **Strongest objection**: open-ended exploration with no precise
   oracle-backed sub-claim. Sprint 091's NO-GO for further
   architectural axes leaves this as the *next-sprint* pivot, but
   bird-in-hand c-push (Direction A) is preferred. Per the user
   directive "do not file proposals", any analytic-Lean sprint that
   reaches `proposal_002`/`proposal_003`-style territory must be a
   self-contained derived theorem from existing `Section2Assumptions`
   + Mathlib. Sprint 091's witness gives a +1e-6 push without that
   derivation, so this direction can be a sprint 093+ option after
   V68 lands. **Demoted.**

6. **Direction F — file `proposal_004` for the `hH2_v6×` /
   `hCircleGapInt_v6×` migration into `Section2Assumptions`**. Per the
   user directive "do not file proposals" and the four-condition
   proposal-filing checklist (`AGENT_BRIEF.md`): the migration has not
   been "tried hard and failed" in Lean (there is no prior generator
   session attempting it), and it does not improve `c_value`.
   **Demoted (and forbidden by the directive prompt).**

Direction A wins on **expected analytical novelty per session-budget**:
it lands the next strict score push using sprint 091's pinned witness,
exercises the mixed reducer at `n = 10` for the first time on a real
candidate, and produces the workspace's largest-mode-index-yet
per-mode windows (j=8, 9, 10) — three additional analytic τ-bound
discharges that are direct extensions of V67's pattern. If Direction A
blocks at the candidate level, the per-deliverable factoring naturally
degrades into Direction B's outcome via the BLOCKED stop condition.

### Why this is bounded for one session

The work is **directly templated** on sprint 090 with strict
incremental scope:

  * **Wrapper** (`certify_seven_window_mass_at_356565_modeJ10`):
    templated on sprint 090's `certify_seven_window_mass_at_356564_modeJ7`
    (~120 lines). The eleven-window architecture has 1 Branch.one
    helper call + 10 per-mode helper calls (vs sprint 090's 1 + 7);
    helpers are parametric in `j` and `[a, b]` (verified in sprint 090's
    code review). Estimated ~140-160 lines (similar size, +3
    mode-window calls, identical helper-call shape).
  * **`Proof/Reduction.lean` extension**: sprint 090's pattern has 4
    helper defs (`v67CValue`, `v67EightWindowKind`,
    `v67EightWindowStart`, `v67EightWindowStop`) + 1 free axiom
    (`h_eight_window_mass_certified_at_356564_modeJ7`), totaling ~115
    lines appended at the bottom of `Reduction.lean` immediately
    before the closing `end`. V68 adds the same shape with `Fin 11`
    instead of `Fin 8` and 11 endpoints instead of 8. Estimated ~125
    lines.
  * **`Candidates/V68/ElevenWindowEndpoints.lean`**: templated on V67's
    `EightWindowEndpoints.lean` (674 lines). Differences: +3 mode
    τ-bound theorem pairs (j=8, 9, 10 — six new theorems total), +3
    entries in the geometric-ordering chain (11 endpoints), updated
    `fin_cases` bodies for `v68_modeJ_tau_bounds`,
    `v68_modeJ_one_le_j`, `v68_c_lt_start`, `v68_stop_lt_one`,
    `v68_start_le_stop`, `v68_adj`, `v68_stop_le_branchSplit`. Net +6
    theorems (the τ-bound pairs at j=8, 9, 10) and ~+3 lines per
    `fin_cases`-style theorem. Estimated ~750-800 lines. **One
    expected significant cleanup opportunity**: a parametric
    mode-τ-bound theorem indexed by `j ∈ {1, …, 10}` could collapse
    twenty discharges to one, but is not required (V67 did not factor
    them; V68 follows V67's pattern).
  * **`Candidates/V68.lean`**: templated on V67.lean (357 lines). The
    `v68_witness` body uses `fin_cases i` over `Fin 11` instead of
    `Fin 8`. Per-mode integrability calls V63's parametric
    `modeScalarIntegrand_intervalIntegrable` ten times (vs V67's
    seven); per-window kind dispatch has 10 mode cases + 1 branch1
    case (vs V67's 7 + 1). Estimated ~380 lines.
  * **`lemma.toml`**: 2 new `[seed_axioms].allowed` entries
    (`hH2_v68`, `hCircleGapInt_v68`), 1 new `[seed_axioms].allowed`
    entry for the new oracle axiom, 1 new `[[oracles]]` row, 2 new
    `[import_policy].allowed_exact` entries (V68 main +
    V68/ElevenWindowEndpoints). Estimated <40 lines of TOML.

Total: ~1300-1500 lines across files. Sprint 090 itself shipped
~1150-1300 lines in one session (a slightly smaller delta);
**bounded for one session**. The only risk is the wrapper's
mpmath plumbing for the deeper Branch.one box `[c·(1+1e-9),
c·sqrt(121/120)]`, which is a slightly shorter integration interval
than V67's `[c·(1+1e-9), c·sqrt(64/63)]` (the Branch.one integrand
mass on this shorter interval is ~50% smaller, but sprint 091's
witness already verified the joint mass at full envelope gives margin
+1.005e-4 ≥ 1e-4).

## Concrete edits expected

### 1. `Numerical_Library/rigorous_scalar.py` (modify)

Add new wrapper function `certify_seven_window_mass_at_356565_modeJ10`
(name per the user prompt; despite the `seven_window` name prefix the
wrapper pins the eleven-window architecture). Templated **byte-for-byte**
on sprint 090's `certify_seven_window_mass_at_356564_modeJ7` (lines
1629-1749 of `rigorous_scalar.py`). The wrapper:

  * Pins `c = mp.mpf("71313") / mp.mpf("200000")` (equivalent to
    `Fraction(71313, 200000)`; the unreduced form `Fraction(356565,
    1000000)` reduces to this via Python's `Fraction` canonicalization).
  * Computes the eleven-window endpoint sequence using sprint 091's
    sqrt ratios `[121/120, 100/99, 81/80, 64/63, 49/48, 36/35, 25/24,
    16/15, 9/8, 4/3]` plus `(1 + 1e-9)` as the box-A start factor and
    `(1 - 1e-9)` as `ρ_top`.
  * Calls the existing `_two_window_mass_window(c, j, ρ_a, ρ_b,
    n_trunc)` helper at `j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}` and the
    existing `_branch1_window_mass(c, ρ_a, ρ_b, n_trunc)` helper at
    the single Branch.one residual box.
  * Sums to a rational total mass at `(dps=80, n_trunc=300)`,
    asserts `total ≥ 1 + 10⁻³⁰`, and returns `Fraction(1, 1)` if so.
    Margin floor: `10⁻³⁰` (well below the live `+1.005e-4`).
  * Adds three structural ordering checks for the new endpoints (`c <
    box0_lo`, `box0_lo < rho_10_lo`, `rho_10_lo < rho_9_lo`,
    `rho_9_lo < rho_8_lo`, `rho_8_lo < rho_7_lo`, …) — same pattern as
    sprint 090's wrapper, three additional checks.
  * Live-test signature: `certify_seven_window_mass_at_356565_modeJ10()
    → Fraction(1, 1)`.

The existing helpers `_two_window_mass_window` (parametric in `j`) and
`_branch1_window_mass` (parametric in `[a, b]`) are unchanged. The
wrapper is purely a new top-level function appended after sprint 090's
wrapper.

Live-test the wrapper before shipping:
```bash
env UV_CACHE_DIR=korenblum/.uv-cache uv run python -c "
from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import \
  certify_seven_window_mass_at_356565_modeJ10
print(certify_seven_window_mass_at_356565_modeJ10())
"
```
Expected output: `1` (i.e. `Fraction(1, 1)`).

### 2. `Proof/Reduction.lean` (extend)

Append immediately before `end ProofRefinement.Korenblum`, after the
existing sprint-090 `v67*` defs and `h_eight_window_mass_certified_at_356564_modeJ7`
axiom (lines 9590-9667):

```lean
/-- V68 c-value: `71313/200000 = 356565/1000000` (sprint 091 GO ceiling). -/
def v68CValue : ℝ := 71313 / 200000

/-- Eleven-window kind dispatch: 1 Branch.one + 10 per-mode windows
    j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}. -/
def v68ElevenWindowKind : Fin 11 → KernelKind
  | ⟨0, _⟩ => KernelKind.branch1
  | ⟨1, _⟩ => KernelKind.modeJ 10
  | ⟨2, _⟩ => KernelKind.modeJ 9
  | ⟨3, _⟩ => KernelKind.modeJ 8
  | ⟨4, _⟩ => KernelKind.modeJ 7
  | ⟨5, _⟩ => KernelKind.modeJ 6
  | ⟨6, _⟩ => KernelKind.modeJ 5
  | ⟨7, _⟩ => KernelKind.modeJ 4
  | ⟨8, _⟩ => KernelKind.modeJ 3
  | ⟨9, _⟩ => KernelKind.modeJ 2
  | ⟨10, _⟩ => KernelKind.modeJ 1

/-- Eleven-window window-start sequence. -/
def v68ElevenWindowStart : Fin 11 → ℝ
  | ⟨0, _⟩ => v68CValue * (1 + 1 / 1000000000)
  | ⟨1, _⟩ => v68CValue * Real.sqrt (121 / 120)
  | ⟨2, _⟩ => v68CValue * Real.sqrt (100 / 99)
  | ⟨3, _⟩ => v68CValue * Real.sqrt (81 / 80)
  | ⟨4, _⟩ => v68CValue * Real.sqrt (64 / 63)
  | ⟨5, _⟩ => v68CValue * Real.sqrt (49 / 48)
  | ⟨6, _⟩ => v68CValue * Real.sqrt (36 / 35)
  | ⟨7, _⟩ => v68CValue * Real.sqrt (25 / 24)
  | ⟨8, _⟩ => v68CValue * Real.sqrt (16 / 15)
  | ⟨9, _⟩ => v68CValue * Real.sqrt (9 / 8)
  | ⟨10, _⟩ => v68CValue * Real.sqrt (4 / 3)

/-- Eleven-window window-stop sequence. -/
def v68ElevenWindowStop : Fin 11 → ℝ
  | ⟨0, _⟩ => v68CValue * Real.sqrt (121 / 120)
  | ⟨1, _⟩ => v68CValue * Real.sqrt (100 / 99)
  | ⟨2, _⟩ => v68CValue * Real.sqrt (81 / 80)
  | ⟨3, _⟩ => v68CValue * Real.sqrt (64 / 63)
  | ⟨4, _⟩ => v68CValue * Real.sqrt (49 / 48)
  | ⟨5, _⟩ => v68CValue * Real.sqrt (36 / 35)
  | ⟨6, _⟩ => v68CValue * Real.sqrt (25 / 24)
  | ⟨7, _⟩ => v68CValue * Real.sqrt (16 / 15)
  | ⟨8, _⟩ => v68CValue * Real.sqrt (9 / 8)
  | ⟨9, _⟩ => v68CValue * Real.sqrt (4 / 3)
  | ⟨10, _⟩ => 1 - 1 / 1000000000

/-- Joint-mass oracle for V68's eleven-window architecture. Backed by
    `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10`
    via the `[[oracles]]` row in `lemma.toml`. -/
axiom h_eleven_window_mass_certified_at_356565_modeJ10
    (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤ ∑ i : Fin 11,
      match v68ElevenWindowKind i with
      | KernelKind.modeJ j =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            ModeBridge.scalarIntegrand v68CValue j
              (WangOuter.paperLambda K v68CValue) ρ
      | KernelKind.branch1 =>
          ∫ ρ in (v68ElevenWindowStart i)..(v68ElevenWindowStop i),
            Korenblum.scalarIntegrand1 v68CValue
              (WangOuter.paperLambda K v68CValue) ρ
```

**Important**: the axiom body must match the kind-dispatched joint-mass
cell of the sprint 086 mixed reducer **byte-for-byte** (modulo the
sprint-092-specific `c`, `kind`, `start`, `stop` defs). Compare
character-by-character against sprint 090's
`h_eight_window_mass_certified_at_356564_modeJ7` axiom body
(`Reduction.lean:9655-9667`).

### 3. `Candidates/V68/ElevenWindowEndpoints.lean` (new file)

Per-candidate derived-theorem file, scope is V68 only. **No `axiom`s,
no `sorry`s, no `Section2Assumptions` field extensions.** Imports:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge
import KorenblumPaper.PaperAxioms
import ProofRefinement.Korenblum.Proof.Reduction
```

Required theorems (templated **byte-for-byte** on
V67/EightWindowEndpoints.lean's pattern):

  * **Six new mode τ-bound theorems** (three pairs):

    - **mode10 pair (uses `OneModeTail.tau 9`)**:
      ```lean
      theorem tau_nine_le_c_sq_div_stop_mode10 {c : ℝ} (hc : 0 < c) :
          OneModeTail.tau 9 ≤ c ^ 2 / (c * Real.sqrt (100 / 99)) ^ 2 := by
        rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 100 / 99)]
        have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
        have heq : c ^ 2 / (c ^ 2 * (100 / 99)) = 99 / 100 := by field_simp
        rw [heq]
        unfold OneModeTail.tau
        norm_num

      theorem c_sq_div_start_mode10_le_tau_ten {c : ℝ} (hc : 0 < c) :
          c ^ 2 / (c * Real.sqrt (121 / 120)) ^ 2 ≤ OneModeTail.tau 10 := by
        rw [sq_c_mul_sqrt (by norm_num : (0 : ℝ) ≤ 121 / 120)]
        have hcsq_ne : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
        have heq : c ^ 2 / (c ^ 2 * (121 / 120)) = 120 / 121 := by field_simp
        rw [heq]
        unfold OneModeTail.tau
        norm_num
      ```

    - **mode9 pair (uses `OneModeTail.tau 8`)**:
      `tau_eight_le_c_sq_div_stop_mode9` with τ-band 81/80 → 80/81;
      `c_sq_div_start_mode9_le_tau_nine` with τ-band 100/99 → 99/100.
      Identical algebraic shape.

    - **mode8 pair (uses `OneModeTail.tau 7`)**:
      `tau_seven_le_c_sq_div_stop_mode8` with τ-band 64/63 → 63/64;
      `c_sq_div_start_mode8_le_tau_eight` with τ-band 81/80 → 80/81.
      Identical algebraic shape.

    The existing seven mode τ-bound pairs from V67 (j = 1, …, 7) are
    re-stated with renamed identifiers (e.g.
    `tau_six_le_c_sq_div_stop_mode7`, `c_sq_div_start_mode7_le_tau_seven`,
    etc.) verbatim from V67's file — copy them to V68's file with no
    semantic change so V68's namespace is self-contained. (The V67
    file is V67-namespace-scoped; V68's namespace must contain its own
    copies.)

  * **`v68_branchSplit_lt_one`**: at `c = 71313/200000`,
    `branchSplit c = c · sqrt(4/3) = 71313/200000 · sqrt(4/3) ≈
    0.4117 · 1.0 = 0.4117 · 0.999… < 1`. By `unfold +
    norm_num`. (Templated on V67's `v67_branchSplit_lt_one`.)

  * **Eleven-way geometric ordering**: `c < ρStart 0 ≤ ρStop 0 = ρStart
    1 ≤ … ≤ ρStop 10 < 1` at `c = v68CValue`. Ten adjacency equations
    are by `rfl` (definitional via `v68ElevenWindowStart` /
    `v68ElevenWindowStop` line-up, exactly mirroring V67's pattern).
    The remaining inequalities chain through `Real.sqrt`-monotonicity:

    ```lean
    theorem v68_c_lt_start (i : Fin 11) :
        v68CValue < v68ElevenWindowStart i := by
      fin_cases i
      all_goals (try
        (unfold v68CValue v68ElevenWindowStart;
         apply lt_of_lt_of_le _ (mul_le_of_one_le_right (by norm_num) (by …));
         norm_num) <;>
        · …)
      …  -- 11 sub-cases, each one to three lines (see V67's pattern)

    theorem v68_stop_lt_one (i : Fin 11) :
        v68ElevenWindowStop i < (1 : ℝ) := by
      fin_cases i
      …  -- 11 sub-cases

    theorem v68_start_le_stop (i : Fin 11) :
        v68ElevenWindowStart i ≤ v68ElevenWindowStop i := by
      fin_cases i <;>
        (try unfold v68ElevenWindowStart v68ElevenWindowStop;
         apply mul_le_mul_of_nonneg_left _ (by norm_num [v68CValue] : (0:ℝ) ≤ v68CValue);
         exact Real.sqrt_le_sqrt (by norm_num)) <;>
        · …  -- the boxed start (i = 0) and the rho_top stop (i = 10) get
              -- separate sub-cases with explicit norm_num on the additive
              -- tweak.

    theorem v68_adj (i : Fin 10) :
        v68ElevenWindowStop i.castSucc = v68ElevenWindowStart i.succ := by
      fin_cases i <;> rfl

    theorem v68_c_le_start (i : Fin 11) : v68CValue ≤ v68ElevenWindowStart i :=
      le_of_lt (v68_c_lt_start i)
    theorem v68_stop_le_one (i : Fin 11) : v68ElevenWindowStop i ≤ 1 :=
      le_of_lt (v68_stop_lt_one i)
    theorem v68_c_le_stop (i : Fin 11) : v68CValue ≤ v68ElevenWindowStop i :=
      le_trans (v68_c_le_start i) (v68_start_le_stop i)
    ```

  * **`v68_modeJ_one_le_j`**: per `i ∈ {1, …, 10}` the kind is `modeJ
    j` for `j ∈ {10, 9, 8, 7, 6, 5, 4, 3, 2, 1}` respectively, all
    `≥ 1`. By `fin_cases i <;> simp [v68ElevenWindowKind]`. (Templated
    on V67's `v67_modeJ_one_le_j`.)

  * **`v68_modeJ_tau_bounds`**: full mode-window τ-bound discharge
    bundled per `i ∈ {1, …, 10}`. Templated **byte-for-byte** on V67's
    `v67_modeJ_tau_bounds` (`EightWindowEndpoints.lean:559-656`), with
    three additional `fin_cases` branches for j = 10, 9, 8 that invoke
    the new mode10/9/8 τ-bound pairs. Specifically:

    ```lean
    theorem v68_modeJ_tau_bounds (i : Fin 11) (j : ℕ)
        (h : v68ElevenWindowKind i = KernelKind.modeJ j) :
        1 ≤ j ∧
        OneModeTail.tau (j - 1) ≤ v68CValue ^ 2 / v68ElevenWindowStop i ^ 2 ∧
        v68CValue ^ 2 / v68ElevenWindowStart i ^ 2 ≤ OneModeTail.tau j := by
      fin_cases i
      · exfalso; simp [v68ElevenWindowKind] at h
      · -- i = 1: kind = modeJ 10
        have hj : j = 10 := …
        subst hj
        refine ⟨by decide, ?_, ?_⟩
        · show OneModeTail.tau 9 ≤ …
          exact tau_nine_le_c_sq_div_stop_mode10 v68CValue_pos
        · show … ≤ OneModeTail.tau 10
          exact c_sq_div_start_mode10_le_tau_ten v68CValue_pos
      · -- i = 2: kind = modeJ 9 (similar)
        …
      · -- i = 3: kind = modeJ 8 (similar, exercises tau 7 and tau 8)
        …
      · -- i = 4..10: kind = modeJ {7, 6, 5, 4, 3, 2, 1}
        -- (templated on V67's i = 1..7 cases)
        …
    ```

  * **`v68_stop_le_branchSplit`**: per `i = 0` (the only Branch.one
    box), `v68ElevenWindowStop 0 = v68CValue · sqrt(121/120) ≤
    branchSplit v68CValue = v68CValue · sqrt(4/3)`. By
    `mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by norm_num : (121/120 :
    ℝ) ≤ 4/3)) c_nonneg`. For `i ∈ {1, …, 10}` the kind is `modeJ`, so
    the `branch1` hypothesis yields `False`. (Templated on V67's
    `v67_stop_le_branchSplit`.)

### 4. `Candidates/V68.lean` (new file)

The candidate body, templated **byte-for-byte** on V67.lean. Imports:

```lean
-- @parent V67
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
import ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints
```

Required content:

```lean
namespace ProofRefinement.Korenblum.Candidates.V68

def c_value : ℝ := 71313 / 200000   -- = v68CValue = 356565/1000000

theorem c_value_eq_v68CValue : c_value = v68CValue := rfl

theorem c_value_pos : (0 : ℝ) < c_value := by
  unfold c_value; norm_num
theorem c_value_lt_one : c_value < (1 : ℝ) := by
  unfold c_value; norm_num
theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- V68's c strictly improves on V67's `89141/250000 = 356564/1000000`. -/
theorem c_value_gt_v67 : (89141 : ℝ) / 250000 < c_value := by
  unfold c_value
  norm_num

/-- Evaluator-facing oracle bound-field. Matches the
    `bound_field = "eleven_window_mass_lower"` row in `lemma.toml`. -/
def eleven_window_mass_lower : ℝ := 1

/-- branchSplit < 1 at c_value. -/
theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 :=
  v68_branchSplit_lt_one

/-- Free per-candidate axiom: H² boundary-norm finiteness. Templated on V67. -/
axiom hH2_v68 : ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Free per-candidate axiom: 2ρ·circleGap integrability on (c, 1). Templated on V67. -/
axiom hCircleGapInt_v68 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-- The h_witness predicate for the mixed reducer at n = 10. -/
theorem v68_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin (10 + 1) → ℝ) (kind : Fin (10 + 1) → KernelKind),
        … (full body of the mixed reducer's h_witness, instantiated at
           v68ElevenWindowStart, v68ElevenWindowStop, v68ElevenWindowKind) := by
  intro a b K paper
  refine ⟨v68ElevenWindowStart, v68ElevenWindowStop, v68ElevenWindowKind,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  -- (Per-cell discharge: V68/ElevenWindowEndpoints + V63 derived files +
  -- V66/Branch1Integrability + the new oracle.)
  …
  -- joint eleven-window mass cell:
  · show (1 : ℝ) ≤ ∑ i : Fin 11, … (with c_value)
    show (1 : ℝ) ≤ ∑ i : Fin 11, … (with v68CValue)
    exact h_eleven_window_mass_certified_at_356565_modeJ10 K

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    (n := 10) c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v68_witness paper)

end ProofRefinement.Korenblum.Candidates.V68
```

The witness body's per-`i` dispatch:

  * `hModeJ` cell: `fin_cases i`. For `i = 0` (Branch.one), `cases hKind`
    rejects `modeJ`. For `i ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}` (modeJ
    10, 9, 8, 7, 6, 5, 4, 3, 2, 1), invoke `v68_modeJ_tau_bounds`.
  * `hBranch1Split` cell: `fin_cases i`. For `i = 0`, invoke
    `v68_stop_le_branchSplit`. For `i ∈ {1, …, 10}`, `cases hKind`
    rejects branch1.
  * `hIntKind` cell: 11-way `fin_cases i` with kind dispatch:
    - `i = 0` (branch1): invoke
      `V66.Branch1Integrability.branch1ScalarIntegrand_intervalIntegrable`
      directly with the V68 endpoints `(v68ElevenWindowStart 0,
      v68ElevenWindowStop 0) = (c·(1+1e-9), c·sqrt(121/120))`.
    - `i ∈ {1, …, 10}` (modeJ): invoke
      `V63.Integrability.modeScalarIntegrand_intervalIntegrable`
      (parametric in `j`) at j=10, 9, 8, 7, 6, 5, 4, 3, 2, 1
      respectively.
  * Six summability witnesses: invoke
    `V63.Summability.six_summability_shapes_from_h2` with
    `(hH2_v68 a)`, `(hH2_v68 b)`, `c_value_nonneg`, `c_value_lt_one`.
  * `hIntCircle`: `exact hCircleGapInt_v68 a b`.
  * `hInner`: invoke
    `V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess` with
    the kit and the absolute-summability witness, exactly as in V67.
  * `hMassTotal`: `exact h_eleven_window_mass_certified_at_356565_modeJ10 K`.

### 5. `lemma.toml` updates (inline, no proposal)

Add to `[seed_axioms].allowed`:

  * `"hH2_v68"`,
  * `"hCircleGapInt_v68"`,
  * `"h_eleven_window_mass_certified_at_356565_modeJ10"`.

Add to `[[oracles]]` (new table entry):

```toml
[[oracles]]
axiom = "h_eleven_window_mass_certified_at_356565_modeJ10"
bound_field = "eleven_window_mass_lower"
wrapper = "Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10"
# (note: wrapper name retained from sprint 091's witness for backwards
# consistency; despite the `seven_window` prefix it pins the
# eleven-window architecture.)
```

Add to `[import_policy].allowed_exact`:

  * `"ProofRefinement.Korenblum.Candidates.V68"`,
  * `"ProofRefinement.Korenblum.Candidates.V68.ElevenWindowEndpoints"`.

### 6. `Bulletin.md` and `Experience.md` append

Append one row each per the standard pattern:

  * The score push (`356564/1000000 → 356565/1000000`, `+1e-6` above
    V67, smallest in project history).
  * V68's audit set: standard Lean axioms + `hH2_v68` +
    `hCircleGapInt_v68` +
    `h_eleven_window_mass_certified_at_356565_modeJ10` (the latter at
    `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`,
    not a candidate-namespace copy).
  * One new derived-theorem file
    (`Candidates/V68/ElevenWindowEndpoints.lean`) plus reuse of
    `Candidates/V66/Branch1Integrability.lean` and V67's pattern.
  * Forward direction: sprint 093 must pivot to a structurally
    different idea per sprint 091's NO-GO verdict on further
    architectural axes (the union sprint 089 ∪ sprint 091 directions
    is exhausted). Candidates: per-k cross-coupling derived theorem,
    variable-α kernel Phase-0 re-sweep, tightened H(c, ρ) envelope
    via Wang Lemma 2 / Fourier orthogonality derivation, or
    trust-surface compaction of `hH2_v6×` / `hCircleGapInt_v6×`.

### 7. NOT modified

  * `KorenblumPaper/` (read-only).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Any V0–V67 candidate file (V67 stays at `89141/250000`; the new
    seed-axiom and oracle additions do not perturb V64-V67 audit sets).
  * Any V63 derived file (Integrability/Summability/DiskInnerSeriesBridge
    reused as-is).
  * Any V64 derived file (TauWindowEndpoints is V64-specific).
  * `Candidates/V66/SevenWindowEndpoints.lean` (V66-specific).
  * `Candidates/V67/EightWindowEndpoints.lean` (V67-specific; V68 has
    its own ElevenWindowEndpoints).
  * `Candidates/V66/Branch1Integrability.lean` is **reused directly**
    (the file's `branch1ScalarIntegrand_intervalIntegrable` is
    parametric in `[a, b]`, so V68's single-box invocation calls it
    with V68 endpoints; no edit to the V66 file).
  * The existing `[[oracles]]` rows
    (`h_two_window_mass_certified_at_35646_sqrt`,
    `h_seven_window_mass_certified_at_356562_sqrt`,
    `h_eight_window_mass_certified_at_356564_modeJ7`).
  * Existing wrappers in `Numerical_Library/rigorous_scalar.py`
    (`certify_two_window_mass_at_35646_sqrt`,
    `certify_seven_window_mass_at_356562_sqrt`,
    `certify_seven_window_mass_at_356564_modeJ7`).
  * `Proposals/` (no proposal filed; per the user directive prompt and
    the four-condition checklist in `AGENT_BRIEF.md`, this is an
    inline-pattern oracle addition).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds.

2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true`.

3. The Evaluator's reported `score` (`= c_value`) is `71313/200000`
   (= `356565/1000000`), strictly greater than V67's `89141/250000`
   (= `356564/1000000`). The `score` field in
   `Refinement_Log/log.jsonl` reflects this.

4. `axioms_used` in V68's audit consists of standard Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`, optionally
   `Lean.ofReduceBool` / `Lean.trustCompiler`) plus exactly:

     * `ProofRefinement.Korenblum.Candidates.V68.hH2_v68`,
     * `ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68`,
     * `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`.

   No other free axioms; no `sorryAx`. `[seed_axioms].allowed` contains
   all three names. **V68's audit envelope extends V67's by exactly
   one entry (the new oracle).**

5. The oracle audit on V68 reports `oracle=1, declared=1, ok=true` for
   the row `axiom = "h_eleven_window_mass_certified_at_356565_modeJ10"`,
   `bound_field = "eleven_window_mass_lower"`. V68's
   `def eleven_window_mass_lower : ℝ := 1` exposes the matching
   bound-field.

6. The numerical wrapper
   `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356565_modeJ10`
   is live-tested **before** the evaluator run and returns
   `Fraction(1, 1)` (i.e. integer 1). The Phase 0 margin recorded in
   `Scratch/sprint_091_witness.txt` (`+1.0048e-4` at `(dps=80,
   n_trunc=300)`) is reproduced or exceeded.

7. `lake build ProofRefinement.Korenblum.Candidates.V64`,
   `lake build ProofRefinement.Korenblum.Candidates.V65`,
   `lake build ProofRefinement.Korenblum.Candidates.V66`, and
   `lake build ProofRefinement.Korenblum.Candidates.V67` continue to
   succeed (regression: the new seed-axiom and oracle additions do not
   perturb older candidates).

8. `Bulletin.md` and `Experience.md` each gain one row per the standard
   pattern, naming the c-push, the new files, the audit extension, and
   the forward direction.

## Out of scope

  * Push `c_value` beyond `71313/200000`. Sprint 091's sweep
    documented this as the c-ceiling for the eleven-window
    architecture at `(verify_dps, verify_n_trunc) = (80, 300)`. The
    union of sprint 089's directions and sprint 091's directions
    E1/E2/E3 is exhausted — pushing further requires a structurally
    different idea (per-k oracle, variable-α kernel, tightened H(c, ρ)
    envelope) — sprint 093+ work.
  * Replace `hH2_v68` / `hCircleGapInt_v68` with derivations from
    `Section2Assumptions`. Trust-surface tightening is a separate
    direction; sprint 092's job is the c-push.
  * Edit any V63-V67 derived file. V68 imports them as-is.
  * Hoist V66/Branch1Integrability into `Proof/`. It is reused as-is via
    direct import.
  * Edit `Proof/Main.lean`, `Proof/CandidateContract.lean`, or any
    `KorenblumPaper/` file (read-only).
  * Modify any existing helper or axiom in `Proof/Reduction.lean`
    (load-bearing for V64-V67; this sprint only appends new defs and a
    new axiom alongside).
  * Modify any existing wrapper in `Numerical_Library/rigorous_scalar.py`
    (load-bearing for V64-V67; this sprint only adds a new wrapper
    alongside).
  * File `proposal_004` (forbidden by the directive prompt; the
    seed-axiom and oracle additions are inline-pattern per
    `Proposals/README.md` "Do not use a proposal for … new oracle
    registry entries that are already fully specified and directly
    consumed by the current sprint").
  * Add a parametric mode-τ-bound theorem indexed by
    `j ∈ {1, …, 10}` to collapse the twenty discharges to one. V67
    did not factor them; V68 follows V67's pattern. Hoisting can be a
    sprint 094+ refactor when the c-push surface is fully exhausted.

## Time budget

≤ 240 minutes runtime.

  * `Numerical_Library/rigorous_scalar.py` wrapper: ~30 minutes
    (sprint 090's wrapper template; +3 mode-window helper calls,
    deeper Branch.one box endpoint; live-test against sprint 091's
    witness).
  * `Proof/Reduction.lean` extension (4 helper defs + 1 free axiom):
    ~25 minutes (mechanical mirror of sprint 090's pattern with
    `Fin 11`).
  * `Candidates/V68/ElevenWindowEndpoints.lean`: ~80 minutes
    (templated on V67's 674-line `EightWindowEndpoints.lean`; +6 new
    τ-bound theorems for j=8/9/10, +3 entries in geometric ordering,
    updated `fin_cases` bodies for the eleven-way structural
    theorems).
  * `Candidates/V68.lean`: ~50 minutes (templated on V67.lean's 357
    lines; the witness body uses `fin_cases` over `Fin 11` with kind
    dispatch).
  * `lemma.toml`: ~10 minutes (3 seed-axiom entries + 1 oracle row + 2
    import-policy entries).
  * Bulletin/Experience appends: ~10 minutes.
  * Build + Evaluator regression: ~35 minutes.

## Stop conditions

  * **Wrapper live-tests, all eleven-window τ-bounds, branchSplit
    constraint, integrabilities, and the joint-mass discharge typecheck;
    V68 builds; Evaluator reports `pass: true` with `score =
    71313/200000` and the audit set above**: `STATUS=READY_FOR_EVALUATION`.
    The harness gains its fourth consecutive c-push past V52.

  * **The wrapper live-test fails** (returns `Fraction(0, 1)` or some
    non-1 rational, or raises): document the failing margin or error
    at `Scratch/sprint_092_obstruction.md` and `STATUS=BLOCKED`.
    Sprint 093 either re-tunes the wrapper (e.g. higher `dps`) or
    chooses a smaller c with more headroom — but the sprint 091
    witness already pins the +1e-4 margin at the published envelope,
    so a wrapper failure here is most likely a transcription bug
    (wrong endpoint, wrong sqrt ratio) rather than a numerical
    precision issue. **First diagnosis**: print the eleven endpoints
    against the witness file at `Scratch/sprint_091_witness.txt`
    line-by-line.

  * **The `v68_witness` body fails to typecheck on a specific cell**
    (e.g. a τ-bound discharge for j=8/9/10, an integrability
    invocation, the joint-mass cell): ship the per-candidate
    derived-theorem file (`ElevenWindowEndpoints.lean`) and the
    wrapper / oracle-row / helper-def-and-axiom infrastructure anyway
    if they typecheck and live-test standalone, and document the
    specific witness-cell obstruction at
    `Scratch/sprint_092_obstruction.md` with the exact unification
    error or unprovable goal. `STATUS=BLOCKED`. Sprint 093 picks up
    with the candidate alone.

  * **A new free axiom beyond `hH2_v68` / `hCircleGapInt_v68` /
    `h_eleven_window_mass_certified_at_356565_modeJ10` would be
    required**: do not ship it. Document at
    `Scratch/sprint_092_obstruction.md` and `STATUS=BLOCKED_NEEDS_HUMAN`.
    (Highly unlikely — V67's three free axioms cover the analogous
    chain at the same shape, and the j=8/9/10 + Branch.one extension
    does not introduce new axiomatically distinct content.)

  * **The oracle audit fails because the candidate-side oracle invocation
    does not unify with the registered axiom in `Proof/Reduction.lean`**:
    the candidate must invoke the axiom via the fully-qualified name
    `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`,
    not redeclare it candidate-side (per the V67 pattern; redeclaring
    would put it in the V68 namespace and break the oracle row's
    axiom-name resolution). The `c_value = v68CValue` alignment is by
    definitional `rfl` (`c_value := 71313/200000` and
    `v68CValue := 71313/200000`); use `show` rewrites to align the
    sum's `c_value` to `v68CValue`, exactly mirroring V67's pattern
    (`Candidates/V67.lean:314-337`). `STATUS=BLOCKED` if unification
    still fails after one round-trip.

  * **The `OneModeTail.tau k` discharge for k ∈ {7, 8, 9} encounters
    an unfolding obstruction** (e.g. `OneModeTail.tau` is not
    parametric enough to unfold cleanly at k = 9): document at
    `Scratch/sprint_092_obstruction.md`. The `tau` definition in
    `KorenblumPaper.OneModePaperBridge` is `tau k = k(k+2)/(k+1)²` =
    `1 - 1/(k+1)²`, fully parametric in `k : ℕ`; unfolding at any k
    via `unfold OneModeTail.tau; norm_num` should succeed
    mechanically. If it does not, the obstruction is structural in
    the `tau` definition and `STATUS=BLOCKED_NEEDS_HUMAN`. **Highly
    unlikely** — V67 exercised k = 7 cleanly via the same shape.

## Notes for the generator

  * **Read first**:
    - `Candidates/V67.lean` (your candidate-body template, 357 lines).
    - `Candidates/V67/EightWindowEndpoints.lean` (your endpoints-file
      template, 674 lines).
    - `Candidates/V66/Branch1Integrability.lean` (113 lines; the
      file you import directly into V68).
    - `Candidates/V63/Integrability.lean`,
      `Candidates/V63/Summability.lean`,
      `Candidates/V63/DiskInnerSeriesBridge.lean` (reuse as-is via
      direct import; do not edit).
    - `Proof/Reduction.lean:9590-9667` (sprint 090's wrapper of helper
      defs + free axiom; **template byte-for-byte** for the V68
      additions, swapping `Fin 8` → `Fin 11`, `v67*` → `v68*`,
      `356564` → `356565`, `89141/250000` → `71313/200000`, etc.).
    - `Proof/Reduction.lean:8934` (the mixed reducer's signature; the
      witness shape is fully specified there).
    - `Numerical_Library/rigorous_scalar.py:1629-1749`
      (`certify_seven_window_mass_at_356564_modeJ7` function, ~120
      lines, your wrapper template).
    - `Scratch/sprint_091_witness.txt` (the exact eleven-window endpoint
      sequence + margin + envelope settings, to 28 digits).
    - `KorenblumPaper/PaperEq15.lean` (the
      `Korenblum.scalarIntegrand1` definition; same as V67).
    - `KorenblumPaper/PaperAxioms.lean` (the `branchSplit` definition;
      same as V67).
    - `KorenblumPaper/OneModePaperBridge.lean` (the
      `OneModeTail.tau k = k(k+2)/(k+1)²` definition).

  * **Wrapper live-test before everything else**: the wrapper is the
    cheapest fail-fast gate. Once it returns `Fraction(1, 1)` against
    sprint 091's pinned endpoints, the rest of the sprint is mechanical.
    If it fails, all downstream Lean work is wasted; abort and document
    at `Scratch/sprint_092_obstruction.md`. Cross-check the eleven
    endpoints against `Scratch/sprint_091_witness.txt` to 28 digits
    line-by-line.

  * **The mixed reducer's witness shape over `Fin 11`** (~32 universal-
    quantifier cells when expanded). Each cell is a one- to five-line
    invocation of an existing derived theorem. Use `fin_cases i`
    heavily: it splits `Fin 11` into eleven concrete subgoals, each
    of which can be discharged by a one-line `simp` + theorem
    invocation. The kind dispatch (1 branch1, 10 mode) requires
    `cases` on `kind i` per `i`.

  * **Per-mode integrability for j ∈ {1, …, 10}**: V63's
    `modeScalarIntegrand_intervalIntegrable`
    (`Candidates/V63/Integrability.lean:114`) is parametric in `j`
    with hypothesis `1 ≤ j`. Invoke it directly at j = 10, 9, 8, 7,
    6, 5, 4, 3, 2, 1. **No new mode-window integrability lemma
    needed.**

  * **Branch.one integrability**: V66/Branch1Integrability provides
    `branch1ScalarIntegrand_intervalIntegrable` parametric in
    `[a, b]`. V68 invokes it at `(v68ElevenWindowStart 0,
    v68ElevenWindowStop 0) = (c·(1+1e-9), c·sqrt(121/120))`. **No
    edit to the V66 file.** Sprint 090 has already verified the
    parametricity by re-using it at V67's `[c·(1+1e-9), c·sqrt(64/63)]`;
    V68's even-shorter box is structurally identical.

  * **Adjacency `ρStop i.castSucc = ρStart i.succ` is by `rfl`** —
    sprint 092's defs `v68ElevenWindowStart` and `v68ElevenWindowStop`
    line up so that adjacency is definitional. `fin_cases i` + `rfl`
    discharges all ten adjacencies.

  * **The eleven-window mass oracle is invoked unchanged after
    declaration.** The axiom
    `h_eleven_window_mass_certified_at_356565_modeJ10` (in
    `Proof/Reduction.lean`) takes a single argument `K : ℝ → ℝ → ℝ`
    and asserts the joint-mass inequality with `v68CValue`,
    `v68ElevenWindowKind`, `v68ElevenWindowStart`,
    `v68ElevenWindowStop` baked in. V68's witness invokes it directly:
    `exact h_eleven_window_mass_certified_at_356565_modeJ10 K`. This
    matches the witness's `hMassTotal` cell shape after the
    `c_value = v68CValue`, `ρStart = v68ElevenWindowStart`, etc.,
    substitutions land via the `refine ⟨v68ElevenWindowStart, …⟩`
    instantiation.

  * **`c_value` aliasing**: declare `def c_value : ℝ := 71313 / 200000`
    in the V68 candidate so that `ValidKorenblumBound c_value` refers
    to the same constant as the oracle axiom's `v68CValue`. The
    Evaluator's literal-rational extraction requires the literal form
    `71313 / 200000` (Python's `Fraction(71313, 200000)`), not the
    unreduced `356565 / 1000000` (which is the same number but a
    different literal — Lean's `def c_value : ℝ := 356565 / 1000000`
    would give the same value, but the Evaluator reads the literal
    AST and may not canonicalize). **Use `71313 / 200000` exactly.**
    All `c_value`-bearing theorems in V68 (`c_value_pos`, etc.) can
    `unfold c_value v68CValue` and then `norm_num`.

  * **`hH2_v68` parametricity**: same shape as `hH2_v67` /
    `hH2_v66` / `hH2_v64`. Instantiate twice in the witness body
    (once for `a`, once for `b`) when invoking
    `V63.Summability.six_summability_shapes_from_h2`.

  * **The c-push is +1e-6, the smallest in project history.** This is
    deliberate and acceptable: the score gate is `c_value > c_prev`,
    not `c_value ≥ c_prev + threshold`. The Phase-0 margin
    `+1.0048e-4` is ~26 orders of magnitude above the strict-margin
    floor `10⁻³⁰` and 4.75% above the 1e-4 acceptance threshold.

  * **Generator capability budget**: ~1300-1500 lines across files.
    If `Candidates/V68/ElevenWindowEndpoints.lean` exceeds 850 lines,
    consider factoring the ten mode τ-bound theorems into a parametric
    `tau_bounds_at_mode_j (j : Fin 11) : …` (collapsing twenty
    discharges to one — but only if the generator finds it natural;
    do not introduce new axioms while factoring).

  * **No new files in `Proof/`**. The new file lives under
    `Candidates/V68/`. Do edit `Proof/Reduction.lean` (append-only,
    same pattern as sprint 090); do not modify any existing helper or
    axiom there.

  * **First-time exercise of `OneModeTail.tau k` for k ∈ {7, 8, 9}**:
    sprint 091's honesty notes flag this as a structural extension
    point. The `tau k = k(k+2)/(k+1)² = 1 - 1/(k+1)²` definition is
    parametric in `k : ℕ` and `unfold OneModeTail.tau; norm_num`
    should succeed mechanically at any k. V67 exercised k = 0, 1, 2,
    3, 4, 5, 6, 7 cleanly via this shape; V68 extends to k = 7, 8, 9
    (sprint 091's witness already showed k = 9 is the deepest the
    eleven-window architecture reaches).

  * **Forward to sprint 093** (for context, not for action this
    sprint): once V68 ships, sprint 091's union-exhaustion of the
    architectural surface (sprint 089 ∪ sprint 091 directions
    E1/E2/E3) means the c-push surface is genuinely exhausted at the
    seven-window-and-its-extensions design level. The next c-push
    must come from a structurally different idea: per-k cross-coupling
    derived theorem (sprint 077's mathematical content lifted into
    Lean, exercising V63's existing parametric integrability), a
    tightened H(c, ρ) envelope on the deep band via Wang Lemma 2 /
    Fourier orthogonality derivation as a per-candidate derived
    theorem, or a variable-α kernel Phase-0 re-sweep at finer α-grid.
    Sprint 093 may also pivot to trust-surface compaction (`hH2_v6×`
    / `hCircleGapInt_v6×` migration) if the next planner judges the
    c-push axis genuinely closed.
