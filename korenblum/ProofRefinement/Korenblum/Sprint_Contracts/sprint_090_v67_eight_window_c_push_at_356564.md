# Sprint 090: V67 eight-window c-push at `c = 89141/250000` via the mixed-kernel reducer at `n = 7`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V66.lean` (V66 is the live ceiling at
`356562/1000000`; V67 inherits V66's `h_witness` shape extended for one
additional per-mode window).
**Target file**: `Candidates/V67.lean` plus per-candidate derived-theorem
files under `Candidates/V67/`, plus oracle infrastructure in
`Proof/Reduction.lean`, `Numerical_Library/rigorous_scalar.py`,
`lemma.toml`.
**Direction**: raise-c

## Goal

Ship `Candidates/V67.lean` proving `ValidKorenblumBound (89141/250000)`
by invoking sprint 086's mixed-kernel multi-window reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` with
`n = 7` (i.e. `Fin 8` windows) over the eight-window split sprint 089's
adaptive sweep pinned (`Scratch/sprint_089_witness.txt`):

| i | kind        | ρStart                              | ρStop                               |
|---|-------------|-------------------------------------|-------------------------------------|
| 0 | `branch1`   | `c · (1 + 1/1000000000)`            | `c · sqrt(64/63)`                   |
| 1 | `modeJ 7`   | `c · sqrt(64/63)`                   | `c · sqrt(49/48)`                   |
| 2 | `modeJ 6`   | `c · sqrt(49/48)`                   | `c · sqrt(36/35)`                   |
| 3 | `modeJ 5`   | `c · sqrt(36/35)`                   | `c · sqrt(25/24)`                   |
| 4 | `modeJ 4`   | `c · sqrt(25/24)`                   | `c · sqrt(16/15)`                   |
| 5 | `modeJ 3`   | `c · sqrt(16/15)`                   | `c · sqrt(9/8)`                     |
| 6 | `modeJ 2`   | `c · sqrt(9/8)`                     | `c · sqrt(4/3)`                     |
| 7 | `modeJ 1`   | `c · sqrt(4/3)`                     | `1 - 1/1000000000`                  |

with `c = v67CValue = 89141/250000 = 356564/1000000` (i.e.
`c_value_v67 = 89141/250000`, the canonical-rational reduction of
`356564/1000000`).

The τ-band ratios pinned by sprint 089's witness are:

```
mode7 :  τ_6 = 1 - 1/49 = 48/49      ↔  ρ² = c² · 49/48
mode6 :  τ_5 = 1 - 1/36 = 35/36      ↔  ρ² = c² · 36/35
mode5 :  τ_4 = 1 - 1/25 = 24/25      ↔  ρ² = c² · 25/24
mode4 :  τ_3 = 1 - 1/16 = 15/16      ↔  ρ² = c² · 16/15
mode3 :  τ_2 = 1 -  1/9 =  8/9       ↔  ρ² = c² ·  9/8
mode2 :  τ_1 = 1 -  1/4 =  3/4       ↔  ρ² = c² ·  4/3
mode1 :  τ_0 = 0                      ↔  upper edge ρ = 1 - 1/10⁹
```

Branch.one residual box `[c · (1 + 1e-9), c · sqrt(64/63)]` retains the
`τ_7 = 1 - 1/64 = 63/64` upper edge; this is the only Branch.one window
in the partition.

The joint-mass cell is discharged by a **new oracle axiom**
`h_eight_window_mass_certified_at_356564_modeJ7` (added in this
sprint), backed by a new wrapper
`Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
(name reused from the user prompt; despite the `seven_window` name
prefix the wrapper actually pins the eight-window architecture
sprint 089 found). Live margin per sprint 089: **+1.183e-4** at
`(dps, n_trunc) = (80, 300)`.

The `c_value` constant on V67's candidate side is
`89141/250000 = 356564/1000000`, strictly above V66's
`178281/500000 = 356562/1000000` by `+2/1000000 ≈ +2e-6`.

## Why

Sprint 089's adaptive Phase-0 sweep delivered a complete witness for an
eight-window architecture (one Branch.one residual box + seven per-mode
windows for `j ∈ {7, 6, 5, 4, 3, 2, 1}`) at the c-ceiling
`c = 89141/250000` with full-envelope margin `+1.183e-4`. The `+2e-6`
push above V66 is the smallest c-push in the project's history but
**strictly positive** and **full-envelope-margin-robust** (~26 orders of
magnitude above the strict-margin floor).

The sprint is heavily templated on already-shipped sprints:

  * Sprint 087 (oracle wrapper + helper defs in `Proof/Reduction.lean`
    + oracle row in `lemma.toml` for the seven-window architecture).
  * Sprint 088 (V66 candidate body composing the mixed reducer over
    `Fin 7`, plus `Candidates/V66/SevenWindowEndpoints.lean` and
    `Candidates/V66/Branch1Integrability.lean`).

The structural delta from V66 to V67 is:

  1. **Eight windows instead of seven**: one Branch.one box (vs three
     in V66) + seven per-mode windows for `j ∈ {7, 6, 5, 4, 3, 2, 1}`
     (vs four for `j ∈ {4, 3, 2, 1}` in V66). Net +1 window total.
  2. **Three additional mode τ-bound discharges**: `tau_six_le_…` /
     `c_sq_div_start_mode7_sq_le_tau_seven_…` for j=7, similar for
     j=6 and j=5 (V66 already covers j=4, 3, 2, 1 in
     `SevenWindowEndpoints`). The V63 parametric integrability
     `modeScalarIntegrand_intervalIntegrable` is already universally
     quantified in `j ≥ 1`, so it covers j=5, 6, 7 with no new file.
  3. **Two Branch.one boxes deleted**: V66's three Branch.one boxes
     `[c·(1+1e-6), c·sqrt(50/49)]`, `[c·sqrt(50/49), c·sqrt(36/35)]`,
     `[c·sqrt(36/35), c·sqrt(25/24)]` collapse into a single deeper
     box `[c·(1+1e-9), c·sqrt(64/63)]`. **`Branch1Integrability.lean`
     applies as-is** to the single residual box (the integrand is
     identical, the constant bound `24/c⁶` is the same — just a
     different `[a, b]` interval). V67 imports
     `Candidates/V66/Branch1Integrability.lean` directly to get the
     parametric `branch1ScalarIntegrand_intervalIntegrable`.
  4. **`ρ_top = 1 - 1e-9` instead of `1 - 1e-6`**: a finer upper
     edge for mode1, requested by sprint 089's witness. This is a
     `norm_num` change in the V67-namespaced `stop7_lt_one`
     theorem; no new lemma needed.
  5. **`δ_lo = 1e-9` instead of `1e-6`**: the Branch.one box's
     start is `c · (1 + 1e-9)` instead of `c · (1 + 1e-6)`. This
     affects only `c_lt_start0` (a `norm_num` change).

The c-push is small (+2e-6) but the work is **almost entirely
mechanical reuse**:

  * **Reuses 100% of V63 derived files** (Integrability, Summability,
    DiskInnerSeriesBridge) — universally `j`-parametric.
  * **Reuses 100% of V66/Branch1Integrability.lean** — parametric in
    `[a, b]`.
  * **Endpoints file** is V66/SevenWindowEndpoints.lean +3 mode τ-bound
    theorems (j=5, 6, 7), -2 Branch.one branchSplit theorems (only one
    box now), updated geometric ordering.
  * **Wrapper** is sprint 087's wrapper + 3 mode-window helpers for
    j=5/6/7 (the modular `_mode_window_mass` helper accepts `j` as
    parameter; only the Python sweep call sites change).
  * **V67 candidate body** is V66's body with one extra `fin_cases`
    branch in `hModeJ` and `hIntKind`, and two fewer Branch.one
    branches.

### Three (and more) distinct directions considered

1. **Direction A — this sprint: ship V67 in one session via the
   prior planner's recommendation.** Single sprint composing V63 derived
   files + V66/Branch1Integrability + new V67/EightWindowEndpoints + new
   wrapper + new oracle row + helper defs in `Proof/Reduction.lean` +
   new free axiom `h_eight_window_mass_certified_at_356564_modeJ7` +
   `hH2_v67` / `hCircleGapInt_v67` inline seed axioms + thin V67
   candidate. **Strongest objection**: scope risk —
   ~4 deliverables (wrapper, helper-defs+axiom, endpoints file, V67
   candidate) plus seed-axiom registry edits in one session. **Counter**:
   sprint 088 successfully shipped 3 new files for V66 *and* consumed an
   already-registered oracle, in one session. V67 swaps in one new
   oracle (mechanical via sprint 087's template, no new analytic
   content) and one new endpoints file (V66's +3 mode τ-bounds, -2
   branchSplit constraints), and reuses Branch1Integrability as-is.
   Net Lean line count is *similar to or smaller than* V66's. Concrete
   prior-art witness: sprint 088 itself.

2. **Direction B — partition: sprint 090a ships only the wrapper +
   oracle row + helper defs + free axiom in `Proof/Reduction.lean` (no
   candidate, V66-tie). Sprint 090b ships V67.** **Strongest objection**:
   pure-infrastructure sprint with no candidate ship leaves the score
   unchanged for a sprint. The directive prompt explicitly says "Prefer
   the c-push attempt if budget allows" and characterises the partition
   as a fallback. The work is structurally bounded for one session.
   **Demoted** in favor of Direction A; if Direction A blocks at the
   candidate level, the BLOCKED stop condition documents the partial
   delivery and sprint 091 finishes V67 (functionally equivalent to
   the partition).

3. **Direction C — abandon V67 in favor of trust-surface compaction**:
   replace `hH2_v6×` / `hCircleGapInt_v6×` per-candidate axioms with
   theorems consuming `Section2Assumptions`. **Strongest objection**:
   doesn't push c. Per the Bulletin's sprint-088 row this is "structural
   cleanup that does not move the score". The genuine c-push is queued
   and ready (Direction A), so trust-surface compaction must wait.
   **Demoted.**

4. **Direction D — re-run sprint 089's adaptive sweep at finer
   precision / different parameter space**, on the hypothesis that the
   c-ceiling at `89141/250000` missed headroom. **Strongest objection**:
   sprint 089's sweep was already at `(verify_dps, verify_n_trunc) =
   (80, 300)` and tested four orthogonal relaxations (ρ_top, δ_lo,
   box-split invariance, extra-mode-window count). The next c above
   `89141/250000` (i.e. `356565/1000000`) gave margin `+9.51e-5 < 1e-4`,
   only ~5e-6 below the GO threshold. The architecture's headroom is
   genuinely tight; pushing further requires a structurally different
   idea (per-k α-varying kernel from sprint 077, per-k oracles from
   proposal_002, etc.), not another sweep. **Demoted.**

5. **Direction E — analytic-Lean sprint to derive a tighter version of
   equation (5)'s envelope on a deep band**, possibly using per-k
   cross-coupling. **Strongest objection**: open-ended exploration with
   no precise oracle-backed sub-claim. Highly speculative. Bird-in-hand
   c-push (Direction A) is preferred. **Demoted.**

6. **Direction F — file `proposal_004` for the `hH2_v6×` /
   `hCircleGapInt_v6×` migration into `Section2Assumptions`**. Per the
   four-condition proposal-filing checklist (`AGENT_BRIEF.md`): the
   migration has not been "tried hard and failed" in Lean (there is no
   prior generator session attempting it), and it does not improve
   `c_value`. **Demoted.**

Direction A wins on **expected analytical novelty per session-budget**:
it lands the next strict score push using sprint 089's pinned witness,
exercises the mixed reducer at `n = 7` for the first time on a real
candidate, and produces the workspace's largest-mode-index-yet
per-mode windows (j=5, 6, 7) — three additional analytic τ-bound
discharges that are direct extensions of V66's pattern. If Direction A
blocks at the candidate level, the per-deliverable factoring naturally
degrades into Direction B's outcome via the BLOCKED stop condition.

### Why this is bounded for one session

The work is **directly templated** on previous sprints with strict
incremental scope:

  * **Wrapper** (`certify_seven_window_mass_at_356564_modeJ7`): templated
    on sprint 087's `certify_seven_window_mass_at_356562_sqrt` (~190
    lines). The eight-window architecture has 1 Branch.one helper call
    + 7 per-mode helper calls (vs sprint 087's 3 + 4); the helpers are
    parametric in `j` and the τ-band ratio. Estimated ~200-220 lines
    (similar size, +3 mode-window calls, -2 branch1-window calls).
  * **`Proof/Reduction.lean` extension**: sprint 087's pattern has 4
    helper defs (`v66CValue`, `v66SevenWindowKind`,
    `v66SevenWindowStart`, `v66SevenWindowStop`) + 1 free axiom
    (`h_seven_window_mass_certified_at_356562_sqrt`), totaling ~70 lines
    appended at the bottom of `Reduction.lean` immediately before the
    closing `end`. V67 adds the same shape with `Fin 8` instead of
    `Fin 7` and 8 endpoints instead of 7. Estimated ~80 lines.
  * **`Candidates/V67/EightWindowEndpoints.lean`**: templated on V66's
    `SevenWindowEndpoints.lean` (533 lines). Differences: +3 mode
    τ-bound theorems (j=5, 6, 7), -2 branchSplit theorems (only 1
    Branch.one box), updated geometric-ordering chain (8 endpoints).
    Estimated ~600-650 lines (one expected significant cleanup
    opportunity: a parametric mode-τ-bound theorem indexed by
    `j ∈ {1, …, 7}` could collapse seven discharges to one, but
    is not required).
  * **`Candidates/V67.lean`**: templated on V66.lean (345 lines). The
    `v67_witness` body uses `fin_cases i` over `Fin 8` instead of
    `Fin 7`. Per-mode integrability calls V63's parametric
    `modeScalarIntegrand_intervalIntegrable` seven times (vs V66's
    four); per-window kind dispatch has 7 mode cases + 1 branch1 case
    (vs V66's 4 + 3). Estimated ~370 lines.
  * **`lemma.toml`**: 2 new `[seed_axioms].allowed` entries
    (`hH2_v67`, `hCircleGapInt_v67`), 1 new `[seed_axioms].allowed`
    entry for the new oracle axiom, 1 new `[[oracles]]` row, 2 new
    `[import_policy].allowed_exact` entries (V67 main +
    V67/EightWindowEndpoints). Estimated <50 lines of TOML.

Total: ~1100-1300 lines across files. The Generator's recent track
record (sprints 080-088) routinely lands 400-700-line single-sprint
deliverables; sprint 088 itself shipped V66 in ~1000 lines across three
files. **Bounded for one session.** The only risk is the wrapper's
sympy/mpmath integration plumbing, which is mechanical reuse of
sprint 087's template.

## Concrete edits expected

### 1. `Numerical_Library/rigorous_scalar.py` (modify)

Add new wrapper function `certify_seven_window_mass_at_356564_modeJ7`
(name per the user prompt; despite the `seven_window` name prefix the
wrapper pins the eight-window architecture). Templated on sprint 087's
`certify_seven_window_mass_at_356562_sqrt`. The wrapper:

  * Pins `c = mp.mpf("89141") / mp.mpf("250000")`.
  * Computes the eight-window endpoint sequence using sprint 089's
    sqrt ratios `[64/63, 49/48, 36/35, 25/24, 16/15, 9/8, 4/3]` plus
    `(1 + 1e-9)` as the box-A start factor and `(1 - 1e-9)` as
    `ρ_top`.
  * Calls the existing `_mode_window_mass(j, c, ρ_a, ρ_b, dps, n_trunc)`
    helper at `j ∈ {7, 6, 5, 4, 3, 2, 1}` and the existing
    `_branch1_window_mass(c, ρ_a, ρ_b, dps, n_trunc)` helper at the
    single Branch.one residual box.
  * Sums to a rational total mass at `(dps=80, n_trunc=300)`,
    asserts `total ≥ 1`, and returns `Fraction(1, 1)` if so. Margin
    floor: `1e-30` (well below the live `+1.18e-4`).
  * Live-test signature: `certify_seven_window_mass_at_356564_modeJ7()
    → Fraction(1, 1)`.

The existing helpers `_mode_window_mass` and `_branch1_window_mass`
are parametric in `j` (mode) and `[a, b]` (box), so no new helper
definitions are required. The wrapper is purely a new top-level
function.

If the existing `_mode_window_mass` helper's `j` parameter is bounded
(e.g. hardcoded `j ∈ {1, 2, 3, 4}`), generalize it to arbitrary
`j ≥ 1` in this sprint; sprint 087 used `j` as a free formal parameter
already, so likely no change is needed. **Verify** by reading the
helper before duplicating; if the helper hardcodes `j ∈ {1, 2, 3, 4}`,
add a path for `j ∈ {5, 6, 7}` (uniform shape; the `H_j(c, ρ) =
(j/(j+1))·c^(2j+2)/ρ^(2j)` formula is uniform in `j`).

Live-test the wrapper before shipping:
```bash
env UV_CACHE_DIR=korenblum/.uv-cache uv run python -c "
from Numerical_Library.rigorous_scalar import certify_seven_window_mass_at_356564_modeJ7
print(certify_seven_window_mass_at_356564_modeJ7())
"
```
Expected output: `1` (i.e. `Fraction(1, 1)`).

### 2. `Proof/Reduction.lean` (extend)

Append immediately before `end ProofRefinement.Korenblum`, after the
existing sprint-087 `v66*` defs and `h_seven_window_mass_certified_at_356562_sqrt`
axiom (lines 9487-9555):

```lean
/-- V67 c-value: `89141/250000 = 356564/1000000` (sprint 089 GO ceiling). -/
def v67CValue : ℝ := 89141 / 250000

/-- Eight-window kind dispatch: 1 Branch.one + 7 per-mode windows
    j ∈ {7, 6, 5, 4, 3, 2, 1}. -/
def v67EightWindowKind : Fin 8 → KernelKind
  | ⟨0, _⟩ => KernelKind.branch1
  | ⟨1, _⟩ => KernelKind.modeJ 7
  | ⟨2, _⟩ => KernelKind.modeJ 6
  | ⟨3, _⟩ => KernelKind.modeJ 5
  | ⟨4, _⟩ => KernelKind.modeJ 4
  | ⟨5, _⟩ => KernelKind.modeJ 3
  | ⟨6, _⟩ => KernelKind.modeJ 2
  | ⟨7, _⟩ => KernelKind.modeJ 1

/-- Eight-window window-start sequence. -/
def v67EightWindowStart : Fin 8 → ℝ
  | ⟨0, _⟩ => v67CValue * (1 + 1 / 1000000000)
  | ⟨1, _⟩ => v67CValue * Real.sqrt (64 / 63)
  | ⟨2, _⟩ => v67CValue * Real.sqrt (49 / 48)
  | ⟨3, _⟩ => v67CValue * Real.sqrt (36 / 35)
  | ⟨4, _⟩ => v67CValue * Real.sqrt (25 / 24)
  | ⟨5, _⟩ => v67CValue * Real.sqrt (16 / 15)
  | ⟨6, _⟩ => v67CValue * Real.sqrt (9 / 8)
  | ⟨7, _⟩ => v67CValue * Real.sqrt (4 / 3)

/-- Eight-window window-stop sequence. -/
def v67EightWindowStop : Fin 8 → ℝ
  | ⟨0, _⟩ => v67CValue * Real.sqrt (64 / 63)
  | ⟨1, _⟩ => v67CValue * Real.sqrt (49 / 48)
  | ⟨2, _⟩ => v67CValue * Real.sqrt (36 / 35)
  | ⟨3, _⟩ => v67CValue * Real.sqrt (25 / 24)
  | ⟨4, _⟩ => v67CValue * Real.sqrt (16 / 15)
  | ⟨5, _⟩ => v67CValue * Real.sqrt (9 / 8)
  | ⟨6, _⟩ => v67CValue * Real.sqrt (4 / 3)
  | ⟨7, _⟩ => 1 - 1 / 1000000000

/-- Joint-mass oracle for V67's eight-window architecture. Backed by
    `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
    via the `[[oracles]]` row in `lemma.toml`. -/
axiom h_eight_window_mass_certified_at_356564_modeJ7
    (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤ ∑ i : Fin 8,
      match v67EightWindowKind i with
      | KernelKind.modeJ j =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            ModeBridge.scalarIntegrand v67CValue j
              (WangOuter.paperLambda K v67CValue) ρ
      | KernelKind.branch1 =>
          ∫ ρ in (v67EightWindowStart i)..(v67EightWindowStop i),
            Korenblum.scalarIntegrand1 v67CValue
              (WangOuter.paperLambda K v67CValue) ρ
```

**Important**: the axiom body must match the kind-dispatched joint-mass
cell of the sprint 086 mixed reducer **byte-for-byte** (modulo the
sprint-090-specific `c`, `kind`, `start`, `stop` defs). Compare
character-by-character against sprint 087's
`h_seven_window_mass_certified_at_356562_sqrt` axiom body
(lines 9543-9555).

### 3. `Candidates/V67/EightWindowEndpoints.lean` (new file)

Per-candidate derived-theorem file, scope is V67 only. **No `axiom`s,
no `sorry`s, no `Section2Assumptions` field extensions.** Imports:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge
import KorenblumPaper.PaperAxioms     -- for branchSplit
import ProofRefinement.Korenblum.Proof.Reduction
```

Required theorems (templated on V66/SevenWindowEndpoints.lean):

  * **Seven mode τ-bound pairs** at the seven mode windows:
    - mode7: `tau_six_le_c_sq_div_stop1_sq` (i.e.
      `τ_6 = 48/49 ≤ c²/(c·sqrt(49/48))² = 48/49`),
      `c_sq_div_start1_sq_le_tau_seven` (i.e.
      `c²/(c·sqrt(64/63))² = 63/64 ≤ τ_7 = 63/64`).
    - mode6: similar at j=6.
    - mode5: similar at j=5.
    - mode4: identical to V66's at j=4 (template).
    - mode3: identical to V66's at j=3 (template).
    - mode2: identical to V66's at j=2 (template).
    - mode1: identical to V66's at j=1 (template, with `ρ_top = 1 - 1e-9`).

    Pattern (templated byte-for-byte on V64 lines 67-104 and V66's
    `SevenWindowEndpoints.lean`):

    ```lean
    theorem c_sq_div_start_mode7_sq_le_tau_seven {c : ℝ} (hc : 0 < c) :
        c ^ 2 / (c * Real.sqrt (64/63)) ^ 2 ≤ OneModeTail.tau 7 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 64/63)]
      have : c ^ 2 / (c ^ 2 * (64 / 63)) = 63 / 64 := by field_simp
      rw [this]
      unfold OneModeTail.tau
      norm_num
    ```

  * **Single Branch.one window's `branchSplit` constraint**: `c ·
    sqrt(64/63) ≤ branchSplit c = c · sqrt(4/3)`. Single-line
    `mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by norm_num : (64/63 :
    ℝ) ≤ 4/3)) c_nonneg`.

  * **Eight-way geometric ordering**: `c < ρStart 0 ≤ ρStop 0 = ρStart
    1 ≤ … ≤ ρStop 7 < 1` at `c = v67CValue`. Seven adjacency equations
    are by `rfl` (definitional via `v67EightWindowStart` /
    `v67EightWindowStop` line-up). The remaining inequalities chain
    through `Real.sqrt`-monotonicity:

    ```lean
    theorem c_lt_start0 : v67CValue < v67EightWindowStart 0 := by
      unfold v67CValue v67EightWindowStart
      norm_num
    theorem stop7_lt_one : v67EightWindowStop 7 < 1 := by
      unfold v67EightWindowStop
      norm_num
    theorem start_i_le_stop_i (i : Fin 8) :
        v67EightWindowStart i ≤ v67EightWindowStop i := by
      fin_cases i <;>
        (try unfold v67EightWindowStart v67EightWindowStop;
         apply mul_le_mul_of_nonneg_left _ (by norm_num [v67CValue] : (0:ℝ) ≤ v67CValue);
         exact Real.sqrt_le_sqrt (by norm_num))
    theorem adj_i (i : Fin 7) :
        v67EightWindowStop i.castSucc = v67EightWindowStart i.succ := by
      fin_cases i <;> rfl
    theorem c_lt_start_i (i : Fin 8) : v67CValue < v67EightWindowStart i := by
      …  -- lift c_lt_start0 + monotonicity
    theorem stop_i_le_one (i : Fin 8) : v67EightWindowStop i ≤ 1 := by
      …
    theorem c_le_start_i (i : Fin 8) : v67CValue ≤ v67EightWindowStart i :=
      fun i => le_of_lt (c_lt_start_i i)
    ```

  * **mode index facts**: `hj_pos i j (h : v67EightWindowKind i =
    KernelKind.modeJ j) : 1 ≤ j` — by `fin_cases i` + `cases h`,
    yielding `j ∈ {1, 2, 3, 4, 5, 6, 7}`.

### 4. `Candidates/V67.lean` (new file)

The candidate body, templated on V66.lean. Imports:

```lean
-- @parent V66
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
import ProofRefinement.Korenblum.Candidates.V67.EightWindowEndpoints
```

Required content:

```lean
namespace ProofRefinement.Korenblum.Candidates.V67

def c_value : ℝ := v67CValue   -- 89141 / 250000 = 356564 / 1000000

theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value, v67CValue]
theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value, v67CValue]
theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- V67's c strictly improves on V66's `178281/500000 = 356562/1000000`. -/
theorem c_value_gt_v66 : (178281 : ℝ) / 500000 < c_value := by
  norm_num [c_value, v67CValue]

/-- Evaluator-facing oracle bound-field. Matches the
    `bound_field = "eight_window_mass_lower"` row in `lemma.toml`. -/
def eight_window_mass_lower : ℝ := 1

/-- branchSplit < 1 at c_value. -/
theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 := by
  unfold PaperAxioms.branchSplit
  -- c_value · sqrt(4/3) ≤ 0.356564 · 1.156 < 1
  …

/-- Free per-candidate axiom: H² boundary-norm finiteness. Templated on V66/V64. -/
axiom hH2_v67 : ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Free per-candidate axiom: 2ρ·circleGap integrability on (c, 1). Templated on V66/V64. -/
axiom hCircleGapInt_v67 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-- The h_witness predicate for the mixed reducer at n = 7. -/
theorem v67_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin 8 → ℝ) (kind : Fin 8 → KernelKind),
        … (full body of the mixed reducer's h_witness, instantiated at
           v67EightWindowStart, v67EightWindowStop, v67EightWindowKind) … := by
  intro a b K paper
  refine ⟨v67EightWindowStart, v67EightWindowStop, v67EightWindowKind,
          …⟩
  -- Per-cell discharge: V67/EightWindowEndpoints + V63 derived files +
  -- V66/Branch1Integrability + the new oracle.
  …
  case hMassTotal =>
    exact h_eight_window_mass_certified_at_356564_modeJ7 K

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v67_witness paper)

end ProofRefinement.Korenblum.Candidates.V67
```

The witness body's per-`i` dispatch:

  * `hModeJ` cell: `fin_cases i`. For `i = 0` (Branch.one), `cases hKind`.
    For `i ∈ {1, 2, 3, 4, 5, 6, 7}` (modeJ 7, 6, 5, 4, 3, 2, 1), invoke
    the corresponding `EightWindowEndpoints` τ-bound pair.
  * `hBranch1Split` cell: `fin_cases i`. For `i = 0`, invoke
    `EightWindowEndpoints.stop0_le_branchSplit`. For `i ∈ {1, …, 7}`,
    `cases hKind` (rejects branch1).
  * `hIntKind` cell: 8-way `fin_cases i` with kind dispatch:
    - `i = 0` (branch1): invoke
      `V66.Branch1Integrability.branch1ScalarIntegrand_intervalIntegrable`
      directly with the V67 endpoints.
      **Or** ship a thin V67-namespaced consolidation
      `v67_branch1_one_window_intervalIntegrable` mirroring V66's
      `v66_branch1_three_window_intervalIntegrable` but for one box.
    - `i ∈ {1, …, 7}` (modeJ): invoke
      `V63.Integrability.modeScalarIntegrand_intervalIntegrable`
      (parametric in `j`) at j=7, 6, 5, 4, 3, 2, 1 respectively.
  * `hPlusDisk`, `hPlusSigma`, `hMinusDisk`, `hMinusSigmaC`,
    `hMinusWeight`, `hMinusSigma`: invoke `V63.Summability.six_summability_shapes_from_h2`
    with `(hH2_v67 a)`, `(hH2_v67 b)`, `c_value_nonneg`, `c_value_lt_one`.
  * `hIntCircle`: `exact hCircleGapInt_v67 a b`.
  * `hInner`: invoke `V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess`
    with the kit and the absolute-summability witness, exactly as in V66.
  * `hMassTotal`: `exact h_eight_window_mass_certified_at_356564_modeJ7 K`.

### 5. `lemma.toml` updates (inline, no proposal)

Add to `[seed_axioms].allowed`:

  * `"hH2_v67"`,
  * `"hCircleGapInt_v67"`,
  * `"h_eight_window_mass_certified_at_356564_modeJ7"`.

Add to `[[oracles]]` (new table entry):

```toml
[[oracles]]
axiom = "h_eight_window_mass_certified_at_356564_modeJ7"
bound_field = "eight_window_mass_lower"
wrapper = "Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7"
# (note: wrapper name retained from sprint 089's witness for backwards
# consistency; despite the `seven_window` prefix it pins the
# eight-window architecture.)
```

Add to `[import_policy].allowed_exact`:

  * `"ProofRefinement.Korenblum.Candidates.V67"`,
  * `"ProofRefinement.Korenblum.Candidates.V67.EightWindowEndpoints"`.

### 6. `Bulletin.md` and `Experience.md` append

Append one row each per the standard pattern:

  * The score push (`356562/1000000 → 356564/1000000`, `+2e-6` above
    V66, +1.14e-4 above V52).
  * V67's audit set: standard Lean axioms + `hH2_v67` +
    `hCircleGapInt_v67` +
    `h_eight_window_mass_certified_at_356564_modeJ7` (the latter at
    `ProofRefinement.Korenblum.h_eight_window_mass_certified_at_356564_modeJ7`,
    not a candidate-namespace copy).
  * One new derived-theorem file
    (`Candidates/V67/EightWindowEndpoints.lean`) plus reuse of
    `Candidates/V66/Branch1Integrability.lean`.
  * Forward direction: sprint 091 either pushes c again (a structurally
    different idea is needed; the seven-window architecture's headroom
    is exhausted at `89141/250000` per sprint 089's findings — the
    next move is per-k oracles, per-k cross-coupling, or a tighter
    `H(c, ρ)` envelope) OR tightens the trust surface
    (`hH2_v6×`/`hCircleGapInt_v6×` migration into `Section2Assumptions`).

### 7. NOT modified

  * `KorenblumPaper/` (read-only).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * Any V0-V66 candidate file (V66 stays at `178281/500000`; the new
    seed-axiom and oracle additions do not perturb V64-V66 audit sets).
  * Any V63 derived file (Integrability/Summability/DiskInnerSeriesBridge
    reused as-is).
  * Any V64 derived file (TauWindowEndpoints is V64-specific; V67 has
    its own EightWindowEndpoints).
  * `Candidates/V66/SevenWindowEndpoints.lean` (V66-specific).
  * `Candidates/V66/Branch1Integrability.lean` is **reused directly**
    (the file's `branch1ScalarIntegrand_intervalIntegrable` is
    parametric in `[a, b]`, so V67's single-box invocation calls it
    with V67 endpoints; no edit to the V66 file).
  * The existing `[[oracles]]` row for `h_two_window_mass_certified_at_35646_sqrt`
    or `h_seven_window_mass_certified_at_356562_sqrt`.
  * `Proposals/` (no proposal filed; per the four-condition checklist
    in `AGENT_BRIEF.md`, this is an inline-pattern oracle addition).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V67` succeeds.

2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V67.lean` succeeds with
   `pass: true`.

3. The Evaluator's reported `score` (`= c_value`) is `89141/250000`
   (= `356564/1000000`), strictly greater than V66's `178281/500000`
   (= `356562/1000000`). The `score` field in
   `Refinement_Log/log.jsonl` reflects this.

4. `axioms_used` in V67's audit consists of standard Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`, optionally
   `Lean.ofReduceBool` / `Lean.trustCompiler`) plus exactly:

     * `ProofRefinement.Korenblum.Candidates.V67.hH2_v67`,
     * `ProofRefinement.Korenblum.Candidates.V67.hCircleGapInt_v67`,
     * `ProofRefinement.Korenblum.h_eight_window_mass_certified_at_356564_modeJ7`.

   No other free axioms; no `sorryAx`. `[seed_axioms].allowed` contains
   all three names.

5. The oracle audit on V67 reports `oracle=1, declared=1, ok=true` for
   the row `axiom = "h_eight_window_mass_certified_at_356564_modeJ7"`,
   `bound_field = "eight_window_mass_lower"`. V67's
   `def eight_window_mass_lower : ℝ := 1` exposes the matching
   bound-field.

6. The numerical wrapper
   `Numerical_Library.rigorous_scalar.certify_seven_window_mass_at_356564_modeJ7`
   is live-tested **before** the evaluator run and returns
   `Fraction(1, 1)` (i.e. integer 1). The Phase 0 margin recorded in
   `Scratch/sprint_089_witness.txt` (`+1.183e-4` at `(dps=80,
   n_trunc=300)`) is reproduced or exceeded.

7. `lake build ProofRefinement.Korenblum.Candidates.V64`,
   `lake build ProofRefinement.Korenblum.Candidates.V65`, and
   `lake build ProofRefinement.Korenblum.Candidates.V66` continue to
   succeed (regression: the new seed-axiom and oracle additions do not
   perturb older candidates).

8. `Bulletin.md` and `Experience.md` each gain one row per the standard
   pattern, naming the c-push, the new files, the audit extension, and
   the forward direction.

## Out of scope

  * Push `c_value` beyond `89141/250000`. Sprint 089's sweep
    documented this as the c-ceiling for the eight-window architecture
    at `(verify_dps, verify_n_trunc) = (80, 300)`. Pushing further
    requires a structurally different idea (per-k oracle, variable-α
    kernel, etc.) — sprint 091+ work.
  * Replace `hH2_v67` / `hCircleGapInt_v67` with derivations from
    `Section2Assumptions`. Trust-surface tightening is a separate
    direction; sprint 090's job is the c-push.
  * Edit any V63-V66 derived file. V67 imports them as-is.
  * Hoist V66/Branch1Integrability into `Proof/`. It is reused as-is via
    direct import.
  * Edit `Proof/Main.lean`, `Proof/CandidateContract.lean`, or any
    `KorenblumPaper/` file (read-only).
  * Modify the existing sprint-087 `v66*` defs or
    `h_seven_window_mass_certified_at_356562_sqrt` axiom in
    `Proof/Reduction.lean` (load-bearing for V66; this sprint only
    appends new defs and a new axiom alongside).
  * Modify `Numerical_Library/rigorous_scalar.py`'s existing wrappers
    `certify_two_window_mass_at_35646_sqrt` and
    `certify_seven_window_mass_at_356562_sqrt` (load-bearing for V64
    and V66; this sprint only adds a new wrapper alongside).
  * File `proposal_004`. The seed-axiom and oracle additions are
    inline-pattern (per `Proposals/README.md` "Do not use a proposal
    for … new oracle registry entries that are already fully specified
    and directly consumed by the current sprint").

## Time budget

≤ 240 minutes runtime.

  * `Numerical_Library/rigorous_scalar.py` wrapper: ~40 minutes
    (sprint 087's 190-line wrapper is the template; +3 mode-window
    helper calls, -2 box-window helper calls; live-test against
    sprint 089's witness).
  * `Proof/Reduction.lean` extension (4 helper defs + 1 free axiom):
    ~20 minutes (mechanical mirror of sprint 087's pattern).
  * `Candidates/V67/EightWindowEndpoints.lean`: ~75 minutes
    (templated on V66's 533-line `SevenWindowEndpoints.lean`; +3 mode
    τ-bound theorems for j=5/6/7, -2 branchSplit theorems, updated
    geometric ordering for `Fin 8`).
  * `Candidates/V67.lean`: ~50 minutes (templated on V66.lean's 345
    lines; the witness body uses `fin_cases` over `Fin 8` with kind
    dispatch).
  * `lemma.toml`: ~10 minutes (3 seed-axiom entries + 1 oracle row + 2
    import-policy entries).
  * Bulletin/Experience appends: ~10 minutes.
  * Build + Evaluator regression: ~35 minutes.

## Stop conditions

  * **Wrapper live-tests, all eight-window τ-bounds, branchSplit
    constraint, integrabilities, and the joint-mass discharge typecheck;
    V67 builds; Evaluator reports `pass: true` with `score =
    89141/250000` and the audit set above**: `STATUS=READY_FOR_EVALUATION`.
    The harness gains its third consecutive c-push past V52.

  * **The wrapper live-test fails** (returns `Fraction(0, 1)` or some
    non-1 rational, or raises): document the failing margin or error
    at `Scratch/sprint_090_obstruction.md` and `STATUS=BLOCKED`.
    Sprint 091 either re-tunes the wrapper (e.g. higher `dps`) or
    chooses a smaller c with more headroom.

  * **The `v67_witness` body fails to typecheck on a specific cell**
    (e.g. a τ-bound discharge for j=5/6/7, an integrability invocation,
    the joint-mass cell): ship the per-candidate derived-theorem files
    (`EightWindowEndpoints.lean`) and the wrapper / oracle-row /
    helper-def-and-axiom infrastructure anyway if they typecheck and
    live-test standalone, and document the specific witness-cell
    obstruction at `Scratch/sprint_090_obstruction.md` with the exact
    unification error or unprovable goal. `STATUS=BLOCKED`. Sprint 091
    picks up with the candidate alone.

  * **The Branch.one integrability for V67's single residual box
    `[c·(1+1e-9), c·sqrt(64/63)]` reveals that `Candidates/V66/Branch1Integrability.lean`
    is not parametric enough** (e.g. its theorem statement bakes in
    V66's specific endpoints): document the missing parametricity at
    `Scratch/sprint_090_obstruction.md` and either (a) generalize
    `branch1ScalarIntegrand_intervalIntegrable` *in this sprint* if
    the generalization is one-line (replace V66-specific endpoints with
    universal `[a, b]`), or (b) ship a fresh
    `Candidates/V67/Branch1Integrability.lean` mirroring V66's body
    with V67's endpoints. Either path keeps `STATUS=READY_FOR_EVALUATION`
    if otherwise complete.

  * **A new free axiom beyond `hH2_v67` / `hCircleGapInt_v67` /
    `h_eight_window_mass_certified_at_356564_modeJ7` would be
    required**: do not ship it. Document at
    `Scratch/sprint_090_obstruction.md` and `STATUS=BLOCKED_NEEDS_HUMAN`.
    (Highly unlikely — V64's three free axioms cover the analogous
    chain, and the j=5/6/7 + Branch.one extension does not introduce
    new axiomatically distinct content.)

  * **The oracle audit fails because the candidate-side oracle invocation
    does not unify with the registered axiom in `Proof/Reduction.lean`**:
    the candidate must invoke the axiom via the fully-qualified name
    `ProofRefinement.Korenblum.h_eight_window_mass_certified_at_356564_modeJ7`,
    not redeclare it candidate-side (per the V66 pattern; redeclaring
    would put it in the V67 namespace and break the oracle row's
    axiom-name resolution). `STATUS=BLOCKED` if the unification still
    fails after one round-trip.

## Notes for the generator

  * **Read first**:
    - `Candidates/V66.lean` (your candidate-body template, 345 lines).
    - `Candidates/V66/SevenWindowEndpoints.lean` (your endpoints-file
      template, 533 lines).
    - `Candidates/V66/Branch1Integrability.lean` (113 lines; the
      file you import directly into V67).
    - `Candidates/V63/Integrability.lean`,
      `Candidates/V63/Summability.lean`,
      `Candidates/V63/DiskInnerSeriesBridge.lean` (reuse as-is via
      direct import; do not edit).
    - `Proof/Reduction.lean:9460-9555` (sprint 087's wrapper of helper
      defs + free axiom; **template byte-for-byte** for the V67
      additions, swapping `Fin 7` → `Fin 8`, `v66*` → `v67*`,
      `356562` → `356564`, etc.).
    - `Proof/Reduction.lean:8934` (the mixed reducer's signature; the
      witness shape is fully specified there).
    - `Numerical_Library/rigorous_scalar.py` (`certify_seven_window_mass_at_356562_sqrt`
      function, ~190 lines, your wrapper template).
    - `Scratch/sprint_089_witness.txt` (the exact eight-window endpoint
      sequence + margin + envelope settings).
    - `Scratch/sprint_087_v38_seven_window_mass_sweep.{py,txt}`
      (sprint 087's adaptive Phase 0 sweep + wrapper-derivation
      methodology; analogous structure for sprint 090's wrapper).
    - `KorenblumPaper/PaperEq15.lean` (the
      `Korenblum.scalarIntegrand1` definition; same as V66).
    - `KorenblumPaper/PaperAxioms.lean` (the `branchSplit` definition;
      same as V66).

  * **Wrapper live-test before everything else**: the wrapper is the
    cheapest fail-fast gate. Once it returns `Fraction(1, 1)` against
    sprint 089's pinned endpoints, the rest of the sprint is mechanical.
    If it fails, all downstream Lean work is wasted; abort and document
    at `Scratch/sprint_090_obstruction.md`.

  * **The mixed reducer's witness shape over `Fin 8`** (~32 universal-
    quantifier cells when expanded). Each cell is a one- to five-line
    invocation of an existing derived theorem. Use `fin_cases i`
    heavily: it splits `Fin 8` into eight concrete subgoals, each of
    which can be discharged by a one-line `simp` + theorem invocation.
    The kind dispatch (1 branch1, 7 mode) requires `cases` on `kind i`
    per `i`.

  * **Per-mode integrability for j ∈ {1, …, 7}**: V63's
    `modeScalarIntegrand_intervalIntegrable`
    (`Candidates/V63/Integrability.lean:114`) is parametric in `j`
    with hypothesis `1 ≤ j`. Invoke it directly at j = 7, 6, 5, 4, 3,
    2, 1. **No new mode-window integrability lemma needed.**

  * **Branch.one integrability**: V66/Branch1Integrability provides
    `branch1ScalarIntegrand_intervalIntegrable` parametric in
    `[a, b]`. V67 invokes it at `(v67EightWindowStart 0,
    v67EightWindowStop 0) = (c·(1+1e-9), c·sqrt(64/63))`. **No edit to
    the V66 file.** If that theorem turns out *not* to be parametric
    enough for V67's `[a, b]` (e.g. it's stated for V66's endpoints),
    then either (a) generalize it inline in this sprint to take `[a, b]`
    parameters (one-line `theorem` change), or (b) ship a fresh
    `Candidates/V67/Branch1Integrability.lean` with V67 endpoints
    (~110 lines, templated on V66's).

  * **Adjacency `ρStop i.castSucc = ρStart i.succ` is by `rfl`** —
    sprint 090's defs `v67EightWindowStart` and `v67EightWindowStop`
    line up so that adjacency is definitional. `fin_cases i` + `rfl`
    discharges all seven adjacencies.

  * **The eight-window mass oracle is invoked unchanged after
    declaration.** The axiom
    `h_eight_window_mass_certified_at_356564_modeJ7` (in
    `Proof/Reduction.lean`) takes a single argument `K : ℝ → ℝ → ℝ`
    and asserts the joint-mass inequality with `v67CValue`,
    `v67EightWindowKind`, `v67EightWindowStart`, `v67EightWindowStop`
    baked in. V67's witness invokes it directly:
    `exact h_eight_window_mass_certified_at_356564_modeJ7 K`. This
    matches the witness's `hMassTotal` cell shape after the
    `c_value = v67CValue`, `ρStart = v67EightWindowStart`, etc.,
    substitutions land via the `refine ⟨v67EightWindowStart, …⟩`
    instantiation.

  * **`c_value` aliasing**: declare `def c_value : ℝ := v67CValue` in
    the V67 candidate so that `ValidKorenblumBound c_value` refers to
    the same constant as the oracle axiom's `v67CValue`. All
    `c_value`-bearing theorems in V67 (`c_value_pos`, etc.) can
    `unfold c_value v67CValue` and then `norm_num`.

  * **`hH2_v67` parametricity**: same shape as `hH2_v64` and
    `hH2_v66`. Instantiate twice in the witness body (once for `a`,
    once for `b`) when invoking
    `V63.Summability.six_summability_shapes_from_h2`.

  * **The c-push is +2e-6, the smallest in project history.** This is
    deliberate and acceptable: the score gate is `c_value > c_prev`,
    not `c_value ≥ c_prev + threshold`. The Phase-0 margin
    `+1.183e-4` is ~26 orders of magnitude above the strict-margin
    floor `10^-30`.

  * **Generator capability budget**: ~1100-1300 lines across files. If
    `Candidates/V67/EightWindowEndpoints.lean` exceeds 700 lines,
    consider factoring the seven mode τ-bound theorems into a
    parametric `tau_bounds_at_mode_j (j : Fin 8) : …` (collapsing
    seven discharges to one — but only if the generator finds it
    natural; do not introduce new axioms while factoring).

  * **No new files in `Proof/`**. The new file lives under
    `Candidates/V67/`. Do edit `Proof/Reduction.lean` (append-only,
    same pattern as sprint 087); do not modify any existing helper or
    axiom there.

  * **Forward to sprint 091** (for context, not for action this
    sprint): once V67 ships, the seven-window architecture's c-ceiling
    is exhausted at `89141/250000`. The next sprint must pivot to a
    structurally different c-push idea (per-k oracle from
    `proposal_002`, per-k cross-coupling from `proposal_003`,
    variable-α kernel from sprint 077, or a tightened H(c, ρ) envelope
    on the deep band) OR pivot to trust-surface compaction
    (`hH2_v6×`/`hCircleGapInt_v6×` migration into
    `Section2Assumptions`).
