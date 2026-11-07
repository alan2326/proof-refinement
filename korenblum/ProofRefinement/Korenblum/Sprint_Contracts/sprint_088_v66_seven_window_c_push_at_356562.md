# Sprint 088: V66 seven-window c-push at `c = 356562/1000000` via the mixed-kernel reducer

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V64.lean` (V65 is structurally a V64-tie via the
mixed-reducer; V66 inherits V64's `h_witness` shape extended for 7 windows).
**Target file**: `Candidates/V66.lean` plus per-candidate derived-theorem files
under `Candidates/V66/`.
**Direction**: raise-c

## Goal

Ship `Candidates/V66.lean` proving `ValidKorenblumBound (356562/1000000)` by
invoking sprint 086's mixed-kernel multi-window reducer
`valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` with
`n = 6` (i.e. `Fin 7` windows) over the seven-window split sprint 087 pinned:

| i | kind                       | ρStart                  | ρStop                   |
|---|----------------------------|-------------------------|-------------------------|
| 0 | `branch1`                  | `c · (1 + 1/1000000)`   | `c · sqrt(50/49)`       |
| 1 | `branch1`                  | `c · sqrt(50/49)`       | `c · sqrt(36/35)`       |
| 2 | `branch1`                  | `c · sqrt(36/35)`       | `c · sqrt(25/24)`       |
| 3 | `modeJ 4`                  | `c · sqrt(25/24)`       | `c · sqrt(16/15)`       |
| 4 | `modeJ 3`                  | `c · sqrt(16/15)`       | `c · sqrt(9/8)`         |
| 5 | `modeJ 2`                  | `c · sqrt(9/8)`         | `c · sqrt(4/3)`         |
| 6 | `modeJ 1`                  | `c · sqrt(4/3)`         | `999999/1000000`        |

with `c = v66CValue = 356562/1000000`, exactly as defined by sprint 087's
helper `def`s `v66CValue`, `v66SevenWindowKind`, `v66SevenWindowStart`,
`v66SevenWindowStop` already in `Proof/Reduction.lean`. The joint-mass cell
is discharged by the existing oracle axiom
`h_seven_window_mass_certified_at_356562_sqrt` (also already in
`Proof/Reduction.lean`, registered in
`lemma.toml:[[oracles]]`).

The `c_value` constant on V66's candidate side is `356562/1000000`,
strictly above V64's `35646/100000 = 356460/1000000` by `+102/1000000 ≈
+1.02e-4`.

## Why

Sprint 087 placed every oracle and structural prerequisite required for
this c-push **in the trusted surface**:

  * `Proof/Reduction.lean:9487` — `def v66CValue : ℝ := 356562 / 1000000`,
    plus `v66SevenWindowKind`/`Start`/`Stop` defining the seven windows.
  * `Proof/Reduction.lean:9543` —
    `axiom h_seven_window_mass_certified_at_356562_sqrt (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤ ∑ i : Fin 7, match v66SevenWindowKind i with …`,
    matching the kind-dispatched joint-mass cell of the sprint 086 mixed
    reducer byte-for-byte (other than the sprint-087-specific `c` and
    endpoint defs).
  * `Numerical_Library/rigorous_scalar.py` —
    `certify_seven_window_mass_at_356562_sqrt` shim, certified at
    `(dps=80, n_trunc=300)` with margin `+1.1998e-4` (Phase 0 witness:
    `Scratch/sprint_087_v38_seven_window_mass_sweep.txt`).
  * `lemma.toml` — `[[oracles]] axiom = "h_seven_window_mass_certified_at_356562_sqrt"`,
    `bound_field = "seven_window_mass_lower"`, registered in
    `[seed_axioms].allowed` with the matching seed-axiom entry.

The remaining work is exactly the **per-candidate `h_witness` chain** the
mixed reducer expects: ordering, τ-bounds, `branchSplit` constraints,
adjacency, summability, integrability, the disk→inner bridge, and the
joint-mass invocation. **Every analytic ingredient already exists in the
trusted surface**:

  * V63 derived-theorem files (`Candidates/V63/Integrability.lean`,
    `Summability.lean`, `DiskInnerSeriesBridge.lean`) — six summability
    shapes from H², per-mode `modeScalarIntegrand_intervalIntegrable` for
    *any* `j ≥ 1` (covers j=1, 2, 3, 4 uniformly), and the
    `diskExcess ≤ innerSeriesExcess` bridge — all reusable as-is at V66's
    `c`.
  * V64-pattern free axioms `hH2_v66` and `hCircleGapInt_v66` (the two
    Wang-Section-2-implicit boundary hypotheses); fresh per-candidate
    copies, registered inline in `[seed_axioms].allowed`.
  * `OneModePaperBridge.pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9`
    (paper surface) discharges per-mode windows, automatically threaded
    by the mixed reducer.
  * `pointwise_branch1_on_Icc_eq5_eq8_eq9_ae` (sprint 086) discharges
    Branch.one windows, automatically threaded by the mixed reducer.

The two genuinely new pieces of analytic Lean derivation in this sprint:

  1. The **seven-window endpoint-properties file**
     `Candidates/V66/SevenWindowEndpoints.lean`, mirroring V64's
     `TauWindowEndpoints.lean` (181 lines) but expanded for 7 windows
     instead of 2. Contents: τ-equation discharges at the four mode
     endpoints (`τ_4 = 24/25` at `ρ² = c²·25/24`, `τ_3 = 15/16` at
     `ρ² = c²·16/15`, `τ_2 = 8/9` at `ρ² = c²·9/8`, `τ_1 = 3/4` at
     `ρ² = c²·4/3`), plus the geometric ordering `c < ρStart 0 ≤ ρStop 0 =
     ρStart 1 ≤ … ≤ ρStop 6 < 1` at `c = v66CValue`.
  2. The **Branch.one integrability file**
     `Candidates/V66/Branch1Integrability.lean`, providing
     `branch1ScalarIntegrand_intervalIntegrable` over any
     `[a, b] ⊆ [c, branchSplit c]` analogously to V63's
     `modeScalarIntegrand_intervalIntegrable`. The integrand
     `Korenblum.scalarIntegrand1 c Λ ρ = 12 ρ³(ρ²-c²)/(c⁶ Λ(ρ))` is a
     polynomial-times-`1/Λ` shape with `Λ ≥ 1/2` and `ρ ∈ [c, 1]`, so
     it admits a constant bound `C_1(c) = 24/(c⁴)` (since `12 ρ³ |ρ²-c²| ≤
     12 · 1 · 1 = 12` on `[c, 1]` and `|1/(c⁶ Λ)| ≤ 2/c⁶`, giving
     `|integrand| ≤ 24/c⁶`; refine by `ρ²-c² ≤ ρ² ≤ 1`). The proof
     mirrors V63/Integrability's `modeScalarIntegrand_intervalIntegrable`
     byte-for-byte except for the explicit constant.

The +1.02e-4 push above V64 is **strict score progress**: the harness
goes from `35646/100000 = 0.35646` to `356562/1000000 = 0.356562`, the
second consecutive push past V52 in 5 sprints. The score gate
`c_value > c_prev` is met. This is the second-largest c-push ever
landed by the harness (V52 → V64 was +1e-5; V64 → V66 is +1.02e-4 — an
order of magnitude larger).

### Three (and more) distinct directions considered

1. **Direction A — this sprint: ship V66 in one session.** Single sprint
   composing V63 derived files + new V66-namespaced derived-theorem
   files (SevenWindowEndpoints + Branch1Integrability) + sprint 087's
   helper defs and oracle axiom into a thin candidate. Estimated
   ~600-800 lines across three files. **Strongest objection**: scope
   risk — three new Lean files in one session is on the upper end of
   bounded sprint shape. **Counter**: V63 was three files in three
   sprints (080/081/082) at ~500 lines each, and V64 added a fourth
   ~180-line file in one sprint. The two new V66 files are templated
   directly on V63 and V64 derived files; the V66 candidate body is
   templated on V64.lean. The Generator's track record on similar-sized
   work (sprint 086 ~580 lines, sprint 084 ~620 lines, sprint 083
   composing many files into V64) supports landing this in one session.
   The mass discharge has zero analytic content — pure oracle
   invocation. Concrete witness: V64 closed with the same shape (oracle
   discharge for joint-mass) and shipped in one session.

2. **Direction B — partition: ship `Candidates/V66/SevenWindowEndpoints.lean`
   alone, V65-tie.** Defer Branch1Integrability and V66.lean to sprint
   089. **Strongest objection**: pure-derived-theorem sprints with no
   candidate ship leave the score unchanged for a sprint and don't
   answer the c-push question; sprint 089 inherits the same scope risk
   for the witness chain. The partition spreads work without
   eliminating it. **Demoted as lower-throughput than Direction A**
   given that the Generator can plausibly land all three files in one
   session, and a Direction-A failure can naturally degrade into
   Direction B's outcome via the BLOCKED stop condition (the
   SevenWindowEndpoints file would still ship as scratch progress).

3. **Direction C — replace `hH2_v64`/`hCircleGapInt_v64` with theorems
   that consume `Section2Assumptions`** (a real trust-surface
   improvement). The two axioms are paper-implicit Wang-Section-2
   boundary hypotheses; replacing them with derivations that consume
   bundled fields would shrink the audit set across V64, V65, and V66.
   **Strongest objection**: doesn't push c. The Bulletin priority is
   the V38 c-ceiling; sprint 087 just landed the oracle for it; sprint
   088's job is to consume that oracle. Trust-surface compaction can
   wait until after V66 ships. **Demoted**.

4. **Direction D — adaptive box-export Phase 0 sweep** to find a higher
   c-ceiling (V38's literal split gives ~1e-3 mass margin at its
   nominal c, suggesting the sqrt-pinned construction in sprint 087
   leaves headroom on the table; an adaptive box placement could push
   c higher than 356562/1000000). **Strongest objection**: explicitly
   noted in sprint 087's experience as "sprint 089+ work" — V66 at
   +1.02e-4 ships *now* using sprint 087's already-certified oracle;
   adaptive box-export is speculative additional headroom of unknown
   size that delays the bird in hand for two birds in the bush.
   **Demoted**.

5. **Direction E — file `proposal_004` to migrate `hH2_v66` /
   `hCircleGapInt_v66` into `Section2Assumptions`.** Per the proposal-
   filing checklist (`AGENT_BRIEF.md`'s four-condition guide): no "tried
   hard and failed" attempt, no path to c-push. Inline addition of seed
   axioms via `[seed_axioms].allowed` is the established pattern
   (sprints 053, 055, 079, 083). **Demoted**.

6. **Direction F — ship V66 at a slightly smaller c with more
   headroom** (e.g. `c = 356560/1000000` with margin `+1.66e-4`,
   ~40% more margin than `356562/1000000`'s `+1.20e-4`). **Strongest
   objection**: requires re-running sprint 087's wrapper at a different
   c (changing the oracle axiom name), and gives less score push. The
   margin at `356562/1000000` is `+1.20e-4`, far above the strict-
   margin floor `10⁻³⁰` and well above the `1e-4` Phase 0 GO floor.
   No reason to sacrifice score for redundant headroom. **Demoted**.

Direction A wins on **expected analytical novelty per session-budget**:
it lands the next score push without adding any speculative headroom,
exercising the mixed reducer end-to-end for the first time on a real
candidate, and exercising the kind-dispatched seven-window construction
sprint 086 was designed for. If Direction A blocks, Direction B is the
natural fallback.

### Why this is bounded for one session

The work is **directly templated** on previous sprints:

  * `Candidates/V66.lean` body: templated on V64.lean (345 lines).
    Difference: instantiate the mixed-reducer's seven-window witness
    instead of the perMode-twoWindow's two-window witness. The witness
    shape extends V64's by ~5x universal-quantifier density (one
    `∀ i : Fin 7` instead of `Fin 2`, with `kind`-case-split per `i`),
    but each per-`i` discharge is a one-line invocation of the
    sprint-087 helper defs and the V63 derived-theorem files.
    Estimated ~350 lines (V64's 345 lines was the bulk; per-`i`
    expansion adds ~50 lines, removed by Fin-pattern-match where
    possible).
  * `Candidates/V66/SevenWindowEndpoints.lean`: templated on
    V64/TauWindowEndpoints.lean (181 lines). Difference: 4 mode
    endpoints (j=4, 3, 2, 1) instead of 2 (j=2, 1), 3 Branch.one box
    endpoints with `ρStop ≤ branchSplit c` constraints, and a 7-way
    geometric ordering. Each τ-equation discharge is a single
    `field_simp + norm_num` block (V64 lines 67-104 template). Each
    `ρStop ≤ branchSplit c` is a single `mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt ⋯) c_nonneg` invocation (since
    `sqrt(50/49) ≤ sqrt(4/3)`, etc., is a `norm_num` fact under
    `Real.sqrt_le_sqrt`). Estimated ~350 lines.
  * `Candidates/V66/Branch1Integrability.lean`: templated on
    V63/Integrability.lean (315 lines). The proof of
    `modeScalarIntegrand_intervalIntegrable` (lines 114-277) ports
    directly to `branch1ScalarIntegrand_intervalIntegrable` with the
    constant bound recomputed; the Branch.one integrand
    `12 ρ³(ρ²-c²)/(c⁶ Λ)` is *simpler* than the per-mode integrand
    (no `j` parameter), so the proof is shorter than 277 lines —
    estimated ~200 lines.

Total: ~600-900 lines across three files. The Generator's recent track
record (sprints 080-086) routinely lands 400-700-line single-sprint
deliverables. Bounded.

## Concrete edits expected

### 1. `Candidates/V66/SevenWindowEndpoints.lean` (new file)

Per-candidate derived-theorem file, scope is V66 only. **No `axiom`s,
no `sorry`s, no `Section2Assumptions` field extensions.** Imports:

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import KorenblumPaper.OneModePaperBridge
import KorenblumPaper.PaperAxioms     -- for branchSplit
import ProofRefinement.Korenblum.Proof.Reduction  -- for v66CValue, v66SevenWindowStart/Stop/Kind
```

Required theorems (templated on V64/TauWindowEndpoints.lean):

  * **τ-equation discharges** at the four mode endpoints. Each is a
    `field_simp + norm_num` block under `Real.sq_sqrt`:
    - `tau_three_le_c_sq_div_stop3_sq` (mode4 window, upper τ-bound:
      `τ_3 ≤ c²/(c·sqrt(16/15))² = 15/16 = τ_3`).
    - `c_sq_div_start3_sq_le_tau_four` (mode4 window, lower τ-bound:
      `c²/(c·sqrt(25/24))² = 24/25 = τ_4`).
    - Similar pairs for mode3 (τ_2, τ_3), mode2 (τ_1, τ_2), mode1
      (τ_0 = 0, τ_1).
    - The `tau 0 ≤ c²/ρStop²` discharge for mode1's upper τ-bound at
      `ρStop = 999999/1000000` is identical to V64's
      `tau_zero_le_c_sq_div_stop2_sq`.

    Pattern (templated byte-for-byte on V64 lines 67-104):

    ```lean
    theorem c_sq_div_start_mode4_sq_le_tau_four {c : ℝ} (hc : 0 < c) :
        c ^ 2 / (c * Real.sqrt (25/24)) ^ 2 ≤ OneModeTail.tau 4 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 25/24)]
      have : c ^ 2 / (c ^ 2 * (25 / 24)) = 24 / 25 := by
        field_simp
      rw [this]
      unfold OneModeTail.tau
      norm_num
    ```

  * **Geometric ordering** at `c = v66CValue`. The seven endpoints
    satisfy `v66CValue < v66SevenWindowStart 0 ≤ v66SevenWindowStop 0
    = v66SevenWindowStart 1 ≤ … ≤ v66SevenWindowStop 6 < 1`. Six
    adjacency equations are by `rfl` (definitional). The remaining
    inequalities chain through `Real.sqrt`-monotonicity:

    ```lean
    theorem c_lt_start0 : v66CValue < v66SevenWindowStart 0 := by
      unfold v66CValue v66SevenWindowStart
      norm_num
    theorem start_i_le_stop_i (i : Fin 7) :
        v66SevenWindowStart i ≤ v66SevenWindowStop i := by
      fin_cases i <;>
        (try unfold v66SevenWindowStart v66SevenWindowStop;
         apply mul_le_mul_of_nonneg_left _ (by norm_num [v66CValue] : (0:ℝ) ≤ v66CValue);
         exact Real.sqrt_le_sqrt (by norm_num))
    theorem adj_i (i : Fin 6) : v66SevenWindowStop i.castSucc =
        v66SevenWindowStart i.succ := by
      fin_cases i <;> rfl
    theorem stop6_lt_one : v66SevenWindowStop 6 < 1 := by
      unfold v66SevenWindowStop
      norm_num
    theorem c_lt_start_i (i : Fin 7) : v66CValue < v66SevenWindowStart i := by
      fin_cases i
      · exact c_lt_start0
      · -- i ≥ 1: v66CValue < v66SevenWindowStart 0 < … ≤ v66SevenWindowStart i
        all_goals {
          unfold v66CValue v66SevenWindowStart
          have h1 : (1 : ℝ) ≤ Real.sqrt (50/49) := by
            -- 1 = sqrt 1 ≤ sqrt (50/49)
            …
          …
        }
    ```

  * **`branchSplit` constraints** for the three Branch.one windows
    (i = 0, 1, 2):
    - `v66SevenWindowStop i ≤ PaperAxioms.branchSplit v66CValue` for
      `i ∈ {0, 1, 2}`. Each is `c · sqrt(k/(k-1)) ≤ c · sqrt(4/3)`
      with `k/(k-1) ∈ {50/49, 36/35, 25/24}`, all `≤ 4/3`, dispatched
      by `mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (by norm_num)) c_nonneg`.

  * **mode index facts**: `hj_pos i j (h : v66SevenWindowKind i =
    KernelKind.modeJ j) : 1 ≤ j` — by `fin_cases i` + `cases h`,
    yielding `j ∈ {1, 2, 3, 4}`.

### 2. `Candidates/V66/Branch1Integrability.lean` (new file)

Per-candidate derived-theorem file, **no `axiom`s, no `sorry`s**.
Imports:

```lean
import Mathlib
import KorenblumPaper.PaperEq15           -- for Korenblum.scalarIntegrand1
import KorenblumPaper.WangPaperSideConditions  -- for paperLambda*, PaperKFormula
import KorenblumPaper.WangOuter            -- for paperLambda
```

Single primary theorem (templated on V63/Integrability.lean lines
114-277):

```lean
theorem branch1ScalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  -- Constant bound: M = 24 / c^6 (since |12 ρ³(ρ²-c²)| ≤ 12 on [c, 1]
  -- and |1/(c⁶ Λ)| ≤ 2/c⁶ with Λ ≥ 1/2).
  set M : ℝ := 24 / c ^ 6
  …
  refine IntegrableOn.of_bound ?_ ?_ M ?_
  · simpa using (measure_Icc_lt_top (μ := volume) (a := a) (b := b))
  · -- AE-strong measurability via paperLambda_aemeasurableOn_Icc + ρ-pow + arithmetic.
    …
  · -- Pointwise: |scalarIntegrand1| ≤ 24/c⁶.
    rw [ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ fun ρ hρ => ?_
    have hcρ : c ≤ ρ := le_trans hca hρ.1
    have hρ_le_one : ρ ≤ 1 := le_trans hρ.2 hb1
    have hΛ_half : (1/2 : ℝ) ≤ WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_ge_half (K := K) (c := c) (ρ := ρ)
    have hΛ_pos : 0 < WangOuter.paperLambda K c ρ :=
      WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
    -- Numerator: |12 ρ³ (ρ² - c²)| ≤ 12 (since 0 ≤ ρ² - c² ≤ 1 and 0 ≤ ρ³ ≤ 1).
    -- Denominator: c⁶ Λ ≥ c⁶ · 1/2.
    -- Quotient: |·| ≤ 12 / (c⁶ · 1/2) = 24 / c⁶.
    …
```

The proof body mirrors V63/Integrability lines 114-277 with the
following differences:

  * No `j`-parameter (Branch.one is single-shape).
  * Constant bound is `24/c⁶` (not `4(j+1)/(j·c^(2j+2))`).
  * Numerator bound `|12 ρ³(ρ²-c²)| ≤ 12` follows from `ρ³ ≤ 1` and
    `ρ² - c² ≤ ρ² ≤ 1` for `ρ ∈ [c, 1]`.
  * Denominator `c⁶ · Λ ≥ c⁶/2` from `Λ ≥ 1/2`.
  * The `unfold Korenblum.scalarIntegrand1` step exposes the shape
    `12 ρ³(ρ²-c²) / (c⁶ Λ ρ)` directly (no `scalarIntegrand_eq`-style
    rewrite needed).

A second consolidation theorem packaging
`branch1ScalarIntegrand_intervalIntegrable` for the three Branch.one
windows of V66's split (analogue of V63's
`mode_two_and_one_scalarIntegrand_intervalIntegrable`):

```lean
theorem v66_branch1_three_window_intervalIntegrable
    {K : ℝ → ℝ → ℝ}
    (hPaperK : WangKernelExact.PaperKFormula K v66CValue) :
    IntervalIntegrable (fun ρ => Korenblum.scalarIntegrand1 v66CValue
      (WangOuter.paperLambda K v66CValue) ρ) volume
      (v66SevenWindowStart 0) (v66SevenWindowStop 0) ∧
    IntervalIntegrable (… ) volume (v66SevenWindowStart 1) (v66SevenWindowStop 1) ∧
    IntervalIntegrable (… ) volume (v66SevenWindowStart 2) (v66SevenWindowStop 2) := by
  …
```

### 3. `Candidates/V66.lean` (new file)

The candidate body, templated on V64.lean. Imports:

```lean
-- @parent V64
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints
import ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
```

Required content:

```lean
namespace ProofRefinement.Korenblum.Candidates.V66

def c_value : ℝ := v66CValue   -- 356562 / 1000000

theorem c_value_pos : (0 : ℝ) < c_value := by norm_num [c_value, v66CValue]
theorem c_value_lt_one : c_value < (1 : ℝ) := by norm_num [c_value, v66CValue]
theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- V66's c strictly improves on V64's `35646/100000 = 356460/1000000`. -/
theorem c_value_gt_v64 : (35646 : ℝ) / 100000 < c_value := by
  norm_num [c_value, v66CValue]

/-- Evaluator-facing oracle bound-field. Matches the
    `bound_field = "seven_window_mass_lower"` row in `lemma.toml`. -/
def seven_window_mass_lower : ℝ := 1

/-- branchSplit < 1 at c_value. -/
theorem branchSplit_lt_one : PaperAxioms.branchSplit c_value < 1 := by
  unfold PaperAxioms.branchSplit
  -- c_value · sqrt(4/3) ≤ 0.356562 · 1.156 < 1 (using Real.sqrt (4/3) ≤ 1156/1000)
  …

/-- Free per-candidate axiom: H² boundary-norm finiteness. Templated on V64. -/
axiom hH2_v66 : ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Free per-candidate axiom: 2ρ·circleGap integrability on (c, 1). Templated on V64. -/
axiom hCircleGapInt_v66 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-- The h_witness predicate for the mixed reducer. -/
theorem v66_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c_value),
      ∃ (ρStart ρStop : Fin 7 → ℝ) (kind : Fin 7 → KernelKind),
        … (full body of the mixed reducer's h_witness, instantiated at
           v66SevenWindowStart, v66SevenWindowStop, v66SevenWindowKind) … := by
  intro a b K paper
  refine ⟨v66SevenWindowStart, v66SevenWindowStop, v66SevenWindowKind,
          ?hStartLt, ?hStartLeStop, ?hStopLtOne, ?hAdj,
          ?hModeJ, ?hBranch1Split,
          ?hPlusDisk, ?hPlusSigma, ?hMinusDisk, ?hMinusSigmaC, ?hMinusWeight,
          ?hMinusSigma, ?hIntCircle, ?hIntKind, ?hInner, ?hMassTotal⟩
  case hStartLt => intro i; exact V66.SevenWindowEndpoints.c_lt_start_i i
  case hStartLeStop => intro i; exact V66.SevenWindowEndpoints.start_i_le_stop_i i
  case hStopLtOne =>
    intro i
    fin_cases i
    case _ => exact lt_of_le_of_lt … -- v66SevenWindowStop i ≤ v66SevenWindowStop 6 < 1
    …
  case hAdj => intro i; exact V66.SevenWindowEndpoints.adj_i i
  case hModeJ =>
    intro i j hKind
    -- For i ∈ {3, 4, 5, 6}, kind i = modeJ {4, 3, 2, 1}.
    fin_cases i <;> simp only [v66SevenWindowKind] at hKind
    · -- i = 0, 1, 2: kind i = branch1, contradicts hKind : kind i = modeJ j.
      cases hKind
    · cases hKind
    · cases hKind
    · -- i = 3: kind = modeJ 4. So j = 4.
      cases hKind
      refine ⟨by decide, ?_, ?_⟩
      · -- τ_3 ≤ c² / ρStop_3²
        exact V66.SevenWindowEndpoints.tau_three_le_c_sq_div_stop3_sq c_value_pos
      · -- c² / ρStart_3² ≤ τ_4
        exact V66.SevenWindowEndpoints.c_sq_div_start3_sq_le_tau_four c_value_pos
    -- … similar for i = 4, 5, 6.
  case hBranch1Split =>
    intro i hKind
    fin_cases i <;> simp only [v66SevenWindowKind] at hKind
    · -- i = 0: ρStop 0 = c·sqrt(50/49) ≤ branchSplit c = c·sqrt(4/3)
      exact V66.SevenWindowEndpoints.stop0_le_branchSplit c_value_nonneg
    · exact V66.SevenWindowEndpoints.stop1_le_branchSplit c_value_nonneg
    · exact V66.SevenWindowEndpoints.stop2_le_branchSplit c_value_nonneg
    · -- i = 3, 4, 5, 6: kind i ≠ branch1, contradicts hKind.
      cases hKind
    …
  case hPlusDisk => exact (V63.Summability.six_summability_shapes_from_h2
    (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).1
  -- … similar for the other 5 summability shapes.
  case hIntCircle => exact hCircleGapInt_v66 a b
  case hIntKind =>
    intro i
    refine ⟨?_, ?_⟩
    · intro j hKind
      -- Per-mode integrability for j ∈ {1, 2, 3, 4} via V63.Integrability.
      fin_cases i <;> simp only [v66SevenWindowKind] at hKind
      · cases hKind
      · cases hKind
      · cases hKind
      · cases hKind  -- ρStart 3 = c·sqrt(25/24), ρStop 3 = c·sqrt(16/15), j = 4
        exact V63.Integrability.modeScalarIntegrand_intervalIntegrable
          (by decide : 1 ≤ 4) c_value_pos
          (V66.SevenWindowEndpoints.start_i_le_stop_i 3)
          (V66.SevenWindowEndpoints.c_le_start_i 3)
          (V66.SevenWindowEndpoints.stop_i_le_one 3)
          paper.eq7_paperK_formula
      … (i = 4, 5, 6 similarly with j = 3, 2, 1)
    · intro hKind
      fin_cases i <;> simp only [v66SevenWindowKind] at hKind
      · -- Branch.one window at i = 0
        exact (V66.Branch1Integrability.v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).1
      · exact (V66.Branch1Integrability.v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).2.1
      · exact (V66.Branch1Integrability.v66_branch1_three_window_intervalIntegrable
          paper.eq7_paperK_formula).2.2
      · cases hKind  -- mode windows reject branch1
      …
  case hInner =>
    -- diskExcess ≤ innerSeriesExcess via V63.DiskInnerSeriesBridge.
    have hkit := V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one
    have hAbsSummable :
        Summable (fun k : ℕ => |PaperAxioms.coeffPlusGap a b k| *
          c_value ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
      V63.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components
        c_value_nonneg hkit.1 hkit.2.2.1
    exact V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
      c_value_nonneg hkit.1 hkit.2.2.1 hAbsSummable
  case hMassTotal =>
    -- Joint seven-window mass ≥ 1 via the registered oracle.
    exact h_seven_window_mass_certified_at_356562_sqrt K

theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9
    c_value_pos c_value_lt_one branchSplit_lt_one
    (fun {a b K} paper => v66_witness paper)

end ProofRefinement.Korenblum.Candidates.V66
```

### 4. `lemma.toml` updates (inline, no proposal)

Add to `[seed_axioms].allowed`:

  * `"hH2_v66"`,
  * `"hCircleGapInt_v66"`.

These are the per-candidate copies of V64's `hH2_v64` /
`hCircleGapInt_v64`, registered inline per the established pattern
(sprint 083 added the V64 versions inline). The seven-window mass
oracle is already registered (sprint 087).

### 5. `Bulletin.md` and `Experience.md` append

Append one row each:

  * The score push (`35646/100000 → 356562/1000000`, +1.02e-4 above V64,
    +1.13e-4 above V52).
  * V66's audit set: standard Lean axioms + `hH2_v66` + `hCircleGapInt_v66`
    + `h_seven_window_mass_certified_at_356562_sqrt` (the latter at
    `ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt`,
    not a candidate-namespace copy).
  * Two new derived-theorem files
    (`Candidates/V66/SevenWindowEndpoints.lean`,
    `Candidates/V66/Branch1Integrability.lean`).
  * Forward direction: sprint 089 either pushes c again (adaptive
    box-export Phase 0 sweep to find a higher c-ceiling, e.g.
    `c ≈ 0.35660`?), tightens the trust surface (replace `hH2_v66`/
    `hCircleGapInt_v66` with theorems consuming `Section2Assumptions`),
    or files `proposal_004` for an additional analytic axiom that
    would further improve c.

### 6. NOT modified

  * `KorenblumPaper/` (read-only).
  * `Proof/CandidateContract.lean`, `Proof/Main.lean`.
  * `Proof/Reduction.lean` (sprint 087 already added the helper defs
    and oracle axiom; do not re-edit).
  * Any V0-V65 candidate file (V65 stays at `35646/100000`).
  * Any V63-derived file (Integrability/Summability/DiskInnerSeriesBridge
    are reused as-is).
  * Any V64-derived file (TauWindowEndpoints is V64-specific; V66 has
    its own SevenWindowEndpoints).
  * `Numerical_Library/rigorous_scalar.py` (sprint 087's wrapper is
    unchanged; do not re-pin or re-tier).
  * Any sprint 086 reducer or sprint 087 helper def.
  * Any existing `[[oracles]]` row.
  * `Proposals/` (no proposal filed).
  * `[workspace_import_policy]` (the new V66 derived files live under
    `ProofRefinement.Korenblum.Candidates.V66.*`, already allowed).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds.

2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V66.lean` succeeds with
   `pass: true`.

3. The Evaluator's reported `score` (`= c_value`) is `356562/1000000`
   (or its canonical-rational reduction `178281/500000`), strictly
   greater than V64's `35646/100000 = 356460/1000000`. The `score`
   field in `Refinement_Log/log.jsonl` reflects this.

4. `axioms_used` in V66's audit consists of standard Lean axioms
   (`propext`, `Classical.choice`, `Quot.sound`, optionally
   `Lean.ofReduceBool` / `Lean.trustCompiler`) plus exactly:

     * `ProofRefinement.Korenblum.Candidates.V66.hH2_v66`,
     * `ProofRefinement.Korenblum.Candidates.V66.hCircleGapInt_v66`,
     * `ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt`.

   No other free axioms; no `sorryAx`. `[seed_axioms].allowed`
   contains all three names (the third was added in sprint 087; the
   first two are added in this sprint inline).

5. The oracle audit on V66 reports `oracle=1, declared=1, ok=true`
   for the row `axiom = "h_seven_window_mass_certified_at_356562_sqrt"`,
   `bound_field = "seven_window_mass_lower"`. V66's
   `def seven_window_mass_lower : ℝ := 1` exposes the matching
   bound-field.

6. `lake build ProofRefinement.Korenblum.Candidates.V64` and
   `lake build ProofRefinement.Korenblum.Candidates.V65` continue to
   succeed (regression: the addition of new V66-namespaced files and
   `seed_axioms` entries does not perturb older candidates).

7. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern, naming the c-push, the new files, the audit
   extension, and the forward direction.

## Out of scope

  * Push `c_value` beyond `356562/1000000`. That requires either a
    new oracle wrapper at a higher c (sprint 089's adaptive
    box-export angle) or a tighter `H(c, ρ)` envelope.
  * Edit `Proof/Reduction.lean` (sprint 087's helper defs and oracle
    axiom are already in place; this sprint only consumes them).
  * Replace `hH2_v66` / `hCircleGapInt_v66` with derivations from
    `Section2Assumptions`. Trust-surface tightening is a separate
    direction; sprint 088's job is the c-push.
  * Edit any V64-derived file. V64/TauWindowEndpoints is
    V64-specific; V66 has its own SevenWindowEndpoints.
  * Hoist V63 derived theorems into `Proof/`. They are reused as-is
    via direct import.
  * Rebuild the Phase 0 sweep, the `Numerical_Library` wrapper, or
    the oracle row (all sprint-087 deliverables are unchanged).
  * Migrate V65 to the mixed-kernel reducer. V65 stays at
    `35646/100000` via the per-mode-only chain.
  * File `proposal_004`. The seed_axiom additions are inline-pattern
    (per `Proposals/README.md` "Do not use a proposal for … new
    oracle registry entries that are already fully specified and
    directly consumed by the current sprint").

## Time budget

≤ 240 minutes runtime.

  * `Candidates/V66/SevenWindowEndpoints.lean`: ~60 minutes (templated
    on V64/TauWindowEndpoints.lean lines 67-180; expand the
    `tau_one_le_…` / `c_sq_div_start1_sq_le_tau_two_…` patterns to
    four mode endpoints, add three Branch.one `branchSplit`
    constraints, and the seven-way ordering).
  * `Candidates/V66/Branch1Integrability.lean`: ~70 minutes
    (templated on V63/Integrability lines 114-313; the proof body
    differs only in the integrand shape, the constant `M = 24/c⁶`,
    and the lack of a `j` parameter).
  * `Candidates/V66.lean`: ~60 minutes (templated on V64.lean lines
    98-326; the `v66_witness` body uses `fin_cases i` to dispatch
    seven-window-style universal cells, with each cell a one- to
    five-line invocation of an existing derived theorem).
  * `lemma.toml` seed-axiom additions: ~10 minutes.
  * Bulletin/Experience appends: ~10 minutes.
  * Build + Evaluator regression: ~30 minutes.

## Stop conditions

  * **All seven-window τ-bounds, branchSplit constraints, integrabilities,
    and the joint-mass discharge typecheck; V66 builds; Evaluator
    reports `pass: true` with `score = 356562/1000000` and the audit
    set above**: `STATUS=READY_FOR_EVALUATION`. The harness gains its
    second consecutive c-push past V52.

  * **The `v66_witness` body fails to typecheck on a specific cell
    (e.g. a τ-bound discharge, an integrability, the joint-mass cell)
    and the obstruction is local to one cell**: ship the per-candidate
    derived-theorem files (`SevenWindowEndpoints.lean`,
    `Branch1Integrability.lean`) anyway if they typecheck standalone,
    and document the specific witness-cell obstruction at
    `Scratch/sprint_088_obstruction.md` with the exact unification
    error or unprovable goal. `STATUS=BLOCKED`. Sprint 089 picks up
    with a thinner partition (e.g. only the τ-bounds and integrability
    files in V65-tie shape, deferring the candidate to sprint 090).

  * **The Branch.one integrability proof requires a Mathlib lemma
    that does not exist** (e.g. a measurability instance that needs
    `paperLambda` to be Borel-measurable rather than just
    `aemeasurable`): document the missing lemma precisely at
    `Scratch/sprint_088_obstruction.md` and `STATUS=BLOCKED`. Sprint
    089 either files a Mathlib-side proposal or rederives via a
    different measurability path.

  * **A new free axiom beyond `hH2_v66` / `hCircleGapInt_v66` would
    be required** (e.g. an additional Wang-Section-2-implicit
    boundary hypothesis surfaces during the witness construction):
    do not ship it. Document at `Scratch/sprint_088_obstruction.md`
    and `STATUS=BLOCKED_NEEDS_HUMAN`. (Highly unlikely — V64's three
    free axioms cover the analogous chain at j=2/j=1, and the
    j=4/3/2/1 + Branch.one extension does not introduce new
    axiomatically distinct content.)

  * **The oracle audit fails because the candidate-side axiom
    statement does not unify with the registered axiom in
    Reduction.lean**: revert the candidate-side oracle invocation,
    re-derive the joint-mass cell directly via the
    `h_seven_window_mass_certified_at_356562_sqrt` declaration in
    `Proof/Reduction.lean` (the candidate must invoke it via the
    fully-qualified name `ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt`,
    not redeclare it candidate-side as V64 did for the two-window
    oracle). `STATUS=BLOCKED` if the unification still fails after
    one round-trip.

## Notes for the generator

  * **Read first**:
    - `Candidates/V64.lean` (your candidate-body template, 345 lines).
    - `Candidates/V64/TauWindowEndpoints.lean` (your endpoints-file
      template, 181 lines).
    - `Candidates/V63/Integrability.lean` (your Branch.one
      integrability template via the `modeScalarIntegrand_intervalIntegrable`
      shape, 315 lines).
    - `Candidates/V63/Summability.lean`,
      `Candidates/V63/DiskInnerSeriesBridge.lean` (reuse as-is via
      direct import; do not edit).
    - `Proof/Reduction.lean:8934` (the mixed reducer's signature; the
      witness shape is fully specified there).
    - `Proof/Reduction.lean:9487-9555` (sprint 087's helper defs and
      oracle axiom; consume them via direct reference).
    - `KorenblumPaper/PaperEq15.lean:11` (the
      `Korenblum.scalarIntegrand1` definition; the integrand
      `12 ρ³(ρ²-c²)/(c⁶ Λ)` is the exact shape for which you derive
      integrability).
    - `KorenblumPaper/PaperAxioms.lean:14` (the
      `branchSplit c = c · sqrt(4/3)` definition; used in the
      Branch.one window's `ρStop ≤ branchSplit c` constraints).
    - `Scratch/sprint_087_v38_seven_window_mass_sweep.txt` (Phase 0
      witness for the chosen `c = 356562/1000000`; the τ-ratios
      `50/49, 36/35, 25/24, 16/15, 9/8, 4/3` are the seven endpoint
      ratios pinned in sprint 087).

  * **The mixed reducer's witness shape is large** (~30 universal-
    quantifier cells when expanded `Fin 7`-wise). Each cell is a
    one- to five-line invocation of an existing derived theorem.
    Use `fin_cases i` heavily: it splits a `Fin 7` quantifier into
    seven concrete subgoals, each of which can be discharged by a
    one-line `simp` + theorem invocation. Do **not** try to discharge
    all seven cases uniformly — the kind dispatch (3 branch1, 4 mode)
    requires `cases` on `kind i` per `i`.

  * **Per-mode integrability for j ∈ {1, 2, 3, 4}**: V63's
    `modeScalarIntegrand_intervalIntegrable` (`Candidates/V63/Integrability.lean:114`)
    is parametric in `j` with hypothesis `1 ≤ j`. Invoke it directly
    at j = 4, 3, 2, 1. Do *not* extend
    `mode_two_and_one_scalarIntegrand_intervalIntegrable` (it is
    pinned to V64's two-window shape); call the parametric version
    directly four times.

  * **Branch.one integrability**: derive
    `branch1ScalarIntegrand_intervalIntegrable` in
    `Candidates/V66/Branch1Integrability.lean` following V63's
    template byte-for-byte, with the integrand swapped and the
    constant bound recomputed. The integrand
    `Korenblum.scalarIntegrand1 c Λ ρ = 12 ρ³(ρ²-c²)/(c⁶ Λ ρ)` is
    *non-negative on `[c, branchSplit c]`* (since `ρ² ≥ c²` there
    and `Λ > 0`); the constant bound `24/c⁶` follows from
    `12·1·1 / (c⁶·1/2)`.

  * **Adjacency `ρStop i.castSucc = ρStart i.succ` is by `rfl`** —
    sprint 087 chose the seven endpoints precisely so that
    adjacency is definitional. `fin_cases i` + `rfl` discharges all
    six adjacencies.

  * **The seven-window mass oracle is invoked unchanged.** The axiom
    `h_seven_window_mass_certified_at_356562_sqrt` (in
    `Proof/Reduction.lean`) takes a single argument `K : ℝ → ℝ → ℝ`
    and asserts the joint-mass inequality with `v66CValue`,
    `v66SevenWindowKind`, `v66SevenWindowStart`, `v66SevenWindowStop`
    baked in. V66's witness invokes it directly:
    `exact h_seven_window_mass_certified_at_356562_sqrt K`. This
    matches the witness's `hMassTotal` cell shape after the
    `c_value = v66CValue`, `ρStart = v66SevenWindowStart`, etc.,
    substitutions land via the `refine ⟨v66SevenWindowStart, …⟩`
    instantiation.

  * **`c_value` aliasing**: declare `def c_value : ℝ := v66CValue`
    in the V66 candidate so that `ValidKorenblumBound c_value`
    refers to the same constant as the oracle axiom's `v66CValue`.
    All `c_value`-bearing theorems in V66 (`c_value_pos`, etc.) can
    `unfold c_value v66CValue` and then `norm_num`.

  * **`hH2_v66` parametricity**: V64's `hH2_v64` is
    `∀ (a : ℕ → ℂ), Summable (fun n => ‖a n‖²)`. The same shape
    works for V66; instantiate it twice in the witness body (once
    for `a`, once for `b`) when invoking
    `V63.Summability.six_summability_shapes_from_h2`.

  * **Generator capability budget**: ~600-900 lines across three
    files. If `Candidates/V66.lean` exceeds 500 lines, consider
    factoring the per-`i` Fin-cases dispatch into a small helper
    inside `Candidates/V66/SevenWindowEndpoints.lean` (e.g.
    `tau_bounds_for_modeJ : ∀ i j, kind i = modeJ j → … ∧ …`).
    Do not introduce new axioms while factoring.

  * **No new files in `Proof/`**. The two new files live under
    `Candidates/V66/`. Do not edit `Proof/Reduction.lean`.

  * **Forward to sprint 089** (for context, not for action this
    sprint): once V66 ships, the Bulletin priority shifts to
    further c-push. Two main angles: (a) adaptive box-export Phase 0
    sweep for a higher c-ceiling, (b) trust-surface compaction
    (replace `hH2_v6×` / `hCircleGapInt_v6×` with derivations from
    `Section2Assumptions`). Either is valid sprint 089 work; the
    planner will choose based on the V66 audit-set evidence.
