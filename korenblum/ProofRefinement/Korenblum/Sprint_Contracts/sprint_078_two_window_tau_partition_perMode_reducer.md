# Sprint 078: Two-window τ-partition per-mode closing reducer + V61

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V60.lean` (high-water-tied; `c_value = 7129/20000 = 0.35645`)
**Target file**: `Candidates/V61.lean` plus new closing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` in
`Proof/Reduction.lean`.
**Direction**: section2-proof + scratch-numerical-witness (Phase 0
gates whether the candidate ships at a strict c-push or as a V60-tie
with the structural reducer advance).

## Goal

Build the **first multi-window per-mode τ-partition closing reducer**
in the workspace, restricted to **m = 2 windows** (j*=2 then j*=1, the
two outermost τ-windows that cover the high-`ρ` region of `(c, 1)`).
Concretely, ship in `Proof/Reduction.lean`:

```text
theorem valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : PaperAxioms.Section2Assumptions a b K c)
    (cPos : 0 < c)
    -- two concrete τ-windows on (c, 1):
    (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ)
    (hAdj : ρStop₁ = ρStart₂)
    (hOrd : c < ρStart₁ ∧ ρStart₁ < ρStop₁ ∧ ρStop₁ < ρStop₂ ∧ ρStop₂ ≤ 1)
    -- per-window mode indices (j₁ = 2, j₂ = 1, but the theorem accepts
    -- any (j₁, j₂) with appropriate τ-bounds):
    (j₁ j₂ : ℕ) (j₁_pos : 1 ≤ j₁) (j₂_pos : 1 ≤ j₂)
    -- τ-membership on each window (polynomial inequalities, no sqrt):
    (hτ₁_lo : (j₁ - 1).toReal * (j₁ + 1).toReal * ρStart₁^2 ≤ j₁.toReal * (j₁ + 2).toReal * c^2)
    (hτ₁_hi : j₁.toReal * (j₁ + 2).toReal * ρStop₁^2 ≥ (j₁ + 1).toReal^2 * c^2)
    (hτ₂_lo : ...analogous for window 2 with j₂...)
    (hτ₂_hi : ...analogous for window 2 with j₂...)
    -- per-window summability and integrability:
    (hSum₁ hInt₁ hSum₂ hInt₂ : ...)
    -- joint-mass-≥-1 hypothesis:
    (hMassTotal :
       1 ≤ ∫ ρ in ρStart₁..ρStop₁,
              ModeBridge.scalarIntegrand c j₁ (paperLambda K c) ρ
         + ∫ ρ in ρStart₂..ρStop₂,
              ModeBridge.scalarIntegrand c j₂ (paperLambda K c) ρ) :
    ValidKorenblumBound c
```

The proof body composes two invocations of sprint 071's
`valid_of_perMode_tau_window_eq8_eq9` (one per window) with
`AnnulusIntegralReduction.annulusSlice_add_adjacent` to glue the two
windows' annulus slices into `annulusSlice circleGap c 1`, then
applies `AnnulusIntegralReduction.innerExcess_le_of_window_bounds` (or
the equivalent two-window splitting machinery sprint 071 already
links into) to conclude `innerExcess ≤ annulusExcess`.

V61 ships **conditionally on Phase 0's outcome**:

- **If Phase 0 GO at some `c > 7129/20000`** with joint mass ≥ 1 with
  margin ≥ 1e-3: V61 ships at the witness's c, axioms_used target
  `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
  Lean.trustCompiler}` only — **first oracle-free, eq15-axiom-free
  certified bound in the workspace** — strict c-push above V52.

- **If Phase 0 NO-GO** (joint mass < 1 at every tested
  `c > 7129/20000`): V61 ties V60 at `c_value = 7129/20000` via
  `valid_of_eq15` discharged by `hEq15_oracle_certified_hp_35645`,
  same axiom envelope as V60. The sprint's structural advance is the
  new reducer in `Reduction.lean`, exercised by a side lemma in V61
  that re-states the reducer's signature against an arbitrary
  `Section2Assumptions` instance and discharges by direct invocation
  (non-vacuity check).

Either way, the new reducer is the load-bearing structural deliverable
and the Bulletin's "Sprint B" from the 2026-05-04 V38 directive update
becomes shipped Lean.

## Why

### The strategic gap

Sprint 071 shipped the **single-window** per-mode τ-partition reducer
`valid_of_perMode_tau_window_eq8_eq9`. The Bulletin's 2026-05-04 V38
directive lays out a deliberate three-sprint chain — Sprint A (single
window, sprint 071, shipped), Sprint B (two windows, this sprint),
Sprint C (seven windows at V38's `c = 356401/1000000`). Sprint B is
the natural next concrete step; the Bulletin explicitly states:

> Sprint B introduces the `annulusSlice_add_adjacent` chaining and the
> per-mode coefficient discharge, but only at `m = 2`. Run a Phase 0
> sweep at `c = 7129/20000 + ε` and confirm two-window mass crosses
> 1; if it does, ship V57 with a strict c-push. If not, V57 ties V52
> and Sprint C continues from there.

The harness has not yet built any multi-window reducer; sprint 072
attempted general-`m` `Fin m`-indexed partitions, hit a
`hcEqStart0 : c = start 0` rewrite-motive obstruction, and was rolled
back by sprint 074. The two-window concrete-endpoint shape **avoids
the `Fin m` motive issue entirely** by having the four endpoints
`ρStart₁, ρStop₁, ρStart₂, ρStop₂` as plain real parameters with a
single adjacency equality `ρStop₁ = ρStart₂` — no
indexed-family `start : Fin m → ℝ` motive to rewrite under.

### Why this is a structurally novel advance even on a NO-GO branch

Sprint 077 ran a Phase 0 mpmath sweep over the per-`k` α-varying
register and found a witness only outside the contraction regime
(`max_k |α(k)| = 1.01 > 1`). The sprint 077 Experience entry's
analytical refutation argues this witness is structurally vacuous —
the `(1 − α(k)²)` sign-flip at `α(k)² > 1` does not change the
underlying truth that the integrated lift identity at α = c falsifies
on E1. Sprint 077 explicitly recommended **Path B**: pivot to one of
Wang Lemma 2, multi-window τ-partition reducer (this sprint), or
HP-precision push. The HP-precision route is dead per sprint 060
(c=35646 → margin -2.19e-04). Wang Lemma 2 is a substantial
preparatory sprint (~500–1000 lines, no immediate c-push). The
multi-window τ-partition route is concrete, falsifiable in one
session, and ships a new reducer in `Reduction.lean` regardless of
Phase 0 outcome.

### Why Phase 0 must precede

The numerical question — **does the sum of two mass integrals cross 1
at any c > 7129/20000?** — is an mpmath check, not a Lean check. The
Bulletin's V38 directive cites Wang's strict bracket
`c=0.356401 → total seven-window mass = 1.000012381570; c=0.356402 →
0.999989183931`, which means the **seven-window** envelope is tight at
`c ≈ 0.3564015`, **below** V52's `0.35645`. The two-window envelope is
strictly weaker than the seven-window envelope (it discards five
contributing windows), so the two-window mass at any c ≥ 0.35645 is
expected to be substantially below 1.

**However**, the j=1 window
`[ρ_1(c), 1]` with kernel `H_1(c, ρ) = (1/2)·c⁴/ρ²` is the **dominant
single contribution** in V38's seven-window split (Wang's `eq(6)`),
and the j=2 window `[ρ_2(c), ρ_1(c)]` with kernel
`H_2(c, ρ) = (2/3)·c⁶/ρ⁴` is the second-largest. The two-window
mass `mass₁ + mass₂` may therefore be ≥ some non-trivial fraction of
1 (e.g., 0.6 or 0.7 — well below 1, but informative). Phase 0 records
the deficit precisely; this number determines whether (a) more
windows would close the gap (Sprint C territory) or (b) the deficit
is unrecoverable (route is structurally limited even with full V38
seven-window).

### Why this is not a proposal

The four-condition guide:

1. **Tried hard and failed**: sprint 072 attempted general-`m`
   τ-partition reducer; sprint 074 repaired the broken trailing block;
   the obstruction note documents the precise `hcEqStart0` motive
   issue. The two-window concrete-endpoint shape is a **different
   sprint** (m=2 with concrete `(ρStart_i, ρStop_i)` parameters, not
   `Fin m`-indexed start/stop) and has not been attempted.
2. **Genuinely large derivation cost**: the proof body is ~150–200
   lines, well within capacity. The Bulletin's V38 directive lists the
   three composing theorems (`annulusSlice_add_adjacent`,
   `mass_mul_le_annulusSlice_of_integral_bound`,
   `innerExcess_le_of_window_bounds`) all already in
   `KorenblumPaper.AnnulusIntegralReduction`, plus sprint 071's
   single-window reducer. The composition is a finite chain.
3. **Strong reason to believe correct**: the τ-window structure is
   well-defined (`τ_j = 1 − 1/(j+1)²` increasing to 1 as `j → ∞`,
   so `c < c/√τ_2 < c/√τ_1` covers the high-`ρ` region of `(c, 1)`).
   The composition is mechanical Lean-engineering on top of sprint
   071's sound theorem.
4. **Strong evidence of c improvement**: Phase 0 produces this
   evidence. If the joint two-window mass crosses 1 above 7129/20000,
   the sprint pushes c. If not, the sprint ties V60 with structural
   advance. Either branch is a well-defined sprint outcome.

So: attempt-first (numerically + Lean), no proposal.

## Read this before starting

1. `ProofRefinement/Korenblum/Proof/Reduction.lean` lines 7398–7689
   — sprint 071's `valid_of_perMode_tau_window_eq8_eq9` (the reducer
   to compose twice); read its signature, its `OneModePaperBridge.
   pointwise_on_Icc_of_series_endpoint_tau_window_eq8_eq9` discharge
   pattern, and its closing chain via
   `AnnulusIntegralReduction.mass_mul_le_annulusSlice_of_integral_bound`.

2. `KorenblumPaper.AnnulusIntegralReduction` — the three composing
   theorems `annulusSlice_add_adjacent`,
   `mass_mul_le_annulusSlice_of_integral_bound`,
   `innerExcess_le_of_window_bounds` (search for these names; they
   are the Bulletin V38 directive's named building blocks).

3. `Bulletin.md` "Directive update — 2026-05-04 (human, EXPLICIT V38
   REFERENCE)" — the Sprint A/B/C plan, the τ-window endpoint formula
   `ρ_j(c) = c / √τ_j`, the polynomial-inequality form
   `τ_{j-1} · ρ² ≤ c² ≤ τ_j · ρ²` for the τ-bounds, the V38
   strict bracket showing seven-window mass ≈ 1 at c=0.356401.

4. `ProofRefinement/Korenblum/Scratch/sprint_071_per_mode_kernel_witness.{py,txt}`
   — sprint 071's Phase 0 sweep showing single-window kernel mass
   `≈ 0.005` at j*=2, `≈ 5e-4` at j*=3. The script's mpmath
   conventions (`mp.prec = 200`, `n_trunc = 200`) and τ-window
   endpoint-derivation logic (`ρ_j_start = c/sqrt(tau(j))`,
   `ρ_j_stop = c/sqrt(tau(j-1))`) should be reused verbatim. **Note
   that sprint 071 omitted j*=1**; the j=1 window
   `[ρ_1(c), 1]` integrates `H_1 = (1/2)·c⁴/ρ²` and should give a
   substantially larger contribution than j=2's window — this is one
   of the open numerical questions Phase 0 resolves.

5. Sprint 074 (`Sprint_Contracts/sprint_074_repair_reduction_lean_…`)
   — the documentation of the `hcEqStart0` motive obstruction that
   blocked sprint 072's general-`m` `Fin m`-indexed approach. The
   two-window concrete-endpoint shape sidesteps this; the contract's
   signature deliberately uses four plain-real-parameter endpoints
   `ρStart₁, ρStop₁, ρStart₂, ρStop₂` plus a single equality
   `hAdj : ρStop₁ = ρStart₂` rather than `start, stop : Fin 2 → ℝ`.

**Do not modify** `KorenblumPaper/`, `Numerical_Library/`,
`Proof/CandidateContract.lean`, `Proof/Main.lean`, any existing
`Candidates/V<K>.lean` for `K ≤ 60`, any per-candidate derived-theorem
file under `Candidates/V<N>/` for `N ≤ 60`, or `lemma.toml` (other
than possibly one allowlist line for the new candidate's per-candidate
folder, if needed; but no new oracles, no new axioms).

**Do not file a proposal.** Phase 0 must complete first; even a NO-GO
outcome is a structurally informative input to the next planner, not
a trust-base expansion request.

## Concrete edits expected

### Phase 0: mpmath sweep of joint two-window mass

- `Scratch/sprint_078_two_window_tau_mass_sweep.py` (NEW, ≈200–350
  lines): the load-bearing numerical deliverable. Required structure:

  1. **Imports and precision**: `mpmath` with `mp.prec = 200`. No
     `numpy`/`scipy` needed (this is integral computation, not
     optimisation).

  2. **τ-window endpoints**:

     ```python
     def tau(j):  # j ≥ 1; tau(j) = j(j+2)/(j+1)^2
         return mpf(j) * mpf(j+2) / mpf(j+1)**2

     def rho_j(c, j):  # ρ_j(c) = c / sqrt(tau(j))
         return c / mp.sqrt(tau(j))
     ```

     For j=1: `tau(1) = 3/4`, `ρ_1(c) = c·2/√3 ≈ 1.1547·c`.
     For j=2: `tau(2) = 8/9`, `ρ_2(c) = c·3/(2√2) ≈ 1.0607·c`.
     **Sanity check**: `c < ρ_2(c) < ρ_1(c) < 1` for all c ∈ (0, √3/2).

  3. **Mode kernel** (matching sprint 071's
     `ModeBridge.scalarIntegrand c j (paperLambda K c) ρ`):

     ```python
     def H_j(c, j, rho):  # H_j(c, ρ) = (j/(j+1)) · c^(2j+2) / ρ^(2j)
         return mpf(j) / mpf(j+1) * c**(2*j+2) / rho**(2*j)

     def paper_Lambda(c, rho):
         # paperLambda K c ρ = (ρ² − c²)·(ρ² + c²·ρ⁴/c⁴ ?) — match
         # Section2Assumptions.eq7_paperK_formula's K(c, ρ) definition.
         # For the canonical case Wang's K(c, ρ) = (ρ⁴ − c⁴)/c²
         # giving Λ(c, ρ) = K(c, ρ) ?? — verify against
         # sprint 071's Phase 0 script, which has the exact formula.
         # If sprint 071's script uses a closed-form Lambda formula,
         # transcribe it verbatim; otherwise derive from
         # Section2Assumptions.eq7_paperK_formula.
         ...

     def kernel_integrand(c, j, rho):
         # 2ρ / (H_j(c, ρ) · Λ(c, ρ))
         return 2 * rho / (H_j(c, j, rho) * paper_Lambda(c, rho))
     ```

     **Critical**: the Lambda formula **must** be transcribed
     verbatim from sprint 071's script
     (`Scratch/sprint_071_per_mode_kernel_witness.py`) to ensure the
     two scripts compute the same kernel. Add a sanity-check assertion
     at the top of the new script: at `(c, j, ρ) = (0.36, 2, 0.4)`,
     the new script's `H_j · Λ` value matches sprint 071's value to
     within `10^-50`.

  4. **Per-window mass integral**:

     ```python
     def mass_window(c, j, rho_start, rho_stop):
         # mass = ∫_{ρ_start..ρ_stop} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ
         return mp.quad(lambda rho: kernel_integrand(c, j, rho),
                        [rho_start, rho_stop])
     ```

     Use `mp.quad` (Gauss-Legendre at `mp.prec = 200`).

  5. **The two-window joint mass at canonical (j₁, j₂) = (2, 1)**:

     ```python
     def joint_mass_2_1(c):
         rho_start_1 = rho_j(c, 2)   # j=2 window's lower endpoint
         rho_stop_1 = rho_j(c, 1)    # j=2 window's upper endpoint
         rho_start_2 = rho_j(c, 1)   # j=1 window's lower endpoint
         rho_stop_2 = mpf(1)         # j=1 window's upper endpoint
         m1 = mass_window(c, 2, rho_start_1, rho_stop_1)
         m2 = mass_window(c, 1, rho_start_2, rho_stop_2)
         return m1, m2, m1 + m2
     ```

  6. **c-grid**:
     `c ∈ {0.35645, 0.35650, 0.35660, 0.35680, 0.35700, 0.35720,
            0.35740, 0.35760, 0.35780, 0.35800, 0.35820, 0.35840,
            0.35860, 0.35880, 0.35900, 0.35950, 0.36000, 0.36050,
            0.35640, 0.35635}` (the last two are sub-V52 sanity points
     to confirm the kernel is monotone in c near the V52 shoulder).

  7. **Output**:

     - `Scratch/sprint_078_two_window_tau_mass_sweep.txt` — a
       human-readable table with columns
       `(c, ρ_2(c), ρ_1(c), mass_2, mass_1, total = mass_1 + mass_2,
       deficit = 1 − total)`. **Always written.**

     - `Scratch/sprint_078_witness.txt` if some `c > 7129/20000` has
       `total ≥ 1 + 1e-3`: a precise `(c, ρ_2(c), ρ_1(c), mass_1,
       mass_2, total, margin)` dump suitable for Lean instantiation
       in V61. **Written if and only if a witness exists.**

     - `Scratch/sprint_078_no_go.txt` if no such `c` exists: the
       precise deficit (`1 − total`) at every tested c, the worst-c
       deficit, and a closed-form algebraic note on whether the
       deficit appears recoverable by adding more windows (i.e.
       whether Sprint C's seven-window split could close the gap, or
       whether the route is structurally limited even at full V38
       widening). **Written if and only if no witness exists.**

     **Exactly one** of `_witness.txt` or `_no_go.txt` must exist
     after the script completes; presence of both, or of neither,
     is a sprint failure.

  8. **Determinism**: the script is fully deterministic (no
     `random.*` calls). Re-running it produces byte-identical outputs.

### Phase A: closing reducer in `Proof/Reduction.lean`

- `Proof/Reduction.lean` (one new theorem appended before the closing
  `end ProofRefinement.Korenblum`, ≈150–250 lines): the
  `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` theorem
  described in §"Goal" above. Proof body structure:

  1. **Apply sprint 071's `valid_of_perMode_tau_window_eq8_eq9` on
     window 1** to get
     `mass₁ · innerExcess ≤ annulusSlice circleGap ρStart₁ ρStop₁`,
     using the per-window τ-bounds, summability, integrability, and
     the OneModePaperBridge pointwise discharge.

  2. **Apply sprint 071's reducer on window 2** to get
     `mass₂ · innerExcess ≤ annulusSlice circleGap ρStart₂ ρStop₂`.

  3. **Compose via `annulusSlice_add_adjacent`** (using `hAdj :
     ρStop₁ = ρStart₂`) to identify
     `annulusSlice circleGap ρStart₁ ρStop₁ +
       annulusSlice circleGap ρStart₂ ρStop₂ =
         annulusSlice circleGap ρStart₁ ρStop₂`.

  4. **Sum the two `mass · innerExcess ≤ annulusSlice` inequalities**
     to get
     `(mass₁ + mass₂) · innerExcess ≤ annulusSlice circleGap ρStart₁ ρStop₂`.

  5. **Apply `hMassTotal : 1 ≤ mass₁ + mass₂`** plus `innerExcess ≥ 0`
     to get
     `innerExcess ≤ annulusSlice circleGap ρStart₁ ρStop₂`.

  6. **Connect to `ValidKorenblumBound c`** via the existing
     reduction chain in `Proof/Main.lean` (the contract is
     `diskExcess(circleGap) c ≤ annulusExcess(circleGap) c`, which
     splits as `≤ annulusSlice c 1 = annulusSlice c ρStart₁ +
     annulusSlice ρStart₁ ρStop₂ + annulusSlice ρStop₂ 1`; the first
     and last summands are non-negative by `circleGap_nonneg_of_eq8_eq9`,
     reducing the inequality to step 5's output).

  The proof body must:
  - **not use `rewrite` on `ρStart₁ = c`** (that motive issue blocked
    sprint 072; here `ρStart₁` is strictly `> c` by `hOrd.1`, so no
    such rewrite is needed).
  - **not introduce `Fin 2`-indexed `start`/`stop` families**; use
    plain `(ρStart₁, ρStop₁, ρStart₂, ρStop₂ : ℝ)` parameters
    throughout.
  - **explicitly state intermediate lemmas as `have` blocks** so the
    proof can be inspected step-by-step.
  - close with no `axiom`s, no `sorry`s, no `admit`s.

### Phase B: candidate-side V61

If Phase 0 returns **GO** (witness at some `c* > 7129/20000`):

- `Candidates/V61.lean` (NEW, ≈250–400 lines): the c-pushing
  candidate. The theorem `korenblum_constant_search` discharges
  `ValidKorenblumBound (witness_c : ℝ)` via:

  1. `c_value : ℚ := <witness rational>` (e.g. `c_value = 357/1000` if
     the witness is at c=0.357 with sufficient margin); the contract's
     Phase 0 GO definition requires the witness's mass margin ≥ 1e-3
     so a small rational truncation is safe.

  2. The discharge invokes
     `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` with the
     concrete numeric `(ρStart₁, ρStop₁, ρStart₂, ρStop₂)`
     transcribed from the witness file as exact rationals (e.g.
     `ρStart₁ := <ρ_2(c) as rational, sufficient digits to preserve
     margin>`, etc.).

  3. The τ-membership polynomial inequalities are discharged by
     `norm_num` over rationals.

  4. The summability/integrability hypotheses are discharged by the
     existing summability machinery in
     `KorenblumPaper.OneModePaperBridge` (the `circleGap` summability
     at `ρ < 1` is bundled in `Section2Assumptions`).

  5. **The `hMassTotal : 1 ≤ ∫₁ + ∫₂` hypothesis** is the load-bearing
     numerical premise. It is not a closed-form rational; it requires
     either:

     - **An interval-arithmetic Lean derivation** (the integrand is a
       closed-form rational function of `(c, ρ)`, and the
       integral over a rational interval can be bounded below by
       Riemann-sum lower bounds discharged by `norm_num` — analogous
       to V38's `hybridTotalMassQ_ge_one` `norm_num` discharge), or

     - **A new `Numerical_Library` oracle** registered inline in
       `lemma.toml` per AGENT_BRIEF rule 7's pre-approved channel.

     **Use the interval-arithmetic Lean derivation if it fits.** If
     it doesn't (e.g. the kernel's integrand is too oscillatory for a
     `norm_num` Riemann lower-bound to clear with margin), register
     a single oracle per the AGENT_BRIEF preamble's "registered
     oracle" rule with explicit `Numerical_Library` function name,
     `lemma.toml [[oracles]]` row, and Lean-facing axiom statement.
     **Prefer the `norm_num` route** since it gives a strictly
     stronger axiom envelope (no oracle row).

  6. The expected `axioms_used` set, on the GO branch with the
     `norm_num` route, is `{propext, Classical.choice, Quot.sound,
     Lean.ofReduceBool, Lean.trustCompiler}` — **the workspace's
     first oracle-free, eq15-axiom-free certified bound at
     `c > V52`**. This is a strict c-push and a structural
     trust-surface advance simultaneously.

If Phase 0 returns **NO-GO** (joint two-window mass < 1 at every
tested `c > 7129/20000`):

- `Candidates/V61.lean` (NEW, ≈100 lines): V60-tied at
  `c_value = 7129/20000 = 0.35645` via `valid_of_eq15` discharged by
  `hEq15_oracle_certified_hp_35645`, byte-for-byte axiom envelope
  identical to V60. The body is a V60-pattern duplicate plus a side
  lemma `v61_two_window_reducer_compiles_at_witness` that re-states
  the `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` signature
  against an arbitrary `Section2Assumptions` instance and discharges
  by direct invocation (statement-level non-vacuity check; closes
  by `exact valid_of_perMode_twoWindow_tau_partition_eq8_eq9 …`
  threading the hypotheses through `Or.elim` or simply asserting the
  witness side-conditions as further hypotheses on the side lemma).
  The expected `axioms_used` is the V60 set, byte-for-byte.

- `Bulletin.md`: append one row under "Recent events":

  ```
  sprint_078 PASS [GO|NO-GO]: two-window τ-partition reducer in Reduction.lean; V61 [pushes c to <c*> | ties V60 at 7129/20000]
  ```

- `Experience.md`: append a sprint-078 section per the AGENT_BRIEF
  "Honesty in Experience.md" rules, with:
  - **What was attempted**: the reducer signature, the Phase 0 sweep
    grid, the kernel transcription from sprint 071.
  - **What numerical exploration was done**: the joint two-window
    mass at every tested c, the worst deficit on NO-GO, the witness
    margin on GO.
  - **The current obstacle to `c > 7129/20000`**: on GO, the obstacle
    is dissolved (c-push lands); on NO-GO, the obstacle is named as
    the deficit value (e.g., "joint two-window mass = 0.65 at
    c=0.357, deficit = 0.35; bridging this requires four+ additional
    windows per V38's seven-window split"), with a comment on whether
    Sprint C is expected to recover the gap.
  - **What is the next move**: on GO, the next sprint pushes further
    (Sprint C at V38's c with seven windows, or a higher c at three
    windows if Phase 0 GO at multi-c). On NO-GO, the next sprint
    pivots — either to Wang Lemma 2 derivation (Sprint 077 Path B
    item 1) or to Sprint C's seven-window infrastructure as a tie at
    V38's c (if the deficit is reasonably closeable by adding the
    fallback windows + j=3, j=4 windows V38 uses).
  - **What would unblock a c-push faster**: noted per the actual
    sweep result.

## Acceptance criteria

1. **Phase 0: sweep script runs cleanly.**
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run python
   ProofRefinement/Korenblum/Scratch/sprint_078_two_window_tau_mass_sweep.py`
   exits with code 0. The Lambda-formula sanity check vs sprint 071's
   script passes to `10^-50`.

2. **Phase 0: outputs.**
   - `Scratch/sprint_078_two_window_tau_mass_sweep.txt` exists and
     contains the full sweep table.
   - **Exactly one** of `Scratch/sprint_078_witness.txt` or
     `Scratch/sprint_078_no_go.txt` exists.

3. **Phase A: reducer builds.**
   `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.
   The new `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` theorem
   is present with no `axiom`s, no `sorry`s, no `admit`s. The
   theorem's signature uses four plain real parameters
   `(ρStart₁, ρStop₁, ρStart₂, ρStop₂ : ℝ)` plus
   `hAdj : ρStop₁ = ρStart₂`; **no `Fin 2`-indexed start/stop
   families.**

4. **Phase B: candidate builds and evaluator passes.**
   `lake build ProofRefinement.Korenblum.Candidates.V61` succeeds.
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V61.lean` reports
   `pass: true`.

5. **Phase B: score.**
   - On Phase 0 **GO**: score `= witness_c > 7129/20000`. The
     `axioms_used` set excludes `hEq15_oracle_certified_hp_35645`
     and excludes any new oracle (preferring the `norm_num`
     mass-discharge route); if a new oracle is registered, the sprint
     contract's `lemma.toml [[oracles]]` row, `Numerical_Library`
     function, and Lean-facing axiom statement are all explicitly
     named in `Candidates/V61.lean`'s docstring.
   - On Phase 0 **NO-GO**: score `= 7129/20000 = V60`. The
     `axioms_used` set is byte-for-byte the V60 envelope.

6. **No edits to read-only / out-of-scope surfaces.** No edits to
   `KorenblumPaper/*.lean`, no edits to `Numerical_Library/`
   (other than the optional oracle wrapper if Phase 0 GO and the
   `norm_num` route does not fit), no edits to existing
   `Candidates/V<K>.lean` for `K ≤ 60`, no edits to any per-candidate
   derived-theorem file under `Candidates/V<N>/` for `N ≤ 60`,
   no edits to `Proof/CandidateContract.lean` or `Proof/Main.lean`.

7. **No new paper axioms, no new free-floating axioms, no proposal
   filing.** A new oracle row (Phase 0 GO branch only, if `norm_num`
   route doesn't fit) is permitted under the AGENT_BRIEF
   pre-approved channel and does not require a `Proposals/` filing.

8. **Honesty in `Experience.md`.** All five honesty bullets are
   satisfied with concrete content drawn from the actual sweep output
   (no boilerplate, no copy-paste from prior sprint Experience
   entries).

## Out of scope

- A general-`m` `Fin m`-indexed multi-window reducer (sprint 072's
  goal). This sprint targets **m = 2 concrete-endpoint** explicitly
  to sidestep the `hcEqStart0` motive obstruction. Generalisation to
  arbitrary `m` is sprint 079+ territory if (a) the two-window route
  Lean-builds cleanly here and (b) Phase 0's deficit suggests
  Sprint C's seven-window split is needed.

- Sprint C's seven-window split at V38's `c = 356401/1000000`. That
  is sprint 079+ territory regardless of Phase 0 outcome here.

- Wang Lemma 2 / Fourier orthogonality derivation. That is the other
  Path B option from sprint 077; the next planner picks between this
  sprint's outcome and that derivation based on Phase 0 results.

- HP-precision push on the eq15 oracle. Per sprint 060, the cliff
  at HP-35645 is ~1.35e-05 above the literal Wang-(15) crossover at
  c≈0.35635; further HP precision will not move the crossover (the
  limit is mathematical, not numerical).

- An α-varying lift identity Lean derivation (sprint 077 Path A).
  Sprint 077's Experience entry analytically refuted this register;
  running it in Lean would mostly confirm NO-GO.

- Any edit to `KorenblumPaper/`, `Proof/CandidateContract.lean`,
  `Proof/Main.lean`, or `Numerical_Library/rigorous_scalar.py` /
  `wang_box_math.py` / `wang_k_kernel.py`.

- Re-registering the `hEq15_oracle_certified_hp_35645` axiom or
  bumping HP precision.

## Time budget

≤ 120 minutes runtime.

- Phase 0 (mpmath sweep): 15–30 minutes. The cost is ≈20 c-values ×
  2 windows × `mp.quad` Gauss-Legendre at `mp.prec = 200`. Each
  integral is ≈seconds.

- Phase A (`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
  Lean proof): 50–80 minutes. The proof body composes sprint 071
  twice plus three `KorenblumPaper.AnnulusIntegralReduction`
  theorems; the dominant cost is `have` bookkeeping for the four
  endpoint parameters and the per-window τ-bound discharges.

- Phase B (V61 candidate): 30–50 minutes on the GO branch
  (interval-arithmetic `norm_num` mass discharge or oracle
  registration); 10–15 minutes on the NO-GO branch (V60-pattern
  duplicate + side lemma).

- `Bulletin.md` / `Experience.md`: 5 minutes.

If Phase 0 sanity check (Lambda formula vs sprint 071) fails, halt
with `STATUS=BLOCKED` and document the discrepancy; do not proceed
to Phase A or B.

## Stop conditions

- **All eight acceptance criteria met (Phase 0 + Phase A + Phase B
  ship)**: `STATUS=READY_FOR_EVALUATION`. Standard PASS outcome.
  GO branch: c-push lands. NO-GO branch: V60-tie with structural
  reducer advance.

- **Phase 0 sanity check fails** (Lambda formula vs sprint 071
  mismatches by `> 10^-50`): `STATUS=BLOCKED` with obstruction note
  at `Scratch/sprint_078_obstruction.md` documenting the mismatch.
  Do not ship Phase A or Phase B.

- **Phase A reducer build fails** (e.g. an unforeseen rewrite-motive
  obstruction analogous to sprint 072 surfaces, or the
  `annulusSlice_add_adjacent` composition has a hypothesis form
  mismatch): `STATUS=BLOCKED` with obstruction note at
  `Scratch/sprint_078_obstruction.md` documenting the precise tactic
  state at failure plus at least three attempted fixes. Phase 0
  output is preserved as a load-bearing input regardless.

- **Phase B candidate build fails on GO branch** (e.g. `norm_num`
  mass discharge fails at the witness `c` because the integrand
  is too oscillatory): pivot to the oracle registration route per
  the contract's "Phase B" §5; if the oracle route also doesn't
  fit in the remaining budget, fall back to the **NO-GO V60-tie
  branch** documenting Phase 0 GO but Phase B-GO unimplemented at
  `Scratch/sprint_078_obstruction.md`. Ship the V60-tie candidate
  with the structural advance preserved (the new reducer plus the
  Phase 0 witness file). `STATUS=READY_FOR_EVALUATION` is acceptable
  in this fallback.

- **Phase B candidate build fails on NO-GO branch** (some unforeseen
  Lean issue with the V60-pattern duplicate): `STATUS=BLOCKED` with
  obstruction note. Phase A's reducer in `Reduction.lean` is
  preserved as a structural advance regardless.

## Sprint sequencing note (for the next planner)

If Phase 0 returns **GO** and V61 c-pushes:

- **Sprint 079 (GO branch)** — Sprint C from the Bulletin's V38
  directive. Build a seven-window τ-partition reducer (or, if the
  two-window route already pushed strongly, a three-window or
  four-window intermediate as a stepping stone). Target a c above
  the V61 witness or at V38's `c = 356401/1000000`. The seven-window
  split adds j=3, j=4, plus three Wang-eq(5) fallback windows on the
  deep `c < ρ < √(4/3)·c` band. Phase 0 must precede.

If Phase 0 returns **NO-GO** and V61 ties V60:

- **Sprint 079 (NO-GO branch)** — pivot per sprint 077's Path B
  recommendations:

  - **Wang Lemma 2 boundary-L² Parseval-at-radius-ρ** as a V62
    derived theorem. Read `KorenblumPaper.OneModePaperBridge` and
    `KorenblumPaper.PaperEq15` for the existing `tsum`-of-coefficients
    machinery; the Lemma 2 candidate is a per-candidate file
    `Candidates/V62/BoundaryL2Parseval.lean` deriving
    `(1/(2π))·∫_{|z|=ρ} ‖f(z)‖² dθ = ∑'_k ‖f_k‖²·ρ^(2k)` for f
    given as a power series. This Lean-derives a step the paper
    surface currently bundles in `eq3` / `eq8` / `eq9`; if successful
    it eventually enables eliminating those paper axioms from future
    candidates.

  - **Sprint C nonetheless** — even if NO-GO, the seven-window
    infrastructure is necessary for the future paper-axiom-free V38
    route. The seven-window split adds the Wang-eq(5) fallback
    windows that are necessary to close the `c < ρ < √(4/3)·c`
    pocket; these are essential on any tighter envelope, regardless
    of whether Sprint C's ultimate c is above or below V52.
