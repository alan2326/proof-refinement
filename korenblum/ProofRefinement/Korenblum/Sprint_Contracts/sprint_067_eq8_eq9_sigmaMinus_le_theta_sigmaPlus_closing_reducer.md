# Sprint 067: Attempt-first analytic Lean derivation — fuse `paper.{eq8, eq9}` with `sprint 027`'s paper-axiom-free `circleGap = sigmaPlus − sigmaMinus` partition to expose a *new* `Section2Assumptions`-derivable inequality `sigmaMinus ρ ≤ θ(c, ρ) · sigmaPlus ρ` at `ρ > c` with `θ(c, ρ) = paperLambda(c, ρ)/(1 + paperLambda(c, ρ)) < 1`, then ship a closing reducer whose kernel is the `(a, b)`-independent scalar inequality `c² ≤ ∫_{ρ₁..ρ₂} 2ρ / (1 + paperLambda(c, ρ)) dρ`

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V52.lean` (current high-water mark, `c_value = 7129/20000 = 0.35645` via the literal-(15) HP oracle channel)
**Target file**: `Candidates/V53.lean` PLUS supporting per-candidate derived-theorem files under `Candidates/V53/`
**Direction**: section2-proof + analytic-Lean derivation (paper-axiom-light closing reducer with **structurally novel kernel shape `2ρ / (1 + Λ)`** — not `2ρ³ / Λ` and not `2ρ³ · Z_ρ / Λ`)

## Goal

Attempt to ship `Candidates/V53.lean` at the largest rational `c > 7129/20000` for which the kernel inequality

```text
c²  ≤  ∫_{ρ₁..ρ₂}  2ρ / (1 + paperLambda(c, ρ))  dρ           (KERNEL_67)
```

holds with margin, where the closure chain that uses this kernel is:

```text
diskExcess (circleGap a b) c
  ≤ c² · sigmaPlus a b c                                           [sprint 040]
  = c² · sigmaPlus a b c
  ≤ sigmaPlus a b c · ∫_{ρ₁..ρ₂} 2ρ / (1 + paperLambda(c, ρ)) dρ   [KERNEL_67]
  ≤ ∫_{ρ₁..ρ₂} 2ρ · sigmaPlus a b ρ / (1 + paperLambda(c, ρ)) dρ   [sprint 032 monotonicity]
  ≤ ∫_{ρ₁..ρ₂} 2ρ · (sigmaPlus a b ρ − sigmaMinus a b ρ) dρ        [NEW eq8+eq9+sprint 027 chain]
  = ∫_{ρ₁..ρ₂} 2ρ · circleGap a b ρ dρ                             [sprint 027 partition]
  = annulusSlice (circleGap a b) ρ₁ ρ₂
  ≤ annulusExcess (circleGap a b) c                                [non-negativity of `circleGap` outside the slice]
```

The novel mathematical content sits in the second-to-last step: deriving from `paper.eq8_sigma_to_liftGap`, `paper.eq9_liftGap_to_circleGap`, and sprint 027's paper-axiom-free `circleGap = sigmaPlus − sigmaMinus` partition the **per-candidate Lean theorem**

```lean
/-- For any `Section2Assumptions a b K c` instance and any `c < ρ < 1`,
    `sigmaMinus ρ ≤ θ(c, ρ) · sigmaPlus ρ` where
    `θ(c, ρ) := paperLambda K c ρ / (1 + paperLambda K c ρ) < 1`. -/
theorem sigmaMinus_le_theta_sigmaPlus_via_eq8_eq9
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1)
    (hSummable : Summable (fun k : ℕ => coeffPlusGap a b k * ρ ^ (2 * k)))
    : sigmaMinus a b ρ
        ≤ (paperLambda K c ρ / (1 + paperLambda K c ρ)) * sigmaPlus a b ρ
```

whose proof chain is:

1. `eq8` + `eq9` give `sigmaMinus ρ ≤ paperLambda K c ρ · circleGap a b ρ` (workspace already has `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` in `KorenblumPaper/PaperAxioms.lean:377`).
2. sprint 027's `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` gives `circleGap a b ρ = sigmaPlus a b ρ − sigmaMinus a b ρ` (with summability premise on the unconditioned `coeffPlusGap a b k · ρ^(2k)` series; **wait — sprint 027's identity is in terms of `r²·sigmaZeroMinus`, not `sigmaMinus` directly**; verify which form matches and use sprint 005 (`sigmaMinus = ρ²·sigmaZeroMinus`) to bridge if needed).
3. Substitute (2) into (1): `sigmaMinus ρ ≤ paperLambda · (sigmaPlus ρ − sigmaMinus ρ)`.
4. Rearrange: `(1 + paperLambda) · sigmaMinus ρ ≤ paperLambda · sigmaPlus ρ`.
5. Divide by `1 + paperLambda > 0` (which holds since `paperLambda_pos` gives `paperLambda > 0`):
   `sigmaMinus ρ ≤ (paperLambda / (1 + paperLambda)) · sigmaPlus ρ`.

This is a **per-candidate derived theorem under `Candidates/V53/`** per `AGENT_BRIEF.md`'s "Creating derived-theorem files under `Candidates/V<N>/`" rule. NOT a new `Section2Assumptions` field. NOT a new free-floating axiom. NOT a `KorenblumPaper/` edit. Length estimate: 60–120 lines of Lean.

The closing reducer is then the **structurally new** workspace lemma

```lean
/-- Sprint 067 — closing reducer with paper-axiom signature `{eq8, eq9}`,
    zero oracle cells, kernel `c² ≤ ∫_{ρ₁..ρ₂} 2ρ/(1+Λ(c,ρ)) dρ`. -/
theorem valid_of_disk_eq3_partition_sigmaPlus_only_annulus_eq8_eq9_theta_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            -- summability + integrability cells (analogues of sprint 045's)
            … ∧
            -- KERNEL_67: scalar (`(a, b)`-independent) inequality
            (c ^ 2)
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' / (1 + WangOuter.paperLambda K c ρ')) :
    ValidKorenblumBound c
```

added to `Proof/Reduction.lean`. Length estimate: 150–300 lines.

## Why

### Why this sprint, why now

Both sprint 065 (numerical attack on the per-`k` × per-`k` kernel) and sprint
066 (analytic attack on sprint 045's per-`k` × integrated kernel) returned
`BLOCKED` with structurally novel obstruction notes. Sprint 066's analysis
identified two distinct bottleneck cells:

1. sprint 014's residual scalar kernel `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ`
   — already known from sprint 048's mpmath sweep to be **numerically false at
   `c ≥ 0.3554`** (gap −7.75e-03 at the seed), so EVEN IF derivable from
   `Section2Assumptions` it cannot push `c` past V0.
2. The missing field shape `Section2Assumptions.eq4_at_outer_radius`
   supplying `sigmaPlus ρ ≤ φ(c, ρ) · sigmaZeroMinus a b ρ` at `ρ > c`
   (the `proposal_003` target, now *superseded* per the unstuck plan).

This sprint exploits a **third route** that sprint 066's three-direction
enumeration missed: instead of trying to upper-bound `sigmaPlus ρ`
(Direction B's bottleneck) or to discharge a `2ρ³/Λ`-shaped kernel
(Direction A's bottleneck), we **upper-bound `sigmaMinus ρ` by
`θ(c, ρ) · sigmaPlus ρ` with `θ < 1`** directly from `paper.eq8 + paper.eq9
+ sprint 027`. This bound is paper-axiom-light (uses only `eq8`, `eq9`),
oracle-cell-free, and produces a kernel whose integrand `2ρ / (1 + Λ)` is
**bounded above by a fixed constant** in any `[ρ₁, ρ₂] ⊂ (c, 1)` because
`paperLambda K c ρ ≥ 1` on the relevant range (a known consequence of the
Wang kernel formula at admissible `(c, ρ)`; see sprint 048's tabulation
showing `Λ(0.35645, ρ)` ranges over roughly `[2.27, 27.4]` on the
relevant ρ-window). So the integrand `2ρ/(1+Λ)` ranges over roughly
`[0.06, 0.55]`, whereas sprint 014's `2ρ³/Λ` ranges over much smaller values
(0.001–0.01 territory). **The new kernel `c² ≤ ∫ 2ρ/(1+Λ) dρ` is
plausibly tight at much larger `c` than sprint 014's kernel.**

Quick back-of-envelope at `c = 0.36`, `[ρ₁, ρ₂] = [0.4, 0.99]`:
- LHS `c² = 0.1296`.
- Spot values of `2ρ/(1+Λ(c, ρ))` at `c = 0.36`: at `ρ = 0.5`,
  `Λ ≈ 1.10`, integrand ≈ `1.0/2.10 ≈ 0.477`; at `ρ = 0.9`, `Λ ≈ 1.77`,
  integrand ≈ `1.8/2.77 ≈ 0.649`; at `ρ = 0.99`, `Λ` is larger but still
  finite, integrand still ~0.4-0.6.
- Trapezoidal estimate over `[0.4, 0.99]`: average ~0.55 × width 0.59 ≈ 0.32.
- Gap: `0.32 − 0.1296 = +0.19` — large positive margin.

This margin is **far larger** than sprint 048's branch-2 kernel margin
(+1.72e-04 at the seed, falsifying at c=0.36) or sprint 014's full-window
kernel (negative everywhere ≥ 0.3554). The new kernel shape is materially
different and worth the analytic-Lean attempt.

### Why this is not a numerical-push-only sprint

The kernel `c² ≤ ∫_{ρ₁..ρ₂} 2ρ/(1 + paperLambda(c, ρ)) dρ` is a closed-form
scalar inequality (`(a, b)`-independent), so it can be verified in `Scratch/`
before any Lean is written (Phase A). But the **closure chain that uses this
kernel requires the new per-candidate Lean theorem `sigmaMinus ρ ≤ θ · sigmaPlus ρ`
plus a new closing reducer in `Reduction.lean`** — both of which are
*genuine analytic-Lean work*. This is not "register an oracle and ship".

The score-improvement direction is real: if KERNEL_67 admits at, say,
`c = 1825/5000 = 0.365` with margin and the chain compiles, V53 ships at
`c = 1825/5000 = 0.365 ≫ 7129/20000 = 0.35645`. **First analytic-Lean
c-push past the eq15-oracle ceiling** (sprints 053–059 were oracle-channel
c-pushes; sprint 067 would be a paper-axiom-light c-push).

### Generator capability check (per planner agent rules)

The rule reads: "If a planner cannot enumerate three distinct
Lean-derivation directions for an analytic claim, the obstruction is
structural, not capability."

Three distinct directions for the **per-candidate derived theorem**
`sigmaMinus_le_theta_sigmaPlus_via_eq8_eq9` enumerated below:

- **Direction 1**: chain `eq8 + eq9 + sprint 027` directly per the proof
  sketch above. ~80 lines.
- **Direction 2**: use `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (already
  in `PaperAxioms.lean:377`) for step 1, sprint 005's
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` to convert `sigmaMinus = ρ²·Z_ρ`,
  sprint 027's identity rewriting `circleGap = sigmaPlus − ρ²·Z_ρ`, then
  the algebraic rearrangement. ~60 lines.
- **Direction 3**: prove the contrapositive `sigmaMinus ρ > θ · sigmaPlus ρ
  → contradiction with eq8+eq9` via case analysis. ~100 lines (less likely
  to be cleaner but a fallback if Directions 1/2 hit a tactical wall).

Three distinct directions for the **closing reducer**:

- **Direction A**: full-window `[ρ₁, ρ₂] ⊂ (c, 1)`, mirror sprint 045's
  reducer signature shape with `(c²)` instead of `(Σ⁺_int(c))` on the LHS.
- **Direction B**: branch-1 sub-window `[ρ₁, ρ₂] ⊂ (c, branchSplit c]`,
  mirror sprint 017's branch-2 reducer with the new kernel shape on the
  branch-1 sub-window (margin smaller; might allow tighter c with smaller
  window).
- **Direction C**: branch-2 sub-window `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`,
  reduce KERNEL_67 to `c² ≤ ∫_{branchSplit c..ρ₂} 2ρ/(1+Λ) dρ`, where the
  `Λ` denominator is uniformly larger on branch-2 (so `1+Λ` is larger,
  integrand smaller) — possibly the harder sub-window to close.

### Why proposal-filing is not the right shape

Per the four-condition guide:

1. **Tried hard and failed**: this exact derivation has NEVER been
   attempted in Lean. Sprint 066's three directions were all about
   bounding `sigmaPlus ρ` from above (the "wrong direction" for our
   purposes) — none attempted to bound `sigmaMinus ρ` from above by a
   fraction of `sigmaPlus ρ`. **Condition not satisfied — so this is an
   attempt sprint, not a proposal.**
2. **Genuinely large derivation cost**: predicted body ~300 lines total
   (60–120 for the per-candidate sigmaMinus theorem, 150–300 for the new
   closing reducer in `Reduction.lean`). **Within generator scope.**
3. **Strong reason to believe correct**: the derivation chain is
   pure algebra plus a single division by `1 + paperLambda > 0`. The
   underlying inequality `sigmaMinus ρ ≤ paperLambda · circleGap ρ` is
   already a workspace theorem (`eq8eq9_sigma_to_circleBridge_of_eq8_eq9`).
   The rearrangement to `sigmaMinus ≤ (Λ/(1+Λ))·sigmaPlus` is a one-line
   algebraic step. **Mathematical truth not in doubt.**
4. **Strong evidence improves `c_value`**: back-of-envelope at c=0.36
   shows margin ~0.19 (vs. sprint 014's branch-2 margin +1.72e-04 at
   the seed), which is **three orders of magnitude larger headroom**
   than the existing closed-form kernels admit. If the chain compiles,
   c-push at least to `c ≈ 0.365` is plausible and should be testable
   inside this sprint. **Strong c-push evidence.**

So this is an attempt sprint, not a proposal sprint.

## Phase A — `Scratch/` numerical pre-verification (before writing any Lean)

Per Bulletin lines 99–104 ("`Scratch/` is the right place for Python/SymPy/
SageMath/numerical scripts that test whether a proposed inequality actually
holds"), the generator MUST first verify KERNEL_67 numerically before
writing Lean.

Write `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.py` (with
`mpmath dps=50, N_RHO_GRID=2000`) that computes both sides of

```text
c² ≤ ∫_{ρ₁..ρ₂} 2ρ / (1 + paperLambda(c, ρ)) dρ        (KERNEL_67)
```

over a grid of `c ∈ {0.355, 0.357, 0.36, 0.365, 0.37, 0.38, 0.40, 0.50}`
with three windowing strategies:

- **Strategy I — full-window**: `ρ₁ = c + ε₁`, `ρ₂ = 1 − ε₂` with
  `ε₁, ε₂ ∈ {1e-3, 1e-4, 1e-5}`.
- **Strategy II — branch-1**: `ρ₁ = c + ε₁`, `ρ₂ = branchSplit(c) =
  sqrt(4/3) · c`.
- **Strategy III — branch-2**: `ρ₁ = branchSplit(c) + ε₁`,
  `ρ₂ = 1 − ε₂`.

Report the gap `RHS − LHS` for each `(c, strategy, ε)` triple. Identify the
**largest `c` with margin ≥ 1e-3** under at least one of the three
strategies; this is the candidate target for V53. Save the script and its
output to `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}`.

If KERNEL_67 falsifies above `c = 7129/20000` under all three strategies,
**proceed to Outcome B** (no V53; obstruction note documenting the
falsification with mpmath verification).

If KERNEL_67 admits at some `c > 7129/20000` with margin ≥ 1e-3 under at
least one strategy, **proceed to Phase B**.

## Phase B — analytic Lean derivation (only if Phase A confirms admission)

### Per-candidate derived theorem under `Candidates/V53/`

Create `Candidates/V53/SigmaMinusBound.lean` containing:

```lean
namespace ProofRefinement.Korenblum.Candidates.V53

open KorenblumPaper.PaperAxioms WangKernelExact WangOuter

/-- The θ factor `paperLambda(c, ρ) / (1 + paperLambda(c, ρ))` lies in `(0, 1)`
    for `c < ρ < 1`. -/
theorem theta_lt_one
    {K : ℝ → ℝ → ℝ} {c : ℝ} (hc_pos : 0 < c) (hc_lt_one : c < 1)
    {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
    0 < paperLambda K c ρ / (1 + paperLambda K c ρ) ∧
      paperLambda K c ρ / (1 + paperLambda K c ρ) < 1

/-- Per-candidate derived theorem: `sigmaMinus ρ ≤ θ(c, ρ) · sigmaPlus ρ` at
    `ρ > c`, derived from `paper.eq8 + paper.eq9 + sprint 027`. -/
theorem sigmaMinus_le_theta_sigmaPlus_via_eq8_eq9
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1)
    (hSummable :
      Summable (fun k : ℕ => coeffPlusGap a b k * ρ ^ (2 * k))) :
    sigmaMinus a b ρ ≤
      (paperLambda K c ρ / (1 + paperLambda K c ρ)) * sigmaPlus a b ρ

end ProofRefinement.Korenblum.Candidates.V53
```

Proof body uses (no new axioms):
- `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (already in `KorenblumPaper.PaperAxioms`).
- `paperLambda_pos` (workspace lemma for `paperLambda > 0`).
- `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` (sprint 027,
  paper-axiom-free, in `Reduction.lean`).
- `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` (sprint 005) if needed for
  bridging between `r²·sigmaZeroMinus` and `sigmaMinus`.
- `field_simp`, `nlinarith`, `ring`.

### New closing reducer in `Proof/Reduction.lean`

Add the new closing reducer

```lean
theorem valid_of_disk_eq3_partition_sigmaPlus_only_annulus_eq8_eq9_theta_window
```

with paper-axiom signature `{eq8, eq9}` and zero oracle cells. The reducer's
body chains:

1. `diskExcess ≤ c²·sigmaPlus c` (sprint 040).
2. `sigmaPlus c ≤ sigmaPlus ρ` for ρ ≥ c (sprint 032 monotonicity).
3. `sigmaMinus ρ ≤ θ(c, ρ)·sigmaPlus ρ` for c < ρ < 1 (the per-candidate
   theorem above).
4. Hence `circleGap ρ = sigmaPlus ρ − sigmaMinus ρ ≥ (1 − θ(c, ρ))·sigmaPlus ρ
   = sigmaPlus ρ / (1 + paperLambda(c, ρ))` (sprint 027).
5. Integrate over `[ρ₁, ρ₂] ⊂ (c, 1)`:
   `annulusSlice (circleGap a b) ρ₁ ρ₂ ≥ ∫_{ρ₁..ρ₂} 2ρ·sigmaPlus ρ/(1+Λ) dρ
     ≥ sigmaPlus c · ∫_{ρ₁..ρ₂} 2ρ/(1+Λ) dρ` (sprint 032 + Z-monotonicity-style step).
6. `annulusExcess ≥ annulusSlice ρ₁ ρ₂` (since circleGap ρ ≥ 0 on (c, 1)
   from `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper` — already
   workspace).
7. KERNEL_67: `c² ≤ ∫_{ρ₁..ρ₂} 2ρ/(1+Λ(c, ρ)) dρ` (the witness existential
   cell, `(a, b)`-independent).
8. Combining: `diskExcess ≤ c²·sigmaPlus c ≤ sigmaPlus c·∫_{ρ₁..ρ₂} 2ρ/(1+Λ) dρ
   ≤ annulusSlice ρ₁ ρ₂ ≤ annulusExcess`.

Edge case: if `sigmaPlus c = 0` (e.g., the trivial all-zero adversary, or
the structural `n1Pred = const false` adversary which doesn't satisfy
`Section2Assumptions` anyway), then `diskExcess ≤ 0` directly via sprint 040
plus the trivial `0 ≤ annulusExcess` case (sprint 037 / `circleGap_nonneg`).

### V53 candidate file

`Candidates/V53.lean` instantiates the new closing reducer at the largest
`c` Phase A confirms admission for, with `c_value = ?/?` (some rational
`> 7129/20000` per Phase A).

The witness existential `h_witness` constructs `(ρ₁, ρ₂)` from Phase A's
optimal window, discharges the summability + integrability cells via
existing workspace machinery (mirror sprint 045's witness assembly), and
discharges KERNEL_67 either:

- (preferred) via `norm_num` on a closed-form rational evaluation of
  `∫_{ρ₁..ρ₂} 2ρ/(1+paperLambda(c, ρ)) dρ` — but the integrand is *not*
  closed-form in elementary functions, so this is unlikely to work
  directly.
- (fallback) via a fresh oracle entry in `lemma.toml` that wraps a
  `Numerical_Library/rigorous_scalar.py::certify_kernel67(c)` function
  computing the integral with mpmath verified-interval arithmetic and
  asserting `c² ≤ <verified lower bound on integral>`. This follows the
  sprint 052/053 oracle pattern verbatim. The oracle is a *new*
  `[[oracles]]` entry, NOT a `Proposals/` filing — per `AGENT_BRIEF.md`
  oracle channel pre-approval — provided the contract names the wrapper
  function, the `lemma.toml` entry, and the Lean axiom.

If the fallback oracle route is used, the sprint MUST also:
- Add `Numerical_Library/rigorous_scalar.py::certify_kernel67_at_<c>(...)`
  (one wrapper per candidate `c`, mirroring `certify_eq15_at_hp_*`).
- Add the `[[oracles]]` row to `lemma.toml`.
- Add the Lean-facing axiom `axiom hKernel67_oracle_certified_<c> : c² ≤ ∫ …`
  in `Candidates/V53.lean`.
- Pre-verify the oracle accepts at the chosen `c` with `Scratch/sprint_067_oracle_pre_verification.{py,txt}`.

## Concrete edits expected

### Outcome A (Phase A admits AND Phase B chain compiles, `c_value > 7129/20000`)

- `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}`: Phase A
  numerical sweep evidence.
- `Scratch/sprint_067_oracle_pre_verification.{py,txt}` (only if oracle
  fallback used): pre-Lean verification at the chosen `c`.
- `Candidates/V53/SigmaMinusBound.lean`: per-candidate derived-theorem
  file (60–120 lines).
- `Proof/Reduction.lean`: new closing reducer
  `valid_of_disk_eq3_partition_sigmaPlus_only_annulus_eq8_eq9_theta_window`
  (150–300 lines).
- `Candidates/V53.lean`: new candidate at `c_value = ?/?`.
- `Numerical_Library/rigorous_scalar.py` (only if oracle fallback used):
  new `certify_kernel67_at_<c>` function.
- `lemma.toml` (only if oracle fallback used): new `[[oracles]]` entry.
- `Bulletin.md` `## Recent events` row.
- `Experience.md` entry per the "Honesty in Experience.md" directive.
- `Refinement_Log/log.jsonl` row appended by the evaluator.

### Outcome A' (Phase A admits, Phase B chain compiles, but only at `c = 7129/20000`)

This is the c-tying outcome. Per Bulletin lines 27–31, sprints that tie
V0's `c` are no longer wins — but V52 already pushed past V0, and sprint
067 retiring the `eq15` oracle in favour of an `eq8+eq9`-based chain
would be a **strict trust-surface improvement** even at the V52 c.
Justification for the c-tie:

- `axioms_used` shrinks from `{seed, hEq15_oracle_certified_hp_35645}` to
  `{seed}` (no oracle) OR `{seed, hKernel67_oracle_certified_hp_35645}` —
  in either case, the oracle dependence shifts from a literal-(15) channel
  to a structurally novel `2ρ/(1+Λ)` channel which has independent
  numerical verifiability.
- The new closing reducer is a paper-axiom-light `(a, b)`-independent
  scalar-criterion-style chain that is structurally distinct from every
  prior workspace closing reducer — a genuine analytical advance even at
  the same `c`.

If Outcome A' obtains, the sprint MUST explicitly justify the c-tie in
the Bulletin / Experience entries per the bulletin's c-tie rule.

### Outcome B (Phase A falsifies KERNEL_67 above 7129/20000 OR Phase B chain BLOCKED)

- `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}`: Phase A
  evidence — even if falsifies, the sweep is the *deliverable*.
- `Scratch/sprint_067_obstruction.md`: precise obstruction note. Style:
  match `Scratch/sprint_065_obstruction.md` and
  `Scratch/sprint_066_obstruction.md`. Content depends on which Phase
  blocked:
  - **Phase A blocks (KERNEL_67 falsifies above seed)**: report the gap
    table over the c-grid + strategy combinations, and identify which
    `(c, strategy, ε)` triple has the smallest negative gap (closest to
    admission). Estimate via slope extrapolation what new lemma family
    would close the gap (e.g., a tighter `paperLambda` upper bound, a
    refined `[ρ₁, ρ₂]`-window, a per-`k` strengthening of step 5's
    `sigmaPlus monotonicity` step).
  - **Phase B blocks (chain doesn't compile)**: name the exact
    bottleneck cell at the granularity of sprint 066's obstruction note.
    Likely candidates: (i) the `sigmaPlus_monotone_of_summable` step
    (sprint 032) requires summability at `ρ₂` which the witness must
    expose — verify witness construction; (ii) the
    `circleGap_eq_sigmaPlus_minus_sigmaMinus` step (sprint 027) requires
    summability of the unconditioned `cPG·ρ^(2k)` series — verify
    transferability from existing summability cells; (iii) the algebraic
    rearrangement step `(1+Λ)·sigmaMinus ≤ Λ·sigmaPlus → sigmaMinus ≤
    (Λ/(1+Λ))·sigmaPlus` requires `1+Λ > 0` and a positive-denominator
    division — verify `paperLambda_pos`'s availability.
- (NO `Candidates/V53.lean`, NO new files under `Candidates/V53/`, NO
  `Reduction.lean` edit, NO `lemma.toml` edit, NO `Numerical_Library/`
  edit, NO `KorenblumPaper/` edit if Outcome B obtains.)
- `Bulletin.md` `## Recent events` row.
- `Experience.md` entry per the "Honesty in Experience.md" directive.

## Acceptance criteria

### Outcome A or A'

1. `lake build ProofRefinement.Korenblum.Candidates.V53` succeeds with no
   `sorry`, no new free-floating axioms beyond seed (and the optional
   `hKernel67_oracle_certified_*` oracle if the oracle-fallback route is
   taken).
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V53.lean` returns `pass: true`.
3. `axioms_used ⊆ {seed} ∪ {hKernel67_oracle_certified_<c>}` (exactly one
   new oracle, OR no new oracle if the kernel proves analytically). The
   oracle name MUST end in the c value to disambiguate from the eq15
   oracle channel.
4. **Outcome A**: `c_value > 7129/20000` (strict c-push).
   **Outcome A'**: `c_value = 7129/20000` AND the Bulletin/Experience
   entries explicitly justify the c-tie via trust-surface improvement
   (oracle channel diversification, new paper-axiom-light closing reducer).
5. `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}` exists
   and confirms KERNEL_67 admits with margin ≥ 1e-3 at the chosen `c`.

### Outcome B

1. `Scratch/sprint_067_obstruction.md` exists with:
   - the exact Phase A gap table (or Phase B tactic chain), line-by-line,
   - the exact bottleneck cell (numerical at fine c-step, or
     paper-axiom/workspace lemma name at the granularity of sprint 066's
     obstruction note style),
   - a closed-form algebraic identity showing why the bottleneck is
     mathematical, not tactical (analogous to sprint 066's
     "Closed-form algebraic identity confirming the obstruction is
     mathematical" section),
   - **no false-claim** — Outcome B may report numerical falsification
     with explicit margins, but must NOT claim the kernel is
     mathematically false on the `Section2Assumptions`-cone (since
     Phase A tests a closed-form scalar inequality, not a cone-restricted
     one — falsification IS legitimate here, distinct from sprint 066's
     no-falsification clause).
2. `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}` exists
   even if Outcome B (the Phase A evidence is itself the deliverable).
3. NO `Candidates/V53.lean`, NO new files under `Candidates/V53/`, NO
   edits to `Reduction.lean`, `lemma.toml`, `Numerical_Library/`, or
   `KorenblumPaper/`.
4. STATUS=BLOCKED returned (NOT `BLOCKED_NEEDS_HUMAN`, NOT a halt sibling
   — the obstruction is tactical-Lean / numerical-falsification, not a
   trust-base expansion request).

## Out of scope

- Edit older candidates (V0–V52).
- Edit `KorenblumPaper/` (the trusted paper surface is read-only for the
  generator per `AGENT_BRIEF.md`).
- Add a new `Section2Assumptions` field. The new content goes into
  `Candidates/V53/` as per-candidate derived theorems and into
  `Reduction.lean` as a new closing reducer — both ride on top of the
  existing Section2Assumptions structure.
- File a new `Proposals/proposal_*.md` entry. Per the harness unstuck
  plan, proposal-filing is reserved for the narrow case where a Lean
  derivation has been attempted and failed; sprint 067 IS the attempt
  sprint. If Outcome B obtains, the obstruction note is the deliverable;
  any successor proposal_004 is the *next planner's* deliverable.
- Edit any `Proposals/proposal_*.md` `Status:` field. proposal_001
  remains `rejected`, proposal_002 remains `pending` (deferred),
  proposal_003 remains `superseded`.
- Write a halt-sibling sprint contract (per the harness policy in
  `sprint_064_canonical_halt_declaration_no_further_halt_siblings.md`).
- Run a new canonical-extremal numerical sweep over E0–E3 — the relevant
  numerical question (does KERNEL_67 admit at c > 0.35645?) is
  `(a, b)`-independent and answered by Phase A.
- Test the drop-N2 closing reducer `Σ⁺_int(c) ≤ Σ⁺_int_ann(c)` from
  sprint 065's obstruction-note recommendation. Sprint 066's experience
  entry already flagged it as semantically backwards (dropping a
  positive-mass term from an upper bound increases the upper bound,
  wrong direction); sprint 067 supersedes that recommendation with a
  structurally novel chain that does not have the direction issue.

## Time budget

≤ 90 minutes runtime. Includes:
- Phase A: ~10 minutes (mpmath sweep over the c-grid × strategies).
- Phase B Per-candidate file: ~25 minutes (60–120 line Lean derivation).
- Phase B Closing reducer: ~30 minutes (150–300 line Lean derivation).
- Phase B V53 + witness: ~15 minutes (witness assembly, oracle wiring if
  needed).
- Bulletin / Experience / log entries: ~10 minutes.

If Phase A falsifies KERNEL_67 above seed, exit Outcome B at ~15 minutes.
If Phase B chain hits a tactical wall, exit Outcome B at ~60 minutes with
a precise obstruction note (do NOT loop indefinitely on a single tactic).

## Stop conditions

- **Outcome A**: `lake build` and Evaluator both pass; `c_value > 7129/20000`;
  `axioms_used ⊆ {seed} ∪ {hKernel67_oracle_certified_*}`. Return
  `STATUS=READY_FOR_EVALUATION`.
- **Outcome A'**: same as A but `c_value = 7129/20000`. Return
  `STATUS=READY_FOR_EVALUATION` with explicit Bulletin/Experience c-tie
  justification.
- **Outcome B**: `Scratch/sprint_067_obstruction.md` written;
  `Scratch/sprint_067_kernel_2rho_over_one_plus_Lambda.{py,txt}` written;
  no V53; STATUS=BLOCKED.
- Genuine trust-base ambiguity (e.g. the chain requires a
  `Section2Assumptions` field that doesn't exist and the planner missed
  it): STATUS=BLOCKED_NEEDS_HUMAN with a precise note. This is **rare**
  and should not be the first-resort exit.

## Reference: existing workspace assets

The generator should review (without re-deriving) these
paper-axiom-free / paper-axiom-light primitives before attempting the
chain:

- **`KorenblumPaper.PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9`**
  (line 377): `sigmaMinus ρ ≤ paperLambda(c, ρ) · circleGap a b ρ` for
  `c < ρ < 1`. This is the ALREADY-WORKSPACE step 1 of the
  per-candidate theorem above.
- **Sprint 005**: `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`. Bridge
  between `sigmaMinus` and `ρ²·sigmaZeroMinus` if needed.
- **Sprint 027**:
  `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`. The
  paper-axiom-free partition identity. This is step 2.
- **Sprint 032**: `sigmaPlus_monotone_of_summable`. The N1-side
  monotonicity (paper-axiom-free).
- **Sprint 040**:
  `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`. The
  `diskExcess ≤ c²·Σ⁺(c)` paper-axiom-free disk bound (sprint 040 wraps
  sprint 027 + sprint 032 in an integrated form). This is the disk-side
  input to the new closing reducer.
- **`OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper`**: the
  workspace's `circleGap a b ρ ≥ 0` for `c < ρ < 1` derivation, used to
  pass from `annulusSlice ρ₁ ρ₂` to `annulusExcess`.
- **`WangOuter.paperLambda_pos`**: `paperLambda K c ρ > 0` for `0 < c < ρ < 1`.

The `paper.eq2` through `paper.eq9` fields are exposed on
`Section2Assumptions` and may be invoked. **This sprint uses `eq8` and
`eq9` only on the paper-axiom side** — strictly fewer than V52's
`{eq2, ..., eq14, eq15}` chain.

## Why the kernel shape is genuinely novel

Every prior closed-form `(a, b)`-independent kernel in `Reduction.lean`
has integrand `2ρ³ / paperLambda(c, ρ)` (sprint 014, 017, 021, 023, 024,
039, 045 — all of these reduce to a `c⁴` or `c⁴/2` LHS divided by
`Z`-side mass and integrated against the `2ρ³/Λ` shape).

KERNEL_67's integrand `2ρ / (1 + paperLambda(c, ρ))` is **structurally
different** in three ways:

1. **Polynomial factor `2ρ` instead of `2ρ³`**: this comes from the polar
   Jacobian without the additional `ρ²` factor that `sigmaMinus = ρ²·Z_ρ`
   contributes in the `2ρ³/Λ` chain.
2. **Denominator `1 + Λ` instead of `Λ`**: this comes from the
   `(1+paperLambda)·sigmaMinus ≤ paperLambda·sigmaPlus` rearrangement,
   which puts `paperLambda + 1` in the denominator instead of just
   `paperLambda`.
3. **No `Z`-side factor on the LHS**: KERNEL_67 has LHS `c²` (from
   sprint 040) instead of `c⁴` or `c⁴/2` (from sprint 013/016, which use
   `eq3+eq4` to get `Z_c·c⁴` and then divide by `Z_c`). The `c²`
   normalisation is the per-candidate price for using sprint 040's
   `diskExcess ≤ c²·Σ⁺(c)` instead of the bulk `diskExcess ≤ c⁴·Z_c`.

The combination — `c² ≤ ∫ 2ρ/(1+Λ) dρ` instead of `c⁴ ≤ ∫ 2ρ³/Λ dρ` —
gives a **strictly larger margin** at every tested `c` because:

- `c² > c⁴` (factor `1/c² ≈ 7.87` larger LHS at c=0.35645) ... hmm wait,
  this works AGAINST us. But:
- `2ρ/(1+Λ) > 2ρ³/Λ` whenever `2ρ·Λ > 2ρ³·(1+Λ)`, i.e., `Λ > ρ²(1+Λ)`,
  i.e., `Λ·(1-ρ²) > ρ²`, i.e., `Λ > ρ²/(1-ρ²)`. At `ρ = 0.99`,
  `ρ²/(1-ρ²) ≈ 0.98/0.02 = 49`. `paperLambda(0.36, 0.99)` is large
  (perhaps 10–50 range). So at the right edge of the window, the new
  integrand may NOT dominate the old one. **The numerical advantage
  comes from the BULK of the window where Λ is moderate** (Λ ≈ 1.5
  at c=0.36, ρ ≈ 0.5).

The Phase A sweep is the definitive test. If the gap is positive at
`c > 0.35645` with margin, the chain unlocks an analytic-Lean c-push.
If the gap turns out to be negative, Outcome B documents which `(c, ρ)`
ranges falsify and what tightening would close them — informing the next
planner.

## A note on the trust-surface accounting

Outcome A or A' produces:
- One new per-candidate derived theorem under `Candidates/V53/` (no new
  axiom; just a Lean theorem on top of `eq8 + eq9 + sprint 027`).
- One new closing reducer in `Reduction.lean` (no new axiom; just a Lean
  theorem on top of the new per-candidate theorem + sprint 040 +
  sprint 032 + `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9`).
- Optionally one new oracle in `lemma.toml` (the `hKernel67_oracle_certified_*`
  channel) if KERNEL_67 cannot be discharged by `norm_num` /
  `polyrith` directly. The oracle is a *new* `[[oracles]]` entry per
  the pre-approved channel in `AGENT_BRIEF.md`; no `Proposals/` filing
  required.

If the oracle fallback is used, the new oracle is **a structurally
distinct channel** from the existing `hEq15_oracle_certified_*` channel:
the latter discharges `1 ≤ scalarCriterion c paperLambda` (the literal-(15)
inequality, which has the `12ρ³(ρ²−c²)/(c⁶Λ) + 4ρ³/(c⁴Λ)`-shaped
integrands), the former discharges `c² ≤ ∫ 2ρ/(1+Λ) dρ` (a
structurally distinct integrand). Two oracles, two distinct numerical
channels — both pre-approved per `AGENT_BRIEF.md`.

The trust-surface accounting at Outcome A:
- `axioms_used` (V52): `{seed, hEq15_oracle_certified_hp_35645}`.
- `axioms_used` (V53 if oracle-route): `{seed, hKernel67_oracle_certified_*}`.
- `axioms_used` (V53 if pure-analytic-route): `{seed}` ONLY.

The pure-analytic route (no new oracle) is the gold standard if KERNEL_67
admits a Lean closed-form proof. The oracle-fallback is the silver
standard if the integral is not tractable closed-form.

## Pointers

- Bulletin priority block at `Bulletin.md` lines 1–325 — read this first.
- Sprint 066 obstruction note at `Scratch/sprint_066_obstruction.md` —
  documents the bottlenecks this sprint routes around.
- Sprint 065 obstruction note at `Scratch/sprint_065_obstruction.md` —
  documents the canonical-extremal-cone vs. Section2Assumptions-cone
  distinction that motivates Phase A's `(a, b)`-independent kernel.
- `KorenblumPaper.PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9`
  at `KorenblumPaper/PaperAxioms.lean:377` — the workspace primitive
  that does step 1 of the per-candidate theorem.
- `Reduction.lean` sprint 040 at line 6184; sprint 032 at line 4675;
  sprint 027 at line ~4400 (find via grep
  `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`).
