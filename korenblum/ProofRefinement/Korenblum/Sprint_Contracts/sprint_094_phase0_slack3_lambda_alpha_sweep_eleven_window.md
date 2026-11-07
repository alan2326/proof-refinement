# Sprint 094: Phase 0 probe — Slack 3 Λ-tightening on V68's eleven windows via fine α-sweep

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`)
**Target file**: `Scratch/sprint_094_slack3_lambda_alpha_sweep.{py,txt,witness.txt}` (no Lean changes this sprint)
**Direction**: raise-c (Phase 0 only, structural — Slack 3 attacks the outer/boundary kernel `Λ(c, ρ) := paperLambda K c ρ`, distinct from Slacks 1/2/5 which all act on the inner per-mode kernel `H_j(c, ρ)`)

## Goal

Numerically probe whether the outer paper kernel `Λ(c, ρ)` (the "outer
control" the Bulletin's standing diagnosis flags as the bottleneck for
any push past the per-mode architectural ceiling) admits a tightening
on V68's eleven-window ρ-band when the eq (8) bridge parameter `α`
(in `a := ω₀^α`) is varied over a finer grid than has been swept
previously. Produce a falsifiable Scratch witness with an explicit
`DECISION:` line — either (GO) a per-window α-choice that tightens
the integrand `scalarIntegrand_*(c, Λ_α(c, ρ), ρ)` enough to push the
joint mass above `1 + 10^(-4)` at some `c_new > 71313/200000`, or
(NO-GO) a documented insensitivity / monotonicity result confirming
that no α in the swept grid improves on V68's bridge choice.

The move uses neither equation `(15)` nor any new oracle. It is a
pure Phase 0 numerical sweep whose output is one of two falsifiable
DECISION lines.

## Why

Sprint 093 falsified Slack 1 (the inner-kernel sup-relaxation step is
attained with equality on the eq (4) admissible cone — the
single-mode-at-argmax saturator pins R = 1 exactly at every V68
window). Slack 1 is therefore not a viable c-push direction without a
new paper-faithful constraint on the η-distribution, which would be
a trust-surface expansion. The remaining viable structural slacks
listed in the 2026-05-05 directive are:

- **Slack 3** (this sprint): outer kernel `Λ(c, ρ)` — *boundary*
  control, not inner. The standing auto-memory diagnosis is that
  **the inner kernel is optimal** (sprint 091's exhaustion sweep +
  sprint 093's saturator confirmation) **and the bottleneck for any
  push past the per-mode architectural ceiling is outer control**.
  A 1% reduction in `Λ` on the dominant ρ-band translates to roughly
  `+10^(-3)` in c — three orders of magnitude above V68's `+10^(-6)`
  uplift over V67.
- Slack 5 (Σ⁺ vs Σ⁻ asymmetry, signed-η regime, eq (4) non-trivial)
  and Slack 2 (per-k cross-coupling lift, sprint 077's chain into
  Lean) remain on the planner's queue if Slack 3 returns NO-GO.

Slack 3 is preferred for this sprint over Slack 5 / Slack 2 because:

1. **Distinct lever, untested at V68's c.** Slack 3 attacks `Λ(c, ρ)`,
   not `H_j(c, ρ)`. Sprint 093's saturator argument is a statement
   about the inner per-mode kernel only — it carries zero information
   about the outer/boundary kernel. The two kernels combine
   multiplicatively in the scalar integrand
   `scalarIntegrand_w(c, Λ, ρ) := mass_density_w(c, ρ) / Λ(c, ρ)`, so
   any tightening of `Λ` propagates directly to the joint mass.
2. **Sprint 077's α-grid was coarse on the per-k chain and
   not on Λ.** Sprint 077 swept α on the per-k cross-coupling lift
   identity (a different chain, exited V54's contraction regime).
   Sprint 077's α-grid was structured (`{0.1, 0.2, …, 0.9}` plus
   structured-`α_h` extensions) and on the wrong kernel — there has
   been **no fine α-sweep on the eq (8) bridge that produces `Λ`**,
   at any c, ever. The Bulletin §B Slack 3 bullet explicitly flags
   "**The α-grid was coarse**" as the open question.
3. **Clean Phase 0 falsifier.** Either some α in the grid yields a
   pointwise lower `Λ_α(c, ρ)` than V68's choice (and the c-push
   integrates), or the Λ-curve is locally α-flat / α-monotone at
   V68's c-band (Slack 3 falsified). NO-GO is a well-defined
   structural fact, not an artefact of inadequate gridding.
4. **The numerical surface is small.** V68 has eleven windows; the
   α-grid in the Bulletin §B Slack 3 has ten points. The full sweep
   is `11 × 10 = 110` `Λ_α(c, ρ)` evaluations per c, plus a c-sweep
   under the best per-window α. At `mpmath dps=40` for the bulk
   sweep + `dps=80` for the chosen `c_new` re-verification, this is
   a single-generator-session probe.

If the probe falsifies Slack 3 (Λ-curve is α-flat or α-pessimal at
V68's c-band on the relevant windows), the result is documented and
the planner pivots to Slack 5 (Σ⁺ vs Σ⁻ asymmetry) or Slack 2 (per-k
cross-coupling Lean derivation) in sprint 095. Either way, this
sprint costs ~1 generator session and produces an unambiguous
decision.

## Concrete edits expected

- `Scratch/sprint_094_slack3_lambda_alpha_sweep.py`
  (~400-700 lines): a Phase 0 sweep script that
  - **Defines V68's eleven windows** by their canonical sqrt-pinned
    τ-breakpoints plus the Branch.one residual box, exactly as in
    sprint 091's witness file
    `Scratch/sprint_091_witness.txt`. Window endpoints (use the
    rationals that match V68's `v68ElevenWindowStart` /
    `v68ElevenWindowStop` defs in `Proof/Reduction.lean`):
        i = 0  Branch.one  [c·(1 + 10⁻⁹), c·sqrt(121/120)]
        i = 1  modeJ 10    [c·sqrt(121/120), c·sqrt(100/99)]
        i = 2  modeJ 9     [c·sqrt(100/99), c·sqrt(81/80)]
        ...
        i = 10 modeJ 1     [c·sqrt(9/8),  999999/1000000]
    Endpoints are exact rationals via the canonical
    `c²/ρ² = τ_j = 1 - 1/(j+1)²` recipe, identical to sprint 091's
    sweep.
  - **Imports** `Numerical_Library.rigorous_scalar` and uses
    `_lambda_from_k_upper`, `k_upper_at_point`, `k_upper_on_interval`
    as the **baseline** Λ values. Reads V68's c (`71313/200000`)
    from a top-of-file constant.
  - **Defines a parametric Λ-family.** Wang's eq (8) introduces a
    bridge parameter `α` via `a := ω₀^α` where `ω₀ := c / ρ` (the
    paper's auxiliary multiplier) and the bridge inequality is
    `Σ⁻(ρ) ≤ ω₀^(2α) · liftGap(ρ; a)`. The induced upper bound on
    the scalar integrand uses `Λ_α(c, ρ)` where the α-dependent
    weighting modifies the K-product. Construct the α-parametric
    `Λ_α(c, ρ)` via the explicit formula (the script must derive
    the α-dependence from Wang 2025 eq (8) by reading the
    `paperLambda K c ρ` definition — see
    `KorenblumPaper.WangPaperSideConditions` and Wang's 2011 annulus
    pseudodistance — and document the derivation inline in a top-of-
    file comment of ~30-50 lines).

    **If** the script's author cannot derive a closed-form `Λ_α(c, ρ)`
    purely from the existing trusted Lean+paper surface (i.e. without
    introducing a new paper field), the contract permits the
    **alternative probe shape** described in §"Alternative probe
    shape" below.
  - **Sweeps α** on the Bulletin §B Slack 3 grid:
    `α ∈ {0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.5, 1.0}`
    (ten points). For each α and each of V68's eleven windows, compute
    the per-window mass-density integral
        m_w(c, α) := ∫ scalarIntegrand_w(c, Λ_α(c, ρ), ρ) dρ
    over the window's ρ-range, at `mpmath dps=40, n_trunc=120`.
  - **Reports the per-window α-sensitivity table.** Columns: window
    index, kind, `m_w(α=baseline)` (V68's α-choice — record the V68
    bridge α for reference), `m_w(α_min)` for the minimizing α in
    the grid, `Δm_w := m_w(α_min) - m_w(baseline)`, and the
    α-argmin per window.
  - **If any window has `Δm_w > 0`** (i.e. α-tightening is positive
    on at least one window), recompute the joint mass `Σ_w m_w(c,
    α_w*)` with α chosen *per-window* (the joint mass is additive in
    windows, so per-window α-choice is admissible). Report the
    joint-mass margin at V68's c under the per-window-best α-vector.
  - **Sweeps c upward** under the per-window-best α-vector to find
    the largest `c_new` with margin `≥ 10^(-4)`. Report the c-ceiling
    and the per-window α-vector that achieves it. Re-verify the
    final `c_new` at `mpmath dps=80, n_trunc=300`.
  - **Emits a DECISION line** at the end of stdout, in one of the
    two prescribed formats:
        DECISION: GO with c_new = <fraction>, target +<delta>e-N margin <margin>
        DECISION: NO-GO — Slack 3 falsified, structural reason: <one-line>
    Examples of NO-GO structural reasons:
      * "Λ_α(c, ρ) is α-monotone-non-decreasing on every V68 window
        at α ∈ [0.01, 1.0]; baseline α minimizes Λ"
      * "Per-window α-tightening is non-zero but joint-mass margin at
        c_new = 71313/200000 + 1e-6 is +9.x e-5 < 1e-4"
      * "α-derivative of `Λ_α(c, ρ)` vanishes to numerical precision
        on the dominant mode-1 window — Λ is α-stationary at V68's
        c-band"
  - Uses `mpmath` at `dps ∈ {40, 80}` (40 for the bulk sweep, 80
    for the final re-verification at the chosen `c_new`).
- `Scratch/sprint_094_slack3_lambda_alpha_sweep.txt`
  (~150-300 lines): captured stdout including the per-window
  α-sensitivity table, the α-argmin per window, the joint-mass
  margin at V68's c under per-window-best α, the c-sweep table,
  and the DECISION line.
- `Scratch/sprint_094_witness.txt` (~30-80 lines): if GO, the
  per-window α-vector and chosen `c_new` in a format ready for
  sprint 095 to consume; if NO-GO, a structural memo summarizing
  the falsification (which window's Λ is α-stationary, what the
  α-derivative magnitude is, why the bridge parameter cannot be
  tuned to tighten Λ at V68's c-band).
- `Experience.md`: append a "Sprint 094 — …" subsection summarizing
  the DECISION, the falsifying or supporting evidence, and the
  forward direction (sprint 095 either ships GO via a Lean
  derivation that lifts the per-window α-vector into a candidate-
  facing `Λ_α` definition, or pivots to Slack 5 / Slack 2 with the
  lessons recorded).
- `Bulletin.md`: append one row per the standard pattern
  (`sprint_094 PASS|FAIL: …`).

No Lean files modified. No `Numerical_Library` wrappers added (this is
a pure Scratch sweep that *reads* `rigorous_scalar.py` helpers, never
extends them). No `lemma.toml` edits. No proposals filed (per the
2026-05-05 human directive Section C and the 2026-05-05 planner
instruction "Do not file proposals").

### Alternative probe shape

If the sprint author determines that a closed-form `Λ_α(c, ρ)` cannot
be derived from the existing trusted Lean+paper surface without
introducing a new paper field (e.g. eq (8)'s α appears only as a
hidden quantifier inside Wang 2011's annulus pseudodistance and is
not directly exposed), the script may instead probe **K-tightening**
directly: for each window, evaluate `K(c, ρ)` at multiple sub-window
points (rather than the worst-case point currently used by
`k_upper_on_interval`) and verify whether a tighter pointwise
`K_w(c, ρ) ≤ K(c, ρ)` is admissible on the integration sub-interval
via Schur-test or Hölder reasoning. The DECISION line shape is
unchanged; the structural reason on NO-GO would name the K-bound
saturator instead of the α-stationary point.

### Numerical guardrails

- Use `mp.workdps(40)` for the bulk sweep, `mp.workdps(80)` for the
  final re-verification at chosen `c_new`.
- Guard against `Λ_α(c, ρ) ≤ 0` (numerically meaningless): if the
  α-formula produces a non-positive `Λ_α`, skip that (α, window) pair
  and log it.
- Guard against `n_trunc` truncation error — verify that the per-
  window mass at `n_trunc=120` and `n_trunc=300` agree to
  `≤ 10^(-12)` before drawing the DECISION.
- Use exact `Fraction` rationals for window endpoints; convert to
  `mpf` only inside `mp.quad` integrand evaluations.

## Acceptance criteria

1. `Scratch/sprint_094_slack3_lambda_alpha_sweep.py` runs end-to-end
   without errors at `dps = 40` for the bulk sweep and `dps = 80` for
   any chosen `c_new` re-verification (or `dps = 80` for one
   representative window if the DECISION is NO-GO and no `c_new` is
   chosen).
2. The captured stdout `.txt` file contains:
   - the eleven-window endpoint table (one row per window, exact
     rational endpoints);
   - the ten-α grid sensitivity table (ten α values × eleven windows
     = up to 110 cells of `Δm_w(α) := m_w(c, α) - m_w(c, baseline)`);
   - the per-window α-argmin (one row per window);
   - either (GO) the joint-mass margin at V68's c under per-window-
     best α, plus a c-sweep table showing the largest `c_new >
     71313/200000` with margin `≥ 10^(-4)`, **or** (NO-GO) a
     numerical fact (α-derivative magnitude, K-saturator location,
     or joint-mass margin at `c = c_v68 + 10^(-6)` under per-window-
     best α showing it is `< 10^(-4)`) demonstrating that Slack 3
     does not yield a c-push;
   - a final `DECISION:` line in one of the two prescribed formats.
3. The `witness.txt` file's content matches the DECISION line: GO →
   contains the per-window α-vector and `c_new`; NO-GO → contains
   the structural-reason memo.
4. `Experience.md` and `Bulletin.md` each gain one row per the
   standard pattern.
5. No edits to `Candidates/`, `Proof/`, `KorenblumPaper/`,
   `Numerical_Library/`, `lemma.toml`, or `Proposals/`.

The sprint is **PASS** in either DECISION outcome — both the GO and
NO-GO branches discharge the contract. The score gate is *not*
applicable this sprint (no Lean candidate ships); the value is the
falsifiable witness.

## Out of scope

- Edit older candidates, `Candidates/V68.lean`, or any
  derived-theorem file under `Candidates/Vk/` for any `k`.
- Change the final theorem statement.
- Add a free-floating new axiom or oracle.
- Modify `Numerical_Library/rigorous_scalar.py` (the existing
  `lambda_upper_on_interval` and `k_upper_on_interval` helpers are
  read but not extended — extending them, if warranted by the GO
  branch, is sprint 095's task).
- Modify `KorenblumPaper/` (read-only).
- File a `Proposals/` entry. (Per Section C of the 2026-05-05 human
  directive and the 2026-05-05 planner instruction. If the GO branch
  triggers and a Lean derivation is needed, sprint 095 may file a
  proposal at that point — not this sprint.)
- Lift any of this sprint's content into a Lean per-candidate
  derived-theorem file — that is sprint 095's task if this sprint
  emits GO.
- Sweep over architectures other than V68's eleven-window split. The
  Λ-tightening is on the same windows V68 already uses; the point is
  to replace V68's α-baseline with a finer per-window α-choice on
  each existing window, not to repartition.
- Probe Slack 1 (sprint 093 already falsified it), Slack 5, or Slack 2
  in this sprint. One slack per sprint per the 2026-05-05 directive
  Section C (3).

## Time budget

≤ 60 minutes runtime for the Scratch sweep
(~6-12 minutes of `mpmath dps=40` bulk α×window sweep at `n_trunc=120`,
+ ~2-4 minutes of `dps=80` re-verification, in line with sprint 089's,
sprint 091's, and sprint 093's wall-clock profiles).

≤ 1 generator session (~2-3 hours including derivation of the α-form
of Λ, scripting, sweep runtime, witness drafting, and Bulletin/
Experience append).

## Stop conditions

- DECISION GO emitted with witness file populated:
  `STATUS=READY_FOR_EVALUATION` (the evaluator will Pass/Fail-no-Lean
  in the standard "Phase 0 sprint" pattern of sprints 077, 087, 089,
  091, 093).
- DECISION NO-GO emitted with structural-reason memo:
  `STATUS=READY_FOR_EVALUATION` (same pattern; NO-GO is a valid
  Phase 0 outcome and the sprint is still PASS).
- Phase 0 sweep crashes / cannot produce a DECISION line:
  `STATUS=BLOCKED` with the exact failure (e.g. mpmath precision
  inadequate, α-form of Λ ill-defined for some α, or the script
  cannot derive a closed-form `Λ_α(c, ρ)` from the existing trusted
  surface and the alternative K-tightening probe is also infeasible).
- Phase 0 sweep produces an ambiguous result (e.g. per-window α-best
  yields joint margin in the range `[5e-5, 1e-4]` — strictly
  positive but below the contract floor at any candidate `c_new`):
  `STATUS=BLOCKED` with the ambiguity documented and the planner
  asked to pick a clearer acceptance threshold (or to consider whether
  a relaxed `1e-5`-margin push is admissible at this point in the
  project lifecycle).
- Trust expansion needed (the α-form of Λ requires a new paper field):
  `STATUS=BLOCKED_NEEDS_HUMAN`. Note: this should not occur for the
  K-tightening alternative probe shape, which uses only existing
  `Numerical_Library` helpers.
