# Sprint 095: Phase 0 probe — Slack 5 Σ⁺ vs Σ⁻ asymmetry in the signed-η regime where eq(4) is non-trivial

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`)
**Target file**: `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.{py,txt,witness.txt}` (no Lean changes this sprint)
**Direction**: raise-c (Phase 0 only, structural — Slack 5 attacks the inner-disk Σ⁺ vs Σ⁻ asymmetry on the signed-η admissible cone, distinct from Slacks 1/3 which attack the inner per-mode kernel and the outer paper kernel respectively)

## Goal

Numerically probe whether the inner-disk per-mode kernel admits a
strict reduction `R(c, ρ; (a, b)) ≤ γ < 1` uniformly over the signed-η
admissible cone — the (a, b)-cone where some `η_j := |b_j|² − |a_j|²`
are positive and some negative, with `Σ⁺(c) := Σ_{η_j < 0} (−η_j) c^(2j+2)`
and `Σ⁻(c) := Σ_{η_j > 0} η_j c^(2j+2)` both strictly positive and
satisfying eq(4)'s binding constraint `Σ⁺(c) ≤ Σ⁻(c)`. Sprint 093
falsified Slack 1 by exhibiting the all-non-negative single-mode
argmax saturator (η_j ≥ 0 ∀ j, eq(4) trivially `0 ≤ Σ⁻(c)`); in that
unsigned cone R = 1 is attained. Slack 5's hypothesis is that this
saturator is *not admissible* in the signed-η regime when eq(4) binds
non-trivially — and that a strict gap `1 − R ≥ γ > 0` is available on
the signed cone.

The move uses neither equation `(15)` nor any new oracle. It is a pure
Phase 0 numerical sweep whose output is one of two falsifiable
DECISION lines:

- (GO) Signed-η admissible distributions exhibit a strict per-window
  envelope `Σ_j p_j H_j(c, ρ) ≤ γ_w · sup_j H_j(c, ρ)` with
  `γ_w < 1` uniformly across V68's eleven windows, large enough to
  push the joint mass above `1 + 10^(-4)` at some `c_new > 71313/200000`.
- (NO-GO) The signed-η cone admits a configuration that achieves
  `R(c, ρ; (a, b)) ≥ 1 − ε` for arbitrary `ε > 0` on at least one
  V68 window, falsifying the strict-asymmetry hypothesis.

## Why

The 2026-05-05 directive Section B identifies five sources of slack in
the architectural ceiling at `c ≈ 0.356565`. Sprints 093 and 094 have
falsified Slacks 1 and 3:

- Slack 1 (sprint 093 NO-GO): single-mode argmax saturator η_j = δ_{j, j*(ρ)}
  with all-non-negative coefficients pins R = 1; eq(4) `Σ⁺(c) ≤ Σ⁻(c)`
  is trivially `0 ≤ Σ⁻(c)` on this cone and provides no constraint.
- Slack 3 (sprint 094 NO-GO): the eq(8) bridge α-parametric Λ_α
  tightening requires the unstated Σ⁻ → Λ propagation through Wang
  2011's annulus pseudodistance; K is already at machine precision.

Both falsifications confirm the standing diagnosis: the inner kernel
H_j(c, ρ) and outer kernel Λ(c, ρ) are *both* optimal at the existing
trust surface. The only remaining structural slacks the directive
flags are Slack 2 (per-k cross-coupling lift, sprint 077's chain) and
Slack 5 (Σ⁺ vs Σ⁻ asymmetry, this sprint).

Slack 5 is preferred for this sprint over Slack 2 because:

1. **Sprint 077's data already strongly evidences Slack 2 NO-GO.**
   Sprint 077's per-k α-varying kernel sweep at c = 0.35645
   (V52, ε = 7.15e-4 *below* V68's c) reports kernel margin uniformly
   `≈ −0.86 to −0.99` across all α-families and all canonical
   extremals E1–E5 in the contraction regime |α(k)| < 1. The only
   positive witness exits the contraction regime to |α(k)| > 1 where
   the V54 `lift_identity_per_k_rearranged` chain breaks (the
   structurally-trivial sign flip flagged in `Scratch/sprint_077_witness.txt`).
   Pushing the c-axis from 0.35645 to 0.356565 (+1.15e-4, smaller
   than the slope's noise floor) is mathematically unlikely to
   reverse a uniform −90% margin. Slack 2 is effectively settled by
   sprint 077; re-running at V68's c would mostly confirm.

2. **Slack 5 is structurally untouched.** Sprint 040's downstream
   consumer of `Σ⁺(c)` (the integrated `c² · Σ⁺(c)` route) and
   sprint 044's per-k integrated `Σ⁺_int(c)` route both *use* Σ⁺ as
   a target, but neither probes whether the Σ⁺/Σ⁻ asymmetry alone
   reduces R strictly below 1 on the signed cone. Sprint 093's
   single-mode argmax saturator only probes the unsigned cone where
   eq(4) is trivial. The signed cone has never been swept.

3. **Eq(4) is non-trivial in the signed regime.** When `Σ⁻(c) > 0`
   (some η_j > 0) AND `Σ⁺(c) > 0` (some η_j < 0), the constraint
   `Σ⁺(c) ≤ Σ⁻(c)` *binds*: it forces a balance between negative-η
   modes (which contribute to Σ⁺) and positive-η modes (which
   contribute to Σ⁻), and the `c^(2j+2)` weighting means the
   binding is mode-dependent. A configuration that excites mode j
   negatively and mode j+1 positively must satisfy
   `c^(2j+2) ≤ c^(2j+4)` weighted comparison — a non-trivial
   geometric constraint on the relative magnitudes.

4. **Clean Phase 0 falsifier.** Either signed-η admissible
   distributions (those satisfying eq(4) with binding) yield a
   strict `R ≤ γ < 1` envelope on V68's windows (and the c-push
   integrates), or a signed-η near-saturator achieves R → 1
   (Slack 5 falsified).

5. **The numerical surface is small.** V68 has eleven windows; the
   signed-η probe is parametrized by a small set of admissible
   distributions (e.g. mode-j negative + mode-(j+δ) positive with
   eq(4)-binding ratios) — concretely `O(10²)` distributions across
   `j ∈ {1, …, 10}`, `δ ∈ {1, 2, 3}`, and a handful of magnitudes —
   times eleven windows = a single-generator-session probe.

If the probe falsifies Slack 5 (a signed-η near-saturator achieves
R → 1 on at least one V68 window), the result is documented and the
planner pivots to one of the score-neutral options (Slack 4
trust-surface compaction, Wang Lemma 2 / Fourier orthogonality
derived theorem, or hoisting V53–V68 derived theorems to `Proof/`)
or to a fresh non-slack direction. Either way, this sprint costs ~1
generator session and produces an unambiguous decision.

## Concrete edits expected

- `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.py`
  (~400-700 lines): a Phase 0 sweep script that

  - **Defines V68's eleven windows** by their canonical
    sqrt-pinned τ-breakpoints plus the Branch.one residual box,
    exactly as in sprint 091's, sprint 093's, and sprint 094's
    witness files. Window endpoints (use the rationals that match
    V68's `v68ElevenWindowStart` / `v68ElevenWindowStop` defs in
    `Proof/Reduction.lean`):
        i = 0  Branch.one  [c·(1 + 10⁻⁹), c·sqrt(121/120)]
        i = 1  modeJ 10    [c·sqrt(121/120), c·sqrt(100/99)]
        i = 2  modeJ 9     [c·sqrt(100/99), c·sqrt(81/80)]
        ...
        i = 10 modeJ 1     [c·sqrt(9/8), 999999/1000000]
    Endpoints are exact rationals via the canonical
    `c²/ρ² = τ_j = 1 − 1/(j+1)²` recipe.

  - **Defines the signed-η admissible cone** parametrically. Take a
    finite truncation `K = 20` (matches sprint 077's K_TRUNC). For
    each pair `(j_minus, j_plus)` with `j_minus < j_plus ≤ K−1`
    and a magnitude parameter `s ∈ (0, 1]`, construct the η-vector

        η_{j_minus} := −s · c^(−2 j_minus − 2)   (negative; contributes to Σ⁺)
        η_{j_plus}  := +s · c^(−2 j_plus  − 2)   (positive; contributes to Σ⁻)
        η_j         := 0   for j ∉ {j_minus, j_plus}

    Verify that this configuration satisfies eq(4):
        Σ⁺(c) = s · c^(−2 j_minus − 2) · c^(2 j_minus + 2) = s
        Σ⁻(c) = s · c^(−2 j_plus  − 2) · c^(2 j_plus  + 2) = s
    so eq(4) `Σ⁺(c) ≤ Σ⁻(c)` is `s ≤ s`, binding with equality.
    This is the **two-mode binding-eq(4) family**, the simplest
    signed-η configuration where eq(4) is non-trivial.

    Sweep `j_minus ∈ {0, 1, 2, 3, 4, 5}`,
    `j_plus  ∈ {j_minus + 1, …, min(j_minus + 5, K − 1)}`,
    `s ∈ {1.0}` (the magnitude doesn't matter for R since R is
    homogeneous of degree 0 in η; record one value as a sanity
    check then fix s = 1).

    **Also sweep a three-mode cone** for breadth: pairs
    `(j_minus, j_plus, j_plus2)` with two positive modes balancing
    one negative mode at eq(4) binding. Weight-balance:
        η_{j_minus} := −1
        η_{j_plus}  := +λ · c^(−2 j_plus  − 2 + 2 j_minus + 2)
        η_{j_plus2} := +(1 − λ) · c^(−2 j_plus2 − 2 + 2 j_minus + 2)
    with `λ ∈ {0.25, 0.5, 0.75}`, ensuring `Σ⁺(c) = Σ⁻(c)` at
    binding. Sweep `j_minus ∈ {0, 1, 2}`,
    `(j_plus, j_plus2)` from `{(j_minus + 1, j_minus + 3),
    (j_minus + 2, j_minus + 4)}`.

    The total sweep size is `O(80)` η-vectors × 11 windows
    `≈ 880` evaluations of `R(c, ρ; η)`. At `mpmath dps=40,
    n_trunc=120`, well within budget.

  - **Defines the signed-η R-quantity.** For each η-vector and each
    V68 window, evaluate at multiple ρ-points inside the window
    (use the window's left endpoint, midpoint, and right endpoint
    plus three `mp.quad`-style Gauss-Legendre nodes — six points
    per window) the ratio

        R(c, ρ; η) := Σ_j p_j(ρ) H_j(c, ρ)  /  sup_j H_j(c, ρ)

    where
        p_j(ρ) := η_j · ρ^(2j) / Σ⁻_pointwise(ρ)
        Σ⁻_pointwise(ρ) := Σ_{η_j > 0} η_j · ρ^(2j)
        H_j(c, ρ) := (j / (j+1)) · c^(2j+2) / ρ^(2j)

    Note the asymmetry: `p_j(ρ) ≥ 0` for j with η_j > 0, and
    `p_j(ρ) ≤ 0` for j with η_j < 0; the convex relaxation at the
    heart of Slack 1 only sees the positive-η contributions, but
    the actual per-mode bound also includes the negative-η piece
    on the other side (via `circleGap = Σ⁺ − Σ⁻`). The script must
    document explicitly which "R" formula it is computing — there
    are at least two natural choices:

      (R-conv) The convex relaxation R as in sprint 093 (only
      positive-η modes contribute to the convex combination,
      negative-η modes are absorbed elsewhere); R-conv ≤ 1 always,
      and Slack 5 GO requires R-conv ≤ γ < 1 strictly.

      (R-full) The full per-mode envelope including both signs,
      computed via the `circleGap = Σ⁺ − Σ⁻` decomposition; this
      may be < 1 by a different mechanism even when R-conv = 1.

    The script runs **both** R-conv and R-full and reports both
    columns. The DECISION line specifies which R is the binding one.

  - **Reports the per-window R-table.** Columns: window index, kind,
    η-vector signature (compact representation, e.g.
    `(j_-=0, j_+=1, s=1.0)`), R-conv max over the six ρ-points
    inside the window, R-full max over the six ρ-points, eq(4)
    binding margin (should be ≤ 1e-12 since we engineered it).

  - **Reports the per-window R-supremum across the η-sweep.** Columns:
    window index, kind, sup_R-conv (over all swept η), sup_R-full,
    argmax η-vector. If sup_R-conv < 1 with γ_w := 1 − sup_R-conv
    ≥ 1e-3 uniformly across the eleven windows, that is the GO
    branch's per-window envelope reduction.

  - **If GO**, project `γ_w` (per-window envelope reduction) into a
    candidate joint-mass margin at V68's c, then sweep c upward to
    find the largest `c_new` with margin `≥ 10^(-4)` under the
    reduced kernel. Re-verify the final `c_new` at `mpmath dps=80,
    n_trunc=300`.

  - **If NO-GO**, identify the η-vector that achieves R ≥ 1 − ε for
    smallest ε on the most permissive window. Document the
    structural reason: e.g. "two-mode signed-η cone admits a
    near-saturator with R → 1 as `j_minus → j_plus − 1` and the
    weights concentrate at the argmax mode". Confirm at higher
    precision (dps=80) on the worst-case (η, ρ).

  - **Emits a DECISION line** at the end of stdout, in one of the
    two prescribed formats:
        DECISION: GO with c_new = <fraction>, target +<delta>e-N margin <margin>, γ_w = <vector>
        DECISION: NO-GO — Slack 5 falsified, structural reason: <one-line>
    Examples of NO-GO structural reasons:
      * "Two-mode signed-η near-saturator (j_minus = K−2, j_plus = K−1)
        achieves R-conv → 1 as the support concentrates at the argmax,
        eq(4) binding does not exclude the limit"
      * "Three-mode signed-η balanced configuration achieves
        R-full ≥ 0.999 on window i = 10 (mode-1 dominant), Slack 5
        envelope reduction below the 10^(-3) threshold"
      * "R-conv saturates at 1 on every window when η is concentrated
        at a single positive mode at the argmax (sprint 093's
        all-non-negative single-mode argmax saturator is a limiting
        case of the signed-η two-mode family, j_minus → −∞)"

  - Uses `mpmath` at `dps ∈ {40, 80}` (40 for the bulk sweep, 80
    for the final re-verification at chosen `c_new` or worst-case
    near-saturator).

- `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.txt`
  (~150-300 lines): captured stdout including the eleven-window
  endpoint table, the per-window R-table for both R-conv and R-full
  across the swept η-vectors, the per-window R-supremum, eq(4)
  binding margins, the c-sweep table (GO) or worst-case near-saturator
  identification (NO-GO), and the final `DECISION:` line.

- `Scratch/sprint_095_witness.txt` (~30-80 lines): if GO, the per-window
  envelope reductions `γ_w` and chosen `c_new` in a format ready for
  sprint 096 to consume; if NO-GO, a structural memo summarizing the
  falsification (which η-family achieves R → 1, on which window, why
  eq(4) does not exclude the limit, what additional paper-faithful
  constraint would be required to close it, and the implication for
  the remaining slacks).

- `Experience.md`: append a "Sprint 095 — …" subsection summarizing
  the DECISION, the falsifying or supporting evidence, and the
  forward direction (sprint 096 either ships GO via a Lean derivation
  that lifts the per-window γ_w envelope into a candidate-facing
  reducer, or pivots to score-neutral cleanup with the lessons
  recorded).

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_095 PASS|FAIL: …`).

No Lean files modified. No `Numerical_Library` wrappers added (this is
a pure Scratch sweep that *reads* `rigorous_scalar.py` helpers — for
H_j, paperLambda, n_trunc=120 conventions — never extends them). No
`lemma.toml` edits. No proposals filed (per the 2026-05-05 human
directive Section C and the 2026-05-05 planner instruction "Do not
file proposals").

### Numerical guardrails

- Use `mp.workdps(40)` for the bulk sweep, `mp.workdps(80)` for the
  final re-verification at chosen `c_new` (GO) or worst-case
  near-saturator (NO-GO).
- Guard against `Σ⁻_pointwise(ρ) = 0` (numerically meaningless): if
  the η-vector has no positive coefficients, skip that vector and
  log it. Skip if `Σ⁻_pointwise(ρ) < 10^(−40)` at the test point
  (numerical precision floor).
- Verify `Σ⁺(c) ≤ Σ⁻(c)` holds with margin ≤ `10^(-30)` (i.e. eq(4)
  is binding to numerical zero by construction); if not, log the
  vector and skip — the script's η-engineering is meant to produce
  binding-eq(4) configurations.
- Guard against `n_trunc` truncation error — verify that the
  per-window R at `n_trunc=120` and `n_trunc=300` agree to
  `≤ 10^(-12)` before drawing the DECISION.
- Use exact `Fraction` rationals for window endpoints; convert to
  `mpf` only inside `mp.quad` integrand evaluations and inside the
  `R(c, ρ; η)` evaluation.
- Document explicitly which "R" (R-conv or R-full) the DECISION line
  is binding on, since the two definitions can disagree.

## Acceptance criteria

1. `Scratch/sprint_095_slack5_signed_eta_sigma_asymmetry.py` runs
   end-to-end without errors at `dps = 40` for the bulk sweep and
   `dps = 80` for any chosen `c_new` re-verification (GO) or
   worst-case near-saturator confirmation (NO-GO).
2. The captured stdout `.txt` file contains:
   - the eleven-window endpoint table (one row per window, exact
     rational endpoints);
   - the η-sweep summary (count of two-mode and three-mode signed-η
     vectors swept, sample of representative vectors);
   - the per-window R-table (for both R-conv and R-full across the
     swept η-vectors, eq(4) binding margins);
   - the per-window R-supremum and argmax η-vector;
   - either (GO) the per-window envelope reduction `γ_w := 1 − sup_R`,
     a c-sweep table showing the largest `c_new > 71313/200000` with
     margin `≥ 10^(-4)` under the reduced kernel, **or** (NO-GO) the
     identified near-saturator η-vector achieving R → 1 on the worst
     window, plus a structural memo;
   - a final `DECISION:` line in one of the two prescribed formats,
     specifying explicitly which R (R-conv or R-full) is binding.
3. The `witness.txt` file's content matches the DECISION line: GO →
   contains the per-window γ_w vector and `c_new`; NO-GO → contains
   the structural-reason memo with the near-saturator η-vector,
   the worst-case window, the limit R-value, and the implication
   for remaining slacks.
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
  helpers are read but not extended — extending them, if warranted
  by the GO branch, is sprint 096's task).
- Modify `KorenblumPaper/` (read-only).
- File a `Proposals/` entry. (Per Section C of the 2026-05-05 human
  directive and the 2026-05-05 planner instruction. If the GO branch
  triggers and a Lean derivation requires a new paper field, sprint
  096 may file a proposal at that point — not this sprint.)
- Lift any of this sprint's content into a Lean per-candidate
  derived-theorem file — that is sprint 096's task if this sprint
  emits GO.
- Sweep over architectures other than V68's eleven-window split. The
  Σ⁺/Σ⁻ asymmetry probe is on the same windows V68 already uses.
- Probe Slack 1 (sprint 093 already falsified it), Slack 3 (sprint 094
  already falsified it), Slack 2 (sprint 077 already strongly
  evidenced NO-GO at lower c), or Slack 4 (score-neutral, separate
  sprint). One slack per sprint per the 2026-05-05 directive Section
  C (3).
- Probe non-binding-eq(4) signed-η configurations. Eq(4) binding is
  the structural assumption of Slack 5; non-binding configurations
  fall back to Slack 1 (which sprint 093 already settled). The point
  is to test whether eq(4) binding *adds* a strict R-reduction, not
  to revisit the unsigned cone.

## Time budget

≤ 60 minutes runtime for the Scratch sweep
(~5-10 minutes of `mpmath dps=40` bulk η × window sweep at
`n_trunc=120`, + ~2-4 minutes of `dps=80` re-verification, in line
with sprint 089's, sprint 091's, sprint 093's, and sprint 094's
wall-clock profiles).

≤ 1 generator session (~2-3 hours including η-family construction,
scripting, sweep runtime, witness drafting, and Bulletin/Experience
append).

## Stop conditions

- DECISION GO emitted with witness file populated:
  `STATUS=READY_FOR_EVALUATION` (the evaluator will Pass/Fail-no-Lean
  in the standard "Phase 0 sprint" pattern of sprints 077, 087, 089,
  091, 093, 094).
- DECISION NO-GO emitted with structural-reason memo and
  near-saturator η-vector identified:
  `STATUS=READY_FOR_EVALUATION` (same pattern; NO-GO is a valid
  Phase 0 outcome and the sprint is still PASS).
- Phase 0 sweep crashes / cannot produce a DECISION line:
  `STATUS=BLOCKED` with the exact failure (e.g. mpmath precision
  inadequate for the η-engineering, eq(4) binding cannot be
  reliably enforced numerically, or R-conv vs R-full disagree
  pathologically and neither admits a clean DECISION).
- Phase 0 sweep produces an ambiguous result (e.g. per-window γ_w
  yields joint margin in the range `[5e-5, 1e-4]` — strictly
  positive but below the contract floor at any candidate `c_new`):
  `STATUS=BLOCKED` with the ambiguity documented and the planner
  asked to pick a clearer acceptance threshold (or to consider whether
  a relaxed `1e-5`-margin push is admissible at this point in the
  project lifecycle).
- Trust expansion needed (the signed-η cone with binding eq(4)
  requires a new paper field to specify, e.g. a third constraint
  beyond eq(4) and the H² hypothesis):
  `STATUS=BLOCKED_NEEDS_HUMAN`. Note: this should not occur for the
  Phase 0 numerical sweep, which only requires the existing
  `Section2Assumptions` fields plus the algebraic decomposition
  `circleGap = Σ⁺ − Σ⁻` already established by sprint 027.
