# Sprint 093: Phase 0 probe — Slack 1 (convex relaxation) two-moment envelope at V68's c

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`)
**Target file**: `Scratch/sprint_093_slack1_two_moment_envelope.{py,txt,witness.txt}` (no Lean changes this sprint)
**Direction**: raise-c (Phase 0 only, structural)

## Goal

Numerically probe whether the per-mode kernel's sup-relaxation step
`Σ_j p_j(ρ) · H_j(c, ρ) ≤ sup_j H_j(c, ρ)` (Bulletin Slack 1) is loose
enough on V68's eleven-window ρ-band to support a c-push, and if so,
characterize a **two-moment** envelope `H_*(m₁(p), m₂(p), c, ρ)` that is
both ≥ Σ_j p_j H_j and strictly below sup_j H_j on the dominant
mode-1/mode-2 windows. Produce a falsifiable Scratch witness with an
explicit DECISION line (GO with target c, or NO-GO with the structural
reason).

The move uses neither equation `(15)` nor any new oracle. It is a
diagnostic Phase 0 sweep whose output is either (a) a concrete
two-moment envelope and target `c_new` for a follow-up Lean sprint, or
(b) a documented falsification that demotes Slack 1 below Slacks 2/3/5.

## Why

V68 sits at the eleven-window architecture's c-ceiling
(`71313/200000`). Sprint 091's adaptive sweep along three architectural
axes was exhaustive; the c-push surface is genuinely exhausted at the
seven/eight/eleven-window design level. Per the 2026-05-05 human
directive (Bulletin §B), the next c-push must come from a
*structurally different* idea, and Slack 1 is the directive's
top-listed candidate.

Slack 1 is uniquely attractive because:

- **It targets the dominant mode-1 mass (~0.9945 of the V68 budget).**
  Even a 1% reduction on that single window's envelope translates to
  roughly +1e-3 in c — three orders of magnitude above the recent
  +1e-6 increments.
- **It has a clean Phase 0 falsifier.** At admissible coefficient
  sequences `(a, b)` with `(η_j) ≈ δ_{j*}` (single-mode excitation),
  the convex bound is tight at sup_j H_j by definition. The Phase 0
  question is whether *all* admissible `(a, b)` consistent with
  Wang's `Section2Assumptions` plus paper eq (4) (`Σ⁺(c) ≤ Σ⁻(c)`)
  saturate this bound, or whether the eq (4) constraint forces
  multi-mode spread that the sup-relaxation throws away.
- **Sprint 077 (per-k α-varying kernel) does not subsume it.** Sprint
  077 attacked a different chain — the per-k cross-coupling lift,
  which exited V54's contraction regime and produced uniformly
  negative kernels (`Scratch/sprint_077_per_k_alpha_varying_kernel_sweep.txt`).
  This sprint stays inside the sup-relaxation step of the existing
  per-mode kernel, not the lift identity.

If the probe falsifies Slack 1 (single-mode coefficients are admissible
and force the bound to be tight), the result is documented and the
planner pivots to Slack 5 (Σ⁺ vs Σ⁻ asymmetry) or Slack 3 (Λ-tightening)
in sprint 094. Either way, this sprint costs ~1 generator session and
produces an unambiguous decision.

## Concrete edits expected

- `Scratch/sprint_093_slack1_two_moment_envelope.py`
  (~400-700 lines): a Phase 0 sweep script that
  - **Defines the eleven V68 windows** by their canonical
    sqrt-pinned τ-breakpoints plus the Branch.one residual box, exactly
    as in sprint 091's witness.
  - **Constructs a parametric family of test coefficient
    distributions** `(η_j)_{j=1..J}` (with `J ∈ {10, 20, 40}`) covering:
      (i) δ-supported single-mode excitations `η_j = δ_{j, j*}` for
          `j* ∈ {1, …, J}`;
      (ii) two-mode excitations `η_j ∝ {1 at j*, λ at j*+k}` for
           `λ ∈ {0.1, 0.5, 1.0, 5.0, 10.0}` and `k ∈ {1, 2, 3}`;
      (iii) geometric decay `η_j ∝ r^j` for
            `r ∈ {0.3, 0.5, 0.7, 0.9}`;
      (iv) uniform `η_j ∝ 1` on `j ≤ J`;
      (v) Hayman-extremal-like power-law `η_j ∝ j^{-α}` for
          `α ∈ {0.5, 1.0, 1.5, 2.0}`.
    For each distribution, parameterize `(|a_j|², |b_j|²)` by
    `|b_j|² - |a_j|² = η_j` and `|a_j|² + |b_j|² = ξ_j` with
    `ξ_j ≥ |η_j|` (so `|a_j|², |b_j|² ≥ 0`). Sweep `ξ_j` shapes
    independently to test the eq (4) constraint.
  - **Verifies eq (4) admissibility per distribution.** For each
    candidate `(a, b)`, compute `Σ⁺(c) := Σ_{j : η_j ≤ 0} (-η_j) c^{2j+2}`
    and `Σ⁻(c) := Σ_{j : η_j ≥ 0} η_j c^{2j+2}` (Wang's split at the
    sign of η_j). Reject distributions violating `Σ⁺(c) ≤ Σ⁻(c)`. The
    sweep reports the rejection rate per family.
  - **Computes the relaxation ratio** at each of V68's eleven
    ρ-windows:

        R(c, ρ; (a, b)) := Σ_j p_j(ρ) · H_j(c, ρ) / sup_j H_j(c, ρ)

    where `p_j(ρ) := η_j ρ^{2j} / Σ⁻(ρ)`,
    `H_j(c, ρ) := (j/(j+1)) · c^{2j+2} / ρ^{2j}`, and `Σ⁻(ρ) := Σ_j η_j ρ^{2j}`.
    The ratio is in `[0, 1]` by construction. Report the per-window
    `inf_{(a,b)} R` over the admissible test family.
  - **Computes the two moments** `m₁(p) := Σ_j j p_j(ρ)` and
    `m₂(p) := Σ_j j² p_j(ρ)` per ρ for each admissible `(a, b)`, and
    records scatter plots of `R` versus `(m₁, m₂)`.
  - **Attempts a moment-bound fit.** For each ρ, fit
    `R̂(m₁, m₂) := f₀(c, ρ) + f₁(c, ρ) · m₁ + f₂(c, ρ) · m₂` (or a
    suitable parametric form) to the scatter, and verify whether
    `R(c, ρ; (a, b)) ≤ R̂(m₁(p), m₂(p))` holds across the test family
    with `R̂ < 1` strict.
  - **Translates the gain to a c-push estimate.** If the per-window
    fitted `R̂` is below 1 by `δ_w(c, ρ)` on window w, recompute V68's
    joint mass under the tightened envelope `R̂ · sup_j H_j` and find
    the largest `c_new` for which the joint mass still exceeds
    `1 + 1e-4`.
  - **Emits a DECISION line** at the end of stdout:
    `DECISION: GO with c_new = <fraction>, target +<delta>e-3` or
    `DECISION: NO-GO — Slack 1 falsified, structural reason: <one-line>`.
  - Uses `mpmath` at `dps ∈ {40, 80}` (40 for the bulk sweep, 80 for
    the final re-verification at the chosen c_new).
- `Scratch/sprint_093_slack1_two_moment_envelope.txt`
  (~150-300 lines): captured stdout including per-family rejection
  rate, per-window inf-ratio table, moment scatter summary,
  fitted-envelope coefficients, c-sweep table under the proposed
  envelope, and the DECISION line.
- `Scratch/sprint_093_witness.txt` (~30-80 lines): if GO, the
  two-moment envelope coefficients and chosen c_new in a format ready
  for sprint 094 to consume; if NO-GO, a structural memo summarizing
  the falsification (which test family saturates the bound, what
  Section2Assumptions field would need to constrain it, why eq (4)
  doesn't suffice).
- `Experience.md`: append a "Sprint 093 — …" subsection summarizing
  the DECISION, the falsifying or supporting evidence, and the
  forward direction (sprint 094 either ships GO via a Lean
  derivation, or pivots to Slack 5/3 with the lessons recorded).
- `Bulletin.md`: append one row per the standard pattern
  (`sprint_093 PASS|FAIL: …`).

No Lean files modified. No `Numerical_Library` wrappers added (this is a
pure Scratch sweep). No `lemma.toml` edits. No proposals filed (the
human directive Section C explicitly endorses Phase-0-first probing on
Slacks 1–5).

## Acceptance criteria

1. `Scratch/sprint_093_slack1_two_moment_envelope.py` runs end-to-end
   without errors at `dps = 40` for the bulk sweep and `dps = 80` for
   the chosen `c_new` re-verification.
2. The captured stdout `.txt` file contains:
   - a non-empty per-family rejection-rate table for the eq (4)
     admissibility check;
   - a per-window inf-ratio table over the eleven V68 windows;
   - either (GO) a fitted two-moment envelope with per-window `δ_w(c, ρ)`
     gap and a c-sweep showing the largest `c_new > 71313/200000` with
     joint mass `≥ 1 + 1e-4` under the tightened envelope, **or**
     (NO-GO) a single-mode test case with `R(c, ρ; (a, b)) = 1.0` to
     within numerical noise (`|1 - R| ≤ 1e-12`) at some `ρ` in the
     V68 windows, demonstrating the bound is tight.
   - a final `DECISION:` line in one of the two prescribed formats.
3. The `witness.txt` file's content matches the DECISION line: GO →
   contains envelope coefficients and `c_new`; NO-GO → contains the
   structural-reason memo.
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
- Modify `Numerical_Library/rigorous_scalar.py` (the existing per-mode
  mass helpers are referenced for documentation but not extended).
- Modify `KorenblumPaper/` (read-only).
- File a `Proposals/` entry. (Per Section C of the human directive
  and the AGENT_BRIEF "default disposition" guidance.)
- Lift any of this sprint's content into a Lean per-candidate
  derived-theorem file — that is sprint 094's task if this sprint
  emits GO.
- Sweep over architectures other than V68's eleven-window split. The
  envelope tightening is on the same windows V68 already uses; the
  point is to replace `sup_j H_j` with a tighter envelope on each
  existing window, not to repartition.

## Time budget

≤ 60 minutes runtime for the Scratch sweep
(~6-10 minutes of `mpmath dps=40` bulk sweep + ~2-3 minutes of `dps=80`
re-verification, in line with sprint 089's and sprint 091's wall-clock
profiles).

≤ 1 generator session.

## Stop conditions

- DECISION GO emitted with witness file populated:
  `STATUS=READY_FOR_EVALUATION` (the evaluator will Pass/Fail-no-Lean
  in the standard "Phase 0 sprint" pattern of sprints 077, 087, 089,
  091).
- DECISION NO-GO emitted with structural-reason memo:
  `STATUS=READY_FOR_EVALUATION` (same pattern; NO-GO is a valid
  Phase 0 outcome and the sprint is still PASS).
- Phase 0 sweep crashes / cannot produce a DECISION line:
  `STATUS=BLOCKED` with the exact failure (e.g. mpmath precision
  inadequate, unexpected sign in η-distribution, eq (4) check
  ill-defined for some family).
- Phase 0 sweep produces an ambiguous result (e.g. `R̂` fits but only
  marginally, or `c_new = c_v68 + 0` rounds): `STATUS=BLOCKED` with
  the ambiguity documented and the planner asked to pick a clearer
  acceptance threshold.
- Trust expansion needed: `STATUS=BLOCKED_NEEDS_HUMAN`. (Should not
  occur — this sprint doesn't touch the trust surface at all.)
