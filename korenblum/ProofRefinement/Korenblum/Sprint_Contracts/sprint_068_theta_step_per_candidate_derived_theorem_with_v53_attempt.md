# Sprint 068: Ship THETA_STEP `(1+Λ)·sigmaMinus ρ ≤ Λ·sigmaPlus ρ` (and the equivalent `sigmaMinus ρ ≤ Λ/(1+Λ)·sigmaPlus ρ` shrinkage form) as a per-candidate derived theorem, then attempt to compose it with sprint 045 / sprint 040 into a closing reducer for V53; ship V53 if a discharge route closes, otherwise produce Outcome B exhaustion synthesis

**Created**: 2026-05-04 by Planner
**Parent candidate**: `Candidates/V52.lean` (current high-water mark, `c_value = 7129/20000 = 0.35645` via the literal-(15) HP oracle channel)
**Target file**: `Candidates/V53.lean` PLUS supporting per-candidate derived-theorem files under `Candidates/V53/` (notably `Candidates/V53/ThetaStep.lean`)
**Direction**: section2-proof + analytic-Lean derivation — the FIRST attempt to ship THETA_STEP as a Lean theorem (065/066/067 only treated it as an analytic identity, never wrote any Lean for it)

## Goal

Ship the analytic identity

```text
(1 + paperLambda K c ρ) · sigmaMinus a b ρ ≤
   paperLambda K c ρ · sigmaPlus a b ρ
                                         (THETA_STEP_RAW)
```

equivalently

```text
sigmaMinus a b ρ ≤
   (paperLambda K c ρ / (1 + paperLambda K c ρ)) · sigmaPlus a b ρ
                                         (THETA_STEP)
```

valid for `ρ ∈ (c, 1)`, as a Lean `theorem` (not an `axiom`) in a per-candidate
derived-theorem file `Candidates/V53/ThetaStep.lean`, derived from
`Section2Assumptions a b K c` plus existing workspace lemmas (`paper.eq8`,
`paper.eq9`, sprint 027) plus Mathlib. **No new axiom. No oracle. No edit
to `KorenblumPaper/`. No edit to `Reduction.lean`. No edit to `lemma.toml`.**

Then attempt to compose THETA_STEP with sprint 045's closing reducer
(`valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`,
`Reduction.lean:6927`) — specifically by exposing THETA_STEP as a per-`ρ`
upper bound on `sigmaMinus` and seeing whether the resulting witness chain
admits a discharge route distinct from V52's `valid_of_eq15` /
`hEq15_oracle_certified_hp_35645` channel. Two outcomes are explicitly
contracted; either is a successful sprint.

The fixed quantitative target is `c_value = 7129/20000 = 0.35645` (V52's
ceiling). This sprint deliberately does NOT push `c`; it pursues the
**structural** advance the harness has been missing: the FIRST per-candidate
Lean theorem corresponding to a Wang un-numbered intermediate algebraic step,
following the institutional pattern the unstuck plan
(`docs/HARNESS_UNSTUCK_PLAN.md` §5, `AGENT_BRIEF.md` lines 154–204) was
written to enable.

## Why

Three sprints (065, 066, 067) have established that the closed-form
`(a, b)`-independent kernel space is **structurally exhausted** above the
literal-(15) crossover at `c ≈ 0.35635`:

| Sprint | Kernel                                              | Status |
|--------|-----------------------------------------------------|--------|
| 014/048 full | `c⁴ ≤ ∫_{c..1} 2ρ³/Λ(c, ρ) dρ`                   | falsified `c ≥ 0.3554` |
| 017/048 b-2  | `c⁴/2 ≤ ∫_{branchSplit..1} 2ρ³/Λ(c, ρ) dρ`       | falsified `c ≥ 0.3554` |
| 067 full     | `c² ≤ ∫_{c..1} 2ρ/(1+Λ(c, ρ)) dρ`                 | falsified everywhere   |
| 067 b-1, b-2 | `c² ≤ ∫ 2ρ/(1+Λ(c, ρ)) dρ` on each sub-window     | falsified everywhere   |
| 045 ×k       | `Σ⁺_int(c) ≤ ∫_{c..1} 2ρ³·Z_ρ/Λ(c, ρ) dρ`         | sprint 051 NEGATIVE on E0–E3; sprint 066 BLOCKED from `Section2Assumptions` |

This sprint does NOT propose another `(a, b)`-independent scalar kernel.
Instead it follows the unstuck-plan directive
(`docs/HARNESS_UNSTUCK_PLAN.md` §5; `AGENT_BRIEF.md` lines 197–204):

> When a sprint needs such a handle, **prove it in a derived-theorem file
> scoped to the candidate version you are shipping**. … Default disposition:
> when proposal_003-shaped requests come up (intermediate Wang derivation
> step needed), the answer is "prove it in Lean in a per-candidate
> derived-theorem file," not "file a proposal."

Sprints 065, 066, 067 each *reference* THETA_STEP as analytically valid but
NEVER write any Lean for it. Sprint 067 obstruction lines 211–238 explicitly
isolates THETA_STEP as the analytic step that survives the falsification of
its consumer kernel. Sprint 066 obstruction lines 99–113 describes the
chain `eq8: σ⁻ ≤ liftGap → eq9: liftGap ≤ Λ·circleGap → sprint 027:
circleGap = σ⁺ − σ⁻ → algebra: (1+Λ)·σ⁻ ≤ Λ·σ⁺` line by line in prose but
ships zero `.lean` files. Sprint 065 references it only via the
single-mode E1 closed-form. **No prior sprint has actually written
THETA_STEP into Lean.**

The advance this sprint targets is therefore **structurally novel and
measurable**: a reusable Lean theorem in `Candidates/V53/ThetaStep.lean`
that future planners can compose. The unstuck plan §5 explicitly calls
this out as "the answer" to the proposal_003-shaped pattern. Per the
`AGENT_BRIEF.md` "Generator capability" section (lines 154–171) THETA_STEP
is well within scope:

- algebraic identities on `ℝ`-valued sums (`(1+Λ)·σ⁻ ≤ Λ·σ⁺` via division
  by `1+Λ > 0`),
- termwise `tsum` partitioning (sprint 027 already in the workspace),
- chains of `paper.eq*` projections (`eq8.2`, `eq9.1`).

The expected proof body is roughly **40–80 lines of Lean** plus standard
imports — well below the multi-hundred-line analytic chains the brief
asserts the generator can handle. If the generator cannot produce
THETA_STEP in 40–80 lines from the existing trusted surface, the
obstruction note from this sprint will be a *fourth* genuinely-distinct
attempt-first datum (joining 065/066/067) that the closed-form-kernel
exhaustion finding has reached the Lean tactic level.

The composition arm of this sprint (`## Phase B`) is genuinely speculative:
sprint 067 falsified one specific consumer (the bulk-integrated-with-`(1+Λ)`
closing reducer), but THETA_STEP composed with sprint 040's
`diskExcess ≤ c²·Σ⁺(c)` route plus sprint 032's `Σ⁺` monotonicity — using
THETA_STEP per-`ρ` rather than integrated against `(1+Λ)` — is a
*different* discharge structure that has not been tested. Phase B's
explicit honest disclosure (see §"Phase B" below) acknowledges the
high probability of a falsification cascade similar to sprint 067's;
the sprint's primary deliverable is Phase A (THETA_STEP as a reusable
Lean theorem). **Phase B is exploratory and is contracted under
Outcome B if it falsifies.**

## Roadmap to `c > 0.3554`

> *(Bulletin Step 1 mandates this section even for c-tying sprints.)*

1. **Which existing closing reducer is the cheapest path to `c > 0.3554`?**
   None of the existing closing reducers in `Reduction.lean` admits a
   discharge above `c ≈ 0.35635` without a structural input that is not
   currently in `Section2Assumptions` (per sprints 048/050/051/065/066/067
   cumulative evidence). The cheapest path *through Lean* is now
   THETA_STEP-as-building-block plus a NEW closing reducer that consumes
   it. Sprint 045 is the closest existing reducer; its kernel
   `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ` is per-`k` on the LHS and
   integrated-`(a, b)`-dependent on the RHS, and Phase B asks whether
   THETA_STEP unlocks a shorter discharge of this kernel.

2. **What is the numerical kernel?** For Phase A: there is no numerical
   kernel — THETA_STEP is an algebraic identity. For Phase B (if reached):
   the candidate kernel is

   ```text
   diskExcess (circleGap a b) c
     ≤ c² · sigmaPlus a b c                      [sprint 040, paper-axiom-free]
     ≤ c² · (1 + paperLambda K c ρ) · circleGap a b ρ
                                                 [THETA_STEP rearranged at ρ > c]
     ≤ ?                                          [per-ρ → integrated route]
   ```

   The unknown step is converting a per-`ρ` upper bound on `circleGap ρ`
   into an integrated bound on `annulusExcess` — the obvious step
   (multiplying by `2ρ` and integrating) requires a window in which
   `c²·(1+Λ(c,ρ))/Λ(c,ρ)·1/ρ²` is bounded above by `1` against
   `2ρ·circleGap ρ dρ`, which is a closed-form scalar inequality of
   exactly the shape sprint 067 falsified. **Phase B is therefore
   expected to falsify**; the value is in producing the Outcome-B
   obstruction note, not in expecting Phase B to succeed.

3. **Does the kernel hold with margin at some `c > 0.3554`?** Phase A:
   N/A (algebraic identity, not a numerical kernel). Phase B: per the
   structural argument above, the implied numerical kernel is sprint
   067's KERNEL_67 with at most a closed-form scaling factor; expected
   to falsify above `c = 0.3554` per sprint 067's evidence. The
   *generator* must do the Phase A spot-check before any Phase B Lean
   work — see Phase B step 1 below.

4. **What is the trust gap between the Scratch witness and a Lean proof?**
   For Phase A: zero — THETA_STEP is paper-axiom-shape `{eq8, eq9}` plus
   sprint 027 (paper-axiom-free), no oracle, no `Numerical_Library`,
   no Scratch.

5. **Decide between two routes per gap, for each non-closed-form cell.**
   Phase A: pure Lean theorem, no cells. Phase B: if Phase B reaches
   Lean and surfaces a missing closed-form scalar inequality, the route
   is Outcome B — record the falsification, do not expand the trust
   surface (Bulletin lines 174–187).

6. **What does the c-pushing candidate look like?** This sprint does
   NOT push `c`. V53 ships at `c_value = 7129/20000 = 0.35645` (ties
   V52). The c-pushing candidate beyond V52 is deferred per the
   bulletin's three-sprint exhaustion synthesis; this sprint's purpose
   is to put a reusable Lean building block in place that future
   c-pushing sprints can consume.

## Three candidate sprint shapes considered (per Planner ultrathink rule)

The Planner enumerated three structurally distinct sprint shapes before
choosing this one:

1. **Drop-N2 closing reducer** — test the kernel `Σ⁺_int(c) ≤ Σ⁺_int_ann(c)`
   per sprint 065 obstruction note line 168–181. **Strongest objection**:
   the witness obligation is `diskExcess ≤ annulusExcess`, where
   `annulusExcess = Σ⁺_int_ann(c) − Σ⁻_int_ann(c)` (sprint 047). On the
   single-mode E1 family (`a ≡ 0, b_1 = 1, others 0`), `Σ⁻_int_ann(c) =
   (1 − c⁴)/2 > 0`, so dropping `Σ⁻_int_ann` from the RHS *weakens* the
   target (we'd need `diskExcess ≤ Σ⁺_int_ann(c)` which is strictly weaker
   than the witness obligation). The chain therefore does not close: even
   if `Σ⁺_int(c) ≤ Σ⁺_int_ann(c)` holds termwise (which it does for
   `c² ≤ 1/2`), the sufficient condition `Σ⁺_int(c) ≤ Σ⁺_int_ann(c) −
   Σ⁻_int_ann(c)` is FALSE on E1 by sprint 065's obstruction note.
   Demoted: this is sprint 065's already-falsified kernel, just relabelled.

2. **Convexity-via-sprint-033 chain bypassing eq4-bulk** — use sprint 033's
   `sigmaPlus c ≤ μ₁·sigmaPlus 0 + μ₂·sigmaPlus ρ` at `r = 0`, which
   combined with `paper.eq4 (r := 0)` (giving `sigmaPlus 0 ≤ sigmaMinus
   0 = 0`) yields `sigmaPlus c ≤ (c²/ρ²)·sigmaPlus ρ`. **Strongest
   objection**: this is exactly Direction B of sprint 066 (obstruction
   lines 300–435), which produced one of the three obstruction notes
   informing this planner session. Re-running it is duplicative; the
   Lean tactic chain reduces to the same `sigmaPlus ρ ≤ φ(c, ρ)·Z_ρ`
   bottleneck at `ρ > c` that sprint 066 enumerated as missing. Demoted.

3. **THETA_STEP as a per-candidate derived theorem, with a Phase B
   composition probe.** **Chosen.** This is the FIRST sprint to actually
   write Lean for THETA_STEP. The Phase A deliverable is a reusable Lean
   theorem in `Candidates/V53/ThetaStep.lean`, which is concrete,
   measurable, and survives independently of Phase B's outcome. The
   sprint advances the harness regardless of whether Phase B falsifies
   (in which case Outcome B produces a fourth attempt-first datum
   distinct from 065/066/067 — namely, the FIRST attempt to compose
   THETA_STEP with sprint 040 / sprint 045 in Lean) or admits (in
   which case V53 ties V52 with a structurally novel discharge route).

## Concrete edits expected

### Phase A (deliverable, must succeed)

1. **NEW**: `ProofRefinement/Korenblum/Candidates/V53/ThetaStep.lean`.

   Contains theorems (no axioms, no new `Section2Assumptions` fields):

   a. The raw cross-multiplied form THETA_STEP_RAW:
      ```lean
      theorem theta_step_raw {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
          (paper : Section2Assumptions a b K c)
          {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
          (1 + WangOuter.paperLambda K c ρ) *
              PaperAxioms.sigmaMinus a b ρ ≤
            WangOuter.paperLambda K c ρ * PaperAxioms.sigmaPlus a b ρ
      ```
      Proof sketch (40–80 lines):
      - Apply `paper.eq8_sigma_to_liftGap hcρ hρ_lt_one` (yields
        `sigmaMinus ρ ≤ liftGap a b ρ`).
      - Apply `paper.eq9_liftGap_to_circleGap hcρ hρ_lt_one` (yields
        `liftGap a b ρ ≤ paperLambda K c ρ · circleGap a b ρ`).
      - Chain to get `sigmaMinus ρ ≤ paperLambda K c ρ · circleGap a b ρ`.
      - Apply `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
        (sprint 027, `Reduction.lean:3902`) — *requires the workspace
        summability premise*; the generator must surface it as a
        hypothesis to the theorem if `Section2Assumptions` does not
        already imply it. **Honest disclosure**: if the summability
        premise is not derivable from `Section2Assumptions a b K c`
        directly, this becomes an Outcome B candidate (record which
        cell is missing and why); see §"Phase A failure mode" below.
      - Substitute `circleGap = σ⁺ − σ⁻` to rewrite the inequality as
        `σ⁻ ≤ Λ·(σ⁺ − σ⁻)`, equivalently `(1+Λ)·σ⁻ ≤ Λ·σ⁺`. Use
        `WangOuter.paperLambda_pos paper hcρ hρ_lt_one` (or whichever
        positivity lemma is currently exposed) to discharge `0 < Λ`
        side conditions.

   b. The shrinkage form THETA_STEP:
      ```lean
      theorem theta_step {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
          (paper : Section2Assumptions a b K c)
          {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
          PaperAxioms.sigmaMinus a b ρ ≤
            (WangOuter.paperLambda K c ρ /
              (1 + WangOuter.paperLambda K c ρ)) *
              PaperAxioms.sigmaPlus a b ρ
      ```
      Proof: divide THETA_STEP_RAW by `1 + Λ > 0`. ~10 lines.

   c. The `θ < 1` corollary:
      ```lean
      theorem theta_step_strict_less_than_one
          {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
          (paper : Section2Assumptions a b K c)
          {ρ : ℝ} (hcρ : c < ρ) (hρ_lt_one : ρ < 1) :
          WangOuter.paperLambda K c ρ /
              (1 + WangOuter.paperLambda K c ρ) < 1
      ```
      Proof: standard `Λ/(1+Λ) < 1 ↔ Λ < 1+Λ ↔ 0 < 1`, given `1+Λ > 0`.
      ~5 lines.

2. **NEW**: `ProofRefinement/Korenblum/Candidates/V53.lean`.

   Imports `ProofRefinement.Korenblum.Candidates.V53.ThetaStep` plus
   the existing trusted surface. Defines `c_value := (7129 : ℚ) / 20000`,
   plus the `korenblum_constant_search` theorem.

   The discharge route is one of:

   **Phase B-a (Phase B succeeds)**: a NEW closing reducer that consumes
   THETA_STEP plus sprint 040 plus sprint 045's existing infrastructure,
   producing a witness chain whose existential cell admits a paper-faithful
   discharge at `c = 7129/20000`. The discharge must NOT be
   `valid_of_eq15`-via-`hEq15_oracle_certified_*` (that is V52's route);
   the structural novelty is a non-eq15 closing reducer at the same `c`.

   **Phase B-b (Phase B falsifies)**: V53 ships with the same
   `valid_of_eq15`-via-`hEq15_oracle_certified_hp_35645` discharge as V52,
   imports `Candidates/V53/ThetaStep.lean` (forcing the elaborator to
   verify the new theorem compiles), and includes a side lemma
   `v53_theta_step_compiles_at_seed_witness` that exercises THETA_STEP
   against a constructed `Section2Assumptions` instance to confirm the
   theorem is non-vacuous. **This is still a successful sprint**: V53's
   trust-base footprint is identical to V52's (both `axioms_used =
   {seed} ∪ {hEq15_oracle_certified_hp_35645}`), but the workspace gains
   a reusable Lean theorem.

3. **`lemma.toml`**: NO edits expected. The new file
   `Candidates/V53/ThetaStep.lean` is under
   `ProofRefinement.Korenblum.Candidates.V53.ThetaStep`, which the
   existing `[workspace_import_policy]` already permits via the
   `ProofRefinement.Korenblum.*` prefix (per `AGENT_BRIEF.md` rule 4
   and the unstuck plan §5 third bullet).

4. **`Bulletin.md`**: append one `## Recent events` row recording
   sprint 068's outcome (Phase A success/failure, Phase B success/failure).

5. **`Experience.md`**: append one entry per the Bulletin honesty rules
   (lines 139–161): what was attempted, dead ends if any, current
   obstacle, numerical exploration (Phase B only), next move,
   trust-surface accounting.

### Phase B (exploratory; Outcome B is permitted)

If Phase A succeeds — i.e. `Candidates/V53/ThetaStep.lean` compiles
with the three named theorems all proved by `theorem` (not `sorry`)
and `axioms_used` for these theorems is `⊆ {seed}` — the generator
attempts Phase B:

1. **Phase B step 1: Scratch spot-check first.** Before any Phase B
   Lean work, the generator writes
   `Scratch/sprint_068_phaseB_kernel_check.py` (mpmath dps=50, n_trunc=200,
   per Bulletin lines 313–317 and sprint 067's recommendation lines
   311–316) computing the candidate Phase B kernel at the proposed
   `(c, ρ₁, ρ₂)` grid and reporting the gap. If the gap is uniformly
   negative at every tested c-value at and above `c = 7129/20000`,
   skip to Phase B-b *immediately* (do NOT write Lean for a falsified
   kernel).

2. **Phase B step 2: closing reducer attempt.** If Phase B step 1
   admits at any `c ≥ 7129/20000` with margin ≥ 1e-3 at the dps=50
   envelope, attempt the Lean derivation of the closing reducer in
   `Candidates/V53.lean` (or in a sibling `Candidates/V53/` derived
   file). The reducer must consume THETA_STEP from
   `Candidates/V53/ThetaStep.lean`. Time budget: ≤ 60 minutes.

3. **Phase B step 3: outcome decision.** If the reducer compiles and
   `Candidates/V53.lean` evaluates `pass: true`, this is **Phase B-a**
   (V53 ties V52 via a structurally novel chain — accept). Otherwise
   record the obstruction in `Scratch/sprint_068_phaseB_obstruction.md`
   and proceed to Phase B-b.

## Acceptance criteria

### Outcome A — Phase A succeeds, Phase B-a or Phase B-b ships V53

1. `lake build ProofRefinement.Korenblum.Candidates.V53.ThetaStep`
   succeeds. The file contains `theorem theta_step_raw`, `theorem
   theta_step`, `theorem theta_step_strict_less_than_one` as `theorem`s
   (no `axiom`s, no `sorry`s).
2. `lake build ProofRefinement.Korenblum.Candidates.V53` succeeds.
3. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py
   --file ProofRefinement/Korenblum/Candidates/V53.lean` succeeds with
   `pass: true`.
4. The evaluator's `axioms_used` for V53 is `⊆ {seed} ∪
   {hEq15_oracle_certified_hp_35645}` (Phase B-b) or `⊆ {seed}` plus
   any Phase B-a-specific axioms registered in `lemma.toml` *with the
   sprint contract naming each one* (Phase B-a). No new free-floating
   axioms beyond those already permitted.
5. The evaluator's `score` is exactly `7129/20000` (NOT a c-push;
   acceptance under Outcome A requires the score-tie justification
   is the THETA_STEP advance, recorded in `Experience.md`).
6. `axioms_used` for the three theorems in
   `Candidates/V53/ThetaStep.lean` (verified separately if needed via a
   targeted `#print axioms` check) is `⊆ {seed}` (no eq15 oracle
   leakage; THETA_STEP is paper-axiom-free of `eq15`).

### Outcome B — Phase A blocks (THETA_STEP cannot be derived from
`Section2Assumptions`)

If the generator cannot complete Phase A in a reasonable budget (e.g.
the summability premise needed by sprint 027 cannot be discharged from
`Section2Assumptions a b K c` directly, or the `paperLambda` positivity
side condition has no exposed lemma at `ρ ∈ (c, 1)`):

1. Write `Scratch/sprint_068_obstruction.md` documenting at the
   granularity of sprints 065/066/067:
   - Which exact intermediate goal blocked the proof (e.g. "after
     applying `paper.eq8_sigma_to_liftGap` and
     `paper.eq9_liftGap_to_circleGap`, the next step to substitute
     `circleGap = σ⁺ − σ⁻` requires a `Summable` cell at radius `ρ` that
     `Section2Assumptions a b K c` does not bundle and that
     workspace lemma `<name>` cannot supply").
   - The Lean tactic transcript at the blocking goal (use `lean_goal`
     output or `#check`-traced state).
   - Whether the obstruction is missing-field (legitimate proposal_004
     target per the four-condition guide in `AGENT_BRIEF.md` lines
     154–204) or gap-in-attack (capability — record as a request for
     a successor sprint to retry with a different lemma family).
   - A closed-form algebraic identity confirming the obstruction is
     mathematical not tactical — or, if no such identity exists,
     record explicitly that the obstruction is purely a workspace-API
     gap.
2. Do NOT ship `Candidates/V53.lean`. Do NOT edit
   `KorenblumPaper/`, `Reduction.lean`, `lemma.toml`, or
   `Numerical_Library/`. The deliverable is the obstruction note.
3. Do NOT file proposal_004 in this sprint. The four-condition guide
   (`AGENT_BRIEF.md` lines 154–204, `HARNESS_UNSTUCK_PLAN.md` §1)
   requires *judgment*, not a mechanical gate; the next planner makes
   that judgment after reading the obstruction note. This sprint's
   role is to produce the attempt-first evidence.
4. Update `Bulletin.md` and `Experience.md` per Phase A failure-mode
   honesty rules.

### Outcome C — Phase A succeeds, Phase B-step-1 falsifies, Phase B-b ships V53

This is a successful sprint identical to Outcome A's Phase B-b. Score
ties V52 at `7129/20000`. The Phase B falsification produces a fourth
genuinely-distinct attempt-first datum:

| Sprint | Phase B kernel under test                                         | Status |
|--------|-------------------------------------------------------------------|--------|
| 065    | `Σ⁺_int(c) ≤ Σ⁺_int_ann(c) − Σ⁻_int_ann(c)` (canonical extremals) | falsified at every c |
| 066    | `c⁴ ≤ ∫ 2ρ³/Λ` derivable from Section2Assumptions                  | non-derivable; reduces to sprint 014 kernel which is `c ≥ 0.3554`-falsified |
| 067    | `c² ≤ ∫ 2ρ/(1+Λ)` (closed-form scalar)                            | falsified at every c |
| 068 PB | (whatever closing-reducer kernel the generator picks)             | record outcome |

Outcome C **must** include the kernel that was tested (Phase B step 1's
output), the gap values at `c ∈ {0.355, 0.357, 0.36, 0.37, 0.40}`, and
the comparison to sprint 067's tabulation (per the sprint 067 obstruction
note's methodological-recommendation §3 at lines 311–316).

## Honest disclosure: this sprint may produce zero c-push

Per Bulletin lines 27–31, c-tying sprints are **demoted** from the
default success criterion. This sprint's primary deliverable is the
THETA_STEP-as-per-candidate-Lean-theorem advance per the unstuck-plan
directive. The c-tie is acceptable here ONLY because:

1. **No prior sprint has attempted to ship THETA_STEP as Lean.** Sprints
   065/066/067 all reference it as an analytic identity but never write
   `.lean` for it. Producing the first Lean theorem corresponding to a
   Wang un-numbered intermediate algebraic step is the institutional
   pattern the unstuck plan §5 was written to enable. This is a
   measurable, scopeable advance.

2. **THETA_STEP is mathematically valid at the workspace's current
   trust surface.** Sprint 067 obstruction lines 211–238 confirm the
   chain `eq8 + eq9 + sprint 027 + algebra` derives THETA_STEP without
   any new axiom or oracle. The four-condition proposal-filing guide
   (`AGENT_BRIEF.md` lines 154–204) makes proving-it-in-Lean the
   correct first move, not proposal-filing.

3. **Phase B is genuinely novel.** Even if Phase B falsifies, the
   resulting obstruction note will be a fourth attempt-first datum
   distinct from sprints 065/066/067 (it's the FIRST sprint that
   tests a closing reducer through THETA_STEP-as-an-actual-Lean-theorem
   rather than treating THETA_STEP as an unwritten identity).

4. **The c-push remains pending.** This sprint does not push `c` past
   V52. The next planner — informed by either the new THETA_STEP
   building block (Outcome A/C) or the Phase A obstruction note
   (Outcome B) — will be in a strictly better position to either
   (a) compose THETA_STEP with another building block toward a c-push,
   (b) file proposal_004 with a fourth row of attempt-first evidence,
   or (c) declare the harness genuinely halted and synthesize the
   four-sprint exhaustion finding for human review.

## Out of scope

- Editing files under `KorenblumPaper/` (the trusted paper surface;
  `AGENT_BRIEF.md` lines 197–204 / unstuck plan §5 explicitly forbid
  this for the generator).
- Editing `Proof/Reduction.lean` (per-candidate derived theorems live
  under `Candidates/V53/`, not in the shared reducer module — unstuck
  plan §5).
- Adding new free-floating `axiom` declarations (Phase A is theorems
  only; Phase B-a may register an oracle wrapper *only if* the contract
  text below explicitly names the `Numerical_Library` function, the
  `lemma.toml` entry, and the Lean-facing axiom — see `AGENT_BRIEF.md`
  Numerical-tooling §). This contract does NOT pre-name any oracle for
  Phase B-a; the generator must inline the oracle registration in its
  own contract amendment if it pursues that route, OR ship under
  Phase B-b.
- Pushing `c_value` above `7129/20000`. The sprint's score target is
  exactly `7129/20000` (tie V52). Any candidate with a higher `c_value`
  is out of contract scope and a regression to be removed before
  evaluation.
- Filing proposal_004 (any successor proposal). The four-condition
  guide is satisfied by judgment after reading the obstruction notes;
  this sprint produces evidence, not proposal text. Proposal-filing
  is the next planner's call (or a human's), not this sprint's
  generator's.
- Editing other candidate files (`Candidates/V0.lean` … `Candidates/V52.lean`).
- Editing the proposal_001 / proposal_002 / proposal_003 status fields.

## Time budget

- Phase A: ≤ 90 minutes runtime (the generator's first-attempt budget;
  multi-hundred-line Lean is in scope per the brief, but THETA_STEP
  itself is expected ≤ 80 lines so this budget gives ample headroom
  for searching).
- Phase B step 1 (Scratch): ≤ 15 minutes.
- Phase B step 2 (Lean if step 1 admits): ≤ 60 minutes.
- Total wall-clock target: ≤ 165 minutes for Outcome A; ≤ 105 minutes
  for Outcome C (Phase B-step-1 falsifies, Phase B-b ships); ≤ 90
  minutes for Outcome B.

## Stop conditions

- Phase A theorems compile, V53 ships and evaluates `pass: true`,
  `axioms_used` matches the V52 envelope (Outcome A or C):
  `STATUS=READY_FOR_EVALUATION`.
- Phase A blocks at a precisely-named tactical or structural cell:
  `STATUS=BLOCKED` with `Scratch/sprint_068_obstruction.md` written
  per Outcome B above.
- The obstruction is a genuine trust-base expansion that no
  combination of `Section2Assumptions` fields plus existing workspace
  lemmas plus Mathlib could close — and the four-condition guide is
  unambiguously satisfied per `AGENT_BRIEF.md` lines 154–204:
  `STATUS=BLOCKED_NEEDS_HUMAN`, with the obstruction note plus an
  explicit citation of why it cannot be a Lean theorem from existing
  material. **Default to `BLOCKED` over `BLOCKED_NEEDS_HUMAN`**: the
  unstuck-plan diagnosis lines 5–32 documents that the harness has
  been over-using `BLOCKED_NEEDS_HUMAN` as a cheap exit; only invoke
  it if the four-condition guide is rigorously met.
