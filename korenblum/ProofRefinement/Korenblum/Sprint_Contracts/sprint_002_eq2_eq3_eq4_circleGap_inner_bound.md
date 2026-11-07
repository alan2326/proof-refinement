# Sprint 002: Derive a `(2)+(3)+(4)` pointwise upper bound on `circleGap(r)` for `r < c`

**Created**: 2026-05-02 13:30 by Planner
**Parent candidate**: `Candidates/V1.lean`
**Target file**: `Candidates/V2.lean`
**Direction**: section2-proof

## Goal

Ship a *new generic Lean theorem*

```text
circleGap_inner_bound_of_eq2_eq3_eq4 :
    {a b : ℕ → ℂ} → {K : ℝ → ℝ → ℝ} → {c : ℝ} →
    (paper : Section2Assumptions a b K c) →
    {r ρ : ℝ} → 0 ≤ r → r < c → c < ρ → ρ < 1 →
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ
```

in `Proof/Reduction.lean`. The proof must route through *only*
`paper.eq3_circleGap_decomposition`, `paper.eq4_sigmaPlus_bound`, and
`paper.eq2_sigmaZeroMinus_lower`, with no use of `paper.eq5_*`, `paper.eq6_*`,
`paper.eq8_*`, `paper.eq9_*`, `paper.eq10_*`, `paper.eq11_*`, `paper.eq12_*`,
`paper.eq13_*`, `paper.eq14_combined`, or `paper.eq7_paperK_formula`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V2.lean` at the same `c = 0.3554` that compiles, scores
`≥` V1, and *materializes* the new chain by using
`circleGap_inner_bound_of_eq2_eq3_eq4` somewhere in its closure — even if V2
ultimately falls back to `valid_of_eq15` for the final sink theorem (e.g. as a
verified side lemma `v2_eq2_eq3_eq4_chain_compiles` that exercises the new
bound on the seed paper context).

## Why

The bulletin asks for *novel analytical derivations* through
`Section2Assumptions`, not numerical pushes. Sprints 000 and 001 both attack
the right-hand side of `diskExcess ≤ annulusExcess`: they integrate Wang's
pointwise bounds `(10)/(11)` (or their integrated forms `(12)/(13)/(14)`)
multiplied by the polar Jacobian, then cite `(15)` to drop the scalar mass.

**This sprint attacks the LEFT-hand side instead.** `diskExcess` is
`∫_0^c 2ρ · circleGap(ρ) dρ`, so any pointwise upper bound on `circleGap(r)`
for `r < c` immediately upper-bounds `diskExcess`. Equations `(3)` and `(4)`
already give upper bounds on `circleGap(r)` in terms of `sigmaPlus(c)` and
`sigmaZeroMinus(r)`; equation `(2)` gives a *lower* bound on
`sigmaZeroMinus(r)` in terms of values at `c` and a free parameter `ρ ∈ (c, 1)`.
Combining them gives a clean two-term pointwise bound on `circleGap(r)` whose
two factors are *non-negative on the inner disk* and depend only on
`sigmaZeroMinus(c)` and `sigmaZeroMinus(ρ)` — quantities that the
`(8)+(9)` chain ties back to `circleGap(ρ)` on the outer annulus.

This bound is the structural ingredient missing from every prior sprint:

- it gives downstream sprints a fundamentally different chain
  (`diskExcess` → `sigmaZeroMinus` → annulus, instead of
  `diskExcess` → `circleGap` → annulus via `(10)/(11)`);
- it exposes the `ρ ∈ (c, 1)` free parameter, which is a *new degree of
  freedom* not present in the `(15)` route;
- it requires zero new axioms, zero new oracle entries, no new Mathlib lemmas,
  and no expansion of `Section2Assumptions` — it is pure algebra over three
  hypotheses already exposed by the structure;
- having the lemma in `Reduction.lean` immediately enables a downstream
  sprint to integrate it against `r ∈ [0, c]` (with `ρ` chosen as a function
  of integration variables) and produce a wholly new sufficient condition
  for `diskExcess ≤ annulusExcess`.

The current sprint deliberately stops at the *pointwise* bound and exposes the
free parameter `ρ` as a forall, so the next sprint can attack the integration
step and the choice of `ρ(r)` as a separate problem.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add new generic theorem `circleGap_inner_bound_of_eq2_eq3_eq4` matching
    the shape above. The proof must:
    1. Apply `paper.eq3_circleGap_decomposition` (with hypothesis
       `0 ≤ r ∧ r < 1`, the latter from `r < c < ρ < 1`) to rewrite
       `circleGap a b r = sigmaPlus a b r - r^2 * sigmaZeroMinus a b r`.
    2. Apply `paper.eq4_sigmaPlus_bound` (with `0 ≤ r ∧ r < c ∧ c < 1`,
       where `c < 1` follows from `c < ρ < 1`) to obtain
       `sigmaPlus a b r ≤ sigmaPlus a b c`,
       `sigmaPlus a b c ≤ sigmaMinus a b c`,
       and `sigmaMinus a b c = c^2 * sigmaZeroMinus a b c`.
    3. Apply `paper.eq2_sigmaZeroMinus_lower` with the supplied
       `0 ≤ r ∧ r < c ∧ c < ρ ∧ ρ < 1` to obtain
       `sigmaZeroMinus a b r ≥
          ((ρ^2 - r^2)/(ρ^2 - c^2)) · sigmaZeroMinus a b c
          - ((c^2 - r^2)/(ρ^2 - c^2)) · sigmaZeroMinus a b ρ`.
    4. Substitute (3) into the rewritten `(3)` from step 1 — note the
       sign-flip from the `-r^2 * sigmaZeroMinus a b r` term — and chain
       with the `(4)` upper bound from step 2 to land on the stated
       two-term bound. The denominator `ρ^2 - c^2 > 0` (from `c < ρ`)
       is needed to flip the inequality in the right direction;
       multiplying by `r^2 ≥ 0` preserves the inequality. Use
       `nlinarith` / `linarith` with the explicit positivity facts as
       the closer; do not invoke `polyrith`.
  - Must NOT mention `paper.eq14_combined`, `paper.eq15_*`,
    `paper.eq{5,6,7,8,9,10,11,12,13}_*`, `WangOuter.paperLambda`,
    `Korenblum.scalarCriterion`, or `Korenblum.scalarIntegrand{1,2}` in the
    new theorem's body.
  - Add a one-line module-doc comment above the new theorem explaining
    that this is the Sprint 002 inner-disk bound and that the free
    parameter `ρ` is intentionally exposed for downstream integration.
- `ProofRefinement/Korenblum/Candidates/V2.lean`:
  - `-- @parent V1`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly as
    in V1; the seed-axiom token is already in `lemma.toml:[seed_axioms]`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does not
    regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v2_eq2_eq3_eq4_chain_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {r ρ : ℝ}
        (hr_nonneg : 0 ≤ r)
        (hr_lt : r < c_value)
        (hcρ : c_value < ρ)
        (hρ1 : ρ < 1) :
        PaperAxioms.circleGap a b r ≤
          (c_value ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c_value ^ 2))
              * PaperAxioms.sigmaZeroMinus a b c_value
            + r ^ 2 * ((c_value ^ 2 - r ^ 2) / (ρ ^ 2 - c_value ^ 2))
              * PaperAxioms.sigmaZeroMinus a b ρ :=
      circleGap_inner_bound_of_eq2_eq3_eq4 paper hr_nonneg hr_lt hcρ hρ1
    ```

    so the new chain is exercised at the seed `c_value` but the sink
    theorem is still discharged via `valid_of_eq15`.
- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`, no
  edits to `lemma.toml`, no edits to `Candidates/V0.lean` or
  `Candidates/V1.lean`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V2.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V2.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V2 scores `≥` V1 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V2.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -nE 'eq14_combined|eq15|eq5_|eq6_|eq7_|eq8_|eq9_|eq10_|eq11_|eq12_|eq13_|paperLambda|scalarCriterion|scalarIntegrand' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that those substrings appear *only* outside the body of
   `circleGap_inner_bound_of_eq2_eq3_eq4` — the new theorem's proof must use
   exactly `eq2_sigmaZeroMinus_lower`, `eq3_circleGap_decomposition`, and
   `eq4_sigmaPlus_bound` from `paper`, and nothing else from the
   `Section2Assumptions` API.
6. `grep -n 'circleGap_inner_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Candidates/V2.lean`
   returns at least one match (V2 actually invokes the new bound in its body,
   inside `v2_eq2_eq3_eq4_chain_compiles`).
7. `grep -n 'circleGap_inner_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site.

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, or any file in
  `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Integrating the new pointwise bound over `r ∈ [0, c]` to derive a
  closed-form upper bound on `diskExcess`. That is the explicit subject of a
  *future* sprint. The free parameter `ρ` must remain a `forall` here.
- Choosing a concrete `ρ(r)` (e.g. `ρ = √((1+c²)/2)` or any other tuned
  value). That is a numerical question and out of scope.
- Discharging the adjacency hypothesis from sprint 001 — that remains the
  subject of a separate follow-up sprint.
- Attempting a strictly larger `c_value` in this sprint — the goal is the
  structural new chain, not a numerical push.
- Adding new Wang-paper axioms, new oracle entries, or any new `Proposals/`
  entry. This sprint must be self-contained against the current trust
  surface.

## Time budget

≤ 90 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- The Generator finds the algebra correct but `nlinarith`/`linarith` cannot
  close the final inequality in one session: try `field_simp` + explicit
  positivity facts (`have hρ2c2 : 0 < ρ^2 - c^2 := by nlinarith`,
  `have hr2 : 0 ≤ r^2 := by positivity`, etc.) and one `nlinarith`-with-hints
  retry; if still stuck, `STATUS=BLOCKED` with the unprovable subgoal copied
  into the report.
- The proof would require a Mathlib lemma not yet in the pinned toolchain
  (e.g. an obscure inequality manipulation that has no `nlinarith` proof):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- The proof requires invoking `paper.eq{5..15}_*`, `WangOuter.paperLambda`,
  or any `Korenblum.scalar*` definition to close: `STATUS=BLOCKED` — that
  would defeat the structural novelty of this sprint and indicates the goal
  statement needs revision.
- Any of acceptance criteria 4, 5, 6, or 7 cannot be satisfied without
  weakening the contract: `STATUS=BLOCKED`.
