# Sprint 003: Integrate sprint 002's pointwise inner bound into a closed-form `diskExcess` upper bound

**Created**: 2026-05-02 14:30 by Planner
**Parent candidate**: `Candidates/V2.lean`
**Target file**: `Candidates/V3.lean`
**Direction**: section2-proof

## Goal

Ship a *new generic Lean theorem*

```text
diskExcess_upper_bound_of_eq2_eq3_eq4 :
    {a b : ℕ → ℂ} → {K : ℝ → ℝ → ℝ} → {c : ℝ} →
    (paper : Section2Assumptions a b K c) →
    {ρ : ℝ} →
    0 < c → c < ρ → ρ < 1 →
    IntervalIntegrable (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c →
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b c
        + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
          * PaperAxioms.sigmaZeroMinus a b ρ
```

in `Proof/Reduction.lean`. The proof must:

1. Invoke the existing `circleGap_inner_bound_of_eq2_eq3_eq4` (sprint 002) at
   each `r ∈ [0, c)` with the supplied `ρ`, multiply by `2 * r ≥ 0` to preserve
   the inequality, and integrate over `r ∈ [0, c]`.
2. Reduce the integrated upper bound to closed form by computing the two scalar
   integrals
     `∫_0^c 2r · (c² − r²·(ρ²−r²)/(ρ²−c²)) dr = (c⁴/6)·(3ρ² − 4c²)/(ρ²−c²)`
   and
     `∫_0^c 2r · r²·((c² − r²)/(ρ²−c²)) dr = (c⁶/6)/(ρ²−c²)`
   using `intervalIntegral.integral_pow`,
   `intervalIntegral.integral_const_mul`,
   `intervalIntegral.integral_add`, and `ring`/`field_simp` to land on the
   stated coefficients. The denominator `ρ² − c² > 0` follows from `c < ρ`,
   so `field_simp` is safe.
3. **Not** use `paper.eq{5,6,7,8,9,10,11,12,13,14}_*`, `paper.eq15_*`,
   `WangOuter.paperLambda`, `Korenblum.scalarCriterion`, or
   `Korenblum.scalarIntegrand{1,2}`. The only `paper`-API touched in the proof
   is the chain through `circleGap_inner_bound_of_eq2_eq3_eq4` (which itself
   uses only `paper.eq{2,3,4}_*` per sprint 002).

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V3.lean` at the same `c = 0.3554` that compiles, scores
`≥` V2, and *materializes* the new chain by using
`diskExcess_upper_bound_of_eq2_eq3_eq4` somewhere in its closure — even if V3
ultimately falls back to `valid_of_eq15` for the final sink theorem (e.g. as a
verified side lemma `v3_diskExcess_upper_bound_chain_compiles` that exercises
the new bound on the seed paper context with an explicit
`IntervalIntegrable` hypothesis).

## Why

This is the *natural* downstream sprint to sprint 002. Sprint 002 explicitly
left this integration step as out-of-scope and exposed the free parameter `ρ`
as a `forall` precisely so this sprint could integrate at fixed `ρ` against
the polar Jacobian `2r`.

Why this is **structurally novel**, not a numerical push:

- Both prior sprints (001, 002) and the seed all reduce
  `diskExcess ≤ annulusExcess` via the `(15)` route — i.e. they multiply the
  scalar criterion by `diskExcess` and bound the result by `annulusExcess`.
  After this sprint, we have a *direct closed-form upper bound* on
  `diskExcess` itself, in terms of the two scalar quantities
  `sigmaZeroMinus a b c` and `sigmaZeroMinus a b ρ` evaluated at one inner and
  one outer radius. That is a fundamentally different reduction shape: it
  attacks the *left-hand side* of the Korenblum inequality with a closed
  form, rather than the right-hand side via integrated kernels.
- Once this lemma is in `Reduction.lean`, a *future* sprint can chain it with
  the `(8)+(9)`-derived bridge `sigmaMinus ρ ≤ Λ(c,ρ) · circleGap ρ` (already
  exposed as `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` in `PaperAxioms.lean`)
  and with the relation `sigmaMinus ρ = ρ² · sigmaZeroMinus ρ` (or the
  `sigmaZeroMinus ρ` ≤ `sigmaMinus ρ / ρ²` direction once justified) to
  produce a wholly new sufficient condition for
  `diskExcess ≤ annulusExcess` that is **not** Wang's `(15)`. That is a
  prerequisite for any candidate that proves a strictly larger `c_value`
  *without* a new `(15)`-style scalar axiom.
- Zero new free axioms, zero new oracle entries, zero `Section2Assumptions`
  expansions, zero new `Proposals/` entries. The sprint is self-contained
  against the current trust surface. The integrability premise on
  `paper.circleGap` is intentionally left as an *explicit hypothesis* of
  the new reduction (mirroring sprint 001's adjacency hypothesis) so that
  the next sprint can attack it as a separate question — for example by
  proving integrability under a hypothesis exposed via
  `paper.eq3_circleGap_decomposition` or by extending
  `Section2Assumptions`.

The closed-form coefficients
  `α(c, ρ) := (c⁴/6) · (3ρ² − 4c²)/(ρ² − c²)`
and
  `β(c, ρ) := (c⁶/6)/(ρ² − c²)`
are elementary rational functions of `c` and `ρ`. Their derivation from
`∫_0^c 2r dr = c²`, `∫_0^c 2r³ dr = c⁴/2`, `∫_0^c 2r⁵ dr = c⁶/3` is purely
algebraic and bounded.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add new generic theorem `diskExcess_upper_bound_of_eq2_eq3_eq4` matching
    the shape above. The proof must:
    1. Use `circleGap_inner_bound_of_eq2_eq3_eq4` (sprint 002) to obtain the
       pointwise bound on `paper.circleGap r` for each `r ∈ [0, c)`. Since
       the conclusion is an integral over `[0, c]` and the bound holds on
       `[0, c)` (a set differing by a single point of measure zero), use
       `intervalIntegral.integral_mono_ae` (or a pointwise variant on `[0, c)`
       extended via almost-everywhere equality) plus the supplied
       integrability hypothesis on `fun r => 2 * r * paper.circleGap r`.
    2. Compute the two scalar integrals explicitly with
       `intervalIntegral.integral_add`, `intervalIntegral.integral_const_mul`,
       `intervalIntegral.integral_pow`, and `ring` / `field_simp` (with
       `have hρ2c2 : 0 < ρ ^ 2 - c ^ 2 := by nlinarith` to discharge the
       denominator-nonzero side condition).
    3. Land on the stated closed-form bound. The final
       `field_simp` + `ring` step should close the algebraic equality between
       the integrated upper bound and the stated coefficient form.
  - The new theorem's body must NOT mention `paper.eq14_combined`,
    `paper.eq15_*`, `paper.eq{5,6,7,8,9,10,11,12,13}_*`,
    `WangOuter.paperLambda`, `Korenblum.scalarCriterion`,
    `Korenblum.scalarIntegrand{1,2}`, or `WangPaperSideConditions.*`.
  - Add a one-line module-doc comment above the new theorem explaining that
    this is the Sprint 003 integrated form of sprint 002's pointwise bound,
    that the free parameter `ρ` is intentionally exposed for downstream
    optimisation, and that the integrability hypothesis on
    `2r · paper.circleGap r` is intentionally left as a hypothesis pending
    a future sprint that derives it from `Section2Assumptions`.

- `ProofRefinement/Korenblum/Candidates/V3.lean`:
  - `-- @parent V2`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly as
    in V1/V2; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does not
    regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v3_diskExcess_upper_bound_chain_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ : ℝ}
        (hcρ : c_value < ρ)
        (hρ1 : ρ < 1)
        (hInt : IntervalIntegrable
                  (fun r => 2 * r * PaperAxioms.circleGap a b r)
                  volume 0 c_value) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          (c_value ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c_value ^ 2)
              / (ρ ^ 2 - c_value ^ 2)
              * PaperAxioms.sigmaZeroMinus a b c_value
            + (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
              * PaperAxioms.sigmaZeroMinus a b ρ :=
      diskExcess_upper_bound_of_eq2_eq3_eq4 paper c_value_pos hcρ hρ1 hInt
    ```

    so the new chain is exercised at the seed `c_value` but the sink theorem
    is still discharged via `valid_of_eq15`.

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`, no
  edits to `lemma.toml`, no edits to `Candidates/V0.lean`, `V1.lean`, or
  `V2.lean`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V3.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V3.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V3 scores `≥` V2 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V3.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -nE 'eq14_combined|eq15|eq5_|eq6_|eq7_|eq8_|eq9_|eq10_|eq11_|eq12_|eq13_|paperLambda|scalarCriterion|scalarIntegrand|WangPaperSideConditions' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that those substrings appear *only* outside the body of
   `diskExcess_upper_bound_of_eq2_eq3_eq4` — the new theorem's proof must use
   exactly `circleGap_inner_bound_of_eq2_eq3_eq4` plus elementary
   `intervalIntegral.*` and arithmetic tactics.
6. `grep -n 'diskExcess_upper_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Candidates/V3.lean`
   returns at least one match (V3 actually invokes the new bound in its body,
   inside `v3_diskExcess_upper_bound_chain_compiles`).
7. `grep -n 'diskExcess_upper_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site.
8. `grep -n 'circleGap_inner_bound_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes sprint 002's lemma (i.e. there are at
   least two matches — the original definition site and at least one use
   inside `diskExcess_upper_bound_of_eq2_eq3_eq4`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`, or
  any file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Discharging the `IntervalIntegrable` hypothesis on
  `2r · paper.circleGap r` from `Section2Assumptions`. That is the explicit
  subject of a *future* sprint. The hypothesis must remain explicit on
  `diskExcess_upper_bound_of_eq2_eq3_eq4` here.
- Choosing a concrete `ρ(c)` (e.g. `ρ = √((1+c²)/2)` or any tuned value) and
  evaluating the closed-form bound numerically. That is the subject of a
  *future* sprint and out of scope for this sprint.
- Combining the new closed-form bound with any annulus-side lower bound to
  produce a candidate sufficient condition for
  `diskExcess ≤ annulusExcess`. That is also a future-sprint question. The
  free parameter `ρ` must remain a `forall` here.
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
- The Generator finds the algebra correct but cannot match the closed-form
  coefficient `(c⁴/6)·(3ρ² − 4c²)/(ρ²−c²)` exactly because of how
  `field_simp` normalises the rational expression: try restating the
  conclusion using a normalised form (e.g. multiply through by `6·(ρ²−c²)`
  on both sides as an intermediate step) and then `linarith`-close the
  resulting polynomial inequality. If still stuck, `STATUS=BLOCKED` with the
  unprovable subgoal copied into the report.
- The proof requires `intervalIntegral.integral_mono_ae` with an
  almost-everywhere hypothesis the Generator cannot construct without an
  `ae_restrict_iff'` step against `Set.Ioo 0 c` (sprint 002's bound is on
  `r < c`, not `r ≤ c`): use `Measure.restrict_congr_set Ioo_ae_eq_Icc`
  exactly as in `Reduction.lean`'s existing `annulusExcess_nonneg` — that
  pattern is already in this file and known to work.
- The proof requires invoking `paper.eq{5..15}_*`, `WangOuter.paperLambda`,
  or any `Korenblum.scalar*` definition to close: `STATUS=BLOCKED` — that
  would defeat the structural novelty of this sprint and indicates the goal
  statement needs revision.
- The proof would require a Mathlib lemma not yet in the pinned toolchain
  (e.g. an obscure rational-coefficient integral identity that has no
  `intervalIntegral.integral_pow` proof): `STATUS=BLOCKED_NEEDS_HUMAN`.
- Any of acceptance criteria 4, 5, 6, 7, or 8 cannot be satisfied without
  weakening the contract: `STATUS=BLOCKED`.
