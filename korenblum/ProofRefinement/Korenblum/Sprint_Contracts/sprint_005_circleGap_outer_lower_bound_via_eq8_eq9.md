# Sprint 005: Annulus-side pointwise lower bound on `2ρ · circleGap ρ` via `(8)+(9)` and the `sigmaMinus = ρ²·sigmaZeroMinus` identity

**Created**: 2026-05-02 11:30 by Planner
**Parent candidate**: `Candidates/V4.lean`
**Target file**: `Candidates/V5.lean`
**Direction**: section2-proof

## Goal

Ship two *new generic Lean theorems* in `Proof/Reduction.lean`:

1. A pure series identity

   ```text
   sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus :
       (a b : ℕ → ℂ) → (s : ℝ) →
       PaperAxioms.sigmaMinus a b s = s ^ 2 * PaperAxioms.sigmaZeroMinus a b s
   ```

   relating Wang's two coefficient series. Provable termwise: `n2Pred a b k`
   forces `0 < k`, so for the only contributing `k` we have
   `s^(2*k) = s^2 * s^(2*k - 2)`; the `k = 0` summands vanish on both sides,
   so `tsum_congr` plus `pow_mul`/`pow_add` arithmetic plus
   `tsum_mul_left` closes the equality without any positivity assumption on
   `s` and without requiring summability hypotheses (the equality holds in
   `ℝ`'s `tsum` even when both series diverge — they sum to `0` by Mathlib
   convention, and the termwise equality forces the sums to agree).

2. The annulus-side pointwise lower bound

   ```text
   circleGap_outer_lower_bound_of_eq8_eq9 :
       {a b : ℕ → ℂ} → {K : ℝ → ℝ → ℝ} → {c : ℝ} →
       (paper : Section2Assumptions a b K c) →
       {ρ : ℝ} → 0 < c → c < ρ → ρ < 1 →
       2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
           / WangOuter.paperLambda K c ρ
         ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
   ```

   This is the *symmetric counterpart* of sprint 002's inner-disk pointwise
   upper bound. The proof must route through:
     - `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
        paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap` to obtain
       `sigmaMinus a b ρ ≤ Λ(c,ρ) · paper.circleGap ρ`;
     - the new identity from (1) to rewrite the LHS as
       `ρ² · sigmaZeroMinus a b ρ ≤ Λ(c,ρ) · paper.circleGap ρ`;
     - `WangPaperSideConditions.paperLambda_pos` to divide through by
       `Λ(c,ρ) > 0` and obtain
       `ρ² · sigmaZeroMinus a b ρ / Λ(c,ρ) ≤ paper.circleGap ρ`;
     - multiply both sides by `2ρ ≥ 0` (from `0 < c < ρ`) to land on the
       stated form.

   The new theorem's body must NOT mention `paper.eq{2,3,4,5,6,7,10,11,12,
   13,14,15}_*`, `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand{1,2}`,
   or any `WangPaperSideConditions.*` other than `paperLambda_pos`.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V5.lean` at the same `c = 0.3554` that compiles, scores
`≥` V4, and *materializes* the new chain by using
`circleGap_outer_lower_bound_of_eq8_eq9` somewhere in its closure — even if V5
ultimately falls back to `valid_of_eq15` for the final sink theorem (e.g. as a
verified side lemma `v5_circleGap_outer_lower_bound_chain_compiles` that
exercises the new bound on the seed paper context).

## Why

The bulletin's current priority is *novel analytical derivations*, ideally
through a chain that sets up an end-to-end `(15)`-free reduction. Sprints
002–004 built the entire **inner-disk side**:

  - sprint 002: pointwise `circleGap r` upper bound on `r ∈ [0, c)`;
  - sprint 003: integrated `diskExcess` upper bound on `[0, c]`;
  - sprint 004: end-to-end reduction lifting that upper bound to
    `ValidKorenblumBound c`, modulo an existential annulus-side budget
    hypothesis.

Sprint 004 deliberately accepted the budget hypothesis
`α(c,ρ) · Z_c + β(c,ρ) · Z_ρ ≤ annulusExcess paper.circleGap c` as an
explicit premise. The natural next question is: **can we lower-bound
`annulusExcess` from `Section2Assumptions` alone?** The answer must come
from the *outer* annulus side, which has not been touched by any prior
sprint. The (8)+(9) bridge is already in `OneModePaperBridge`/`PaperAxioms`,
and gives `sigmaMinus ρ ≤ Λ(c,ρ) · circleGap ρ`. To turn that into a lower
bound on the annulus integrand `2ρ · circleGap ρ` in terms of
`sigmaZeroMinus ρ` (matching the variables used by sprint 003's upper
bound), we need the structural identity `sigmaMinus = ρ² · sigmaZeroMinus`.

Why this is **structurally novel**:

- Every prior sprint's analytical work happens on the *inner disk*. This is
  the **first workspace theorem that produces an annulus-side pointwise
  bound** — that is, a bound on the integrand of `annulusExcess` on the
  open interval `(c, 1)`.
- The `sigmaMinus = ρ² · sigmaZeroMinus` identity is **not exposed
  anywhere in `Section2Assumptions` or `OneModePaperBridge`**. It is a
  consequence of the *definitions* of the two coefficient series (because
  `n2Pred` requires `0 < k`), but it has never been proved in the
  workspace. Once landed, downstream sprints can freely interconvert the
  two normalizations.
- The chain `eq8 → eq9 → sigmaMinus = ρ²·sigmaZeroMinus → ÷ Λ(c,ρ)` is a
  fundamentally different route from any prior sprint's. Sprints 001–004
  use either `(15)` (which routes through `paperLambda` integrated into
  the scalar criterion) or `(2)+(3)+(4)` (purely inner-side, no
  `paperLambda` dependence). This sprint introduces `paperLambda` as a
  *pointwise denominator* on the annulus side — a new dependency
  signature.

Why this is **not a numerical push**:

- No `c`-tuning, no choice of `ρ`, no integration. The new theorems are
  purely structural identities and inequalities.
- `c_value` stays at `3554/10000`; V5 still discharges the sink theorem
  via `valid_of_eq15` so the score is exactly preserved at `1777/5000`.
- The only "numerical" content is `paperLambda > 0`, which is already a
  Lean theorem in `WangPaperSideConditions` and is consumed verbatim.

Why this opens a **clear path to closing sprint 004's budget without
`(15)`**:

The annulus integrand lower bound

  `2ρ · circleGap ρ ≥ 2ρ³ · sigmaZeroMinus ρ / Λ(c,ρ)`

integrates over any sub-interval `[ρ₁, ρ₂] ⊆ (c, 1)` to a lower bound on
`annulusExcess`:

  `annulusExcess ≥ ∫_{ρ₁}^{ρ₂} 2ρ³ · sigmaZeroMinus ρ / Λ(c,ρ) dρ`.

A future sprint can then:

  (a) integrate the new pointwise bound over a chosen sub-interval (sprint
      006-style, mirroring sprint 003's polar integration), producing a
      generic *integrated* annulus lower bound; or
  (b) at the candidate level, choose `ρ*` close to `c` so that
      `sigmaZeroMinus ρ*` is comparable to `sigmaZeroMinus c` (via the
      already-trusted `eq2`) and dominate sprint 003's `α·Z_c + β·Z_ρ*`
      upper bound by a sub-interval mass.

Either route closes sprint 004's budget hypothesis using only `(2), (3),
(4), (8), (9)` — no `Eq15`, no `paperLambda`-integrated `scalarCriterion`,
no seed axiom. That is the strategic payoff: this sprint is the
**structural prerequisite** for the first end-to-end Korenblum proof in
the workspace that does not depend on `hEq15_seed_*`.

Why this is **bounded enough for one Generator session**:

- Theorem (1) is at most ~25 lines: `sigmaMinus_eq_sigmaSeq` and
  `sigmaZeroMinus`'s definition unfold to `tsum`s; the proof is
  `tsum_congr` (or `Summable.tsum_eq` after a `tsum_mul_left`) plus a
  `by_cases h : n2Pred a b k` split. The `k = 0` branch is closed by
  `simp [n2Pred]` (since `n2Pred a b 0 = (0 < 0 ∧ ...)` is `False`); the
  `0 < k` branch is closed by `pow_mul` / `Nat.sub_add_cancel`-style
  arithmetic on the exponent and `ring`.
- Theorem (2) is at most ~15 lines: invoke
  `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`, rewrite by theorem (1),
  divide by `Λ > 0` via `div_le_iff₀`, multiply by `2ρ ≥ 0` via
  `mul_le_mul_of_nonneg_left`. All tactics already used in `Reduction.lean`
  or in `OneModePaperBridge.lean`.
- The candidate side lemma is a one-line application.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic identity `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
    at the top level (i.e. not gated on `Section2Assumptions`). The proof
    must:
      1. Unfold `PaperAxioms.sigmaMinus` and `PaperAxioms.sigmaZeroMinus`
         to their `∑'` definitions.
      2. Rewrite `s ^ 2 * (∑' k, ...) = ∑' k, s ^ 2 * (...)` via
         `tsum_mul_left` (or `mul_tsum`-style lemma; if neither matches
         the goal shape exactly, use `tsum_congr` after pulling `s^2`
         inside the if-then-else).
      3. Apply `tsum_congr` and split on `PaperAxioms.n2Pred a b k`:
           - `n2Pred = false`: both `if`s collapse to `0`; close by `simp`.
           - `n2Pred = true`: extract `0 < k` from the `n2Pred` conjunction;
             rewrite `s^(2*k) = s^2 * s^(2*k - 2)` using
             `pow_add`/`pow_mul`/`Nat.sub_add_cancel` (with the `k ≥ 1`
             hypothesis to discharge `2 ≤ 2*k`), then close by `ring`.
      4. Must NOT use any `paper.*` field — this is a definitional identity
         about `sigmaMinus` and `sigmaZeroMinus`, not about `Section2Assumptions`.
  - Add the new generic theorem `circleGap_outer_lower_bound_of_eq8_eq9`
    matching the shape above. The proof must:
      1. Apply `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
         paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap hcρ hρ1`
         to obtain `hBridge : sigmaMinus a b ρ ≤ Λ(c,ρ) · paper.circleGap ρ`.
      2. Rewrite `sigmaMinus a b ρ` via the new identity from step (1) to
         `ρ² · sigmaZeroMinus a b ρ`.
      3. Use `WangPaperSideConditions.paperLambda_pos` to obtain
         `hΛpos : 0 < Λ(c,ρ)`.
      4. Divide through to get
         `ρ² · sigmaZeroMinus a b ρ / Λ(c,ρ) ≤ paper.circleGap ρ`
         via `div_le_iff₀ hΛpos`.
      5. Multiply both sides by `2ρ ≥ 0` (using `0 < c < ρ` for `0 < ρ`
         hence `0 ≤ 2ρ`) via `mul_le_mul_of_nonneg_left`.
      6. Close by `ring`-style rearrangement of
         `2ρ · (ρ² · Z_ρ / Λ) = 2ρ³ · Z_ρ / Λ`.
  - The new theorem's body must NOT mention `paper.eq14_combined`,
    `paper.eq15_*`, `paper.eq{2,3,4,5,6,7,10,11,12,13}_*`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand{1,2}`, or any
    `WangPaperSideConditions.*` other than `paperLambda_pos`.
  - Add a one-line module-doc comment above each new theorem explaining
    that:
      - `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` is the Sprint 005 series
        identity that lets us interconvert Wang's two coefficient
        normalizations on the outer annulus side;
      - `circleGap_outer_lower_bound_of_eq8_eq9` is the Sprint 005 outer
        pointwise lower bound — the structural counterpart of sprint 002's
        inner pointwise upper bound — and is the prerequisite for any
        future sprint that closes sprint 004's annulus budget without
        `Eq15`.

- `ProofRefinement/Korenblum/Candidates/V5.lean`:
  - `-- @parent V4`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3/V4).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly as
    in V1/V2/V3/V4; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does not
    regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v5_circleGap_outer_lower_bound_chain_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ : ℝ}
        (hcρ : c_value < ρ)
        (hρ1 : ρ < 1) :
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c_value ρ
          ≤ 2 * ρ * PaperAxioms.circleGap a b ρ :=
      circleGap_outer_lower_bound_of_eq8_eq9 paper c_value_pos hcρ hρ1
    ```

    so the new chain is exercised at the seed `c_value` but the sink
    theorem is still discharged via `valid_of_eq15`. The side lemma must
    NOT be `axiom`-ed and must NOT call the seed axiom.

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`, no
  edits to `lemma.toml`, no edits to `Candidates/V0.lean`, `V1.lean`,
  `V2.lean`, `V3.lean`, or `V4.lean`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V5.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V5.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V5 scores `≥` V4 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V5.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site.
6. `grep -n 'circleGap_outer_lower_bound_of_eq8_eq9' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains a use of `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` and a use of
   `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`.
7. `grep -n 'circleGap_outer_lower_bound_of_eq8_eq9' korenblum/ProofRefinement/Korenblum/Candidates/V5.lean`
   returns at least one match (V5 actually invokes the new bound in its body,
   inside `v5_circleGap_outer_lower_bound_chain_compiles`).
8. The body of `circleGap_outer_lower_bound_of_eq8_eq9` does NOT mention
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
   `paper.eq7_`, `paper.eq10_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
   `paper.eq14_combined`, `paper.eq15_`, `Korenblum.scalarCriterion`,
   `Korenblum.scalarIntegrand`, `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`, or
   `eq15_implies_disk_le_annulus`. (Verify with `grep -nE` against the
   substring of the theorem body.)
9. The body of `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` does NOT reference
   any `paper.*` field at all (it is a definitional identity about
   `sigmaMinus` and `sigmaZeroMinus`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, `Candidates/V4.lean`, or any file in
  `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new import
  allowances).
- Integrating the new pointwise lower bound over `ρ ∈ [c, 1]` to derive a
  closed-form lower bound on `annulusExcess`. That is the explicit subject
  of a *future* sprint (sprint 006 candidate). The free parameter `ρ` must
  remain a `forall` here.
- Choosing a concrete `ρ*` (e.g. `ρ = √((1+c²)/2)` or any tuned value).
  That is a numerical question and out of scope.
- Discharging sprint 004's budget hypothesis from `Section2Assumptions`.
  That requires the integrated form (future sprint).
- Discharging the `IntervalIntegrable` hypothesis on
  `2ρ · paper.circleGap ρ` on `[0, c]` or on `[c, 1]`. That is also a
  future-sprint question.
- Attempting a strictly larger `c_value` in this sprint — the goal is the
  structural new chain, not a numerical push.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
- Refactoring or simplifying sprints 001, 002, 003, or 004. Their lemmas
  are consumed verbatim (sprint 005 only *adds* new theorems).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem with a
  `(2)+(3)+(4)+(8)+(9)`-only proof. That is the strategic payoff of the
  *next* sprint, not this one.

## Time budget

≤ 90 minutes runtime. The two new theorems are short; most of the budget
will be spent on the `tsum`/`pow_mul`/`Nat.sub_add_cancel` arithmetic in
theorem (1) and on the `div_le_iff₀` chain in theorem (2).

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Theorem (1)'s `tsum_congr`/`tsum_mul_left` step does not match Mathlib's
  exact lemma name (Mathlib has both `tsum_mul_left` and the direct
  `(tsum_congr ...).trans` shape): try the alternative form
  `congr 1; ext k; ...` after a `simp only [PaperAxioms.sigmaMinus,
  PaperAxioms.sigmaZeroMinus]` unfold, then handle the if-then-else
  branches and `pow_add` arithmetic. If still stuck, `STATUS=BLOCKED` with
  the exact unprovable subgoal copied into the report.
- Theorem (1) requires a summability hypothesis to commute `s^2 *` with
  `tsum`: in `ℝ`, Mathlib's `tsum_mul_left` does not require summability
  (it agrees on both sides via the divergent → `0` convention). If the
  Generator hits a missing summability lemma, try
  `tsum_mul_left` / `tsum_const_smul` directly with no hypothesis; if
  Mathlib insists on summability, fall back to a termwise rewrite under
  `tsum_congr` followed by extraction of the `s^2` factor inside the
  conditional itself (i.e. prove
  `(if n2Pred then g_k * s^(2k) else 0) = s^2 * (if n2Pred then g_k * s^(2k-2) else 0)`
  for each `k` and then `tsum_congr` to conclude). If still stuck,
  `STATUS=BLOCKED`.
- Theorem (2)'s `div_le_iff₀` direction is reversed (the bridge gives
  `LHS ≤ Λ · circleGap`, we want `LHS / Λ ≤ circleGap`): use
  `(div_le_iff₀ hΛpos).mpr` with a `mul_comm` to align, exactly as the
  pattern in `eq10_of_eq5_eq8_eq9` in `KorenblumPaper.PaperAxioms`. If
  that pattern still fails, `STATUS=BLOCKED` with the unprovable subgoal
  copied into the report.
- The proof of theorem (2) requires invoking `paper.eq{2,3,4,5,6,7,10,11,
  12,13,14,15}_*`, `Korenblum.scalar*`, `valid_of_eq15`, or any other
  reduction theorem to close: `STATUS=BLOCKED` — that would defeat the
  structural novelty of this sprint and indicates the contract needs
  revision.
- The proof would require a Mathlib lemma not yet in the pinned toolchain
  (e.g. an obscure `tsum`/`pow` identity that has no direct counterpart):
  `STATUS=BLOCKED_NEEDS_HUMAN`.
- Any of acceptance criteria 4, 5, 6, 7, 8, or 9 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
