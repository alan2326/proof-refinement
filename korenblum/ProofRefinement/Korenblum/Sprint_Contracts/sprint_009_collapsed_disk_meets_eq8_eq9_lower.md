# Sprint 009: First cross-chain `(15)`-free reducer — sprint 007's collapsed disk upper bound meets sprint 006's `(8)+(9)` annulus lower bound

**Created**: 2026-05-02 16:00 by Planner
**Parent candidate**: `Candidates/V8.lean`
**Target file**: `Candidates/V9.lean`
**Direction**: section2-proof

## Goal

Ship one *new generic Lean theorem* in `Proof/Reduction.lean` that closes the
final-theorem contract `ValidKorenblumBound c` using a sufficient condition
expressed *purely* in `sigmaZeroMinus` and `paperLambda`, with **no
`diskExcess` or `annulusExcess` quantity ever appearing on the LHS of the
sufficient condition itself**.

```lean
theorem valid_of_collapsed_disk_eq8_eq9_lower
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ ρ₁ ρ₂ : ℝ,
          c < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c ^ 2 ∧ ρ < 1 ∧
            c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
                * PaperAxioms.sigmaZeroMinus a b ρ
              ≤ ∫ ρ' in ρ₁..ρ₂,
                  2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The proof body is a three-line stitch:

1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
2. Obtain `⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁₂, hρ₂_lt_one,
   hIntDisk, hIntCircle, hIntLambda, hSuff⟩` from `h_witness paper`.
3. Apply
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
   (sprint 007) with the disk-side witness `ρ` to get
   `diskExcess paper.circleGap c
     ≤ (c^6/6)/(ρ^2 − c^2) * sigmaZeroMinus a b ρ`.
4. Apply `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006) with the
   annulus-side window `[ρ₁, ρ₂]` to get
   `∫ ρ' in ρ₁..ρ₂, 2·(ρ')^3 · sigmaZeroMinus a b ρ' / Λ(c, ρ')
     ≤ annulusExcess paper.circleGap c`.
5. Chain via `hSuff`: the disk upper bound `≤ hSuff` `≤` the annulus lower
   bound `≤ annulusExcess`, closing the contract by `linarith` (or
   `le_trans` chained twice).

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V9.lean` at the same `c = 0.3554` that compiles,
scores `≥ V8`, and *materializes* the new cross-chain reducer in a side
lemma `v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles` exercised
against an abstract witness/integrability bundle (mirroring V4's
`v4_valid_of_eq2_eq3_eq4_annulus_budget_chain_compiles` and V8's
`v8_valid_of_eq10_subinterval_branch1_chain_compiles` patterns). The sink
theorem `korenblum_constant_search` is still discharged via `valid_of_eq15`
so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprints 002–007 built two **independent** ladders:

- **Disk side via `(2)+(3)+(4)`:** `circleGap_inner_bound_…` (sprint 002)
  → `diskExcess_upper_bound_…` (sprint 003) →
  `diskExcess_upper_bound_collapsed_single_Z_…` (sprint 007).
- **Annulus side via `(8)+(9)`:** `circleGap_outer_lower_bound_…`
  (sprint 005) → `annulusExcess_lower_bound_…` (sprint 006).

Sprint 008 opened a *separate* `(10)`-pointwise sub-interval axis. But —
critically — **no existing reducer in `Reduction.lean` chains the disk
upper bound directly with the annulus lower bound.** Every existing
`valid_of_*` reducer either:

- threads through `Korenblum.scalarCriterion` / `scalarIntegrand1` /
  `scalarIntegrand2` (the `(12)`/`(13)`/`(14)`/`(15)` family), or
- takes the entire `α·Z_c + β·Z_ρ ≤ annulusExcess` budget as an opaque
  hypothesis (sprint 004's `valid_of_eq2_eq3_eq4_annulus_budget`).

Sprint 009 produces the **first cross-chain reducer**: it consumes both
ladders simultaneously and *eliminates the opaque `annulusExcess`-side
quantity* from the sufficient-condition surface, replacing it with a
concrete integrated kernel `∫ 2(ρ')^3 · Z_{ρ'} / Λ(c, ρ')`. The resulting
sufficient condition

```text
(c^6/6)/(ρ^2 − c^2) * sigmaZeroMinus a b ρ
  ≤ ∫ ρ' in ρ₁..ρ₂, 2·(ρ')^3 · sigmaZeroMinus a b ρ' / Λ(c, ρ')
```

is the workspace's first end-to-end `(15)`-free `ValidKorenblumBound`
sufficient condition expressed **without `diskExcess` or `annulusExcess`
on the LHS** — both opaque integrals have been replaced by their
closed-form `Z_·`/`Λ` envelopes. This is qualitatively new in three ways:

1. **Cross-chain synthesis.** All prior reducers stayed inside one
   ladder. Sprint 009 stitches the `(2)+(3)+(4)` disk chain to the
   `(8)+(9)` annulus chain through one `linarith` call. This is the
   inevitable next structural move and produces the **first single-line
   composition of the two chains**.
2. **Opaque-quantity elimination.** Sprint 004's existing reducer takes
   `α·Z_c + β·Z_ρ ≤ annulusExcess` (an inequality whose RHS is the
   opaque paper integral). After sprint 009, the same closure can be
   triggered from `α·Z_c·collapsed + β·Z_ρ ≤ ∫ Z_·/Λ` (an inequality
   whose RHS is a concrete `Mathlib`-style integral over `Z_·` against
   a polynomial-and-`Λ` kernel). Equivalently: the *opaque
   `annulusExcess` premise becomes a closed-form integral premise*,
   which is then attackable by every `intervalIntegral.*` lemma in
   Mathlib.
3. **First reducer that uses sprint 007's collapse on disk side.**
   Sprint 007 ships the single-`Z` disk upper bound but is not yet
   consumed by any reducer. Sprint 009 is the first reducer to use it,
   reducing the disk-side coefficient to a single `(c^6/6)/(ρ^2 − c^2)
   · Z_ρ` term (no `Z_c` term) on the branch-split sub-regime
   `3ρ² ≤ 4c²`, which keeps the cross-chain inequality clean.

Why this is **not** a numerical push:

- The new theorem's statement is purely structural: it exposes `ρ` (the
  disk-side witness on the branch-split sub-regime), `[ρ₁, ρ₂]` (the
  annulus-side window), and the kernel inequality as
  `forall`/explicit hypotheses inside `h_witness`.
- `c_value` stays at `3554/10000`; V9 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
- The candidate side lemma is a one-line application of the new
  theorem against an *abstract* witness bundle (the candidate accepts
  the bundle as opaque assumptions and confirms it discharges the
  contract).

Why this is **bounded enough for one Generator session**:

- The proof body is genuinely tiny: one `refine` + one `obtain` + one
  application of `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
  + one application of `annulusExcess_lower_bound_of_eq8_eq9` + one
  `linarith` (or three `le_trans` calls). Estimate: ≤ 30 lines of Lean
  in `Reduction.lean`.
- No new Mathlib lemmas needed beyond what sprints 003, 006, 007 already
  use.
- The candidate side lemma is one line: invoke
  `valid_of_collapsed_disk_eq8_eq9_lower` against `c_value_pos`,
  `c_value_lt_one`, and the abstract witness hypothesis.

Why this opens a clear path to a future `c`-pushing sprint without
trust expansion:

- The kernel inequality
  `(c^6/6)/(ρ^2 − c^2) · Z_ρ
     ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 · Z_{ρ'} / Λ(c, ρ')`
  is a single scalar relation between two `sigmaZeroMinus`-weighted
  quantities and a `paperLambda` envelope. A future sprint can attack
  it by:
    (a) **Choosing the disk witness `ρ` to lie inside the annulus
        window `[ρ₁, ρ₂]`** (legal as long as `ρ ≤ branchSplit c < 1`,
        which holds at the seed `c_value` since
        `branchSplit c_value ≈ 0.4104`). Then `Z_ρ` appears on both
        sides at the same point, and one can extract a *common factor*
        of `Z_ρ` if a monotonicity lemma for `sigmaZeroMinus` becomes
        available, or use `Z_·` non-negativity (sprint 006's
        `sigmaZeroMinus_nonneg_of_pos`) plus a measure-theoretic
        lower bound on the integral.
    (b) **Bounding `paperLambda K c ρ'` from above by a constant
        `Λmax(c)`** (the paper's `WangPaperSideConditions` should
        expose such a bound; if not, this is the natural follow-up
        sprint), reducing the integrand to
        `2·(ρ')^3 · Z_{ρ'} / Λmax(c)` and rewriting the kernel
        inequality as a polynomial-weighted integral comparison.
    (c) **A registered numerical oracle returning a certified lower
        bound on the kernel integral** — first oracle in the workspace,
        with the Lean-facing axiom matching exactly the
        `(c^6/6)/(ρ^2 − c^2) · Z_ρ ≤ ∫ …` shape.
- Each route uses only the already-trusted surface plus possibly one
  registered numerical oracle — no new free-floating axiom, no new
  paper equation.

Why this is **not** a numerical-budget push in disguise:

- The witness triple `(ρ, ρ₁, ρ₂)` is exposed as a `forall` inside the
  sufficient condition, not pinned to any concrete tuple.
- The inequality `(c^6/6)/(ρ^2 − c^2) · Z_ρ ≤ ∫ 2·(ρ')^3 · Z_{ρ'}/Λ`
  is structural: both sides are closed-form expressions in
  `sigmaZeroMinus` and `paperLambda`. No numeric bounds are baked in.
- The Lean theorem is a complete reduction, not a numerical step. The
  numerical work (if any) is deferred to the sprint after this one.

Why this beats the obvious alternatives I considered:

- **A: branch-2 mirror `valid_of_eq11_subinterval_branch2`.** Would be
  a direct flavour-clone of sprint 008 on the other branch — exactly
  the "three flavours of the same chain" pattern the bulletin warns
  against. Demoted.
- **B: hybrid two-window `(10) ∨ (11)` reducer.** A generalisation of
  sprint 008 + the demoted A. Modest novelty per session; mostly
  bookkeeping. Demoted.
- **D: `paperLambda K c ρ ≤ 1` exploitation.** Would require a
  not-yet-confirmed `paperLambda_le_one` lemma in
  `WangPaperSideConditions`; without `Scratch/`-side numerical
  verification first, fragile. Better suited as a follow-up after
  sprint 009 lands the cross-chain reducer (the bulletin's "Working
  practices" section explicitly says a sprint should not commit to a
  Lean theorem without prior `Scratch/` evidence).
- **E: prove `Eq15ScalarBound` in Lean for `c = 0.3554`.** Pure
  numerical push against the existing chain — exactly what the
  bulletin de-prioritises.

Compared to B/D/E, candidate C (this sprint) maximises analytical novelty
per bounded Generator session: it uses *only existing lemmas*, produces
a structurally new sufficient condition that opens three independent
follow-up routes (a/b/c above), and extends the workspace's reducer
inventory along an axis no prior sprint has touched.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic theorem `valid_of_collapsed_disk_eq8_eq9_lower`
    matching the shape above. The proof body must:
      1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
      2. `obtain ⟨ρ, ρ₁, ρ₂, hcρ, hρ_branch, hρ1, hcρ₁, hρ₁₂,
          hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambda, hSuff⟩ :=
          h_witness paper`.
      3. `have hDisk :=
            diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
              paper hc_pos hcρ hρ_branch hρ1 hIntDisk` (sprint 007).
      4. `have hAnn :=
            annulusExcess_lower_bound_of_eq8_eq9
              paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambda`
            (sprint 006).
      5. `linarith [hDisk, hSuff, hAnn]` to close
         `diskExcess paper.circleGap c
            ≤ annulusExcess paper.circleGap c`.

  - The new theorem's body must NOT mention
    `paper.eq{2,3,4,5,6,8,9,10,11,12,13}_*`,
    `paper.eq14_combined`, `paper.eq15_*`,
    `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
    `Korenblum.scalarIntegrand2`, `valid_of_eq15`, `valid_of_eq12_eq13`,
    `valid_of_eq2_eq3_eq4_annulus_budget`,
    `valid_of_eq10_subinterval_branch1`,
    `eq15_implies_disk_le_annulus`,
    `circleGap_inner_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4` (the *uncollapsed* sprint
    003 version — the collapsed sprint 007 version is the only allowed
    disk-side bound),
    `circleGap_outer_lower_bound_of_eq8_eq9` (the pointwise sprint 005
    version — the integrated sprint 006 version is the only allowed
    annulus-side bound),
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    `sigmaZeroMinus_nonneg_of_pos`. The *only* existing-workspace
    reducer machinery the new theorem may invoke directly is
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` (sprint
    007) and `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006).
    `paper.eq7_paperK_formula` MAY appear if and only if it is
    transitively required by the integrability hypotheses inside
    sprint 006's premises (it is not — sprint 006 takes integrability
    as an explicit premise).

  - Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 009 is the **first cross-chain reducer**,
    stitching sprint 007's collapsed disk upper bound on the
    branch-split sub-regime `3ρ² ≤ 4c²` to sprint 006's `(8)+(9)`
    annulus lower bound on a free window `[ρ₁, ρ₂] ⊆ (c, 1)`. The
    resulting sufficient condition is the workspace's first
    `ValidKorenblumBound c` premise expressed *purely in `sigmaZeroMinus`
    and `paperLambda`* (no `diskExcess` or `annulusExcess` opaque
    quantity on the LHS), opening three independent follow-up routes
    (closed-form `paperLambda` envelope, common-factor `Z_ρ`
    extraction with the disk witness inside the annulus window, or a
    registered numerical-integration oracle).

- `ProofRefinement/Korenblum/Candidates/V9.lean`:
  - `-- @parent V8`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3/V4/V5/V6/V7/V8).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly
    as in V1/V2/V3/V4/V5/V6/V7/V8; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does
    not regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ ρ₁ ρ₂ : ℝ,
              c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 ∧
                c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                IntervalIntegrable
                  (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c_value 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
                    * PaperAxioms.sigmaZeroMinus a b ρ
                  ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                        / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_collapsed_disk_eq8_eq9_lower
        c_value_pos c_value_lt_one h_witness
    ```

    so the new cross-chain reducer is exercised at the seed `c_value`
    against an abstract witness bundle, but the sink theorem is still
    discharged via `valid_of_eq15`. The side lemma must NOT be
    `axiom`-ed and must NOT call the seed axiom. It exists purely to
    verify that the new reduction chain typechecks at the seed
    `c_value`.

  - Additionally, prove a tiny structural witness lemma confirming
    that the sub-regime constraint `3ρ² ≤ 4c_value²` is non-vacuous at
    the seed (i.e. there exists `ρ` with `c_value < ρ < 1` and
    `3ρ² ≤ 4c_value²`):

    ```lean
    theorem v9_branch_split_witness_at_seed :
        ∃ ρ : ℝ, c_value < ρ ∧ 3 * ρ ^ 2 ≤ 4 * c_value ^ 2 ∧ ρ < 1 := by
      refine ⟨4 / 10, ?_, ?_, ?_⟩ <;>
        · simp [c_value]; norm_num
    ```

    (Sanity check: `c_value = 0.3554`, `4 · c_value² = 4 · 0.12631 ≈
    0.5052`, `3 · 0.4² = 3 · 0.16 = 0.48 ≤ 0.5052`, and `0.3554 < 0.4 <
    1`. The witness lemma is local to V9 and is not used elsewhere —
    its purpose is to demonstrate that the disk-side witness component
    of the new theorem's `h_witness` premise is non-vacuous at the
    seed `c_value`.)

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V8.lean`.

### Note on the disk witness ρ vs. the annulus window [ρ₁, ρ₂]

The contract above keeps the disk witness `ρ` and the annulus window
`[ρ₁, ρ₂]` as **independent free parameters**. This is the cleanest
first move: the cross-chain reducer must not assume a particular
relationship between them. A future sprint that *does* impose
`ρ ∈ [ρ₁, ρ₂]` to extract a common `Z_ρ` factor is the natural
follow-up. Locking the relationship now would forfeit the structural
generality of the cross-chain composition.

### Note on integrability premises

The contract takes three integrability hypotheses (`hIntDisk`,
`hIntCircle`, `hIntLambda`) packed into `h_witness`. This mirrors
sprint 003 (`hInt`), sprint 006 (`hIntCircle`, `hIntLambda`), and
sprint 008 (`hIntDensity`)'s pattern of leaving `circleGap`/`Z_·`/`Λ`
integrability as explicit premises rather than deriving them from
`Section2Assumptions`. Deriving any of them in-house from the paper
surface is the subject of a separate sprint (continuity of
`circleGap`, `sigmaZeroMinus`, and `paperLambda` from
`Section2Assumptions`). Keeping them explicit here keeps the sprint
self-contained against the current trust surface.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V9.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V9.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V9 scores `≥` V8 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V9.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains:
   - exactly one use of
     `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
     (sprint 007),
   - exactly one use of `annulusExcess_lower_bound_of_eq8_eq9`
     (sprint 006),
   - and at least one `linarith` (or three `le_trans`) chaining the
     two bounds against the witness inequality.
6. `grep -n 'valid_of_collapsed_disk_eq8_eq9_lower' korenblum/ProofRefinement/Korenblum/Candidates/V9.lean`
   returns at least one match (V9 actually invokes the new reduction in
   its body, inside `v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles`).
7. The body of `valid_of_collapsed_disk_eq8_eq9_lower` does NOT mention
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
   `paper.eq7_paperK_formula` (NB: stricter than sprint 008 — sprint 009
   is a pure stitch over sprint 006 + sprint 007, and neither of those
   directly references `eq7_paperK_formula` in their *output* signature),
   `paper.eq8_`, `paper.eq9_`, `paper.eq10_`, `paper.eq11_`,
   `paper.eq12_`, `paper.eq13_`, `paper.eq14_combined`, `paper.eq15_`,
   `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
   `Korenblum.scalarIntegrand2`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`,
   `valid_of_eq10_subinterval_branch1`,
   `eq15_implies_disk_le_annulus`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4` (the *uncollapsed* version),
   `circleGap_outer_lower_bound_of_eq8_eq9` (the *pointwise* version),
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   `sigmaZeroMinus_nonneg_of_pos`. The *only* allowed in-workspace
   references are
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` and
   `annulusExcess_lower_bound_of_eq8_eq9`. Verify with
   `grep -nE` against the substring of the theorem body. (If
   `eq7_paperK_formula` *is* required because Mathlib's
   `IntervalIntegrable` glue forces some downstream of sprint 006 to
   surface it, document the deviation in the report and mark
   `STATUS=BLOCKED` if the deviation cannot be removed.)
8. `grep -n 'diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes sprint 007 at least once (the new
   `valid_of_collapsed_disk_eq8_eq9_lower` body must contain a match in
   addition to sprint 007's own definition site).
9. `grep -n 'annulusExcess_lower_bound_of_eq8_eq9' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   shows that the new theorem invokes sprint 006 at least once (the new
   `valid_of_collapsed_disk_eq8_eq9_lower` body must contain a match in
   addition to sprint 006's own definition site).
10. `grep -n 'v9_branch_split_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V9.lean`
    returns exactly one definition site (the small structural witness
    lemma confirming the disk-side branch-split sub-regime is
    non-vacuous at the seed `c_value`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, `Candidates/V4.lean`, `Candidates/V5.lean`,
  `Candidates/V6.lean`, `Candidates/V7.lean`, `Candidates/V8.lean`, or any
  file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
- Discharging *any* of the three integrability premises (`hIntDisk`,
  `hIntCircle`, `hIntLambda`) from `Section2Assumptions`. They are
  intentionally taken as explicit premises packed into `h_witness`,
  mirroring sprints 003, 006, 008. Deriving any of them in-house is
  the subject of a separate sprint.
- Discharging the kernel inequality
  `(c^6/6)/(ρ^2 − c^2) · Z_ρ
     ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 · Z_{ρ'} / Λ(c, ρ')`
  itself. That is the explicit subject of a future sprint (numerical
  oracle, `paperLambda` envelope, or common-`Z_ρ` factor extraction;
  see "Why" section, paragraph on future `c`-pushing routes).
- Choosing any concrete `(ρ, ρ₁, ρ₂)` triple beyond the V9 witness
  lemma `v9_branch_split_witness_at_seed` (which only verifies the
  disk-side `ρ`-coordinate is non-vacuous; the annulus-side
  `(ρ₁, ρ₂)` and the kernel inequality are NOT discharged). The free
  parameters must remain `forall`-quantified inside `h_witness` —
  sprint 009 must not commit to any particular witness policy.
- Adding a *common-`Z_ρ`-factor* variant that imposes
  `ρ ∈ [ρ₁, ρ₂]`. That is a clean follow-up sprint but should be
  queued separately to keep this sprint single-axis (the unconstrained
  cross-chain reducer comes first).
- Adding a *branch-2* variant that uses sprint 003's full uncollapsed
  bound on `ρ ∈ (branchSplit c, 1)` instead of sprint 007's
  branch-split-collapsed bound. Sprint 007 explicitly identified
  `(c, branchSplit c]` as the only sub-regime where the `Z_c`
  coefficient flips sign favorably; using the uncollapsed bound on
  branch 2 would re-introduce the `Z_c` term and complicate the
  cross-chain inequality. Strictly branch-1 / branch-split sub-regime
  in this sprint.
- Pushing `c_value` upward in this sprint — the goal is the structural
  cross-chain reducer, not a numerical push. Any future sprint that
  *does* push `c` is expected to consume
  `valid_of_collapsed_disk_eq8_eq9_lower` by proving the kernel
  inequality at the new `c`.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
- Refactoring or simplifying sprints 001–008. Their lemmas are consumed
  verbatim (sprint 009 only *adds* one new theorem and one V9 candidate).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via `valid_of_collapsed_disk_eq8_eq9_lower`. That
  requires proving the kernel inequality at the seed `c_value`,
  which is the subject of a future sprint.
- Extending the sub-regime `3ρ² ≤ 4c²` to allow `ρ` slightly above
  `branchSplit c` (which would re-introduce the `Z_c` term).
  Strictly branch-split sub-regime in this sprint.
- Removing any of the three explicit `IntervalIntegrable` premises.
  The whole point of taking them as explicit hypotheses is to keep
  this sprint independent of any future continuity/measurability work
  on `circleGap`, `sigmaZeroMinus`, or `paperLambda`.

## Time budget

≤ 30 minutes runtime. The new theorem is genuinely small: ~15–25 lines
of Lean, since both heavy lifters (sprint 006 and sprint 007) are
already in `Reduction.lean` with the correct premise shape. The proof
body is essentially one `obtain`, two named `have`s (one per ladder),
and one `linarith`. The candidate side lemma is one line. The
structural witness lemma is ~3 lines.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Sprint 007's
  `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`'s premise
  shape does not match the new theorem's witness shape (e.g. it
  requires `IntervalIntegrable` on `[0, c]` with a different functional
  form than `(fun r => 2 * r * PaperAxioms.circleGap a b r)`):
  re-read sprint 007's signature in `Reduction.lean` and adjust the
  `h_witness` shape in the new theorem to match exactly. If the shape
  cannot be made to match without rewriting sprint 007 itself,
  document the mismatch in the report and mark `STATUS=BLOCKED`.
- Sprint 006's `annulusExcess_lower_bound_of_eq8_eq9`'s premise shape
  does not match (e.g. it requires the `Λ` integrand integrability on
  a different interval than `[ρ₁, ρ₂]`): re-read sprint 006's
  signature in `Reduction.lean` and adjust accordingly. Same
  fallback as the previous bullet.
- The `linarith` at step 5 cannot close the chain because the disk
  upper bound and the annulus lower bound do not share a common
  `sigmaZeroMinus` evaluation point: this is *expected* — the
  contract intentionally keeps `ρ` (disk witness) and `[ρ₁, ρ₂]`
  (annulus window) independent, and the `h_witness`-supplied
  `hSuff : (c^6/6)/(ρ^2 − c^2) · Z_ρ ≤ ∫ 2(ρ')^3·Z_{ρ'}/Λ` is the
  bridge. `linarith [hDisk, hSuff, hAnn]` should close the chain
  via transitivity. If `linarith` fails, fall back to three explicit
  `le_trans` applications.
- The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat the
  cross-chain novelty of this sprint and indicates the contract needs
  revision.
- The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
- The structural witness lemma `v9_branch_split_witness_at_seed`
  fails to close with `simp [c_value]; norm_num`: try `decide` on
  each conjunct individually, or fall back to explicit
  `norm_num [c_value]` plus a manual `nlinarith`. If that still
  fails, fall back to taking the witness existence as an
  un-discharged hypothesis on
  `v9_valid_of_collapsed_disk_eq8_eq9_lower_chain_compiles` and
  *not* providing the witness lemma — flag this as a partial
  discharge in the report.
- Any of acceptance criteria 4, 5, 6, 7, 8, 9, or 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
