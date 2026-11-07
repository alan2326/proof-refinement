# Sprint 007: Single-`Z` collapse of sprint 003's disk-side upper bound on the branch-split sub-regime

**Created**: 2026-05-02 13:30 by Planner
**Parent candidate**: `Candidates/V6.lean`
**Target file**: `Candidates/V7.lean`
**Direction**: section2-proof

## Goal

Ship one *new generic Lean theorem* in `Proof/Reduction.lean` that strictly
refines sprint 003's two-`Z`-point disk-side upper bound into a **single-`Z`
upper bound** on `diskExcess` whenever the free parameter `ρ` lies in the
branch-split sub-regime `c < ρ ∧ 3·ρ² ≤ 4·c²` (equivalently
`ρ ∈ (c, (2/√3)·c]`, which is exactly the lower branch
`(c, branchSplit c]`):

```lean
theorem diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hcρ : c < ρ)
    (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c ^ 2)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
        * PaperAxioms.sigmaZeroMinus a b ρ
```

The theorem statement intentionally has **only `Z_ρ`** on the right; the
`Z_c` term from sprint 003 is dropped because its coefficient
`α(c, ρ) := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is `≤ 0` on the branch-split
sub-regime (the numerator factor `3ρ²−4c²ρ` is non-positive, and the
denominator `ρ²−c²` is positive), and `Z_c ≥ 0` by sprint 006's
`sigmaZeroMinus_nonneg_of_pos`.

The proof body must consume **exactly**:

- `diskExcess_upper_bound_of_eq2_eq3_eq4` (sprint 003) at the same `ρ`,
- `sigmaZeroMinus_nonneg_of_pos` (sprint 006) applied at `c` (with
  `hc_pos`),
- arithmetic / `linarith` / `nlinarith`.

It must NOT reference any `paper.eq{2,3,4,5,6,7,8,9,10,11,12,13}_*` field,
must NOT reference `paper.eq14_combined`, must NOT reference any
`paper.eq15_*` field, must NOT reference `Korenblum.scalarCriterion`,
`Korenblum.scalarIntegrand{1,2}`, `valid_of_eq15`, `valid_of_eq12_eq13`,
`valid_of_eq2_eq3_eq4_annulus_budget`, `eq15_implies_disk_le_annulus`,
`circleGap_inner_bound_of_eq2_eq3_eq4`, `circleGap_outer_lower_bound_of_eq8_eq9`,
`annulusExcess_lower_bound_of_eq8_eq9`, `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
or `OneModePaperBridge.*` directly. Sprint 003 and sprint 006's
`sigmaZeroMinus_nonneg_of_pos` already wrap those dependencies; the new
theorem talks to them only through these two existing entry points.

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V7.lean` at the same `c = 0.3554` that compiles,
scores `≥ V6`, and *materializes* the new bound in a side lemma
`v7_diskExcess_collapsed_single_Z_chain_compiles` exercised against an
abstract integrability premise (mirroring V3's
`v3_diskExcess_upper_bound_chain_compiles` and V6's
`v6_annulusExcess_lower_bound_chain_compiles` patterns). The sink
theorem is still discharged via `valid_of_eq15` so the score does not
regress.

## Why

The bulletin's current priority is *novel analytical chains* that build
toward an end-to-end `(15)`-free reduction. After sprint 006, the workspace
has:

- a closed-form *upper* bound on `diskExcess` from `(2)+(3)+(4)` (sprint
  003) — but it has **two** `Z`-evaluation points (`Z_c` and `Z_ρ`),
- a closed-form *lower* bound on `annulusExcess` from `(8)+(9)` (sprint
  006) — its integrand has **one** `Z`-evaluation point (`Z_ρ` at the
  integration variable),
- the end-to-end seed-free reduction `valid_of_eq2_eq3_eq4_annulus_budget`
  (sprint 004) — which requires closing the budget
  `(disk-side α·Z_c + β·Z_ρ at one ρ) ≤ (annulus-side ∫_{ρ₁}^{ρ₂} ...)`.

The structural obstruction to closing sprint 004's budget at the seed
`c = 0.3554` is the **disk-side `Z_c` term**: it sits at the *inner*
radius `c`, while the annulus side never integrates `Z` at `c`. There is
no general inequality of the form `Z_c ≤ (integral of Z_ρ at varying ρ)`
for arbitrary admissible `(a, b)`. Sprint 007's collapse trick **eliminates
the `Z_c` term entirely** in the branch-split sub-regime
`(c, branchSplit c]`, by exploiting that sprint 003's `Z_c` coefficient
`α(c, ρ) = (c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-positive precisely there
(numerator non-positive, denominator strictly positive), so combining with
`Z_c ≥ 0` (a one-line corollary of sprint 006's already-proved
`sigmaZeroMinus_nonneg_of_pos`) lets us drop the entire `α·Z_c` term and
keep only `β·Z_ρ`.

Why this is **structurally novel**:

- It is the **first workspace theorem that produces a single-`Z` upper bound
  on `diskExcess`**. Every prior disk-side bound (sprints 002, 003) carries
  both `Z_c` and `Z_ρ`. Single-`Z` is a qualitatively new shape.
- It exposes a **structural link between sprint 003's coefficient algebra
  and Wang's branch split `branchSplit c = √(4/3)·c`**. The exact threshold
  `3ρ² ≤ 4c²` ↔ `ρ ≤ branchSplit c` is the same threshold that splits
  Wang's scalar criterion into `scalarIntegrand1` and `scalarIntegrand2`.
  Sprint 007 makes this connection a Lean theorem, exposing for the first
  time that the lower branch is geometrically distinguished by collapsing
  the `Z_c` coefficient in the `(2)+(3)+(4)` upper bound.
- It is **directly chainable with sprint 006**: a future sprint can pick
  `ρ ∈ (c, branchSplit c]`, apply sprint 007 to dominate `diskExcess` by
  `(c⁶/6)/(ρ²−c²)·Z_ρ`, and then apply sprint 006 with `[ρ₁, ρ₂]` chosen
  as a tiny window around `ρ` to lower-bound `annulusExcess` by an
  integral of `2ρ'³·Z_{ρ'}/Λ(c,ρ')` near the same `Z_ρ`. The remaining
  gap between the two single-`Z` quantities then becomes a question
  about *one* `Z`-radius `ρ` rather than two, which is the deepest
  structural simplification possible without invoking the seed `(15)`.
- The dependency signature is fundamentally distinct from any prior
  sprint: it consumes `(2)+(3)+(4)` (via sprint 003) and the `(8)+(9)`-
  derived `sigmaZeroMinus_nonneg_of_pos` (via sprint 006), but in a
  fundamentally new combination — *cancelling* a coefficient using the
  identity-derived non-negativity facts rather than *integrating* them.

Why this is **not a numerical push**:

- No `c`-tuning, no choice of concrete `ρ`, no concrete numbers in the
  generic theorem statement. The constraint `3ρ² ≤ 4c²` is exposed as a
  hypothesis on the free parameter.
- `c_value` stays at `3554/10000`; V7 still discharges the sink theorem
  via `valid_of_eq15` so the score is exactly preserved at `1777/5000`.
- The "numerics" are entirely absent from the generic theorem; only the
  V7 side lemma instantiates a concrete admissible `ρ` (e.g. `ρ = 41/100`)
  to confirm the constraint is non-vacuous at the seed `c_value`.

Why this is **bounded enough for one Generator session**:

- The proof has at most ~25 lines:
  1. `have hupperFromSprint003 := diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt`,
  2. `have hZc_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c := sigmaZeroMinus_nonneg_of_pos a b hc_pos`,
  3. positivity facts: `0 < ρ²−c²` (`nlinarith`), `0 ≤ 3ρ²−4c² → false` (since hypothesis says the negation),
  4. compute the `Z_c`-coefficient `α := (c⁴/6)·(3ρ²−4c²)/(ρ²−c²) ≤ 0`
     by `div_nonpos_of_nonpos_of_nonneg` or by `nlinarith`,
  5. compute `α · Z_c ≤ 0` by `mul_nonpos_of_nonpos_of_nonneg hα hZc_nonneg`,
  6. chain `diskExcess ≤ α·Z_c + β·Z_ρ ≤ 0 + β·Z_ρ = β·Z_ρ` by `linarith`.
- The candidate side lemma is a one-line application of the new bound at
  `c_value = 3554/10000` against an abstract `ρ` constrained by the
  branch-split inequality.
- No new Mathlib plumbing (no `intervalIntegral.*`, no measure theory,
  no `tsum`, no `mono_set`) — pure algebra.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`:
  - Add the new generic theorem
    `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` matching
    the shape above. The proof must:
      1. Establish `0 < ρ ^ 2 - c ^ 2` from `hc_pos` and `hcρ` (use
         `nlinarith [sq_nonneg (ρ - c), sq_nonneg (ρ + c), hcρ, hc_pos]`
         or similar).
      2. Invoke
         `hUpper := diskExcess_upper_bound_of_eq2_eq3_eq4 paper hc_pos hcρ hρ1 hInt`
         to obtain the two-`Z` upper bound:
         `diskExcess ≤ (c^4/6)*(3ρ^2 - 4c^2)/(ρ^2 - c^2)*Z_c + (c^6/6)/(ρ^2 - c^2)*Z_ρ`.
      3. Invoke
         `hZc_nonneg := sigmaZeroMinus_nonneg_of_pos a b hc_pos`
         to obtain `0 ≤ PaperAxioms.sigmaZeroMinus a b c`.
      4. Show `(3*ρ^2 - 4*c^2) ≤ 0` from `hρ_branch` (`linarith`).
      5. Show the `Z_c` coefficient
         `α := (c^4/6)*(3*ρ^2 - 4*c^2)/(ρ^2 - c^2) ≤ 0` by combining
         the numerator non-positivity with the denominator positivity:
         `mul_nonpos_iff.mpr` or
         `div_nonpos_of_nonpos_of_nonneg` (Mathlib has both; pick the
         one that matches the `(numerator/denominator)*` shape) plus
         `mul_nonpos_of_nonneg_of_nonpos` for the leading `(c^4/6) ≥ 0`.
         A direct `nlinarith [sq_nonneg c, sq_nonneg ρ, hρ_branch, ...]`
         should also close it if the lemma names don't match cleanly.
      6. Conclude `α * Z_c ≤ 0` by
         `mul_nonpos_of_nonpos_of_nonneg hα hZc_nonneg`.
      7. Chain `diskExcess ≤ α * Z_c + β * Z_ρ ≤ 0 + β * Z_ρ = β * Z_ρ`
         by `linarith`.
      8. Must NOT reference `paper.eq{2,3,4,5,6,7,8,9,10,11,12,13}_*`,
         `paper.eq14_combined`, `paper.eq15_*`,
         `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand{1,2}`,
         `valid_of_eq15`, `valid_of_eq12_eq13`,
         `valid_of_eq2_eq3_eq4_annulus_budget`,
         `eq15_implies_disk_le_annulus`,
         `circleGap_inner_bound_of_eq2_eq3_eq4`,
         `circleGap_outer_lower_bound_of_eq8_eq9`,
         `annulusExcess_lower_bound_of_eq8_eq9`,
         `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, or
         `OneModePaperBridge.*` (since sprint 003 and sprint 006's
         `sigmaZeroMinus_nonneg_of_pos` already wrap these).

  - Add a one-line module-doc comment above the new theorem explaining:
    sprint 007 is the single-`Z` collapse of sprint 003's two-`Z` upper
    bound, valid on the branch-split sub-regime `(c, branchSplit c]`,
    derived by combining sprint 003 with sprint 006's
    `sigmaZeroMinus_nonneg_of_pos` to drop the `Z_c` term whose
    coefficient is non-positive there. Note that the threshold
    `3ρ² ≤ 4c²` is exactly the same as `ρ ≤ branchSplit c =
    √(4/3)·c`, exposing for the first time that Wang's branch split is
    geometrically distinguished by collapsing the `Z_c` coefficient in
    the `(2)+(3)+(4)` disk-side upper bound.

- `ProofRefinement/Korenblum/Candidates/V7.lean`:
  - `-- @parent V6`.
  - Set `def c_value : ℝ := 3554 / 10000` (same as V0/V1/V2/V3/V4/V5/V6).
  - Reuse the seed axiom name `hEq15_seed_3554` (declare locally, exactly
    as in V1/V2/V3/V4/V5/V6; the seed-axiom token is already in
    `lemma.toml:[seed_axioms].allowed`).
  - Prove the final sink theorem via `valid_of_eq15` (so the score does
    not regress).
  - Additionally, prove a *verifying* side lemma

    ```lean
    theorem v7_diskExcess_collapsed_single_Z_chain_compiles
        {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value)
        {ρ : ℝ}
        (hcρ : c_value < ρ)
        (hρ_branch : 3 * ρ ^ 2 ≤ 4 * c_value ^ 2)
        (hρ1 : ρ < 1)
        (hInt :
          IntervalIntegrable
            (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
        PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
          (c_value ^ 6 / 6) / (ρ ^ 2 - c_value ^ 2)
            * PaperAxioms.sigmaZeroMinus a b ρ :=
      diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4
        paper c_value_pos hcρ hρ_branch hρ1 hInt
    ```

    so the new chain is exercised at the seed `c_value` against an
    abstract `ρ` constrained by the branch-split inequality. The side
    lemma must NOT be `axiom`-ed and must NOT call the seed axiom. It
    exists purely to verify that the new bound typechecks at the seed
    `c_value`.

  - Additionally, prove a small numeric witness lemma confirming the
    branch-split constraint is non-vacuous at the seed `c_value`:

    ```lean
    theorem v7_branch_split_witness_at_seed :
        c_value < 41 / 100 ∧ 3 * (41 / 100 : ℝ) ^ 2 ≤ 4 * c_value ^ 2 := by
      refine ⟨?_, ?_⟩ <;> norm_num [c_value]
    ```

    (Sanity check: `c_value = 0.3554`, `branchSplit c_value =
    √(4/3)·0.3554 ≈ 0.41036`, so `ρ = 41/100 = 0.41 ∈ (c_value,
    branchSplit c_value]`. The witness lemma is local to V7 and is not
    used elsewhere — its purpose is to demonstrate that the
    branch-split sub-regime is non-empty at the seed `c_value`, so the
    new bound has a non-trivial domain of applicability.)

- No edits to `Proof/CandidateContract.lean`, no edits to `Proof/Main.lean`,
  no edits to `Proof/ProblemAxioms.lean`, no edits to `KorenblumPaper/*`,
  no edits to `lemma.toml`, no edits to `Candidates/V0.lean`–`V6.lean`.

## Acceptance criteria

1. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_lake_build.sh Candidates/V7.lean` succeeds.
2. `bash korenblum/ProofRefinement/Korenblum/scripts/korenblum_eval_candidate.sh Candidates/V7.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V7 scores `≥` V6 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V7.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build emits
   them) — no new free-floating axioms.
5. `grep -n 'diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns exactly one definition site, and the body of that theorem
   contains a use of `diskExcess_upper_bound_of_eq2_eq3_eq4` and a use of
   `sigmaZeroMinus_nonneg_of_pos`.
6. `grep -n 'diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4' korenblum/ProofRefinement/Korenblum/Candidates/V7.lean`
   returns at least one match (V7 actually invokes the new bound in its
   body, inside `v7_diskExcess_collapsed_single_Z_chain_compiles`).
7. The body of `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`
   does NOT mention `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
   `paper.eq6_`, `paper.eq7_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`,
   `paper.eq11_`, `paper.eq12_`, `paper.eq13_`, `paper.eq14_combined`,
   `paper.eq15_`, `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`, `eq15_implies_disk_le_annulus`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `annulusExcess_lower_bound_of_eq8_eq9`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, or
   `OneModePaperBridge`. (Verify with `grep -nE` against the substring of
   the theorem body.)
8. `grep -n 'v7_branch_split_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V7.lean`
   returns exactly one definition site (the small numeric witness lemma
   confirming the branch-split sub-regime is non-empty at `c_value`).

## Out of scope

- Changing `c_value` away from `3554 / 10000`.
- Editing `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
  `Candidates/V3.lean`, `Candidates/V4.lean`, `Candidates/V5.lean`,
  `Candidates/V6.lean`, or any file in `KorenblumPaper/`.
- Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
- Discharging the `IntervalIntegrable` premise from `Section2Assumptions`.
  The integrability hypothesis is intentionally taken as an explicit
  premise, mirroring sprints 003 and 006. Deriving it from
  `Section2Assumptions` (which would require a continuity result for
  `circleGapSeries`) is the subject of a *future* sprint.
- Choosing concrete `ρ` in the generic theorem (e.g. `ρ = (1+c)/2`,
  `ρ = (2/√3)·c` exactly, …). The free parameter `ρ` must remain a
  `forall` here, subject only to the branch-split constraint
  `3·ρ² ≤ 4·c²`.
- Closing sprint 004's annulus budget hypothesis from `Section2Assumptions`
  using the new collapsed bound. That requires comparing the single-`Z`
  upper bound `(c⁶/6)/(ρ²−c²)·Z_ρ` against sprint 006's integral lower
  bound `∫_{ρ₁}^{ρ₂} 2ρ'³·Z_{ρ'}/Λ(c,ρ') dρ'`, which still requires a
  pointwise comparison of `Z_ρ` against `Z_{ρ'}` for `ρ' ≈ ρ` — a
  separate analytical move that is NOT in scope for sprint 007.
- Pushing `c_value` upward in this sprint — the goal is the single-`Z`
  collapse, not a numerical push. Any future sprint that *does* push
  `c` is expected to consume
  `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4` alongside
  sprint 006's lower bound and sprint 004's
  `valid_of_eq2_eq3_eq4_annulus_budget`.
- Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
- Refactoring or simplifying sprints 001–006. Their lemmas are consumed
  verbatim (sprint 007 only *adds* one new theorem and one V7 candidate).
- Replacing the seed `valid_of_eq15` discharge of the sink theorem with
  a `(2)+(3)+(4)+(8)+(9)`-only proof. That requires bridging
  `(c⁶/6)/(ρ²−c²)·Z_ρ ≤ annulusExcess` and is beyond this sprint.
- Deriving an analogous "collapsed `Z_ρ`" upper bound on sprint 003's
  *other* coefficient (the `Z_ρ` term has a strictly positive
  coefficient on the entire admissible region, so collapsing it is
  algebraically impossible — the collapse is one-sided, only the `Z_c`
  side admits it, and only on `(c, branchSplit c]`).

## Time budget

≤ 60 minutes runtime. The new theorem is ~25 lines of pure algebra (no
measure theory, no `tsum`, no integration). The candidate side lemma is
one line. The witness lemma is two lines. Most of the time will be in
picking the right Mathlib lemma name for "if `numerator ≤ 0` and
`denominator > 0` then `numerator/denominator ≤ 0`" and for "if
`a ≤ 0` and `b ≥ 0` then `a*b ≤ 0`".

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- The "numerator non-positive divided by denominator positive ⇒ quotient
  non-positive" step does not match a single Mathlib lemma name: fall
  back to `div_nonpos.mpr (Or.inl ⟨hNum, hDen.le⟩)` /
  `div_nonpos_of_nonpos_of_nonneg` /
  `div_nonpos_iff` (depending on Mathlib version), or close the entire
  coefficient non-positivity step with a single
  `nlinarith [sq_nonneg c, sq_nonneg ρ, hρ_branch, hc_pos.le, hcρ.le,
  pow_pos hc_pos 2, pow_pos (lt_trans hc_pos hcρ) 2]`.
- The "non-positive times non-negative ⇒ non-positive product" step is
  `mul_nonpos_of_nonpos_of_nonneg` in Mathlib 4 (signature:
  `(h1 : a ≤ 0) (h2 : 0 ≤ b) : a * b ≤ 0`); if the name has shifted in
  the pinned toolchain, use `mul_nonpos_iff.mpr (Or.inr ⟨hα, hZc⟩)` or
  fall back to `nlinarith [hα, hZc_nonneg]`.
- The chain `diskExcess ≤ α·Z_c + β·Z_ρ ≤ 0 + β·Z_ρ = β·Z_ρ` should
  close with a single `linarith` once `hUpper`, `hα * Z_c ≤ 0`, and the
  positivity of `β · Z_ρ` are in scope. If `linarith` rejects the
  rewrites, expand to a `calc` block mirroring sprint 003's final
  `calc`.
- The branch-split positivity `0 < ρ² − c²` follows from
  `hcρ : c < ρ` and `0 < c`: use
  `nlinarith [hcρ, hc_pos, sq_nonneg (ρ - c), sq_nonneg (ρ + c)]` or
  derive `c² < ρ²` via `sq_lt_sq'` then `linarith`.
- The proof would require `paper.eq{2,3,4,5,6,7,8,9,10,11,12,13,14,15}_*`,
  `Korenblum.scalar*`, `valid_of_eq15`, `valid_of_eq12_eq13`,
  `valid_of_eq2_eq3_eq4_annulus_budget`,
  `circleGap_inner_bound_of_eq2_eq3_eq4`,
  `circleGap_outer_lower_bound_of_eq8_eq9`,
  `annulusExcess_lower_bound_of_eq8_eq9`,
  `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, or
  `OneModePaperBridge.*` directly: `STATUS=BLOCKED` — sprint 003 and
  sprint 006's `sigmaZeroMinus_nonneg_of_pos` already wrap these, and
  the whole point of the sprint is to consume only those two existing
  entry points.
- The witness lemma `v7_branch_split_witness_at_seed` fails to close
  with `norm_num [c_value]`: try
  `refine ⟨?_, ?_⟩ <;> simp [c_value] <;> norm_num` or compute the
  inequalities manually
  (`c_value = 3554/10000 = 0.3554`,
  `41/100 = 0.41 > 0.3554`,
  `3 * (41/100)^2 = 3 * 1681/10000 = 5043/10000 = 0.5043`,
  `4 * c_value^2 = 4 * (3554/10000)^2 = 4 * 12630916/100000000 =
  50523664/100000000 = 0.50523664`,
  so `0.5043 ≤ 0.50523664` ✓). If `norm_num` chokes on the squaring,
  expand `c_value` once first via `unfold c_value` or
  `show … < 41 / 100`.
- Any of acceptance criteria 4, 5, 6, 7, or 8 cannot be satisfied
  without weakening the contract: `STATUS=BLOCKED`.
