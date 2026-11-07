# Sprint 022: `(2)+(3)+(4)`-derived branch-2 disk bound `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` — the workspace's **first disk-side bound on the branch-2 sub-regime that is *not* derived from `paper.eq6_branch2_sigmaReduction`**, the **first paper-internal cross-validation that the printed equation `(6)` is algebraically subsumed by `(2)+(3)+(4)` plus a single application of `Z`-monotonicity on `(branchSplit c, 1)`**, and the **first workspace lemma whose disk-side `Z_c → Z_ρ` collapse is justified by sprint 011's series monotonicity rather than by an axiomatic paper hypothesis**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V21.lean`
**Target file**: `Candidates/V22.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c : ℝ}
    (paper : Section2Assumptions a b K c)
    {ρ : ℝ}
    (hc_pos : 0 < c)
    (hρ_split : PaperAxioms.branchSplit c ≤ ρ)
    (hρ1 : ρ < 1)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c)
    (hSummable_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0)) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      (c ^ 4 / 2) * PaperAxioms.sigmaZeroMinus a b ρ
```

The bound `(c⁴/2) · Z_ρ` is **algebraically identical** to the closed form
of sprint 016's `diskExcess_upper_bound_via_eq6` after the paper kernel
collapse `branch2SigmaKernel c ρ · ρ² = c⁴/(2ρ²) · ρ² = c⁴/2`. What
changes is the **derivation chain**: instead of consuming
`paper.eq6_branch2_sigmaReduction` directly (sprint 016's chain), sprint 022's
proof body **re-derives** the same closed-form bound from sprint 003's
two-`Z` integrated bound `diskExcess_upper_bound_of_eq2_eq3_eq4` (which
consumes `paper.eq2_sigmaZeroMinus_lower`,
`paper.eq3_circleGap_decomposition`, and `paper.eq4_sigmaPlus_bound`),
then collapses the `Z_c` term into `Z_ρ` via sprint 011's
`sigmaZeroMinus_monotone_of_summable` on the branch-2 sub-regime where
sprint 003's `Z_c` coefficient `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is
non-negative.

The full proof body is short and entirely algebraic on top of sprint 003 +
sprint 011:

1. **Apply sprint 003.** `diskExcess_upper_bound_of_eq2_eq3_eq4 paper
   hc_pos hc_lt_one hρcρ' hρ'1 hInt` (with `ρ' = ρ`, where
   `hc_lt_one : c < 1` follows from `hρ_split : branchSplit c ≤ ρ`
   together with `hρ1 : ρ < 1` and the elementary fact
   `c ≤ branchSplit c` proved via `c·1 ≤ c·√(4/3)` from
   `1 ≤ √(4/3)`) gives the two-`Z` bound

   ```lean
   diskExcess (circleGap a b) c ≤
     (c ^ 4 / 6) * (3 * ρ ^ 2 - 4 * c ^ 2) / (ρ ^ 2 - c ^ 2)
       * sigmaZeroMinus a b c
     + (c ^ 6 / 6) / (ρ ^ 2 - c ^ 2)
       * sigmaZeroMinus a b ρ.
   ```

2. **Branch-2 sub-regime gives `Z_c` coefficient ≥ 0.** From
   `branchSplit c ≤ ρ` (i.e. `c·√(4/3) ≤ ρ`) deduce `4c² ≤ 3ρ²` (square
   both sides, multiply by 3, use `(√(4/3))² = 4/3`), so
   `3ρ² − 4c² ≥ 0`. Combined with `ρ² − c² > 0` (from `c < ρ`,
   established via `c < branchSplit c ≤ ρ`), the `Z_c` coefficient
   `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-negative.

3. **Sprint 011 collapse `Z_c ≤ Z_ρ`.** Apply
   `sigmaZeroMinus_monotone_of_summable hc_pos.le hcρ.le hSummable_ρ`
   (where `hcρ : c < ρ` was already established at step 2) to obtain
   `Z_c ≤ Z_ρ`. Since the `Z_c` coefficient is `≥ 0`, multiplying gives

   ```lean
   (c⁴/6)·(3ρ²−4c²)/(ρ²−c²) · Z_c ≤ (c⁴/6)·(3ρ²−4c²)/(ρ²−c²) · Z_ρ.
   ```

4. **Combine the two `Z_ρ` summands and verify the algebraic identity.**
   The combined coefficient is

   ```text
   (c⁴/6)·(3ρ²−4c²)/(ρ²−c²) + (c⁶/6)/(ρ²−c²)
     = [c⁴·(3ρ²−4c²) + c⁶] / (6·(ρ²−c²))
     = [3c⁴ρ² − 4c⁶ + c⁶] / (6·(ρ²−c²))
     = [3c⁴ρ² − 3c⁶] / (6·(ρ²−c²))
     = 3c⁴·(ρ²−c²) / (6·(ρ²−c²))
     = c⁴/2.
   ```

   Discharge this in Lean via `field_simp [ne_of_gt hρ²minusc²pos]; ring`
   on a single `have hCoeff : … = c^4 / 2 := by …` step.

5. **Final calc chain.** Compose sprint 003's bound, the `Z_c → Z_ρ`
   collapse, the algebraic identity, to obtain
   `diskExcess ≤ (c⁴/2) · Z_ρ`.

No new paper axioms are consumed beyond what sprint 003 + sprint 011
already pull (`eq2`, `eq3`, `eq4`, plus the series-summability hypothesis
at `ρ`). **No invocation of `paper.eq6_branch2_sigmaReduction` anywhere
in the proof body.**

Then ship a `Candidates/V22.lean` at the same `c = 0.3554` that compiles,
scores `≥ V21`, and *materialises* the new lemma in side lemmas
`v22_disk_bound_eq2_eq3_eq4_branch2_compiles` and
`v22_branch2_witness_at_seed` (the second exhibits a concrete `ρ`
strictly above `branchSplit c_value ≈ 0.4103`, e.g. `ρ = 0.5`, where the
new bound applies — it does **not** numerically discharge the
summability premise, which remains an existential premise on the
generic lemma). The sink theorem `korenblum_constant_search` is still
discharged via `valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 022 ships a structurally novel disk-side bound along
three independent axes that no prior workspace sprint touches:

1. **First disk-side bound on the branch-2 sub-regime that does *not*
   consume `paper.eq6_branch2_sigmaReduction`.** Sprint 016 is the only
   workspace lemma that produces `(c⁴/2) · Z_ρ` on `(branchSplit c, 1)`;
   its proof body invokes `paper.eq6_branch2_sigmaReduction` as the sole
   paper hypothesis (`Reduction.lean:1894-1895`). Sprint 022 produces
   the **same closed-form bound** with a **disjoint paper-axiom
   signature** `{eq2, eq3, eq4}` instead of `{eq6}`. This is the
   workspace's first paper-internal cross-validation that
   `(2)+(3)+(4) ⊢ branch-2 collapse to (c⁴/2)·Z_ρ` — i.e., that Wang's
   printed equation `(6)` is **algebraically a consequence** of
   `(2)+(3)+(4)` plus `Z`-monotonicity on the branch-2 sub-regime, not
   an additional structural assumption.

   Cross-check this against sprint 019's pattern: sprint 019 was the
   workspace's first sub-interval reducer to re-derive `(10)` from
   `(5)+(8)+(9)` instead of consuming `eq10_branch1_pointwise` directly.
   Sprint 022 is the **dual** move — re-deriving the branch-2
   *integrated* disk bound (`(6)`'s consequence after the
   `sigmaMinus = ρ²·Z` identity) from the *upstream*
   `(2)+(3)+(4)`-chain, on the branch-2 sub-regime where the
   collapse is valid.

2. **First workspace lemma whose disk-side `Z_c → Z_ρ` collapse is
   discharged by sprint 011's series monotonicity rather than by an
   axiomatic paper hypothesis.** Every prior closing reducer that
   invokes sprint 011 (sprints 014/017/021) uses it on the **annulus
   side** to bridge `Z_anchor ≤ Z_ρ'` for `ρ' ∈ [ρ₁, ρ₂]`. Sprint 022
   is the first to use sprint 011 on the **disk side** — to collapse
   the `Z_c` summand in sprint 003's two-`Z` bound into the same `Z_ρ`
   the second summand already carries, *eliminating* the two-`Z`
   structure in favour of a single-`Z_ρ` bound. This is a structurally
   distinct use of sprint 011: previous uses bridge anchor-to-window;
   sprint 022 bridges disk-anchor-to-disk-anchor at the same `ρ`.

3. **First paper-internal verification that sprint 003's `Z_c`
   coefficient `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)` is non-negative on the
   branch-2 sub-regime, complementing sprint 007's verification that
   the same coefficient is non-positive on the branch-1 sub-regime.**
   Sprint 007 (`Reduction.lean:597`) collapses sprint 003 in the
   *opposite* direction: on `(c, branchSplit c]` where `3ρ²−4c² ≤ 0`,
   the `Z_c` coefficient is non-positive, so the whole `Z_c` summand
   can be **dropped** (using `Z_c ≥ 0`) to give a single-`Z_ρ` bound
   `(c⁶/6)/(ρ²−c²) · Z_ρ`. Sprint 022 collapses sprint 003 in the
   complementary direction: on `[branchSplit c, 1)` where
   `3ρ²−4c² ≥ 0`, the `Z_c` coefficient is non-negative, so the `Z_c`
   summand can be **upper-bounded** (using `Z_c ≤ Z_ρ` from sprint 011)
   to merge with the second summand. **Together, sprints 007 and 022
   exhaust the two algebraic regimes of sprint 003's two-`Z` bound**,
   producing matching single-`Z_ρ` collapses on the two halves of
   `(c, 1)`. Both bounds are derived from the same `(2)+(3)+(4)` chain
   but use *opposite* signs of the `Z_c` coefficient.

   Notably: sprint 007's branch-1 collapse gives `(c⁶/6)/(ρ²−c²)·Z_ρ`,
   which is **strictly tighter than** what sprint 015's `(5)`-based
   bound `branch1SigmaKernel c ρ · ρ²·Z_ρ = (c⁶/6)·ρ²/(ρ²·(ρ²−c²))·Z_ρ
   = (c⁶/6)/(ρ²−c²)·Z_ρ` produces. *(The two are in fact equal,
   confirming sprint 015's bulletin entry that `(5)` is the integrated
   form of `(eq2+eq3+eq4)` on the branch-1 sub-regime.)* Sprint 022's
   collapse gives `(c⁴/2)·Z_ρ`, **equal to** sprint 016's `(6)`-based
   bound. So sprint 022 closes the workspace's sprint-007/sprint-016
   cross-check: the `(2)+(3)+(4)` chain **exactly reproduces both
   `(5)` and `(6)`** in their respective sub-regimes, with the
   branch-split radius as the algebraic crossover where the `Z_c`
   coefficient changes sign.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V22 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form disk-side
  upper bound parameterised by a single radial knob `ρ ∈
  [branchSplit c, 1)`, with the same closed form as sprint 016 but
  derived from a *different* set of paper hypotheses.
* No concrete numerical tuple is committed beyond a one-line witness
  lemma exhibiting a concrete `ρ` in the admissible sub-regime at the
  seed — the summability premise at `ρ` remains an existential
  premise on the new lemma.

Why this is **not** "the same chain" as sprint 016:

* **Disjoint paper-axiom consumption.** Sprint 016 invokes
  `paper.eq6_branch2_sigmaReduction` and *only* that paper hypothesis
  on the disk side. Sprint 022 invokes `paper.eq2_sigmaZeroMinus_lower`,
  `paper.eq3_circleGap_decomposition`, and `paper.eq4_sigmaPlus_bound`
  via sprint 003, plus sprint 011's series monotonicity (an
  axiom-free workspace lemma about `sigmaZeroMinus`). **Zero
  invocation of `eq6` anywhere in the proof body** — verifiable by
  inspection of the proof and by axiom-extraction over the new
  lemma's transitive closure.
* **Different proof shape.** Sprint 016's proof is a 4-line `calc`
  on top of `paper.eq6_branch2_sigmaReduction` + sprint 005's series
  identity. Sprint 022's proof is sprint 003's full integrated
  two-`Z` bound + a sign analysis of the `Z_c` coefficient + a
  series-monotonicity invocation + an algebraic identity collapsing
  the merged coefficient to `c⁴/2`. **Strictly more steps, strictly
  different structure, same closed-form output.**
* **Different summability requirements.** Sprint 016 has no
  series-side summability premise. Sprint 022 carries an explicit
  `Summable` premise at `ρ` (needed for sprint 011's monotonicity).
  This is a real cost of the alternative chain — and a measurable
  signal that the two chains are structurally distinct, not
  notational variants.
* **Different integrability requirements.** Sprint 016 has no
  integration on the disk side. Sprint 022 inherits sprint 003's
  `IntervalIntegrable (2r · circleGap)` premise on `[0, c]`.

Why this is **not** "the same chain" as sprint 007 or sprint 015:

* **Different sub-regime.** Sprint 007 and sprint 015 both produce
  bounds on the branch-1 sub-regime `(c, branchSplit c]`. Sprint 022
  produces a bound on the **branch-2** sub-regime
  `[branchSplit c, 1)`. The sign of the `Z_c` coefficient — the
  central algebraic switch — is **opposite** in the two regimes.
* **Different collapse direction.** Sprint 007 *drops* the `Z_c`
  summand (because its coefficient is non-positive). Sprint 022
  *upper-bounds* the `Z_c` summand by the `Z_ρ` summand (because the
  coefficient is non-negative and `Z_c ≤ Z_ρ`). Same starting bound
  (sprint 003), opposite collapse direction.

Why this is **not** "the same chain" as sprint 014 or sprint 021:

* Sprint 014 produces `c⁴ · Z_c` (anchored at `c`) via sprint 013's
  `(3)+(4)`-only bound, **without using `(2)`**. Sprint 022 uses
  `(2)`, which is what introduces the `Z_ρ` summand and enables the
  `Z_c → Z_ρ` collapse. Different paper-axiom signature on the disk
  side.
* Sprint 021 anchors the disk side at an interior `ρ_disk ∈
  (c, branchSplit c)` via sprint 015's `(5)`-based bound — branch-1
  only. Sprint 022 anchors at `ρ ∈ [branchSplit c, 1)` via the
  `(2)+(3)+(4)` chain — branch-2 only. Disjoint sub-regimes, disjoint
  paper-axiom signatures.

## Forward roadmap (for `Experience.md` post-sprint)

After sprint 022 lands, a natural follow-up is:

1. A **closing reducer** mirroring sprint 017's
   `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` but with the disk
   side replaced by sprint 022's `(2)+(3)+(4)` chain. This would be the
   workspace's first end-to-end branch-2 closing reducer that does
   **not** consume `eq6` anywhere — paper-internal cross-validation at
   the closing-reducer level for the entire branch-2 chain.

2. A **paper-internal lemma**
   `eq6_of_eq2_eq3_eq4 : Eq2SigmaZeroMinusLower → Eq3CircleGapDecomposition
   → Eq4SigmaPlusBound → ⋯ → Eq6Branch2SigmaReduction` formalizing the
   algebraic implication shown by sprint 022. Sprint 022 effectively
   proves a *case* of this implication (at fixed `ρ` with summability
   at `ρ`); a fully-quantified version would be a `KorenblumPaper.*`
   contribution requiring a proposal, but is now well-motivated.

3. A **workspace cross-check lemma** that sprint 015's
   `branch1SigmaKernel c ρ · ρ² · Z_ρ` and sprint 007's
   `(c⁶/6)/(ρ²−c²) · Z_ρ` are pointwise equal on `(c, branchSplit c]`,
   completing the "(2)+(3)+(4) reproduces (5) on branch-1" half of the
   cross-validation that sprint 022 starts on the branch-2 half.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: append the new
  generic theorem `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
  in the established style, with a docstring explaining the
  cross-validation framing. Place it after sprint 016's
  `diskExcess_upper_bound_via_eq6` (around the current line 1913) so
  the two branch-2 disk bounds sit side-by-side.
- `ProofRefinement/Korenblum/Candidates/V22.lean`: new candidate file
  mirroring V21's structure. Keep `c_value = 3554/10000`; reuse
  `hEq15_seed_3554` to discharge the sink theorem via `valid_of_eq15`;
  add side lemmas
  - `v22_disk_bound_eq2_eq3_eq4_branch2_compiles` showing the new
    lemma type-checks and accepts the expected hypothesis shapes;
  - `v22_branch2_witness_at_seed` exhibiting a concrete `ρ` strictly
    above `branchSplit c_value` (e.g. `ρ = 0.5`, since
    `branchSplit (3554/10000) = (3554/10000)·√(4/3) ≈ 0.4103 < 0.5`)
    where the new lemma's geometric admissibility holds. The
    summability premise is *not* numerically discharged.
- `ProofRefinement/Korenblum/Bulletin.md`: append
  `sprint_022 queued: ...` line.
- `ProofRefinement/Korenblum/Experience.md`: post-sprint, append a
  paragraph documenting the cross-validation framing and the
  follow-up roadmap above.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V22` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V22.lean` succeeds.
3. The new theorem
   `ProofRefinement.Korenblum.diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`
   exists in `Proof/Reduction.lean`, type-checks, and is consumed by
   `v22_disk_bound_eq2_eq3_eq4_branch2_compiles` in `V22.lean`.
4. The proof body of the new theorem **does not invoke**
   `paper.eq6_branch2_sigmaReduction` or
   `paper.eq5_branch1_sigmaReduction` (verifiable by `grep`). It
   *does* invoke
   `diskExcess_upper_bound_of_eq2_eq3_eq4` (sprint 003) and
   `sigmaZeroMinus_monotone_of_summable` (sprint 011).
5. The closed-form RHS is exactly `(c ^ 4 / 2) * sigmaZeroMinus a b ρ`
   (no residual `ρ²`, no residual `(ρ²−c²)` denominator, no residual
   `Z_c` term) — verifiable by reading the theorem statement.
6. `v22_branch2_witness_at_seed` discharges that
   `branchSplit (3554/10000) ≤ (1 : ℝ)/2 ∧ (1 : ℝ)/2 < 1` so the
   geometric admissibility of the new lemma at `ρ = 0.5` is concrete
   at the seed `c_value`.
7. Score is `≥ 1777/5000` (i.e. ties or beats V21 — a tie is the
   expected outcome since the sink theorem is unchanged).
8. Axiom set on V22 is `{propext, Classical.choice, Quot.sound,
   Lean.ofReduceBool, Lean.trustCompiler, hEq15_seed_3554}` exactly,
   matching V21.

## Out of scope

- Edit older candidates V0–V21.
- Change the final theorem statement or the `c_value` definition.
- Add a free-floating new axiom; the existing seed `hEq15_seed_3554`
  remains the only candidate-side axiom.
- Build the closing reducer that consumes the new disk bound — that
  is the natural follow-up sprint, intentionally deferred to keep this
  sprint to a single new generic lemma + candidate.
- Modify `KorenblumPaper.*` modules; the new lemma lives entirely
  inside `ProofRefinement/Korenblum/Proof/Reduction.lean`.
- Numerically discharge the summability premise; it remains an
  existential hypothesis on the generic lemma.
- Prove the fully-quantified `eq6_of_eq2_eq3_eq4` paper-internal
  implication; sprint 022 only proves a case of it (at fixed `ρ` with
  point-wise summability), and the fully-quantified version would
  require a KorenblumPaper proposal.

## Time budget

≤ 60 minutes runtime.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
