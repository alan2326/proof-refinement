# Sprint 044: First **paper-axiom-free, oracle-cell-free** disk-side upper bound on `diskExcess` via dropping the non-negative `Σ⁻_int(c)` summand of sprint 043's N1/N2 partition identity

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V43.lean`
**Target file**: `Candidates/V44.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_tsum_partition_drop_N2
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      ∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            c ^ (2 * k + 2) / (k + 1)
        else 0
```

The proof body:

1. **Apply sprint 043** (`diskExcess_eq_tsum_partition_via_series`) at
   `(a, b, c)` with `hc_nonneg` and `hSummable_int_norm` to give the
   exact equality

   ```text
   diskExcess (circleGap a b) c
     = (∑' k, if n1Pred a b k then coeffPlusGap a b k · c^(2k+2)/(k+1) else 0)
       − (∑' k, if n2Pred a b k then coeffMinusGap a b k · c^(2k+2)/(k+1) else 0)
   ```

2. **Show the N2 summand is non-negative termwise.** For each `k`:
   - If `n2Pred a b k` (i.e. `0 < k ∧ ‖a k‖ < ‖b k‖`), then
     `coeffMinusGap a b k = ‖b k‖² − ‖a k‖² ≥ 0` (by `pow_le_pow_left₀`
     on `‖a k‖ ≤ ‖b k‖` after `le_of_lt`, or by `sub_nonneg.mpr` on
     `‖a k‖^2 ≤ ‖b k‖^2`). The summand
     `coeffMinusGap a b k · c^(2k+2)/(k+1)` is therefore non-negative
     (using `c ≥ 0` so `c^(2k+2) ≥ 0`, and `(k+1 : ℝ) > 0`).
   - If `¬ n2Pred a b k`, the summand is `0` by the `if … then … else 0`
     form.

3. **Conclude `Σ⁻_int(c) := ∑' k, … ≥ 0`** via `tsum_nonneg`
   (`Mathlib/Topology/Algebra/InfiniteSum/Order.lean`, takes a single
   pointwise non-negativity hypothesis and concludes the `tsum` is
   non-negative; no `Summable` premise is required on `ℝ` because the
   default `tsum` of a non-summable family is `0`, which is also
   non-negative).

4. **Subtract** to give the upper bound:

   ```text
   diskExcess = Σ⁺_int(c) − Σ⁻_int(c) ≤ Σ⁺_int(c)
   ```

   discharged by `linarith` from sprint 043's equality and step 3's
   non-negativity.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 044 ships:

1. **First workspace `diskExcess` upper bound that is simultaneously
   paper-axiom-free *and* oracle-cell-free.** The current state of the
   workspace's disk-side `diskExcess ≤ …` matrix:

   | Sprint | Disk-side bound RHS | Paper-axiom signature | Oracle cells | Series shape |
   |--------|-----|-----|-----|-----|
   | 003 | `(c⁴/6)·(3ρ²−4c²)/(ρ²−c²)·Z_c + (c⁶/6)/(ρ²−c²)·Z_ρ` | `{eq2, eq3, eq4}` | none | function-level |
   | 013 | `c⁴ · Z_c` | `{eq3, eq4}` | none | function-level |
   | 026 | `c⁴ · Z_c` | `{eq4}` | none | function-level |
   | 030 | sprint-003 RHS | `{eq4}` | none | function-level |
   | 031 | sprint-007 RHS (collapsed single-`Z`) | `{eq4}` | none | function-level |
   | 034 | `c⁴ · Z_c` | `{}` | `{hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)}` | function-level |
   | 040 | `c² · Σ⁺(c)` | `{}` | none | function-level |
   | **044 (NEW)** | **`Σ⁺_int(c) := ∑' k, [n1Pred] · coeffPlusGap_k · c^(2k+2)/(k+1)`** | **`{}`** | **none** | **N1-restricted termwise series** |

   Sprint 040 already ships an empty-paper-axiom, empty-oracle-cell
   bound, but its RHS is *function-level* (`c²·Σ⁺(c)`, a single bulk
   number). Sprint 044 is the **first** such bound whose RHS is a
   per-`k` termwise series — every `k`-th coefficient is independently
   computable from `(a k, c)` alone, with closed-form per-`k` weight
   `c^(2k+2)/(k+1)`. This unlocks **partial-sum truncation analysis,
   per-`k` numerical witnesses, and per-`k` comparison against an
   eventual annulus-side termwise series**, all of which are
   inaccessible from sprint 040's function-level RHS.

2. **First downstream consumer of sprint 043's partition equality.**
   Sprint 043 ships the equality
   `diskExcess = Σ⁺_int(c) − Σ⁻_int(c)` but no downstream lemma
   exploits it. Sprint 044 is the natural first downstream consumer:
   drop the non-negative N2 piece (`Σ⁻_int(c) ≥ 0`) to upgrade the
   equality to an upper bound. This pattern mirrors the relationship
   between sprint 027's pointwise equality
   `circleGap r = Σ⁺(r) − r²·Z(r)` and its downstream consumers (e.g.
   sprint 040's drop of the `−r²·Z` summand).

3. **Eliminates the `hSigmaCmp` oracle cell from sprint 034's chain.**
   Sprint 034 ships
   `diskExcess ≤ c⁴·Z_c modulo Σ⁺(c) ≤ Σ⁻(c)` (the
   `hSigmaCmp` cell). Sprint 044 ships
   `diskExcess ≤ Σ⁺_int(c)` with **no** comparison cell. The
   structural mechanism is **strictly disjoint**: sprint 034 uses the
   *bulk* `Σ⁺(c) ≤ Σ⁻(c)` inequality (a comparison between two
   N1/N2-aggregate quantities at the same radius), whereas sprint 044
   uses *termwise N2 sign structure* (`coeffMinusGap_k ≥ 0` on N2 is
   *built into the definition of N2*, not a paper hypothesis or
   oracle). The bulk comparison is non-trivial in general; the
   termwise sign is structural.

   This pattern reflects an analytical asymmetry that sprint 034's
   contract acknowledges but does not exploit: the N2 contribution to
   `diskExcess` (after the `coeffPlusGap → −coeffMinusGap` sign swap)
   is non-negative termwise, so dropping the *integrated* counterpart
   of `Σ⁻(c)` from the partitioned identity gives a paper-axiom-free,
   oracle-free upper bound that sprint 034 misses by working at the
   non-partitioned function-level layer.

4. **Foundation for an `{eq8, eq9}`-only closing reducer.** Once
   sprint 044 is in place, a future closing reducer can fuse it with
   sprint 006's `(8)+(9)`-derived annulus lower bound to produce a
   `valid_of_*` reducer with paper-axiom signature `{eq8, eq9}` only
   — strictly smaller than every prior closing reducer's signature
   except sprint 039's, which uses `{}` modulo two oracle cells
   `{hSigmaCmp, hLambdaBridgeWindow}`. Sprint 044's RHS shape
   `Σ⁺_int(c) = ∑' k, … · c^(2k+2)/(k+1)` introduces a **new disk-side
   kernel**: any closing reducer using sprint 044 will have the
   kernel inequality `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`,
   structurally distinct from every prior kernel (`c⁴`, `c⁴/2`,
   `c²·Σ⁺(c)`, `(c⁶/6)/(ρ²−c²)·Z_ρ`, etc.).

5. **Paper-axiom-free downstream of sprint 042.** Sprint 042's
   `tsum`-of-integrals identity is paper-axiom-free, and sprint 043's
   N1/N2 partition is paper-axiom-free. Sprint 044 is the third
   step in the chain — the first paper-axiom-free *upper bound* on
   `diskExcess` derived through the `tsum`-of-integrals path
   (sprints 042/043/044 form a coherent paper-axiom-free chain
   `unfolded tsum → N1/N2 partition → N2 drop`).

6. **Structurally disjoint mechanism from sprint 040's `c²·Σ⁺(c)`
   bound.** Sprint 040 derives a paper-axiom-free, oracle-free disk
   bound `diskExcess ≤ c²·Σ⁺(c)` via:

   * pointwise series identity `circleGap r = Σ⁺(r) − r²·Z(r)` (sprint
     027),
   * pointwise drop of the non-negative `−r²·Z(r)` integrand,
   * pointwise `Σ⁺` monotonicity `Σ⁺(r) ≤ Σ⁺(c)` for `r ∈ [0, c]`
     (sprint 032), pulling the constant out of the integral.

   Sprint 044 derives its bound via:

   * termwise integration of the unconditioned series (sprint 042),
   * termwise N1/N2 partition of the resulting `tsum` (sprint 043),
   * termwise drop of the non-negative N2 piece.

   The two mechanisms differ at every step: sprint 040 swaps a
   pointwise comparison and a function-level integration; sprint
   044 swaps a per-`k` comparison and a `tsum`-of-integrals. The
   resulting RHS shapes are also disjoint:
   * Sprint 040's RHS `c² · Σ⁺(c) = c² · ∑'_{N1} coeffPlusGap_k · c^(2k)`
     has per-`k` weight `c^(2k+2)`;
   * Sprint 044's RHS `Σ⁺_int(c) = ∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1)`
     has per-`k` weight `c^(2k+2) / (k+1)`.

   The `1/(k+1)` integration weight makes sprint 044's RHS **strictly
   smaller** than sprint 040's RHS termwise (for non-negative
   `coeffPlusGap_k` on N1), so sprint 044 is a **strictly tighter
   bound** than sprint 040 at the per-`k` level. (Note: the
   termwise comparison only needs `coeffPlusGap_k ≥ 0` on N1, which
   holds by definition of N1 except at `k = 0` where it can be
   either sign. Section "Edge case `k = 0` on N1" in the
   implementation notes below addresses this.)

   This makes sprint 044 the **first workspace bound** that is
   strictly tighter than sprint 040 at the per-`k` level while
   sharing sprint 040's empty paper-axiom signature and empty oracle
   cell list.

7. **Strict structural upgrade over sprint 026's `c⁴·Z_c` bound.**
   Sprint 026's bound `c⁴·Z_c` is derived via `paper.eq4_sigmaPlus_bound`'s
   third conjunct `Σ⁻(c) = c²·Z_c`. Sprint 044 reaches an *equally
   tight or tighter* per-`k` series bound with **no paper-axiom
   invocation**. Specifically, sprint 026's `c⁴·Z_c` aggregates over
   N2 as a single bulk number whereas sprint 044's `Σ⁺_int(c)` aggregates
   over N1 with a per-`k` integration weight `1/(k+1)`. The two
   bounds compare differently for different `(a, b)` data:
   * For `(a, b)` heavily weighted on low-`k` N1 indices, sprint
     044's `1/(k+1)` weight makes it tighter than sprint 026.
   * For `(a, b)` heavily weighted on N2 indices, sprint 026's `Z_c`
     bound is tighter.

   Sprint 044's value is not in being uniformly tighter than 026,
   but in being **paper-axiom-free** while exposing per-`k`
   structure that 026 cannot.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V44 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is a new lemma layer (paper-axiom-free, oracle-free,
  per-`k` series RHS), not a numerical refinement of an existing
  closed-form coefficient.

Why this is **not** "the same chain" as sprint 043:

* **Equality vs upper bound.** Sprint 043 ships
  `diskExcess = Σ⁺_int(c) − Σ⁻_int(c)` (an equality). Sprint 044 ships
  `diskExcess ≤ Σ⁺_int(c)` (an inequality after dropping the non-negative
  `Σ⁻_int(c)` piece). Different conclusion shape, different downstream
  consumer pattern.
* **No partition machinery in 044's body.** Sprint 043's body uses
  `Summable.indicator`, `Summable.tsum_add`, `tsum_congr`, `tsum_neg`
  to *establish* the partition. Sprint 044 *consumes* sprint 043's
  established partition and adds only `tsum_nonneg` plus a termwise
  non-negativity argument. The two bodies use disjoint Mathlib
  machinery families.
* **First downstream use of sprint 043.** Sprint 043 lands the
  partition equality but no prior workspace lemma uses it. Sprint 044
  is the first.

Why this is **not** "the same chain" as sprint 040:

* **Function-level vs termwise.** Sprint 040's RHS `c²·Σ⁺(c)` is
  a single function-level expression. Sprint 044's RHS `Σ⁺_int(c)`
  is a per-`k` termwise series with explicit weights `c^(2k+2)/(k+1)`.
* **Disjoint analytical chain.** Sprint 040's body uses sprint 027's
  pointwise equality + sprint 032's pointwise `Σ⁺` monotonicity
  + `intervalIntegral.integral_sub`. Sprint 044's body uses sprint
  043's `tsum`-partition equality + `tsum_nonneg` + termwise N2
  sign. **Zero shared lemmas in the body** (sprint 044 does not
  invoke sprint 027 directly, nor sprint 032, nor
  `intervalIntegral.integral_sub`).

Why this is **not** "the same chain" as sprint 026:

* **Paper-axiom dependence.** Sprint 026 invokes `paper.eq4_sigmaPlus_bound`.
  Sprint 044 invokes no `paper.eq*` field projection.
* **RHS shape.** Sprint 026's RHS `c⁴·Z_c` is a function-level
  product. Sprint 044's RHS is a series with per-`k` weights.
* **Mechanism.** Sprint 026 chains pointwise inequalities then
  integrates. Sprint 044 partitions the integrated equality then
  drops a non-negative summand.

Why this is **not** "the same chain" as sprint 034:

* **`hSigmaCmp` oracle cell.** Sprint 034's body uses the
  `hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)` cell (a function-level bulk comparison
  between N1 and N2 aggregates). Sprint 044's body uses **no** such
  cell — instead it uses the *termwise* N2 non-negativity
  `coeffMinusGap_k ≥ 0` which is structural (built into N2's
  definition). Different mechanism, different signature.
* **RHS shape.** Sprint 034's RHS is `c⁴·Z_c` (function-level).
  Sprint 044's RHS is `Σ⁺_int(c)` (per-`k` series).

Why this is **bounded enough for one Generator session**:

* The proof body is the **composition of one existing workspace
  lemma (sprint 043) plus one Mathlib lemma (`tsum_nonneg`) plus a
  termwise non-negativity argument that mirrors sprint 025's N2
  drop pattern**.
* Sprint 043's invocation is one line.
* `tsum_nonneg` is a one-line invocation taking a single
  `∀ k, 0 ≤ f k` hypothesis.
* The termwise non-negativity proof for the N2 indicator summand
  is a `by_cases hk : n2Pred a b k` split:
  * `n2Pred` case: unfold `coeffMinusGap`, derive `‖a k‖² ≤ ‖b k‖²`
    from `‖a k‖ < ‖b k‖` (the `n2Pred` second conjunct) via
    `pow_le_pow_left₀` (or `sq_le_sq'` then absolute-value cleanup),
    multiply by `c^(2k+2) ≥ 0` and divide by `(k+1) > 0`.
    Approximately 8–12 lines.
  * `¬ n2Pred` case: the summand is `0`; non-negativity is `le_refl 0`.
    1 line.
* The final algebraic chain `eq → ≤` is a single `linarith` call
  from sprint 043's equality and step 3's non-negativity.
* No new Mathlib lemmas are needed; `tsum_nonneg` is well-tested
  in pinned Mathlib and is the analog of `Finset.sum_nonneg`.
* Estimated body length: **~30–60 lines** (much shorter than
  sprints 042/043, since sprint 044 reuses sprint 043 wholesale and
  only adds the termwise drop argument).

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* The Mathlib lemma `tsum_nonneg` lives at
  `Mathlib/Topology/Algebra/InfiniteSum/Order.lean` and takes a
  single `∀ i, 0 ≤ f i` hypothesis on an `OrderedAddCommMonoid` —
  no `Summable` premise needed. Verified by Planner against pinned
  Mathlib v4.28.0 (search target: `theorem tsum_nonneg`).
* All other ingredients (`pow_le_pow_left₀`, `sub_nonneg`,
  `mul_nonneg`, `div_nonneg`, `pow_nonneg`) are well-tested and used
  throughout the existing `Reduction.lean` body.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem `diskExcess_upper_bound_via_tsum_partition_drop_N2`
  after sprint 043's `diskExcess_eq_tsum_partition_via_series`
  (current end of `Reduction.lean`, after line 6831).

  Estimated body length: ~30–60 lines.

  The proof body structure (high-level):

  1. **Apply sprint 043** to get the partition equality:
     ```lean
     have h_sprint043 :
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
           (∑' k : ℕ,
             if PaperAxioms.n1Pred a b k then
               PaperAxioms.coeffPlusGap a b k *
                 c ^ (2 * k + 2) / (k + 1)
             else 0)
             - ∑' k : ℕ,
                 if PaperAxioms.n2Pred a b k then
                   PaperAxioms.coeffMinusGap a b k *
                     c ^ (2 * k + 2) / (k + 1)
                 else 0 :=
       diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
         hc_nonneg hSummable_int_norm
     ```

  2. **Termwise non-negativity of the N2 summand:**
     ```lean
     have h_n2_term_nonneg :
         ∀ k : ℕ,
           0 ≤ (if PaperAxioms.n2Pred a b k then
                  PaperAxioms.coeffMinusGap a b k *
                    c ^ (2 * k + 2) / (k + 1)
                else 0) := by
       intro k
       by_cases hk : PaperAxioms.n2Pred a b k
       · -- n2Pred ⇒ ‖a k‖ < ‖b k‖ ⇒ ‖a k‖² ≤ ‖b k‖² ⇒ coeffMinusGap ≥ 0
         simp only [hk, if_true]
         have h_norm_le : ‖a k‖ ≤ ‖b k‖ := le_of_lt hk.2
         have h_norm_sq : ‖a k‖ ^ 2 ≤ ‖b k‖ ^ 2 := by
           have h_a_nonneg : (0 : ℝ) ≤ ‖a k‖ := norm_nonneg _
           exact pow_le_pow_left₀ h_a_nonneg h_norm_le 2
         have h_coeff_nonneg :
             (0 : ℝ) ≤ PaperAxioms.coeffMinusGap a b k := by
           unfold PaperAxioms.coeffMinusGap
           linarith
         have h_pow_nonneg : (0 : ℝ) ≤ c ^ (2 * k + 2) :=
           pow_nonneg hc_nonneg _
         have h_kp1_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
         positivity
       · simp [hk]
     ```

  3. **Apply `tsum_nonneg`:**
     ```lean
     have h_n2_tsum_nonneg :
         (0 : ℝ) ≤
           ∑' k : ℕ,
             if PaperAxioms.n2Pred a b k then
               PaperAxioms.coeffMinusGap a b k *
                 c ^ (2 * k + 2) / (k + 1)
             else 0 :=
       tsum_nonneg h_n2_term_nonneg
     ```

  4. **Conclude:**
     ```lean
     linarith [h_sprint043, h_n2_tsum_nonneg]
     ```

- `ProofRefinement/Korenblum/Candidates/V44.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V43),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V43),
  4. Adds two side lemmas exercising the new generic upper bound:
     - `v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_compiles` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; applies the new theorem at the seed
       `c = c_value`; conclusion is the new upper bound
       `diskExcess (circleGap a b) c_value ≤ Σ⁺_int(c_value)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_recovers_sprint043_at_seed` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; applies sprint 043 at the seed to
       get the equality, then applies sprint 044 to get the upper
       bound, and demonstrates that the upper bound is consistent
       with the equality (i.e., the dropped N2 piece is non-negative).
       Body shape: invoke sprint 044 (one line) then optionally
       a `linarith` chain through sprint 043. Acceptable
       simplification: the side lemma may stop at a tautological
       compilation check after invoking sprint 044 alone if the
       full consistency check is friction-heavy.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V43) — the new upper bound
     is materialised in side lemmas, **not** as the sink theorem's
     discharge route.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V44` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V44.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V44 ties V43 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V44.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `diskExcess_upper_bound_via_tsum_partition_drop_N2`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V44.lean`'s two side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken —
   sprint 044's signature is `(a, b, c)`-only with no `K` and no
   `paper`.)
7. The proof body invokes
   `diskExcess_eq_tsum_partition_via_series` (sprint 043) at
   least once. Greppable check: count of
   `diskExcess_eq_tsum_partition_via_series` in the body of the new
   theorem is **≥ 1**.
8. The proof body invokes `tsum_nonneg` at least once. Greppable
   check: count of `tsum_nonneg` in the body of the new theorem
   is **≥ 1**.
9. The proof body **does not** invoke `Summable.indicator`,
   `Summable.tsum_add`, `tsum_congr`, or `tsum_neg`. The partition
   machinery lives in sprint 043; sprint 044 only consumes the
   established partition and applies a termwise non-negativity
   argument. Greppable check: counts of `Summable.indicator`,
   `.tsum_add`, `tsum_congr`, `tsum_neg` in the body of the new
   theorem are all **0**.
10. The new theorem's conclusion is an **inequality** (not an
    equality): the conclusion contains `≤` between
    `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c` and the
    `∑' k, if n1Pred a b k then ... else 0` RHS. Greppable check: in
    the new theorem's signature line, the substring `≤` appears in
    the conclusion. The substring `=` does **not** appear in the
    conclusion outside of the `if` keyword's `then` arm.
11. The new theorem **does not invoke** sprint 042's
    `diskExcess_eq_tsum_via_termwise_integration` directly — sprint
    042's identity is reached *transitively* through sprint 043 only.
    Greppable check: count of
    `diskExcess_eq_tsum_via_termwise_integration` in the body of the
    new theorem is **0**.
12. The new theorem **does not invoke** any of sprints 003 / 013 /
    026 / 030 / 031 / 034 / 040's `diskExcess_upper_bound_*`
    lemmas. Sprint 044 is built on top of sprint 043 (an *equality*),
    not on any prior bound. Greppable check: in the new theorem
    body, counts of `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`,
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_via_eq3_eq4`,
    `diskExcess_upper_bound_via_series_eq4_only_two_Z`,
    `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`,
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    are all **0**.
13. The new theorem **does not invoke** `paperLambda` anywhere in
    its proof body or signature. Greppable check: count of
    `paperLambda` in the new theorem (signature + body) is **0**.
14. The new theorem **does not invoke** any `Section2Assumptions`
    field — its signature does not contain `Section2Assumptions`.
    Greppable check: count of `Section2Assumptions` in the new
    theorem (signature + body) is **0**.
15. The V44 `_compiles` side lemma's conclusion is the new
    upper bound at `c = c_value`, with the `hSummable_int_norm`
    cell as a universally-quantified hypothesis on the side lemma.
16. The V44 `_recovers_sprint043_at_seed` side lemma takes the same
    universally-quantified `(a, b)` and `hSummable_int_norm` cell;
    invokes sprint 044 at the seed; demonstrates a tautological
    compilation check (or a full `linarith` consistency check
    against sprint 043's equality — either is acceptable).

## Out of scope

- Edit older candidates V0–V43.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V44 is
  the same `hEq15_seed_3554` that V0–V43 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the `hSummable_int_norm` hypothesis cell from the
  workspace's existing N1/N2 series-summability lemmas (sprints
  011, 012, 032). This is queueable as a separate sprint.
- Ship a closing reducer fusing sprint 044 with sprint 006's
  annulus-side `(8)+(9)` bound to produce a paper-axiom-`{eq8, eq9}`-only
  closing reducer with kernel `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`.
  That is the **next** sprint's scope after 044 lands; sprint 044
  ships only the disk-side termwise upper bound. Reason: composing
  the new disk RHS with sprint 006's existing annulus RHS and
  setting up the witness existential is a separate analytical sprint.
- Ship a witness at any `c > 0.3554`. Sprint 044 does not raise
  `c_value`. The eventual numerical push is a *consumer* of sprint
  044 + a future closing reducer + the kernel inequality
  evaluation, not sprint 044 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15`
  to any new chain. The new upper bound is materialised in side
  lemmas only.
- Ship the analogous `tsum`-partition + N1/N2 drop for sprint 041's
  `annulusSlice_eq_via_series_partition`. This is a natural
  follow-up sprint but is out of scope here — the annulus-side
  termwise expansion requires sprint 042-style swap-of-sum-and-integral
  machinery applied to the `[c, β]` window (or `[α, β]` window in
  general), and the convergence questions for the annulus window
  are non-trivial.
- Ship a parallel termwise upper bound on the N1 piece (i.e., drop
  the `coeffPlusGap_k ≤ 0` summands at `k = 0` if `coeffPlusGap_0 < 0`).
  This is a structural refinement of sprint 044's RHS but is
  queueable separately — the basic sprint 044 contract above does
  not need to handle the `k = 0` edge case (it's contained inside
  `Σ⁺_int(c)` as written, since the full N1 sum is taken with no
  drop on the N1 side).
- Ship per-`k` numerical sufficient conditions for the disk-vs-annulus
  inequality. That is a *consumer* of sprint 044 and is queueable
  as a separate sprint.
- Re-derive sprint 040's `c²·Σ⁺(c)` bound as a corollary of sprint
  044 by termwise comparison `c^(2k+2)/(k+1) ≤ c^(2k+2)`. This is
  algebraically true (since `1/(k+1) ≤ 1`) and would establish
  sprint 044 as a strict refinement of sprint 040 at the per-`k`
  level, but the precise algebraic chain is queueable separately.

## Time budget

≤ 45 minutes runtime. (Sprint 044's body is the **shortest sprint
since at least sprint 030**: it composes one existing workspace
lemma (sprint 043, one line) + one Mathlib lemma (`tsum_nonneg`,
one line) + a termwise non-negativity argument (~15–25 lines).
Estimated body: ~30–60 lines. The two V44 side lemmas reuse the
universally-quantified hypothesis pattern from V42's and V43's
`_compiles` and `_recovers_*` side lemmas, ~15–25 lines each. Total
V44 size: ≤ 120 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* The Mathlib lemma `tsum_nonneg` lives at
  `Mathlib/Topology/Algebra/InfiniteSum/Order.lean`. Signature:
  ```
  theorem tsum_nonneg {f : α → β} (h : ∀ i, 0 ≤ f i) : 0 ≤ ∑' i, f i
  ```
  No `Summable` premise — the default value of `tsum` for a
  non-summable family is `0`, which is also `≥ 0`. This makes
  sprint 044's body strictly shorter than sprint 043's
  (which had to discharge several `Summable` cells).

* The termwise N2 non-negativity argument:
  - `n2Pred a b k = 0 < k ∧ ‖a k‖ < ‖b k‖`
  - From `‖a k‖ < ‖b k‖` derive `‖a k‖ ≤ ‖b k‖` via `le_of_lt`
  - From `0 ≤ ‖a k‖` (via `norm_nonneg`) and the previous step
    derive `‖a k‖^2 ≤ ‖b k‖^2` via `pow_le_pow_left₀`
  - Unfold `coeffMinusGap a b k = ‖b k‖^2 - ‖a k‖^2` and conclude
    `0 ≤ coeffMinusGap a b k` via `sub_nonneg.mpr` (or `linarith`).
  - From `0 ≤ c` and `c^(2k+2) = c^(2k+2)` derive `0 ≤ c^(2k+2)`
    via `pow_nonneg`.
  - From `0 < (k + 1 : ℝ)` (via `positivity` or
    `Nat.cast_add_one_pos`) and the previous nonnegativities,
    conclude `0 ≤ coeffMinusGap_k * c^(2k+2) / (k+1)` via
    `positivity` or repeated `mul_nonneg` / `div_nonneg`.

* For the `¬ n2Pred` branch the summand reduces to `0` by the
  `if … then … else 0` form; `simp [hk]` closes it.

* The final algebraic step `diskExcess ≤ Σ⁺_int(c)` from
  `diskExcess = Σ⁺_int(c) − Σ⁻_int(c)` and `0 ≤ Σ⁻_int(c)` is a
  one-line `linarith [h_sprint043, h_n2_tsum_nonneg]` invocation.

* Edge case `k = 0` on N1: at `k = 0`, `n1Pred a b 0 = (0 = 0 ∨ ‖a 0‖ ≥ ‖b 0‖)`
  is always true, so the `k = 0` summand is in the N1 sum. The
  `coeffPlusGap a b 0 = ‖a 0‖² − ‖b 0‖²` can be either sign at
  `k = 0` (no constraint on `(a 0, b 0)` from `n1Pred`). However,
  this does not affect sprint 044's correctness: sprint 044's RHS
  includes the `k = 0` term whatever its sign — the upper bound
  holds termwise on the N2 side (which is what we drop), not on
  the N1 side (which we keep). So the `k = 0` edge case is
  *transparent* to sprint 044's argument.

* The `_compiles` side lemma's expected shape:
  ```lean
  theorem v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_compiles
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / (k + 1))) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
        ∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c_value ^ (2 * k + 2) / (k + 1)
          else 0 :=
    diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
      c_value_nonneg hSummable_int_norm
  ```
  (Note: `c_value_nonneg : 0 ≤ c_value` may need to be derived
  inline; sprint 042's V42 file should have an analogous helper —
  check there for the exact form. If not present, derive via
  `by unfold c_value; norm_num` or similar.)

* The `_recovers_sprint043_at_seed` side lemma's expected shape:
  ```lean
  theorem v44_diskExcess_upper_bound_via_tsum_partition_drop_N2_recovers_sprint043_at_seed
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / (k + 1))) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
        ∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c_value ^ (2 * k + 2) / (k + 1)
          else 0 := by
    -- Two routes converge on the same conclusion: sprint 044 directly,
    -- or sprint 043's equality + non-negativity of the dropped N2 piece.
    -- The side lemma exhibits the convergence (or stops at a tautological
    -- check after invoking sprint 044 alone).
    exact diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
      c_value_nonneg hSummable_int_norm
  ```
  (Acceptable simplification per the contract: the side lemma may
  stop at the direct invocation above. A full alternative chain
  through sprint 043 + `linarith` is also acceptable but not
  required.)
