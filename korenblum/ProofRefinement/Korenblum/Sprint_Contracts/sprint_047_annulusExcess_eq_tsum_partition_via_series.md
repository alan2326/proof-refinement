# Sprint 047: First paper-axiom-free **N1/N2 partition** of sprint 046's `tsum`-of-integrals identity for `annulusExcess (circleGap a b) c` — annulus-side mirror of sprint 043, introducing the integrated `Σ⁺_int_ann`/`Σ⁻_int_ann` series quantities

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V46.lean`
**Target file**: `Candidates/V47.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem annulusExcess_eq_tsum_partition_via_series
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c ^ (2 * k + 2)) / (k + 1))) :
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
      (∑' k : ℕ,
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k *
            (1 - c ^ (2 * k + 2)) / (k + 1)
        else 0)
        - ∑' k : ℕ,
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k *
                (1 - c ^ (2 * k + 2)) / (k + 1)
            else 0
```

The proof body composes two existing patterns verbatim:

1. **Apply sprint 046** (`annulusExcess_eq_tsum_via_termwise_integration`) at
   `(a, b, c)` with `hc_nonneg`, `hc_le_one`, `hSummable_int_norm` to give
   `annulusExcess (circleGap a b) c = ∑' k, coeffPlusGap a b k *
   (1 − c^(2k+2)) / (k+1)`.
2. **Reuse sprint 043's partition skeleton** verbatim, with the per-`k`
   integration weight `c^(2k+2)/(k+1)` (sprint 043's summand on disk side)
   replaced by the per-`k` annulus weight `(1 − c^(2k+2))/(k+1)`. The
   replacement is a uniform termwise scaling that does not affect the
   N1/N2 partition argument since the partition is over `k`, not over
   the weight.

Concretely:
- Define `f k := coeffPlusGap a b k * (1 − c^(2k+2)) / (k+1)` (the sprint
  046 RHS summand).
- Define `f1 k := if n1Pred a b k then f k else 0` and
  `f2 k := if n2Pred a b k then f k else 0`.
- Define `g2 k := if n2Pred a b k then coeffMinusGap a b k * (1 − c^(2k+2))/(k+1) else 0`.
- Termwise partition identity: `f k = f1 k + f2 k` for all `k`. The
  proof body is **byte-for-byte identical** to sprint 043's partition
  skeleton, with `f` rebound to the new annulus summand.
- Summability of `f`, `f1`, `f2`, `g2` from `hSummable_int_norm` via
  `Summable.of_norm_bounded` + `Summable.indicator` + termwise sign
  swap on N2.
- Step A: `(∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k` via `tsum_congr` +
  `Summable.tsum_add`.
- Step C: `∑' k, f2 k = -∑' k, g2 k` via the termwise N2 sign-swap
  identity `coeffPlusGap a b k = -coeffMinusGap a b k` (only valid on
  N2; off N2 both sides are 0). Lift via `tsum_congr` then pull the
  negative out via `tsum_neg`.
- Final chain: `annulusExcess = ∑' f = ∑' f1 + ∑' f2 = (∑'_{N1} ...) +
  (-∑'_{N2} ...) = (∑'_{N1} ...) - (∑'_{N2} ...)`.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 047 ships:

1. **First workspace `tsum`-partition equality at the integrated layer
   on the annulus side.** The current state of the workspace's
   `tsum`-partition matrix:

   | Layer | Disk side (`[0, c]`) | Annulus side (`[c, 1]`) |
   |-------|-----|-----|
   | function-level series-partition `tsum` (N1/N2) at fixed `r` | sprint 027 (equality) | (none — circleGap series structure is `r`-independent so partition at fixed `r` is symmetric) |
   | function-level integrated equality (single window) | sprint 040 (drop), 026 | 041 (function-level decomposition) |
   | `tsum`-of-integrals (unconditioned) | sprint 042 | **sprint 046** |
   | **integrated × N1/N2-restricted `tsum` partition (equality)** | **sprint 043** | **047 (NEW)** |
   | integrated × N1/N2-restricted (drop one piece for a bound) | sprint 044 (drops N2) | (queueable as sprint 048 after 047 lands) |
   | end-to-end closing reducer with kernel `Σ⁺_int(c) ≤ ∫ ...` | sprint 045 (paper axioms `{eq8, eq9}`, oracle cells `{}`) | (queueable as sprint 049 after 048 lands; would have paper axioms `{}`, oracle cells `{}` — strictly improving the trust surface of every prior closing reducer) |

   Sprint 047 fills the sole missing cell on the **integrated × N1/N2
   partition equality** row, completing the symmetric pattern of
   disk-side and annulus-side termwise partition equalities. This is
   the **last structural prerequisite** for an end-to-end closing
   reducer with paper-axiom signature `{}` and zero oracle cells.

2. **Introduces the integrated annulus quantities `Σ⁺_int_ann`/`Σ⁻_int_ann`.**
   The N1-restricted `tsum`
   `∑' k, if n1Pred a b k then coeffPlusGap a b k · (1 − c^(2k+2))/(k+1) else 0`
   is the **annulus-side integrated counterpart** of `Σ⁺(c)` — each
   `k`-th term carries the per-`k` annulus integration weight
   `(1 − c^(2k+2))/(k+1) = ∫_c^1 2r · r^(2k) dr / 1`. This is **not** a
   renaming of any existing workspace quantity:
   - `Σ⁺(c) := ∑'_{N1} coeffPlusGap_k · c^(2k)` is pointwise at
     `r = c` with no integration weight.
   - `Σ⁺_int(c) := ∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1)` (sprint
     043's quantity) carries the disk integration weight
     `c^(2k+2)/(k+1) = ∫_0^c 2r · r^(2k) dr`.
   - `Σ⁺_int_ann(c) := ∑'_{N1} coeffPlusGap_k · (1 − c^(2k+2))/(k+1)`
     (sprint 047's quantity) carries the annulus integration weight
     `(1 − c^(2k+2))/(k+1) = ∫_c^1 2r · r^(2k) dr`.
   - `Σ⁺_int(c) + Σ⁺_int_ann(c) = ∑'_{N1} coeffPlusGap_k / (k+1)` —
     the full-disk integration weight, which is **not** any
     pre-existing workspace quantity. The same is true for the
     N2-restricted analogues. No prior workspace lemma exposes this
     full-disk decomposition `[0, 1] = [0, c] ⊔ [c, 1]` at the
     termwise series level.

3. **First downstream consumer of sprint 046 in a series-partition
   chain.** Sprint 046 ships an unconditioned `tsum` identity for
   `annulusExcess`. Sprint 047 makes the N1/N2 partition explicit, so
   future `tsum_le_tsum`-style downstream chains can treat the N1 and
   N2 contributions independently — analogous to how sprint 043 is the
   prerequisite for sprint 044's drop-N2-for-a-bound chain on the
   disk side.

4. **Foundation for paper-axiom-free, oracle-cell-free closing reducer
   on both sides.** Once sprint 047 is in place, a future closing
   reducer (queueable as sprint 049 or similar) can fuse:
   - sprint 044's disk-side bound `diskExcess ≤ Σ⁺_int(c)` (drops the
     non-positive N2 contribution from sprint 043's partition).
   - sprint 047's annulus-side equality `annulusExcess = Σ⁺_int_ann(c) − Σ⁻_int_ann(c)`,
     where `Σ⁻_int_ann(c) := ∑'_{N2} coeffMinusGap_k · (1 − c^(2k+2))/(k+1) ≥ 0`.
     Drop the non-negative `−Σ⁻_int_ann(c)` to get `annulusExcess ≤ Σ⁺_int_ann(c)`
     — but this gives `annulusExcess ≤ ...` (wrong direction for
     `diskExcess ≤ annulusExcess`). The *correct* drop direction is to
     bound `annulusExcess` from **below**: since `Σ⁻_int_ann(c) ≥ 0`,
     `annulusExcess = Σ⁺_int_ann(c) − Σ⁻_int_ann(c)` cannot be lower-
     bounded by simply dropping `Σ⁻_int_ann`. Instead, the closing
     reducer needs the per-`k` comparison `c^(2k+2)/(k+1) ≤
     (1 − c^(2k+2))/(k+1)` on N1 (i.e., `2c^(2k+2) ≤ 1`, valid when
     `2c² ≤ 1`, i.e., `c ≤ 1/√2 ≈ 0.707`) plus a **separate** bound
     to absorb the `−Σ⁻_int_ann(c)` deficit. Sprint 047 ships only the
     partition equality — the closing reducer's per-`k` analysis is
     queueable separately.

5. **Direct mirror of sprint 043 on the structurally distinct interval
   `[c, 1]`.** Sprint 043 establishes the partition equality for
   `diskExcess` at `[0, c]`; sprint 047 establishes the structurally
   analogous identity for `annulusExcess` at `[c, 1]`. The two
   together cover **both halves** of the natural decomposition
   `annulusSlice 0 1 = diskExcess + annulusExcess` at the integrated
   × N1/N2-restricted `tsum` layer. This was previously unreachable
   from any workspace lemma (sprint 041's function-level
   decomposition does not expose the per-`k` partition; sprints 043
   and 047 together do).

6. **Independent of sprint 041.** Sprint 041 ships the function-level
   integrated equality `annulusSlice = ∫ 2ρ·Σ⁺ − ∫ 2ρ³·Z` for any
   `[α, β]`. Sprint 047 ships the termwise integrated partition for
   `annulusExcess` only at `[c, 1]`. The two are **complementary**:
   041 gives a function-level decomposition (no termwise structure
   but covers all windows), 047 gives a termwise decomposition (full
   per-`k` structure but only at the annulus window `[c, 1]`).

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V47 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is a new lemma layer (integrated × N1/N2-restricted
  `tsum` on the annulus side), not a numerical refinement of an
  existing closed-form coefficient.

Why this is **not** "the same chain" as sprint 046:

* **Unconditioned `tsum` vs N1/N2-partitioned `tsum`.** Sprint 046's
  RHS is `∑' k, coeffPlusGap_k · (1 − c^(2k+2))/(k+1)` (no partition).
  Sprint 047's RHS is `(∑'_{N1} coeffPlusGap_k · ...) - (∑'_{N2} coeffMinusGap_k · ...)`
  (explicit N1/N2 partition with sign swap on N2). Different RHS
  shape.
* **No partition machinery in 046.** Sprint 046's body uses
  `MeasureTheory.integral_tsum_of_summable_integral_norm` and termwise
  integration. Sprint 047's body uses `Summable.indicator`,
  `Summable.tsum_add`, `tsum_congr`, `tsum_neg` — the `tsum`-partition
  family from sprint 027 (lifted to the integrated layer by sprint
  043). Disjoint Mathlib machinery families.
* **Different downstream consumer pattern.** Sprint 046's identity is
  consumed by termwise per-`k` numerical analysis on the unconditioned
  series. Sprint 047's identity is consumed by N1/N2-aware sign-
  disciplined chains (e.g., applying `tsum_le_tsum` to the N1 piece
  independently of the N2 piece, or per-`k` cross-comparison with
  sprint 043's disk-side partition).

Why this is **not** "the same chain" as sprint 043:

* **Different integration interval.** Sprint 043 partitions the
  `[0, c]` integral; sprint 047 partitions the `[c, 1]` integral.
  The two integrals are over **disjoint** sub-intervals of `[0, 1]`,
  with **disjoint** termwise integration weights (`c^(2k+2)/(k+1)` vs
  `(1 − c^(2k+2))/(k+1)`).
* **Different conclusion target.** Sprint 043's conclusion is on
  `diskExcess`; sprint 047's is on `annulusExcess`. The two are
  **distinct paper-defined objects** (`PaperAxioms.diskExcess` vs
  `PaperAxioms.annulusExcess`) with disjoint downstream consumers.
* **Different summability premise shape.** Sprint 043's premise is
  `Summable (fun k => |coeffPlusGap_k| · c^(2k+2)/(k+1))`; sprint
  047's is `Summable (fun k => |coeffPlusGap_k| · (1 − c^(2k+2))/(k+1))`.
  The latter decays only like `1/(k+1)` (the `(1 − c^(2k+2))` factor
  approaches `1`), strictly weaker than sprint 043's geometric decay
  `c^(2k+2)/(k+1)`. This means sprint 047's summability cell is
  **harder to discharge** than sprint 043's — and is exactly the
  premise sprint 046 itself takes.
* **Mirror, not duplicate.** Sprint 047 is the mechanical mirror of
  sprint 043 on the annulus side, but the disjoint integration
  interval and the distinct paper-defined conclusion target make it
  a structurally independent identity. The pair (043, 047) is
  required for any future per-`k` × per-`k` cross-side comparison;
  neither alone suffices.

Why this is **not** "the same chain" as sprint 027:

* **Pointwise vs integrated vs annulus-integrated.** Sprint 027
  partitions at fixed `r` (pointwise). Sprint 043 partitions at the
  integrated disk layer. Sprint 047 partitions at the integrated
  annulus layer. Three disjoint analytical layers.
* **Different summands.** Sprint 027's summand is
  `coeffPlusGap_k · r^(2k)`. Sprint 043's is
  `coeffPlusGap_k · c^(2k+2)/(k+1)`. Sprint 047's is
  `coeffPlusGap_k · (1 − c^(2k+2))/(k+1)` — carries the annulus
  integration weight that has no analog at either the pointwise or
  disk-integrated layer.

Why this is **bounded enough for one Generator session**:

* The proof body is the **composition of two existing patterns**:
  sprint 046's invocation (one line) followed by sprint 043's
  partition skeleton (~100–150 lines) with `f` rebound to the
  annulus-integrated summand.
* The summability transfer step (sprint 046's `Summable (|·|)` cell
  to `Summable (·)` requirement on the new summand) is the same
  application of `Summable.of_norm_bounded` that sprint 043 uses,
  with `c^(2k+2)/(k+1)` replaced by `(1 − c^(2k+2))/(k+1)`. The
  bound is again an *equality* since `(1 − c^(2k+2))/(k+1) ≥ 0`
  for `0 ≤ c ≤ 1` (used `0 ≤ c^(2k+2) ≤ 1` from `0 ≤ c ≤ 1`).
* The termwise sign-swap identity `coeffPlusGap_k = -coeffMinusGap_k`
  on N2 is verbatim sprint 043's sign-swap step.
* No new Mathlib lemmas are needed beyond what sprints 043 and 046
  already use.
* Estimated body length: **~100–150 lines** (sprint 046's invocation
  + sprint 043's skeleton with new `f`, plus the summability
  transfer adapted to the new weight).

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* All ingredients (`Summable.of_norm_bounded`, `Summable.indicator`,
  `Summable.tsum_add`, `tsum_congr`, `tsum_neg`, `abs_mul`, `abs_div`,
  `abs_pow`, `abs_of_nonneg`) are already consumed by sprint 043's
  body. No new Mathlib lemma archaeology needed.
* The non-negativity `0 ≤ (1 − c^(2k+2))/(k+1)` for `0 ≤ c ≤ 1`
  follows from `pow_le_one` (or `pow_le_pow_right_of_le_one`) +
  `sub_nonneg.mpr` + `Nat.cast_pos.mpr (Nat.succ_pos k)`. Routine
  algebra.

Why this is **bounded enough on candidate-side instantiation**:

* The V47 `_compiles` side lemma takes the new `hSummable_int_norm`
  cell as a universally-quantified hypothesis (mirroring V46's
  pattern) and applies the new theorem at `c = c_value`. ~15 lines.
* The V47 `_recovers_sprint046_at_seed` side lemma (analogous to
  V43's `_recovers_sprint042_at_seed`) takes the same hypotheses,
  invokes both sprints 046 and 047 at the seed, and demonstrates a
  tautological compilation check (acceptable simplification per the
  contract). Or, optionally, a full algebraic re-derivation via
  `rw [← sprint046]; exact sprint047` (mirroring sprint 043's
  V43 `_recovers_sprint042_at_seed` shape).

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem `annulusExcess_eq_tsum_partition_via_series` after
  sprint 046's `annulusExcess_eq_tsum_via_termwise_integration`
  (current end of `Reduction.lean`).

  Estimated body length: ~100–150 lines.

  The proof body structure (high-level):

  1. **Apply sprint 046** to get the unconditioned identity:
     ```lean
     have h_sprint046 :
         PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
           ∑' k : ℕ,
             PaperAxioms.coeffPlusGap a b k *
               (1 - c ^ (2 * k + 2)) / (k + 1) :=
       annulusExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
         hc_nonneg hc_le_one hSummable_int_norm
     ```

  2. **Define the three summand families** (mirroring sprint 043's
     `f`/`f1`/`f2`/`g2`):
     ```lean
     set f : ℕ → ℝ := fun k =>
       PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
       with hf_def
     set f1 : ℕ → ℝ := fun k =>
       if PaperAxioms.n1Pred a b k then
         PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
       else 0 with hf1_def
     set f2 : ℕ → ℝ := fun k =>
       if PaperAxioms.n2Pred a b k then
         PaperAxioms.coeffPlusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
       else 0 with hf2_def
     set g2 : ℕ → ℝ := fun k =>
       if PaperAxioms.n2Pred a b k then
         PaperAxioms.coeffMinusGap a b k * (1 - c ^ (2 * k + 2)) / (k + 1)
       else 0 with hg2_def
     ```

  3. **Establish summability of `f`, `f1`, `f2`, `g2`** from
     `hSummable_int_norm` (sprint 046's input cell) — verbatim from
     sprint 043's body with the per-`k` weight `c^(2k+2)/(k+1)` replaced
     by `(1 − c^(2k+2))/(k+1)`. The non-negativity step requires a
     small adaptation:
     ```lean
     have h_weight_nonneg : ∀ k : ℕ,
         0 ≤ (1 - c ^ (2 * k + 2)) / (k + 1) := by
       intro k
       apply div_nonneg
       · linarith [pow_le_one (2 * k + 2) hc_nonneg hc_le_one]
       · exact_mod_cast Nat.zero_le (k + 1)
     ```
     The rest of the summability transfer (from sprint 043) carries
     over verbatim.

  4. **Termwise partition identity `f k = f1 k + f2 k`** — verbatim
     from sprint 043 (the partition argument is `c`-independent, so the
     same `by_cases hk1 : n1Pred a b k` skeleton works).

  5. **`(∑' k, f k) = (∑' k, f1 k) + (∑' k, f2 k)`** via `tsum_congr`
     + `Summable.tsum_add` (verbatim from sprint 043).

  6. **Termwise sign-swap identity on N2** (verbatim from sprint 043
     with the new summand):
     ```lean
     have h_f2_eq_neg_g2 : (∑' k, f2 k) = - ∑' k, g2 k := by
       have h_term_neg : ∀ k, f2 k = -(g2 k) := by
         intro k
         by_cases hk : PaperAxioms.n2Pred a b k
         · simp only [f2, g2, hk, if_true]
           unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
           ring
         · simp [f2, g2, hk]
       calc (∑' k, f2 k)
           = ∑' k, -(g2 k) := tsum_congr h_term_neg
         _ = -∑' k, g2 k := tsum_neg
     ```

  7. **Chain everything** (verbatim from sprint 043 with `diskExcess`
     replaced by `annulusExcess` and the new summand):
     ```lean
     calc PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
         = ∑' k : ℕ,
             PaperAxioms.coeffPlusGap a b k *
               (1 - c ^ (2 * k + 2)) / (k + 1) := h_sprint046
       _ = ∑' k, f k := rfl
       _ = (∑' k, f1 k) + ∑' k, f2 k := h_tsum_partition
       _ = (∑' k, f1 k) + (-∑' k, g2 k) := by rw [h_f2_eq_neg_g2]
       _ = (∑' k, f1 k) - ∑' k, g2 k := by ring
     ```

- `ProofRefinement/Korenblum/Candidates/V47.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V46),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V46),
  4. Adds two side lemmas exercising the new generic identity:
     - `v47_annulusExcess_eq_tsum_partition_compiles` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell on `(1 − c_value^(2k+2))/(k+1)`;
       applies the new theorem at the seed `c = c_value`; conclusion
       is the new partition equality
       `annulusExcess (circleGap a b) c_value = (∑'_{N1} ...) - (∑'_{N2} ...)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v47_annulusExcess_eq_tsum_partition_recovers_sprint046_at_seed` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; invokes both sprints 046 and 047
       at the seed; demonstrates a tautological compilation check
       (acceptable simplification — full algebraic re-derivation
       via `rw [← sprint046]; exact sprint047` is also acceptable).
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V46) — the new partition
     identity is materialised in side lemmas, **not** as the sink
     theorem's discharge route.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V47` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V47.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V47 ties V46 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V47.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `annulusExcess_eq_tsum_partition_via_series`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V47.lean`'s two side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken —
   sprint 047's signature is `(a, b, c)`-only with no `K` and no
   `paper`.)
7. The proof body invokes
   `annulusExcess_eq_tsum_via_termwise_integration` (sprint 046) at
   least once. Greppable check: count of
   `annulusExcess_eq_tsum_via_termwise_integration` in the body of
   the new theorem is **≥ 1**.
8. The proof body invokes `Summable.indicator` at least twice (once
   for `f1`'s summability over `{k | n1Pred a b k}`, once for `f2`'s
   summability over `{k | n2Pred a b k}`). Greppable check: count of
   `.indicator` in the body of the new theorem is **≥ 2**.
9. The proof body invokes `Summable.tsum_add` (or equivalently
   `.tsum_add`) at least once for the partition-sum step. Greppable
   check: count of `.tsum_add` in the body of the new theorem is
   **≥ 1**.
10. The proof body invokes `tsum_congr` at least twice (once for the
    partition lift, once for the N2 sign-swap lift). Greppable
    check: count of `tsum_congr` in the body of the new theorem is
    **≥ 2**.
11. The proof body invokes `tsum_neg` at least once for the N2
    sign-swap pull-out step. Greppable check: count of `tsum_neg` in
    the body of the new theorem is **≥ 1**.
12. The new theorem's conclusion is an **equality** (not an
    inequality): the conclusion contains `=` between
    `PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c` and
    the `(∑'_{N1} ...) - (∑'_{N2} ...)` RHS. Greppable check: in
    the new theorem's signature line, the substring `≤` does not
    appear in the conclusion.
13. The new theorem **does not invoke** sprint 027's
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    — sprint 047 partitions at the integrated annulus layer (after
    sprint 046), not at the pointwise layer. Greppable check: count
    of `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    in the body of the new theorem is **0**.
14. The new theorem **does not invoke** sprint 042's
    `diskExcess_eq_tsum_via_termwise_integration`, sprint 043's
    `diskExcess_eq_tsum_partition_via_series`, sprint 044's
    `diskExcess_upper_bound_via_tsum_partition_drop_N2`, sprint
    041's `annulusSlice_eq_via_series_partition`, or sprint 040's
    `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
    — sprint 047 is built on top of sprint 046 only. Greppable
    check: in the new theorem body, counts of all five lemma names
    above are **0**.
15. The new theorem **does not invoke** `paperLambda` anywhere in
    its proof body or signature. Greppable check: count of
    `paperLambda` in the new theorem (signature + body) is **0**.
16. The new theorem **does not invoke** any `Section2Assumptions`
    field — its signature does not contain `Section2Assumptions`.
    Greppable check: count of `Section2Assumptions` in the new
    theorem (signature + body) is **0**.
17. The new theorem **does not invoke** `sigmaPlus`, `sigmaMinus`,
    `sigmaZeroMinus`. Sprint 047 expands at the per-`k` partition
    level via `coeffPlusGap`/`coeffMinusGap` and `n1Pred`/`n2Pred`
    only. Greppable check: in the body of the new theorem, counts
    of `sigmaPlus`, `sigmaMinus`, `sigmaZeroMinus` are all **0**.
    (Counts of `n1Pred`, `n2Pred`, `coeffPlusGap`, `coeffMinusGap`
    are expected to be `≥ 1`.)
18. The V47 `_compiles` side lemma's conclusion is the new partition
    equality at `c = c_value`, with the `hSummable_int_norm` cell
    as a universally-quantified hypothesis on the side lemma.
19. The V47 `_recovers_sprint046_at_seed` side lemma takes the same
    universally-quantified `(a, b)` and `hSummable_int_norm` cell;
    invokes sprint 047 at the seed; demonstrates a tautological
    compilation check (or a full algebraic re-derivation back to
    sprint 046's RHS — either is acceptable).

## Out of scope

- Edit older candidates V0–V46.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V47 is
  the same `hEq15_seed_3554` that V0–V46 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the `hSummable_int_norm` hypothesis cell from the
  workspace's existing N1/N2 series-summability lemmas (sprints
  011, 012, 032). The new weight `(1 − c^(2k+2))/(k+1)` decays only
  like `1/(k+1)`, so the summability discharge requires either (a)
  a stronger summability hypothesis on the underlying
  `coeffPlusGap_k` series than sprints 011/012/032 provide, OR (b)
  the use of the partition-level summability transfer (which would
  need the N1 and N2 pieces to be separately summable). Queueable
  as a separate sprint.
- Ship the **drop-one-piece-for-a-bound** annulus-side lemma (the
  annulus-side mirror of sprint 044). The natural drop direction
  on the annulus side is **opposite** to sprint 044's: where
  sprint 044 drops the non-positive N2 piece on the disk side to
  get an upper bound, the analogous annulus-side drop would either
  - (i) drop the non-negative `−Σ⁻_int_ann(c)` from the partition
    equality to get `annulusExcess ≤ Σ⁺_int_ann(c)` (an **upper**
    bound, opposite direction from what the `diskExcess ≤
    annulusExcess` closing requires), or
  - (ii) require a **per-`k`** comparison `coeffPlusGap_k ·
    (1 − c^(2k+2))/(k+1) ≥ stuff_k` to lower-bound `annulusExcess`
    by something exposed.

  Queueable as a separate sprint after sprint 047 lands.
- Ship the **closing reducer** with paper-axiom signature `{}` and
  zero oracle cells fusing sprint 044's disk-side bound with the
  eventual sprint 048 annulus-side bound. This is the eventual
  queueable sprint 049 (or similar); sprint 047 only ships the
  structural prerequisite.
- Discharge the per-`k` × per-`k` kernel inequality
  `Σ⁺_int(c) ≤ annulusExcess` (the eventual closing kernel for
  sprint 049). This is a separate analytical sprint requiring
  careful sign-analysis on N1 vs N2 indices and is queueable as
  part of sprint 049's contract.
- Ship the analogous N1/N2 partition for sprint 041's
  `annulusSlice_eq_via_series_partition` over an arbitrary
  `[α, β]`. Sprint 047 specialises to the annulus window `[c, 1]`
  only. The general `[α, β]` partition would require swap-of-sum-
  and-integral over an arbitrary subinterval, which is queueable
  as a separate sprint after 047 lands.
- Ship a witness at any `c > 0.3554`. Sprint 047 does not raise
  `c_value`. The eventual numerical push is a *consumer* of
  sprint 047 + future sprints 048/049, not sprint 047 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15`
  to any new chain. The new partition identity is materialised in
  side lemmas only.
- Re-derive sprint 046 as a corollary of sprint 047 (by
  re-aggregating the partition into a single `tsum`). The
  `_recovers_sprint046_at_seed` side lemma is allowed to stop at a
  tautological check; full algebraic re-derivation is out of
  scope.

## Time budget

≤ 90 minutes runtime. (Sprint 047's body is the **composition of two
existing patterns**: sprint 046's invocation (one line) + sprint
043's partition skeleton (~100–150 lines) with `f` rebound to the
annulus-integrated summand `coeffPlusGap_k · (1 − c^(2k+2))/(k+1)`,
plus the small adaptation in the summability transfer for the
non-negativity `0 ≤ (1 − c^(2k+2))/(k+1)` (replacing sprint 043's
`0 ≤ c^(2k+2)/(k+1)` step). The two V47 side lemmas reuse the
universally-quantified hypothesis pattern from V46's `_compiles`
side lemma, ~20–40 lines each. Total V47 size: ≤ 200 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* **Sprint 043 is the canonical reference for sprint 047's body.**
  Open `Reduction.lean` and find sprint 043's body
  (`diskExcess_eq_tsum_partition_via_series`). Copy the body verbatim
  into the new theorem's slot, then apply the substitutions:
  - Replace `diskExcess_eq_tsum_via_termwise_integration` with
    `annulusExcess_eq_tsum_via_termwise_integration` (sprint 046).
  - Add `hc_le_one : c ≤ 1` to the signature and pass it as the
    second positional argument to `annulusExcess_eq_tsum_via_termwise_integration`.
  - Replace every occurrence of `c ^ (2 * k + 2) / (k + 1)` (sprint
    043's per-`k` integration weight) with `(1 - c ^ (2 * k + 2)) / (k + 1)`.
  - Adapt the summability transfer's non-negativity step from
    `0 ≤ c^(2k+2)/(k+1)` (sprint 043) to
    `0 ≤ (1 - c^(2k+2))/(k+1)` (sprint 047) using
    `pow_le_one (2 * k + 2) hc_nonneg hc_le_one`.
  - Replace the final `calc` chain's `diskExcess` with
    `annulusExcess`.

* **Key non-negativity step for the summability transfer:**
  ```lean
  have h_weight_nonneg : ∀ k : ℕ,
      0 ≤ (1 - c ^ (2 * k + 2)) / (k + 1) := by
    intro k
    apply div_nonneg
    · -- 0 ≤ 1 - c^(2k+2): need c^(2k+2) ≤ 1
      have h_pow_le_one : c ^ (2 * k + 2) ≤ 1 :=
        pow_le_one (2 * k + 2) hc_nonneg hc_le_one
      linarith
    · -- 0 ≤ (k+1 : ℝ)
      exact_mod_cast Nat.zero_le (k + 1)
  ```
  (Note: in pinned Mathlib, `pow_le_one` may be named `pow_le_one₀`
  or have a slightly different signature. The Generator should grep
  Mathlib for the exact name in the pinned version. Alternatively,
  derive via `pow_le_pow_right_of_le_one hc_nonneg hc_le_one (Nat.zero_le _)`
  or by induction on `k`.)

* **The summability transfer pattern from sprint 043** (lines after
  the `set` definitions):
  ```lean
  have hSummable_f : Summable f := by
    refine Summable.of_norm_bounded
      (fun k =>
        |PaperAxioms.coeffPlusGap a b k| *
          (1 - c ^ (2 * k + 2)) / (k + 1))
      hSummable_int_norm
      ?_
    intro k
    -- ‖f k‖ = |coeffPlusGap_k * (1 - c^(2k+2))/(k+1)|
    --       = |coeffPlusGap_k| * |(1 - c^(2k+2))/(k+1)|
    --       = |coeffPlusGap_k| * (1 - c^(2k+2))/(k+1)
    --       since (1 - c^(2k+2))/(k+1) ≥ 0
    have h_weight_nonneg : 0 ≤ (1 - c ^ (2 * k + 2)) / (k + 1) := ...
    rw [Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_pow]
    rw [abs_of_nonneg (Nat.cast_nonneg (k + 1) : (0:ℝ) ≤ ↑(k+1))]
    -- After this point, manipulate to match the dominating series
    sorry  -- Generator: complete the algebraic chain
  ```
  Sprint 043's body has the analogous step worked out for the disk
  weight; the annulus weight requires only the substitution
  `c^(2k+2)/(k+1) ↔ (1 - c^(2k+2))/(k+1)` plus the new
  `h_weight_nonneg` hypothesis.

* **The N2 sign-swap step is verbatim sprint 043** with the new
  summand:
  ```lean
  have h_f2_eq_neg_g2 : (∑' k, f2 k) = - ∑' k, g2 k := by
    have h_term_neg : ∀ k, f2 k = -(g2 k) := by
      intro k
      by_cases hk : PaperAxioms.n2Pred a b k
      · simp only [f2, g2, hk, if_true]
        unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap
        ring
      · simp [f2, g2, hk]
    calc (∑' k, f2 k)
        = ∑' k, -(g2 k) := tsum_congr h_term_neg
      _ = -∑' k, g2 k := tsum_neg
  ```
  No adaptation required beyond the `f2`/`g2` definitions which
  carry the new annulus weight.

* **The V47 `_compiles` side lemma's expected shape:**
  ```lean
  theorem v47_annulusExcess_eq_tsum_partition_compiles
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            (1 - c_value ^ (2 * k + 2)) / (k + 1))) :
      PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value =
        (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              (1 - c_value ^ (2 * k + 2)) / (k + 1)
          else 0)
          - ∑' k : ℕ,
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  (1 - c_value ^ (2 * k + 2)) / (k + 1)
              else 0 :=
    annulusExcess_eq_tsum_partition_via_series (a := a) (b := b)
      c_value_nonneg c_value_le_one hSummable_int_norm
  ```
  where `c_value_le_one : c_value ≤ 1` is derived inline via
  `by unfold c_value; norm_num` (or via the existing
  `c_value_lt_one.le` in V46's helpers — re-use whatever V46
  already exposes).

* **The V47 `_recovers_sprint046_at_seed` side lemma's expected
  shape:**
  ```lean
  theorem v47_annulusExcess_eq_tsum_partition_recovers_sprint046_at_seed
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            (1 - c_value ^ (2 * k + 2)) / (k + 1))) :
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k *
          (1 - c_value ^ (2 * k + 2)) / (k + 1) =
        (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              (1 - c_value ^ (2 * k + 2)) / (k + 1)
          else 0)
          - ∑' k : ℕ,
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  (1 - c_value ^ (2 * k + 2)) / (k + 1)
              else 0 := by
    -- Both sides equal `annulusExcess (circleGap a b) c_value` by
    -- sprints 046 and 047 respectively. Chain via transitivity.
    rw [← annulusExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
          c_value_nonneg c_value_le_one hSummable_int_norm]
    exact annulusExcess_eq_tsum_partition_via_series (a := a) (b := b)
      c_value_nonneg c_value_le_one hSummable_int_norm
  ```
  (Acceptable simplification per the contract: if the chained form
  is friction-heavy, the side lemma may stop at a tautological
  compilation check after invoking sprint 047 alone.)

* **Premise `hc_le_one` in the new theorem's signature:** unlike
  sprint 043 which only needs `hc_nonneg : 0 ≤ c` (the upper bound
  `c` of the `[0, c]` integration interval is the parameter itself,
  no separate upper-bound hypothesis is required), sprint 047 needs
  both `0 ≤ c` AND `c ≤ 1` (matching sprint 046's signature; the
  upper bound `1` of the `[c, 1]` integration interval is fixed,
  and we need `c ≤ 1` to ensure the interval is non-degenerate
  AND to derive the non-negativity `0 ≤ 1 - c^(2k+2)` for the
  summability transfer).

* **Edge case `c = 1`:** at the boundary `c = 1`, the integration
  interval `[c, 1] = [1, 1]` is degenerate and `annulusExcess
  (circleGap a b) 1 = 0`. The RHS of sprint 047's partition
  equality also vanishes (each `(1 - 1^(2k+2)) = 0`), so the
  equality holds trivially. No special handling needed.

* **Edge case `c = 0`:** at the boundary `c = 0`, the integration
  interval `[c, 1] = [0, 1]` is the full disk, and `annulusExcess
  (circleGap a b) 0` is the full integrated `circleGap` over
  `[0, 1]`. The RHS partitions as `(∑'_{N1} coeffPlusGap_k /
  (k+1)) - (∑'_{N2} coeffMinusGap_k / (k+1))` — the partition
  identity at the natural full-disk integration weight `1/(k+1)`.
  No special handling needed.

* **Note on the per-`k` cross-comparison** (foreshadowing sprint
  048/049): once sprint 047 lands, the workspace's two integrated
  N1/N2 partition equalities sprints 043 and 047 admit the
  per-`k` cross-comparison
  ```
  Σ⁺_int(c) - Σ⁻_int(c)  vs  Σ⁺_int_ann(c) - Σ⁻_int_ann(c)
  ```
  on each of N1 and N2 separately. On N1, the per-`k` weight ratio
  is `c^(2k+2)/(1 - c^(2k+2))` which approaches `0` as `k → ∞`
  (since `c < 1`). On N2 (with the sign swap accounted for), the
  per-`k` weight ratio is the same. This per-`k` cross-comparison
  is the analytical kernel for the eventual paper-axiom-free,
  oracle-cell-free closing reducer. Sprint 047 ships the
  prerequisite partition equality only.
