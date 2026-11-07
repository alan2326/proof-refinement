# Sprint 043: First paper-axiom-free **N1/N2 partition** of sprint 042's `tsum`-of-integrals identity for `diskExcess (circleGap a b) c` — introducing the integrated `Σ⁺_int`/`Σ⁻_int` series quantities

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V42.lean`
**Target file**: `Candidates/V43.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_eq_tsum_partition_via_series
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| *
          c ^ (2 * k + 2) / (k + 1))) :
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
            else 0
```

The proof body:

1. **Apply sprint 042** (`diskExcess_eq_tsum_via_termwise_integration`) at
   `(a, b, c)` with `hSummable_int_norm` to give
   `diskExcess = ∑' k, coeffPlusGap a b k * c^(2k+2) / (k+1)`.
2. **Reuse sprint 027's partition skeleton** verbatim, with the termwise
   summand `coeffPlusGap a b k * r ^ (2 * k)` replaced by
   `coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)`. The replacement is
   a uniform termwise scaling by `c² / (k + 1)` (treated as a constant in
   the partition argument since the partition is over `k`, not `r`).
   Concretely:
   - Define `f k := coeffPlusGap a b k * c^(2k+2) / (k+1)` (the sprint
     042 RHS summand).
   - Define `f1 k := if n1Pred a b k then f k else 0` and
     `f2 k := if n2Pred a b k then f k else 0`.
   - Termwise partition identity: `f k = f1 k + f2 k` for all `k`. The
     proof body is **byte-for-byte identical** to sprint 027 lines
     3927–3954, with `f` rebound to the new summand.
3. **Establish summability of `f1`, `f2`, `g2`** (where
   `g2 k := if n2Pred a b k then coeffMinusGap a b k * c^(2k+2)/(k+1) else 0`)
   from `hSummable_int_norm`. Sprint 042 takes `Summable (|coeffPlusGap| · …)`
   as input; sprint 043 derives `Summable (coeffPlusGap · …)` from it
   (the absolute-value summability dominates the signed summability via
   `Summable.of_nonneg_of_le` plus `|coeffPlusGap_k * c^(2k+2)/(k+1)| ≤
   |coeffPlusGap_k| * c^(2k+2)/(k+1)`). Then `f1`, `f2`, `g2`
   summabilities follow via `Summable.indicator` over
   `{k | n1Pred a b k}` and `{k | n2Pred a b k}`, mirroring sprint 027's
   `hSummable_f1`/`hSummable_f2` derivations (lines 3956–3974).
4. **Step A**: `(∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k` via
   `tsum_congr` + `Summable.tsum_add` (sprint 027 line 3978–3982 verbatim).
5. **Step B**: `∑' k, f1 k = ∑' k, if n1Pred a b k then ... else 0`
   (definitional via `change`).
6. **Step C**: `∑' k, f2 k = -∑' k, g2 k` via the termwise N2 sign-swap
   identity `coeffPlusGap a b k = -coeffMinusGap a b k` (only valid on
   N2; off N2 both sides are 0). Lift via `tsum_congr` then pull the
   negative out via `tsum_neg`. Sprint 027 lines 3996–4006 verbatim.
7. **Chain**: `diskExcess = ∑' f = ∑' f1 + ∑' f2 = (∑'_{N1} ...) +
   (-∑'_{N2} ...) = (∑'_{N1} ...) - (∑'_{N2} ...)`. Single `linarith`
   or `ring` close.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 043 ships:

1. **First workspace `tsum`-partition identity at the integrated layer.**
   Sprint 027 ships the partition `circleGap r = sigmaPlus r − r²·Z(r)`
   at the **pointwise** layer (single fixed `r`). Sprint 042 ships the
   integrated `tsum` identity `diskExcess = ∑' k, coeffPlusGap_k · …` at
   the **integrated** layer (single unconditioned `tsum`). Sprint 043 is
   the **first lemma to combine the partition methodology of sprint 027
   with the integrated layer of sprint 042**, producing
   `diskExcess = (∑'_{N1} coeffPlusGap_k · …) − (∑'_{N2} coeffMinusGap_k · …)`.
   This is **structurally distinct** from both predecessors: it lives at
   a layer (integrated × N1/N2-restricted `tsum`) where no prior workspace
   lemma operates.

   | Layer | Description | Sprints |
   |-------|-------------|---------|
   | function-level pointwise | (in)equality on `circleGap a b r` for fixed `r` | 002, 011, 012, 015, 016, 022, 029, 032, 033, 036, 037 |
   | function-level series-partition `tsum` (N1/N2) | partition at fixed `r` | 005, 027, 028 |
   | function-level integrated (single window) | `intervalIntegral` over `[α, β]` | 003, 006, 007, 013, 026, 030, 031, 034, 038, 040, 041 |
   | `tsum`-of-integrals (unconditioned) | `∑' k, ∫ F k` | 042 |
   | **integrated × N1/N2-restricted `tsum`** | **`(∑'_{N1} ...) − (∑'_{N2} ...)`** at integrated layer | **043 (NEW)** |

2. **Introduces the integrated `Σ⁺_int`/`Σ⁻_int` series quantities.**
   The N1-restricted `tsum`
   `∑' k, if n1Pred a b k then coeffPlusGap a b k · c^(2k+2)/(k+1) else 0`
   is the **integrated counterpart** of `Σ⁺(c) = ∑' k, if n1Pred then
   coeffPlusGap_k · c^(2k) else 0` (the pointwise N1 sum). It carries a
   uniform `c² / (k+1)` weighting compared to `Σ⁺(c)`, integrating each
   `k`-th term over `[0, c]` against `2r dr`. The same is true for the
   N2 piece relative to `Σ⁻(c)`. **No prior workspace lemma introduces
   either of these integrated N1/N2-restricted quantities** — they are
   genuinely new analytical primitives.

   These quantities have a clean interpretation: each `k`-th term of
   `Σ⁺_int(c)` is the `k`-th coefficient's contribution to `diskExcess`
   restricted to N1 indices. The bulletin's "design a strictly stronger
   sufficient condition than the seed's `(15)`" axis is naturally
   accessed via per-`k` (per-coefficient) sufficient conditions, which
   require these integrated N1/N2 quantities to even state.

3. **First downstream consumer of sprint 042 in a series-partition
   chain.** Sprint 042 ships an unconditioned `tsum` identity. Every
   future analytical use of sprint 042 will eventually need to
   distinguish N1 (where `coeffPlusGap_k > 0`) from N2 (where
   `coeffPlusGap_k < 0`), since the sign structure governs which
   per-`k` inequalities can be combined termwise. Sprint 043 makes the
   partition explicit, so future `tsum_le_tsum`-style downstream chains
   can treat the N1 and N2 contributions independently — analogous to
   how sprint 027's partition was the prerequisite for sprints
   028/029/032/033/036/037/040/041's series-level analytical chains.

4. **Foundation for paper-axiom-free, oracle-cell-free closing reducer
   on the disk side via per-`k` comparison.** Once sprint 043 is in
   place, a future closing reducer can attempt to bound
   `diskExcess (circleGap a b) c` from above by a sum of per-`k`
   sufficient conditions:

   `diskExcess = (∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1))
                  - (∑'_{N2} coeffMinusGap_k · c^(2k+2)/(k+1))`

   `≤ (∑'_{N1} coeffPlusGap_k · c^(2k+2)/(k+1))` (drop the non-negative
   N2 piece, since `coeffMinusGap_k = ‖b k‖² − ‖a k‖² ≥ 0` on N2)

   This is the **first workspace bound** that drops a piece of `diskExcess`
   based on **N1/N2 partition sign structure** rather than on the
   pointwise `Σ⁺(r) ≤ Σ⁻(r)` comparison cell that all sprint 034/035/036
   chains require. The analytical content is **disjoint** from the
   `hSigmaCmp` route — sprint 043 trades the bulk `Σ⁺(c) ≤ Σ⁻(c)` cell
   for the structurally-derivable termwise sign structure of N1/N2.

5. **Integrated counterpart of sprint 027's pointwise equality.** Sprint
   027 establishes `circleGap r = Σ⁺(r) − r²·Z(r)` at fixed `r`. Sprint
   043 establishes `diskExcess (circleGap a b) c = Σ⁺_int(c) − Σ⁻_int(c)/?`
   at the integrated layer. Both are *equalities* (not bounds), both are
   paper-axiom-free, both use the same N1/N2 partition methodology. But
   sprint 043's RHS quantities are integrated against the disk-side
   measure `2r dr` over `[0, c]`, exposing per-`k` weights `c^(2k+2)/(k+1)`
   that no pointwise version can have. (Note: the precise relation between
   `Σ⁻_int(c) := ∑'_{N2} coeffMinusGap_k · c^(2k+2)/(k+1)` and
   `c²·Σ⁻(c) = c² · ∑'_{N2} coeffMinusGap_k · c^(2k)` is **not**
   `Σ⁻_int(c) = c²·Σ⁻(c)`: each `k`-th term of `Σ⁻_int(c)` carries weight
   `c^(2k+2)/(k+1)` while the corresponding `c²·Σ⁻(c)` term carries weight
   `c^(2k+2)` — the `1/(k+1)` factor is the integration weight from
   `∫₀^c 2r · r^(2k) dr = c^(2k+2)/(k+1)`. So sprint 043 introduces a
   genuinely new quantity, **not** a renaming of `c²·Σ⁻(c)`.)

6. **Strict structural upgrade over sprint 042's identity.** Sprint 042's
   RHS is a single unconditioned `tsum` whose termwise sign varies with
   `k` (positive on N1, negative on N2 for the typical `(a, b)`). Sprint
   043's RHS exposes the sign structure explicitly: the N1 piece is a
   sum of non-negative termwise contributions, the N2 piece is a sum
   of non-negative termwise contributions (after the sign swap from
   `coeffPlusGap` to `coeffMinusGap`). This is **strictly more
   informative** than sprint 042's bulk `tsum` — it allows future
   sprints to apply termwise inequalities to the two pieces
   independently, with consistent sign discipline on each.

7. **Independent of sprint 041.** Sprint 041 ships the function-level
   integrated equality `annulusSlice = ∫ 2ρ·Σ⁺ − ∫ 2ρ³·Z` for any
   `[α, β]`. Sprint 043 ships the termwise integrated partition for
   `diskExcess` only. The two are **complementary**: 041 gives a
   function-level decomposition (no termwise structure but covers all
   windows including annulus), 043 gives a termwise decomposition (full
   per-`k` structure but only at the disk window `[0, c]`). After both
   are in place, future sprints can compare the function-level annulus
   side (041's annulus specialisation) against the termwise disk side
   (043) — a comparison shape unavailable in either direction
   individually.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V43 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is a new lemma layer (integrated × N1/N2-restricted
  `tsum`), not a numerical refinement of an existing closed-form
  coefficient.

Why this is **not** "the same chain" as sprint 042:

* **Unconditioned `tsum` vs N1/N2-partitioned `tsum`.** Sprint 042's
  RHS is `∑' k, coeffPlusGap_k · c^(2k+2)/(k+1)` (no partition).
  Sprint 043's RHS is `(∑'_{N1} coeffPlusGap_k · ...) - (∑'_{N2} coeffMinusGap_k · ...)`
  (explicit N1/N2 partition with sign swap on N2). Different RHS shape.
* **No partition machinery in 042.** Sprint 042's body uses
  `MeasureTheory.integral_tsum_of_summable_integral_norm` and termwise
  integration. Sprint 043's body uses
  `Summable.indicator`, `Summable.tsum_add`, `tsum_congr`, `tsum_neg` —
  the `tsum`-partition family from sprint 027. Disjoint Mathlib
  machinery families.
* **Different downstream consumer pattern.** Sprint 042's identity is
  consumed by termwise per-`k` numerical analysis. Sprint 043's identity
  is consumed by N1/N2-aware sign-disciplined chains (e.g., dropping
  the non-negative `Σ⁻_int` piece, or applying `tsum_le_tsum` to the
  N1 piece independently of the N2 piece).

Why this is **not** "the same chain" as sprint 027:

* **Pointwise vs integrated.** Sprint 027 partitions at fixed `r`.
  Sprint 043 partitions at the integrated layer. Different layers.
* **Different summands.** Sprint 027's summand is
  `coeffPlusGap_k · r^(2k)`. Sprint 043's summand is
  `coeffPlusGap_k · c^(2k+2)/(k+1)` — carries the integration weight
  `1/(k+1)` that has no analog at the pointwise layer.
* **Different RHS shape.** Sprint 027's RHS is `Σ⁺(r) − r²·Z(r)` (a
  function-level expression in pre-existing series quantities). Sprint
  043's RHS is `Σ⁺_int(c) − Σ⁻_int(c)`, where `Σ⁺_int`/`Σ⁻_int` are
  **brand-new integrated `tsum` quantities**, not renamings of any
  prior workspace quantity.

Why this is **not** "the same chain" as sprints 040/041:

* **Sprint 040** ships an *inequality* `diskExcess ≤ c²·Σ⁺(c)` after
  dropping the non-negative `−r²·Z` integrand. Sprint 043 ships an
  *equality* with both N1 and N2 pieces retained. An equality is
  strictly stronger than an inequality.
* **Sprint 041** ships a function-level integrated *equality*
  `annulusSlice = ∫ 2ρ·Σ⁺ − ∫ 2ρ³·Z` for any `[α, β]`. Sprint 043
  ships a termwise integrated *equality* for `diskExcess` only at
  `[0, c]`. The two equalities are at different layers (function-level
  vs termwise), produce different RHS shapes (function-level integrals
  vs termwise `tsum`s), and target different windows
  (any `[α, β] ⊂ [0, 1)` vs only `[0, c]`).

Why this is **bounded enough for one Generator session**:

* The proof body is the **composition of two existing patterns**:
  sprint 042's invocation (one line) followed by sprint 027's
  partition skeleton (lines 3911–4026, ~115 lines) with `f` rebound
  to the integrated summand.
* The summability transfer step (sprint 042's `Summable (|·|)` cell to
  sprint 043's `Summable (·)` requirement) is one application of
  `Summable.of_nonneg_of_le` or `Summable.of_norm_bounded` — well-tested
  in pinned Mathlib, ~5–10 lines.
* The termwise sign-swap identity `coeffPlusGap_k = -coeffMinusGap_k`
  (only on N2; off N2 both sides are 0) is verbatim sprint 027 line
  3996–4006, ~10 lines.
* No new Mathlib lemmas are needed beyond what sprints 027 and 042
  already use. No new `MeasureTheory` machinery.
* Estimated body length: **~100–150 lines** (sprint 042's invocation +
  the sprint 027 skeleton with new `f`, plus the summability transfer).

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* All ingredients (`Summable.indicator`, `Summable.tsum_add`,
  `tsum_congr`, `tsum_neg`, `Summable.of_norm_bounded`) are already
  consumed by prior sprints (027, 028, 032). No new Mathlib lemma
  archaeology needed.
* The summability transfer from `Summable (|f|)` to `Summable f` is
  standard — `Summable.of_norm_bounded` (or `Summable.of_abs` after
  normalising via `Real.norm_eq_abs`) provides the dispatch in one
  step.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem `diskExcess_eq_tsum_partition_via_series` after
  sprint 042's `diskExcess_eq_tsum_via_termwise_integration` (current
  end of `Reduction.lean`, after line 6681).

  Estimated body length: ~100–150 lines.

  The proof body structure (high-level):

  1. **Apply sprint 042** to get the unconditioned identity:
     ```lean
     have h_sprint042 :
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
           ∑' k : ℕ,
             PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
       diskExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
         hc_nonneg hSummable_int_norm
     ```

  2. **Define the three summand families** (mirroring sprint 027's
     `f`/`f1`/`f2`/`g2`):
     ```lean
     set f : ℕ → ℝ := fun k =>
       PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
       with hf_def
     set f1 : ℕ → ℝ := fun k =>
       if PaperAxioms.n1Pred a b k then
         PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
       else 0 with hf1_def
     set f2 : ℕ → ℝ := fun k =>
       if PaperAxioms.n2Pred a b k then
         PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
       else 0 with hf2_def
     set g2 : ℕ → ℝ := fun k =>
       if PaperAxioms.n2Pred a b k then
         PaperAxioms.coeffMinusGap a b k * c ^ (2 * k + 2) / (k + 1)
       else 0 with hg2_def
     ```

  3. **Establish summability of `f`, `f1`, `f2`, `g2`** from
     `hSummable_int_norm` (sprint 042's input cell):
     ```lean
     -- f is summable from the dominated summability of |f|.
     have hSummable_f : Summable f := by
       refine Summable.of_norm_bounded
         (fun k =>
           |PaperAxioms.coeffPlusGap a b k| *
             c ^ (2 * k + 2) / (k + 1))
         hSummable_int_norm
         ?_
       intro k
       -- ‖f k‖ = |coeffPlusGap_k * c^(2k+2)/(k+1)|
       --       ≤ |coeffPlusGap_k| * c^(2k+2)/(k+1)
       -- since c^(2k+2)/(k+1) ≥ 0.
       sorry  -- Generator: discharge with abs_mul, abs_div, abs_pow,
              -- |c^...| = c^... (since c ≥ 0), and (k+1) > 0.
     have hSummable_f1 : Summable f1 := by
       have h_indicator :
           Summable ({k | PaperAxioms.n1Pred a b k}.indicator f) :=
         hSummable_f.indicator {k | PaperAxioms.n1Pred a b k}
       have h_eq : f1 = {k | PaperAxioms.n1Pred a b k}.indicator f := by
         funext k; simp [f1, f, Set.indicator]
       rw [h_eq]; exact h_indicator
     have hSummable_f2 : Summable f2 := by
       -- analogous to hSummable_f1
       sorry
     have hSummable_g2 : Summable g2 := by
       -- g2 differs from f2 only by the termwise sign swap on N2;
       -- summability is equivalent (verified via tsum_congr-style argument
       -- or by noting g2 = -f2 termwise on N2).
       sorry
     ```

  4. **Termwise partition identity `f k = f1 k + f2 k`** — verbatim from
     sprint 027 lines 3927–3954:
     ```lean
     have h_n1_to_n2 :
         ∀ k, ¬ PaperAxioms.n1Pred a b k → PaperAxioms.n2Pred a b k := by
       intro k hk
       unfold PaperAxioms.n1Pred at hk
       unfold PaperAxioms.n2Pred
       push_neg at hk
       exact ⟨Nat.pos_of_ne_zero hk.1, hk.2⟩
     have h_n2_to_not_n1 :
         ∀ k, PaperAxioms.n2Pred a b k → ¬ PaperAxioms.n1Pred a b k := by
       intro k hk2 hk1
       unfold PaperAxioms.n2Pred at hk2
       unfold PaperAxioms.n1Pred at hk1
       obtain ⟨hk_pos, hab⟩ := hk2
       rcases hk1 with h | h
       · exact (Nat.lt_irrefl 0 (h ▸ hk_pos))
       · exact (not_lt_of_ge h) hab
     have h_term_partition : ∀ k, f k = f1 k + f2 k := by
       intro k
       by_cases hk1 : PaperAxioms.n1Pred a b k
       · have hk2 : ¬ PaperAxioms.n2Pred a b k := fun hcontra =>
           h_n2_to_not_n1 k hcontra hk1
         simp [f, f1, f2, hk1, hk2]
       · have hk2 : PaperAxioms.n2Pred a b k := h_n1_to_n2 k hk1
         simp [f, f1, f2, hk1, hk2]
     ```

  5. **`(∑' k, f k) = (∑' k, f1 k) + (∑' k, f2 k)`** via
     `tsum_congr` + `Summable.tsum_add` (sprint 027 line 3978–3982
     verbatim):
     ```lean
     have h_tsum_partition :
         (∑' k, f k) = (∑' k, f1 k) + ∑' k, f2 k := by
       have h_congr : (∑' k, f k) = ∑' k, (f1 k + f2 k) :=
         tsum_congr h_term_partition
       rw [h_congr, hSummable_f1.tsum_add hSummable_f2]
     ```

  6. **Termwise sign-swap identity on N2** (sprint 027 lines 3996–4006
     verbatim with the new summand):
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

  7. **Chain everything:**
     ```lean
     calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
         = ∑' k : ℕ,
             PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
           h_sprint042
       _ = ∑' k, f k := rfl
       _ = (∑' k, f1 k) + ∑' k, f2 k := h_tsum_partition
       _ = (∑' k, f1 k) + (-∑' k, g2 k) := by rw [h_f2_eq_neg_g2]
       _ = (∑' k, f1 k) - ∑' k, g2 k := by ring
     ```
     Then close with `change` or `rfl` to identify `f1` and `g2` with
     their indicator-form `if … then … else 0` expressions in the
     conclusion.

- `ProofRefinement/Korenblum/Candidates/V43.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V42),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V42),
  4. Adds two side lemmas exercising the new generic identity:
     - `v43_diskExcess_eq_tsum_partition_compiles` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; applies the new theorem at the seed
       `c = c_value`; conclusion is the new partition equality
       `diskExcess (circleGap a b) c_value = (∑'_{N1} ...) - (∑'_{N2} ...)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v43_diskExcess_eq_tsum_partition_recovers_sprint042_at_seed` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; applies the new theorem at the seed
       and demonstrates that re-aggregating the partition recovers
       sprint 042's unconditioned `tsum` form. The body invokes both
       sprints 042 and 043 at the seed, then uses `linarith` /
       `omega` / a re-applied partition argument to show the two
       RHS expressions are equal. (Acceptable simplification: if the
       full re-aggregation is friction-heavy, the side lemma may stop
       at a tautological compilation check after invoking sprint 043
       — the structural point of the side lemma is that the new
       partition identity is *consistent with* sprint 042's
       unconditioned identity, not that the Generator must
       algebraically re-derive sprint 042 from sprint 043.)
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V42) — the new partition
     identity is materialised in side lemmas, **not** as the sink
     theorem's discharge route.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V43` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V43.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V43 ties V42 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V43.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `diskExcess_eq_tsum_partition_via_series` appears
   in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V43.lean`'s two side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken —
   sprint 043's signature is `(a, b, c)`-only with no `K` and no
   `paper`.)
7. The proof body invokes
   `diskExcess_eq_tsum_via_termwise_integration` (sprint 042) at
   least once. Greppable check: count of
   `diskExcess_eq_tsum_via_termwise_integration` in the body of the
   new theorem is **≥ 1**.
8. The proof body invokes `Summable.indicator` at least twice (once
   for `f1`'s summability over `{k | n1Pred a b k}`, once for `f2`'s
   summability over `{k | n2Pred a b k}`). Greppable check: count of
   `.indicator` in the body of the new theorem is **≥ 2**.
9. The proof body invokes `Summable.tsum_add` (or equivalently
   `.tsum_add`) at least once for the partition-sum step. Greppable
   check: count of `.tsum_add` in the body of the new theorem is
   **≥ 1**.
10. The proof body invokes `tsum_congr` at least twice (once for the
    partition lift, once for the N2 sign-swap lift). Greppable check:
    count of `tsum_congr` in the body of the new theorem is **≥ 2**.
11. The proof body invokes `tsum_neg` at least once for the N2
    sign-swap pull-out step. Greppable check: count of `tsum_neg` in
    the body of the new theorem is **≥ 1**.
12. The new theorem's conclusion is an **equality** (not an
    inequality): the conclusion contains `=` between
    `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c` and the
    `(∑'_{N1} ...) - (∑'_{N2} ...)` RHS. Greppable check: in the
    new theorem's signature line, the substring `≤` does not appear
    in the conclusion.
13. The new theorem **does not invoke** sprint 027's
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` —
    sprint 043 partitions at the integrated layer (after sprint 042),
    not at the pointwise layer. Greppable check: count of
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    in the body of the new theorem is **0**.
14. The new theorem **does not invoke** any of sprints 003 / 013 /
    026 / 030 / 031 / 034 / 040's `diskExcess_upper_bound_*`
    lemmas. Sprint 043 is built on top of sprint 042 (an *equality*),
    not on any prior bound. Greppable check: in the new theorem
    body, counts of `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`,
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_via_eq3_eq4`,
    `diskExcess_upper_bound_via_series_eq4_only_two_Z`,
    `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`,
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    are all **0**.
15. The new theorem **does not invoke** `paperLambda` anywhere in
    its proof body or signature. Greppable check: count of
    `paperLambda` in the new theorem (signature + body) is **0**.
16. The V43 `_compiles` side lemma's conclusion is the new
    partition equality at `c = c_value`, with the
    `hSummable_int_norm` cell as a universally-quantified
    hypothesis on the side lemma.
17. The V43 `_recovers_sprint042_at_seed` side lemma takes the same
    universally-quantified `(a, b)` and `hSummable_int_norm` cell;
    applies sprint 043 at the seed; demonstrates a tautological
    compilation check (or a full algebraic re-derivation back to
    sprint 042's RHS — either is acceptable).

## Out of scope

- Edit older candidates V0–V42.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V43 is
  the same `hEq15_seed_3554` that V0–V42 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the `hSummable_int_norm` hypothesis cell from the
  workspace's existing N1/N2 series-summability lemmas (sprints
  011, 012, 032). This is queueable as a separate sprint.
- Ship a closing reducer fusing sprint 043 with sprint 041's
  annulus-side identity to produce a paper-axiom-free, oracle-free
  `valid_of_*` reducer. That is the **next** sprint's scope after
  043 lands; sprint 043 ships only the disk-side termwise partition
  equality. Reason: the termwise comparison of disk-side and
  annulus-side `tsum` identities, plus the convergence/integrability
  bookkeeping for the annulus-side termwise expansion, is a separate
  analytical sprint.
- Ship a witness at any `c > 0.3554`. Sprint 043 does not raise
  `c_value`. The eventual numerical push is a *consumer* of sprint
  043 + a future closing reducer + the kernel inequality
  evaluation, not sprint 043 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15`
  to any new chain. The new identity is materialised in side
  lemmas only.
- Ship the analogous N1/N2 partition for sprint 041's
  `annulusSlice_eq_via_series_partition`. This is a natural
  follow-up sprint but is out of scope here — sprint 041's
  identity uses function-level integrals (`∫ 2ρ·Σ⁺` and
  `∫ 2ρ³·Z`), so the analogous partition would partition each of
  those two function-level integrals along N1/N2, requiring a
  swap-of-sum-and-integral step (sprint 042-style machinery) that
  is not available in sprint 041's body.
- Ship per-`k` numerical sufficient conditions for the disk-vs-annulus
  inequality. That is a *consumer* of sprint 043 and is queueable as
  a separate sprint.
- Re-derive sprint 042 as a corollary of sprint 043 (by re-aggregating
  the partition into a single `tsum`). The `_recovers_sprint042_at_seed`
  side lemma is allowed to stop at a tautological check; full algebraic
  re-derivation is out of scope.

## Time budget

≤ 90 minutes runtime. (Sprint 043's body is the **composition of two
existing patterns**: sprint 042's invocation (one line) + sprint
027's partition skeleton (~115 lines) with `f` rebound to the
integrated summand, plus a summability transfer step (~10 lines)
and the final algebraic chain (~10 lines). Estimated body: ~100–150
lines. The two V43 side lemmas reuse the universally-quantified
hypothesis pattern from V42's `_compiles` and
`_recovers_via_eq4_at_seed` side lemmas, ~20–40 lines each. Total
V43 size: ≤ 200 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* The summability transfer step (from sprint 042's `Summable (|f|)`
  cell to sprint 043's `Summable f` requirement) is dischargeable
  via `Summable.of_norm_bounded` with the bound
  `‖f k‖ = |coeffPlusGap_k * c^(2k+2)/(k+1)|
        ≤ |coeffPlusGap_k| * c^(2k+2)/(k+1)`
  (the bound is in fact an *equality* since `c^(2k+2)/(k+1) ≥ 0`).
  Use `abs_mul`, `abs_div`, `abs_pow`, `abs_of_nonneg` for the
  algebraic manipulations. Alternatively, use `Summable.of_abs` if
  pinned Mathlib provides that direct route.

* The N1 summand `f1 k = if n1Pred a b k then coeffPlusGap_k *
  c^(2k+2)/(k+1) else 0` is **definitionally equal** to the indicator
  expression `({k | n1Pred a b k}.indicator f) k`. Sprint 027 lines
  3956–3964 demonstrate the `funext + simp [Set.indicator]` pattern
  for this identification — verbatim usage in sprint 043.

* The N2 summand `f2 k = if n2Pred a b k then coeffPlusGap_k *
  c^(2k+2)/(k+1) else 0` is similarly identified with
  `({k | n2Pred a b k}.indicator f) k`. Sprint 027 lines 3966–3974
  demonstrate the analogous pattern.

* The N2 sign-swap identity `coeffPlusGap_k = -coeffMinusGap_k` (only
  on N2; off N2 both sides are 0) is dispatched by
  `unfold PaperAxioms.coeffPlusGap PaperAxioms.coeffMinusGap` followed
  by `ring`. Sprint 027 line 3998–4002 documents this exact pattern.

* The `tsum_congr` + `tsum_neg` combination for the N2 piece pulls
  the negative out of the `tsum`. Sprint 027 line 4004–4006 documents
  this exact pattern.

* The final `change` / `rfl` step to identify the `f1`-form
  `∑' k, if n1Pred a b k then ... else 0` with the conclusion's
  identical RHS expression should be a one-liner. If `change` does
  not fully reduce, try `simp only [hf1_def, hg2_def]` followed
  by `rfl`, or unpack the `set` definitions manually.

* The V43 `_compiles` side lemma's expected shape:
  ```lean
  theorem v43_diskExcess_eq_tsum_partition_compiles
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / (k + 1))) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value =
        (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c_value ^ (2 * k + 2) / (k + 1)
          else 0)
          - ∑' k : ℕ,
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  c_value ^ (2 * k + 2) / (k + 1)
              else 0 :=
    diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
      c_value_nonneg hSummable_int_norm
  ```

* The V43 `_recovers_sprint042_at_seed` side lemma's expected shape:
  ```lean
  theorem v43_diskExcess_eq_tsum_partition_recovers_sprint042_at_seed
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / (k + 1))) :
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k *
          c_value ^ (2 * k + 2) / (k + 1) =
        (∑' k : ℕ,
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k *
              c_value ^ (2 * k + 2) / (k + 1)
          else 0)
          - ∑' k : ℕ,
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k *
                  c_value ^ (2 * k + 2) / (k + 1)
              else 0 := by
    -- Both sides equal `diskExcess (circleGap a b) c_value` by sprints
    -- 042 and 043 respectively. Chain via transitivity.
    rw [← diskExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
          c_value_nonneg hSummable_int_norm]
    exact diskExcess_eq_tsum_partition_via_series (a := a) (b := b)
      c_value_nonneg hSummable_int_norm
  ```
  (Acceptable simplification per the contract: if the chained form
  is friction-heavy, the side lemma may stop at a tautological
  compilation check after invoking sprint 043 alone.)
