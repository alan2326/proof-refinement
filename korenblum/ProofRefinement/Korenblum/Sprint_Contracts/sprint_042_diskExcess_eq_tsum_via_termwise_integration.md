# Sprint 042: First paper-axiom-free **`tsum`-of-integrals closed-form identity** for `diskExcess (circleGap a b) c` via Mathlib's `MeasureTheory.integral_tsum_of_summable_integral_norm` (termwise integration of `circleGapSeries`)

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V41.lean`
**Target file**: `Candidates/V42.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_eq_tsum_via_termwise_integration
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 2) / (k + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
```

The proof body:

1. **Unfold `diskExcess` to its `intervalIntegral` form.**
   `PaperAxioms.diskExcess (circleGap a b) c =
    ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r`
   (definitional; this is the disk-side `annulusSlice (circleGap a b) 0 c`,
   matching sprint 041's disk-side specialisation pattern).

2. **Pointwise series unfold of `circleGap a b r`.**
   On `r ∈ Set.uIcc 0 c = [0, c]`,
   `circleGap a b r = circleGapSeries a b r =
    ∑' k, coeffPlusGap a b k * r ^ (2 * k)` (definitional, `rfl`).
   So `2r · circleGap a b r = ∑' k, 2r · coeffPlusGap a b k * r ^ (2 * k)
                            = ∑' k, 2 · coeffPlusGap a b k * r ^ (2 * k + 1)`.
   Lift to a pointwise integrand identity on `[0, c]` via `intervalIntegral.integral_congr`
   (no a.e.-upgrade needed).

3. **Define the termwise function family**
   `F : ℕ → ℝ → ℝ`, `F k r := 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1)`.

4. **Establish termwise integrability and the sum-norm summability hypothesis.**
   Each `F k` is a polynomial in `r`, hence
   `IntervalIntegrable (F k) volume 0 c` (via
   `Polynomial.intervalIntegrable` or `Continuous.intervalIntegrable`
   composed with `continuous_pow` + `continuous_const_mul`).
   The `L¹` norm on `[0, c]` is
   `∫ r in 0..c, ‖F k r‖ = ∫ r in 0..c, |2 · coeffPlusGap a b k| · r^(2k+1)
                         = |coeffPlusGap a b k| · c^(2k+2) / (k+1)`
   (using `c ≥ 0` to drop the absolute value on `r^(2k+1)`, and
   `@integral_pow 0 c (2k+1)` to give
   `c^(2k+2) / (2k+2) = c^(2k+2) / (2(k+1))`, then multiply by the leading
   `2|coeffPlusGap a b k|` to get `|coeffPlusGap a b k| · c^(2k+2) / (k+1)`).
   So the `Summable (fun k => ∫ r in 0..c, ‖F k r‖)` hypothesis is exactly
   the lemma's `hSummable_int_norm`.

5. **Apply `MeasureTheory.integral_tsum_of_summable_integral_norm`**
   (Mathlib pinned `MeasureTheory/Integral/DominatedConvergence.lean:156`):
   `∑' k, ∫ r, F k r ∂μ = ∫ r, ∑' k, F k r ∂μ`,
   for the measure `μ := volume.restrict (Set.uIoc 0 c)` (so the integrals
   become `intervalIntegral` expressions). The conversion uses
   `intervalIntegral.intervalIntegral_eq_integral_uIoc` (or
   `intervalIntegral_eq_integral_of_le hc_nonneg` since `0 ≤ c`).

6. **Compute each termwise integral in closed form.**
   `∫ r in 0..c, F k r = ∫ r in 0..c, 2 · coeffPlusGap a b k · r^(2k+1)
                      = 2 · coeffPlusGap a b k · c^(2k+2) / (2k+2)
                      = coeffPlusGap a b k · c^(2k+2) / (k+1)`,
   using `intervalIntegral.integral_const_mul` and `@integral_pow 0 c (2*k+1)`,
   followed by `field_simp` / `ring` to normalize the denominator.

7. **Chain everything.**
   `diskExcess (circleGap a b) c
    = ∫ r in 0..c, 2r · circleGap a b r
    = ∫ r in 0..c, ∑' k, 2 · coeffPlusGap a b k · r^(2k+1)   -- step 2
    = ∑' k, ∫ r in 0..c, 2 · coeffPlusGap a b k · r^(2k+1)   -- step 5
    = ∑' k, coeffPlusGap a b k · c^(2k+2) / (k+1)            -- step 6`.

This is the workspace's **first lemma at the `tsum`-of-integrals layer** —
every prior workspace lemma either:

* operates on a *single* (pointwise or fixed-window) inequality / equality on
  the **function** `circleGap a b r` (sprints 002, 005, 011, 012, 015, 016,
  022, 025, 027, 028, 029, 032, 033, 036, 037), or
* integrates *one* such function-level (in)equality once over a fixed window
  (sprints 003, 006, 007, 013, 026, 030, 031, 034, 038, 040, 041),

but **none** ever swaps a `tsum` past an `intervalIntegral`. Sprint 042 is the
first.

The conclusion is a **closed-form `tsum` equality** expressing `diskExcess`
purely in series coefficients (`coeffPlusGap a b k`) and a single radial
parameter (`c`). The shape `∑' k, coeffPlusGap a b k · c^(2k+2) / (k+1)` is a
**new RHS shape** for `diskExcess`, distinct from every prior RHS (`c⁴·Z_c`,
`c²·Σ⁺(c)`, `(c⁴/6)·(...)·Z_c + (c⁶/6)/(...)·Z_ρ`, `c⁴·Z_ρ`, etc.).
The kernel-side identity is also termwise-explicit (each `k`-th summand
is computable in closed form from `(a k, b k, c)` alone), unlocking
**termwise** numerical and analytical comparisons against any annulus-side
representation in future sprints — including the analogous termwise expansion
of `annulusSlice (circleGap a b) c β` that sprint 041's identity sets up.

Then ship a `Candidates/V42.lean` at the same `c = 0.3554` that compiles,
scores `≥ V41 = 1777/5000`, and **materialises** the new identity in two side
lemmas:

- `v42_diskExcess_eq_tsum_compiles` — signature compilation of the new
  identity at the seed (universally-quantified `(a, b)` and the
  summability hypothesis).
- `v42_diskExcess_eq_tsum_recovers_via_eq4_at_seed` — when a
  `Section2Assumptions a b K c_value` instance is available, the new
  `tsum` identity's RHS bounds via `paper.eq4_sigmaPlus_bound`'s
  termwise consequence (`coeffPlusGap a b k = ‖a k‖² − ‖b k‖² ≤ 0`
  on N2, and the `Σ⁺(c) ≤ Σ⁻(c) = c²·Z_c` algebraic chain) connect
  back to sprint 026's `c⁴·Z_c` shape — *not* by reproducing sprint
  026's exact bound, but by exhibiting that the new termwise identity
  is **strictly more refined** (it gives an exact value, not an upper
  bound), so any inequality previously derived as a function-level
  upper bound is recoverable from sprint 042 plus a termwise comparison.

The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 042 ships:

1. **First workspace lemma at the `tsum`-of-integrals layer.** Every prior
   workspace lemma operates at one of three layers:

   | Layer | Description | Sprints |
   |-------|-------------|---------|
   | function-level pointwise | (in)equality on `circleGap a b r` for fixed `r` | 002, 011, 012, 015, 016, 022, 025, 027, 028, 029, 032, 033, 036, 037 |
   | function-level series-partition `tsum` | `tsum`-partition equality on `circleGapSeries a b r` for fixed `r` | 005, 027, 028 |
   | function-level integrated | `intervalIntegral` of a function-level (in)equality over a fixed window `[α, β]` | 003, 006, 007, 013, 026, 030, 031, 034, 038, 040, 041 |
   | **`tsum`-of-integrals** | **`∑' k, ∫ F k`** (or its swap to **`∫ ∑' k, F k`**) | **042 (NEW)** |

   The new layer is *qualitatively distinct* from all three predecessors. It
   composes a `tsum` over the series index `k` *outside* an `intervalIntegral`
   over the radial variable `r`, exposing each `k`-th termwise integral as an
   independently-computable quantity. This unlocks **per-coefficient** (per-`k`)
   analytical and numerical handling of `diskExcess` for the first time.

2. **First workspace consumer of `MeasureTheory.integral_tsum`-style
   swap-of-sum-and-integral machinery.** The Mathlib lemma
   `MeasureTheory.integral_tsum_of_summable_integral_norm`
   (`MeasureTheory/Integral/DominatedConvergence.lean:156`) is the canonical
   tool for swapping `∑'` and `∫`, and is the natural Mathlib entry-point for
   any `tsum`-of-integrals lemma over a `ℕ`-indexed series. No prior workspace
   lemma uses it; sprint 042 is the first.

   Mathlib also exposes `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`
   (`DominatedConvergence.lean:265`), which is the `intervalIntegral`-form
   counterpart taking continuous functions in `C(ℝ, E)`. Sprint 042 may use
   either; the contract recommends `integral_tsum_of_summable_integral_norm`
   composed with `intervalIntegral_eq_integral_of_le` for cleaner bookkeeping
   (no `C(ℝ, ℝ)` packaging boilerplate), but the Generator may pick whichever
   is easier to discharge.

3. **First workspace closed-form *exact identity* (not bound) for
   `diskExcess`.** Every prior `diskExcess` workspace lemma is an *upper
   bound* (sprints 003, 013, 026, 030, 031, 034, 040 ship inequalities on
   `diskExcess`). Sprint 041 ships an *equality* for `annulusSlice (circleGap
   a b) α β` decomposed into two function-level integrals (`∫ 2ρ·Σ⁺` and
   `∫ 2ρ³·Z`), but each summand is still a function-level integrated
   quantity — there is no termwise expression. Sprint 042 ships a
   **termwise-explicit** equality: for each `k`, the contribution is
   `coeffPlusGap a b k · c^(2k+2) / (k+1)`, a closed-form polynomial in `c`
   with computable coefficients.

4. **Different consumer pattern from sprint 041.** Sprint 041's
   disk-side specialisation gives
   `diskExcess (circleGap a b) c = ∫₀^c 2ρ·Σ⁺(ρ) − ∫₀^c 2ρ³·Z(ρ)`
   — a difference of two function-level integrals. To get a closed form,
   one must further bound or evaluate the two integrals (e.g., sprint 040
   uses `Σ⁺` monotonicity and drops the `Z`-integral). Sprint 042 gives
   a termwise series instead, which is **structurally complementary**:
   sprint 041 + 042 together expose `diskExcess` as both an integrated
   difference and a termwise series, and any future closing reducer can
   pick whichever representation fits its kernel best.

5. **First workspace lemma whose conclusion is `∑'` of a closed-form
   polynomial in `c` with explicit per-`k` coefficients.** This unlocks a
   new analytical axis: **partial-sum truncation**, **termwise comparison**,
   **per-`k` numerical witnesses**, and **closed-form per-`k` coefficient
   bounds**. None of these are accessible with the existing function-level
   integrated bounds (sprints 003/013/026/030/034/040 give a single bulk
   number; sprint 042 gives a series whose tail can be analysed
   independently of the head).

6. **Foundation for paper-axiom-free, oracle-cell-free closing reducer
   on the disk side.** Once sprint 042 is in place, a future closing
   reducer can attempt to bound `diskExcess (circleGap a b) c` from above
   by **truncating** the new series at finite `k` — `∑' k, coeffPlusGap k ·
   c^(2k+2)/(k+1) ≤ ∑_{k=0}^N coeffPlusGap k · c^(2k+2)/(k+1) +
   tail_bound(N, c)` — for **any** `(a, b)` satisfying the summability
   hypothesis, with **zero paper-axiom invocations** and **zero oracle
   cells** in the upper bound. The bulletin notes (sprint 041 §6) that
   the naive function-level series-only kernel
   `c²·Σ⁺(c) ≤ Σ⁺(c)·(β²−c²) − Z(β)·(β⁴−c⁴)/2`
   is degenerate. A **termwise** kernel via sprint 042 is structurally
   distinct: each `k`-th term contributes
   `coeffPlusGap a b k · c^(2k+2)/(k+1)`, and the disk-vs-annulus
   inequality factors into termwise comparisons that can hold even when
   the function-level analogue does not.

7. **Strict structural upgrade over sprint 026's `c⁴·Z_c` bound.** Sprint
   026's bound is `diskExcess ≤ c⁴ · sigmaZeroMinus a b c`, derived by
   pointwise-bounding `circleGap r ≤ sigmaPlus r ≤ c²·Z_c` for `r ∈
   [0, c]` then integrating against `2r`. Sprint 042 gives the **exact**
   value via termwise integration: `diskExcess = ∑' k, coeffPlusGap a b k
   · c^(2k+2)/(k+1)`. The `c⁴·Z_c` bound recovers as a (loose) upper bound
   on the new exact series:
   `coeffPlusGap a b k · c^(2k+2)/(k+1) ≤ |coeffPlusGap a b k| · c^(2k+2)
                                       ≤ |coeffPlusGap a b k| · c⁴ · c^(2k-2)
                                       ≤ ‖a k‖²·c⁴·c^(2k-2)` (etc.),
   and after a fair amount of bookkeeping reduces to `c⁴·Σ⁺(c)/c² · Z_c`
   ≈ `c²·Σ⁺(c)` ≈ sprint 040's bound (modulo `paper.eq4`). Sprint 042 is
   thus **strictly more informative** than every prior disk-side bound:
   each prior bound is an inequality on a coarse aggregate; sprint 042 is
   an equality at the per-coefficient level.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V42 still discharges the sink theorem
  via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is a new lemma *layer* (`tsum`-of-integrals), not a
  numerical refinement of an existing closed-form coefficient.

Why this is **not** "the same chain" as sprint 040:

* **Function-level integrated vs `tsum`-of-integrals.** Sprint 040 stays at
  the function-level integrated layer: it bounds `∫₀^c 2r·Σ⁺(r)` by
  `c²·Σ⁺(c)` via function-level monotonicity. Sprint 042 swaps the `tsum`
  past the `∫`, then evaluates each termwise integral in closed form.
  Different layer, different Mathlib machinery
  (`integral_tsum_of_summable_integral_norm` is used **nowhere** in the
  workspace yet).
* **Inequality vs equality.** Sprint 040 ships an inequality; sprint 042
  ships an equality.
* **Function-level vs termwise.** Sprint 040's RHS is `c²·sigmaPlus a b c`
  (one bulk number). Sprint 042's RHS is `∑' k, coeffPlusGap a b k ·
  c^(2k+2)/(k+1)` (a per-`k` series).

Why this is **not** "the same chain" as sprint 041:

* **`tsum`-of-integrals vs function-level integrated equality.** Sprint
  041 ships an equality at the function-level integrated layer
  (`annulusSlice = ∫ 2ρ·Σ⁺ − ∫ 2ρ³·Z`). Sprint 042 ships an equality at
  the `tsum`-of-integrals layer (`diskExcess = ∑' k, ...`).
* **Different Mathlib machinery.** Sprint 041 uses
  `intervalIntegral.integral_sub` and `intervalIntegral.integral_congr`.
  Sprint 042 uses `MeasureTheory.integral_tsum_of_summable_integral_norm`
  (or `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`).
  Disjoint Mathlib import surfaces.
* **Different consumer pattern.** Sprint 041's identity is consumed by
  *function-level* downstream chains (e.g. integrate the difference
  further, drop a non-negative summand). Sprint 042's identity is
  consumed by *termwise* downstream chains (e.g. truncate at finite `k`,
  bound the tail).

Why this is **not** "the same chain" as sprints 025/027/028/032/033:

* **Sprints 025/027/028/032/033 are all function-level series-partition
  lemmas at fixed `r`** — they manipulate the `tsum` over `k` for a
  *single, fixed* radial value. Sprint 042 manipulates the `tsum` over
  `k` *jointly with* an integral over `r ∈ [0, c]`, which is a
  fundamentally different operation requiring the `integral_tsum`
  swap-of-sum-and-integral machinery (not used by any of 025/027/028/
  032/033).
* **Sprints 025/027/028/032/033 produce function-level statements at
  fixed `r`** (`circleGap r ≤ Σ⁺(r)`, `circleGap r = Σ⁺(r) − r²·Z(r)`,
  `Z(c) ≤ μ₁·Z(r) + μ₂·Z(ρ)`, etc.). Sprint 042 produces an
  integrated-statement (`diskExcess`) — a fundamentally different
  conclusion shape.

Why this is **bounded enough for one Generator session**:

* The proof body decomposes cleanly into 7 small steps (listed above), each
  of which is a verbatim Mathlib invocation with at most 1–2 lines of
  algebraic glue (`field_simp` / `ring`).
* All sprint 042 ingredients are already in Mathlib pinned at v4.28.0
  (verified by Planner: `MeasureTheory.integral_tsum`,
  `MeasureTheory.integral_tsum_of_summable_integral_norm`, and
  `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm` all exist
  in `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`).
* The summability hypothesis `Summable (fun k => |coeffPlusGap a b k| ·
  c^(2k+2)/(k+1))` is taken as a **lemma cell** (universally quantified
  on the sprint 042 conclusion), so the Generator does not need to
  derive it from the workspace's existing summability lemmas (sprints
  011, 012, 032). Discharging the cell at the seed is queued as a
  separate sprint that connects the new summability shape to the
  existing N1/N2 series-summability infrastructure.
* Each `F k r := 2 · coeffPlusGap a b k · r^(2k+1)` is a polynomial,
  hence trivially `Continuous` and `IntervalIntegrable` on any compact
  interval. The `Polynomial.intervalIntegrable` /
  `Continuous.intervalIntegrable` Mathlib lemmas dispatch this
  immediately.
* `@integral_pow 0 c (2k+1)` was already used in sprint 026 for the
  analogous (simpler) calculation `∫₀^c 2r dr = c²`. The pattern is
  verbatim.
* Estimated body length: **~150–200 lines**. The bulk is the
  bookkeeping for the `Summable (fun k => ∫ ‖F k‖)` hypothesis discharge
  (matching the abstract Mathlib signature against the lemma's concrete
  hypothesis). The `integral_tsum_of_summable_integral_norm` invocation
  itself is a single line.

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* The Mathlib lemma exists at a known location
  (`MeasureTheory/Integral/DominatedConvergence.lean:156`).
* The hypothesis shape (`Summable (fun i => ∫ a, ‖F i a‖ ∂μ)`) is
  standard and the closed-form formula
  `∫₀^c |F k r| dr = |coeffPlusGap a b k| · c^(2k+2)/(k+1)` is
  elementary calculus.
* The conversion from `intervalIntegral` to
  `integral_tsum_of_summable_integral_norm`'s
  `∫ a, F i a ∂μ` form is one step:
  `intervalIntegral.intervalIntegral_eq_integral_uIoc` plus
  `Set.uIoc_of_le hc_nonneg` (matches `0 ≤ c`).
* Fallback: if `integral_tsum_of_summable_integral_norm` proves
  difficult to instantiate due to measurability dispatch, switch to
  `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`, which
  works on `C(ℝ, ℝ)` continuous-function packaging (each `F k` is
  trivially continuous) and uses sup-norm on the compact interval
  `uIcc 0 c = [0, c]` — the sup of `|F k r|` on `[0, c]` is `|F k c| =
  2|coeffPlusGap a b k|·c^(2k+1)`, which gives a slightly different
  (but algebraically equivalent) summability hypothesis. Either
  Mathlib lemma is acceptable.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem `diskExcess_eq_tsum_via_termwise_integration`
  after sprint 041's `annulusSlice_eq_via_series_partition`
  (current end of `Reduction.lean`, after line 6444).
  Estimated body length: ~150–200 lines.

  The proof body structure (high-level):

  1. **Unfold `diskExcess` to its `intervalIntegral` form.**
     ```lean
     have h_diskExcess_unfold :
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
           ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := rfl
     ```
     (Adjust `rfl` to the actual unfolding strategy used in sprint 041's
     `hAnnulusSliceUnfold` step — possibly `unfold PaperAxioms.diskExcess`
     or a `simp only [PaperAxioms.diskExcess]`. Sprint 003 / 013 /
     026 / 040 / 041 have the verbatim unfolding pattern.)

  2. **Termwise integrand identity.**
     ```lean
     have h_integrand_eq :
         ∀ r ∈ Set.uIcc (0:ℝ) c,
           2 * r * PaperAxioms.circleGap a b r =
             ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) := by
       intro r hr
       rw [show PaperAxioms.circleGap a b r = PaperAxioms.circleGapSeries a b r
            from rfl]
       rw [show PaperAxioms.circleGapSeries a b r =
             ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k) from rfl]
       rw [show (2 : ℝ) * r *
             (∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)) =
             ∑' k : ℕ, 2 * r *
               (PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))
           from (tsum_mul_left).symm]
       refine tsum_congr (fun k => ?_)
       ring
     ```
     Note: the `tsum_mul_left` direction may need to be swapped; check
     Mathlib for the exact name (`tsum_const_mul` is also available,
     and `tsum_mul_const` for the right-multiplication variant). The
     pattern is well-tested in sprints 027 (`tsum_neg`) and 028
     (`tsum_le_tsum`).

  3. **Lift the integrand identity to an integral equality.**
     ```lean
     have h_integral_eq :
         ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r =
           ∫ r in (0:ℝ)..c,
             ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) :=
       intervalIntegral.integral_congr h_integrand_eq
     ```

  4. **Apply Mathlib's swap-of-sum-and-integral lemma.**

     Option A (recommended; uses `MeasureTheory.integral_tsum_of_summable_integral_norm`):
     ```lean
     -- Convert intervalIntegral on `0..c` to general integral on
     -- `volume.restrict (Set.uIoc 0 c)`. Since `0 ≤ c`,
     -- `Set.uIoc 0 c = Set.Ioc 0 c` and the orientation sign is `+1`.
     have h_intervalIntegral_eq_general :
         ∀ k : ℕ,
           ∫ r in (0:ℝ)..c, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) =
             ∫ r, (Set.Ioc 0 c).indicator
                    (fun r => 2 * PaperAxioms.coeffPlusGap a b k *
                              r ^ (2 * k + 1)) r := by
       intro k
       rw [intervalIntegral.integral_of_le hc_nonneg, integral_indicator measurableSet_Ioc]
     -- (Adjust to taste; the goal is just to reach a form where
     -- `MeasureTheory.integral_tsum_of_summable_integral_norm` applies.)

     have h_integral_tsum :
         ∫ r in (0:ℝ)..c,
             ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) =
           ∑' k : ℕ,
             ∫ r in (0:ℝ)..c, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) := by
       -- Apply MeasureTheory.integral_tsum_of_summable_integral_norm
       -- composed with intervalIntegral.integral_of_le.
       sorry  -- Generator: discharge using the Mathlib lemma.
     ```

     Option B (alternative; uses `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`):
     ```lean
     -- Package each F k as a `C(ℝ, ℝ)` continuous map.
     let F : ℕ → C(ℝ, ℝ) := fun k => ⟨fun r =>
       2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1),
       (continuous_const.mul (continuous_const.mul (continuous_pow _)))⟩
     -- The sup-norm of F k on [0, c] is 2|coeffPlusGap a b k|·c^(2k+1).
     have h_sup_norm_eq :
         ∀ k : ℕ,
           ‖(F k).restrict (⟨Set.uIcc 0 c, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ =
             2 * |PaperAxioms.coeffPlusGap a b k| * c ^ (2 * k + 1) := by
       sorry  -- Generator: discharge using ContinuousMap.norm_eq_iSup_norm and
              -- sup of |2·coeffPlusGap·r^(2k+1)| on [0, c].
     -- Translate hSummable_int_norm to summability of the sup-norms.
     have h_sup_norm_summable :
         Summable (fun k : ℕ =>
           ‖(F k).restrict (⟨Set.uIcc 0 c, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
       sorry  -- Generator: rewrite via h_sup_norm_eq, then transfer from
              -- hSummable_int_norm via summability multiplication.
     have h_integral_tsum :
         ∑' k : ℕ, ∫ r in (0:ℝ)..c, F k r =
           ∫ r in (0:ℝ)..c, ∑' k : ℕ, F k r :=
       intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm h_sup_norm_summable
     ```

     The Generator should pick whichever option results in less
     bookkeeping. Option A is recommended because the workspace's
     `coeffPlusGap`-summability shape directly matches the
     `∫ ‖F k‖` shape (one less conversion step). Option B has the
     advantage that each `F k` is trivially continuous (no
     measurability dispatch).

  5. **Compute each termwise integral in closed form.**
     ```lean
     have h_termwise_integral :
         ∀ k : ℕ,
           ∫ r in (0:ℝ)..c, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) =
             PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) := by
       intro k
       rw [intervalIntegral.integral_const_mul]
       rw [show (2 * k + 1 + 1 : ℕ) = 2 * k + 2 by ring,
           show ((2 * k + 1 : ℕ) + 1 : ℝ) = 2 * (k + 1) by
             push_cast; ring]
       -- ∫₀^c r^(2k+1) dr = c^(2k+2) / (2k+2)
       have h_pow := @integral_pow 0 c (2 * k + 1)
       rw [show (0:ℝ)^(2*k+1+1) = 0 from by positivity, sub_zero] at h_pow
       -- (Or: `convert h_pow using 2 <;> norm_num`, sprint 003's verbatim
       -- pattern from Experience.md sprint_003 entry.)
       rw [h_pow]
       field_simp
       ring
     ```
     (Sprint 003 documents the exact `convert h_pow using 2 <;> norm_num`
     pattern needed to handle Mathlib's `n+1` exponent normalisation —
     see Experience.md sprint_003 entry for the full discussion.)

  6. **Chain everything.**
     ```lean
     calc PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
         = ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r :=
           h_diskExcess_unfold
       _ = ∫ r in (0:ℝ)..c,
             ∑' k : ℕ, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) :=
           h_integral_eq
       _ = ∑' k : ℕ,
             ∫ r in (0:ℝ)..c, 2 * PaperAxioms.coeffPlusGap a b k * r ^ (2 * k + 1) :=
           h_integral_tsum
       _ = ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1) :=
           tsum_congr h_termwise_integral
     ```

- `ProofRefinement/Korenblum/Candidates/V42.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V41),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V41),
  4. Adds two side lemmas exercising the new generic identity:
     - `v42_diskExcess_eq_tsum_compiles` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell; applies the new theorem at the seed
       `c = c_value`; conclusion is the equality
       `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value =
        ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k * c_value^(2*k+2)/(k+1)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v42_diskExcess_eq_tsum_recovers_via_eq4_at_seed` —
       takes universally-quantified `(a, b, K, paper)` (with `paper
       : Section2Assumptions a b K c_value`) and the
       `hSummable_int_norm` cell; applies the new identity at the
       seed; **demonstrates** that the resulting equality can be
       chained with `paper.eq4_sigmaPlus_bound`'s third conjunct
       (`Σ⁻(c) = c² · sigmaZeroMinus a b c`) and a termwise
       comparison `coeffPlusGap a b k = ‖a k‖² − ‖b k‖² ≤ ‖a k‖² ≤
       ‖a k‖² + ‖b k‖²` (for example) to recover a bound matching
       sprint 026's shape `c⁴ · sigmaZeroMinus a b c_value`. The
       precise form of the recovery chain may need adjustment by
       the Generator; the structural point is that the new termwise
       identity **is at least as informative** as sprint 026's
       function-level bound.
       Acceptable simplification: if the full recovery chain is
       analytically delicate to discharge in the side lemma, the
       Generator may substitute a trivially-true compilation check
       (e.g., a tautological `have : True := trivial` after
       invoking the new identity) — the structural point of the
       side lemma is that the new identity composes with `paper`,
       not that it reproduces sprint 026's bound exactly.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V41) — the new identity is
     materialised in side lemmas, **not** as the sink theorem's
     discharge route, since exercising the new termwise series in a
     closing-reducer chain is queueable as a separate sprint.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V42` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V42.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V42 ties V41 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V42.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `diskExcess_eq_tsum_via_termwise_integration`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V42.lean`'s two side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken —
   sprint 042's signature is `(a, b, c)`-only with no `K` and no
   `paper`.)
7. The proof body invokes Mathlib's `integral_tsum`-style lemma
   (either `MeasureTheory.integral_tsum_of_summable_integral_norm`,
   `MeasureTheory.integral_tsum`, or
   `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`)
   at least once. Greppable check: the body contains **at least one**
   of: `integral_tsum`, `tsum_intervalIntegral_eq_of_summable_norm`,
   `hasSum_intervalIntegral_of_summable_norm`,
   `hasSum_integral_of_summable_integral_norm`,
   `integral_tsum_of_summable_integral_norm`.
8. The proof body invokes `@integral_pow 0 c _` (or
   `intervalIntegral.integral_pow`, the namespaced form) at least
   once for the closed-form `∫₀^c r^n dr = c^(n+1)/(n+1)` evaluation.
   Greppable check: count of `integral_pow` in the new theorem body
   is **≥ 1**.
9. The proof body invokes `tsum_congr` at least once for the
   termwise-equality lifting step. Greppable check: count of
   `tsum_congr` in the new theorem body is **≥ 1**.
10. The new theorem's conclusion is an **equality** (not an
    inequality): the conclusion contains `=` between
    `PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c` and the
    `∑' k, ...` RHS.
11. The new theorem **does not invoke** sprint 040's lemma
    `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`,
    sprint 026's lemma
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only`, or any of
    sprints 003 / 013 / 030 / 031 / 034's `diskExcess_upper_bound_*`
    lemmas. Sprint 042 is a parallel chain at a strictly different
    layer (`tsum`-of-integrals vs function-level integrated), not a
    refinement of any prior bound. Greppable check: in the new
    theorem body, counts of `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`,
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only`,
    `diskExcess_upper_bound_of_eq2_eq3_eq4`,
    `diskExcess_upper_bound_via_eq3_eq4`,
    `diskExcess_upper_bound_via_series_eq4_only_two_Z`,
    `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`,
    and `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    are all **0**.
12. The new theorem **does not invoke** `paperLambda` anywhere in
    its proof body or signature. Greppable check: count of
    `paperLambda` in the new theorem (signature + body) is **0**.
13. The new theorem **does not invoke** `paper.eq3_circleGap_decomposition`
    or sprint 027's `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`.
    The decomposition `circleGap = circleGapSeries = ∑' k,
    coeffPlusGap · r^(2k)` is purely *definitional* (`rfl`) and does
    not require sprint 027's identity (which is a *partition* identity
    on N1/N2, a different decomposition than the unconditioned `∑' k`
    used here). Greppable check: in the new theorem body, counts of
    `eq3_circleGap_decomposition` and
    `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
    are both **0**.
14. The V42 `_compiles` side lemma's conclusion is the new
    `tsum`-equality at `c = c_value`, with the
    `hSummable_int_norm` cell as a universally-quantified
    hypothesis on the side lemma.
15. The V42 `_recovers_via_eq4_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance and applies the
    new identity. The body may stop at signature-compilation
    check (i.e., a `True`-returning tautology after invoking the
    new identity), or attempt the full recovery to sprint 026's
    `c⁴·Z_c` shape; either is acceptable.

## Out of scope

- Edit older candidates V0–V41.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V42 is
  the same `hEq15_seed_3554` that V0–V41 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the `hSummable_int_norm` hypothesis cell from the
  workspace's existing N1/N2 series-summability lemmas (sprints
  011, 012, 032). This is queueable as a separate sprint that
  connects the new `Summable (fun k => |coeffPlusGap a b k| ·
  c^(2k+2)/(k+1))` shape to the existing N1/N2 summability shapes.
  Sprint 042 takes the cell as universally quantified.
- Ship a closing reducer fusing sprint 042 with sprint 041's
  annulus-side identity to produce a paper-axiom-free, oracle-free
  `valid_of_*` reducer. That is the **next** sprint's scope; sprint
  042 ships only the disk-side `tsum`-equality. Reason: the
  termwise comparison of disk-side and annulus-side series, plus
  the convergence/integrability bookkeeping for the annulus-side
  termwise expansion, is a separate analytical sprint that can
  use sprint 042 as a building block.
- Ship a witness at any `c > 0.3554`. Sprint 042 does not raise
  `c_value`. The eventual numerical push is a *consumer* of sprint
  042 + a future closing reducer + the kernel inequality
  evaluation, not sprint 042 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15` to
  any new chain. The new identity is materialised in side lemmas
  only.
- Ship the analogous `tsum`-of-integrals identity for
  `annulusSlice (circleGap a b) α β` over an arbitrary `[α, β]`.
  This is a natural follow-up sprint but is out of scope here —
  the disk-side `[0, c]` window already exercises the
  `integral_tsum`-style machinery, and the annulus-side window
  raises additional convergence questions (the series may not
  converge uniformly on `[c, β]` near `β = 1`).
- Re-derive sprints 003 / 013 / 026 / 030 / 031 / 034 / 040 as
  corollaries of the new termwise identity. Although each prior
  bound recovers from sprint 042 plus a termwise comparison, the
  precise algebraic chain is non-trivial and is queueable as a
  separate cleanup sprint.

## Time budget

≤ 90 minutes runtime. (Sprint 042's body is moderately complex —
slightly longer than sprint 041's but with no new analytical content
beyond the swap of `tsum` and `∫`. Estimated body: ~150–200 lines,
dominated by the bookkeeping for the swap-of-sum-and-integral
hypothesis discharge. The Mathlib lemma is well-documented; the main
risk is matching the exact hypothesis shape (Option A vs Option B
above) and is mitigated by the fallback strategy. The two V42 side
lemmas reuse the universally-quantified hypothesis pattern from V40
/ V41, ~30–60 lines each. Total V42 size: ≤ 250 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* The Mathlib lemma `MeasureTheory.integral_tsum_of_summable_integral_norm`
  lives at `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:156`:
  ```
  lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
      (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
      ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ
  ```
  The `Integrable (F i) μ` hypothesis for each polynomial term on the
  measure `volume.restrict (Set.uIoc 0 c)` is dischargeable via
  `Continuous.integrableOn_uIoc` or
  `(IntervalIntegrable.continuousOn ...).integrableOn_compact`.
  The summability hypothesis is exactly `hSummable_int_norm` (modulo
  a pointwise rewrite of `∫ a, ‖F k a‖ ∂μ = |coeffPlusGap a b k| ·
  c^(2k+2) / (k+1)`).

* The conversion from the intervalIntegral form to the general
  `∫ a, F a ∂μ` form on `volume.restrict (Set.uIoc 0 c)` uses
  `intervalIntegral.integral_of_le hc_nonneg` (which gives
  `∫ a in 0..c, f a = ∫ a in Set.Ioc 0 c, f a`, with no orientation
  sign since `0 ≤ c`).

* For each polynomial term `r ↦ 2 · coeffPlusGap a b k · r^(2k+1)`,
  the closed-form integral
  `∫₀^c 2 · coeffPlusGap a b k · r^(2k+1) dr =
   coeffPlusGap a b k · c^(2k+2) / (k+1)`
  follows from `@integral_pow 0 c (2k+1)`:
  `∫₀^c r^(2k+1) dr = c^(2k+2) / (2k+2)`,
  scaled by `2 · coeffPlusGap a b k` and simplified via `field_simp; ring`.
  Sprint 003's Experience.md entry documents the exact
  `convert h_pow using 2 <;> norm_num` pattern needed to handle
  Mathlib's `(n + 1)` exponent normalisation.

* The `hSummable_int_norm` cell is intentionally stated in the
  closed-form `|coeffPlusGap a b k| · c^(2k+2) / (k+1)` shape — the
  exact shape that emerges from each termwise `∫₀^c |F k r| dr`
  computation. This avoids any algebraic conversion in the proof
  body; the Generator should invoke the cell directly after
  computing each termwise `∫ ‖F k‖`.

* If the Generator finds the absolute-value bookkeeping
  (`|coeffPlusGap a b k|`) friction-heavy, an acceptable variation
  is to state the summability cell as
  `Summable (fun k : ℕ => (‖a k‖^2 + ‖b k‖^2) * c^(2*k+2) / (k+1))`
  (which dominates `|coeffPlusGap a b k|` since
  `|coeffPlusGap a b k| = |‖a k‖² − ‖b k‖²| ≤ ‖a k‖² + ‖b k‖²`)
  and invoke `Summable.of_nonneg_of_le` to transfer summability.
  Either form is acceptable.

* The new identity is **paper-axiom-free** (no `Section2Assumptions`
  in the signature) and **`paperLambda`-free** (no oracle cell).
  The only paper-side objects in the conclusion are
  `PaperAxioms.diskExcess`, `PaperAxioms.circleGap`, and
  `PaperAxioms.coeffPlusGap` — all definitional unfoldings, not
  axiom field projections.

* The V42 `_compiles` side lemma should take the
  `hSummable_int_norm` cell as a universally-quantified hypothesis
  (mirroring sprint 040's and 041's `_compiles` side lemma patterns).
  The side lemma's conclusion is the new `tsum`-equality at
  `c = c_value`.

* The V42 `_recovers_via_eq4_at_seed` side lemma is
  **structurally optional**: if discharging the recovery chain
  (`paper.eq4_sigmaPlus_bound` + termwise comparison →
  sprint 026's `c⁴·Z_c` bound) proves friction-heavy in the side
  lemma, the Generator may substitute a tautological compilation
  check after invoking the new identity. The structural point of
  the side lemma is that the new identity **composes** with a
  `Section2Assumptions a b K c_value` instance, not that it
  reproduces sprint 026's bound algebraically.
