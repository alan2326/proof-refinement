# Sprint 046: First **paper-axiom-free, oracle-cell-free annulus-side `tsum`-of-integrals closed-form *equality*** for `annulusExcess (circleGap a b) c` — direct mirror of sprint 042 over `[c, 1]`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V45.lean`
**Target file**: `Candidates/V46.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem annulusExcess_eq_tsum_via_termwise_integration
    (a b : ℕ → ℂ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hc_le_one : c ≤ 1)
    (hSummable_int_norm :
      Summable (fun k : ℕ =>
        |PaperAxioms.coeffPlusGap a b k|
          * (1 - c ^ (2 * k + 2)) / (k + 1))) :
    PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
      ∑' k : ℕ,
        PaperAxioms.coeffPlusGap a b k
          * (1 - c ^ (2 * k + 2)) / (k + 1)
```

The proof body is **sprint 042's body verbatim with `[0, c]` replaced by
`[c, 1]`** and the termwise integral closed form
`∫₀^c r^(2k+1) dr = c^(2k+2)/(2k+2)` replaced by
`∫_c^1 r^(2k+1) dr = (1^(2k+2) − c^(2k+2))/(2k+2) = (1 − c^(2k+2))/(2k+2)`.

The high-level steps mirror sprint 042 line-for-line:

1. **Define termwise family** `F k r := 2 * coeffPlusGap a b k * r^(2k+1)`.
2. **Continuity / integrability of each `F k` on `Ioc c 1`** (`continuousOn`
   restricted from the global continuous polynomial).
3. **Termwise L¹-norm closed form** on `[c, 1]`:
   ```
   ∫_c^1 ‖F k r‖ dr = |coeffPlusGap a b k| * (1 − c^(2k+2)) / (k + 1)
   ```
   via the same `Set.uIcc_of_le hc_le_one` + `Real.norm_eq_abs` +
   `abs_of_nonneg` chain sprint 042 uses, applied with `r ≥ c ≥ 0` instead
   of `r ≥ 0`.
4. **Summability of the L¹-norms** via the new `hSummable_int_norm` premise
   (the natural mirror of sprint 042's `hSummable_int_norm` cell, with the
   termwise weight `c^(2k+2)/(k+1)` replaced by
   `(1 − c^(2k+2))/(k+1)`).
5. **Apply `MeasureTheory.integral_tsum_of_summable_integral_norm`** with
   `hF_int` (each `F k` is `Integrable` on `volume.restrict (Ioc c 1)`) and
   `h_int_norm_summable` to swap `∑'` past `∫` over `[c, 1]`.
6. **Pointwise series unfold** `2r * circleGap a b r = ∑' k, F k r`
   (definitional `tsum_mul_left` + `pow_succ` argument identical to sprint
   042's Step 4).
7. **Termwise integral closed form on `[c, 1]`**:
   ```
   ∫_c^1 F k r dr = coeffPlusGap a b k * (1 − c^(2k+2)) / (k + 1)
   ```
   via `intervalIntegral.integral_const_mul` + `@integral_pow c 1 (2*k+1)`.
   Unlike sprint 042, the `0^(2k+1+1) = 0` simplification is replaced by
   `1^(2k+1+1) = 1` (and a `c^(2k+1+1) = c^(2k+2)` exponent normalisation).
8. **Identify `annulusExcess` with the integral** via the definitional
   equality `annulusExcess (circleGap a b) c = annulusSlice (circleGap a b)
   c 1 = ∫ r in c..1, 2 * r * circleGap a b r` (same `rfl` chain sprint 042
   uses for the `diskExcess = annulusSlice 0 c` identification).
9. **Calc-chain** the four equalities:
   ```
   annulusExcess (circleGap a b) c
     = ∫ r in c..1, 2 * r * circleGap a b r            -- (8)
     = ∫ r in c..1, ∑' k, F k r                         -- (6)
     = ∑' k, ∫ r in c..1, F k r                         -- (5).symm
     = ∑' k, coeffPlusGap a b k * (1 − c^(2k+2)) / (k+1) -- (7)
   ```

## Why

The bulletin's current priority is **novel analytical chains** through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 046 ships:

1. **First workspace `annulusExcess` *equality* identity at the
   `tsum`-of-integrals layer.** The current state of the workspace's
   annulus-side `annulusExcess ≥ …` and `annulusExcess = …` matrix:

   | Sprint | Annulus-side conclusion shape | Paper-axiom signature | Oracle cells | Series shape |
   |--------|-----|-----|-----|-----|
   | 005 | `2ρ³·Z_ρ/Λ ≤ 2ρ·circleGap` (pointwise) | `{eq8, eq9}` | none | function-level |
   | 006 | `∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ ≤ annulusExcess` (integrated) | `{eq8, eq9}` | none | function-level |
   | 037 | pointwise outer bound modulo `hLambdaBridge` | `{}` | `{hLambdaBridge}` | function-level |
   | 038 | integrated annulus bound modulo `hLambdaBridgeWindow` | `{}` | `{hLambdaBridgeWindow}` | function-level |
   | 041 | `annulusSlice (circleGap a b) α β = (∫ 2ρ·sigmaPlus) − (∫ 2ρ³·Z)` (equality) | `{}` | none | function-level |
   | **046 (NEW)** | **`annulusExcess (circleGap a b) c = ∑' k, coeffPlusGap_k · (1 − c^(2k+2)) / (k+1)`** (equality) | **`{}`** | **none** | **per-`k` termwise series** |

   Sprint 046 is the **first** annulus-side equality identity at the
   per-`k` termwise series layer. Sprint 041 ships a function-level
   *equality* on `annulusSlice` (decomposed as `∫ Σ⁺ − ∫ ρ²·Z`), and
   sprint 038 ships a function-level *bound* modulo an oracle cell, but
   neither expresses `annulusExcess` as a per-`k` `tsum` with explicit
   per-`k` integration weights.

   Sprint 046's RHS shape `∑' k, coeffPlusGap_k · (1 − c^(2k+2))/(k+1)`
   has per-`k` weight `(1 − c^(2k+2))/(k+1)` — closely paralleling sprint
   044's disk-side per-`k` weight `c^(2k+2)/(k+1)` — and the two together
   admit a structurally novel **per-`k` × per-`k` comparison** between
   disk and annulus contributions of the *same* `coeffPlusGap_k`
   coefficient family. No prior pair of workspace lemmas supports such a
   per-`k` × per-`k` closing inequality.

2. **Direct mirror of sprint 042 on the structurally distinct interval
   `[c, 1]`.** Sprint 042 establishes the `tsum`-of-integrals identity
   for `diskExcess = annulusSlice 0 c`. Sprint 046 establishes the
   structurally analogous identity for `annulusExcess = annulusSlice c
   1`. The two together cover **both halves** of the natural decomposition
   `annulusSlice 0 1 = diskExcess + annulusExcess`, exposing the entire
   `[0, 1)`-integrated `2r · circleGap a b r` as a `tsum` of polynomial
   integrals on each half. This was previously unreachable from any
   workspace lemma.

3. **Foundation for sprint 047 (queueable separately): annulus-side
   N1/N2 partition equality `annulusExcess = Σ⁺_int_ann(c) −
   Σ⁻_int_ann(c)`.** Sprint 046 is the structural prerequisite for
   reproducing sprint 043's N1/N2 partition pattern on the annulus side.
   Once both are in place, sprint 048 (queueable) can drop the
   non-negative `Σ⁺_int_ann ≥ 0` piece (or the non-negative `−Σ⁻_int_ann`
   piece, depending on direction) to produce a *lower bound* on
   `annulusExcess` paralleling sprint 044's disk-side upper bound.

4. **Direct path to a closing reducer with paper-axiom signature `{}`
   and zero oracle cells.** Once sprint 046 is in place, a future
   closing reducer (queueable as sprint 049 or similar) can fuse:
   - sprint 044's disk-side bound `diskExcess ≤ Σ⁺_int(c) := ∑' k, [n1Pred] coeffPlusGap_k · c^(2k+2)/(k+1)`
   - sprint 046's annulus-side equality `annulusExcess = ∑' k, coeffPlusGap_k · (1 − c^(2k+2))/(k+1)`

   into a closing reducer with **paper-axiom signature `{}`** AND **zero
   oracle cells** — strictly improving on sprint 045's `{eq8, eq9}` and
   sprint 039's two oracle cells. The kernel inequality reduces to
   `Σ⁺_int(c) ≤ ∑' k, coeffPlusGap_k · (1 − c^(2k+2))/(k+1)`, which on
   N1 indices is the **per-`k` termwise comparison**
   `c^(2k+2)/(k+1) ≤ (1 − c^(2k+2))/(k+1)` (i.e., `2c^(2k+2) ≤ 1`),
   discharged at the seed `c = 0.3554` by `2 · 0.3554^(2k+2) ≤
   2 · 0.3554^2 = 0.252... ≤ 1` for all `k ≥ 0`. On N2 indices, the LHS
   is `0` (sprint 044 drops N2) and the RHS is `coeffMinusGap_k · (1 −
   c^(2k+2))/(k+1) · (−1)` (the partition's negative branch) — needs
   careful sign handling but is purely algebraic. **This is the
   bulletin's "design a strictly stronger sufficient condition than the
   seed's `(15)`" axis materialised at the closing-reducer trust-base
   layer.**

5. **Paper-axiom-free downstream of sprint 027 + sprint 042's machinery.**
   Sprint 046's body uses:
   - The definitional series unfolding `circleGap a b r =
     circleGapSeries a b r = ∑' k, coeffPlusGap a b k · r^(2k)`
     (definitional `rfl`, paper-axiom-free).
   - `MeasureTheory.integral_tsum_of_summable_integral_norm` (Mathlib,
     paper-axiom-free).
   - `intervalIntegral.integral_const_mul` and `@integral_pow c 1 (2k+1)`
     (Mathlib, paper-axiom-free).
   - Continuity / `IntegrableOn` of polynomials (Mathlib, paper-axiom-free).

   No `paper.eq*` invocation. No `paperLambda`. No `Section2Assumptions`
   parameter. No oracle cell. Signature is `(a, b, c)`-only with
   `0 ≤ c ≤ 1` and a single integral-norm summability hypothesis on the
   per-`k` weight `(1 − c^(2k+2))/(k+1)`.

6. **Structurally distinct from sprint 041's annulus-side equality.**
   Sprint 041 ships `annulusSlice (circleGap a b) α β = ∫ 2ρ·sigmaPlus
   − ∫ 2ρ³·Z` — a *function-level* decomposition into two pure-series
   integrals (one of `sigmaPlus`, one of `sigmaZeroMinus`), each still
   evaluated as a single `∫`. Sprint 046 ships
   `annulusExcess (circleGap a b) c = ∑' k, coeffPlusGap_k · (1 −
   c^(2k+2))/(k+1)` — a *per-`k` termwise expansion* with each `k`-th
   coefficient computed via a closed-form polynomial integral.
   * Sprint 041's RHS still contains two integrals; sprint 046's RHS
     contains zero integrals (the integration is fully discharged
     termwise, leaving only a `tsum` over `k`).
   * Sprint 041's RHS aggregates over `k` inside the `sigmaPlus` and
     `sigmaZeroMinus` definitions; sprint 046 exposes each `k`-th
     coefficient explicitly.
   * Sprint 041 is the **annulus-side mirror of sprint 027 → sprint 040's
     intermediate** (function-level integrated equality); sprint 046 is
     the **annulus-side mirror of sprint 042's** (per-`k` `tsum`-of-
     integrals identity, the strictly stronger statement).

7. **Mirror-of-sprint-042 transitivity strategy.** Sprint 042's body is
   the canonical reference for sprint 046's body. The only changes
   required are:
   * Replace `Set.Ioc 0 c` with `Set.Ioc c 1` (or `Set.Icc c 1`
     depending on the integrability lemma used).
   * Replace `intervalIntegral.integral_of_le hc_nonneg` with
     `intervalIntegral.integral_of_le hc_le_one` (when converting
     `intervalIntegral` to `MeasureTheory.integral` over the restricted
     measure on `[c, 1]`).
   * Replace `@integral_pow 0 c (2*k+1)` with `@integral_pow c 1
     (2*k+1)` (no `0^(2k+1+1) = 0` cancellation; instead get
     `1^(2k+1+1) = 1` which is **kept** in the formula as `(1 −
     c^(2k+2))/(2k+2)`).
   * Replace `Set.uIcc_of_le hc_nonneg` with `Set.uIcc_of_le hc_le_one`
     for the absolute-value chain.
   * Replace the `diskExcess = annulusSlice 0 c` `rfl` step (sprint
     042's Step 7 `change AnnulusIntegralReduction.annulusSlice
     (PaperAxioms.circleGap a b) 0 c = _` then `rfl`) with the
     analogous `annulusExcess = annulusSlice c 1` `rfl` step. Per
     `KorenblumPaper.PaperAxioms` lines 272–273:
     ```
     def annulusExcess (circleGap : ℝ → ℝ) (c : ℝ) : ℝ :=
       AnnulusIntegralReduction.annulusSlice circleGap c 1
     ```
     so the change tactic is
     `change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) c 1 = _`
     followed by `rfl`.

   Estimated body length: **~150–200 lines** (sprint 042's body is ~210
   lines including the L¹-norm closed-form derivation; sprint 046's
   body is sprint 042's body with the integration limits replaced and
   the `(2k+2)` denominator unchanged. The only non-trivial new
   algebraic work is normalising `(1^(2k+2) − c^(2k+2))/(2k+2)` to
   `(1 − c^(2k+2))/(2k+2)` — a one-line `norm_num`/`ring` step).

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V46 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is a new lemma layer (paper-axiom-free, oracle-free,
  per-`k` `tsum`-of-integrals identity on `[c, 1]`), not a numerical
  refinement of an existing closed-form coefficient.
* The new identity introduces a fundamentally novel analytical object —
  the per-`k` annulus-integrated weight `(1 − c^(2k+2))/(k+1)` —
  with no analog in any prior workspace lemma.

Why this is **not** "the same chain" as sprint 042:

* **Integration interval.** Sprint 042 integrates over `[0, c]` (the
  disk side); sprint 046 integrates over `[c, 1]` (the annulus side).
  The two integrals are over **disjoint** sub-intervals of `[0, 1]`,
  with **disjoint** integrand-evaluation closed forms (sprint 042's
  termwise integral is `c^(2k+2)/(2k+2)`; sprint 046's is `(1 −
  c^(2k+2))/(2k+2)`).
* **Different conclusion target.** Sprint 042's conclusion is on
  `diskExcess`; sprint 046's is on `annulusExcess`. The two are
  **distinct paper-defined objects** (`PaperAxioms.diskExcess` vs
  `PaperAxioms.annulusExcess`) with disjoint downstream consumers.
* **Different summability premise shape.** Sprint 042's premise is
  `Summable (fun k => |coeffPlusGap_k| · c^(2k+2)/(k+1))`; sprint 046's
  is `Summable (fun k => |coeffPlusGap_k| · (1 − c^(2k+2))/(k+1))`.
  Note: the latter is **strictly weaker** for `c < 1` because
  `(1 − c^(2k+2)) ≤ 1` is bounded above whereas `c^(2k+2)` decays
  geometrically — so `(1 − c^(2k+2))/(k+1)` decays only like `1/(k+1)`
  while `c^(2k+2)/(k+1)` decays geometrically. This means sprint 046's
  summability cell is **harder to discharge** than sprint 042's; this
  is acknowledged in the contract as part of the structural cost of
  exposing the annulus-side termwise expansion.

Why this is **not** "the same chain" as sprint 041:

* **Termwise vs function-level.** Sprint 041's RHS contains two
  function-level integrals (`∫ 2ρ·sigmaPlus`, `∫ 2ρ³·Z`); sprint 046's
  RHS contains a single `tsum` over `k` with each `k`-th term being a
  **closed-form polynomial weight** times `coeffPlusGap_k`. Sprint
  041's representation requires `sigmaPlus` and `sigmaZeroMinus`
  integrability cells (three cells); sprint 046's representation
  requires only the integral-norm summability cell (one cell).
* **Disjoint Mathlib machinery.** Sprint 041's body uses
  `intervalIntegral.integral_congr` + `intervalIntegral.integral_sub`.
  Sprint 046's body uses `MeasureTheory.integral_tsum_of_summable_integral_norm`
  + termwise polynomial integration + `tsum_mul_left`. Zero shared
  Mathlib lemmas in the body skeleton.
* **Different direction of decomposition.** Sprint 041 *splits*
  `annulusSlice circleGap` into a difference of two integrals of
  paper-defined series objects. Sprint 046 *expands* `annulusSlice
  circleGap` into a `tsum` over the *unconditioned* `coeffPlusGap_k`
  family — no separation into `sigmaPlus` vs `sigmaMinus` is done at
  this layer (that separation is what sprint 047 will do as the N1/N2
  partition of sprint 046's identity).

Why this is **not** "the same chain" as sprint 038:

* **Equality vs lower bound.** Sprint 038 ships an *inequality*
  `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
  modulo an oracle cell. Sprint 046 ships an *equality* with no oracle
  cell. The equality shape is strictly more informative.
* **No `paperLambda`.** Sprint 038's RHS contains
  `paperLambda K c ρ` inside an integrand; sprint 046's RHS contains
  zero `paperLambda` invocations (the `Λ` factor is absent because
  sprint 046 expands `annulusExcess` directly via `circleGap`'s series
  representation, bypassing the `circleGap → Z/Λ` bridge step
  entirely).
* **No `Section2Assumptions` parameter.** Sprint 038's signature
  carries a `paper : Section2Assumptions a b K c` parameter (even
  though the body doesn't invoke `paper.eq*`); sprint 046 takes only
  `(a, b, c)` with no `K` and no `paper`.

Why this is **bounded enough for one Generator session**:

* The proof body is the **mechanical mirror of sprint 042's body**.
  Sprint 042 is ~210 lines and the mirror should be ~150–200 lines
  (slightly shorter because the `0^(2k+2) = 0` cancellation step is
  replaced by a `1^(2k+2) = 1` step that needs no `zero_pow` invocation).
* All Mathlib lemmas used by sprint 042's body
  (`MeasureTheory.integral_tsum_of_summable_integral_norm`,
  `intervalIntegral.integral_of_le`, `intervalIntegral.integral_const_mul`,
  `@integral_pow`, `tsum_mul_left`, `tsum_congr`,
  `Real.norm_eq_abs`, `abs_of_nonneg`, `abs_pow`, `pow_succ`,
  `field_simp`, `push_cast`, `ring`, `norm_num`, `funext`) are reused
  verbatim with only the integration-bounds substitution.
* No new Mathlib lemmas are needed.
* No new structural moves are required — the entire body is sprint 042's
  body with `0` replaced by `c` and `c` replaced by `1` in the
  integration bounds (and the corresponding closed-form simplifications).

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* Zero new Mathlib lemmas. Every ingredient is already exercised in
  sprint 042's body.
* The integral closed form on `[c, 1]` is `∫_c^1 r^(2k+1) dr =
  (1^(2k+2) − c^(2k+2))/(2k+2)` — a routine application of
  `@integral_pow c 1 (2k+1)`. No archaeology beyond verifying the
  argument order matches sprint 042's `@integral_pow 0 c (2k+1)`.
* The premise `0 ≤ c ≤ 1` is satisfied at the seed `c_value =
  3554/10000` and is the natural domain of validity for the
  `circleGap a b r` series at `r = 1` (which is the boundary of
  convergence for the `‖a k‖²r^(2k)` and `‖b k‖²r^(2k)` series
  appearing in `coeffPlusGap a b k = ‖a k‖² − ‖b k‖²`).

Why this is **bounded enough on candidate-side instantiation**:

* The V46 `_compiles` side lemma takes the new
  `hSummable_int_norm` cell as a universally-quantified hypothesis
  (mirroring V42's pattern) and applies the new theorem at `c =
  c_value`. ~15 lines.
* The V46 `_recovers_via_sprint041_at_seed` side lemma (optional,
  per the contract) demonstrates that sprint 046's per-`k` expansion
  is consistent with sprint 041's function-level expansion at the
  seed (i.e., the two right-hand sides are equal under the
  `sigmaPlus = ∑' k, [n1Pred] coeffPlusGap_k · ρ^(2k)` and
  `sigmaMinus = ρ² · sigmaZeroMinus = ρ² · ∑' k, [n2Pred] coeffMinusGap_k · ρ^(2k)`
  representations). Acceptable simplification: this side lemma may
  stop at a tautological compilation check after invoking sprint 046
  alone if the full consistency check is friction-heavy.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem `annulusExcess_eq_tsum_via_termwise_integration`
  after sprint 045's
  `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
  (current end of `Reduction.lean`, after line 6992).

  Estimated body length: ~150–200 lines.

  The proof body is sprint 042's body verbatim with the following
  substitutions (the line numbers below refer to sprint 042's body in
  `Reduction.lean` starting at line 6473):

  | Sprint 042 step | Sprint 046 substitution |
  |-----------------|-------------------------|
  | `set F : ℕ → ℝ → ℝ := fun k r => 2 * coeffPlusGap a b k * r^(2k+1)` | unchanged |
  | `Continuous (F k)` via `fun_prop` | unchanged |
  | `IntegrableOn (F k) (Ioc 0 c)` | `IntegrableOn (F k) (Ioc c 1)` (use `hc_le_one` instead of `hc_nonneg`) |
  | `‖F k r‖ on Set.uIcc 0 c` chain | `‖F k r‖ on Set.uIcc c 1` chain (replace `hc_nonneg` with `hc_le_one`; replace `0 ≤ r` with `c ≤ r` then derive `0 ≤ r` from `0 ≤ c ≤ r` for `abs_of_nonneg`) |
  | `∫_0^c r^(2k+1) dr = c^(2k+2)/(2k+2)` via `@integral_pow 0 c (2k+1)` and `0^(2k+1+1) = 0` cancellation | `∫_c^1 r^(2k+1) dr = (1^(2k+2) − c^(2k+2))/(2k+2)` via `@integral_pow c 1 (2k+1)`; `1^(2k+1+1) = 1` (use `one_pow` instead of `zero_pow`) |
  | Final algebraic normalisation `(2 \cdot ?) / (2(k+1)) = ?/(k+1)` | unchanged (the `2` on top and the `2` in `2(k+1) = 2k+2` cancel identically) |
  | `change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) 0 c = _` | `change AnnulusIntegralReduction.annulusSlice (PaperAxioms.circleGap a b) c 1 = _` |
  | `intervalIntegral.integral_of_le hc_nonneg` | `intervalIntegral.integral_of_le hc_le_one` |

  The L¹-norm closed form on `[c, 1]` evaluates to
  `|coeffPlusGap a b k| * (1^(2k+2) − c^(2k+2)) / (k+1)` which after
  normalisation is `|coeffPlusGap a b k| * (1 − c^(2k+2)) / (k+1)`.

- `ProofRefinement/Korenblum/Candidates/V46.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V45),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V45),
  4. Adds two side lemmas exercising the new generic equality:
     - `v46_annulusExcess_eq_tsum_via_termwise_integration_compiles` —
       takes universally-quantified `(a, b)` and the
       `hSummable_int_norm` cell on `(1 − c_value^(2k+2))/(k+1)`;
       applies the new theorem at the seed `c = c_value`; conclusion
       is the new equality
       `annulusExcess (circleGap a b) c_value = ∑' k, coeffPlusGap_k · (1 − c_value^(2k+2))/(k+1)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v46_annulusExcess_eq_tsum_via_termwise_integration_recovers_sprint041_at_seed` —
       takes universally-quantified `(a, b)` and the new
       `hSummable_int_norm` cell; invokes sprint 046 at the seed; demonstrates
       a tautological compilation check (or, optionally, a full
       consistency check against sprint 041's function-level identity at
       the seed via the definitional series unfoldings of `sigmaPlus`
       and `sigmaMinus`).
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V45) — the new equality is
     materialised in side lemmas, **not** as the sink theorem's
     discharge route.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V46` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V46.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V46 ties V45 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V46.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `annulusExcess_eq_tsum_via_termwise_integration`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V46.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken — sprint
   046's signature is `(a, b, c)`-only with no `K` and no `paper`.)
7. The proof body invokes
   `MeasureTheory.integral_tsum_of_summable_integral_norm` at least
   once. Greppable check: count of
   `integral_tsum_of_summable_integral_norm` in the body of the new
   theorem is **≥ 1**.
8. The proof body invokes `@integral_pow c 1` (or
   `@integral_pow (?c) (?1)` form) at least once for the termwise
   polynomial integral. Greppable check: count of `integral_pow` in
   the body of the new theorem is **≥ 2** (one for the L¹-norm closed
   form, one for the termwise integral closed form — same as sprint
   042's body which also has two `integral_pow` invocations).
9. The new theorem's conclusion is an **equality** (not an
   inequality): the conclusion contains `=` between
   `PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c` and the
   `∑' k, coeffPlusGap a b k * (1 - c^(2k+2)) / (k+1)` RHS.
   Greppable check: in the new theorem's signature line, the
   substring `=` appears in the conclusion.
10. The new theorem's RHS contains the substring `1 - c ^ (2 * k + 2)`
    (or definitionally equivalent) — this is the structurally novel
    per-`k` annulus-integrated weight. Greppable check: in the new
    theorem's signature line, the substring `1 - c` (or `(1 - c`)
    appears at least once.
11. The new theorem **does not invoke** sprint 042's
    `diskExcess_eq_tsum_via_termwise_integration` directly — sprint
    046 is a structurally analogous derivation, **not** a downstream
    consumer of sprint 042. Greppable check: count of
    `diskExcess_eq_tsum_via_termwise_integration` in the body of the
    new theorem is **0**.
12. The new theorem **does not invoke** sprint 041's
    `annulusSlice_eq_via_series_partition` — sprint 046 is at a
    different layer (per-`k` `tsum`-of-integrals vs function-level
    decomposition) and is independently derived from
    `circleGap`'s definitional series representation. Greppable check:
    count of `annulusSlice_eq_via_series_partition` in the body of
    the new theorem is **0**.
13. The new theorem **does not invoke** `paperLambda` anywhere in its
    proof body or signature. Greppable check: count of `paperLambda`
    in the new theorem (signature + body) is **0**.
14. The new theorem **does not invoke** any `Section2Assumptions`
    field — its signature does not contain `Section2Assumptions`.
    Greppable check: count of `Section2Assumptions` in the new
    theorem (signature + body) is **0**.
15. The new theorem **does not invoke** `sigmaPlus`, `sigmaMinus`,
    `sigmaZeroMinus`, `n1Pred`, or `n2Pred` — sprint 046 expands
    `circleGap` directly via `coeffPlusGap`, with no separation into
    N1/N2. (The N1/N2 partition of sprint 046's identity is the
    queueable sprint 047's scope.) Greppable check: in the body of
    the new theorem, counts of `sigmaPlus`, `sigmaMinus`,
    `sigmaZeroMinus`, `n1Pred`, `n2Pred` are all **0**.
16. The V46 `_compiles` side lemma's conclusion is the new equality
    at `c = c_value`, with the `hSummable_int_norm` cell as a
    universally-quantified hypothesis on the side lemma.
17. The V46 `_recovers_sprint041_at_seed` side lemma takes the same
    universally-quantified `(a, b)` and the new `hSummable_int_norm`
    cell; invokes sprint 046 at the seed; demonstrates a tautological
    compilation check (or a full consistency check — either is
    acceptable per the contract).

## Out of scope

- Edit older candidates V0–V45.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V46 is
  the same `hEq15_seed_3554` that V0–V45 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the `hSummable_int_norm` hypothesis cell from the
  workspace's existing N1/N2 series-summability lemmas (sprints
  011, 012, 032). The new weight `(1 − c^(2k+2))/(k+1)` decays only
  like `1/(k+1)`, so the summability discharge requires either (a)
  a stronger summability hypothesis on the underlying `coeffPlusGap_k`
  series than sprints 011/012/032 provide, OR (b) decomposition into
  N1/N2 (which is sprint 047's scope) where the N1 piece reduces to
  `(coeffPlusGap_k ≥ 0 on N1) · (1/(k+1) decay)` and the N2 piece
  uses `coeffPlusGap_k = -coeffMinusGap_k` to access N2 summability.
  Queueable as a separate sprint after sprint 046 lands.
- Ship the **N1/N2 partition** of sprint 046's identity (the annulus-
  side mirror of sprint 043). This is the natural follow-up sprint
  after 046 lands; sprint 046 ships only the unconditioned
  `tsum`-of-integrals identity.
- Ship the **N2-drop or N1-drop** of the partitioned annulus equality
  (the annulus-side mirror of sprint 044). Queueable separately after
  sprint 047.
- Ship the **closing reducer with paper-axiom signature `{}` and zero
  oracle cells** that fuses sprint 044's disk-side bound with sprint
  048's annulus-side bound. This is the eventual queueable sprint
  049 (or similar); sprint 046 only ships the structural prerequisite.
- Ship a witness at any `c > 0.3554`. Sprint 046 does not raise
  `c_value`. The eventual numerical push is a *consumer* of sprint
  046 + future sprints 047/048/049, not sprint 046 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15`
  to any new chain. The new equality is materialised in side
  lemmas only.
- Discharge the per-`k` × per-`k` kernel inequality
  `Σ⁺_int(c) ≤ ∑' k, coeffPlusGap_k · (1 − c^(2k+2))/(k+1)` (the
  eventual closing kernel for sprint 049). This is a separate
  analytical sprint requiring careful sign-analysis on N1 vs N2
  indices and is queueable as part of sprint 049's contract.

## Time budget

≤ 90 minutes runtime. (Sprint 046's body is the **mechanical mirror
of sprint 042's body**; the only non-trivial new work is the
`1^(2k+2) = 1` simplification step replacing sprint 042's
`0^(2k+2) = 0` step. All other steps are sprint 042's verbatim with
the integration bounds substituted. Estimated body: ~150–200 lines.
The two V46 side lemmas reuse the universally-quantified hypothesis
pattern from V42's `_compiles` side lemma, ~15–25 lines each. Total
V46 size: ≤ 250 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* **Sprint 042 is the canonical reference for sprint 046's body.**
  Open `Reduction.lean` and find sprint 042's body
  (`diskExcess_eq_tsum_via_termwise_integration`, lines 6473–6680).
  Copy the body verbatim into the new theorem's slot, then apply the
  substitutions in the table above.

* **Key integration-bounds substitutions:**
  - `Set.Ioc 0 c` → `Set.Ioc c 1`
  - `Set.uIcc 0 c` → `Set.uIcc c 1`
  - `Set.uIcc_of_le hc_nonneg` → `Set.uIcc_of_le hc_le_one`
  - `intervalIntegral.integral_of_le hc_nonneg` →
    `intervalIntegral.integral_of_le hc_le_one`
  - `@integral_pow 0 c (2 * k + 1)` → `@integral_pow c 1 (2 * k + 1)`

* **Key closed-form substitution** (the `0^(2k+2)` vs `1^(2k+2)`
  step): in sprint 042's Step 6 (and Step 1), the line
  ```lean
  have h0 : (0:ℝ) ^ (2 * k + 1 + 1) = 0 := by
    apply zero_pow
    omega
  rw [h0, sub_zero] at h
  ```
  becomes
  ```lean
  have h1 : (1:ℝ) ^ (2 * k + 1 + 1) = 1 := one_pow _
  rw [h1] at h
  -- Now h : ∫ r in c..1, r^(2k+1) = 1 / (2k+1+1) - c^(2k+1+1) / (2k+1+1)
  -- Need to combine the two terms: 1/(2k+2) - c^(2k+2)/(2k+2) = (1 - c^(2k+2))/(2k+2)
  ```
  The combination step `1/(2k+2) - c^(2k+2)/(2k+2) = (1 - c^(2k+2))/(2k+2)`
  is a one-line `field_simp` or `ring` invocation.

* **Annulus-side `rfl` step:** in sprint 042's Step 7
  ```lean
  have h_diskExcess :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c =
        ∫ r in (0:ℝ)..c, 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) 0 c = _
    rfl
  ```
  becomes
  ```lean
  have h_annulusExcess :
      PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c =
        ∫ r in c..(1:ℝ), 2 * r * PaperAxioms.circleGap a b r := by
    change AnnulusIntegralReduction.annulusSlice
      (PaperAxioms.circleGap a b) c 1 = _
    rfl
  ```
  This works because `PaperAxioms.annulusExcess` is defined as
  `AnnulusIntegralReduction.annulusSlice circleGap c 1` (verified via
  `KorenblumPaper/PaperAxioms.lean` lines 272–273).

* **Absolute-value chain on `[c, 1]`:** in sprint 042's Step 1, the
  L¹-norm closed form starts with
  ```lean
  have h_norm_eq :
      ∀ r ∈ Set.uIcc (0:ℝ) c,
        ‖F k r‖ = 2 * |coeffPlusGap a b k| * r^(2*k+1) := by
    intro r hr
    rw [Set.uIcc_of_le hc_nonneg] at hr
    have hr_nonneg : 0 ≤ r := hr.1
    -- ...
  ```
  becomes
  ```lean
  have h_norm_eq :
      ∀ r ∈ Set.uIcc c (1:ℝ),
        ‖F k r‖ = 2 * |coeffPlusGap a b k| * r^(2*k+1) := by
    intro r hr
    rw [Set.uIcc_of_le hc_le_one] at hr
    have hr_nonneg : 0 ≤ r := le_trans hc_nonneg hr.1
    -- ...
  ```
  The only change is deriving `0 ≤ r` from `c ≤ r` and `0 ≤ c` (one
  `le_trans` step) instead of taking `0 ≤ r` directly from
  `(Ioc 0 c).1`.

* **The `_compiles` side lemma's expected shape:**
  ```lean
  theorem v46_annulusExcess_eq_tsum_via_termwise_integration_compiles
      (a b : ℕ → ℂ)
      (hSummable_int_norm :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            (1 - c_value ^ (2 * k + 2)) / (k + 1))) :
      PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c_value =
        ∑' k : ℕ, PaperAxioms.coeffPlusGap a b k *
          (1 - c_value ^ (2 * k + 2)) / (k + 1) :=
    annulusExcess_eq_tsum_via_termwise_integration (a := a) (b := b)
      c_value_nonneg c_value_le_one hSummable_int_norm
  ```
  where `c_value_le_one : c_value ≤ 1` is derived inline via `by
  unfold c_value; norm_num` (or via the existing `c_value_lt_one.le`
  in V45's helpers).

* **The `_recovers_sprint041_at_seed` side lemma's expected shape:**
  Acceptable simplification: stop at the direct invocation of sprint
  046 alone, mirroring sprint 044's `_recovers_sprint043_at_seed`
  pattern. The full consistency check against sprint 041 is queueable
  separately if needed.

* **Premise `hc_le_one` in the new theorem's signature:** unlike
  sprint 042 which only needs `hc_nonneg : 0 ≤ c` (the upper bound
  `c` of the `[0, c]` integration interval is the parameter itself,
  no separate upper-bound hypothesis is required), sprint 046 needs
  both `0 ≤ c` AND `c ≤ 1` (the upper bound `1` of the `[c, 1]`
  integration interval is fixed, and we need `c ≤ 1` to ensure the
  interval is non-degenerate).

* **Edge case `c = 1`:** at the boundary `c = 1`, the integration
  interval `[c, 1] = [1, 1]` is degenerate and `annulusExcess
  (circleGap a b) 1 = ∫_1^1 ... = 0`. The RHS `∑' k, coeffPlusGap_k
  · (1 − 1^(2k+2))/(k+1) = ∑' k, coeffPlusGap_k · 0 / (k+1) = 0`
  also vanishes, so the equality holds trivially. No special handling
  needed.

* **Edge case `c = 0`:** at the boundary `c = 0`, the integration
  interval `[c, 1] = [0, 1]` is the full disk, and `annulusExcess
  (circleGap a b) 0 = annulusSlice (circleGap a b) 0 1 = ∫_0^1 2r ·
  circleGap a b r dr` is the full integrated `circleGap`. The RHS
  `∑' k, coeffPlusGap_k · (1 − 0)/(k+1) = ∑' k, coeffPlusGap_k /
  (k+1)` is the natural full-disk per-`k` series. The equality
  recovers the limit case naturally — no special handling needed.

* **Note on summability premise's seed-witness discharge:** the
  workspace's `OneModePaperBridge.lean` may expose a single-mode
  example where `coeffPlusGap_k = ‖a k‖² − ‖b k‖²` is identically
  `0` for all but one `k`, in which case the premise's single
  non-trivial term is bounded and summability is trivial. For
  general `(a, b)` data the summability discharge requires the
  N1/N2 decomposition (sprint 047's scope). The V46 side lemma may
  take the summability cell as an explicit hypothesis without
  discharging it inline — mirroring sprint 042's V42 file pattern.
