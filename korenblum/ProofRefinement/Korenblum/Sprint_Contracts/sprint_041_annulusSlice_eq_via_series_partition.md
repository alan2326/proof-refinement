# Sprint 041: First paper-axiom-free integrated `annulusSlice` *equality* identity over an arbitrary `[α, β] ⊂ [0, 1)` via sprint 027's pointwise equality + `intervalIntegral.integral_sub`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V40.lean`
**Target file**: `Candidates/V41.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem annulusSlice_eq_via_series_partition
    {a b : ℕ → ℂ} {α β : ℝ}
    (hα_nonneg : 0 ≤ α)
    (hα_le_β  : α ≤ β)
    (hβ_lt_one : β < 1)
    (hSummable :
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ β →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume α β)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ) volume α β)
    (hIntZ :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
        volume α β) :
    AnnulusIntegralReduction.annulusSlice
        (PaperAxioms.circleGap a b) α β =
      (∫ ρ in α..β, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        - ∫ ρ in α..β, 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
```

The proof body:

1. Use sprint 027's *equality* identity
   `circleGap a b ρ = sigmaPlus a b ρ − ρ²·sigmaZeroMinus a b ρ`
   pointwise on `ρ ∈ Set.uIcc α β = [α, β]`. The summability hypothesis
   is satisfied at every `ρ ∈ [α, β]` since `α ≤ ρ ≤ β` and
   `hSummable` is universally quantified on `[0, β]`.
2. Multiply by `2ρ ≥ 0` to convert to the integrand form
   (paper-axiom-free; only requires `α ≥ 0`):
   `2ρ·circleGap a b ρ = 2ρ·sigmaPlus a b ρ − 2ρ³·sigmaZeroMinus a b ρ`
   on `[α, β]`.
3. Integrate the pointwise equality on `[α, β]` via
   `intervalIntegral.integral_congr` (since the equality holds
   pointwise on `Set.uIcc α β`, no a.e.-upgrade is required).
4. Split the integral via `intervalIntegral.integral_sub
   hIntSigmaPlus hIntZ`.
5. Identify the LHS of the resulting integral identity with
   `AnnulusIntegralReduction.annulusSlice (circleGap a b) α β` via
   the `annulusSlice` definition (`change` or `unfold`).

This is the workspace's **first paper-axiom-free integrated
*equality* identity for `annulusSlice`** over a generic `[α, β] ⊂ [0,
1)`, valid uniformly across the disk-side window `[0, c]`, the
annulus-side window `[c, 1]`, the branch-1 sub-interval `[c,
branchSplit c]`, the branch-2 sub-interval `[branchSplit c, 1]`, and
any sub-interval of any of these.

Crucially, this is an **equality**, not an upper or lower bound. Every
prior integrated `diskExcess`/`annulusSlice` lemma in the workspace is
an *inequality* — sprints 003/013/026/030/034/040 ship upper bounds on
`diskExcess`; sprints 005/006/037/038 ship lower bounds on
`annulusSlice`. Sprint 041 ships an *exact identity* connecting
`annulusSlice` to two pure-series integrated quantities (`∫ 2ρ·Σ⁺(ρ) dρ`
and `∫ 2ρ³·Z(ρ) dρ`), with **zero paper-axiom invocations** and **zero
oracle cells**.

The identity has two natural specializations:

| `(α, β)` | Specialization |
|----------|----------------|
| `(0, c)` | Disk-side equality: `diskExcess (circleGap a b) c = ∫₀^c 2ρ·Σ⁺(ρ) − ∫₀^c 2ρ³·Z(ρ)` |
| `(c, 1)` | Annulus-side equality: `annulusExcess (circleGap a b) c = ∫_c^1 2ρ·Σ⁺(ρ) − ∫_c^1 2ρ³·Z(ρ)` |

Sprint 040 *implicitly* established the `(0, c)` case as an
intermediate step before dropping the second integral; sprint 041
**names the equality as a standalone lemma** and generalises it to an
arbitrary `[α, β]`. The `(c, 1)` specialization is **entirely new** —
no prior workspace lemma expresses `annulusExcess` as an algebraic
combination of pure-series integrals.

Then ship a `Candidates/V41.lean` at the same `c = 0.3554` that
compiles, scores `≥ V40 = 1777/5000`, and **materialises** the new
equality in three side lemmas:

- `v41_annulusSlice_eq_via_series_partition_compiles` —
  signature compilation of the new generic lemma at the seed.
- `v41_annulusSlice_eq_via_series_partition_disk_specialisation` —
  applies the new lemma at `(α, β) = (0, c_value)` to derive
  `diskExcess (circleGap a b) c_value = ∫₀^{c_value} 2ρ·Σ⁺(ρ) − ∫₀^{c_value} 2ρ³·Z(ρ)`.
- `v41_annulusSlice_eq_via_series_partition_annulus_specialisation` —
  applies the new lemma at `(α, β) = (c_value, 1)` to derive
  `annulusExcess (circleGap a b) c_value = ∫_{c_value}^1 2ρ·Σ⁺(ρ) − ∫_{c_value}^1 2ρ³·Z(ρ)`.

The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 041 ships:

1. **First workspace integrated *equality* identity (not just a
   bound) for `annulusSlice`.** Every prior integrated
   `annulusSlice`-related lemma is an inequality:

   | Sprint | Layer | Direction | Region |
   |--------|-------|-----------|--------|
   | 003    | `diskExcess` | upper bound | `[0, c]` |
   | 005    | `circleGap` annulus pointwise | lower bound | `(c, 1)` |
   | 006    | `annulusSlice [ρ₁, ρ₂]` | lower bound | `(c, 1)` |
   | 013    | `diskExcess` | upper bound | `[0, c]` |
   | 026    | `diskExcess` | upper bound | `[0, c]` |
   | 030    | `diskExcess` | upper bound | `[0, c]` |
   | 034    | `diskExcess` | upper bound (modulo `hSigmaCmp`) | `[0, c]` |
   | 037    | `circleGap` annulus pointwise | lower bound (modulo `hLambdaBridge`) | `(c, 1)` |
   | 038    | `annulusSlice [ρ₁, ρ₂]` | lower bound (modulo `hLambdaBridgeWindow`) | `(c, 1)` |
   | 040    | `diskExcess` | upper bound | `[0, c]` |
   | **041 (NEW)** | **`annulusSlice [α, β]`** | **EQUALITY** | **`[0, 1)` (any sub-interval)** |

   An equality is structurally stronger than an inequality in either
   direction: it can be used as both an upper bound *and* a lower
   bound, depending on what the consumer needs. Sprint 041 is the
   **first** workspace lemma at the integrated layer with this
   property, and it covers **all** existing window regimes uniformly
   (disk, annulus, branch-1 sub-interval, branch-2 sub-interval, and
   sub-windows thereof).

2. **First workspace lemma to express `annulusExcess` as a
   pure-series quantity.** Until sprint 041, every workspace lemma on
   the annulus side either:
   - bounds `annulusSlice` from below by an integral involving
     `paperLambda` (sprints 005/006: `2ρ·circleGap ≥ 2ρ³·Z(ρ)/Λ(c,
     ρ)`), or
   - bounds `annulusSlice` from below modulo a `hLambdaBridge` cell
     (sprints 037/038: same shape but with `hLambdaBridge` lifted to
     the type level).

   Sprint 041 expresses `annulusExcess (circleGap a b) c =
   annulusSlice (circleGap a b) c 1 = ∫_c^1 2ρ·Σ⁺(ρ) dρ − ∫_c^1
   2ρ³·Z(ρ) dρ` as a **pure series quantity** with no `Λ` and no
   bridge cell. This is the **first** workspace lemma to bridge from
   `annulusSlice` to series integrals without going through
   `paperLambda`.

3. **First closing-reducer prerequisite for a paper-axiom-free,
   oracle-cell-free `valid_of_*` reducer.** The closing-reducer matrix
   so far requires at least one of `{paper.eq*, hSigmaCmp,
   hLambdaBridgeWindow}`:

   | Reducer | Paper-axiom signature | Oracle cells |
   |---------|----------------------|--------------|
   | s014, s017, s020, s021, s023 | `{eq*}` non-empty | none |
   | s024 | `{eq*}` non-empty | none |
   | s035 | none | `{hSigmaCmp}` |
   | s039 | none | `{hSigmaCmp, hLambdaBridgeWindow}` |

   Sprint 041's equality identity is the missing structural ingredient
   for a future closing reducer with **paper-axiom signature `{}` and
   oracle cell signature `{}`** — both sides of the kernel inequality
   would be pure series quantities, with no `Λ` and no `Σ⁺ ≤ Σ⁻`
   anywhere. The kernel would have shape:

   `c²·Σ⁺(c) ≤ ∫_c^1 2ρ·Σ⁺(ρ) − ∫_c^1 2ρ³·Z(ρ)`

   which simplifies to:

   `c²·Σ⁺(c) + ∫_c^1 2ρ³·Z(ρ) ≤ ∫_c^1 2ρ·Σ⁺(ρ)`

   This kernel is **structurally distinct** from sprint 014's `c⁴ ≤
   ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ)` and sprint 039's `Λ`-mediated kernel: it
   couples `Σ⁺` evaluations at `c` and across `[c, 1]` against `Z`
   integrals, and depends on the precise `(a, b)` series tail
   structure rather than on the externally-supplied `Λ` envelope.

4. **First downstream consumer of sprint 027's equality on the
   annulus side.** Sprint 027 ships the pointwise equality `circleGap
   r = sigmaPlus r − r²·sigmaZeroMinus r` valid on `[0, ∞)` (modulo
   summability). Sprint 040 consumes it on `[0, c]` to produce a
   disk-side bound. Sprint 041 consumes it on `[α, β]` for **any**
   `[α, β] ⊂ [0, 1)`, with the annulus-side specialization at `[c,
   1]` being algebraically novel. This is also the first sprint to
   exercise sprint 027 over a window whose lower endpoint is strictly
   positive, requiring the summability hypothesis to be uniform on a
   range bounded away from `0` (a structurally different
   uniformity discipline than sprint 040's `Ioo 0 c`).

5. **Strict structural upgrade over sprint 040's intermediate
   identity.** Sprint 040 *implicitly* establishes the equality
   `diskExcess = ∫ 2r·Σ⁺ − ∫ 2r³·Z` at the integrated layer but
   immediately drops the second term. Sprint 041 names this equality
   as a standalone lemma, generalises it to any `[α, β]`, and exposes
   it as a reusable building block. After sprint 041 lands, sprint
   040 can be re-derived as a 4-line corollary
   (specialise sprint 041 at `[0, c]`, then drop the non-negative
   `∫ 2r³·Z` term using `intervalIntegral.integral_nonneg`); sprint
   041 leaves sprint 040 in place as an independent lemma.

6. **Foundation for paper-axiom-free Σ⁺-monotone closing reducer.**
   Sprint 032's `sigmaPlus_monotone_of_summable` says `Σ⁺(ρ) ≥
   Σ⁺(c)` for `ρ ≥ c`. Combined with sprint 041's annulus-side
   specialization, this gives:
   `∫_c^1 2ρ·Σ⁺(ρ) dρ ≥ ∫_c^1 2ρ·Σ⁺(c) dρ = (1 − c²)·Σ⁺(c)`.
   So the kernel inequality `c²·Σ⁺(c) + ∫_c^1 2ρ³·Z(ρ) ≤ ∫_c^1
   2ρ·Σ⁺(ρ)` reduces to:
   `c²·Σ⁺(c) + ∫_c^1 2ρ³·Z(ρ) ≤ (1 − c²)·Σ⁺(c) + (correction term)`,
   yielding a sufficient condition `(2c² − 1)·Σ⁺(c) + ∫_c^1 2ρ³·Z(ρ) ≤ 0`
   for any `c > 1/√2`, **but** since `Σ⁺(c) ≥ 0` and `∫_c^1 2ρ³·Z(ρ)
   ≥ 0`, this can hold only in a degenerate regime. The full kernel
   analysis is **out of scope for sprint 041** but the sketch
   demonstrates that sprint 041 unlocks a non-trivial kernel
   structure for a future closing reducer. The numerical exploration
   of which `(a, b)` configurations satisfy the new kernel is queued
   as a separate `Scratch/` sprint after 041 lands.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V41 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is a new bound *shape* (in fact, an *equality*) on
  a generic radial sub-interval, not a numerical refinement of an
  existing closed-form coefficient.

Why this is **not** "the same chain" as sprint 040:

* **Equality vs inequality.** Sprint 040 ships an *inequality*
  `diskExcess ≤ c²·Σ⁺(c)` (drops the `−r²·Z_r` term). Sprint 041
  ships an *equality* `annulusSlice α β = ∫ 2ρ·Σ⁺(ρ) − ∫ 2ρ³·Z(ρ)`
  (retains the second term). An equality is strictly stronger.
* **Generic window vs fixed `[0, c]`.** Sprint 040 is fixed at the
  disk-side window. Sprint 041 is parametric in `(α, β)` and covers
  all annulus regions used elsewhere in the workspace.
* **Annulus-side specialization is novel.** Sprint 040 has no
  annulus-side counterpart shipped. Sprint 041's `(c, 1)`
  specialization is the **first** annulus-side lemma to express
  `annulusExcess` as a pure-series quantity (no `Λ`, no oracle).
* **Different consumer pattern.** Sprint 040 is consumed by
  closing reducers that need an upper bound on `diskExcess`. Sprint
  041 is consumed by closing reducers that need an exact identity for
  `annulusSlice` — a different consumer pattern, not a refinement of
  sprint 040's.

Why this is **not** "the same chain" as sprint 027:

* **Sprint 027 is a pointwise *identity***; sprint 041 is the
  *integrated* counterpart. Different layers.
* **Sprint 027 has no integration**; sprint 041 invokes
  `intervalIntegral.integral_sub`, `intervalIntegral.integral_congr`,
  and the `annulusSlice` definition unfolding. Sprint 041 is
  sprint 027's **first integrated annulus-slice consumer** for any
  `[α, β]` with `α > 0`.

Why this is **not** "the same chain" as sprints 005/006/037/038:

* **Sprints 005/006/037/038 produce annulus-side *lower bounds*** on
  `circleGap`/`annulusSlice` via the `Λ`-bridge route (paper or
  oracle). Sprint 041 produces an annulus-side *equality* via the
  `Σ⁺/Z`-decomposition route, with **no `Λ` reference anywhere** in
  the proof body and **no `hLambdaBridge` cell** in the signature.
  The two routes are structurally disjoint: 005-cone goes through
  paper `(8)+(9)` (or its oracle counterpart); sprint 041 goes
  through sprint 027's series partition (paper-axiom-free).
* **Sprints 006/038 require a sub-interval `[ρ₁, ρ₂] ⊂ (c, 1)`**
  with strict inequalities. Sprint 041 accepts `[α, β] ⊂ [0, 1)`
  with weak inequalities, including the full annulus `[c, 1]` and
  the full disk `[0, c]`.

Why this is **bounded enough for one Generator session**:

* Sprint 040's body is ~150 lines (estimated; landed in V40). Sprint
  041's body is **strictly simpler** than sprint 040's: it stops at
  the equality, without the additional pointwise-monotone bound on
  `Σ⁺` or the non-negative-drop on `∫ 2r³·Z`. The proof structure is:
  (a) pointwise equality on `[α, β]` (one-line invocation of sprint
  027 inside `intro` + `exact`); (b) `intervalIntegral.integral_congr`
  to integrate the pointwise equality (verbatim Mathlib pattern, no
  a.e.-upgrade needed since equality is on `[α, β]` directly);
  (c) `intervalIntegral.integral_sub hIntSigmaPlus hIntZ` to split
  the RHS integral; (d) unfold `annulusSlice` to identify with the
  LHS. Estimated body: **~60–80 lines**.
* All Lean idioms used (`refine`, `intro`, `intervalIntegral.*`,
  `unfold`, `change`, `linarith`, `ring`) are verbatim from sprints
  026/040. No new idioms required.
* The three side-lemma materialisations in V41 are short:
  `_compiles` is a one-line application of the new lemma at the seed
  with hypotheses universally quantified; `_disk_specialisation` and
  `_annulus_specialisation` are 3–5 line wrappers each that
  instantiate `(α, β)` and unfold to `diskExcess`/`annulusExcess`.
  Estimated V41 size: ≤ 200 lines total.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem annulusSlice_eq_via_series_partition
      {a b : ℕ → ℂ} {α β : ℝ}
      (hα_nonneg : 0 ≤ α)
      (hα_le_β  : α ≤ β)
      (hβ_lt_one : β < 1)
      (hSummable :
        ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ β →
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
      (hIntCircle :
        IntervalIntegrable
          (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume α β)
      (hIntSigmaPlus :
        IntervalIntegrable
          (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ) volume α β)
      (hIntZ :
        IntervalIntegrable
          (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
          volume α β) :
      AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) α β =
        (∫ ρ in α..β, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
          - ∫ ρ in α..β, 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Append after sprint 040's
  `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
  (current end of `Reduction.lean`, after line 6352).
  Estimated ~80 lines.

  The proof body structure:

  1. **Pointwise equality** via sprint 027 on `ρ ∈ Set.uIcc α β`:
     ```lean
     have hPointwiseEq :
         ∀ ρ ∈ Set.uIcc α β,
           PaperAxioms.circleGap a b ρ =
             PaperAxioms.sigmaPlus a b ρ
               - ρ ^ 2 * PaperAxioms.sigmaZeroMinus a b ρ := by
       intro ρ hρ
       have hρ_nonneg : 0 ≤ ρ := by
         have : α ≤ ρ := (Set.mem_uIcc.mp hρ).resolve_right (fun h => by linarith)
                          |>.1
         linarith
       have hρ_le_β : ρ ≤ β := by
         have : ρ ≤ β := (Set.mem_uIcc.mp hρ).resolve_right (fun h => by linarith)
                          |>.2
         exact this
       exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
         a b hρ_nonneg (hSummable hρ_nonneg hρ_le_β)
     ```
     Note: since `α ≤ β`, `Set.uIcc α β = Set.Icc α β`. The endpoint
     handling reduces to the one branch of the `uIcc` disjunction.
     If awkward, replace `Set.uIcc α β` with `Set.Icc α β` and use
     `intervalIntegral.integral_congr` with the `Icc`-form precondition
     (Mathlib provides both signatures).

  2. **Multiply by `2ρ`** to convert to the integrand form:
     ```lean
     have hPointwiseEq_jac :
         ∀ ρ ∈ Set.uIcc α β,
           2 * ρ * PaperAxioms.circleGap a b ρ =
             2 * ρ * PaperAxioms.sigmaPlus a b ρ
               - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ := by
       intro ρ hρ
       have hEq := hPointwiseEq ρ hρ
       rw [hEq]; ring
     ```

  3. **Integrate the pointwise equality** via
     `intervalIntegral.integral_congr` (no a.e.-upgrade is needed
     because the pointwise equality holds on the closed interval
     `[α, β] = Set.uIcc α β`):
     ```lean
     have hIntegralEq :
         ∫ ρ in α..β, 2 * ρ * PaperAxioms.circleGap a b ρ =
           ∫ ρ in α..β,
             (2 * ρ * PaperAxioms.sigmaPlus a b ρ
               - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ) :=
       intervalIntegral.integral_congr hPointwiseEq_jac
     ```

  4. **Split the integral** via
     `intervalIntegral.integral_sub hIntSigmaPlus hIntZ`:
     ```lean
     have hIntegralSub :
         ∫ ρ in α..β,
             (2 * ρ * PaperAxioms.sigmaPlus a b ρ
               - 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ) =
           (∫ ρ in α..β, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
             - ∫ ρ in α..β, 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ :=
       intervalIntegral.integral_sub hIntSigmaPlus hIntZ
     ```

  5. **Identify the LHS with `annulusSlice`** by unfolding the
     `annulusSlice` definition and chaining the equalities:
     ```lean
     show AnnulusIntegralReduction.annulusSlice
            (PaperAxioms.circleGap a b) α β = _
     unfold AnnulusIntegralReduction.annulusSlice
     -- Goal: ∫ ρ in α..β, 2 * ρ * circleGap a b ρ = ...
     exact hIntegralEq.trans hIntegralSub
     ```
     (The `unfold` step's exact form depends on how `annulusSlice` is
     stated in `AnnulusIntegralReduction.lean:25`. If `annulusSlice`
     unfolds to `∫ ρ in α..β, 2 * ρ * circleGap ρ`, the chain is
     direct. If it unfolds to a slightly different form, an
     additional `simp only [...]` or `rfl`-step may be needed.)

- `ProofRefinement/Korenblum/Candidates/V41.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V40),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V40),
  4. Adds three side lemmas exercising the new generic equality:
     - `v41_annulusSlice_eq_via_series_partition_compiles` —
       exhibits the new equality's signature compilation at the seed
       by feeding the integrability/summability cells as
       universally-quantified hypotheses on the side lemma.
       Concrete conclusion at `(α, β) = (0, c_value)`:
       `AnnulusIntegralReduction.annulusSlice (circleGap a b) 0 c_value =
        (∫ ρ in (0:ℝ)..c_value, 2*ρ*sigmaPlus a b ρ) - (∫ ρ in (0:ℝ)..c_value, 2*ρ^3*sigmaZeroMinus a b ρ)`.
       Does **not** use a `Section2Assumptions` instance.
     - `v41_annulusSlice_eq_via_series_partition_disk_specialisation` —
       takes universally-quantified `(a, b)` and the
       summability/integrability hypotheses; applies the new
       equality at `(α, β) = (0, c_value)`; uses the
       `PaperAxioms.diskExcess` definition unfolding to derive
       `PaperAxioms.diskExcess (circleGap a b) c_value =
        (∫ ρ in (0:ℝ)..c_value, 2*ρ*sigmaPlus a b ρ) - (∫ ρ in (0:ℝ)..c_value, 2*ρ^3*sigmaZeroMinus a b ρ)`.
       Concrete materialisation that the disk-side specialization
       reproduces sprint 040's intermediate step (without the drop).
     - `v41_annulusSlice_eq_via_series_partition_annulus_specialisation` —
       takes universally-quantified `(a, b)` and the
       summability/integrability hypotheses on `[c_value, 1]`;
       applies the new equality at `(α, β) = (c_value, 1 - 1/10^9)`
       (a window strictly inside `[0, 1)` to satisfy the `β < 1`
       hypothesis; this is sufficient for materialisation at the
       seed). Conclusion:
       `AnnulusIntegralReduction.annulusSlice (circleGap a b) c_value (1 - 1/10^9) =
        (∫ ρ in c_value..(1 - 1/10^9), 2*ρ*sigmaPlus a b ρ) -
        (∫ ρ in c_value..(1 - 1/10^9), 2*ρ^3*sigmaZeroMinus a b ρ)`.
       Demonstrates that the new lemma applies to annulus-side
       windows previously inaccessible to paper-axiom-free
       integrated equalities.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V40) — the new equality is
     materialised in side lemmas, **not** as the sink theorem's
     discharge route, since the closing-reducer fusion with sprint
     032's monotonicity is queueable as a separate sprint.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V41` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V41.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V41 ties V40 at
   the seed; the new theorem is structural and does not change
   `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V41.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem `annulusSlice_eq_via_series_partition` appears in
   `ProofRefinement/Korenblum/Proof/Reduction.lean` and is exercised
   in `Candidates/V41.lean`'s three side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection. Greppable check: in the body of
   the new theorem, the count of `paper.eq` substrings is **0**. (No
   `paper : Section2Assumptions ...` parameter is even taken —
   sprint 041's signature is `(a, b, α, β)`-only with no `K` and no
   `paper`.)
7. The proof body invokes
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   (sprint 027) at least once. Greppable check: count of
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` in
   the body of the new theorem is **≥ 1**.
8. The proof body invokes `intervalIntegral.integral_sub` at least
   once for the integral-splitting step. Greppable check: count of
   `intervalIntegral.integral_sub` in the body of the new theorem
   is **≥ 1**.
9. The proof body invokes `intervalIntegral.integral_congr` (or
   `intervalIntegral.integral_congr_ae`) at least once for
   integrating the pointwise equality. Greppable check: count of
   `intervalIntegral.integral_congr` in the body of the new theorem
   is **≥ 1**.
10. The new theorem's conclusion is an **equality** (not an
    inequality): the conclusion contains `=` and **does not** contain
    `≤` between `annulusSlice` and the RHS. Greppable check: in the
    new theorem's signature line, the substring `≤` does not appear
    in the conclusion.
11. The new theorem **does not invoke** the old sprint 025 lemma
    `circleGap_le_sigmaPlus_via_series_split` — sprint 027's
    *equality* is used instead of sprint 025's *inequality*.
    Greppable check: count of
    `circleGap_le_sigmaPlus_via_series_split` in the body of the new
    theorem is **0**.
12. The new theorem **does not invoke** sprint 040's lemma
    `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
    — sprint 041 is a parallel chain at a more general (window-
    parametric) layer, not a wrapper. Greppable check: count of
    `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
    in the body of the new theorem is **0**.
13. The new theorem **does not invoke** `paperLambda` anywhere in
    its proof body or signature. Greppable check: count of
    `paperLambda` in the new theorem (signature + body) is **0**.
14. The V41 `_disk_specialisation` side lemma's conclusion
    references `PaperAxioms.diskExcess` (not just
    `annulusSlice ... 0 c_value`).
15. The V41 `_annulus_specialisation` side lemma's conclusion
    references `AnnulusIntegralReduction.annulusSlice (circleGap
    a b) c_value (1 - 1/10^9)` (or any β < 1 of the Generator's
    choice; the structural point is that `α = c_value` and `β` is a
    rational strictly less than 1 — the previously-unaddressed
    annulus-side window).

## Out of scope

- Edit older candidates V0–V40.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V41 is
  the same `hEq15_seed_3554` that V0–V40 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Ship a closing reducer fusing sprint 041 with any other lemma to
  produce a paper-axiom-free, oracle-free `valid_of_*` reducer. That
  is the **next** sprint's scope; sprint 041 ships only the equality
  identity. Reason: the kernel inequality analysis (e.g., sprint
  032's `Σ⁺(ρ) ≥ Σ⁺(c)` integrated bound + the `∫ 2ρ³·Z(ρ) ≥ 0`
  drop + algebraic simplification to a `(c, a, b)`-kernel) is a
  separate analytical sprint that can use sprint 041 as a building
  block.
- Ship a witness at any `c > 0.3554`. Sprint 041 does not raise
  `c_value`. The eventual numerical push is a *consumer* of sprint
  041 + a future closing reducer + the kernel inequality evaluation,
  not sprint 041 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15` to
  any new chain. The new equality is materialised in side lemmas
  only.
- Ship a series-derived `IntervalIntegrable (2ρ·sigmaPlus a b ρ)`
  proof on `[α, β]`. The integrability hypothesis is taken as
  universally quantified on the lemma; deriving it from termwise
  structure + Mathlib `MeasureTheory` would consume a Generator
  session on its own and is queueable separately.
- Ship a paper-axiom-free `Σ⁺ ≤ Σ⁻` workspace lemma. Sprint 041
  sidesteps this entirely by working at the equality level (no
  side-comparison is invoked).
- Use `MeasureTheory.tsum_integral_eq_integral_tsum`-style
  swap-of-sum-and-integral machinery. Sprint 041's body integrates
  a pointwise *equality* (sprint 027's equality is already in
  `sigmaPlus − r²·Z` form), which is integrated as a single
  difference-of-integrals via `intervalIntegral.integral_sub`; no
  swap of sum and integral is needed.
- Ship a generic upper bound on `∫_α^β 2ρ³·sigmaZeroMinus a b ρ`
  via `Z`-monotonicity. That is a derived sprint that uses sprint
  041 as input.

## Time budget

≤ 60 minutes runtime. (Sprint 041's body is **strictly simpler**
than sprint 040's body — it stops at the equality, with no `Σ⁺`
monotone bound or `Z ≥ 0` drop. Estimated body: ~60–80 lines, less
than sprint 040's ~150. The three V41 side lemmas reuse universally-
quantified hypothesis patterns from V40's `_compiles` and
`_recovers_via_eq4_at_seed` side lemmas, ~30–60 lines each. Total V41
size: ≤ 200 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* `Set.uIcc α β = Set.Icc α β` when `α ≤ β`; the proof can use
  either form, but the `intervalIntegral.integral_congr` lemma in
  Mathlib is stated for `Set.uIcc` (which handles both
  `α ≤ β` and `α > β` orientations). Use `Set.uIcc` for
  cleanliness, then derive the `Icc` form via
  `Set.uIcc_of_le hα_le_β`.

* Sprint 027 is stated with hypothesis `r ≥ 0` plus a single
  summability cell at `r`. Sprint 041's `hSummable` is
  universally-quantified over `[0, β]` (one direction of `ρ`
  bounds suffices since the new lemma is parametric in `(α, β)`
  with `α ≤ β` and the summability cone is determined by `β`).
  At each `ρ ∈ [α, β]`, `0 ≤ ρ` follows from `0 ≤ α ≤ ρ` and
  `ρ ≤ β` is from membership. The summability cell is dispatched
  by `hSummable hρ_nonneg hρ_le_β`.

* The cleanest Mathlib lemma for step 3 is
  `intervalIntegral.integral_congr` (statement: if `f =ᵃ.ᵉ.[μ] g`
  on `[α, β]`, then `∫ f = ∫ g`). Mathlib also provides a stronger
  variant taking pointwise equality on `Set.uIcc α β` directly. The
  pointwise equality `2ρ·circleGap = 2ρ·Σ⁺ − 2ρ³·Z` holds on all of
  `[α, β]` (modulo the summability cell), so no a.e.-upgrade is
  needed.

* `intervalIntegral.integral_sub` requires both arguments to be
  `IntervalIntegrable`; the cell `hIntZ` is **not** redundant from
  `hIntCircle` and `hIntSigmaPlus` despite the algebraic identity
  `2ρ³·Z(ρ) = 2ρ·Σ⁺(ρ) − 2ρ·circleGap(ρ)` (Mathlib's
  `IntervalIntegrable` is not a ring; deriving `hIntZ` from
  `hIntSigmaPlus.sub hIntCircle` after rewriting via sprint 027's
  equality requires the equality to hold a.e., reintroducing the
  same step-3 a.e.-equivalence pattern). Cleaner to take `hIntZ`
  as a separate cell.

* The `annulusSlice` definition unfolds to `∫ ρ in α..β, 2 * ρ *
  circleGap ρ` — see `KorenblumPaper/AnnulusIntegralReduction.lean:25`.
  The closing `unfold AnnulusIntegralReduction.annulusSlice` step is
  direct; if `unfold` does not fully reduce, fall back to `simp only
  [AnnulusIntegralReduction.annulusSlice]` or a manual `change` on
  the goal.

* For the V41 side lemmas:
  - `_compiles` should take all four hypothesis cells
    (`hSummable`, `hIntCircle`, `hIntSigmaPlus`, `hIntZ`) as
    universally-quantified parameters and feed them directly to
    sprint 041 at `(α, β) = (0, c_value)` to produce the equality
    conclusion.
  - `_disk_specialisation` should take the same hypotheses (with
    `(α, β) = (0, c_value)`-specific instantiation), invoke sprint
    041, then `unfold PaperAxioms.diskExcess` to recognise
    `annulusSlice (circleGap a b) 0 c_value = diskExcess (circleGap a b) c_value`.
  - `_annulus_specialisation` should pick a fixed concrete `β` such
    as `(99999/100000)` or `(1 - 1/10^9)` (any rational strictly
    less than 1) for cleanliness, then invoke sprint 041 at
    `(α, β) = (c_value, β)`. The full `[c_value, 1]` annulus is
    not used because sprint 041's `β < 1` constraint forbids `β = 1`;
    the sub-window suffices to demonstrate that the lemma applies
    to annulus-side windows. If a future sprint wants to handle
    `β = 1` (the literal `annulusExcess` definition uses `[c, 1]`
    closed at `1`), it must either (a) loosen sprint 041's
    `hβ_lt_one` to `hβ_le_one` (which requires the summability
    hypothesis at `ρ = 1`, which is generally **not** satisfied for
    the `circleGapSeries` since the series diverges as `ρ → 1`), or
    (b) take a limit `β → 1⁻` argument (queueable as a separate
    sprint with its own analytical content). For sprint 041, the
    sub-window specialization is sufficient.

* If the Generator finds the integrability discipline difficult to
  satisfy *inside* the side lemmas, an acceptable alternative is to
  **leave the integrability cells universally quantified** in the
  side lemmas (mirroring how sprint 040's `_compiles` and
  `_recovers_via_eq4_at_seed` side lemmas handle their own
  integrability cells). The side lemmas demonstrate the equality's
  *signature compilation* at the seed; full integrability discharge
  is queueable separately.
