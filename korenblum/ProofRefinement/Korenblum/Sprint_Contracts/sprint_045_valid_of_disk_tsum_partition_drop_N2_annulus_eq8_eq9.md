# Sprint 045: First closing reducer with **paper-axiom signature `{eq8, eq9}`**, **zero oracle cells**, and **per-`k` termwise series** disk-side kernel `Σ⁺_int(c)` — fusing sprint 044's paper-axiom-free, oracle-cell-free disk bound with sprint 006's `(8)+(9)`-derived annulus lower bound

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V44.lean`
**Target file**: `Candidates/V45.lean`
**Direction**: section2-proof

## Goal

Ship one new generic closing-reducer theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            -- sprint 044's input cell: integrated absolute-value summability
            Summable (fun k : ℕ =>
              |PaperAxioms.coeffPlusGap a b k| *
                c ^ (2 * k + 2) / (k + 1)) ∧
            -- sprint 006's input cell: summability for series-monotonicity
            -- transfer at the right edge ρ₂
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k)
              else 0) ∧
            -- sprint 044's disk-side integrability (none — sprint 044 is
            -- termwise and doesn't take an `IntervalIntegrable` premise)
            -- sprint 006's annulus-side integrability
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            -- The new per-`k` termwise kernel inequality
            (∑' k : ℕ,
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k *
                  c ^ (2 * k + 2) / (k + 1)
              else 0) ≤
              ∫ ρ' in ρ₁..ρ₂,
                2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                  / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

The proof body:

1. **Unpack** the witness existential to obtain `ρ₁, ρ₂` and the
   premise bundle `(hρ₁_gt_c, hρ₁_le_ρ₂, hρ₂_lt_one, hSummable_int_norm,
   hSummable_n2_at_ρ₂, hIntCircleAnnulus, hIntZOverLambda, hKernel)`.
2. **Disk-side bound** via sprint 044
   (`diskExcess_upper_bound_via_tsum_partition_drop_N2`) at
   `(a, b, c)` with `hc_pos.le` and `hSummable_int_norm`:

   ```text
   diskExcess (circleGap a b) c ≤ Σ⁺_int(c)
   ```

3. **Annulus-side bound** via sprint 006
   (`annulusExcess_lower_bound_of_eq8_eq9`) at
   `(paper, ρ₁, ρ₂)` with `hρ₁_gt_c`, `hρ₁_le_ρ₂`, `hρ₂_lt_one`,
   `hSummable_n2_at_ρ₂`, `hIntCircleAnnulus`, `hIntZOverLambda`:

   ```text
   ∫_{ρ₁..ρ₂} 2ρ'³·Z_{ρ'}/Λ(c, ρ') dρ' ≤ annulusExcess (circleGap a b) c
   ```

4. **Chain via the kernel inequality `hKernel`**:

   ```text
   diskExcess ≤ Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ'³·Z_{ρ'}/Λ ≤ annulusExcess
   ```

5. **Discharge `ValidKorenblumBound c`** via the existing
   `valid_of_disk_le_annulus` lemma (or the equivalent contract
   discharger that takes `diskExcess ≤ annulusExcess` plus the
   `(c, K)` premises and produces `ValidKorenblumBound c` — sprint
   035's body uses this exact pattern).

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 045 ships:

1. **First workspace `valid_of_*` closing reducer with paper-axiom
   signature `{eq8, eq9}` AND zero oracle cells.** The current state of
   the workspace's closing-reducer matrix (paper-axiom signature ×
   oracle cell count):

   | Sprint | Paper-axiom signature | Oracle cells | Disk-side RHS shape |
   |--------|-----------------------|--------------|---------------------|
   | seed (V0) | `{eq15}` (via `valid_of_eq15`) | none | scalar criterion |
   | 014 | `{eq3, eq4, eq8, eq9}` | none | `c⁴` (Z-anchored at c) |
   | 017 | `{eq6, eq8, eq9}` | none | `c⁴/2` |
   | 023 | `{eq2, eq3, eq4, eq8, eq9}` | none | `c⁴/2` (branch-2) |
   | 024 | `{eq2, eq3, eq4, eq8, eq9}` | none | `c⁴/2` (branch-2, single Summable) |
   | 035 | `{eq8, eq9}` | `{hSigmaCmp}` | `c⁴ · Z_c` |
   | 039 | `{}` | `{hSigmaCmp, hLambdaBridgeWindow}` | `c⁴ · Z_c` |
   | **045 (NEW)** | **`{eq8, eq9}`** | **none** | **`Σ⁺_int(c) := ∑' k ∈ N1, coeffPlusGap_k · c^(2k+2)/(k+1)`** |

   Sprint 045 is the **first** closing reducer to combine a strict-
   subset paper-axiom signature `{eq8, eq9}` with **zero** oracle
   cells. Sprint 035 reaches the same paper-axiom signature but
   requires the `hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)` oracle cell. Sprint 039
   eliminates the paper-axiom signature entirely but at the cost of
   *two* oracle cells (`hSigmaCmp` and `hLambdaBridgeWindow`). Sprint
   045 trades sprint 035's oracle cell for the (still small)
   `{eq8, eq9}` paper signature, AND eliminates the oracle cell —
   producing a strictly cleaner trust-base footprint than either
   sprint 035 or any prior reducer except sprint 039 (which trades
   it for two oracle cells).

2. **First workspace closing reducer with a per-`k` termwise series
   kernel.** Every prior closing reducer's kernel inequality is a
   single function-level scalar inequality:

   | Reducer | Kernel inequality LHS |
   |---------|----------------------|
   | 014 | `c⁴` |
   | 017 | `c⁴/2` |
   | 023, 024 | `c⁴/2` |
   | 035 | `c⁴ · Z_c` |
   | 039 | `c⁴ · Z_c` |
   | **045 (NEW)** | **`Σ⁺_int(c) := ∑' k ∈ N1, coeffPlusGap_k · c^(2k+2)/(k+1)`** |

   Sprint 045's kernel `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`
   is **structurally distinct** from every prior kernel: its LHS is
   a `tsum` over N1 with explicit per-`k` weights `c^(2k+2)/(k+1)`,
   not a single closed-form scalar. This unlocks **partial-sum
   truncation analysis on the disk-side LHS**, **per-`k` numerical
   witnesses**, and **per-`k` comparison against an eventual
   termwise annulus-side expansion** (a future sprint), all of which
   are inaccessible from any prior closing reducer's bulk scalar
   kernel.

3. **First downstream materialisation of sprint 044 in a closing-
   reducer chain.** Sprint 044 ships the paper-axiom-free, oracle-
   cell-free disk-side bound `diskExcess ≤ Σ⁺_int(c)` but no closing
   reducer consumes it yet. Sprint 045 is the natural first
   downstream consumer: compose sprint 044 (disk side) with sprint
   006 (annulus side) and connect via a kernel inequality lifted
   into the witness existential. The composition pattern is
   structurally parallel to sprint 035's relationship with sprint
   034 (sprint 035 lifts sprint 034's `hSigmaCmp` cell into the
   witness; sprint 045 needs no analogous lift since sprint 044 has
   no oracle cell).

4. **Strict structural upgrade over sprint 035.** Sprint 035's
   reducer requires the `hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)` cell — a bulk
   N1/N2-aggregate comparison that sprint 044's contract identifies
   as **the cleanest possible precise oracle target for a future
   trust-base expansion**. Sprint 045 eliminates this cell entirely:
   the disk side is bounded by `Σ⁺_int(c)` (a per-`k` series, no
   bulk comparison needed), and the kernel inequality
   `Σ⁺_int(c) ≤ ∫ ...` lives at the per-`k` × integrated layer
   where no `Σ⁺(c) ≤ Σ⁻(c)` comparison is required. The
   structurally critical observation is that sprint 044's RHS
   `Σ⁺_int(c)` does **not** require any `Σ⁻` comparison to derive —
   the N2 piece is dropped via *termwise* sign structure
   (`coeffMinusGap_k ≥ 0` on N2, which is built into N2's
   definition), not via a *bulk* `Σ⁺(c) ≤ Σ⁻(c)` inequality.

   This is sprint 044's contract's promised "Foundation for an
   `{eq8, eq9}`-only closing reducer" — sprint 045 is that closing
   reducer.

5. **Prerequisite for the eventual oracle-backed `c_value` push
   along the per-`k` axis.** Once sprint 045 is in place, a future
   numerical sprint can:
   - Pick a `c > 0.3554` (e.g., `c = 0.36` or `c = 0.4`),
   - Pick a window `[ρ₁, ρ₂] ⊂ (c, 1)` on which Wang's `(15)`
     equation can be replaced by the new kernel
     `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ`,
   - Discharge the per-`k` kernel via partial-sum truncation
     (compute the first few `k`-terms of `Σ⁺_int(c)` exactly,
     bound the tail via geometric/dominated convergence, and
     compare against the closed-form `∫ 2ρ³ · sigmaZeroMinus(ρ) /
     Λ(c, ρ) dρ` — itself a finite-dimensional integral over `ρ`).

   The per-`k` partial-sum mechanism is **strictly more flexible**
   than every prior kernel inequality in the workspace: at the
   bulk-scalar level (sprints 014/017/023/024/035/039), the entire
   disk-side LHS must be discharged as a single number; at the
   per-`k` level (sprint 045), each `k` can be discharged
   independently with its own optimization. This is the bulletin's
   "design a strictly stronger sufficient condition than the seed's
   `(15)`" axis materialised at the closing-reducer layer.

6. **First closing reducer where the disk-side body is BOTH paper-
   axiom-free AND oracle-cell-free.** Sprint 035's disk-side body
   uses sprint 034 modulo `hSigmaCmp`. Sprint 039's disk-side body
   uses sprint 034 modulo `hSigmaCmp` (lifted to the existential).
   Sprint 045's disk-side body uses sprint 044 with no cell of any
   kind — neither paper axiom nor oracle. The transitive paper-axiom
   trace of sprint 045's *disk side* is **empty**; the only paper
   axioms invoked anywhere in sprint 045's transitive proof body
   come from sprint 006's annulus side (`{eq8, eq9}`).

7. **Foundation for a brand-new analytical axis: per-`k` numerical
   sufficient conditions.** The bulletin solicits "design a strictly
   stronger sufficient condition than the seed's `(15)`". Sprint
   045's per-`k` kernel `Σ⁺_int(c) ≤ ∫ ...` is the **first closing-
   reducer-level expression** of a sufficient condition that
   permits per-`k` analysis. Future sprints can:
   - Truncate `Σ⁺_int(c)` to the first `K` terms and bound the tail
     via dominated convergence,
   - Compute each finite `k`-term `coeffPlusGap_k · c^(2k+2)/(k+1)`
     symbolically/numerically,
   - Verify the per-`k` inequality against the closed-form annulus
     integral via SymPy or numerical integration,
   - Replace the bulk kernel inequality with a per-`k` cascade.

   This was unreachable from every prior reducer's bulk-scalar
   kernel.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V45 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is a new closing-reducer layer (paper-axiom
  signature `{eq8, eq9}` + zero oracle cells + per-`k` termwise
  kernel), not a numerical refinement of an existing closed-form
  coefficient.
* The witness existential includes the new per-`k` kernel
  inequality as a hypothesis; the V45 side lemma `_witness_at_seed`
  exhibits a *degenerate* witness (e.g., `(ρ₁, ρ₂) = (1/2, 1/2)`
  with the per-`k` kernel discharged trivially via the eventual
  bulk equivalence). The eventual non-degenerate numerical witness
  is a *consumer* of sprint 045 and is queueable separately.

Why this is **not** "the same chain" as sprint 035:

* **Disk-side body.** Sprint 035's disk-side body uses sprint 034
  (paper-axiom-free `diskExcess ≤ c⁴·Z_c modulo Σ⁺(c) ≤ Σ⁻(c)`).
  Sprint 045's disk-side body uses sprint 044 (paper-axiom-free,
  oracle-cell-free `diskExcess ≤ Σ⁺_int(c)`). Different lemma,
  different RHS shape, different cell list.
* **Witness existential cell list.** Sprint 035's witness includes
  `hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)`. Sprint 045's witness contains
  **no** `Σ⁺` vs `Σ⁻` comparison cell — instead it contains the
  per-`k` kernel inequality `Σ⁺_int(c) ≤ ∫ ...`. Disjoint cell
  shapes.
* **Kernel LHS shape.** Sprint 035's kernel LHS is `c⁴ · Z_c` (a
  closed-form scalar). Sprint 045's kernel LHS is `Σ⁺_int(c)` (a
  per-`k` series). Disjoint LHS shapes.

Why this is **not** "the same chain" as sprint 014/017/023/024:

* **Paper-axiom signature.** Sprints 014/017/023/024 require
  `{eq3, eq4}` or `{eq2, eq3, eq4}` or `{eq6}` on the disk side
  (in addition to `{eq8, eq9}` on the annulus side). Sprint 045
  requires **no paper axioms on the disk side** (sprint 044 is
  paper-axiom-free). Strict subset.
* **Disk-side bound shape.** Sprints 014/017/023/024 use scalar
  closed-form bounds (`c⁴`, `c⁴/2`). Sprint 045 uses a per-`k`
  series bound (`Σ⁺_int(c)`). Disjoint shapes.

Why this is **not** "the same chain" as sprint 039:

* **Paper-axiom signature trade-off.** Sprint 039 has empty paper-
  axiom signature but requires two oracle cells (`hSigmaCmp` and
  `hLambdaBridgeWindow`). Sprint 045 has paper-axiom signature
  `{eq8, eq9}` but **zero** oracle cells. Different trust-base
  trade-off.
* **Disk-side body.** Sprint 039 uses sprint 034 (modulo
  `hSigmaCmp`). Sprint 045 uses sprint 044 (no cell). Different
  source lemma.
* **Kernel LHS shape.** Sprint 039's kernel LHS is `c⁴ · Z_c`.
  Sprint 045's kernel LHS is `Σ⁺_int(c)`. Disjoint shapes.

Why this is **bounded enough for one Generator session**:

* The proof body is the **composition of two existing workspace
  reducers** (sprint 044 disk side + sprint 006 annulus side) plus
  a single `linarith` chain through the kernel inequality and the
  contract discharger.
* Sprint 044's invocation is one line.
* Sprint 006's invocation is one line.
* The kernel chain `diskExcess ≤ Σ⁺_int ≤ ∫ ... ≤ annulusExcess`
  closes via two `le_trans` invocations or one `linarith`.
* The contract discharger (`valid_of_disk_le_annulus` or its
  equivalent) is the same one sprint 035's body uses; sprint 045's
  contract closing follows sprint 035's pattern verbatim.
* The witness existential unpacking is a routine `obtain` pattern;
  sprint 035's body contains the template.
* No new Mathlib lemmas are needed.
* Estimated body length: **~50–80 lines** (sprint 035's body is
  ~80 lines; sprint 045's body is sprint 035's body with the
  disk-side `hSigmaCmp` cell deleted and sprint 044 substituted
  for sprint 034).

Why this is **bounded enough on Mathlib lemma archaeology risk**:

* Zero new Mathlib lemmas. All ingredients (sprint 044, sprint
  006, `le_trans`, `linarith`, the contract discharger) are
  already consumed by prior sprints.
* The witness existential's premise count is similar to sprint
  035's (six cells vs sprint 035's seven; one cell removed —
  `hSigmaCmp`). No structural complexity escalation.

Why this is **bounded enough on witness construction**:

* The V45 `_witness_at_seed` side lemma exhibits a degenerate
  single-point window `(ρ₁, ρ₂) = (1/2, 1/2)` (mirroring sprints
  023/024/035/039's witness pattern). At a degenerate window, the
  kernel inequality `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} ...` reduces to
  `Σ⁺_int(c) ≤ 0` which **does not hold in general**. The witness
  thus needs a non-degenerate window, OR the side lemma can stop
  at a tautological compilation check that exhibits the witness
  existential **without** discharging the kernel inequality cell
  (which is the structurally novel new cell), packaging the kernel
  inequality as a `sorry`-free hypothesis.

  **Recommended pattern (mirroring sprint 035 + sprint 039 +
  sprint 044):** the V45 `_witness_at_seed` side lemma takes a
  `Section2Assumptions` instance and produces the witness
  existential with the kernel inequality discharged at a non-
  degenerate window. The non-degenerate witness can be at the
  same window sprint 014's `Candidates/V14.lean` uses (e.g.,
  `(0.5, 0.7)`) since that's already known to discharge the
  sprint 014 kernel `c⁴ ≤ ∫_{0.5..0.7} 2ρ³/Λ(c, ρ) dρ` and the
  new kernel `Σ⁺_int(c) ≤ ∫ ...` is **comparable in magnitude
  to `c⁴`** for typical `(a, b)` data (with the per-`k`
  decomposition giving slack via the `1/(k+1)` integration
  weights). For the V0 seed `(a, b)` data, both kernels are
  ultimately bounded by the same `(15)` equation, so a
  non-degenerate witness should exist; if the degenerate
  witness is needed, the kernel cell can be discharged by
  composing sprint 014's witness with the sprint 044 vs
  sprint 014 kernel comparison — or, simpler, the V45
  `_witness_at_seed` side lemma may stop at the existential
  with the kernel cell as an explicit assumption (mirroring
  sprint 039's relationship to its `_witness_at_seed`).

  **Acceptable simplification:** the V45 `_witness_at_seed` side
  lemma may take the kernel inequality `Σ⁺_int(c) ≤ ∫ ...` as
  an explicit hypothesis (just like sprint 035 takes `hSigmaCmp`
  as a hypothesis). The structural point of V45 is the closing
  reducer, not the witness — the kernel inequality is the new
  per-`k` analytical axis that future sprints will discharge
  numerically.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic closing-reducer theorem
  `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
  after sprint 044's `diskExcess_upper_bound_via_tsum_partition_drop_N2`
  (current end of `Reduction.lean`, after sprint 044's body).

  Estimated body length: ~50–80 lines.

  The proof body structure (high-level):

  1. **Open the `Section2Assumptions` instance and unpack the
     witness existential:**
     ```lean
     intro a b K paper
     obtain ⟨ρ₁, ρ₂, hρ₁_gt_c, hρ₁_le_ρ₂, hρ₂_lt_one,
             hSummable_int_norm, hSummable_n2_at_ρ₂,
             hIntCircleAnnulus, hIntZOverLambda, hKernel⟩ :=
       h_witness paper
     ```

  2. **Apply sprint 044 for the disk-side bound:**
     ```lean
     have hDisk :
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
           ∑' k : ℕ,
             if PaperAxioms.n1Pred a b k then
               PaperAxioms.coeffPlusGap a b k *
                 c ^ (2 * k + 2) / (k + 1)
             else 0 :=
       diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
         hc_pos.le hSummable_int_norm
     ```

  3. **Apply sprint 006 for the annulus-side bound:**
     ```lean
     have hAnnulus :
         (∫ ρ' in ρ₁..ρ₂,
             2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
               / WangOuter.paperLambda K c ρ') ≤
           PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c :=
       annulusExcess_lower_bound_of_eq8_eq9 paper
         hρ₁_gt_c hρ₁_le_ρ₂ hρ₂_lt_one hSummable_n2_at_ρ₂
         hIntCircleAnnulus hIntZOverLambda
     ```
     (Exact lemma name and argument order to be verified against
     the sprint 006 lemma's signature in `Reduction.lean`. Sprint
     035's body line ~XYZ and sprint 023's body line ~XYZ both
     invoke this lemma; copy the invocation pattern verbatim.)

  4. **Chain the disk × kernel × annulus inequalities:**
     ```lean
     have hDiskLeAnnulus :
         PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
           PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c :=
       le_trans hDisk (le_trans hKernel hAnnulus)
     ```

  5. **Discharge `ValidKorenblumBound c` via the contract
     discharger:**
     ```lean
     exact valid_of_disk_le_annulus hc_pos hc_lt_one hDiskLeAnnulus
     ```
     (Replace `valid_of_disk_le_annulus` with the actual contract
     discharger name used by sprint 035's body. The discharger
     takes `hc_pos`, `hc_lt_one`, and the `diskExcess ≤
     annulusExcess` inequality and produces the `ValidKorenblumBound c`
     conclusion.)

- `ProofRefinement/Korenblum/Candidates/V45.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V44),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V44),
  4. Adds two side lemmas exercising the new closing reducer:
     - `v45_valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window_compiles` —
       takes `hc_pos`, `hc_lt_one`, and a universally-quantified
       `h_witness` cell at `c = c_value`; applies the new theorem;
       conclusion is `ValidKorenblumBound c_value`. Does **not**
       discharge the witness existential — leaves it as a
       universally-quantified hypothesis (the structural point of
       this side lemma is that the new closing reducer compiles
       and discharges the contract from a witness existential).
     - `v45_valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window_witness_at_seed` —
       constructs a concrete witness at `c = c_value` for some
       `(a, b, K, paper)`. The witness uses degenerate window
       `(ρ₁, ρ₂) = (1/2, 1/2)` (matching sprints 023/024/035/039's
       degenerate witness pattern). The kernel inequality cell
       `Σ⁺_int(c_value) ≤ ∫_{1/2..1/2} ...` is discharged via the
       degenerate-window observation that both sides equal `0` (LHS
       requires the degenerate-window constraint to force
       `Σ⁺_int(c) ≤ 0`; ACCEPTABLE SIMPLIFICATION: the side lemma
       may take the kernel inequality as an explicit hypothesis on
       the side lemma's signature, mirroring sprint 035's pattern
       — the structural point is that the witness existential
       compiles, not that every cell is discharged inline). The
       summability cells are discharged via the V0 seed's standard
       pattern (which is paper-axiom-free); the integrability cells
       are discharged via the standard `IntervalIntegrable.const_mul`
       + `IntervalIntegrable.continuousOn_mul` pattern used by
       sprint 014's `Candidates/V14.lean` witness.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V44) — the new closing
     reducer is materialised in side lemmas, **not** as the sink
     theorem's discharge route.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V45` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V45.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V45 ties V44 at
   the seed; the new closing reducer is structural and does not
   change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V45.hEq15_seed_3554}`. No
   new free-floating axioms, no oracle entries.
5. The new theorem
   `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and
   is exercised in `Candidates/V45.lean`'s two side lemmas.
6. The proof body of the new theorem invokes
   `diskExcess_upper_bound_via_tsum_partition_drop_N2` (sprint 044)
   exactly once. Greppable check: count of
   `diskExcess_upper_bound_via_tsum_partition_drop_N2` in the body
   of the new theorem is **= 1**.
7. The proof body of the new theorem invokes
   `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006) exactly
   once. Greppable check: count of
   `annulusExcess_lower_bound_of_eq8_eq9` in the body of the new
   theorem is **= 1**.
8. The proof body of the new theorem **does not invoke** any of
   the sprints 003 / 013 / 022 / 026 / 030 / 031 / 034 / 040
   `diskExcess_upper_bound_*` lemmas. Sprint 045's disk side is
   sprint 044 only. Greppable check: in the new theorem body,
   counts of `diskExcess_upper_bound_via_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_via_circleGapSeries_eq4_only`,
   `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`,
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse`,
   `diskExcess_upper_bound_via_eq6`,
   `diskExcess_upper_bound_via_series_eq4_only_two_Z`,
   `diskExcess_upper_bound_collapsed_single_Z_via_series_eq4_only`,
   `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
   are all **0**.
9. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection on the disk side. Sprint 045's
   disk-side body is sprint 044, which is paper-axiom-free.
   Greppable check: in the *first half* of the new theorem body
   (before the `annulusExcess_lower_bound_of_eq8_eq9` invocation),
   the count of `paper.eq` substrings is **0**.
10. The new theorem's witness existential **does not contain** a
    `Σ⁺ ≤ Σ⁻` comparison cell. Greppable check: in the new
    theorem's signature, the substring
    `PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c`
    does **not** appear. Sprint 045's witness existential is
    *strictly disjoint* from sprint 035's `hSigmaCmp` cell shape.
11. The new theorem's witness existential **contains** the per-
    `k` kernel inequality `Σ⁺_int(c) ≤ ∫ ...`. Greppable check:
    in the new theorem's signature, the substring
    `if PaperAxioms.n1Pred a b k then` appears at least once
    (witnessing the per-`k` kernel LHS).
12. The new theorem's signature contains exactly **6 witness
    existential cells** (counting each `∧` separator and the
    final cell): `hρ₁_gt_c`, `hρ₁_le_ρ₂`, `hρ₂_lt_one`,
    `hSummable_int_norm`, `hSummable_n2_at_ρ₂`,
    `hIntCircleAnnulus`, `hIntZOverLambda`, `hKernel`. Greppable
    check: count of `∧` in the witness existential block is
    **= 7** (six `∧`s separating eight cells; sprint 035 has
    seven `∧`s for nine cells, so sprint 045 has one fewer than
    sprint 035, reflecting the elimination of `hSigmaCmp`).
13. The V45 `_compiles` side lemma's conclusion is
    `ValidKorenblumBound c_value`, derived by invoking the new
    closing reducer at the seed.
14. The V45 `_witness_at_seed` side lemma constructs a concrete
    witness existential at the seed. The window `(ρ₁, ρ₂)` is
    either (a) degenerate single-point `(1/2, 1/2)` mirroring
    sprints 023/024/035/039, or (b) non-degenerate (e.g.,
    `(0.5, 0.7)` mirroring sprint 014). Either is acceptable.
    The kernel inequality cell may be discharged inline OR taken
    as an explicit hypothesis on the side lemma signature
    (acceptable simplification per sprint 035's witness pattern).
15. The new theorem **does not invoke** `paperLambda` directly —
    it appears only inside the integrand of the integral cells
    inherited from sprint 006. Greppable check: in the new
    theorem body, every `paperLambda` substring is inside the
    `∫ ... paperLambda K c ρ' ...` shape, never as a standalone
    invocation.
16. The new theorem **does not invoke** sprint 034's
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare` —
    sprint 045 is built on sprint 044 (no `hSigmaCmp` cell) only.
    Greppable check: count of
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    in the body is **0**.

## Out of scope

- Edit older candidates V0–V44.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V45 is
  the same `hEq15_seed_3554` that V0–V44 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Discharge the per-`k` kernel inequality
  `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ` numerically at any
  `c > 0.3554`. Sprint 045 ships only the closing reducer and
  exposes the kernel inequality as a hypothesis. The numerical
  discharge of the kernel at a larger `c` is a *consumer* of
  sprint 045 + future per-`k` analytical infrastructure, queueable
  separately.
- Ship a parallel termwise upper bound on the N1 piece (i.e.,
  drop the `coeffPlusGap_k ≤ 0` summands at `k = 0` if
  `coeffPlusGap_0 < 0`). This is sprint 044's "out of scope"
  inheritance; queueable separately.
- Ship the analogous closing reducer with sprint 040's `c²·Σ⁺(c)`
  disk bound instead of sprint 044's `Σ⁺_int(c)`. That is a
  parallel closing reducer with a different (function-level)
  disk-side RHS; queueable separately.
- Ship the analogous closing reducer with sprint 038's
  `hLambdaBridgeWindow`-modulo annulus side bound (sprint 037/038)
  to produce a closing reducer with paper-axiom signature `{}`
  and one oracle cell `{hLambdaBridgeWindow}`. That would be a
  hybrid of sprint 045 and sprint 039's annulus side; queueable
  separately if the analytical novelty per session is high enough.
- Ship a witness at any `c > 0.3554`. Sprint 045 does not raise
  `c_value`. The eventual numerical push is a *consumer* of
  sprint 045 + future per-`k` analytical infrastructure, not
  sprint 045 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15`
  to the new closing reducer. The new closing reducer is
  materialised in side lemmas only; the sink theorem still uses
  `valid_of_eq15` to keep V45's score equal to V44's `1777/5000`.
- Ship the disk-side analogue of sprint 044's bound at
  `coeffPlusGap_k ≤ 0` indices (i.e., the N1 indices where
  `‖a k‖ < ‖b k‖` and thus `coeffPlusGap_k = ‖a k‖² − ‖b k‖² < 0`).
  This would be a strict refinement of sprint 044 by dropping
  more terms, but is structurally a separate sprint.
- Ship the analogous N1/N2 partition for the *annulus side* via
  sprint 042-style swap-of-sum-and-integral. This is the sprint
  044 → sprint 045's analogue on the annulus side and would
  unlock per-`k` × per-`k` comparison kernels (sprint 044's
  per-`k` disk LHS vs an as-yet-unwritten per-`k` annulus RHS).
  Queueable separately as the next analytical sprint after 045.

## Time budget

≤ 60 minutes runtime. (Sprint 045's body is the **shortest closing-
reducer sprint since at least sprint 035**: it composes two
existing lemmas (sprint 044, one line; sprint 006, one line) +
two `le_trans` chains + the contract discharger (one line) +
witness existential unpacking (~10 lines). Estimated body:
~50–80 lines. The two V45 side lemmas reuse sprint 035's
`_compiles` and `_witness_at_seed` patterns, ~30–60 lines each.
Total V45 size: ≤ 200 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* **Sprint 035 is the canonical reference for sprint 045's body
  structure.** Open `Reduction.lean`, find sprint 035's body
  (`valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window`),
  copy verbatim, then:
  - Replace the disk-side
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    invocation with
    `diskExcess_upper_bound_via_tsum_partition_drop_N2`.
  - Delete the `hSigmaCmp` cell from the witness existential
    signature and from the body's `obtain` pattern (sprint 044
    takes no `hSigmaCmp` argument).
  - Replace the disk-side `hSummable_at_c_n1` cell (sprint 034's
    pointwise N1 summability at `c`) with sprint 044's
    `hSummable_int_norm` cell (integrated absolute-value
    summability with the `c^(2k+2)/(k+1)` weight).
  - Update the kernel inequality `hKernel`'s LHS from
    `c^4 * sigmaZeroMinus a b c` to
    `∑' k : ℕ, if n1Pred a b k then coeffPlusGap_k · c^(2k+2)/(k+1) else 0`.
  - Keep the rest of the body verbatim from sprint 035 (annulus
    side, kernel chain, contract discharger).

* **The contract discharger that sprint 035 uses** — verify the
  exact name. It might be `valid_of_disk_le_annulus`, or it might
  be inlined as the body of `ValidKorenblumBound`'s definition.
  Sprint 035's body's last lines are the canonical reference.

* **Sprint 006's invocation argument order** — verify against
  sprint 035's body. The arguments are typically:
  `(paper, hρ₁_gt_c, hρ₁_le_ρ₂, hρ₂_lt_one, hSummable_n2_at_ρ₂,
   hIntCircleAnnulus, hIntZOverLambda)`. The sprint 023's body
  also uses this pattern (sprint 023's `hAnnulus` invocation).

* **Sprint 044's invocation argument order:**
  ```
  diskExcess_upper_bound_via_tsum_partition_drop_N2 (a := a) (b := b)
    hc_pos.le hSummable_int_norm
  ```
  Sprint 044 takes only `(a, b, c)`-implicit-or-explicit, `hc_nonneg`,
  and `hSummable_int_norm`. No `paper`, no `K`, no `Section2Assumptions`.

* **The `_witness_at_seed` side lemma** — the simplest acceptable
  form is to take the kernel inequality as an explicit hypothesis
  on the side lemma signature, mirroring sprint 035's
  `_witness_at_seed` shape. This avoids needing to discharge the
  per-`k` kernel `Σ⁺_int(c_value) ≤ ∫_{1/2..1/2} ...` inline (which
  at a degenerate window reduces to `Σ⁺_int(c_value) ≤ 0`, false in
  general). The structural point of `_witness_at_seed` is that the
  closing reducer composes correctly with a witness existential,
  not that the witness is fully discharged.

* **Edge case: degenerate window `(ρ₁, ρ₂) = (1/2, 1/2)`** — at a
  degenerate single-point window, `∫_{1/2..1/2} ... dρ' = 0`. The
  kernel inequality `Σ⁺_int(c) ≤ 0` requires either (a) a
  separate analytical argument that `Σ⁺_int(c) ≤ 0` for the V0
  seed `(a, b)` (false in general for arbitrary `(a, b)`), or
  (b) accepting the kernel as an explicit hypothesis on the side
  lemma. Recommended: option (b), per sprint 035's pattern.

* **Non-degenerate window option:** if the Generator wishes to
  exhibit a non-degenerate witness, the window `(0.5, 0.7)` from
  sprint 014's `Candidates/V14.lean` is a known-good window.
  However, the kernel inequality `Σ⁺_int(c) ≤ ∫_{0.5..0.7}
  2ρ³·Z_ρ/Λ(c, ρ) dρ` requires showing that the new per-`k`
  integrated `Σ⁺_int(c)` is **bounded above by** the same kernel
  RHS that sprint 014 uses. This is a non-trivial numerical
  comparison — out of scope per the contract; the side lemma
  should take the kernel as an explicit hypothesis instead.

* **Witness summability cells** — for the V0 seed `(a, b)`
  (which uses one-mode functions from `OneModePaperBridge`), the
  summability cells `hSummable_int_norm` and `hSummable_n2_at_ρ₂`
  are dischargeable from the seed's series structure. Sprint 044's
  V44 file should have a similar discharge pattern for
  `hSummable_int_norm`; copy the pattern verbatim. For
  `hSummable_n2_at_ρ₂`, copy the pattern from sprint 035's V35
  witness (which discharges the analogous `hSummable_at_c_n1`
  cell at `c` instead of `ρ₂`).
