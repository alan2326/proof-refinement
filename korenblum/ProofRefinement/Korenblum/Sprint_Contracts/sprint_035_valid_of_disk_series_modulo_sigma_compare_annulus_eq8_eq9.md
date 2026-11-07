# Sprint 035: End-to-end full-window closing reducer fusing sprint 034's paper-axiom-free disk bound (modulo `Σ⁺(c) ≤ Σ⁻(c)`) with sprint 006's `(8)+(9)` annulus bound — the workspace's **first `valid_of_*` reducer whose disk-side proof body invokes zero `paper.eq*` field projections**, the **first reducer to lift the unique series-non-derivable conjunct `Σ⁺(c) ≤ Σ⁻(c)` into the witness existential as a type-level cell**, and the **structural prerequisite (and only prerequisite) for a future oracle on `Σ⁺(c) ≤ Σ⁻(c)` to immediately discharge a paper-axiom-free, full-window `ValidKorenblumBound` route**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V34.lean`
**Target file**: `Candidates/V35.lean`
**Direction**: section2-proof

## Goal

Ship one new generic closing-reducer theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
              Summable (fun k : ℕ =>
                PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
              else 0) ∧
            (PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' ^ 3
                / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n2Pred a b k then
                PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
              else 0) ∧
            c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                      2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
    ValidKorenblumBound c
```

This is **sprint 014's `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`
body verbatim**, with one targeted disk-side substitution: the call to
`diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one hIntDisk`
(sprint 013, paper-axiom signature `{eq3, eq4}`) is replaced by a call
to `diskExcess_upper_bound_via_series_only_modulo_sigma_compare
hc_pos hc_lt_one hSummable hSummable_n1_c hSigmaCmp hIntDisk` (sprint
034, paper-axiom-free body modulo explicit `hSigmaCmp`). The witness
existential is correspondingly extended: sprint 014's 8-cell witness
becomes a 12-cell witness with three new disk-side cells (`hSummable`,
`hSummable_n1_c`, `hSigmaCmp`) inserted before `hIntDisk`.

The closed-form kernel inequality is **byte-for-byte identical** to
sprint 014's `c^4 ≤ ∫ ρ' in ρ₁..ρ₂, 2·ρ'^3 / paperLambda K c ρ'` — same
coefficient `c^4`, same integrand, same admissible window
`[ρ₁, ρ₂] ⊂ (c, 1)` (no `branchSplit c` confinement). What changes is
**the type-level provenance of the disk-side bound**: sprint 014's body
delegates the disk-side chain `diskExcess ≤ c^4·Z_c` to sprint 013
(which transitively invokes `paper.eq3` and `paper.eq4`); sprint 035's
body delegates the same chain to sprint 034 (whose body is
paper-axiom-free, with the unique series-non-derivable conjunct
`Σ⁺(c) ≤ Σ⁻(c)` lifted into the type signature as `hSigmaCmp`).

The annulus side is **identical** to sprint 014: sprint 006's
`annulusExcess_lower_bound_of_eq8_eq9` (paper-axiom signature
`{eq8, eq9}`), sprint 011/012's `Z_c → Z_{ρ'}` cascade, and the same
`paperLambda` denominator structure. We are not eliminating annulus-side
paper axioms in this sprint; that is a separate analytical surface (the
`liftGap`/`paperLambda` representation of `eq8`/`eq9` resists series
decomposition).

Then ship a `Candidates/V35.lean` at the same `c = 0.3554` that
compiles, scores `≥ V34 = 1777/5000`, and **materialises** the new
reducer in side lemmas
`v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_compiles`
and
`v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_witness_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_witness_at_seed` side lemma demonstrates that the new reducer's
`hSigmaCmp` cell can be discharged from `paper.eq4_sigmaPlus_bound`'s
second conjunct at the seed (the same discharge route exhibited in
V34's `_recovers_via_eq4_at_seed` side lemma). This is the structural
marker that the new reducer is a strict generalisation of sprint 014:
**any consumer with `paper.eq4` access can recover sprint 014's
end-to-end conclusion through the new chain**, while a future consumer
with an oracle on `Σ⁺(c) ≤ Σ⁻(c)` would discharge the same reducer
**without ever invoking `paper.eq4` (or any `paper.eq*` projection on
the disk side)**. The annulus side still uses `paper.eq8`/`paper.eq9`
unchanged.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 035 ships:

1. **The workspace's first `valid_of_*` reducer with paper-axiom-free
   disk-side body.** Every prior `valid_of_*` reducer in
   `Reduction.lean` invokes at least one disk-side `paper.eq{2..6}`
   field projection in its transitive proof body:

   | Sprint | Reducer | Disk-side `paper.eq*` |
   |--------|---------|------------------------|
   | seed   | `valid_of_eq15` | `eq14_combined`, `eq15`-bridge |
   | 001    | `valid_of_eq12_eq13` | `eq12`, `eq13`, `eq14_combined` |
   | 004    | `valid_of_eq2_eq3_eq4_annulus_budget` | `eq2`, `eq3`, `eq4` |
   | 008    | `valid_of_eq10_subinterval_branch1` | `eq10` |
   | 014    | `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` | `eq3`, `eq4` |
   | 017    | `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` | `eq6` |
   | 018    | `valid_of_eq11_subinterval_branch2` | `eq11` |
   | 019    | `valid_of_eq5_eq8_eq9_subinterval_branch1` | `eq5` |
   | 020    | `valid_of_eq10_eq11_straddling_window` | `eq10`, `eq11` |
   | 021    | `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` | `eq5` |
   | 023    | `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window` | `eq2`, `eq3`, `eq4` |
   | 024    | `... _branch2_window_uniformSummable` | `eq2`, `eq3`, `eq4` |
   | **NEW: 035** | `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window` | **`{}` modulo explicit `hSigmaCmp`** |

   Sprint 035 is the **first to break this chain** on the disk side:
   the disk-side proof body (sprint 034's body) invokes zero
   `paper.eq*` projections, with the unique non-series-derivable
   conjunct lifted as the explicit witness-existential cell `hSigmaCmp`.
   The annulus side still uses `paper.eq8`/`paper.eq9` (these are not
   yet series-derivable in the workspace).

2. **The first reducer to lift `Σ⁺(c) ≤ Σ⁻(c)` into the witness
   existential as a type-level cell.** Sprint 034 lifted `hSigmaCmp`
   into the type signature of an *integrated disk bound*; sprint 035
   propagates this lift one level up into the **type signature of a
   `valid_of_*` closing reducer**. This is structurally significant
   because:

   * The witness existential of a `valid_of_*` reducer is the **direct
     surface a candidate `Vk.lean` consumes** to discharge
     `korenblum_constant_search : ValidKorenblumBound c_value`. By
     placing `hSigmaCmp` in the witness existential, sprint 035 makes
     the precise oracle target **visible to the candidate**. A future
     candidate `V_oracle.lean` with a registered `[[oracles]]` entry
     for `Σ⁺(c) ≤ Σ⁻(c)` would discharge sprint 035's reducer with
     `hSigmaCmp := <oracle invocation at c_value>`, **without ever
     invoking `paper.eq4_sigmaPlus_bound`**.

   * No prior `valid_of_*` reducer in the workspace exposes a
     "scalar inequality at a single radius" cell at the witness level
     in this way. Existing closing reducers' witness existentials
     contain summability hypotheses, integrability hypotheses, kernel
     inequalities (integrals), and pointwise bounds (sometimes with
     branch-split confinement) — but they do **not** contain a single
     scalar inequality at a single radius `c` that can be discharged
     by an `O(1)`-information numerical oracle. Sprint 035 is the
     first.

3. **The structural prerequisite (and only prerequisite) for a future
   oracle-backed `c_value` push via the series-derived disk-side
   chain.** Per the bulletin's high-value direction #4 (oracle-backed
   numeric subclaims that support real Lean theorems), the path from
   "sprint 034 ships a paper-axiom-free integrated disk bound" to
   "candidate `Vk.lean` discharges `ValidKorenblumBound c_value` via a
   paper-axiom-free disk-side route at a *larger* `c`" requires
   exactly two structural steps:

   (a) Land sprint 035 (this sprint): a closing reducer whose witness
       existential exposes `hSigmaCmp`, so a candidate can plug in any
       proof of `Σ⁺(c) ≤ Σ⁻(c)` at its chosen `c_value`.

   (b) Future: register a `[[oracles]]` entry for `Σ⁺(c) ≤ Σ⁻(c)` at a
       specific `c_value` (the natural shape: `Numerical_Library`
       function checking a finite truncation of Wang's series for
       `Σ⁺(c) − Σ⁻(c) ≤ 0` with explicit tail-control bound). The
       Lean-facing axiom is then a single scalar inequality at the
       chosen `c_value`, which sprint 035's `hSigmaCmp` cell consumes
       directly.

   Sprint 035 is **(a)**. Without it, the path from sprint 034 to a
   candidate that discharges a paper-axiom-free disk-side route is
   **blocked** because no closing reducer accepts a `hSigmaCmp` cell.
   With sprint 035, the path is unblocked: a future numerical
   oracle proposal would slot directly into the `hSigmaCmp` slot of
   sprint 035's witness existential, with no further structural
   plumbing needed.

4. **First reducer materialising sprint 034 in a closing-reducer
   chain.** Sprint 034 is the **only** integrated disk bound in the
   workspace whose body is paper-axiom-free (modulo `hSigmaCmp`).
   Without a closing-reducer-level downstream consumer, sprint 034 is
   structurally a *standalone disk bound* — useful as a paper-internal
   cross-validation artefact, but not yet wired into the route from
   `paper`/oracle hypotheses to `ValidKorenblumBound c`. Sprint 035 is
   the **first wire-up of sprint 034 into a closing-reducer chain**.

5. **First paper-axiom-disk-empty closing reducer that does not impose
   branch-split confinement on the admissible window.** Sprint 034's
   bound (single-`Z` full-disk, `c^4 · Z_c` form) is valid on the
   *full* disk regime `(0, c)` with no branch-split sub-regime
   constraint, in contrast to sprint 022's `(c⁴/2) · Z_ρ` collapse
   bound which requires `ρ ∈ [branchSplit c, 1)`. Inheriting this
   property, sprint 035's admissible window is `[ρ₁, ρ₂] ⊂ (c, 1)`
   with **no `branchSplit c` constraint** — matching sprint 014's
   admissible window exactly. This is structurally distinct from
   sprint 023/024's branch-2 closing reducers (which impose
   `[branchSplit c, 1)`).

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V35 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new reducer is purely structural: a closing reducer with the
  same closed-form kernel inequality `c^4 ≤ ∫ ρ' in ρ₁..ρ₂,
  2·ρ'^3 / Λ(c, ρ')` as sprint 014, on the same admissible window.

Why this is **not** "the same chain" as sprint 014:

* **Different paper-axiom signature on the disk side.** Sprint 014's
  body invokes `paper.eq3_circleGap_decomposition` and
  `paper.eq4_sigmaPlus_bound` (transitively, through sprint 013).
  Sprint 035's body invokes **zero** `paper.eq*` projections on the
  disk side — sprint 034's body is paper-axiom-free, with `hSigmaCmp`
  lifted to the witness.
* **Different witness existential shape.** Sprint 014's witness has 8
  cells (`ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle,
  hIntLambdaZ, hIntLambda, hSummable_top, hKernel`). Sprint 035's
  witness has 12 cells — the same 8 plus three new disk-side cells
  (`hSummable`, `hSummable_n1_c`, `hSigmaCmp`) inserted before
  `hIntDisk`.
* **Different downstream consumer profile.** Sprint 014 cannot be
  discharged paper-axiom-free even in principle (its body invokes
  `paper.eq3` and `paper.eq4`). Sprint 035 *can* be discharged
  paper-axiom-free if a future oracle on `Σ⁺(c) ≤ Σ⁻(c)` is provided.
  The two reducers are not interchangeable from the consumer side.
* **Different type-level oracle target.** Sprint 014 has no type-level
  oracle target; the precise inequalities its body relies on are
  hidden behind `paper.eq3`/`paper.eq4` field projections, not
  surfaced at the type level. Sprint 035 has a type-level oracle
  target (`hSigmaCmp`), which makes the precise scalar inequality
  needed for paper-axiom-free closure visible to consumers.

Why this is **not** "the same chain" as sprint 034:

* **Sprint 034 is an integrated disk bound** (a `Prop` of the form
  `diskExcess ≤ c^4 · Z_c`); sprint 035 is a **closing reducer** (a
  `Prop` of the form `ValidKorenblumBound c`). The shapes are
  qualitatively different — the former is a *single inequality on
  `diskExcess`*, the latter is *the workspace's contract goal*.
* **Sprint 034 has no annulus side**; sprint 035 fuses sprint 034's
  disk side with sprint 006's annulus side via the sprint 011/012
  `Z_c → Z_{ρ'}` monotonicity cascade. The fusion machinery (sprint
  014's body verbatim modulo the disk-side substitution) is sprint
  035's contribution.
* **Sprint 034 does not unlock anything by itself** — it is a
  structural cross-validation that the integrated disk bound is
  paper-axiom-free modulo a single scalar inequality, but no
  downstream `valid_of_*` consumer exists yet. Sprint 035 is the
  downstream consumer.

Why this is **not** "the same chain" as sprint 023/024:

* **Different admissible window.** Sprints 023/024 require
  `[ρ₁, ρ₂] ⊂ [branchSplit c, 1)` (branch-2 sub-regime). Sprint 035's
  admissible window is `[ρ₁, ρ₂] ⊂ (c, 1)` with no branch-split
  confinement.
* **Different kernel inequality.** Sprints 023/024 have kernel
  `c^4/2 ≤ ∫_{ρ₁..ρ₂} 2·ρ^3 / Λ` (factor of 2 reduction from the
  branch-2 collapse). Sprint 035 has kernel `c^4 ≤ ∫_{ρ₁..ρ₂}
  2·ρ^3 / Λ` (sprint 014's kernel verbatim).
* **Different paper-axiom signature on the disk side.** Sprints
  023/024 use `paper.eq2`/`paper.eq3`/`paper.eq4` (via sprint 022's
  branch-2 collapse). Sprint 035 uses **none** modulo `hSigmaCmp`.

Why this is **bounded enough for one Generator session**:

* The reducer signature is ~30 lines (sprint 014's signature is ~25
  lines; sprint 035 differs by 3 added witness cells `hSummable`,
  `hSummable_n1_c`, `hSigmaCmp` and a 4-line `Summable` predicate
  for `hSummable_n1_c`).
* The proof body is ~120-140 lines — sprint 014's body (~110 lines,
  starting at line 1712) modified with one targeted substitution at
  the `hDisk :=` line (replace sprint 013 invocation with sprint 034
  invocation) and threading the three new witness cells through the
  destructure pattern. The remaining body (geometric scaffolding,
  annulus-side bound via sprint 006, `Z_c → Z_{ρ'}` cascade via
  sprints 011/012, `calc` chain) is byte-for-byte identical to
  sprint 014.
* All Lean idioms used (`refine ⟨...⟩`, `intro a b K paper`,
  `obtain ⟨...⟩ := h_witness paper`, `mul_le_mul_of_nonneg_right`,
  `intervalIntegral.integral_mul_const`, `intervalIntegral.
  integral_mono_on_of_le_Ioo`, `linarith`, `field_simp`, `calc`) are
  verbatim from sprint 014's body. No new idioms required.
* Estimate: ~120-140 lines for the new reducer. Candidate side lemmas
  ~40 lines each. Total V35 size: ≤ 220 lines.

### Note on the choice of `_full_window` over a `_branch1` or
`_branch2` variant

Sprint 035 fuses sprint 034's *full-window* disk bound (no
branch-split confinement) with sprint 006's annulus bound. The natural
admissible window mirrors sprint 014's: `[ρ₁, ρ₂] ⊂ (c, 1)` with no
sub-regime restriction. This is the **maximally general** closing
reducer in the sprint 035 family — strictly more general than any
branch-restricted variant.

A branch-restricted variant (e.g., `_branch1` requiring
`[ρ₁, ρ₂] ⊂ (c, branchSplit c]` with a kernel inequality involving
the `(c⁶/(6·(ρ²−c²))) · Z_ρ` shape) would be a separate sprint, and
its disk-side bound would currently need to come from sprint 015's
`(5)`-derived bound (still paper-axiom `{eq5}`). To make a branch-1
variant paper-axiom-free, we would first need a series-level
counterpart of sprint 015's bound — which is a separate analytical
surface and out of scope here. Sprint 035 sticks to the full-window
shape that *can* be made paper-axiom-disk-free with the existing
toolkit.

### Note on the annulus side

Sprint 035 does **not** attempt to make the annulus side
paper-axiom-free. The annulus-side body uses sprint 006's
`annulusExcess_lower_bound_of_eq8_eq9` (paper-axiom signature
`{eq8, eq9}`), the sprint 011/012 `sigmaZeroMinus`-monotonicity
cascade, and the `paperLambda K c ρ'` denominator structure verbatim
from sprint 014. Series-deriving `eq8`/`eq9` is a separate analytical
surface (the `liftGap` representation) that has not been touched in
the workspace yet; it would require new Mathlib archaeology and
likely `Scratch/` exploration. Out of scope for sprint 035.

After sprint 035 lands, the workspace's net paper-axiom signature on
the disk-side / annulus-side split for the *full-window* closing
reducer family becomes:

| Reducer | Disk-side `paper.eq*` | Annulus-side `paper.eq*` |
|---------|------------------------|---------------------------|
| sprint 014 | `{eq3, eq4}` | `{eq8, eq9}` |
| **sprint 035** | **`{}` (modulo `hSigmaCmp`)** | `{eq8, eq9}` |

This is the structural goal: **eliminate the disk-side paper-axiom
signature first**, then a future sprint can attempt the annulus side.
Sprint 035 closes the disk-side half of the `paper.eq*`-elimination
program for the full-window closing-reducer family.

### Note on the witness at the seed

V35's `_witness_at_seed` side lemma should exhibit a complete
discharge of the new reducer at the seed `c = c_value = 3554/10000`,
mirroring V14's `v14_full_window_witness_at_seed` but with the three
new disk-side witness cells (`hSummable`, `hSummable_n1_c`,
`hSigmaCmp`) added. Specifically:

* The two new summability hypotheses (`hSummable` over `[0, c)`,
  `hSummable_n1_c` at `c`) are taken as universally-quantified Lean
  hypotheses on the side lemma — exactly as V34's `_compiles` and
  `_recovers_via_eq4_at_seed` side lemmas do.
* The `hSigmaCmp` hypothesis is discharged via `paper.eq4_sigmaPlus_bound
  (r := c_value)`'s second conjunct, *exactly mirroring V34's
  `_recovers_via_eq4_at_seed` discharge*. Greppable check: the `hSigmaCmp`
  binder in the witness should be filled by an expression that
  invokes `paper.eq4_sigmaPlus_bound` at `r := c_value`.
* The remaining 8 cells (the sprint-014-style witness: `ρ₁, ρ₂,
  hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle, hIntLambdaZ,
  hIntLambda, hSummable_top, hKernel`) are discharged via existing
  V14 seed scaffolding patterns at the same structural-marker window
  `(0.5, 0.7)` that V14 uses.

This side lemma serves **two roles**: (a) confirms the new reducer
is non-degenerate at the seed (the witness existential admits an
inhabitant under `Section2Assumptions a b K c_value`); (b)
demonstrates the exact discharge route that a future
oracle-bearing candidate `V_oracle.lean` would substitute (replace
`paper.eq4_sigmaPlus_bound...2.1` with the registered oracle's
witness — every other cell remains identical).

### Note on the `_compiles` side lemma

V35's `_compiles` side lemma should exhibit the new reducer's
*type-shape* compilation at the seed without committing to a specific
discharge route for `hSigmaCmp` — it takes `hSigmaCmp` (and the two
new summability hypotheses, and `hInt*`s, and `hKernel`) as
universally-quantified Lean hypotheses and feeds them into the new
reducer to produce `ValidKorenblumBound c_value`. This mirrors V14's
`v14_full_window_compiles` shape with the three new disk-side
hypothesis cells added.

### Note on hypothesis-count and analytical structure

Sprint 014's witness existential has 8 inner cells (after `ρ₁` and
`ρ₂`); sprint 035's has 11 (after `ρ₁` and `ρ₂`) — three new
disk-side cells (`hSummable`, `hSummable_n1_c`, `hSigmaCmp`) inserted
between `hρ₂_lt_one` and `hIntDisk`. The hypothesis-count delta is
+3; the disk-side paper-axiom signature shrinks from `{eq3, eq4}` to
`{}` modulo the explicit `hSigmaCmp`.

The annulus-side cells (`hIntCircle`, `hIntLambdaZ`, `hIntLambda`,
`hSummable_top`, `hKernel`) are unchanged from sprint 014.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window
      {c : ℝ}
      (hc_pos : 0 < c)
      (hc_lt_one : c < 1)
      (h_witness :
        ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
          (paper : Section2Assumptions a b K c),
          ∃ ρ₁ ρ₂ : ℝ,
            c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
              (∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
                Summable (fun k : ℕ =>
                  PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) ∧
              Summable (fun k : ℕ =>
                if PaperAxioms.n1Pred a b k then
                  PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
                else 0) ∧
              (PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) ∧
              IntervalIntegrable
                (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c ∧
              IntervalIntegrable
                (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c 1 ∧
              IntervalIntegrable
                (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                  / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
              IntervalIntegrable
                (fun ρ' => 2 * ρ' ^ 3
                  / WangOuter.paperLambda K c ρ') volume ρ₁ ρ₂ ∧
              Summable (fun k : ℕ =>
                if PaperAxioms.n2Pred a b k then
                  PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                else 0) ∧
              c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                        2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ') :
      ValidKorenblumBound c
  ```
  Estimated location: append after sprint 034's
  `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
  (after line 5328 of `Reduction.lean`). Estimated ~120-140 lines
  including the witness destructure and the `calc` chain.

  The proof body is structurally **sprint 014's body verbatim** (lines
  1712-1827 of `Reduction.lean`) with the following targeted
  substitutions:

  1. **Update the `obtain ⟨...⟩` destructure** at sprint 014's line
     1714-1716 to thread the three new witness cells:
     ```lean
     obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hSummable, hSummable_n1_c,
         hSigmaCmp, hIntDisk, hIntCircle, hIntLambdaZ, hIntLambda,
         hSummable_top, hKernel⟩ := h_witness paper
     ```
  2. **Replace lines 1722-1723** (the `hDisk :=
     diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one
     hIntDisk` invocation) with:
     ```lean
     have hDisk :=
       diskExcess_upper_bound_via_series_only_modulo_sigma_compare
         hc_pos hc_lt_one hSummable hSummable_n1_c hSigmaCmp hIntDisk
     ```
  3. **Leave everything else byte-for-byte identical** to sprint 014's
     body (lines 1717-1827 modulo the `hDisk` substitution): the
     geometric scaffolding (`hρ₁_lt_one`, `hcρ₂`, `hc_le_ρ₁`), the
     `Z_c ≥ 0` derivation via sprint 005, steps (a)/(b)/(c) for the
     kernel-inequality multiplication and the `Z_c → Z_{ρ'}` integrated
     bound, the annulus-side bound via sprint 006, and the final
     `calc` chain.

- `ProofRefinement/Korenblum/Candidates/V35.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V34),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V34),
  4. Adds two side lemmas
     `v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_compiles`
     and
     `v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_witness_at_seed`
     exercising the new generic reducer:

     - `_compiles` exhibits the new reducer's hypothesis shape — taking
       all the witness cells (including the three new disk-side cells
       `hSummable`, `hSummable_n1_c`, `hSigmaCmp`) as
       universally-quantified Lean hypotheses on the side lemma, and
       applying the new reducer to produce `ValidKorenblumBound
       c_value`. Mirrors V14's `v14_full_window_compiles` shape.

     - `_witness_at_seed` takes a `Section2Assumptions a b K c_value`
       instance, discharges `hSigmaCmp` from `paper.eq4_sigmaPlus_bound
       (r := c_value)`'s second conjunct projection (mirroring V34's
       `_recovers_via_eq4_at_seed`), and discharges the remaining
       witness cells via the same V14 seed scaffolding patterns at
       the structural-marker window `(0.5, 0.7)`. The two new
       summability hypotheses and the integrability hypotheses are
       taken as additional universally-quantified hypotheses on the
       side lemma. Concrete witness fields:
       * `ρ₁ := 1/2`, `ρ₂ := 7/10` (matching V14's window).
       * `hcρ₁ := by norm_num [c_value]` (verifying `c_value < 1/2` at
         the seed).
       * `hρ₁₂ := by norm_num` (verifying `1/2 ≤ 7/10`).
       * `hρ₂_lt_one := by norm_num` (verifying `7/10 < 1`).
       * `hSummable := <hypothesis>`, `hSummable_n1_c :=
         <hypothesis>`, `hSigmaCmp :=
         paper.eq4_sigmaPlus_bound (r := c_value) ... .2.1`,
         `hIntDisk := <hypothesis>`, `hIntCircle := <hypothesis>`,
         `hIntLambdaZ := <hypothesis>`, `hIntLambda := <hypothesis>`,
         `hSummable_top := <hypothesis>`, `hKernel := <hypothesis>`.
       Outputs `ValidKorenblumBound c_value`.

  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V34).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V35` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V35.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V35 ties V34 at the
   seed; the new reducer is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V35.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V35.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq2_*`, `paper.eq3_*`, `paper.eq4_*`, `paper.eq5_*`, or
   `paper.eq6_*` field projection on the disk side — disk-side body is
   paper-axiom-free. Greppable check: in the body of
   `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window`,
   the count of `paper.eq2`, `paper.eq3`, `paper.eq4`, `paper.eq5`, and
   `paper.eq6` substrings is **0** for each.

   (The annulus side does invoke `paper.eq8` / `paper.eq9` transitively
   through sprint 006; this is by design and not in scope to eliminate
   here.)
7. The proof body invokes
   `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
   (sprint 034) at least once. Greppable check: count of
   `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
   substrings in the body of the new theorem is ≥ 1.
8. The proof body invokes `annulusExcess_lower_bound_of_eq8_eq9`
   (sprint 006) at least once. Greppable check: count of
   `annulusExcess_lower_bound_of_eq8_eq9` substrings in the body of the
   new theorem is ≥ 1.
9. The proof body **does not invoke**
   `diskExcess_upper_bound_via_eq3_eq4` (sprint 013),
   `diskExcess_upper_bound_via_circleGapSeries_eq4_only` (sprint 026),
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` (sprint
   022), `diskExcess_upper_bound_via_eq5` (sprint 015), or
   `diskExcess_upper_bound_via_eq6` (sprint 016) anywhere — the
   structural marker that sprint 035 routes the disk side **only**
   through sprint 034. Greppable check: count of
   `diskExcess_upper_bound_via_eq3_eq4` is 0,
   `diskExcess_upper_bound_via_circleGapSeries_eq4_only` is 0,
   `diskExcess_upper_bound_via_eq2_eq3_eq4_branch2_collapse` is 0,
   `diskExcess_upper_bound_via_eq5` is 0,
   `diskExcess_upper_bound_via_eq6` is 0.
10. The new theorem's witness existential includes the explicit
    `hSigmaCmp : PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus
    a b c` cell. Greppable check: the substring
    `PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c`
    appears in the witness existential portion of the signature.
11. The V35 `_witness_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `paper.eq4_sigmaPlus_bound` exactly once, in the proof
    body, to discharge the `hSigmaCmp` cell of the new reducer's
    witness (greppable: count of `paper.eq4_sigmaPlus_bound` in the
    body of `v35_..._witness_at_seed` is exactly 1). This confirms
    the new reducer **strictly generalises** sprint 014 (any consumer
    with `paper.eq4` access can recover sprint 014's exact end-to-end
    conclusion through the new chain).
12. The proof body **does not invoke**
    `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` (sprint 014)
    or any other prior `valid_of_*` reducer — the structural marker
    that sprint 035 is a fresh closing reducer, not a wrapper around
    sprint 014. Greppable check: count of `valid_of_disk_eq3_eq4`,
    `valid_of_eq15`, `valid_of_eq12_eq13`, `valid_of_eq10_subinterval`,
    `valid_of_eq11_subinterval`, `valid_of_eq5_eq8_eq9`,
    `valid_of_disk_eq6`, `valid_of_disk_eq2_eq3_eq4_collapse`,
    `valid_of_disk_eq5_annulus`, `valid_of_eq10_eq11_straddling`, and
    `valid_of_eq2_eq3_eq4_annulus_budget` substrings in the body of
    the new theorem is 0 for each.

## Out of scope

- Edit older candidates V0–V34.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V35 is the
  same `hEq15_seed_3554` that V0–V34 use.
- Add a new `[[oracles]]` entry in `lemma.toml`. The `hSigmaCmp`
  cell in sprint 035's witness is discharged in V35's
  `_witness_at_seed` side lemma via `paper.eq4_sigmaPlus_bound`'s
  second conjunct projection, not via an oracle. Adding a numerical
  oracle for `Σ⁺(c) ≤ Σ⁻(c)` is the natural follow-up sprint (would
  involve a `Numerical_Library/` truncated-series check with explicit
  tail bound, plus a `lemma.toml` entry plus a new candidate consuming
  the oracle in place of `paper.eq4`'s second conjunct), but is **out
  of sprint 035's scope**.
- Land a `Proposals/proposal_*.md` for the `Σ⁺(c) ≤ Σ⁻(c)` oracle. A
  future planner may file this if motivated; sprint 035 is decoupled
  from the proposal in that the new reducer ships and is exercised at
  the seed without any new trust expansion. The proposal would be a
  *separate* trust-expansion path, not a prerequisite for sprint 035.
- Eliminate paper axioms on the *annulus side* (currently sprint 006
  transitively invokes `paper.eq8` and `paper.eq9`). Series-deriving
  `eq8`/`eq9` is a separate analytical surface (involving the
  `liftGap` representation) that has not been touched in the workspace
  yet; would require new Mathlib archaeology and likely `Scratch/`
  exploration. Out of scope.
- Land a branch-restricted variant of sprint 035 (e.g.,
  `_branch1_window` or `_branch2_window` analogues using sprint 015's
  or sprint 016's disk bounds). The full-window shape sprint 035 ships
  is the maximally general one with the existing toolkit; the
  branch-restricted variants would each require additional
  prerequisites (e.g., a series-level counterpart of sprint 015's
  `(5)`-derived bound for a `_branch1` variant). Queueable separately.
- Materialise sprint 035 in a *numerical* push (i.e., a candidate that
  attempts to discharge sprint 035's witness existential at a `c >
  0.3554`, requiring a corresponding numerical proof of `Σ⁺(c) ≤
  Σ⁻(c)` at that `c`). This is the eventual `c_value`-raise sprint
  that sprint 035 *enables* but does not itself execute. Per the
  bulletin's de-prioritisation of numerical pushes against fixed
  reductions, the numerical push should follow only after the
  oracle/proposal infrastructure for `Σ⁺(c) ≤ Σ⁻(c)` is in place.
- Ship a paper-axiom-free counterpart of any other prior closing
  reducer (e.g., a paper-axiom-free counterpart of sprints 023/024 in
  the branch-2 family). Sprint 035 ships only the full-window
  counterpart of sprint 014; branch-restricted counterparts require
  the as-yet-non-existent paper-axiom-free counterparts of sprints
  015/016/022 and are out of scope.
- Land any further `valid_of_*` reducer in the same direction (e.g.,
  a `_uniformSummable` variant of sprint 035 collapsing sprint 014's
  two-anchor summability shape to a single-anchor summability premise
  via sprint 012, mirroring the sprint 023→sprint 024 progression).
  Queueable as a separate sprint after sprint 035 lands.

## Time budget

≤ 75 minutes runtime. (Sprint 014's body is ~110 lines; sprint 035's
body is sprint 014's body verbatim with one targeted disk-side
substitution. The witness destructure adds ~5 lines and the targeted
substitution adds ~3 lines net. V35 candidate adds ~50–70 lines per
side lemma — slightly larger than V14 due to the three new witness
cells.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
