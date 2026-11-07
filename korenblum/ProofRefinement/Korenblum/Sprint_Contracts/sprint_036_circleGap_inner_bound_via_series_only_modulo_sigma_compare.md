# Sprint 036: Pointwise inner-disk two-`Z` upper bound on `circleGap a b r` with **paper-axiom-free body** modulo a single explicit `Σ⁺(c) ≤ Σ⁻(c)` hypothesis — the workspace's **first non-integrated, paper-axiom-free two-`Z` upper bound on `circleGap`**, the **pointwise counterpart of sprint 034**, the **structural prerequisite for paper-axiom-free re-derivations of sprints 030, 031, and the entire branch-collapse cone (sprints 007/022)**, and the **first lemma to fuse sprint 005 + sprint 027 + sprint 028 + sprint 032 + an explicit `hSigmaCmp` cell into a single pointwise chain**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V35.lean`
**Target file**: `Candidates/V36.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem circleGap_inner_bound_via_series_only_modulo_sigma_compare
    {a b : ℕ → ℂ} {r c ρ : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hr_lt : r < c)
    (hcρ : c < ρ)
    (hρ1 : ρ < 1)
    (hSummable_circleGap_r :
      Summable (fun k : ℕ =>
        PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hSummable_n2_ρ :
      Summable (fun k : ℕ =>
        if PaperAxioms.n2Pred a b k then
          PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) :
    PaperAxioms.circleGap a b r ≤
      (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b c
        + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
          * PaperAxioms.sigmaZeroMinus a b ρ
```

This is the workspace's **first pointwise two-`Z` inner-disk upper bound on
`circleGap a b r` whose proof body invokes zero `paper.eq*` field
projections** — and the **pointwise (non-integrated) counterpart of sprint
034**. The unique series-non-derivable conjunct of the `(2)+(3)+(4)` cone,
`Σ⁺(c) ≤ Σ⁻(c)`, is **lifted into the signature** as the explicit
hypothesis `hSigmaCmp`, and **every other analytical step in the body is
supplied by an existing paper-axiom-free workspace lemma**:

| Analytical step inside body                                | Provider |
|------------------------------------------------------------|----------|
| `circleGap r = sigmaPlus r − r²·sigmaZeroMinus r`          | sprint 027 (`circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`) |
| `sigmaPlus r ≤ sigmaPlus c`                                | sprint 032 (`sigmaPlus_monotone_of_summable`) |
| `sigmaPlus c ≤ sigmaMinus c`                               | **explicit hypothesis `hSigmaCmp`** |
| `sigmaMinus c = c² · sigmaZeroMinus c`                     | sprint 005 (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`) |
| `sigmaZeroMinus r ≥ ((ρ²−r²)/(ρ²−c²))·Z_c − ((c²−r²)/(ρ²−c²))·Z_ρ` | sprint 028 (`sigmaZeroMinus_lower_via_series_convexity`) |
| Multiply by `r² ≥ 0`, combine with `circleGap` identity, algebraic clean-up | sprint 029's body verbatim |

The closed-form RHS
`(c² − r²(ρ²−r²)/(ρ²−c²))·Z_c + r²·((c²−r²)/(ρ²−c²))·Z_ρ` is
**byte-for-byte identical** to sprint 002's and sprint 029's RHS — the
analytical chain converges on the same target through a **structurally
distinct paper-axiom signature**: empty body, single explicit hypothesis
`hSigmaCmp` carrying the unique remaining oracle-target inequality.

The N1-restricted summability hypothesis `hSummable_n1_c` at the upper
anchor `c` is required by sprint 032's signature (which takes
`Summable (k ↦ if n1Pred then coeffPlusGap·c^(2k) else 0)`). It is the
exact analog of sprint 034's `hSummable_n1_c` premise: same shape, same
role — feeding sprint 032 a summability witness at the right anchor.

The N2-restricted summability hypothesis `hSummable_n2_ρ` at the upper
anchor `ρ` is required by sprint 028's signature (which takes
`Summable (k ↦ if n2Pred then coeffMinusGap·ρ^(2k−2) else 0)`). It is
verbatim from sprint 029's signature.

The `hSummable_circleGap_r` premise is required by sprint 027's signature
and is verbatim from sprint 029's signature.

Then ship a `Candidates/V36.lean` at the same `c = 0.3554` that
compiles, scores `≥ V35 = 1777/5000`, and **materialises** the new
theorem in side lemmas
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_compiles`
and
`v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_recovers_via_eq4_at_seed` side lemma demonstrates that the
`hSigmaCmp` hypothesis can be discharged from
`paper.eq4_sigmaPlus_bound`'s second conjunct at the seed — exactly
mirroring the V34 `_recovers_via_eq4_at_seed` discharge. This confirms
the new theorem is a **strict generalisation of sprint 029**: any
consumer with `paper.eq4` access can recover sprint 029's exact
conclusion through the new chain.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 036 ships:

1. **The workspace's first non-integrated, paper-axiom-free two-`Z`
   upper bound on `circleGap a b r`.** Every prior pointwise upper
   bound on `circleGap` in `Reduction.lean` either invokes
   `paper.eq{2..4}` field projections or is restricted to the simpler
   single-`Z` shape:

   | Sprint | Pointwise upper bound | Paper-axioms in body |
   |--------|------------------------|----------------------|
   | 002 | `circleGap_inner_bound_of_eq2_eq3_eq4` (two-`Z`)         | `{eq2, eq3, eq4}` |
   | 025 | `circleGap_le_sigmaPlus_via_series_split` (single-`Σ⁺`) | `{}` (no two-`Z` shape; weaker conclusion) |
   | 029 | `circleGap_inner_bound_via_series_eq4_only` (two-`Z`)   | `{eq4}` |
   | **NEW: 036** | `circleGap_inner_bound_via_series_only_modulo_sigma_compare` (two-`Z`) | **`{}` modulo explicit `hSigmaCmp`** |

   Sprint 036 closes this descending sequence at the **pointwise** layer,
   which is the **input layer** for every integrated disk bound, every
   branch-collapse disk bound, and every closing reducer in the disk-side
   cone. By eliminating the disk-side paper-axiom signature at the
   pointwise level, sprint 036 unblocks paper-axiom-free re-derivations
   of every downstream chain (queueable as separate sprints).

2. **Pointwise counterpart of sprint 034 — completes the
   pointwise/integrated symmetry on the disk-side cone.** Sprint 034
   ships the integrated single-`Z` paper-axiom-free disk bound modulo
   `hSigmaCmp`. Sprint 036 ships the pointwise two-`Z` paper-axiom-free
   inner bound modulo `hSigmaCmp`. Together they form the full
   pointwise/integrated × single-`Z`/two-`Z` matrix on the disk side:

   | Layer       | Single-`Z` shape (full-disk) | Two-`Z` shape (parametric ρ) |
   |-------------|------------------------------|-------------------------------|
   | Pointwise   | sprint 025 (single-`Σ⁺`, weaker) | **NEW sprint 036** |
   | Integrated  | **sprint 034**               | (future: sprint 030 counterpart) |

   Sprint 036 is the **missing** pointwise two-`Z` corner. Together
   with sprint 034 the workspace toolkit covers both shapes
   paper-axiom-free modulo the same `hSigmaCmp` cell.

3. **Structural prerequisite for paper-axiom-free re-derivations of
   the entire downstream cone.** Once sprint 036 ships, the following
   downstream sprints become purely mechanical refactors (each ~10–30
   lines net):

   * **A future "sprint 037"** could ship
     `diskExcess_upper_bound_via_series_only_modulo_sigma_compare_two_Z`,
     a paper-axiom-free counterpart of sprint 030 produced by replacing
     the call to `circleGap_inner_bound_via_series_eq4_only` (sprint
     029) at sprint 030's line 4477 with a call to sprint 036.
   * **A future "sprint 038"** could ship
     `diskExcess_upper_bound_collapsed_single_Z_via_series_only_modulo_sigma_compare`,
     a paper-axiom-free counterpart of sprint 031 produced by replacing
     the call to `diskExcess_upper_bound_via_series_eq4_only_two_Z`
     (sprint 030) at sprint 031's body with a call to "sprint 037".
   * **Future paper-axiom-free closing reducers** mirror sprint 035's
     fusion pattern but with branch-1 (sprint 014's pattern) and
     branch-2 (sprint 023/024's pattern) restrictions, each reusing
     sprint 035's annulus-side body.

   Sprint 036 is the **single bottleneck** for this entire downstream
   cone. Without it, the pointwise two-`Z` inner bound necessarily
   passes through `paper.eq4`, and every downstream integrated /
   branch-collapse / closing-reducer sprint inherits this dependency.

4. **First lemma to fuse five paper-axiom-free workspace lemmas
   (sprint 005, 027, 028, 032, plus an explicit `hSigmaCmp` cell)
   into a single pointwise chain.** Sprint 034 fuses sprint 005,
   sprint 025, sprint 032, and `hSigmaCmp` (four-element fusion) at
   the integrated layer. Sprint 036 fuses sprint 005, sprint 027 (the
   *equality* upgrade of sprint 025), sprint 028 (paper-axiom-free
   `(2)`), sprint 032, and `hSigmaCmp` (five-element fusion) at the
   pointwise layer. The addition of sprint 028 to the chain is what
   distinguishes the two-`Z` shape from sprint 034's single-`Z`
   shape: sprint 028's lower bound on `Z_r` in terms of `Z_c` and
   `Z_ρ` is the structural ingredient that lets the bound depend on
   `Z_ρ` (parametrically in `ρ`) rather than collapsing to
   `c²·Z_c` only.

5. **First downstream consumer of the joint sprint 027 + sprint 028
   pair.** Sprint 027 (`circleGap` equality) and sprint 028
   (`Z_r` lower bound) are independent series-level lemmas. Sprint
   034 uses sprint 005 + sprint 025 (the *inequality* form, not
   sprint 027); sprint 029 uses sprint 027 but invokes `paper.eq2`
   instead of sprint 028 (since sprint 029 was queued before sprint
   028 landed). Sprint 036 is the **first lemma** to chain sprint
   027's *equality* with sprint 028's *lower bound* in a single body.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V36 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form pointwise upper
  bound on `circleGap a b r` with the same RHS shape as sprints
  002/029.

Why this is **not** "the same chain" as sprint 029:

* **Different paper-axiom signature.** Sprint 029's body invokes
  `paper.eq4_sigmaPlus_bound` (line 4340 of `Reduction.lean`); sprint
  036's body invokes **zero** `paper.eq*` field projections. The chain
  through which the same RHS is reached is distinct: sprint 029
  delegates `Σ⁺(r) ≤ Σ⁺(c) ≤ Σ⁻(c) = c²·Z_c` to a single paper-axiom
  invocation; sprint 036 splits this chain into:
  - `Σ⁺(r) ≤ Σ⁺(c)` via sprint 032 (paper-axiom-free; not present in
    sprint 029's transitive proof body),
  - `Σ⁺(c) ≤ Σ⁻(c)` as explicit hypothesis `hSigmaCmp`,
  - `Σ⁻(c) = c²·Z_c` via sprint 005 (paper-axiom-free; not present in
    sprint 029's transitive proof body, since sprint 029's `eq4` chain
    bundles all three steps).
* **Different signature shape.** Sprint 029 has 7 cells (`paper`,
  `hr_nonneg`, `hr_lt`, `hcρ`, `hρ1`, `hSummable_circleGap_r`,
  `hSummable_n2_ρ`); sprint 036 has 8 (no `paper` parameter; same
  six geometric/summability cells; new `hSummable_n1_c` and
  `hSigmaCmp`). The structural change: drop `paper`, add
  `hSummable_n1_c` and `hSigmaCmp`.
* **Different downstream consumer pattern.** Sprint 029 cannot be
  consumed without `paper.eq4`; sprint 036 *can* be consumed without
  `paper.eq4` (e.g., via a future oracle on `Σ⁺ c ≤ Σ⁻ c`). This is
  the structural distinction.

Why this is **not** "the same chain" as sprint 025:

* **Different conclusion shape.** Sprint 025 produces the single-`Σ⁺`
  inequality `circleGap a b r ≤ sigmaPlus a b r` — a direct
  comparison without any `Z_c`/`Z_ρ` decomposition. Sprint 036
  produces the two-`Z` upper bound parametric in `ρ`, the same shape
  Wang's printed `(2)+(3)+(4)` chain produces. The two conclusions
  are not comparable as statements: sprint 025 makes no claim
  involving `Z_ρ` and is valid on the full `[0, 1)`; sprint 036
  involves `Z_c` and `Z_ρ` and requires `0 ≤ r < c < ρ < 1`.
* **Different paper-axiom signature on the workspace side.** Sprint
  025 is paper-axiom-free at the type level (no `Section2Assumptions`
  parameter); sprint 036 is also paper-axiom-free at the type level,
  but has the explicit `hSigmaCmp` hypothesis cell that sprint 025
  does not. The cells are independent: sprint 025 uses zero series
  conjuncts of the `(2)+(3)+(4)` cone; sprint 036 uses **one**
  (`hSigmaCmp` is the unique non-series-derivable conjunct).

Why this is **not** "the same chain" as sprint 034:

* **Sprint 034 is integrated** (`diskExcess ≤ c⁴ · Z_c`); sprint 036
  is **pointwise** (`circleGap a b r ≤ ...`). The shapes are
  qualitatively different.
* **Sprint 034 has no `Z_ρ` term**; sprint 036 has both `Z_c` and
  `Z_ρ` in its conclusion. The two-`Z` shape preserves the
  parametric dependence on the outer radius `ρ` that downstream
  branch-collapse arguments require.
* **Sprint 034 does not consume sprint 028**; sprint 036 does. The
  `Z_r` lower bound (sprint 028) is the structural ingredient that
  produces the two-`Z` shape, which sprint 034's single-`Z` shape
  cannot capture.

Why this is **not** "the same chain" as sprint 027 alone:

* Sprint 027 is the *identity* `circleGap a b r = sigmaPlus a b r −
  r²·sigmaZeroMinus a b r`. Sprint 036 *consumes* this identity but
  does additional work: bounds `sigmaPlus r` from above using
  sprints 032/005 + `hSigmaCmp`, bounds `−r²·sigmaZeroMinus r` from
  above using sprint 028, and combines both into a closed-form
  two-`Z` upper bound. Sprint 027 alone produces an equality, not
  an upper bound suitable for closing-reducer consumption.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~22 lines (sprint 029's signature is ~20
  lines; sprint 036 differs by dropping `paper` and `K`, adding
  `hSummable_n1_c` and `hSigmaCmp`).
* The proof body is ~80–100 lines — sprint 029's body (~117 lines,
  lines 4300–4417 of `Reduction.lean`) modified by:
  - replace lines 4337–4346 (the `paper.eq4_sigmaPlus_bound` unfold +
    `obtain ⟨h4a, h4b, h4c⟩`) with three direct workspace lemma
    invocations:
    ```lean
    have hSigmaPlus_le :
        PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
      have hMono : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
        sigmaPlus_monotone_of_summable hr_nonneg hr_lt.le hSummable_n1_c
      have hChain : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
        le_trans hMono hSigmaCmp
      have hIdent :
          PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c :=
        sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b c
      rw [hIdent] at hChain
      exact hChain
    ```
  - drop the `paper` and `{K}` parameters,
  - keep the rest of sprint 029's body (lines 4321–4336 setting up
    positivity facts and invoking sprints 027 + 028; lines 4347–4417
    doing the algebraic chain and matching the goal's denominator
    form) byte-for-byte identical.
* All Lean idioms used (`mul_le_mul_of_nonneg_left`, `linarith`,
  `simp only`, `calc`, `rw`, `nlinarith`) are verbatim from sprint
  029's body. No new idioms required.
* Estimate: ~80–100 lines for the new theorem. Candidate side lemmas
  ~30 lines each. Total V36 size: ≤ 200 lines.

### Note on the choice to lift `Σ⁺(c) ≤ Σ⁻(c)` to a hypothesis

Identical to sprint 034's note: an alternative shape would be to
**derive** `Σ⁺(c) ≤ Σ⁻(c)` from `paper.eq4_sigmaPlus_bound`'s second
conjunct internally and bake `paper : Section2Assumptions a b K c`
into the new theorem's signature, eliminating the `hSigmaCmp`
hypothesis. This would **not** achieve sprint 036's structural goal:
the body would still invoke `paper.eq4` and the paper-axiom signature
would remain non-empty. The chosen shape (lift `hSigmaCmp` to the
signature, drop the `paper` parameter entirely) is what enables the
structural firsts (#1, #3, #4 above) and isolates the unique oracle
target. This deliberate parallelism with sprint 034 ensures consumers
can use the same `hSigmaCmp` cell with both lemmas.

### Note on the discharge of `hSigmaCmp` at the seed

V36's `_recovers_via_eq4_at_seed` side lemma exhibits the
**discharge route via `paper.eq4_sigmaPlus_bound`**: given a
`Section2Assumptions a b K c_value` instance, the lemma extracts
`paper.eq4_sigmaPlus_bound (r := c_value) ... .2.1` (i.e., the
second conjunct of the `eq4` bundle at `r = c`) to produce an
inhabitant of `sigmaPlus a b c_value ≤ sigmaMinus a b c_value`,
then plugs this into the new generic theorem along with the
geometric/summability cells. The resulting conclusion is byte-for-byte
identical to sprint 029's at the seed — recovering sprint 029's exact
bound through sprint 036's chain.

This side lemma serves **two roles**: (a) confirms the new theorem
is a strict generalisation of sprint 029 (any consumer with
`paper.eq4` access can recover sprint 029's bound from sprint 036);
(b) demonstrates the precise discharge route that a future
oracle-bearing consumer would substitute (replace
`paper.eq4_sigmaPlus_bound...2.1` with the oracle's witness — every
other cell remains identical).

### Note on the `hSummable_n1_c` premise

Identical role to sprint 034's `hSummable_n1_c` premise. Sprint 032
takes `Summable (k ↦ if n1Pred a b k then coeffPlusGap·s^(2k) else 0)`
at the upper anchor `s`. Sprint 036 wants to apply sprint 032 with
`s = c` (and `r ≤ c`), so we need this summability **at `c`**. The
premise can be discharged in V36's side lemmas externally (as a
universal hypothesis) or, in a future oracle-bearing candidate, from
a stronger summability assumption at any `t ≥ c`.

### Note on the specific position of `hSummable_n1_c` in the signature

We place `hSummable_n1_c` immediately after `hSummable_circleGap_r`
and immediately before `hSummable_n2_ρ`, matching the natural ordering
"premises feeding sprint 027 / sprint 032 / sprint 028 in body order".
This makes the chain easier to read at the type level and matches
sprint 034's ordering.

### Note on hypothesis-count and analytical structure

Sprint 029 has 7 cells (`paper`, `hr_nonneg`, `hr_lt`, `hcρ`, `hρ1`,
`hSummable_circleGap_r`, `hSummable_n2_ρ`). Sprint 036 has 8
(paper-axiom-free signature; no `paper` parameter; same five
geometric/summability cells; new `hSummable_n1_c` and `hSigmaCmp`).
The hypothesis-count delta is +1 (drop `paper`, add `hSummable_n1_c`
and `hSigmaCmp`). Net: hypothesis count grows by 1; paper-axiom
signature on the body shrinks from `{eq4}` to `{}` modulo the
explicit `hSigmaCmp`.

### Note on the witness at the seed

V36's `_recovers_via_eq4_at_seed` side lemma should exhibit the
discharge of the new theorem at the seed `c = c_value = 3554/10000`,
with `hSigmaCmp` discharged by `paper.eq4_sigmaPlus_bound (r :=
c_value) ...` (the second conjunct projection `.2.1`). The other
hypotheses are discharged via existing seed scaffolding patterns
already used in sprint 029's V29 candidate — the structural-marker
`ρ` value should be a concrete rational larger than `c_value` (e.g.,
`ρ := 1/2` mirroring sprint 022's witness, well above the seed
`c_value ≈ 0.3554`).

The `_compiles` side lemma should exhibit the new theorem's
hypothesis shape with concrete `c = c_value`, `r := c_value/2`,
`ρ := 1/2`, mirroring V29's `_compiles` shape with the two extra
premises.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem circleGap_inner_bound_via_series_only_modulo_sigma_compare
      {a b : ℕ → ℂ} {r c ρ : ℝ}
      (hr_nonneg : 0 ≤ r)
      (hr_lt : r < c)
      (hcρ : c < ρ)
      (hρ1 : ρ < 1)
      (hSummable_circleGap_r :
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
      (hSummable_n1_c :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
          else 0))
      (hSummable_n2_ρ :
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * ρ ^ (2 * k - 2)
          else 0))
      (hSigmaCmp :
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c) :
      PaperAxioms.circleGap a b r ≤
        (c ^ 2 - r ^ 2 * (ρ ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
            * PaperAxioms.sigmaZeroMinus a b c
          + r ^ 2 * ((c ^ 2 - r ^ 2) / (ρ ^ 2 - c ^ 2))
            * PaperAxioms.sigmaZeroMinus a b ρ
  ```
  Estimated location: append after sprint 035's
  `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window`
  (at the current end of `Reduction.lean`). Estimated ~80–100 lines
  including the chain through sprint 005/027/028/032 and the algebraic
  match.

  The proof body is structurally **sprint 029's body verbatim** (lines
  4321–4417 of `Reduction.lean`) with the following targeted
  substitution at lines 4337–4346:

  Replace
  ```lean
  -- Step 2: invoke the eq4 bundle (three pieces about sigmaPlus / sigmaMinus
  -- at c). Verbatim from sprint 002; the sole `paper.*` invocation in this proof.
  have h4 :=
    paper.eq4_sigmaPlus_bound (r := r) hr_nonneg hr_lt hc_lt_one
  have h4_unfold :
      PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c ∧
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c ∧
        PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
  obtain ⟨h4a, h4b, h4c⟩ := h4_unfold
  have hSigmaPlus_le :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    have : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
      le_trans h4a h4b
    rw [h4c] at this
    exact this
  ```
  with
  ```lean
  -- Step 2: paper-axiom-free three-step chain
  --   Σ⁺(r) ≤ Σ⁺(c) ≤ Σ⁻(c) = c²·Z_c.
  -- sprint 032 supplies `Σ⁺(r) ≤ Σ⁺(c)` (paper-axiom-free).
  have hMono : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
    sigmaPlus_monotone_of_summable hr_nonneg hr_lt.le hSummable_n1_c
  -- explicit hypothesis: `Σ⁺(c) ≤ Σ⁻(c)`.
  -- sprint 005 supplies `Σ⁻(c) = c² · Z_c` (paper-axiom-free).
  have hIdent :
      PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c :=
    sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b c
  have hSigmaPlus_le :
      PaperAxioms.sigmaPlus a b r ≤ c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
    have hChain : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
      le_trans hMono hSigmaCmp
    rw [hIdent] at hChain
    exact hChain
  ```

  Drop the `paper : Section2Assumptions a b K c` parameter and the
  derived `hc_pos`, `hc_lt_one`, `hc_lt_ρ` facts that are only
  needed by the dropped `paper.eq4_sigmaPlus_bound` invocation.
  (`hc_pos`, `hc_lt_one`, `hc_lt_ρ` are derived from `hr_nonneg`,
  `hr_lt`, `hcρ`, `hρ1` already at lines 4322–4326 of sprint 029's
  body — keep these because they are needed for sprint 028's
  positivity scaffolding and for the algebraic-chain steps.)

  The remainder of the body (lines 4347–4417 of sprint 029: invoking
  sprint 028 for the `Z_r` lower bound, multiplying by `r² ≥ 0`,
  combining with the `circleGap` identity from sprint 027, building
  the algebraic chain, and matching the goal's denominator-laden
  form) is **byte-for-byte identical** to sprint 029.

- `ProofRefinement/Korenblum/Candidates/V36.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V35),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V35),
  4. Adds two side lemmas
     `v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_compiles`
     and
     `v36_circleGap_inner_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`
     exercising the new generic theorem:
     - `_compiles` exhibits the new theorem's hypothesis shape — eight
       cells: `hr_nonneg`, `hr_lt`, `hcρ`, `hρ1`,
       `hSummable_circleGap_r`, `hSummable_n1_c`, `hSummable_n2_ρ`,
       `hSigmaCmp`. Concrete witness: instantiate at `c = c_value =
       3554/10000`, `r := c_value / 2 = 1777/10000`, `ρ := 1/2`. The
       three summability hypotheses are taken as universally-quantified
       Lean hypotheses on the side lemma; `hSigmaCmp` is also taken
       as a hypothesis (this side lemma does **not** use a `paper`
       instance).
     - `_recovers_via_eq4_at_seed` takes a `Section2Assumptions a b K
       c_value` instance, discharges `hSigmaCmp` from
       `paper.eq4_sigmaPlus_bound (r := c_value)`'s second conjunct
       projection (mirroring V34's `_recovers_via_eq4_at_seed`), and
       applies the new theorem to recover sprint 029's exact
       conclusion at the seed (`circleGap a b r ≤ ...` with `r :=
       c_value / 2`, `ρ := 1/2`). The summability hypotheses are taken
       as additional universally-quantified hypotheses on this side
       lemma.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V35).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V36` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V36.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V36 ties V35 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V36.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `circleGap_inner_bound_via_series_only_modulo_sigma_compare`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V36.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — the body is paper-axiom-free.
   Greppable check: in the body of
   `circleGap_inner_bound_via_series_only_modulo_sigma_compare`, the
   count of `paper.eq` substrings is **0**. (The lemma's signature
   also does not include a `paper : Section2Assumptions ...`
   parameter.)
7. The proof body invokes `sigmaPlus_monotone_of_summable` (sprint
   032) at least once. Greppable check: count of
   `sigmaPlus_monotone_of_summable` substrings in the body of the new
   theorem is ≥ 1.
8. The proof body invokes
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   (sprint 027) at least once. Greppable check: count of
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   substrings in the body of the new theorem is ≥ 1.
9. The proof body invokes `sigmaZeroMinus_lower_via_series_convexity`
   (sprint 028) at least once. Greppable check: count of
   `sigmaZeroMinus_lower_via_series_convexity` substrings in the body
   of the new theorem is ≥ 1.
10. The proof body invokes `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
    (sprint 005) at least once. Greppable check: count of
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` substrings in the body
    of the new theorem is ≥ 1.
11. The new theorem's signature includes the explicit `hSigmaCmp :
    PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c`
    hypothesis. Greppable check: the substring `hSigmaCmp` appears
    in the signature line region (lines containing the new theorem's
    parameter list).
12. The V36 `_recovers_via_eq4_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `paper.eq4_sigmaPlus_bound` exactly once, in the proof
    body (greppable: count of `paper.eq4_sigmaPlus_bound` in the
    body of `v36_..._recovers_via_eq4_at_seed` is exactly 1). This
    confirms the new theorem **strictly generalises** sprint 029
    (any consumer with `paper.eq4` access can recover sprint 029's
    conclusion through the new chain).
13. The proof body of the new theorem **does not invoke**
    `circleGap_inner_bound_via_series_eq4_only` (sprint 029),
    `circleGap_inner_bound_of_eq2_eq3_eq4` (sprint 002), or
    `circleGap_le_sigmaPlus_via_series_split` (sprint 025) — the
    structural marker that sprint 036 is a fresh chain, not a
    repackaging of any prior pointwise inner bound. Greppable check:
    count of `circleGap_inner_bound_via_series_eq4_only` is 0,
    count of `circleGap_inner_bound_of_eq2_eq3_eq4` is 0,
    count of `circleGap_le_sigmaPlus_via_series_split` is 0.

## Out of scope

- Edit older candidates V0–V35.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V36 is the
  same `hEq15_seed_3554` that V0–V35 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land an oracle/proposal for `Σ⁺(c) ≤ Σ⁻(c)`. Sprint 036 isolates
  this as a type-level hypothesis but does not itself discharge it
  via an oracle. A future planner may file
  `Proposals/proposal_001_*.md` for a numerical oracle on `Σ⁺(c) ≤
  Σ⁻(c)` if motivated; sprint 036 is decoupled from that proposal.
- Materialise sprint 036 in a downstream chain (i.e., do not
  re-derive sprint 030, sprint 031, sprint 022, sprint 007, or any
  closing reducer using sprint 036 yet — those are the second-order
  follow-up sprints). Sprint 036 ships only the new pointwise inner
  bound plus its V36 side-lemma materialisations.
- Land a paper-axiom-free counterpart of sprint 002's bound through
  any *other* chain (e.g., via sprint 025's single-`Σ⁺` bound rather
  than sprint 027's equality + sprint 028's `Z_r` lower bound). The
  five-element chain sprint 005 + sprint 027 + sprint 028 + sprint
  032 + `hSigmaCmp` is the unique chain we ship in sprint 036.
- Land the N1-side `sigmaPlus_summable_of_summable_at_upper` lemma
  (the dual of sprint 012's N2-side summability transfer; sprint
  033's "alternative K"). This would let sprint 036's
  `hSummable_n1_c` premise be derived from a single anchor at any
  `t ≥ c` rather than supplied directly. Out of sprint 036's scope;
  queueable separately.
- Series-derive any annulus-side bound (sprint 005's identity is
  the only annulus-side series-level identity in the workspace, and
  it is already used by sprint 036 on the disk side via sprint 005's
  identity at `c`, not the annulus side at `ρ`). The annulus-side
  paper-axiom signature `{eq8, eq9}` is unchanged by sprint 036.
- Land the N1-side counterpart of sprint 028's three-radius
  convexity bound (sprint 033 already shipped this in the upper-bound
  direction; the lower-bound direction would be a separate sprint
  and is not needed by sprint 036).
- Ship a closing-reducer-level downstream consumer of sprint 036
  (e.g., a `valid_of_disk_series_modulo_sigma_compare_two_Z_*`
  reducer that fuses sprint 036's two-`Z` integrated counterpart
  with sprint 006's annulus bound). This is the natural second-order
  follow-up but is queueable as a separate sprint after the integrated
  two-`Z` paper-axiom-free counterpart (intermediate "sprint 037")
  ships.

## Time budget

≤ 75 minutes runtime. (Sprint 029's body is ~117 lines; sprint 036's
body is sprint 029's body with one targeted replacement of ~10 lines
at the `paper.eq4_sigmaPlus_bound` invocation. The new
`hSummable_n1_c` and `hSigmaCmp` premises are threaded through to the
replacement block. V36 candidate adds ~30–40 lines per side lemma —
slightly larger than V29 due to the two extra premises being passed
through.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
