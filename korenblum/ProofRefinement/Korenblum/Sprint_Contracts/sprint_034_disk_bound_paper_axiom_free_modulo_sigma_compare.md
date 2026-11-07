# Sprint 034: Integrated full-disk upper bound `diskExcess ≤ c⁴ · Z_c` with **paper-axiom-free body** modulo a single explicit `Σ⁺ c ≤ Σ⁻ c` hypothesis — the workspace's **first integrated `diskExcess` bound whose proof body invokes zero `paper.eq*` field projections**, the **first sprint to fuse the complete series-level toolkit (sprints 005, 025, 027, 028, 032) into a single integrated chain**, the **first downstream consumer of sprint 032**, and the **type-level isolation of `Σ⁺ c ≤ Σ⁻ c` as the unique series-non-derivable analytical target** for a future oracle/proposal

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V33.lean`
**Target file**: `Candidates/V34.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_series_only_modulo_sigma_compare
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hSigmaCmp :
      PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 4 * PaperAxioms.sigmaZeroMinus a b c
```

This is the workspace's **first integrated `diskExcess` upper bound whose
proof body invokes zero `paper.eq*` field projections**: the unique
series-non-derivable conjunct of the `(2)/(3)/(4)` cone — `Σ⁺(c) ≤
Σ⁻(c)`, identified by sprint 026's "candidate K" and sprint 032's
contract analysis as the lone remaining gap — is **lifted into the
signature** as the explicit hypothesis `hSigmaCmp`, and **every other
analytical step in the body is supplied by an existing paper-axiom-free
workspace lemma**:

| Analytical step inside body | Provider |
|------------------------------|---------|
| `circleGap r ≤ sigmaPlus r` for `r ∈ Ioo 0 c` | sprint 025 (`circleGap_le_sigmaPlus_via_series_split`) |
| `sigmaPlus r ≤ sigmaPlus c` for `0 ≤ r ≤ c` | sprint 032 (`sigmaPlus_monotone_of_summable`) |
| `sigmaPlus c ≤ sigmaMinus c` | **explicit hypothesis `hSigmaCmp`** |
| `sigmaMinus c = c² · sigmaZeroMinus c` | sprint 005 (`sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`) |
| Multiply pointwise by `2r`, integrate over `[0, c]` | sprint 026's body verbatim |
| Closed-form RHS integral `c⁴ · Z_c` | sprint 026's body verbatim |

The closed-form RHS `c⁴ · sigmaZeroMinus a b c` is **byte-for-byte
identical** to sprint 013's, sprint 026's, and sprint 029's (collapsed
to `r = c`) RHS — the analytical chain converges on the same target
through a **structurally distinct paper-axiom signature**: empty body,
single explicit hypothesis `hSigmaCmp` carrying the unique remaining
oracle-target inequality.

The N1-restricted summability hypothesis `hSummable_n1_c` at the upper
anchor `c` is required by sprint 032's signature (which takes `Summable
(N1-indicator * coeffPlusGap * c^(2k))`). It is structurally **derivable
in-house** from the existing `hSummable` premise (uniform summability of
`coeffPlusGap * r^(2k)` on `[0, c)`) via `Summable.indicator` applied
at `r = c`, but `hSummable` is restricted to `r < c` — so we must
either (a) tighten the universal closure of `hSummable` to `r ≤ c`, or
(b) take `hSummable_n1_c` as a separate explicit hypothesis. We choose
(b) because it cleanly mirrors sprint 026's signature shape (uniform
summability premise on the open interval `[0, c)` for sprint 025's
pointwise step) plus an additional anchor at `c` for sprint 032's step,
and avoids overconstraining `hSummable`.

Then ship a `Candidates/V34.lean` at the same `c = 0.3554` that
compiles, scores `≥ V33 = 1777/5000`, and *materialises* the new
theorem in side lemmas
`v34_disk_bound_via_series_only_modulo_sigma_compare_compiles` and
`v34_disk_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_recovers_via_eq4_at_seed` side lemma demonstrates that the
`hSigmaCmp` hypothesis can be discharged from
`paper.eq4_sigmaPlus_bound`'s second conjunct at the seed — i.e., **a
candidate carrying a `Section2Assumptions a b K c_value` instance can
discharge the new theorem's hypothesis directly via `paper.eq4`**,
recovering sprint 026's exact conclusion through the new chain. This is
the structural marker that the new theorem is a strict generalisation
of sprint 026: any consumer with access to `paper.eq4` can recover
sprint 026's bound, and any consumer with access to a stronger oracle/
proposal that proves `Σ⁺(c) ≤ Σ⁻(c)` independently can discharge the
new theorem **without ever invoking `paper.eq4`**.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 034 ships:

1. **The workspace's first integrated `diskExcess` bound with
   paper-axiom-free body.** Every prior integrated `diskExcess` bound in
   `Reduction.lean` invokes at least one `paper.eq*` field projection in
   its body:

   | Sprint | Disk bound theorem | Paper-axioms in body |
   |--------|---------------------|----------------------|
   | 003 | `diskExcess_upper_bound_of_eq2_eq3_eq4` | `{eq2, eq3, eq4}` |
   | 013 | `diskExcess_upper_bound_via_eq3_eq4` | `{eq3, eq4}` |
   | 026 | `diskExcess_upper_bound_via_circleGapSeries_eq4_only` | `{eq4}` |
   | 030 | `diskExcess_upper_bound_via_series_eq4_only_two_Z` | `{eq4}` |
   | **NEW: 034** | `diskExcess_upper_bound_via_series_only_modulo_sigma_compare` | **`{}` modulo explicit `hSigmaCmp`** |

   Sprint 034 closes this descending sequence: **the body invokes zero
   paper axioms**, with the unique non-series-derivable conjunct of the
   `eq4` bundle (`Σ⁺ c ≤ Σ⁻ c`) lifted to the signature as `hSigmaCmp`.

2. **The workspace's first downstream consumer of sprint 032.** Sprint
   032 shipped a paper-axiom-free `sigmaPlus`-monotonicity lemma but
   was not yet materialised in any downstream chain. Sprint 033 was
   parallel-development on N1 convexity, not downstream. Sprint 034 is
   the **first to actually use** sprint 032 in a longer analytical
   chain.

3. **Type-level isolation of the unique series-non-derivable
   analytical fact.** After sprint 032's contract analysis, the
   workspace knows that `Σ⁺(c) ≤ Σ⁻(c)` is the unique conjunct of the
   `eq2`/`eq3`/`eq4` cone that resists series-level derivation
   (because the inequality compares *disjoint partitions* of the
   index set at the same radius — no termwise dominance argument
   applies). Sprint 034 makes this **type-level explicit**: a
   developer writing a downstream consumer sees the `hSigmaCmp`
   hypothesis in the signature and immediately knows what oracle/
   proposal would close the chain. This is **the cleanest possible
   precise oracle target** — a single scalar inequality at one radius
   `c`, surface-area-`O(1)`.

4. **First sprint to fuse the complete series-level toolkit (sprints
   005, 025, 027, 028, 032) into a single integrated chain.** The
   workspace toolkit now includes:
   - sprint 005: `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
   - sprint 025: `circleGap_le_sigmaPlus_via_series_split`
   - sprint 027: `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   - sprint 028: `sigmaZeroMinus_lower_via_series_convexity`
   - sprint 032: `sigmaPlus_monotone_of_summable`
   - sprint 033: `sigmaPlus_upper_via_series_convexity`

   Of these, sprint 034 chains sprint 005, sprint 025, and sprint 032
   in the same body. The chain has the structurally novel property
   that **no `paper.eq*` field projection appears between the chain's
   ends** — the type-level signature consists of (a) standard
   summability hypotheses, (b) the unique series-non-derivable
   `hSigmaCmp` hypothesis, (c) integrability of `2r * circleGap`,
   (d) basic positivity. This is the **first integrated workspace
   chain to express its analytical content as a hypothesis-set rather
   than a paper-axiom-projection set**.

5. **Structural prerequisite for a future oracle-backed `c_value`
   push.** Per the bulletin's high-value direction #4 (oracle-backed
   numeric subclaims that support real Lean theorems), the `hSigmaCmp`
   hypothesis is the *exact site* where a future numerical oracle or
   approved proposal could plug in. Once such an oracle is added,
   sprint 034's new theorem becomes a **fully paper-axiom-free**
   integrated disk bound — which then transitively unlocks
   paper-axiom-free integrated disk bounds for downstream `valid_of_*`
   reducers, removing every `paper.eq2`/`paper.eq3`/`paper.eq4`
   invocation from the disk-side of the closing-reducer cone. This
   is the structural prerequisite for the **first paper-axiom-free
   `valid_of_*` reducer modulo a single oracle**.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V34 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at `1777/5000`.
* The new theorem is purely structural: a closed-form integrated upper
  bound on `diskExcess` with the same RHS as sprints 013/026/030.

Why this is **not** "the same chain" as sprint 026:

* **Different paper-axiom signature.** Sprint 026's body invokes
  `paper.eq4_sigmaPlus_bound` (via three conjunct projections); sprint
  034's body invokes **zero** `paper.eq*` field projections. The chain
  through which the same RHS is reached is distinct: sprint 026
  delegates the chain `Σ⁺(r) ≤ Σ⁺(c) ≤ Σ⁻(c) = c² · Z_c` to a single
  paper-axiom invocation; sprint 034 splits this chain into:
  - `Σ⁺(r) ≤ Σ⁺(c)` via sprint 032 (paper-axiom-free; not present
    in sprint 026's transitive proof body),
  - `Σ⁺(c) ≤ Σ⁻(c)` as explicit hypothesis `hSigmaCmp`,
  - `Σ⁻(c) = c² · Z_c` via sprint 005 (paper-axiom-free; not present
    in sprint 026's transitive proof body).
* **Different signature shape.** Sprint 026 has 4 hypothesis cells
  (`hc_pos`, `hc_lt_one`, `hSummable`, `hInt`); sprint 034 has 6
  (`hc_pos`, `hc_lt_one`, `hSummable`, `hSummable_n1_c`, `hSigmaCmp`,
  `hInt`). The two extra cells are the structurally novel ingredients:
  N1-anchor summability for sprint 032's premise, and the unique
  series-non-derivable inequality.
* **Different downstream consumer pattern.** Sprint 026 cannot be
  consumed without `paper.eq4`; sprint 034 *can* be consumed without
  `paper.eq4` (e.g., via a future oracle on `Σ⁺ c ≤ Σ⁻ c`). This is
  the structural distinction.

Why this is **not** "the same chain" as sprints 030 / 031:

* **Different RHS shape.** Sprint 030 produces a two-`Z` RHS (`(c⁴/6)
  (3ρ²−4c²)/(ρ²−c²) · Z_c + (c⁶/6)/(ρ²−c²) · Z_ρ`) parametrised by an
  outer radius `ρ`; sprint 031 collapses this on the branch-1
  sub-regime to a single-`Z` RHS dropping the `Z_c` term. Sprint 034
  produces the **single-`Z` full-disk** RHS `c⁴ · Z_c` valid on **all**
  of `(0, 1)` (no `ρ` parameter, no branch-split confinement),
  matching sprints 013/026's RHS shape — a different *shape* of
  closed-form bound.
* **Different paper-axiom signature.** Sprints 030/031 have `{eq4}` in
  their body (via the second conjunct of `paper.eq4_sigmaPlus_bound`
  hidden inside the body of sprint 029, which they call). Sprint 034's
  body has **no** `paper.eq*` projection.
* **Different downstream consumer profile.** Sprints 030/031 feed
  branch-restricted closing reducers (sprint 022/023/024 cone). Sprint
  034 feeds the full-window closing reducer cone (sprint 014's
  successor) and is the structural prerequisite for a paper-axiom-free
  `valid_of_*` reducer.

Why this is **not** "the same chain" as sprint 032:

* **Sprint 032 is structural infrastructure** — a paper-axiom-free
  monotonicity lemma on `sigmaPlus` over a two-radius `[r, s]` segment.
  Sprint 034 is **a downstream consumer** — it integrates sprint 032
  into a longer chain that ends in a closed-form integrated disk bound.
  Sprint 032 has no integration step, no `2r` Jacobian multiplication,
  no `intervalIntegral`-machinery. Sprint 034 has all of these (sprint
  026's body verbatim) plus the new sprint 032 step.
* **Sprint 032 ships no new closed-form bound.** Sprint 034 ships
  a closed-form integrated bound on `diskExcess`.

Why this is **not** "the same chain" as sprints 025 / 027 / 028 / 005:

* Each of these is a *single-step* paper-axiom-free lemma at the
  pointwise / series / scalar level. Sprint 034 *fuses* multiple of
  these (sprint 005 + sprint 025 + sprint 032 in the body) plus the
  integration machinery to produce a *closed-form integrated* bound on
  `diskExcess`, of a kind no prior workspace lemma produces with
  paper-axiom-free body.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~15 lines (sprint 026's signature is ~14
  lines; sprint 034 differs by the addition of `hSummable_n1_c` and
  `hSigmaCmp`).
* The proof body is ~80–100 lines — sprint 026's body (~85 lines, lines
  3777–3881 of `Reduction.lean`) modified by:
  - replace the chain `paper.eq4` → unfold → three conjuncts
    (sprint 026 lines 3809–3825) with three direct workspace lemma
    invocations (sprint 005 + sprint 032 + the explicit `hSigmaCmp`
    hypothesis),
  - add a derivation of N1-restricted summability at `c` from
    `hSummable_n1_c` (which is given directly — no derivation
    needed), so the `hSummable_n1_c` premise is consumed verbatim by
    sprint 032's call.
* All Lean idioms used (`mul_le_mul_of_nonneg_left`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `intervalIntegral.integral_const_mul`, `@integral_pow 0 c 1`, basic
  `linarith`/`positivity`) are verbatim from sprint 026's body. No
  new idioms required.
* Estimate: ~80–100 lines for the new theorem. Candidate side lemmas
  ~30 lines each. Total V34 size: ≤ 200 lines.

### Note on the choice to lift `Σ⁺(c) ≤ Σ⁻(c)` to a hypothesis

An alternative shape would be to **derive** `Σ⁺(c) ≤ Σ⁻(c)` from
`paper.eq4_sigmaPlus_bound`'s second conjunct internally and bake
`paper : Section2Assumptions a b K c` into the new theorem's
signature, eliminating the `hSigmaCmp` hypothesis. This would
**not** achieve sprint 034's structural goal: the body would still
invoke `paper.eq4` and the paper-axiom signature would remain
non-empty. The chosen shape (lift `hSigmaCmp` to the signature, drop
the `paper` parameter entirely) is what enables the structural
firsts (#1, #3, #5 above) and isolates the unique oracle target.

The cost is one additional hypothesis cell and the responsibility
shifted to consumers to discharge `hSigmaCmp` (either via
`paper.eq4_sigmaPlus_bound`'s second conjunct, demonstrated in the
V34 `_recovers_via_eq4_at_seed` side lemma, or via a future oracle/
proposal). This is a structurally cleaner separation of concerns:
the *integrated chain* is paper-axiom-free; the *single scalar
inequality* needed to close it is named explicitly at the type level.

### Note on the discharge of `hSigmaCmp` at the seed

V34's `_recovers_via_eq4_at_seed` side lemma exhibits the
**discharge route via `paper.eq4_sigmaPlus_bound`**: given a
`Section2Assumptions a b K c_value` instance, the lemma extracts
`paper.eq4_sigmaPlus_bound (r := c_value) ... .2.1` (i.e., the
second conjunct of the `eq4` bundle at `r = c`) to produce an
inhabitant of `sigmaPlus a b c_value ≤ sigmaMinus a b c_value`,
then plugs this into the new generic theorem. The resulting
conclusion is byte-for-byte identical to sprint 026's at the seed —
recovering sprint 026's exact bound through sprint 034's chain.

This side lemma serves **two roles**: (a) confirms the new theorem
is a strict generalisation of sprint 026 (any consumer with
`paper.eq4` access can recover sprint 026's bound from sprint 034);
(b) demonstrates the precise discharge route that a future
oracle-bearing consumer would substitute (replace
`paper.eq4_sigmaPlus_bound...2.1` with the oracle's witness).

### Note on the `hSummable_n1_c` premise

Sprint 032 takes `Summable (k ↦ if n1Pred a b k then coeffPlusGap·s^(2k)
else 0)` at the upper anchor `s`. Sprint 034 wants to apply sprint 032
with `s = c` (and `r ≤ c`), so we need this summability **at `c`**.
Sprint 026's existing premise `hSummable r hr_nonneg hr_lt` covers
`r < c` (open interval), not `r = c` itself. We add `hSummable_n1_c`
as a separate premise to cover the upper anchor.

In principle, `hSummable_n1_c` *could* be derived from `hSummable` if
the latter were extended to `r ≤ c`. We choose **not** to do this
because:

* Sprint 026's existing signature uses `r < c` (open) and we want
  sprint 034 to be a near-minimal-delta extension of sprint 026's
  signature (preserving consumability by existing patterns).
* The N1-indicator-restricted summability at `c` may in principle
  be **easier** to satisfy than the unrestricted summability at `c`
  (since the indicator drops the N2 contribution), so taking it as
  a separate premise gives consumers the option to discharge it
  through a different route than `hSummable`.
* Sprint 032's own contract takes summability at the upper anchor
  as a primitive premise; sprint 034 inherits the same pattern.

The premise can be derived in the V34 side lemma from `hSummable`
via `Summable.indicator` extended to `c` (using a one-radius
extension of the universal closure), or it can be supplied
externally by a downstream oracle.

### Note on hypothesis-count and analytical structure

Sprint 026 has 4 hypothesis cells (paper-bearing; `paper`, `hc_pos`,
`hc_lt_one`, `hSummable`, `hInt` — actually 5 counting `paper`).
Sprint 034 has 6 hypothesis cells (paper-axiom-free signature; no
`paper` parameter). The hypothesis-count delta is +1 (drop `paper`,
add `hSummable_n1_c` and `hSigmaCmp`). Net: hypothesis count grows
by 1; paper-axiom signature shrinks from `{eq4}` to `{}` modulo the
explicit `hSigmaCmp`.

### Note on the witness at the seed

V34's `_recovers_via_eq4_at_seed` side lemma should exhibit the
discharge of the new theorem at the seed `c = c_value = 3554/10000`,
with `hSigmaCmp` discharged by `paper.eq4_sigmaPlus_bound (r :=
c_value) ...` (the second conjunct projection `.2.1`). The other
hypotheses are discharged via existing seed scaffolding patterns
already used in sprint 026's V26 candidate.

The `_compiles` side lemma should exhibit the new theorem's
hypothesis shape with concrete `c = c_value`, mirroring V26's
`_compiles` shape with the two extra premises.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem diskExcess_upper_bound_via_series_only_modulo_sigma_compare
      {a b : ℕ → ℂ} {c : ℝ}
      (hc_pos : 0 < c)
      (hc_lt_one : c < 1)
      (hSummable :
        ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
      (hSummable_n1_c :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
          else 0))
      (hSigmaCmp :
        PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c)
      (hInt :
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        c ^ 4 * PaperAxioms.sigmaZeroMinus a b c
  ```
  Estimated location: append after sprint 033's
  `sigmaPlus_upper_via_series_convexity` (after the current end of
  `Reduction.lean`). Estimated ~80–100 lines including the chain
  through sprint 005/025/032 and the integration step.

  The proof body is structurally **sprint 026's body verbatim**
  (lines 3791–3881) with the following targeted substitutions:

  1. **Replace lines 3809–3825** (the `paper.eq4_sigmaPlus_bound`
     unfold and chain) with:
     ```lean
     -- sprint 032 supplies `sigmaPlus r ≤ sigmaPlus c` (paper-axiom-free).
     have hMono : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaPlus a b c :=
       sigmaPlus_monotone_of_summable hr_nonneg hr_lt.le hSummable_n1_c
     -- explicit hypothesis: `sigmaPlus c ≤ sigmaMinus c`.
     have hCmp : PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c :=
       hSigmaCmp
     -- sprint 005 supplies `sigmaMinus c = c² · sigmaZeroMinus c` (paper-axiom-free).
     have hIdent :
         PaperAxioms.sigmaMinus a b c = c ^ 2 * PaperAxioms.sigmaZeroMinus a b c :=
       sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b c
     have hSigmaPlus_le :
         PaperAxioms.sigmaPlus a b r ≤
           c ^ 2 * PaperAxioms.sigmaZeroMinus a b c := by
       have hChain : PaperAxioms.sigmaPlus a b r ≤ PaperAxioms.sigmaMinus a b c :=
         le_trans hMono hCmp
       rw [hIdent] at hChain
       exact hChain
     ```
  2. **Drop the `paper` parameter** from the signature (no
     `Section2Assumptions` instance needed).
  3. **Add `hSummable_n1_c` and `hSigmaCmp`** to the signature
     immediately before `hInt`.

  The remainder of the body (steps 2–6 of sprint 026: pointwise
  multiplication by `2r`, integrability of the constant-multiple-of-`r`
  RHS, integration via
  `intervalIntegral.integral_mono_on_of_le_Ioo`, closed-form RHS
  evaluation via `intervalIntegral.integral_const_mul` + `@integral_pow
  0 c 1`, identification of `diskExcess` with the integral and final
  `calc`-chain) is **byte-for-byte identical** to sprint 026's lines
  3827–3881.

- `ProofRefinement/Korenblum/Candidates/V34.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V33),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V33),
  4. Adds two side lemmas
     `v34_disk_bound_via_series_only_modulo_sigma_compare_compiles` and
     `v34_disk_bound_via_series_only_modulo_sigma_compare_recovers_via_eq4_at_seed`
     exercising the new generic theorem:
     - `_compiles` exhibits the new theorem's hypothesis shape — six
       cells: `hc_pos`, `hc_lt_one`, `hSummable`, `hSummable_n1_c`,
       `hSigmaCmp`, `hInt`. Concrete witness: instantiate at `c =
       c_value = 3554/10000`. The two summability and the
       integrability hypotheses are taken as universally-quantified
       Lean hypotheses on the side lemma; `hSigmaCmp` is also taken
       as a hypothesis (this side lemma does **not** use a `paper`
       instance).
     - `_recovers_via_eq4_at_seed` takes a `Section2Assumptions a b K
       c_value` instance, discharges `hSigmaCmp` from
       `paper.eq4_sigmaPlus_bound (r := c_value)`'s second conjunct
       projection, and applies the new theorem to recover sprint
       026's exact conclusion at the seed (`diskExcess (circleGap a
       b) c_value ≤ c_value^4 · sigmaZeroMinus a b c_value`). The
       summability and integrability hypotheses are taken as
       additional universally-quantified hypotheses on this side
       lemma.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V33).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V34` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V34.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V34 ties V33 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V34.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V34.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — the body is paper-axiom-free.
   Greppable check: in the body of
   `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`, the
   count of `paper.eq` substrings is **0**. (The lemma's signature
   also does not include a `paper : Section2Assumptions ...`
   parameter.)
7. The proof body invokes `sigmaPlus_monotone_of_summable` (sprint
   032) at least once. Greppable check: count of
   `sigmaPlus_monotone_of_summable` substrings in the body of the new
   theorem is ≥ 1.
8. The proof body invokes `circleGap_le_sigmaPlus_via_series_split`
   (sprint 025) at least once. Greppable check: count of
   `circleGap_le_sigmaPlus_via_series_split` substrings in the body
   of the new theorem is ≥ 1.
9. The proof body invokes `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
   (sprint 005) at least once. Greppable check: count of
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` substrings in the body
   of the new theorem is ≥ 1.
10. The new theorem's signature includes the explicit `hSigmaCmp :
    PaperAxioms.sigmaPlus a b c ≤ PaperAxioms.sigmaMinus a b c`
    hypothesis. Greppable check: the substring `hSigmaCmp` appears
    in the signature line region (lines containing the new theorem's
    parameter list).
11. The V34 `_recovers_via_eq4_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `paper.eq4_sigmaPlus_bound` exactly once, in the proof
    body (greppable: count of `paper.eq4_sigmaPlus_bound` in the
    body of `v34_..._recovers_via_eq4_at_seed` is exactly 1). This
    confirms the new theorem **strictly generalises** sprint 026
    (any consumer with `paper.eq4` access can recover sprint 026's
    conclusion through the new chain).
12. The proof body of the new theorem **does not invoke**
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only` (sprint
    026) or any earlier `diskExcess_upper_bound_*` lemma — the
    structural marker that sprint 034 is a fresh chain, not a
    repackaging of sprint 026's conclusion. Greppable check: count
    of `diskExcess_upper_bound_via` substrings in the body is 0.

## Out of scope

- Edit older candidates V0–V33.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V34 is the
  same `hEq15_seed_3554` that V0–V33 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land an oracle/proposal for `Σ⁺(c) ≤ Σ⁻(c)`. This is the precise
  oracle target that sprint 034 *isolates as a type-level explicit
  hypothesis* but does not itself discharge — per the bulletin's
  high-value direction #4, this is the natural next-step proposal but
  is **out of sprint 034's scope**. A future planner may file
  `Proposals/proposal_001_*.md` for this oracle if motivated.
- Materialise sprint 034 in any closing-reducer chain (i.e., do not
  re-derive any `valid_of_*` reducer using sprint 034 yet — that is
  the second-order follow-up work). Sprint 034 ships only the new
  integrated bound plus its V34 side-lemma materialisations.
- Land any other downstream consumer of sprint 032 or sprint 033
  (e.g., a paper-axiom-free re-derivation of sprint 029's pointwise
  inner-disk bound that uses sprint 032 to replace `paper.eq4`'s
  first conjunct, or a paper-axiom-free re-derivation of sprint 030
  in the same vein). These are queueable separately.
- Land the N1-side `sigmaPlus_summable_of_summable_at_upper` lemma
  (the dual of sprint 012's N2-side summability transfer; sprint
  033's "alternative K"). This would let sprint 034's
  `hSummable_n1_c` premise be derived from a single anchor at `c`
  rather than supplied directly. Out of sprint 034's scope; queueable
  separately.
- Series-derive the `IntervalIntegrable (fun r => 2*r * circleGap a
  b r) volume 0 c` premise (sprints 028/032's "alternative E").
  Requires Mathlib `MeasureTheory` archaeology; out of scope.
- Land any branch-restricted variant (`branchSplit c`-confined
  versions of sprint 034's bound).

## Time budget

≤ 75 minutes runtime. (Sprint 026's body is ~85 lines; sprint 034's
body is sprint 026's body with one targeted replacement of ~15 lines.
The extra summability-premise pass-through and `hSigmaCmp` chaining
adds ~10 lines net. V34 candidate adds ~30–40 lines per side lemma.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
