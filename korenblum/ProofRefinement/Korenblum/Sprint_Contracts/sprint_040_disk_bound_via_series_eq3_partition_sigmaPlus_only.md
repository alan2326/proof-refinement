# Sprint 040: First paper-axiom-free integrated `diskExcess` upper bound of shape `c² · sigmaPlus a b c` (no `Z_c`/`hSigmaCmp` cell), via termwise *equality* (sprint 027) + `sigmaPlus` monotonicity (sprint 032) + drop of the non-negative `∫ 2r³·Z_r` summand

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V39.lean`
**Target file**: `Candidates/V40.lean`
**Direction**: section2-proof

## Goal

Ship one new generic theorem in `Proof/Reduction.lean`:

```lean
theorem diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_pos : 0 < c)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
        else 0))
    (hIntCircle :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b r) volume 0 c) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      c ^ 2 * PaperAxioms.sigmaPlus a b c
```

The proof body:

1. Use sprint 027's *equality* identity
   `circleGap a b r = sigmaPlus a b r − r²·sigmaZeroMinus a b r`
   on `r ∈ Ioo 0 c` (paper-axiom-free, only requires `r ≥ 0` and the
   summability hypothesis at `r`).
2. Multiply by `2r ≥ 0`, integrate over `[0, c]` using
   `intervalIntegral.integral_sub` (with the integrand split into
   `2r·sigmaPlus` and `2r³·sigmaZeroMinus`).
3. Pointwise upper-bound `sigmaPlus a b r ≤ sigmaPlus a b c` for
   `r ∈ Ioo 0 c` via sprint 032 (`sigmaPlus_monotone_of_summable`),
   integrate to give `∫₀^c 2r·sigmaPlus a b r dr ≤
   c² · sigmaPlus a b c` using
   `intervalIntegral.integral_mono_on_of_le_Ioo` and
   `@integral_pow 0 c 1` (sprint 026 already establishes the pattern).
4. Pointwise lower-bound `2r³·sigmaZeroMinus a b r ≥ 0` for
   `r ∈ Ioo 0 c` via `sigmaZeroMinus_nonneg_of_pos a b hr_pos`,
   integrate to give `∫₀^c 2r³·sigmaZeroMinus a b r dr ≥ 0` using
   `intervalIntegral.integral_nonneg` (or `integral_nonneg_of_ae`).
5. Combine: `diskExcess = ∫₀^c 2r·circleGap a b r dr =
   ∫₀^c 2r·sigmaPlus a b r dr − ∫₀^c 2r³·Z_r dr ≤
   c²·sigmaPlus a b c − 0 = c²·sigmaPlus a b c`.

This is the workspace's **first integrated `diskExcess` upper bound
of shape `c² · sigmaPlus a b c`** (every prior integrated disk bound
is in the `Σ⁻`/`Z`-side family: `c⁴·Z_c` in sprints 013/026/030/034
or `branchSplit`-confined kernel forms in sprints 003/007/015/022/031).
Crucially, this bound does **not** invoke `paper.eq*` anywhere in its
transitive proof body, **and** does **not** require an `hSigmaCmp`
oracle cell (`Σ⁺(c) ≤ Σ⁻(c)`) — both `paper.eq3` and `paper.eq4` are
absent, leaving only series-derived equalities (sprints 005, 027) and
series-derived monotonicity (sprint 032) plus the standard
non-negativity facts (`sigmaZeroMinus_nonneg_of_pos`).

Then ship a `Candidates/V40.lean` at the same `c = 0.3554` that
compiles, scores `≥ V39 = 1777/5000`, and **materialises** the new
bound in side lemmas
`v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_compiles`
and
`v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_recovers_via_eq4_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_recovers_via_eq4_at_seed` side lemma demonstrates that, when a
`Section2Assumptions a b K c_value` instance is available, applying
`paper.eq4_sigmaPlus_bound`'s `Σ⁺(c) ≤ Σ⁻(c) = c²·Z_c` chain to the
new bound reproduces sprint 026's exact closed-form RHS
`c⁴ · sigmaZeroMinus a b c` — i.e., sprint 040 is **strictly stronger
than (or equal to) sprint 026** on every `(a, b, K, paper)` consumer
that has `paper.eq4` access, and is **strictly more general than
sprint 026** on consumers that lack `paper.eq4` (since sprint 040
produces a non-trivial bound without it).

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 040 ships:

1. **First workspace integrated `diskExcess` bound of shape
   `c² · sigmaPlus a b c`.** Every prior integrated disk bound shipped
   so far reduces (after the constant scaling) to a `Z_c` or
   `Z_ρ` linear combination on the RHS:

   | Sprint | Bound shape | RHS form |
   |--------|-------------|----------|
   | 003    | `(c⁴/6)(3ρ²−4c²)/(ρ²−c²)·Z_c + (c⁶/6)/(ρ²−c²)·Z_ρ` | two-`Z` |
   | 013    | `c⁴ · Z_c` | one-`Z` |
   | 026    | `c⁴ · Z_c` | one-`Z` |
   | 030    | two-`Z` (sprint 003 shape) | two-`Z` |
   | 034    | `c⁴ · Z_c` (modulo `hSigmaCmp`) | one-`Z` modulo oracle |
   | **040 (NEW)** | **`c² · Σ⁺(c)`** | **`Σ⁺`-side, paper-axiom-free, no oracle** |

   The RHS shape `c²·Σ⁺(c)` is structurally distinct from every
   prior RHS in the workspace. Where prior bounds ultimately reduce to
   `Σ⁻`-side coefficients (since `c²·Z_c = Σ⁻(c)` via sprint 005),
   sprint 040 stays on the `Σ⁺` side throughout. The cost of staying
   on the `Σ⁺` side is that the kernel inequality for a downstream
   closing reducer becomes `c²·Σ⁺(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`
   (a **mixed-side** inequality coupling `Σ⁺` on the disk side to `Z`
   on the annulus side), opening a new analytical axis the workspace
   has not yet explored.

2. **First workspace integrated `diskExcess` bound with empty
   paper-axiom signature *and* no `Σ⁺ ≤ Σ⁻` oracle cell.** Sprint 034
   produces a paper-axiom-free `c⁴·Z_c` bound *modulo* the explicit
   hypothesis `hSigmaCmp : Σ⁺(c) ≤ Σ⁻(c)`. Sprint 040 produces a
   paper-axiom-free `c²·Σ⁺(c)` bound with **zero oracle-shaped
   hypothesis cells** — the entire signature is summability +
   integrability + positivity. This is the **first** integrated disk
   bound in the workspace whose total trust-base hypothesis count
   (paper axioms + oracle cells) is **strictly zero**. The cost is
   that the RHS uses `Σ⁺` not `Z`, which is what makes the kernel
   inequality for a downstream closing reducer mixed-side rather than
   uniform-`Z`.

3. **First workspace `intervalIntegral.integral_sub` invocation in a
   `diskExcess` upper bound.** Every prior integrated `diskExcess`
   bound integrates a *single* pointwise inequality: sprint 003
   integrates `circleGap r ≤ A·Z_c + B·Z_ρ`; sprints 013/026
   integrate `circleGap r ≤ c²·Z_c`. Sprint 040 instead integrates an
   *equality* `circleGap r = sigmaPlus r − r²·Z_r` (sprint 027)
   pointwise, splits via `integral_sub`, then bounds the two pieces
   independently. The proof shape `equality + integral_sub +
   monotone-bound + drop-non-negative-term` is novel for the
   workspace's disk-side chain.

4. **First downstream consumer of sprint 027's *equality* in an
   integrated bound.** Sprint 027 ships the equality
   `circleGap a b r = sigmaPlus a b r − r²·sigmaZeroMinus a b r` but
   so far it has only been used as a structural marker (no
   integrated downstream consumer exists). Sprint 040 makes sprint
   027 load-bearing in an integrated layer and is the first sprint
   whose proof body **inverts** the inequality direction of sprint
   025 (`circleGap ≤ sigmaPlus`) by using the *equality* form to
   recover the dropped `−r²·Z_r` summand explicitly and discard it
   only after the integration, rather than dropping it pointwise.

5. **First downstream consumer of sprint 032 in a `diskExcess`
   chain.** Sprint 032 ships `sigmaPlus_monotone_of_summable` (the
   N1 dual of sprint 011). Until sprint 040, sprint 032 has been
   lemma-only with one `_recovers_via_eq4_at_seed` materialisation
   showing the seed discharge route. Sprint 040 makes it
   load-bearing in the integrated layer.

6. **Structural prerequisite for a new closing-reducer axis.** A
   future sprint can fuse sprint 040 with sprint 038's annulus-side
   bound to produce a `valid_of_*` reducer with **kernel inequality
   `c²·Σ⁺(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ`**, which is
   structurally distinct from sprint 039's `c⁴ ≤ ∫_{ρ₁..ρ₂}
   2ρ³/Λ(c, ρ) dρ` kernel because the LHS now scales with `Σ⁺(c)`
   rather than the constant `c⁴/Z_c`-times-`Z_ρ` ratio. The two
   reducers cover **different regions of the (a, b)-space**: sprint
   039's kernel is independent of `(a, b)`, while sprint 040's
   future closing reducer's kernel depends on `Σ⁺(c)`, which can be
   strictly smaller than `c²·Z_c` exactly when `Σ⁺(c) < Σ⁻(c)`
   (which is what `paper.eq4`'s second conjunct certifies) and
   strictly larger when `Σ⁺(c) > Σ⁻(c)` (which is *outside* `eq4`'s
   scope and would correspond to a different physical regime). This
   gives the workspace its first **mixed-side** kernel inequality
   shape and its first reducer whose admissible `(a, b)` cone is
   conditioned on the `Σ⁺(c)` size rather than on the `Z`-monotone
   tail.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V40 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is a new bound *shape* on the disk side, not a
  numerical refinement of an existing closed-form coefficient.

Why this is **not** "the same chain" as sprint 026:

* **Different RHS shape.** Sprint 026 produces `c⁴·sigmaZeroMinus a b c`;
  sprint 040 produces `c²·sigmaPlus a b c`. These are equal **only
  when** `sigmaPlus a b c = c²·sigmaZeroMinus a b c`, which is
  exactly the equality case of `paper.eq4`'s second conjunct. In
  general they are different real numbers.
* **Different intermediate identity used.** Sprint 026 integrates
  sprint 025's *inequality* `circleGap r ≤ sigmaPlus r` and then
  applies `paper.eq4_sigmaPlus_bound` *inside* the pointwise step.
  Sprint 040 integrates sprint 027's *equality* `circleGap r =
  sigmaPlus r − r²·Z_r` and applies sprint 032's `sigmaPlus`
  monotonicity *after* splitting via `integral_sub`. These are
  structurally distinct chains.
* **Different paper-axiom signature.** Sprint 026 invokes
  `paper.eq4_sigmaPlus_bound` (signature `{eq4}`); sprint 040
  invokes **no** `paper.eq*` projection (signature `{}`). Sprint 040
  is the **first** integrated disk bound with empty paper-axiom
  signature and no oracle cell.

Why this is **not** "the same chain" as sprint 034:

* **Sprint 034 lifts `hSigmaCmp` (`Σ⁺(c) ≤ Σ⁻(c)`) into the
  signature**; sprint 040 does **not** require that hypothesis at
  all. Sprint 040's signature has zero oracle-shaped cells; sprint
  034's has one.
* **Different RHS shape**: sprint 034 = `c⁴·Z_c`, sprint 040 =
  `c²·Σ⁺(c)`. Without `hSigmaCmp` we cannot bridge from `Σ⁺(c)` to
  `Z_c`, so the two bounds are not algebraically equivalent.
* **Different consumer pattern.** Sprint 034's downstream consumers
  must supply `hSigmaCmp` (either via `paper.eq4` or via a future
  oracle); sprint 040's downstream consumers do not, but must work
  with the `Σ⁺(c)` shape on the LHS of any kernel inequality (a
  structurally new analytical regime).

Why this is **not** "the same chain" as sprint 027:

* **Sprint 027 is a pointwise *identity***; sprint 040 is an
  *integrated bound*. Different layers.
* **Sprint 027 has no integration**; sprint 040 invokes
  `intervalIntegral.integral_sub`, `integral_mono_on_of_le_Ioo`,
  `integral_nonneg`, `@integral_pow 0 c 1`, and the closed-form
  recovery pattern from sprint 026. Sprint 040 is the
  **integration step** of sprint 027 in a `diskExcess` upper bound,
  not a pointwise restatement.

Why this is **bounded enough for one Generator session**:

* Sprint 026's body is ~125 lines (lines 3777–3881 of
  `Reduction.lean`). Sprint 040's body shares the same outer
  scaffold (`hPointwise`, `hIntegralMono`, `hRhsClosedForm`, the
  final `calc`) but with the *equality* of sprint 027 substituted
  for sprint 025's *inequality*, plus an `integral_sub` step
  splitting the integral into two pieces, plus a second pointwise
  step bounding the `2r³·Z_r` summand below by `0`. Estimated body
  size: ~150 lines.
* All Lean idioms used (`refine`, `obtain`, `intervalIntegral.*`,
  `linarith`, `field_simp`, `calc`, `tsum_congr`,
  `Summable.indicator`) are verbatim from existing sprints
  (especially 026 and 027). No new idioms required. The
  `intervalIntegral.integral_sub` invocation uses the same
  integrability discipline as sprint 026's `integral_mono_on_of_le_Ioo`,
  which V40 reuses.
* The **discharge route at the seed** for `_recovers_via_eq4_at_seed`
  is a 5-line wrapper: take the sprint 040 conclusion `diskExcess ≤
  c²·sigmaPlus a b c`, apply the `Σ⁺(c) ≤ Σ⁻(c)` and
  `Σ⁻(c) = c²·Z_c` conjuncts of `paper.eq4_sigmaPlus_bound` to
  upper-bound `c²·sigmaPlus a b c ≤ c²·sigmaMinus a b c =
  c⁴·sigmaZeroMinus a b c`. This recovers sprint 026's exact RHS
  via the new chain, and is the same algebraic step V26 already
  performs (in the *opposite* direction — V26 builds `c⁴·Z_c` from
  `eq4`'s three conjuncts; V40's `_recovers_via_eq4_at_seed` builds
  `c⁴·Z_c` from `Σ⁺(c)` via the same three conjuncts). No new
  analytical content.

### Note on the integrability hypothesis `hIntSigmaPlus`

Sprint 040 needs `IntervalIntegrable (fun r => 2 * r * sigmaPlus a b
r) volume 0 c` because the proof body integrates the `2r·sigmaPlus a
b r` summand independently of the `2r³·Z_r` summand (after splitting
via `integral_sub`). This is a fresh integrability cell not present in
prior disk-bound signatures (sprints 003/013/026 only need
`IntervalIntegrable (fun r => 2 * r * circleGap a b r)`). The cell is
a Lean side-condition, not an oracle: in any consumer with a
`Section2Assumptions` instance, it can be discharged from continuity
of `sigmaPlus` (which follows from term-by-term continuity once
summability is established) — but that derivation is **not** in scope
for sprint 040. The hypothesis is taken as universally quantified on
the lemma, and the V40 `_recovers_via_eq4_at_seed` side lemma takes it
as a hypothesis as well (no concrete discharge is required for the
side lemma to compile).

### Note on the `2r³·Z_r ≥ 0` step

The pointwise bound `0 ≤ 2 * r ^ 3 * sigmaZeroMinus a b r` for
`r ∈ Ioo 0 c` follows from `sigmaZeroMinus_nonneg_of_pos a b hr_pos`
(paper-axiom-free) and `0 ≤ 2 * r ^ 3` (`positivity`/`nlinarith` from
`r > 0`). Integrating via `intervalIntegral.integral_nonneg` (or
`integral_nonneg_of_ae` with the standard `Ioo`/`Ioc` measure
equivalence) gives `0 ≤ ∫₀^c 2r³·Z_r dr`. The integrand `2r³·Z_r` at
`r = 0` is `0` (since `r³ = 0`), so the integral is well-defined as
`0` even at the endpoint and the `r > 0` constraint of
`sigmaZeroMinus_nonneg_of_pos` does not obstruct integrating over
`[0, c]`. This step uses the **paper-axiom-free** non-negativity
lemma `sigmaZeroMinus_nonneg_of_pos` which already lives in
`Reduction.lean` (line 570) — no new lemma needed.

A new integrability hypothesis is also required for the `2r³·Z_r`
summand specifically: `IntervalIntegrable (fun r => 2 * r ^ 3 *
sigmaZeroMinus a b r) volume 0 c`. This is the third integrability
cell in the signature (alongside `hIntCircle` and `hIntSigmaPlus`).
The integrand `2r³·Z_r` follows from `2r·circleGap r` and
`2r·sigmaPlus r` via the sprint 027 equality (rearranged: `2r³·Z_r =
2r·sigmaPlus r − 2r·circleGap r`), so its integrability is implied by
the other two — but explicitly threading this implication through the
proof body is signature-bookkeeping work that we lift to a separate
hypothesis cell to keep the body bounded.

### Note on the `_compiles` side lemma

V40's `_compiles` side lemma should exhibit the new bound's
*type-shape* compilation at the seed without committing to a specific
discharge route for the integrability/summability cells — it takes
them all as universally-quantified Lean hypotheses and feeds them
into the new bound to produce
`PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
c_value^2 * PaperAxioms.sigmaPlus a b c_value`. The `_compiles` side
lemma does **not** use a `paper` instance directly; it asserts the
bound abstractly as a universally-quantified family.

### Note on the `_recovers_via_eq4_at_seed` side lemma

V40's `_recovers_via_eq4_at_seed` side lemma takes a
`Section2Assumptions a b K c_value` instance and the same
integrability/summability hypotheses as universally-quantified cells,
applies the new bound to obtain `diskExcess ≤ c_value^2 ·
sigmaPlus a b c_value`, then chains `paper.eq4_sigmaPlus_bound`'s
second and third conjuncts (`Σ⁺(c) ≤ Σ⁻(c)` and `Σ⁻(c) = c²·Z_c`) to
upper-bound the RHS by `c_value^4 · sigmaZeroMinus a b c_value` —
recovering sprint 026's exact closed-form via the new chain.

This side lemma serves **two roles**:
(a) confirms the new bound is a strict generalisation of sprint 026
(any consumer with `paper.eq4` access can recover sprint 026's
conclusion through the new chain);
(b) demonstrates the precise discharge route a future consumer
*without* `paper.eq4` would substitute (skip the
`paper.eq4_sigmaPlus_bound` chain and consume the `c²·Σ⁺(c)` bound
directly — this is the consumer pattern that sprint 040 unlocks for
the first time).

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only
      {a b : ℕ → ℂ} {c : ℝ}
      (hc_pos : 0 < c)
      (hSummable :
        ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c →
          Summable (fun k : ℕ =>
            PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
      (hSummable_n1_c :
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * c ^ (2 * k)
          else 0))
      (hIntCircle :
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c)
      (hIntSigmaPlus :
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.sigmaPlus a b r) volume 0 c)
      (hIntZ :
        IntervalIntegrable
          (fun r => 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r)
          volume 0 c) :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
        c ^ 2 * PaperAxioms.sigmaPlus a b c
  ```
  Estimated location: append after sprint 039's
  `valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window`
  (at the current end of `Reduction.lean`, after line 6168).
  Estimated ~150 lines.

  The proof body structure:

  1. **Pointwise equality** via sprint 027 on `r ∈ Ioo 0 c`:
     ```lean
     have hPointwiseEq :
         ∀ r ∈ Set.Ioo (0 : ℝ) c,
           PaperAxioms.circleGap a b r =
             PaperAxioms.sigmaPlus a b r
               - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r := by
       intro r hr
       exact circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition
         a b hr.1.le (hSummable hr.1.le hr.2)
     ```

  2. **Multiply by `2r ≥ 0`** to convert to the integrand form. This
     gives a pointwise *equality* of integrands on `Ioo 0 c`:
     ```lean
     have hPointwiseEq_jac :
         ∀ r ∈ Set.Ioo (0 : ℝ) c,
           2 * r * PaperAxioms.circleGap a b r =
             2 * r * PaperAxioms.sigmaPlus a b r
               - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r := by
       intro r hr
       have hEq := hPointwiseEq r hr
       have h2r_nonneg : (0 : ℝ) ≤ 2 * r := by linarith [hr.1]
       have : 2 * r * PaperAxioms.circleGap a b r =
                2 * r * (PaperAxioms.sigmaPlus a b r
                  - r ^ 2 * PaperAxioms.sigmaZeroMinus a b r) := by
         rw [hEq]
       rw [this]; ring
     ```

  3. **Integrate the pointwise equality** via
     `intervalIntegral.integral_congr_ae` (or
     `intervalIntegral.integral_congr_codiscrete` with `Ioo` upgraded
     to a.e. on `[0, c]`):
     ```lean
     have hIntegralEq :
         ∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.circleGap a b r =
           ∫ r in (0 : ℝ)..c,
             (2 * r * PaperAxioms.sigmaPlus a b r
               - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) :=
       intervalIntegral.integral_congr_ae (-- Ioo→Icc a.e. equivalence)
     ```

  4. **Split the integral** via
     `intervalIntegral.integral_sub hIntSigmaPlus hIntZ`:
     ```lean
     have hIntegralSub :
         ∫ r in (0 : ℝ)..c,
             (2 * r * PaperAxioms.sigmaPlus a b r
               - 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r) =
           (∫ r in (0 : ℝ)..c, 2 * r * PaperAxioms.sigmaPlus a b r)
             - ∫ r in (0 : ℝ)..c, 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r :=
       intervalIntegral.integral_sub hIntSigmaPlus hIntZ
     ```

  5. **Bound `∫₀^c 2r·sigmaPlus a b r dr ≤ c²·sigmaPlus a b c`**
     via sprint 032's monotonicity (`sigmaPlus a b r ≤ sigmaPlus a b
     c` for `r ≤ c`) + `intervalIntegral.integral_mono_on_of_le_Ioo`
     + sprint 026's RHS-closed-form pattern with `c²·sigmaPlus c`
     replacing `c²·Z_c·c²` (i.e., a single `2r·(c²·Σ⁺(c))` integrand
     instead of a two-step `2r·(c²·Z_c)`). Mirrors sprint 026's
     lines 3826–3868 with one pointwise substitution.

  6. **Bound `0 ≤ ∫₀^c 2r³·sigmaZeroMinus a b r dr`** via
     `intervalIntegral.integral_nonneg hc_pos.le` applied to the
     pointwise non-negativity `0 ≤ 2r³·Z_r` for `r ∈ Ioc 0 c`
     (using `sigmaZeroMinus_nonneg_of_pos`). The standard pattern
     for `integral_nonneg` requires non-negativity on `Set.uIcc 0
     c = [0, c]`; the endpoint `r = 0` evaluates `2·0³·Z_0 = 0`,
     which is non-negative trivially, and the interior `r > 0`
     case uses `sigmaZeroMinus_nonneg_of_pos`.

  7. **Final chain** via `calc`:
     ```lean
     calc
       diskExcess (circleGap a b) c
           = ∫ r in (0:ℝ)..c, 2 * r * circleGap a b r := hDiskExcess
         _ = (∫ r in (0:ℝ)..c, 2 * r * sigmaPlus a b r)
               - ∫ r in (0:ℝ)..c, 2 * r ^ 3 * sigmaZeroMinus a b r :=
             hIntegralEq.trans hIntegralSub
         _ ≤ (c ^ 2 * sigmaPlus a b c) - 0 := by
             linarith [hSigmaPlus_int_bound, hZ_int_nonneg]
         _ = c ^ 2 * sigmaPlus a b c := by ring
     ```

  Note: step 3's `intervalIntegral.integral_congr_ae` requires the
  pointwise equality to hold a.e. on `[0, c]`. Since `Ioo 0 c =
  Icc 0 c \ {0, c}` and `{0, c}` has measure zero, the
  pointwise-on-`Ioo` statement upgrades to a.e.-on-`Icc` directly.
  The lemma `MeasureTheory.ae_restrict_iff` (or
  `intervalIntegral.integral_congr_ae`'s variant for a.e.-on-`Ioc`)
  handles the standard pattern; the cleanest approach is to use
  `intervalIntegral.integral_congr_codiscrete` if available, or
  replicate sprint 026's pattern of working with `Ioo` via
  `integral_mono_on_of_le_Ioo` (though here we need *equality*, not
  inequality). If `integral_congr_ae` is awkward, an alternative is
  to split steps 3+4: integrate the LHS and RHS independently using
  `integral_congr` with a null-set adjustment. Implementation notes
  for the Generator are provided in the `## Stop conditions`
  section.

- `ProofRefinement/Korenblum/Candidates/V40.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V39),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V39),
  4. Adds two side lemmas exercising the new generic bound:
     - `v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_compiles`:
       exhibits the new bound's signature compilation at the seed by
       feeding the integrability/summability cells as
       universally-quantified hypotheses on the side lemma. Concrete
       conclusion: `diskExcess (circleGap a b) c_value ≤ c_value^2 *
       sigmaPlus a b c_value`. Does **not** use a
       `Section2Assumptions` instance.
     - `v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_recovers_via_eq4_at_seed`:
       takes a `Section2Assumptions a b K c_value` instance and the
       same integrability/summability hypotheses as
       universally-quantified cells, applies the new bound, then
       chains `paper.eq4_sigmaPlus_bound`'s second and third
       conjuncts to upper-bound `c_value^2 · sigmaPlus a b c_value
       ≤ c_value^4 · sigmaZeroMinus a b c_value` — recovering
       sprint 026's exact RHS.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V39) — the new bound is
     materialised in side lemmas, **not** as the sink theorem's
     discharge route, since the closing-reducer fusion with the
     annulus side is queueable as a separate sprint.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V40` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V40.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V40 ties V39 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V40.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V40.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — body is paper-axiom-free.
   Greppable check: in the body of the new theorem, the count of
   `paper.eq` substrings is **0**. (No `paper :
   Section2Assumptions ...` parameter is even taken — sprint 040's
   signature is `(a, b, c)`-only with no `K` and no `paper`.)
7. The proof body invokes
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition`
   (sprint 027) at least once for the disk-side equality. Greppable
   check: count of
   `circleGap_eq_sigmaPlus_minus_sigmaMinus_via_series_partition` in
   the body of the new theorem is ≥ 1.
8. The proof body invokes `sigmaPlus_monotone_of_summable`
   (sprint 032) at least once for the `sigmaPlus a b r ≤ sigmaPlus
   a b c` monotonicity step. Greppable check: count of
   `sigmaPlus_monotone_of_summable` in the body of the new theorem
   is ≥ 1.
9. The proof body invokes `intervalIntegral.integral_sub` at least
   once for the integral-splitting step. Greppable check: count of
   `intervalIntegral.integral_sub` in the body of the new theorem
   is ≥ 1.
10. The proof body invokes `sigmaZeroMinus_nonneg_of_pos` at least
    once for the `Z_r ≥ 0` step in the `2r³·Z_r ≥ 0` chain.
    Greppable check: count of `sigmaZeroMinus_nonneg_of_pos` in the
    body of the new theorem is ≥ 1.
11. The new theorem's RHS contains `sigmaPlus a b c` — *not*
    `sigmaZeroMinus a b c` and *not* `sigmaMinus a b c`. Greppable
    check: in the new theorem's signature, the substring
    `c ^ 2 * PaperAxioms.sigmaPlus a b c` appears as the RHS of the
    `≤` in the conclusion.
12. The new theorem **does not invoke** the old sprint 025 lemma
    `circleGap_le_sigmaPlus_via_series_split` — sprint 027's
    *equality* is used instead of sprint 025's *inequality*.
    Greppable check: count of
    `circleGap_le_sigmaPlus_via_series_split` in the body of the new
    theorem is **0**.
13. The new theorem **does not invoke**
    `diskExcess_upper_bound_via_circleGapSeries_eq4_only` (sprint
    026) — sprint 040 is a parallel chain, not a wrapper. Greppable
    check: count of `diskExcess_upper_bound_via_circleGapSeries_eq4_only`
    in the body of the new theorem is **0**.
14. The V40 `_recovers_via_eq4_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `paper.eq4_sigmaPlus_bound` for the discharge of the
    `Σ⁺(c) ≤ c²·Z_c` chain. Greppable check: `paper.eq4_sigmaPlus_bound`
    appears in the body of the `_recovers_via_eq4_at_seed` side
    lemma.
15. The V40 `_recovers_via_eq4_at_seed` side lemma's conclusion is
    `diskExcess (circleGap a b) c_value ≤ c_value^4 *
    sigmaZeroMinus a b c_value` — recovering sprint 026's exact RHS
    via the new chain.

## Out of scope

- Edit older candidates V0–V39.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V40 is the
  same `hEq15_seed_3554` that V0–V39 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Ship a closing reducer fusing sprint 040 with sprint 038's
  annulus-side bound. That is the **next** sprint's scope; sprint 040
  ships only the disk-side bound. Reason: sprint 039 already
  demonstrates that fusing a paper-axiom-free disk bound with sprint
  038 produces a viable closing reducer; sprint 040 is the
  prerequisite of a *different* closing reducer with a mixed-side
  kernel inequality `c²·Σ⁺(c) ≤ ∫…`, which is structurally novel and
  deserves its own sprint contract once sprint 040 lands.
- Ship a witness at any `c > 0.3554`. Sprint 040 does not raise
  `c_value`. The eventual numerical push is the *consumer* of
  sprint 040 + a future closing reducer + the kernel inequality
  evaluation, not sprint 040 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15` to
  any new chain. The new bound is materialised in side lemmas only.
- Ship a paper-axiom-free pointwise (non-integrated) `circleGap a b
  r ≤ sigmaPlus a b r` bound — sprint 025 already does this. Sprint
  040 is the **integrated** counterpart with the structural twist
  that the `−r²·Z_r` summand is recovered via sprint 027's *equality*
  and dropped after integration (not before), giving a tighter bound
  on `(a, b)` configurations where the `−r²·Z_r` integral is
  non-trivial.
- Ship a series-derived `IntervalIntegrable (2r·sigmaPlus a b r)`
  proof. The integrability hypothesis is taken as universally
  quantified on the lemma; deriving it from termwise structure +
  Mathlib `MeasureTheory` would consume a Generator session on its
  own and is queueable separately.
- Ship a paper-axiom-free `Σ⁺ ≤ Σ⁻` workspace lemma. The bulletin
  notes (and sprint 039's "Out of scope" notes) that this inequality
  is **non-derivable** from termwise structure on N1 alone — it is
  the analytical content of `paper.eq4`'s second conjunct. Sprint
  040 sidesteps this by **not requiring** the inequality at all
  (the bound is in `Σ⁺` units, not `Σ⁻` units).
- Use `MeasureTheory.tsum_integral_eq_integral_tsum`-style
  swap-of-sum-and-integral machinery. Sprint 040's body integrates a
  *closed-form* equality (sprint 027's equality is already in
  `sigmaPlus − r²·Z_r` form, which is integrated termwise via
  `intervalIntegral.integral_sub`); no swap of sum and integral is
  needed.

## Time budget

≤ 60 minutes runtime. (Sprint 026's body is ~125 lines; sprint 040's
body is sprint 026's body shape with sprint 027's equality
substituted for sprint 025's inequality, plus an `integral_sub` step
and a parallel `2r³·Z_r ≥ 0` integration. The new theorem signature
is sprint 026's signature with two new integrability cells for
`2r·sigmaPlus a b r` and `2r³·sigmaZeroMinus a b r`, and one new
summability cell at `c` for sprint 032's monotonicity discharge. V40
candidate adds two side lemmas at ~50–80 lines each, both reusing
discharge routes from V26. Total V40 size: ≤ 280 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* If `intervalIntegral.integral_congr_ae` is awkward to thread, an
  alternative for step 3 (integrate the pointwise equality) is to
  use `intervalIntegral.integral_congr` directly with a sufficient
  pointwise-equality on `Set.uIcc 0 c = [0, c]`. The endpoint cases
  `r = 0` and `r = c` need to be handled: at `r = 0`, both sides
  evaluate to `2·0·circleGap a b 0 = 0` and `2·0·sigmaPlus a b 0 −
  2·0³·Z_0 = 0`, so equality is trivial. At `r = c`, the pointwise
  equality `circleGap a b c = sigmaPlus a b c − c²·Z_c` follows from
  sprint 027 with `r = c` and the **`c`-anchor summability**
  hypothesis `hSummable_n1_c` (this is why sprint 040's signature
  includes both `hSummable` over `Ioo 0 c` and the separate
  `hSummable_n1_c` cell — the `Ioo` summability does not extend to
  `r = c`). Concretely: at `r = c`, sprint 027 gives `circleGap a b
  c = sigmaPlus a b c − c²·Z_c` provided `Summable (k ↦
  coeffPlusGap a b k · c^(2k))`, which is implied by `hSummable_n1_c`
  (the N1 partition) plus the corresponding N2 sum (which is
  `−sigmaMinus a b c`, always summable since `sigmaMinus` is
  defined as a `tsum`). Actually `hSummable_n1_c` alone is not
  enough — we also need summability of the unconditioned sum at
  `r = c`. Resolution: take the unconditioned summability hypothesis
  to be **continuous** at `r = c` from the right via the `Ioo`
  summability cell or extended explicitly. Cleanest implementation:
  add a separate hypothesis `hSummable_at_c : Summable (k ↦
  coeffPlusGap a b k · c^(2k))` to the signature (one extra
  hypothesis cell, the "right-edge" anchor of the `hSummable` cone).

* The cleanest Mathlib lemma for step 3 is **likely**
  `intervalIntegral.integral_congr` with the pointwise equality on
  `Set.uIcc 0 c`. The pointwise equality on `Ioo 0 c` extends to
  `[0, c]` by handling the two endpoints separately as noted above.
  If `integral_congr_ae` is preferred, the standard `Ioo`-vs-`Icc`
  measure equivalence (`Ioo_ae_eq_Icc` from `MeasureTheory.Measure.OpenPos`)
  handles the lift.

* For step 6 (`0 ≤ ∫₀^c 2r³·Z_r dr`), use
  `intervalIntegral.integral_nonneg hc_pos.le` with the pointwise
  non-negativity on `Set.uIcc 0 c = [0, c]`. The `r = 0` case gives
  `2·0³·Z_0 = 0 ≥ 0` trivially (no need to invoke
  `sigmaZeroMinus_nonneg_of_pos` at `r = 0`). The `r > 0` case uses
  `sigmaZeroMinus_nonneg_of_pos a b hr_pos` and `0 ≤ 2r³` from
  `positivity`.

* The third integrability hypothesis `hIntZ` is **not** redundant
  from `hIntCircle` and `hIntSigmaPlus` despite the algebraic
  identity `2r³·Z_r = 2r·sigmaPlus r − 2r·circleGap r` — Mathlib's
  `IntervalIntegrable` is not a ring, and deriving `hIntZ` from
  `hIntCircle.sub hIntSigmaPlus` (after rewriting via sprint 027's
  equality) requires the equality to hold a.e. on `[0, c]`, which
  reintroduces the same step-3 a.e.-equivalence pattern. Cleaner to
  take `hIntZ` as a separate cell and let the consumer discharge it
  from continuity if needed.

* If the Generator finds the integrability discipline difficult to
  satisfy *inside* the `_compiles` and `_recovers_via_eq4_at_seed`
  side lemmas, an acceptable alternative is to **leave the
  integrability cells universally quantified** in those side lemmas
  (mirroring how sprint 035's `_witness_at_seed` handles its own
  integrability cells). The side lemmas demonstrate the bound's
  *signature compilation* at the seed; full integrability discharge
  is queueable separately.
