# Sprint 014: Full-window single-`Z_c` Z-free reducer — fuse sprint 013's `diskExcess ≤ c⁴·Z_c` with sprint 006's annulus lower bound and sprint 011/012 monotonicity to ship the **first workspace reducer with no branch-split constraint and no `(ρ²−c²)` denominator**, kernel `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`

**Created**: 2026-05-02 11:17 by Planner
**Parent candidate**: `Candidates/V13.lean`
**Target file**: `Candidates/V14.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window
    {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1)
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c),
        ∃ ρ₁ ρ₂ : ℝ,
          c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
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

The proof chain, in order:

1. **Unpack** the existential and establish geometric scaffolding
   (`hρ₁_lt_one : ρ₁ < 1`, `hcρ₂ : c < ρ₂`, `hc_le_ρ₁ : c ≤ ρ₁`).

2. **Z_c ≥ 0** via sprint 005 `sigmaZeroMinus_nonneg_of_pos a b hc_pos`.

3. **Disk-side bound** via sprint 013:
   `diskExcess (circleGap a b) c ≤ c⁴ · Z_c` (`= c^4 *
   sigmaZeroMinus a b c`). Use
   `diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one hIntDisk`.

4. **Multiply the kernel inequality `c⁴ ≤ ∫ 2ρ³/Λ` by `Z_c ≥ 0`**
   to get `c⁴ · Z_c ≤ Z_c · ∫ 2ρ³/Λ`. (Use
   `mul_le_mul_of_nonneg_right hKernel hZ_c_nonneg`.)

5. **Pull `Z_c` inside the integral** via
   `intervalIntegral.integral_const_mul` (or `integral_mul_const`):
   `Z_c · ∫ 2ρ³/Λ = ∫ 2ρ³ · Z_c / Λ` (constant factor pulled in).
   This mirrors sprint 010's "Step (b)" at
   `Reduction.lean:1186-1196`. Note the symbol shape after pulling
   in: the integrand is `2 * ρ' ^ 3 / Λ K c ρ' * Z_c`, which is
   *up to associativity* the same as `2 * ρ' ^ 3 * Z_c / Λ K c ρ'`.

6. **Build pointwise monotonicity `Z_c ≤ Z_ρ'`** for every
   `ρ' ∈ Set.Icc ρ₁ ρ₂` via sprint 011's `sigmaZeroMinus_monotone_of_summable`,
   discharging the universal-summability premise via sprint 012's
   `sigmaZeroMinus_summable_of_summable_at_upper`. Specifically:

   ```lean
   have hZmono :
       ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
         PaperAxioms.sigmaZeroMinus a b c ≤
           PaperAxioms.sigmaZeroMinus a b ρ' := by
     intro ρ' hρ'
     have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
     have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
     have hc_le_ρ' : c ≤ ρ' := le_trans hc_le_ρ₁ hρ₁_le_ρ'
     have hρ'_nonneg : 0 ≤ ρ' :=
       le_of_lt (lt_of_lt_of_le hc_pos hc_le_ρ')
     have hSummable_ρ' :
         Summable (fun k : ℕ =>
           if PaperAxioms.n2Pred a b k then
             PaperAxioms.coeffMinusGap a b k * ρ' ^ (2 * k - 2)
           else 0) :=
       sigmaZeroMinus_summable_of_summable_at_upper
         hρ'_nonneg hρ'_le_ρ₂ hSummable_top
     exact sigmaZeroMinus_monotone_of_summable
       hc_pos.le hc_le_ρ' hSummable_ρ'
   ```

7. **Integrate the pointwise `Z_c ≤ Z_ρ'` to dominate the
   constant-`Z_c` integrand by the `Z_ρ'`-weighted integrand**:

   ```lean
   have hPointwise :
       ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
         2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
             PaperAxioms.sigmaZeroMinus a b c ≤
           2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
             WangOuter.paperLambda K c ρ' := by
     intro ρ' hρ'
     have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
     have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
     have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
       WangPaperSideConditions.paperLambda_pos
         (K := K) (c := c) (ρ := ρ')
     have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
     have hWeight_nonneg :
         0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
       div_nonneg hρ'3_nonneg hΛpos.le
     have hZmono_at := hZmono ρ' hρ'_in_Icc
     have hMul :
         2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
             PaperAxioms.sigmaZeroMinus a b c ≤
           2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
             PaperAxioms.sigmaZeroMinus a b ρ' :=
       mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
     have hRewrite :
         2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
             PaperAxioms.sigmaZeroMinus a b ρ' =
           2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
             WangOuter.paperLambda K c ρ' := by
       field_simp
     linarith [hMul, hRewrite.le, hRewrite.symm.le]
   ```

   Then apply `intervalIntegral.integral_mono_on_of_le_Ioo` with
   `hρ₁₂`, the integrability of the constant-`Z_c` weighted
   integrand (built from `hIntLambda.mul_const Z_c`), and
   `hIntLambdaZ`. This step is *line-for-line* the same as sprint
   010's "Step (c)" at `Reduction.lean:1199-1244`, with `ρ` replaced
   by `c` everywhere.

8. **Apply sprint 006** `annulusExcess_lower_bound_of_eq8_eq9` to
   bound the `Z_ρ'`-weighted integral by `annulusExcess`:

   ```lean
   have hAnn :=
     annulusExcess_lower_bound_of_eq8_eq9
       paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
   ```

9. **Chain steps 3 → 4 → 5 → 7 → 8** via `calc` to conclude
   `diskExcess ≤ annulusExcess`:

   ```lean
   refine ⟨hc_pos, hc_lt_one, ?_⟩
   intro a b K paper
   obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle,
       hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
     h_witness paper
   …  -- steps 1–8 as above
   change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
     PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
   calc
     PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
         ≤ c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hDisk
       _ ≤ (∫ ρ' in ρ₁..ρ₂,
               2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
             * PaperAxioms.sigmaZeroMinus a b c := hStepA
       _ = ∫ ρ' in ρ₁..ρ₂,
               2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                 * PaperAxioms.sigmaZeroMinus a b c := hStepB
       _ ≤ ∫ ρ' in ρ₁..ρ₂,
               2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                 / WangOuter.paperLambda K c ρ' := hStepC
       _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn
   ```

The fixed final theorem shape `ValidKorenblumBound c_value` is unchanged.

Then ship a `Candidates/V14.lean` at the same `c = 0.3554` that compiles,
scores `≥ V13`, and *materialises* the new lemma in two side lemmas
`v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles` and
`v14_window_witness_at_seed` (mirroring V11's
`v11_window_witness_at_seed` pattern but **without** the
`3ρ₁² ≤ 4·c²` branch-split conjunct — a structural marker that the
new reducer is full-window). The sink theorem
`korenblum_constant_search` is still discharged via `valid_of_eq15` so
the score does not regress.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions`. Sprint 013 just landed a brand-new disk-side
upper bound `diskExcess ≤ c⁴ · Z_c` that uses **only `eq3` + `eq4`**
(no `eq2`, no `Z_ρ`, no `ρ`-window, no branch-split constraint) and is
valid on the **full** disk regime `c ∈ (0, 1)`. Sprint 013's contract
explicitly queues the natural follow-up reducer:

> Composing it with sprint 006's annulus lower bound + sprint 011
> monotonicity yields a Z-free reducer over the **full window
> `[ρ₁, ρ₂] ⊂ (c, 1)`** (queued for a future sprint), with kernel
> inequality `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` — strictly cleaner
> than sprint 010's `(c⁶/6)/(ρ₁²−c²) ≤ ∫…`.

Sprint 014 is **precisely** that follow-up. It is qualitatively new
along three independent axes:

1. **First workspace reducer with no branch-split constraint.** Every
   Z-free / single-Z reducer in the workspace so far (sprints 007,
   009, 010, 011, 012) carries the constraint `3ρ² ≤ 4c²`
   (i.e. `ρ ≤ branchSplit c = √(4/3) · c`) that came from sprint
   007's branch-split sub-regime requirement. Sprint 014's reducer
   has **no such constraint** because its disk-side ingredient is
   sprint 013's `diskExcess ≤ c⁴·Z_c`, which holds on the full disk
   regime. The witness-bundle existential signature
   `c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1` has **one fewer conjunct** than
   sprint 011's
   `c < ρ₁ ∧ 3ρ₁² ≤ 4c² ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1`. This is a strict
   structural improvement: any window `[ρ₁, ρ₂] ⊂ (c, 1)` is
   admissible, including windows entirely above `branchSplit c`.

2. **First workspace kernel inequality with no `(ρ₁²−c²)` denominator.**
   Sprint 010's Z-free kernel is
   `(c⁶/6)/(ρ₁²−c²) ≤ ∫…` — pathological as `ρ₁ → c` (the LHS blows
   up). Sprints 011 and 012 inherit the same pathological denominator.
   Sprint 014's kernel `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` has **no
   denominator at all**: the LHS is a polynomial in `c` alone,
   independent of the window endpoints. This is a strict structural
   simplification — the next sprint that wants to discharge the
   kernel inequality has a much cleaner target.

3. **First workspace reducer that anchors disk-side monotonicity at
   `c` itself rather than at an interior `ρ`.** Sprint 011's reducer
   anchors at `ρ = ρ₁ > c` (left edge of the annulus window).
   Sprint 014's reducer anchors at `ρ = c` (the disk radius itself).
   This is a genuinely different reduction shape: the
   monotonicity premise becomes `Z_c ≤ Z_ρ'` for every `ρ' ∈
   [ρ₁, ρ₂]`, not `Z_ρ₁ ≤ Z_ρ'`. Combined with the no-branch-split
   improvement, this opens a new feasibility region for the Z-free
   route at any `c ∈ (0, 1)` — including values **larger than the
   seed `0.3554`** where sprint 010/011's branch-split window
   `(c, branchSplit c]` becomes pinched.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V14 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a generic reducer that holds
  for *any* paper-faithful instance and *any* window `[ρ₁, ρ₂] ⊂
  (c, 1)`.
* No concrete numerical tuple is committed; no `(ρ₁, ρ₂)` is named in
  the theorem statement. The witness lemma in V14 only verifies the
  geometric scaffolding is non-vacuous at the seed.

Why this is **not** "the same chain" as sprint 011/012:

* Sprint 011's reducer reaches sprint 010 by specialising the disk
  witness `ρ` to `ρ₁` (left edge of the annulus window). Sprint 011
  inherits sprint 010's branch-split constraint `3ρ²≤4c²` and the
  `(ρ²−c²)` denominator. Sprint 014's reducer **bypasses sprint
  010 entirely** — it composes sprint 013 (the new full-disk-regime
  bound) directly with sprint 006 + sprint 011 + sprint 012, with
  *neither* the branch-split constraint *nor* the `(ρ²−c²)`
  denominator. Two structurally different reduction shapes, both
  Z-free, but with disjoint admissible-window regimes for any fixed
  `c`.

* Sprint 012's reducer is a refinement of sprint 011 that collapses
  the universal summability premise to a single point premise at
  `ρ₂`. Sprint 014 *also* uses a single point summability premise at
  `ρ₂` (via sprint 012's lemma directly inside the proof body), but
  its closure goes through sprint 013 (single-`Z_c` disk bound)
  rather than sprint 010's `Z_ρ`-collapse on the branch-split
  sub-regime. The single-point summability premise is the only
  premise the two reducers share.

Why this is **bounded enough for one Generator session**:

* The proof uses **only existing workspace lemmas**:
  `diskExcess_upper_bound_via_eq3_eq4` (sprint 013),
  `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006),
  `sigmaZeroMinus_monotone_of_summable` (sprint 011),
  `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012),
  `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
  plus `mul_le_mul_of_nonneg_right`, `intervalIntegral.integral_mul_const`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `WangPaperSideConditions.paperLambda_pos`. Every one of these is
  *already used* in `Reduction.lean` and verified to compile.

* The proof **mirrors sprint 010's structure** at
  `Reduction.lean:1142-1267` almost line-for-line, with three
  changes: (a) the disk side uses sprint 013's `c⁴·Z_c` bound
  instead of sprint 007's
  `(c⁶/6)/(ρ²−c²)·Z_ρ` bound, (b) the kernel inequality is `c^4
  ≤ ∫…` instead of `(c⁶/6)/(ρ²−c²) ≤ ∫…`, (c) the
  monotonicity is anchored at `c` rather than at an interior `ρ`,
  using sprint 011 + sprint 012 inline rather than as an explicit
  premise. Estimate: ~80 lines of Lean (vs ~125 for sprint 010).

* The two candidate side lemmas are short:
  `v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles`
  is one line, and `v14_window_witness_at_seed` is ≤ 5 lines.

* No new Mathlib lemmas needed beyond those already used in sprints
  005, 006, 010, 011, 012. Risk of "Mathlib lemma name mismatch" is
  essentially zero.

Why this beats the obvious alternatives I considered:

* **A: closed-form `sigmaZeroMinus(0)` series identity.** Compute
  `sigmaZeroMinus a b 0` in closed form via the series structure
  (`0^(2k-2)` is `1` only at `k=1`, where `2k-2=0`, and `0` for
  `k ≥ 2`). Sprint 013's contract noted this in its "alternative D"
  — combining with `eq2` at `r = 0` to upper-bound `Z_c` gives a
  strictly *worse* disk bound than sprints 003/007 in their
  respective regimes. Demoted: structural novelty without a useful
  downstream consumer.

* **B: parallel `eq3+eq4` *annulus*-side lower bound on `circleGap r`
  for `r ∈ (c, 1)`.** As noted in sprint 013's "Out of scope": `eq4`
  requires `r < c`, so it does not apply on the annulus side. A
  symmetric annulus bound would need a different paper hypothesis
  chain (essentially sprint 005's chain via `eq8 + eq9`). Demoted:
  not actually applicable.

* **C: discharge the `IntervalIntegrable` premise on
  `(fun ρ' => 2ρ'³/Λ(c,ρ'))` over `[ρ₁, ρ₂]` via continuity of
  `paperLambda`.** Requires
  `WangPaperSideConditions.paperLambda_continuous` (or equivalent),
  which lives **outside the workspace allowlist** — same blocker as
  sprint 011 candidate A and sprint 012 candidate A. Would require a
  `Proposals/` entry. Demoted because it requires a non-oracle trust
  expansion that is not approved.

* **D: a series-side closed-form upper bound on `sigmaZeroMinus a b c`
  in terms of a coefficient norm `M = sup_k ‖b k‖`.** Could replace
  the `Z_c` term in sprint 013's bound with an explicit numerical
  envelope. However, this needs an ambient hypothesis on `(a_k, b_k)`
  that is not part of `Section2Assumptions`. Even if it were available,
  the resulting closed-form bound `c⁴ · M²` is *uniform across all
  Section 2 instances*, but `annulusExcess` is *not* uniform across
  instances, so the comparison `c⁴ · M² ≤ annulusExcess` cannot be
  closed without further structural assumptions. Demoted: speculative
  + needs ambient hypothesis not in the trust surface.

* **E: prove `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` symbolically at
  `c = 0.3554` for some specific window**, e.g. via a Mathlib closed-
  form antiderivative + a closed-form bound on `Λ(c, ρ)`. The
  antiderivative side is doable (`∫ 2ρ³ dρ = ρ⁴/2`), but `Λ(c, ρ)`
  is opaque in `Section2Assumptions` — bounding it from above
  requires `WangCertificateCore.paperLambda_le_of_witness` which is
  **not on the allowlist** (same trust-expansion blocker as C).
  Demoted.

* **F: branch-2 mirror of sprint 008** on `(branchSplit c, 1)`. Pure
  flavour-clone of sprint 008, exactly the "three flavours of the
  same chain" pattern the bulletin warns against. Demoted.

* **G: prove `Eq15ScalarBound` in Lean for `c = 0.3554` symbolically**
  to remove the `hEq15_seed_3554` axiom. Pure numerical push against
  the existing chain — exactly what the bulletin de-prioritises.

* **H: a third series-level lemma about `sigmaZeroMinus`** —
  e.g. continuity of `s ↦ sigmaZeroMinus a b s` on `[0, 1)`.
  Genuinely novel series-side axis but **speculative** — the workspace
  doesn't currently consume continuity of `sigmaZeroMinus` anywhere,
  and the natural application (continuity at `c` to derive
  integrability of `r ↦ 2r·sigmaZeroMinus a b r` over `[0, c]`)
  requires both bounding the partial sums uniformly and applying
  uniform-convergence of power series — non-trivial. Better to file
  as a future sprint after a concrete consumer is identified.
  Demoted to "future / needs concrete consumer first".

Compared to A–H, candidate I (this sprint) maximises analytical
novelty per bounded Generator session: it ships the **first workspace
Z-free reducer with no branch-split constraint and no `(ρ²−c²)`
denominator**, fuses **four** existing workspace lemmas (sprints
005, 006, 011, 012, 013) into a coherent `ValidKorenblumBound`-closing
chain that sprint 013 explicitly queued, and uses **only existing
trusted modules + pinned Mathlib** in patterns already verified by
sprints 005–013. No proposal needed.

### Note on why the disk-side anchoring at `c` is structurally cleaner than at `ρ₁`

Sprint 011's anchoring at `ρ = ρ₁` makes the monotonicity premise
`Z_ρ₁ ≤ Z_ρ'` for `ρ' ∈ [ρ₁, ρ₂]`, which only needs monotonicity
*within* the window. Sprint 014's anchoring at `ρ = c` makes the
monotonicity premise `Z_c ≤ Z_ρ'` for `ρ' ∈ [ρ₁, ρ₂]`, which needs
monotonicity from the *outer-disk-radius* `c` up to the
*annulus-window* `[ρ₁, ρ₂]`. The latter is a *strictly stronger*
monotonicity — but sprint 011's monotonicity lemma
`sigmaZeroMinus_monotone_of_summable` discharges it directly under
`c ≤ ρ' ∧ Summable (… ρ' …)`, with no extra structural hypotheses.

### Note on the kernel inequality scaling at the seed

At `c = 0.3554`, the new kernel inequality `c⁴ ≤ ∫…` evaluates to
roughly `0.3554⁴ ≈ 0.01595`. The sprint 010 kernel inequality
`(c⁶/6)/(ρ₁²−c²) ≤ ∫…` at `(c, ρ₁) = (0.3554, 0.4)` evaluates to
`0.3554⁶/(6 · (0.4² − 0.3554²)) ≈ 0.002016 / (6 · 0.03372) ≈
0.00997`. So sprint 014's kernel LHS is **larger** at this specific
window — but this is offset by two structural advantages: (a) sprint
014 admits any `(ρ₁, ρ₂) ⊂ (c, 1)`, including windows where sprint
010's denominator becomes small (and its LHS becomes large),
and (b) sprint 014's LHS is *constant in `(ρ₁, ρ₂)`*, while
sprint 010's LHS *blows up* as `ρ₁ → c`. The two reducers are
incomparable: each is preferable in a different region of the
window-parameter space. A future numerical sprint that searches over
`(ρ₁, ρ₂)` to find the tightest window may legitimately prefer
sprint 014 in some sub-regions and sprint 010/011 in others.

This sprint **does not** discharge the kernel inequality. It only
ships the structural reducer; numerical/symbolic discharge of the
kernel is a separate future sprint.

### Note on why the single-point summability premise at `ρ₂` is reused

Sprint 014's reducer needs monotonicity `Z_c ≤ Z_ρ'` for every
`ρ' ∈ [ρ₁, ρ₂]`. By sprint 011, this requires `Summable (…
ρ' …)` for every such `ρ'`. By sprint 012, a single
`Summable (… ρ₂ …)` premise dominates the universal version. So
sprint 014 carries exactly **one** summability premise — at `ρ₂` —
identical in shape to sprint 012's. A future sprint that discharges
the single-point summability premise (e.g. via a geometric tail bound
on `(b_k - a_k)`) discharges it for **both** sprint 012's and sprint
014's reducers simultaneously.

## Concrete edits expected

* `ProofRefinement/Korenblum/Proof/Reduction.lean`:

  * Add the new generic theorem
    `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` matching the
    shape above. The proof body must:

    1. `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`.
    2. `obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hIntDisk, hIntCircle,
        hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ := h_witness paper`.
    3. Establish geometric scaffolding:

       ```lean
       have hρ₁_lt_one : ρ₁ < 1 := lt_of_le_of_lt hρ₁₂ hρ₂_lt_one
       have hcρ₂ : c < ρ₂ := lt_of_lt_of_le hcρ₁ hρ₁₂
       have hc_le_ρ₁ : c ≤ ρ₁ := hcρ₁.le
       ```
    4. Disk-side bound via sprint 013:

       ```lean
       have hDisk :=
         diskExcess_upper_bound_via_eq3_eq4 paper hc_pos hc_lt_one hIntDisk
       ```
    5. `Z_c ≥ 0`:

       ```lean
       have hZ_c_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b c :=
         sigmaZeroMinus_nonneg_of_pos a b hc_pos
       ```
    6. Multiply kernel by `Z_c`:

       ```lean
       have hStepA :
           c ^ 4 * PaperAxioms.sigmaZeroMinus a b c ≤
             (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
               * PaperAxioms.sigmaZeroMinus a b c :=
         mul_le_mul_of_nonneg_right hKernel hZ_c_nonneg
       ```
    7. Pull `Z_c` inside the integral:

       ```lean
       have hStepB :
           (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
               * PaperAxioms.sigmaZeroMinus a b c =
             ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                   * PaperAxioms.sigmaZeroMinus a b c :=
         (intervalIntegral.integral_mul_const
             (PaperAxioms.sigmaZeroMinus a b c)
             (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')).symm
       ```
    8. Build pointwise `Z_c ≤ Z_ρ'` via sprint 011 + sprint 012:

       ```lean
       have hZmono :
           ∀ ρ' ∈ Set.Icc ρ₁ ρ₂,
             PaperAxioms.sigmaZeroMinus a b c ≤
               PaperAxioms.sigmaZeroMinus a b ρ' := by
         intro ρ' hρ'
         have hρ'_le_ρ₂ : ρ' ≤ ρ₂ := (Set.mem_Icc.mp hρ').2
         have hρ₁_le_ρ' : ρ₁ ≤ ρ' := (Set.mem_Icc.mp hρ').1
         have hc_le_ρ' : c ≤ ρ' := le_trans hc_le_ρ₁ hρ₁_le_ρ'
         have hρ'_nonneg : 0 ≤ ρ' :=
           le_of_lt (lt_of_lt_of_le hc_pos hc_le_ρ')
         have hSummable_ρ' :=
           sigmaZeroMinus_summable_of_summable_at_upper
             hρ'_nonneg hρ'_le_ρ₂ hSummable_top
         exact sigmaZeroMinus_monotone_of_summable
           hc_pos.le hc_le_ρ' hSummable_ρ'
       ```
    9. Build the constant-`Z_c` weighted integrand integrability and
       the `Ioo`-pointwise bound, then apply
       `intervalIntegral.integral_mono_on_of_le_Ioo`:

       ```lean
       have hIntLambda_mul :
           IntervalIntegrable
             (fun ρ' => 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                 * PaperAxioms.sigmaZeroMinus a b c) volume ρ₁ ρ₂ :=
         hIntLambda.mul_const (PaperAxioms.sigmaZeroMinus a b c)
       have hPointwise :
           ∀ ρ' ∈ Set.Ioo ρ₁ ρ₂,
             2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
                 PaperAxioms.sigmaZeroMinus a b c ≤
               2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                 WangOuter.paperLambda K c ρ' := by
         intro ρ' hρ'
         have hρ'_in_Icc : ρ' ∈ Set.Icc ρ₁ ρ₂ := ⟨hρ'.1.le, hρ'.2.le⟩
         have hcρ' : c < ρ' := lt_of_lt_of_le hcρ₁ hρ'.1.le
         have hΛpos : 0 < WangOuter.paperLambda K c ρ' :=
           WangPaperSideConditions.paperLambda_pos
             (K := K) (c := c) (ρ := ρ')
         have hρ'3_nonneg : 0 ≤ 2 * ρ' ^ 3 := by positivity
         have hWeight_nonneg :
             0 ≤ 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' :=
           div_nonneg hρ'3_nonneg hΛpos.le
         have hZmono_at := hZmono ρ' hρ'_in_Icc
         have hMul :
             2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
                 PaperAxioms.sigmaZeroMinus a b c ≤
               2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
                 PaperAxioms.sigmaZeroMinus a b ρ' :=
           mul_le_mul_of_nonneg_left hZmono_at hWeight_nonneg
         have hRewrite :
             2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ' *
                 PaperAxioms.sigmaZeroMinus a b ρ' =
               2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                 WangOuter.paperLambda K c ρ' := by
           field_simp
         linarith [hMul, hRewrite.le, hRewrite.symm.le]
       have hStepC :
           (∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                   * PaperAxioms.sigmaZeroMinus a b c) ≤
             ∫ ρ' in ρ₁..ρ₂,
                 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                   WangOuter.paperLambda K c ρ' :=
         intervalIntegral.integral_mono_on_of_le_Ioo hρ₁₂ hIntLambda_mul
           hIntLambdaZ hPointwise
       ```
    10. Annulus-side lower bound via sprint 006:

        ```lean
        have hAnn :=
          annulusExcess_lower_bound_of_eq8_eq9
            paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
        ```
    11. Final `calc` chain:

        ```lean
        change PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
          PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
        calc
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c
              ≤ c ^ 4 * PaperAxioms.sigmaZeroMinus a b c := hDisk
            _ ≤ (∫ ρ' in ρ₁..ρ₂,
                    2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ')
                  * PaperAxioms.sigmaZeroMinus a b c := hStepA
            _ = ∫ ρ' in ρ₁..ρ₂,
                    2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'
                      * PaperAxioms.sigmaZeroMinus a b c := hStepB
            _ ≤ ∫ ρ' in ρ₁..ρ₂,
                    2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ' /
                      WangOuter.paperLambda K c ρ' := hStepC
            _ ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnn
        ```

  * Add a one-paragraph module-doc comment above the new theorem
    explaining: sprint 014's `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`
    is the workspace's **first Z-free reducer with no branch-split
    constraint and no `(ρ²−c²)` denominator**. It composes sprint 013's
    full-disk-regime single-`Z_c` disk bound with sprint 006's annulus
    lower bound and sprint 011/012's series-level monotonicity +
    summability transfer. The kernel inequality is the cleanest in the
    workspace: `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ`, with the LHS a
    polynomial in `c` alone (no `ρ`, no denominator) and the RHS a
    pure paper-`Λ` integral. The admissible-window region is the
    full open annulus `(c, 1)`, not just `(c, branchSplit c]`.

  * The body of `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window`
    MAY invoke:

    * `diskExcess_upper_bound_via_eq3_eq4` (sprint 013),
    * `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006),
    * `sigmaZeroMinus_monotone_of_summable` (sprint 011),
    * `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012),
    * `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
    * `WangPaperSideConditions.paperLambda_pos`,
    * `intervalIntegral.integral_mul_const`,
    * `intervalIntegral.integral_mono_on_of_le_Ioo`,
    * `IntervalIntegrable.mul_const`,
    * `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`,
      `div_nonneg`, `le_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`,
      `linarith`, `field_simp`, `positivity`,
    * `Set.mem_Icc`, `Set.Icc_subset_Icc`, `change`.

    The body must **NOT** invoke any of the following forbidden
    references (verify via `grep -nE` against the substring of the
    theorem body):

    * `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`,
      `paper.eq6_`, `paper.eq7_`, `paper.eq8_`, `paper.eq9_`,
      `paper.eq10_`, `paper.eq11_`, `paper.eq12_`, `paper.eq13_`,
      `paper.eq14_`, `paper.eq15_` (the proof reaches the paper
      hypotheses **only** transitively through sprint 013 / sprint 006 /
      sprint 011 / sprint 012 / sprint 005, never directly),
    * `valid_of_eq15`, `valid_of_eq12_eq13`,
      `valid_of_eq2_eq3_eq4_annulus_budget`,
      `valid_of_eq10_subinterval_branch1`,
      `valid_of_collapsed_disk_eq8_eq9_lower`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
      `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
      `eq15_implies_disk_le_annulus`,
      `circleGap_inner_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_of_eq2_eq3_eq4`,
      `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
      `circleGap_outer_lower_bound_of_eq8_eq9`,
      `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
    * `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
      `Korenblum.scalarIntegrand2`, `branchSplit`,
      `branch1SigmaKernel`, `branch1PointwiseFactor`,
      `branch2PointwiseFactor`, `liftGap`,
      `branchSplit c`, `3 * ρ` (in the sense of a `3*ρ²≤4c²`-shaped
      conjunct).

    The new theorem's signature MUST take *only* the arguments shown
    in the goal. It MUST NOT contain any `branchSplit`-related or
    `3 * _ ^ 2 ≤ 4 * _ ^ 2`-shaped premise — the absence of any
    branch-split conjunct is the structural marker that this reducer
    is full-window. Verify by `grep -F '3 *' …` returning nothing
    that looks like a branch-split conjunct in the witness existential.

* `ProofRefinement/Korenblum/Candidates/V14.lean`:

  * `-- @parent V13`.

  * Set `def c_value : ℝ := 3554 / 10000` (same as V0–V13).

  * Reuse the seed axiom name `hEq15_seed_3554` (declare locally,
    exactly as in V1–V13).

  * Prove the final sink theorem via `valid_of_eq15` (so the score
    does not regress).

  * Additionally, prove a *verifying* side lemma that exercises the
    new reducer at the seed `c_value` against an abstract witness
    bundle:

    ```lean
    theorem v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles
        (h_witness :
          ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
            (paper : Section2Assumptions a b K c_value),
            ∃ ρ₁ ρ₂ : ℝ,
              c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
                IntervalIntegrable
                  (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ') volume c_value 1 ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                IntervalIntegrable
                  (fun ρ' => 2 * ρ' ^ 3
                    / WangOuter.paperLambda K c_value ρ') volume ρ₁ ρ₂ ∧
                Summable (fun k : ℕ =>
                  if PaperAxioms.n2Pred a b k then
                    PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k - 2)
                  else 0) ∧
                c_value ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂,
                                2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
        ValidKorenblumBound c_value :=
      valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window
        c_value_pos c_value_lt_one h_witness
    ```

  * Additionally, prove a tiny structural witness lemma confirming
    the geometric scaffolding `c_value < ρ₁ ≤ ρ₂ < 1` (note: **no**
    `3ρ₁² ≤ 4·c²` conjunct) is non-vacuous at the seed:

    ```lean
    theorem v14_window_witness_at_seed :
        ∃ ρ₁ ρ₂ : ℝ, c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 := by
      refine ⟨5 / 10, 7 / 10, ?_, ?_, ?_⟩ <;>
        norm_num [c_value]
    ```

    The pair `(5/10, 7/10)` deliberately picks a window with
    `ρ₁ = 0.5 > branchSplit(0.3554) ≈ 0.4103`, so it lies **outside**
    the branch-split sub-regime — a strict structural marker that the
    new reducer admits windows that sprints 010/011/012 cannot. The
    witness lemma is local to V14 and is not used elsewhere; its
    purpose is to demonstrate that the geometric scaffolding of the
    new reducer's `h_witness` premise is non-vacuous at the seed
    `c_value` and *outside* the branch-split sub-regime.

  * Both side lemmas must NOT be `axiom`-ed and must NOT call the
    seed axiom. They exist purely to verify that the new lemma
    typechecks at the seed `c_value`.

* No edits to `Proof/CandidateContract.lean`, no edits to
  `Proof/Main.lean`, no edits to `Proof/ProblemAxioms.lean`, no edits
  to `KorenblumPaper/*`, no edits to `lemma.toml`, no edits to
  `Candidates/V0.lean`–`V13.lean`, no edits to
  `Sprint_Contracts/sprint_001…sprint_013`.

### Note on the `IntervalIntegrable.mul_const` invocation

The integrability `hIntLambda.mul_const Z_c` produces the integrability
of `fun ρ' => (2*ρ'³/Λ(c,ρ')) * Z_c`. Lean may unfold the function
and require a `funext`/`congr` step to match the goal. The pattern
mirrors sprint 010 at `Reduction.lean:1199-1203` verbatim, so if a
unification issue arises, copy that pattern.

### Note on the `field_simp` rewrite

The pointwise step's rewrite
`(2ρ'³/Λ) * Z_ρ' = 2ρ'³·Z_ρ'/Λ` is a routine `field_simp` (mirroring
sprint 010 at `Reduction.lean:1229-1234`). If `field_simp` over-
normalises the form, the fallback is `rw [mul_div_assoc']; ring`.
Sprint 010's exact pattern works in the pinned Mathlib.

### Note on the chain shape

The proof produces a 4-step `calc` chain
(`diskExcess ≤ c⁴·Z_c ≤ Z_c · ∫ 2ρ³/Λ = ∫ Z_c · 2ρ³/Λ ≤ ∫ Z_ρ' · 2ρ³/Λ
≤ annulusExcess`). Lean's `calc` requires each step's RHS to match
the next step's LHS *syntactically*; if associativity issues arise
(e.g. `Z_c * (∫…)` vs `(∫…) * Z_c`), use `mul_comm` or `ring_nf` to
align the shapes. Sprint 010's `calc` at `Reduction.lean:1252-1263`
demonstrates the same alignment pattern — mirror it.

### Note on the witness window choice `(5/10, 7/10)`

At the seed `c_value = 0.3554`:
* `branchSplit(0.3554) = √(4/3) · 0.3554 ≈ 0.4103`.
* `(5/10, 7/10) = (0.5, 0.7)` satisfies `c_value < 0.5 ≤ 0.7 < 1`.
* `ρ₁ = 0.5 > 0.4103 = branchSplit(c_value)`, so the window is
  **outside** the branch-split sub-regime — a structural marker.

This window is **deliberately** chosen to lie outside `(c, branchSplit
c]` to demonstrate that V14's reducer admits windows that V11/V12's
reducers cannot. If `norm_num` cannot close one of the three
inequalities, fall back to `refine ⟨_, ?_, ?_, ?_⟩` and discharge
each individually with `norm_num` or `nlinarith`.

## Acceptance criteria

1. `bash korenblum/scripts/korenblum_lake_build.sh Candidates/V14.lean` succeeds.
2. `bash korenblum/scripts/korenblum_eval_candidate.sh Candidates/V14.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e. V14 scores `≥` V13 and uses the same `c_value`).
4. The evaluator's `axioms_used` set is exactly
   `{propext, Classical.choice, Quot.sound, ProofRefinement.Korenblum.Candidates.V14.hEq15_seed_3554}`
   (plus optional `Lean.ofReduceBool`/`Lean.trustCompiler` if the build
   emits them) — no new free-floating axioms.
5. `grep -n 'valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window' korenblum/ProofRefinement/Korenblum/Proof/Reduction.lean`
   returns at least one definition site. The body of the definition contains:
   * exactly one use of `diskExcess_upper_bound_via_eq3_eq4` (sprint 013),
   * exactly one use of `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006),
   * at least one use of `sigmaZeroMinus_monotone_of_summable` (sprint 011),
   * at least one use of `sigmaZeroMinus_summable_of_summable_at_upper` (sprint 012),
   * at least one use of `sigmaZeroMinus_nonneg_of_pos` (sprint 005),
   * at least one use of `intervalIntegral.integral_mul_const`,
   * at least one use of `intervalIntegral.integral_mono_on_of_le_Ioo`,
   * at least one use of `WangPaperSideConditions.paperLambda_pos`,
   * no reference to `paper.eq2`, `paper.eq3`, `paper.eq4`,
     `paper.eq5`, `paper.eq6`, `paper.eq7`, `paper.eq8`, `paper.eq9`,
     `paper.eq10`, `paper.eq11`, `paper.eq12`, `paper.eq13`,
     `paper.eq14`, `paper.eq15`.
6. `grep -n 'valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window\|v14_window_witness_at_seed' korenblum/ProofRefinement/Korenblum/Candidates/V14.lean`
   returns at least two distinct matches (V14 invokes the new lemma
   in `v14_valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window_compiles`
   and exercises the window witness).
7. The body of `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` does
   NOT mention any of the forbidden references listed in "Concrete
   edits expected" (verify via `grep -nE` against the substring of the
   theorem body):
   `paper.eq2_`, `paper.eq3_`, `paper.eq4_`, `paper.eq5_`, `paper.eq6_`,
   `paper.eq7_`, `paper.eq8_`, `paper.eq9_`, `paper.eq10_`, `paper.eq11_`,
   `paper.eq12_`, `paper.eq13_`, `paper.eq14_`, `paper.eq15_`,
   `valid_of_eq15`, `valid_of_eq12_eq13`,
   `valid_of_eq2_eq3_eq4_annulus_budget`,
   `valid_of_eq10_subinterval_branch1`,
   `valid_of_collapsed_disk_eq8_eq9_lower`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge`,
   `valid_of_collapsed_disk_eq8_eq9_lower_Z_free_atLeftEdge_uniformSummable`,
   `eq15_implies_disk_le_annulus`,
   `circleGap_inner_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_of_eq2_eq3_eq4`,
   `diskExcess_upper_bound_collapsed_single_Z_of_eq2_eq3_eq4`,
   `circleGap_outer_lower_bound_of_eq8_eq9`,
   `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`,
   `Korenblum.scalarCriterion`, `Korenblum.scalarIntegrand1`,
   `Korenblum.scalarIntegrand2`, `branchSplit`,
   `branch1SigmaKernel`, `branch1PointwiseFactor`,
   `branch2PointwiseFactor`, `liftGap`.
8. The new `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` lemma's
   signature does NOT contain any `branchSplit`-related or
   `3 * _ ^ 2 ≤ 4 * _ ^ 2`-shaped premise — verify by inspecting the
   signature. The witness existential should contain exactly the
   conjuncts: `c < ρ₁`, `ρ₁ ≤ ρ₂`, `ρ₂ < 1`, four `IntervalIntegrable`
   conjuncts, one `Summable` conjunct, and one `c^4 ≤ ∫…` conjunct.
   This is the structural marker that the reducer is full-window.
9. The kernel-inequality conjunct of the witness existential is
   exactly `c ^ 4 ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / WangOuter.paperLambda K c ρ'`
   (verify via `grep` of the theorem statement) — no `(c^6/6)` factor,
   no `(ρ²−c²)` denominator, no `Z`-multiplier.
10. The body of `v14_window_witness_at_seed` produces the witness
    `(5/10, 7/10)` (verify via `grep -F '5 / 10' …` and
    `grep -F '7 / 10' …` in `Candidates/V14.lean`). This is the
    structural marker that V14's exercised window is **outside** the
    branch-split sub-regime.

## Out of scope

* Changing `c_value` away from `3554 / 10000`.
* Editing `Candidates/V0.lean`–`V13.lean`, or any file in
  `KorenblumPaper/`.
* Touching `lemma.toml` (no new oracles, no new seed axioms, no new
  import allowances).
* Discharging *any* of the explicit premises in the new reducer's
  `h_witness`: the four integrability premises, the single-point
  summability premise, or the kernel inequality premise. They are
  intentionally taken as explicit premises packed into `h_witness`.
  Deriving any of them in-house from `Section2Assumptions` is the
  subject of separate future sprints.
* Discharging the kernel inequality
  `c^4 ≤ ∫ ρ' in ρ₁..ρ₂, 2(ρ')^3 / paperLambda K c ρ' dρ'` itself.
  That is the explicit subject of a future sprint (numerical oracle,
  closed-form `paperLambda` envelope substitution after a trust-base
  proposal, or symbolic antiderivative).
* Discharging the single-point summability premise. Same as in
  sprint 012.
* Choosing any other concrete `(ρ₁, ρ₂)` pair beyond the V14 witness
  lemma `v14_window_witness_at_seed`. The free parameters must remain
  `forall`-quantified inside `h_witness`.
* Refactoring or simplifying sprints 001–013. Their lemmas are
  consumed verbatim (sprint 014 only *adds* one new reducer).
* Replacing the seed `valid_of_eq15` discharge of the sink theorem
  with a proof via the new reducer. That requires discharging the
  kernel inequality, the integrability premises, and the
  single-point summability premise at the seed `c_value`, which is
  the subject of multiple future sprints.
* Pushing `c_value` upward in this sprint — the goal is the structural
  full-window Z-free reducer, not a numerical push.
* Adding new Wang-paper axioms, new oracle entries, or any new
  `Proposals/` entry. This sprint must be self-contained against the
  current trust surface.
* Touching `Numerical_Library/`. Sprint 014 is purely structural —
  numerical work belongs in a separate sprint that follows.
* Adding a *right-edge* variant `_atRightEdge` with `Z` anchored at
  `ρ = ρ₂`. As noted in sprint 011's contract, this would require an
  *anti*-monotonicity statement on `sigmaZeroMinus`, which is false.
  The right-edge specialisation is not a useful reducer.
* Building a *parallel* reducer that uses sprint 003's two-`Z` disk
  bound + sprint 006's annulus bound. That reducer would inherit
  sprint 003's free `ρ`-parameter on the disk side, producing a
  *worse* witness shape (more conjuncts, more parameters). Sprint
  014's whole structural advantage comes from sprint 013's
  `ρ`-parameter-free disk side.

## Time budget

≤ 35 minutes runtime. The new reducer is ~80 lines of Lean,
roughly 30% smaller than sprint 010's `valid_of_collapsed_disk_eq8_eq9_lower_Z_free`
(~125 lines) because the disk side is one-line via sprint 013 and the
annulus side is one-line via sprint 006. All Mathlib idioms used
(`mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left`,
`intervalIntegral.integral_mul_const`,
`intervalIntegral.integral_mono_on_of_le_Ioo`,
`IntervalIntegrable.mul_const`, `WangPaperSideConditions.paperLambda_pos`,
`field_simp`, `linarith`, `positivity`) are *already verified* in
sprints 005, 006, 010 at `Reduction.lean:514-1267`. The candidate
side lemmas are one to three lines each. The structural witness
lemma is ≤ 5 lines.

## Stop conditions

* Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
* `intervalIntegral.integral_mul_const` may have a different argument
  order in pinned Mathlib — sprint 010 uses
  `(intervalIntegral.integral_mul_const Z_ρ (fun ρ' => …)).symm` at
  `Reduction.lean:1194-1196`. Mirror that exactly.
* `IntervalIntegrable.mul_const` requires the constant on the right —
  sprint 010 uses `hIntLambda.mul_const (sigmaZeroMinus a b ρ)` at
  `Reduction.lean:1202`. Mirror that exactly.
* `intervalIntegral.integral_mono_on_of_le_Ioo` requires
  `IntervalIntegrable` for *both* sides plus the pointwise bound on
  the open interval `Set.Ioo ρ₁ ρ₂`. The pattern is *already* used at
  `Reduction.lean:1243-1244` in sprint 010 with the exact arguments
  `(hρ₁₂, hIntLambda_mul, hIntLambdaZ, hPointwise)`. Mirror that
  signature.
* `field_simp` may over-normalise the rewrite
  `(2ρ'³/Λ)·Z_ρ' = 2ρ'³·Z_ρ'/Λ`; if so, fall back to
  `rw [mul_div_assoc']; ring` or split the rewrite manually with
  `have hΛne : Λ K c ρ' ≠ 0 := ne_of_gt hΛpos; field_simp [hΛne]`.
* `mul_le_mul_of_nonneg_right` requires the LHS multiplied first
  (i.e. `a ≤ b → 0 ≤ c → a * c ≤ b * c`). Sprint 010 uses it at
  `Reduction.lean:1183-1185`. The variant
  `mul_le_mul_of_nonneg_left` requires the constant on the left
  (i.e. `a ≤ b → 0 ≤ c → c * a ≤ c * b`). Use the appropriate one
  for each step's argument order.
* The final `calc` chain may have associativity mismatches between
  steps (e.g. `Z_c * (∫…)` vs `(∫…) * Z_c`). Sprint 010's pattern at
  `Reduction.lean:1252-1263` aligns shapes via `mul_comm` or
  `ring_nf`. If a step fails, insert a `ring`/`ring_nf` step.
* The `change` step before the `calc` chain requires the goal shape to
  match `diskExcess ≤ annulusExcess`. After
  `refine ⟨hc_pos, hc_lt_one, ?_⟩; intro a b K paper`, the goal is
  `diskExcess paper.circleGap c ≤ annulusExcess paper.circleGap c`.
  Sprint 009 uses `change PaperAxioms.diskExcess … ≤
  PaperAxioms.annulusExcess …` at `Reduction.lean:1116-1117`. Mirror
  that exactly. If the `paper.circleGap` form vs
  `PaperAxioms.circleGap a b` form mismatches, the discharging
  identities `paper.circleGap = PaperAxioms.circleGap a b` follow
  by `rfl`.
* The witness `(5/10, 7/10)` should close `v14_window_witness_at_seed`
  via `norm_num [c_value]`. If `norm_num` cannot close one of the
  three inequalities (`c_value < 5/10`, `5/10 ≤ 7/10`, `7/10 < 1`),
  use `refine ⟨_, ?_, ?_, ?_⟩` and discharge each individually.
* Any of acceptance criteria 4, 5, 6, 7, 8, 9, 10 cannot be
  satisfied without weakening the contract: `STATUS=BLOCKED`.
* The proof would require any of the forbidden references in
  acceptance criterion 7: `STATUS=BLOCKED` — that would defeat the
  "fuse sprints 005, 006, 011, 012, 013 only" structural guarantee
  of this sprint.
* The proof would require a Mathlib lemma not yet in the pinned
  toolchain: `STATUS=BLOCKED_NEEDS_HUMAN`.
