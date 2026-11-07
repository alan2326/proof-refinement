# Sprint 038: Integrated annulus-side lower bound on `annulusExcess (circleGap a b) c` with **paper-axiom-free body** modulo a window-uniform `hLambdaBridge` family — the workspace's **first integrated annulus-side bound whose body invokes zero `paper.eq*` field projections**, the **integrated counterpart of sprint 037**, the **annulus-side mirror of sprint 034**, the **single bottleneck for a future closing reducer with empty paper-axiom signature modulo two cells**, and the **first lemma to fuse sprint 037 with the `annulusSlice` integration machinery in a paper-axiom-free body**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V37.lean`
**Target file**: `Candidates/V38.lean`
**Direction**: section2-proof

## Goal

Ship one new generic Lean theorem in `Proof/Reduction.lean`:

```lean
theorem annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ₁ ρ₂ : ℝ}
    (hc_pos : 0 < c)
    (hcρ₁ : c < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hρ₂_lt_one : ρ₂ < 1)
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
    (hIntLambda :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ) volume ρ₁ ρ₂)
    (hLambdaBridgeWindow :
      ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
        PaperAxioms.sigmaMinus a b ρ ≤
          WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
    (∫ ρ in ρ₁..ρ₂,
        2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
          / WangOuter.paperLambda K c ρ)
      ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
```

The statement and conclusion are **byte-for-byte identical** to sprint
006's `annulusExcess_lower_bound_of_eq8_eq9`. The **only** signature
changes are:

| Sprint | Annulus-bridge inputs |
|--------|------------------------|
| 006    | `paper : Section2Assumptions a b K c` (body invokes `paper.eq8_sigma_to_liftGap` and `paper.eq9_liftGap_to_circleGap` transitively via `circleGap_outer_lower_bound_of_eq8_eq9` for the pointwise step, and via `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` for the side-slice non-negativity step) |
| **NEW: 038** | **window-uniform `hLambdaBridgeWindow : ∀ ρ, c < ρ → ρ < 1 → Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ`** |

Sprint 038 is the **integrated counterpart of sprint 037** — sprint 037
ships the *pointwise* outer lower bound paper-axiom-free modulo a
single-`ρ` `hLambdaBridge` cell; sprint 038 integrates that pointwise
bound over `[ρ₁, ρ₂] ⊂ (c, 1)` against `2ρ`, asking the same bridge
to hold uniformly on the open `(c, 1)` window.

Where sprint 006's body invokes `paper`-bound names in **two** distinct
places — (a) the pointwise step inside `hPointwise` that calls
`circleGap_outer_lower_bound_of_eq8_eq9 paper`, and (b) the side-slice
non-negativity steps that call `annulusDensity_nonneg_of_lt hc_pos paper
…` (which itself invokes `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9
paper`) — sprint 038 replaces **both** with paper-axiom-free
substitutes:

| Analytical step inside body                                  | Provider |
|--------------------------------------------------------------|----------|
| Pointwise `2ρ³·Z_ρ/Λ ≤ 2ρ·circleGap ρ` on `Ioo ρ₁ ρ₂`       | sprint 037 (`circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`) consuming `hLambdaBridgeWindow ρ hcρ hρ_lt_one` |
| `circleGap a b ρ ≥ 0` on the side slices `Ioo c ρ₁` and `Ioo ρ₂ 1` | derived **inline** from `hLambdaBridgeWindow ρ hcρ hρ_lt_one`, sprint 005's `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`, `sigmaZeroMinus_nonneg_of_pos`, `paperLambda_pos`, and division-by-positive (no `OneModePaperBridge` invocation) |
| `annulusSlice` adjacency / non-negativity machinery | `AnnulusIntegralReduction.annulusSlice_add_adjacent`, `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae`, `intervalIntegral.integral_mono_on_of_le_Ioo` (verbatim from sprint 006) |
| Recognise `annulusSlice c 1 = annulusExcess` | `rfl`-style equality (verbatim from sprint 006) |

The body invokes **zero `paper.eq*` field projections** and **zero
`OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` invocations**. The
`paper : Section2Assumptions` parameter is dropped entirely. The
conclusion uses `PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c`
directly (matching sprint 037's representation-side conventions),
not `annulusExcess paper.circleGap c` (`paper.circleGap` and
`PaperAxioms.circleGap a b` are definitionally equal in
`Section2Assumptions`, but the new theorem's signature does not need
the `paper` projection).

Then ship a `Candidates/V38.lean` at the same `c = 0.3554` that
compiles, scores `≥ V37 = 1777/5000`, and **materialises** the new
theorem in side lemmas
`v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_compiles`
and
`v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_recovers_via_eq8_eq9_at_seed` side lemma demonstrates that the
window-uniform `hLambdaBridgeWindow` hypothesis can be discharged from
`paper.eq8_sigma_to_liftGap` + `paper.eq9_liftGap_to_circleGap` via
`PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9` applied
**uniformly** at every `ρ ∈ (c, 1)` — exactly mirroring V37's
`_recovers_via_eq8_eq9_at_seed` discharge but lifted to the
universal-quantifier shape. This confirms the new theorem is a
**strict generalisation of sprint 006**: any consumer with
`paper.eq8`/`paper.eq9` access can recover sprint 006's exact
conclusion through the new chain.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 038 ships:

1. **The workspace's first integrated annulus-side bound whose body
   invokes zero `paper.eq*` field projections.** Every prior integrated
   annulus-side bound in `Reduction.lean` invokes `paper.eq8`/`paper.eq9`
   transitively through sprint 006:

   | Sprint | Integrated annulus bound | Annulus-side `paper.eq*` |
   |--------|---------------------------|---------------------------|
   | 006 | `annulusExcess_lower_bound_of_eq8_eq9` | `{eq8, eq9}` (via sprint 005's `circleGap_outer_lower_bound_of_eq8_eq9` and `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9`) |
   | **NEW: 038** | `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge` | **`{}` modulo window-uniform `hLambdaBridgeWindow`** |

   The descending paper-axiom-signature exercise that the disk side
   has gone through (sprints 013, 026, 029, 030, 031, 034, 036, plus
   sprint 035's closing-reducer materialisation) finally has its
   first integrated-layer counterpart on the annulus side, completing
   the disk-side / annulus-side symmetry on the integrated layer.

2. **Integrated counterpart of sprint 037 — completes the
   pointwise/integrated symmetry on the annulus-side
   paper-axiom-free axis.** Sprint 037 ships the *pointwise* outer
   lower bound modulo a single-`ρ` `hLambdaBridge` cell. Sprint 038
   lifts this to the *integrated* layer with a window-uniform
   `hLambdaBridgeWindow` family. Together they form the full
   pointwise/integrated × disk/annulus paper-axiom-free matrix:

   | Layer       | Disk side | Annulus side |
   |-------------|-----------|--------------|
   | Pointwise   | sprint 036 (modulo `hSigmaCmp`) | sprint 037 (modulo `hLambdaBridge`) |
   | Integrated  | sprint 034 (modulo `hSigmaCmp`) | **NEW sprint 038** (modulo window-uniform `hLambdaBridgeWindow`) |

   Sprint 038 is the **missing integrated annulus corner**. Together
   with sprints 034/036/037 the workspace toolkit covers all four
   pointwise/integrated × disk/annulus shapes paper-axiom-free modulo
   the two independent hypothesis cells `hSigmaCmp` and
   `hLambdaBridge[Window]`.

3. **Single bottleneck for a future closing reducer with empty
   paper-axiom signature modulo two cells.** Per sprint 037's "Out of
   scope" #2, the natural follow-up is a closing reducer
   `valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window`
   fusing sprint 035's disk side (paper-axiom-free modulo `hSigmaCmp`)
   with a paper-axiom-free annulus side (modulo
   `hLambdaBridgeWindow`) — the workspace's first end-to-end closing
   reducer with **paper-axiom signature `{}` modulo two independent
   hypothesis cells**. That reducer's body would replace sprint 035's
   call to sprint 006 (`annulusExcess_lower_bound_of_eq8_eq9`) with a
   call to sprint 038. **Sprint 038 is the unique missing
   prerequisite** for that reducer; once shipped, the empty-paper-axiom
   closing reducer becomes a queueable structural follow-up of
   ~50–80 lines (sprint 035's body verbatim with one targeted
   substitution at the `hAnnulus :=` line).

   This is the structural analog of sprint 035's role for the disk
   side: sprint 034 alone is a disk integrated bound; sprint 035
   wires sprint 034 into a closing reducer. Sprint 038 alone is an
   annulus integrated bound; a future "sprint 039" will wire sprints
   034 + 038 into a fully paper-axiom-free closing reducer.

4. **First lemma to fuse sprint 037 with `annulusSlice` integration
   machinery in a paper-axiom-free body.** Sprint 037 is purely
   pointwise (a `Prop` of the form `2ρ³·Z_ρ/Λ ≤ 2ρ·circleGap ρ` at a
   single `ρ`). Sprint 038 is the first lemma to **integrate sprint
   037 over a window** while preserving the paper-axiom-free property.
   The integration step requires four ingredients:
   (a) `intervalIntegral.integral_mono_on_of_le_Ioo` on
   `(ρ₁, ρ₂)` (verbatim from sprint 006);
   (b) integrability of both sides (lifted to type-level
   `hIntCircle`/`hIntLambda` cells, verbatim from sprint 006);
   (c) `annulusSlice_add_adjacent` to split
   `annulusSlice c 1 = annulusSlice c ρ₁ + annulusSlice ρ₁ ρ₂ +
   annulusSlice ρ₂ 1` (verbatim from sprint 006);
   (d) non-negativity of the side slices (`annulusSlice c ρ₁` and
   `annulusSlice ρ₂ 1`).

   Ingredient (d) is where sprint 006 invokes
   `annulusDensity_nonneg_of_lt hc_pos paper` (which itself invokes
   `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper`). Sprint
   038's structural novelty is replacing this side-slice non-negativity
   step with a **paper-axiom-free derivation from `hLambdaBridgeWindow`
   alone**: at any `ρ ∈ (c, 1)`, `Σ⁻(ρ) ≤ Λ(c, ρ) · circleGap a b ρ`
   plus `Σ⁻(ρ) = ρ²·Z_ρ ≥ 0` (sprint 005 + `sigmaZeroMinus_nonneg_of_pos`)
   plus `Λ(c, ρ) > 0` (`paperLambda_pos`) yields
   `circleGap a b ρ ≥ 0` by division-by-positive — **without any
   `paper.eq*` invocation**. This is structurally novel: sprint 037 at
   a single `ρ` does not need this step (its conclusion does not
   require `circleGap ρ ≥ 0` for the pointwise inequality to hold);
   sprint 038's integrated form needs it for the side-slice
   non-negativity, and the way to obtain it paper-axiom-free is the
   bridge-divide-positive trick that sprint 037's body already
   contains in spirit but does not surface as a standalone step.

5. **First annulus-side lemma to lift a window-uniform hypothesis
   family.** Sprint 037 lifts a single-`ρ` `hLambdaBridge`. Sprint
   006's `paper : Section2Assumptions` covers all `ρ ∈ (c, 1)`
   uniformly via the typeclass-style premise structure. Sprint 038
   needs the same uniformity but **paper-axiom-free**, and its
   signature shape — a universally-quantified `∀ ⦃ρ⦄, c < ρ → ρ < 1 →
   …` — is the **first explicit window-uniform hypothesis family
   lifted into a workspace lemma's signature** (every prior
   universally-quantified hypothesis on this workspace lemma surface
   uses `paper` to provide the `Section2Assumptions a b K c`
   bundle, not an individual scalar inequality at every `ρ`). This
   is the natural shape an oracle/proposal on the lambda-bridge
   inequality would target: an oracle would discharge
   `hLambdaBridgeWindow` either as a single window-uniform witness
   or as a per-`ρ` witness threaded through a universal quantifier.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V38 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closed-form integrated
  lower bound with the same shape as sprint 006.

Why this is **not** "the same chain" as sprint 006:

* **Different paper-axiom signature.** Sprint 006's body invokes
  `circleGap_outer_lower_bound_of_eq8_eq9 paper` (transitively
  invoking `paper.eq8`/`paper.eq9`) and
  `annulusDensity_nonneg_of_lt hc_pos paper` (transitively invoking
  `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper`); sprint
  038's body invokes **zero** `paper.eq*` field projections and
  **zero** `OneModePaperBridge` invocations. The chain through which
  the same conclusion is reached is distinct: sprint 006 delegates
  both the pointwise step and the side-slice non-negativity step to
  a single `paper`-bundle premise; sprint 038 lifts the
  `Σ⁻(ρ) ≤ Λ(c,ρ)·circleGap ρ` family to an explicit hypothesis and
  derives both pointwise step and side-slice non-negativity from
  this hypothesis plus paper-axiom-free workspace lemmas.
* **Different signature shape.** Sprint 006 has 7 cells (`paper`,
  `hc_pos`, `hcρ₁`, `hρ₁₂`, `hρ₂_lt_one`, `hIntCircle`, `hIntLambda`).
  Sprint 038 has 7 cells (no `paper` parameter; same 6 geometric /
  integrability cells; new window-uniform `hLambdaBridgeWindow`).
  The structural change: drop `paper`, add `hLambdaBridgeWindow`.
* **Different downstream consumer pattern.** Sprint 006 cannot be
  consumed without `paper.eq8`/`paper.eq9`; sprint 038 *can* be
  consumed without those (e.g., via a future oracle/proposal on the
  lambda-bridge inequality, or via a numerical certificate uniform on
  `(c, 1)`).

Why this is **not** "the same chain" as sprint 037:

* **Sprint 037 is pointwise** (a `Prop` at a single `ρ`); sprint 038
  is **integrated** over `[ρ₁, ρ₂]`. The shapes are qualitatively
  different (different layer).
* **Sprint 037's hypothesis is single-`ρ`**; sprint 038's hypothesis
  is **window-uniform**. The lifted cell upgrades from a single
  inequality at a fixed `ρ` to a universally-quantified family on
  `(c, 1)`.
* **Sprint 037's body does not use `annulusSlice` machinery**;
  sprint 038's body does — `annulusSlice_add_adjacent`,
  `annulusSlice_nonneg_of_ae`, `intervalIntegral.integral_mono_on_of_le_Ioo`,
  and the side-slice non-negativity sub-argument verbatim from
  sprint 006 modulo the paper-axiom replacement.
* **Sprint 037's body has 3 lifted-cell consumers** (the `hLambdaBridge`
  hypothesis is referenced once; `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
  is referenced once; `paperLambda_pos` is referenced once). Sprint
  038's body has **two distinct** uses of `hLambdaBridgeWindow`: one
  for the pointwise step on `Ioo ρ₁ ρ₂`, one for the side-slice
  non-negativity step on `Ioo c ρ₁` and `Ioo ρ₂ 1`. These two uses
  apply the same window-uniform hypothesis at structurally different
  radii sets, requiring the universally-quantified shape (a
  single-`ρ` `hLambdaBridge` would not suffice).

Why this is **not** "the same chain" as sprint 034:

* **Sprint 034 is disk-side**; sprint 038 is annulus-side. Different
  sides of the `diskExcess + annulusExcess` decomposition.
* **Sprint 034 lifts `hSigmaCmp`** (a single scalar inequality at the
  disk anchor `c`); sprint 038 lifts `hLambdaBridgeWindow` (a
  window-uniform family on `(c, 1)`). Different cells, different
  shapes.
* **Sprint 034's body does not use `annulusSlice`**; sprint 038's
  body uses it extensively.

Why this is **not** "the same chain" as sprint 035:

* **Sprint 035 is a closing reducer** (output type
  `ValidKorenblumBound c`); sprint 038 is an **integrated annulus
  bound** (output type `∫ … ≤ annulusExcess …`). Different layers.
* **Sprint 035 still uses the annulus-side `paper.eq8`/`paper.eq9`**
  via sprint 006; sprint 038 eliminates that dependency. The two
  lemmas are not interchangeable: a future "sprint 039" closing
  reducer would compose sprint 035's disk-side body with sprint
  038's annulus-side body, not replace sprint 035 wholesale.

Why this is **bounded enough for one Generator session**:

* The lemma signature is ~25 lines (sprint 006's signature is ~17
  lines; sprint 038 differs by dropping `paper` and adding the
  ~6-line window-uniform `hLambdaBridgeWindow` premise).
* The proof body is sprint 006's body (~175 lines, lines 649–822 of
  `Reduction.lean`) modified by **two targeted substitutions**:
  - replace the `hPointwise` step (line 685) with a call to sprint
    037 consuming `hLambdaBridgeWindow ρ hcρ hρ_lt_one`,
  - replace each `annulusDensity_nonneg_of_lt hc_pos paper hcρ
    hρ_lt_one` invocation (sprint 006's lines 774, 790) with a small
    inline derivation from `hLambdaBridgeWindow ρ hcρ hρ_lt_one` +
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` +
    `sigmaZeroMinus_nonneg_of_pos` + `paperLambda_pos` +
    division-by-positive (~10 lines per invocation, or a small
    private helper extracted once and reused twice).
  - drop the `paper` parameter,
  - replace `annulusSlice paper.circleGap` and `annulusDensity
    paper.circleGap` with their `circleGap a b` counterparts (these
    are definitionally equal, so the substitution is mostly cosmetic
    — but the new theorem's conclusion uses
    `PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c`,
    matching sprint 037's representation conventions).
* All Lean idioms used (`have hPointwise`, `intro ρ hρ`,
  `intervalIntegral.integral_mono_on_of_le_Ioo`,
  `AnnulusIntegralReduction.annulusSlice_add_adjacent`,
  `AnnulusIntegralReduction.annulusSlice_nonneg_of_ae`,
  `Measure.restrict_congr_set Ioo_ae_eq_Icc`, `linarith`, `nlinarith`,
  `field_simp`, `calc`) are verbatim from sprint 006's body. No new
  idioms required.
* Estimate: ~150–180 lines for the new theorem (sprint 006's body
  size with the two targeted substitutions). Candidate side lemmas
  ~30–40 lines each. Total V38 size: ≤ 250 lines.

### Note on the `paper.circleGap` vs `PaperAxioms.circleGap a b` representation

Sprint 006's conclusion uses `annulusExcess paper.circleGap c` and
its body uses `annulusSlice paper.circleGap`/`annulusDensity
paper.circleGap`. These are definitionally equal to
`annulusExcess (PaperAxioms.circleGap a b) c` etc. via the
`paper.circleGap = PaperAxioms.circleGap a b` field defining
equation. Sprint 038's conclusion uses
`PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c` directly
(matching sprint 037's representation conventions; sprint 037 uses
`PaperAxioms.circleGap a b` everywhere with no `paper`-bundle
projection). The body should use `circleGap a b ρ` consistently and
recognise the `annulusSlice c 1` of `circleGap a b ρ` as
`annulusExcess (circleGap a b) c` via the same definitional `rfl`
sprint 006's body uses (line 808-811: `hAnnulusEq` is closed by
`rfl`). The `annulusSlice` and `annulusDensity` machinery in
`AnnulusIntegralReduction` is parametric in the `circleGap`
function, so the substitution is type-level rather than
algebraic — an `intro` in the side-slice non-negativity sub-lemma
introduces `circleGap a b ρ` rather than `paper.circleGap ρ`.

### Note on the inline side-slice non-negativity helper

The two invocations of `annulusDensity_nonneg_of_lt hc_pos paper hcρ
hρ_lt_one` in sprint 006's body (one inside the `Ioo c ρ₁`
non-negativity proof, one inside the `Ioo ρ₂ 1` non-negativity proof)
share the same structure: at any `ρ` in the open side interval, with
`c < ρ < 1`, derive `0 ≤ 2 * ρ * circleGap a b ρ`. Sprint 038
replaces these with the following inline derivation (or a small
private helper called twice):

```lean
have hCircleNonneg :
    ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 → 0 ≤ PaperAxioms.circleGap a b ρ := by
  intro ρ hcρ hρ_lt_one
  have hBridge :
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ :=
    hLambdaBridgeWindow hcρ hρ_lt_one
  have hIdentity := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
  have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
  have hZ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ :=
    sigmaZeroMinus_nonneg_of_pos a b hρ_pos
  have hΣMinus_nonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ := by
    rw [hIdentity]; positivity
  have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
    WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
  -- 0 ≤ Σ⁻(ρ) ≤ Λ · circleGap; divide by Λ > 0.
  have hChain : 0 ≤ WangOuter.paperLambda K c ρ
                  * PaperAxioms.circleGap a b ρ :=
    le_trans hΣMinus_nonneg hBridge
  exact nonneg_of_mul_nonneg_left hChain hΛpos
```

Where `nonneg_of_mul_nonneg_left` is shorthand for the standard
"divide by positive" Mathlib lemma (the precise name in pinned
Mathlib may be `le_div_iff₀` followed by simplification, or
`pos_of_mul_pos_div_lt`, or extracted via `field_simp` + `nlinarith`
— the sprint contract does not pin a specific Mathlib name; the
generator should use whatever cleanly produces the conclusion from
the four facts `0 ≤ Σ⁻`, `Σ⁻ ≤ Λ · circleGap`, `0 < Λ`, and the
goal `0 ≤ circleGap`).

This helper is then called inside the existing `hSlice_cρ₁_nonneg`
and `hSlice_ρ₂1_nonneg` blocks in place of
`annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one`:

```lean
-- old (sprint 006):
exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
-- new (sprint 038):
have hC : 0 ≤ PaperAxioms.circleGap a b ρ := hCircleNonneg hcρ hρ_lt_one
have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
change 0 ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
nlinarith
```

### Note on the discharge of `hLambdaBridgeWindow` at the seed

V38's `_recovers_via_eq8_eq9_at_seed` side lemma exhibits the
**discharge route via `paper.eq8_sigma_to_liftGap` and
`paper.eq9_liftGap_to_circleGap`**, lifted to the universal-quantifier
shape: given a `Section2Assumptions a b K c_value` instance, the
lemma defines

```lean
have hLambdaBridgeWindow :
    ∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c_value ρ
          * PaperAxioms.circleGap a b ρ := by
  intro ρ hcρ hρ_lt_one
  exact PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
    paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap
    hcρ hρ_lt_one
```

then plugs this into the new generic theorem along with the
geometric / integrability cells. The resulting conclusion is
byte-for-byte identical to sprint 006's at the seed — recovering
sprint 006's exact bound through sprint 038's chain.

This side lemma serves **two roles**: (a) confirms the new theorem
is a strict generalisation of sprint 006 (any consumer with
`paper.eq8`/`paper.eq9` access can recover sprint 006's bound from
sprint 038); (b) demonstrates the precise discharge route that a
future oracle-bearing consumer would substitute (replace the
`paper.eq8`/`paper.eq9` invocations with the oracle's witness — every
other cell remains identical).

### Note on the `_compiles` side lemma

V38's `_compiles` side lemma should exhibit the new theorem's
*type-shape* compilation at the seed without committing to a specific
discharge route for `hLambdaBridgeWindow` — it takes
`hLambdaBridgeWindow` (and the integrability hypotheses) as
universally-quantified Lean hypotheses and feeds them into the new
theorem to produce the integrated lower bound. Concrete witness:
instantiate at `c = c_value = 3554/10000`, `ρ₁ := 1/2`, `ρ₂ := 7/10`,
`K := fun _ _ => 1` (or any concrete `K`).

### Note on hypothesis-count and analytical structure

Sprint 006 has 7 cells (`paper`, `hc_pos`, `hcρ₁`, `hρ₁₂`,
`hρ₂_lt_one`, `hIntCircle`, `hIntLambda`). Sprint 038 has 7
(paper-axiom-free; no `paper` parameter; same 6 geometric /
integrability cells; new window-uniform `hLambdaBridgeWindow`). The
hypothesis-count delta is 0 (drop `paper`, add
`hLambdaBridgeWindow`). Net: hypothesis count identical;
paper-axiom signature on the body shrinks from `{eq8, eq9}` to `{}`
modulo the explicit window-uniform `hLambdaBridgeWindow`.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
      {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ} {c ρ₁ ρ₂ : ℝ}
      (hc_pos : 0 < c)
      (hcρ₁ : c < ρ₁)
      (hρ₁₂ : ρ₁ ≤ ρ₂)
      (hρ₂_lt_one : ρ₂ < 1)
      (hIntCircle :
        IntervalIntegrable
          (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ) volume c 1)
      (hIntLambda :
        IntervalIntegrable
          (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ) volume ρ₁ ρ₂)
      (hLambdaBridgeWindow :
        ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
          PaperAxioms.sigmaMinus a b ρ ≤
            WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) :
      (∫ ρ in ρ₁..ρ₂,
          2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
            / WangOuter.paperLambda K c ρ)
        ≤ PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c
  ```
  Estimated location: append after sprint 037's
  `circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`
  (at the current end of `Reduction.lean`). Estimated ~150–180 lines.

  The proof body is structurally **sprint 006's body verbatim**
  (lines 649–822 of `Reduction.lean`) with the following targeted
  substitutions:

  1. **Replace the `hPointwise` step at lines 681–685** (which calls
     `circleGap_outer_lower_bound_of_eq8_eq9 paper hc_pos hcρ
     hρ_lt_one`) with a call to sprint 037 consuming
     `hLambdaBridgeWindow`:

     ```lean
     have hPointwise :
         ∀ ρ ∈ Set.Ioo ρ₁ ρ₂,
           2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ
               / WangOuter.paperLambda K c ρ
             ≤ 2 * ρ * PaperAxioms.circleGap a b ρ := by
       intro ρ hρ
       have hcρ : c < ρ := lt_of_lt_of_le hcρ₁ hρ.1.le
       have hρ_lt_one : ρ < 1 := lt_of_le_of_lt hρ.2.le hρ₂_lt_one
       exact circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge
         hc_pos hcρ hρ_lt_one (hLambdaBridgeWindow hcρ hρ_lt_one)
     ```

  2. **Add a `hCircleNonneg` helper** (paper-axiom-free side-slice
     non-negativity, see "Note on the inline side-slice
     non-negativity helper" above):

     ```lean
     have hCircleNonneg :
         ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 → 0 ≤ PaperAxioms.circleGap a b ρ := by
       intro ρ hcρ hρ_lt_one
       have hBridge := hLambdaBridgeWindow hcρ hρ_lt_one
       have hIdentity := sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus a b ρ
       have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
       have hZ_nonneg : 0 ≤ PaperAxioms.sigmaZeroMinus a b ρ :=
         sigmaZeroMinus_nonneg_of_pos a b hρ_pos
       have hΣMinus_nonneg : 0 ≤ PaperAxioms.sigmaMinus a b ρ := by
         rw [hIdentity]; positivity
       have hΛpos : 0 < WangOuter.paperLambda K c ρ :=
         WangPaperSideConditions.paperLambda_pos (K := K) (c := c) (ρ := ρ)
       have hChain : 0 ≤ WangOuter.paperLambda K c ρ
                       * PaperAxioms.circleGap a b ρ :=
         le_trans hΣMinus_nonneg hBridge
       -- divide by Λ > 0.
       exact nonneg_of_mul_nonneg_left hChain hΛpos
     ```

     (The exact Mathlib name for the final "divide by positive" step
     may need adjustment — `nonneg_of_mul_nonneg_left`,
     `(mul_nonneg_iff_of_pos_left hΛpos).mp hChain`, or a small
     `nlinarith` clean-up. The generator should use whatever cleanly
     closes the goal; this is verbatim arithmetic on
     `0 ≤ a * b` with `0 < a` to conclude `0 ≤ b`.)

  3. **Replace each `annulusDensity_nonneg_of_lt hc_pos paper hcρ
     hρ_lt_one` invocation** (sprint 006's lines 774, 790) with a
     small inline derivation using `hCircleNonneg`:

     ```lean
     -- old (sprint 006, line 774):
     -- exact annulusDensity_nonneg_of_lt hc_pos paper hcρ hρ_lt_one
     -- new (sprint 038):
     have hC : 0 ≤ PaperAxioms.circleGap a b ρ := hCircleNonneg hcρ hρ_lt_one
     have hρ_pos : 0 < ρ := lt_trans hc_pos hcρ
     show 0 ≤ AnnulusIntegralReduction.annulusDensity (PaperAxioms.circleGap a b) ρ
     change 0 ≤ 2 * ρ * PaperAxioms.circleGap a b ρ
     nlinarith
     ```

  4. **Drop the `paper` parameter** entirely.

  5. **Replace `paper.circleGap` with `PaperAxioms.circleGap a b`**
     throughout the body (this is a definitional substitution; the
     `annulusSlice` and `annulusDensity` machinery is parametric in
     the `circleGap` function so the substitution is mostly
     cosmetic — but the conclusion must use `PaperAxioms.annulusExcess
     (PaperAxioms.circleGap a b) c`, not `annulusExcess
     paper.circleGap c`).

  6. **Leave everything else byte-for-byte identical** to sprint
     006's body: the geometric scaffolding (`hc_le_ρ₁`,
     `hρ₁_lt_one`, `hcρ₂`, etc.), the
     `intervalIntegral.integral_mono_on_of_le_Ioo` call, the
     `annulusSlice_add_adjacent` calls, the
     `annulusSlice_nonneg_of_ae` calls (these take a `circleGap`
     argument, not a `paper` argument, so the substitution is
     local), the side-slice
     `hSlice_cρ₁_nonneg`/`hSlice_ρ₂1_nonneg` blocks (modulo the
     `annulusDensity_nonneg_of_lt` substitution above), the
     `hZ_ρ₁_nonneg` materialisation, the final `calc` chain.

- `ProofRefinement/Korenblum/Candidates/V38.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V37),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V37),
  4. Adds two side lemmas
     `v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_compiles`
     and
     `v38_annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge_recovers_via_eq8_eq9_at_seed`
     exercising the new generic theorem:
     - `_compiles` exhibits the new theorem's hypothesis shape — six
       cells: `hc_pos`, `hcρ₁`, `hρ₁₂`, `hρ₂_lt_one`, `hIntCircle`,
       `hIntLambda`, `hLambdaBridgeWindow`. Concrete witness:
       instantiate at `c = c_value`, `ρ₁ := 1/2`, `ρ₂ := 7/10`,
       `K := fun _ _ => 1`. The integrability hypotheses and
       `hLambdaBridgeWindow` are taken as universally-quantified Lean
       hypotheses on the side lemma. This side lemma does **not**
       use a `paper` instance.
     - `_recovers_via_eq8_eq9_at_seed` takes a
       `Section2Assumptions a b K c_value` instance, discharges
       `hLambdaBridgeWindow` from
       `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
       paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap`
       (lifted to the universal-quantifier shape), and applies the new
       theorem to recover sprint 006's exact conclusion at the seed
       (with `ρ₁ := 1/2`, `ρ₂ := 7/10`). The integrability hypotheses
       are taken as additional universally-quantified hypotheses on
       the side lemma.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V37).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V38` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V38.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V38 ties V37 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V38.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V38.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — body is paper-axiom-free.
   Greppable check: in the body of
   `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`,
   the count of `paper.eq` substrings is **0**. (The lemma's signature
   also does not include a `paper : Section2Assumptions ...`
   parameter.)
7. The proof body **does not invoke**
   `circleGap_outer_lower_bound_of_eq8_eq9` (sprint 005) — sprint 037
   is the substitute. Greppable check: count of
   `circleGap_outer_lower_bound_of_eq8_eq9` in the body of the new
   theorem is **0**.
8. The proof body **does not invoke**
   `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` — the side-slice
   non-negativity helper substitutes for it. Greppable check: count
   of `circleGap_nonneg_of_eq8_eq9` in the body of the new theorem is
   **0**.
9. The proof body **does not invoke** `annulusDensity_nonneg_of_lt`
   (the private helper that itself uses
   `circleGap_nonneg_of_eq8_eq9`). Greppable check: count of
   `annulusDensity_nonneg_of_lt` in the body of the new theorem is
   **0**.
10. The proof body invokes
    `circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`
    (sprint 037) at least once for the pointwise step. Greppable
    check: count of
    `circleGap_outer_lower_bound_via_series_only_modulo_lambda_bridge`
    substrings in the body of the new theorem is ≥ 1.
11. The proof body invokes `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`
    (sprint 005) at least once (used in the side-slice non-negativity
    helper). Greppable check: count of
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus` substrings in the body
    of the new theorem is ≥ 1.
12. The proof body invokes `sigmaZeroMinus_nonneg_of_pos` at least
    once (used in the side-slice non-negativity helper). Greppable
    check: count of `sigmaZeroMinus_nonneg_of_pos` substrings in the
    body of the new theorem is ≥ 1.
13. The proof body invokes `paperLambda_pos` at least once (used in
    the side-slice non-negativity helper). Greppable check: count of
    `paperLambda_pos` substrings in the body of the new theorem is
    ≥ 1.
14. The new theorem's signature includes the explicit
    `hLambdaBridgeWindow : ∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
    PaperAxioms.sigmaMinus a b ρ ≤
    WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ`
    hypothesis. Greppable check: the substring `hLambdaBridgeWindow`
    appears in the signature line region of the new theorem.
15. The V38 `_recovers_via_eq8_eq9_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` at least once
    (in the discharge of `hLambdaBridgeWindow`). This confirms the
    new theorem **strictly generalises** sprint 006 (any consumer
    with `paper.eq8`/`paper.eq9` access can recover sprint 006's
    conclusion through the new chain).
16. The proof body of the new theorem **does not invoke**
    `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006) — the
    structural marker that sprint 038 is a fresh chain, not a
    wrapper around sprint 006. Greppable check: count of
    `annulusExcess_lower_bound_of_eq8_eq9` in the body of the new
    theorem is 0.
17. The new theorem's conclusion uses
    `PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c` (not
    `annulusExcess paper.circleGap c`). Greppable check: the substring
    `annulusExcess (PaperAxioms.circleGap a b) c` (or
    `annulusExcess paper.circleGap c` not present, with the
    `circleGap a b` form present) appears in the conclusion line.
18. The new theorem invokes `intervalIntegral.integral_mono_on_of_le_Ioo`
    at least once (verbatim from sprint 006). Greppable check: count
    of `intervalIntegral.integral_mono_on_of_le_Ioo` in the body of
    the new theorem is ≥ 1.
19. The new theorem invokes
    `AnnulusIntegralReduction.annulusSlice_add_adjacent` at least
    twice (verbatim from sprint 006: side-slice splits). Greppable
    check: count of
    `AnnulusIntegralReduction.annulusSlice_add_adjacent` in the body
    of the new theorem is ≥ 2.

## Out of scope

- Edit older candidates V0–V37.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V38 is the
  same `hEq15_seed_3554` that V0–V37 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- Land an oracle/proposal for the lambda-bridge inequality. Sprint 038
  isolates this as a type-level window-uniform hypothesis but does
  not itself discharge it via an oracle. A future planner may file
  `Proposals/proposal_<NNN>_*.md` for a numerical or analytical
  oracle on the window-uniform lambda-bridge if motivated; sprint
  038 is decoupled from that proposal.
- Materialise sprint 038 in a closing reducer (i.e., do not yet ship
  the natural "sprint 039" — the closing reducer fusing sprint 035's
  disk side with sprint 038's annulus side, achieving paper-axiom
  signature `{}` modulo two cells `hSigmaCmp` + `hLambdaBridgeWindow`).
  That reducer is the natural follow-up but is its own bounded
  Generator session: it requires extending sprint 035's witness
  existential by the window-uniform `hLambdaBridgeWindow` cell and
  re-threading it through the sprint 035 body. Queueable separately
  after sprint 038 lands.
- Land a paper-axiom-free outer integrated bound through any *other*
  chain (e.g., via sprint 027's equality decomposition of `circleGap`
  followed by separate bounds on `sigmaPlus ρ` and `sigmaMinus ρ`).
  The single-`hLambdaBridgeWindow`-cell chain is the unique chain we
  ship in sprint 038.
- Replace any other workspace lemma's annulus-side dependency on
  `paper.eq8`/`paper.eq9` (e.g., make sprint 014's annulus-side body
  paper-axiom-free, or sprint 023/024's). Sprint 038 ships only the
  new integrated annulus bound; downstream substitutions in closing
  reducers are queueable separately.
- Series-derive `eq8` or `eq9` themselves (i.e., produce a workspace
  lemma `eq8eq9_sigma_to_circleBridge_via_series` paper-axiom-free).
  This would require analytical work on the `liftGap` representation
  that the workspace has not touched yet, would likely require
  Mathlib archaeology and `Scratch/` exploration, and is structurally
  out of scope for sprint 038 (which lifts the post-substitution form
  of `(8)+(9)` to a hypothesis cell rather than series-deriving it).
- Strengthen the window-uniform hypothesis to a strict-inequality
  `Σ⁻(ρ) < Λ(c, ρ) · circleGap ρ` form, or weaken to a closed-window
  `c ≤ ρ ≤ 1` form. Sprint 038's open-window `c < ρ < 1` shape
  matches sprint 037's signature exactly; alternative shapes would
  introduce signature-mismatch bookkeeping with sprint 037.
- Land any candidate at `c > 0.3554`. Sprint 038 does not raise
  `c_value`. The eventual numerical push is the *consumer* of sprint
  038's downstream "sprint 039" closing reducer combined with future
  oracles on `hSigmaCmp` and `hLambdaBridgeWindow`, not sprint 038
  itself.

## Time budget

≤ 90 minutes runtime. (Sprint 006's body is ~175 lines; sprint 038's
body is sprint 006's body with two targeted substitutions: the
`hPointwise` step (~5 lines replaced) and the side-slice
non-negativity helper (~20 lines added, two
`annulusDensity_nonneg_of_lt` invocations replaced with calls to the
new helper). V38 candidate adds ~30–40 lines per side lemma. Total
V38 size: ≤ 250 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
