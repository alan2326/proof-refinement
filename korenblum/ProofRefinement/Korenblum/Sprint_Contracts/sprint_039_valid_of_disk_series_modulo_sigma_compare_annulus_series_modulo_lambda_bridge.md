# Sprint 039: End-to-end full-window closing reducer fusing sprint 035's paper-axiom-free disk side (modulo `hSigmaCmp`) with sprint 038's paper-axiom-free annulus side (modulo window-uniform `hLambdaBridgeWindow`) — the workspace's **first `valid_of_*` reducer whose entire transitive proof body invokes zero `paper.eq*` field projections** on either disk or annulus side, the **first reducer to lift two independent oracle-shaped hypothesis cells (`hSigmaCmp` + `hLambdaBridgeWindow`) into the witness existential simultaneously**, the **structural completion of the disk/annulus paper-axiom-free `valid_of_*` matrix**, and the **immediate prerequisite for any future oracle on either `Σ⁺(c) ≤ Σ⁻(c)` or `Σ⁻(ρ) ≤ Λ(c, ρ)·circleGap ρ` to deliver a paper-axiom-free, full-window `ValidKorenblumBound c` route**

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V38.lean`
**Target file**: `Candidates/V39.lean`
**Direction**: section2-proof

## Goal

Ship one new generic closing-reducer theorem in `Proof/Reduction.lean`:

```lean
theorem valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window
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
            (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
              PaperAxioms.sigmaMinus a b ρ ≤
                WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) ∧
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

This is **sprint 035's body verbatim**, with one targeted annulus-side
substitution: the call at line 5487–5489 to
`annulusExcess_lower_bound_of_eq8_eq9 paper hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one
hIntCircle hIntLambdaZ` (sprint 006, paper-axiom signature `{eq8, eq9}`)
is replaced by a call to
`annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge hc_pos
hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ hLambdaBridgeWindow` (sprint
038, paper-axiom-free body modulo explicit window-uniform
`hLambdaBridgeWindow`). The witness existential is correspondingly
extended: sprint 035's 12-cell witness becomes a 13-cell witness with
one new annulus-side cell `hLambdaBridgeWindow` inserted between
`hSigmaCmp` and `hIntDisk`.

The closed-form kernel inequality is **byte-for-byte identical** to
sprints 014 and 035: `c^4 ≤ ∫ ρ' in ρ₁..ρ₂, 2·ρ'^3 / paperLambda K c ρ'`
— same coefficient `c^4`, same integrand, same admissible window
`[ρ₁, ρ₂] ⊂ (c, 1)` (no `branchSplit c` confinement). What changes is
**the type-level provenance of the entire reducer**: sprint 035 still
delegates the annulus-side chain to sprint 006 (transitively invoking
`paper.eq8` and `paper.eq9`); sprint 039 delegates that same chain to
sprint 038 (whose body is paper-axiom-free, with the unique
non-series-derivable conjunct on the annulus side lifted into the
type signature as window-uniform `hLambdaBridgeWindow`).

After sprint 039 lands, the workspace has its **first end-to-end
`ValidKorenblumBound c` closing reducer whose entire transitive proof
body invokes zero `paper.eq*` field projections** — both disk and
annulus sides paper-axiom-free, modulo exactly two independent
oracle-shaped hypothesis cells:

| Cell | Shape | Discharge route at the seed |
|------|-------|------------------------------|
| `hSigmaCmp` | scalar inequality `Σ⁺(c) ≤ Σ⁻(c)` at one anchor | `paper.eq4_sigmaPlus_bound` second conjunct |
| `hLambdaBridgeWindow` | `∀ ⦃ρ⦄, c < ρ → ρ < 1 → Σ⁻(ρ) ≤ Λ(c,ρ)·circleGap ρ` window-uniform family | `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9` lifted to universal-quantifier shape |

These are the **two minimal targets** isolated by sprints 034–038. A
future oracle/proposal on either cell (or a `Numerical_Library`-backed
discharge of either) plugs directly into sprint 039's witness existential
and immediately yields a paper-axiom-free `ValidKorenblumBound c` route
*without any further structural plumbing*.

Then ship a `Candidates/V39.lean` at the same `c = 0.3554` that
compiles, scores `≥ V38 = 1777/5000`, and **materialises** the new
reducer in side lemmas
`v39_valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window_compiles`
and
`v39_valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window_witness_at_seed`.
The sink theorem `korenblum_constant_search` is still discharged via
`valid_of_eq15` so the score does not regress.

The `_witness_at_seed` side lemma demonstrates that **both** cells can
be discharged simultaneously from the paper bundle:

- `hSigmaCmp` from `paper.eq4_sigmaPlus_bound` (the same discharge
  route exhibited in V35's `_witness_at_seed`),
- `hLambdaBridgeWindow` from
  `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
  paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap` lifted to
  the universal-quantifier shape (the same discharge route exhibited
  in V38's `_recovers_via_eq8_eq9_at_seed`).

This is the structural marker that the new reducer is a strict
generalisation of sprint 014: **any consumer with `paper.eq4` +
`paper.eq8` + `paper.eq9` access can recover sprint 014's exact
end-to-end conclusion through the new chain**, while a future consumer
with oracles on `hSigmaCmp` and `hLambdaBridgeWindow` would discharge
the same reducer **without ever invoking any `paper.eq*` projection
anywhere in the transitive body**.

## Why

The bulletin's current priority is *novel analytical chains* through
`Section2Assumptions` — quality of analytical move outweighs raw `c`
headroom. Sprint 039 ships:

1. **The workspace's first `valid_of_*` reducer with paper-axiom-free
   body on both disk *and* annulus sides simultaneously.** Every prior
   `valid_of_*` reducer in `Reduction.lean` invokes at least one
   `paper.eq*` field projection somewhere in its transitive proof body:

   | Sprint | Reducer | Disk-side `paper.eq*` | Annulus-side `paper.eq*` |
   |--------|---------|------------------------|---------------------------|
   | seed   | `valid_of_eq15` | `eq14_combined`, `eq15`-bridge | (folded into `eq14`) |
   | 001    | `valid_of_eq12_eq13` | `eq12`, `eq13`, `eq14_combined` | (folded into `eq14`) |
   | 004    | `valid_of_eq2_eq3_eq4_annulus_budget` | `eq2`, `eq3`, `eq4` | (annulus budget premise) |
   | 008    | `valid_of_eq10_subinterval_branch1` | `eq10` | (mass-condition premise) |
   | 014    | `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` | `eq3`, `eq4` | `eq8`, `eq9` |
   | 017    | `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window` | `eq6` | `eq8`, `eq9` |
   | 018    | `valid_of_eq11_subinterval_branch2` | `eq11` | (mass-condition premise) |
   | 019    | `valid_of_eq5_eq8_eq9_subinterval_branch1` | `eq5` | `eq8`, `eq9` |
   | 020    | `valid_of_eq10_eq11_straddling_window` | `eq10`, `eq11` | (mass-condition premise) |
   | 021    | `valid_of_disk_eq5_annulus_eq8_eq9_decoupled_anchor` | `eq5` | `eq8`, `eq9` |
   | 023    | `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window` | `eq2`, `eq3`, `eq4` | `eq8`, `eq9` |
   | 024    | `…_uniformSummable` | `eq2`, `eq3`, `eq4` | `eq8`, `eq9` |
   | 035    | `valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window` | **`{}` modulo `hSigmaCmp`** | `eq8`, `eq9` |
   | **NEW: 039** | `valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window` | **`{}` modulo `hSigmaCmp`** | **`{}` modulo `hLambdaBridgeWindow`** |

   Sprint 035 made the disk side paper-axiom-free; sprint 039 makes
   the annulus side paper-axiom-free as well. The full-matrix
   completion is the structural payoff.

2. **First `valid_of_*` reducer to lift two independent oracle-shaped
   hypothesis cells into the witness existential simultaneously.**
   Sprint 035 lifts `hSigmaCmp` (scalar at one anchor); sprint 038 lifts
   `hLambdaBridgeWindow` (window-uniform family on `(c, 1)`). The two
   cells are **structurally distinct**:

   - `hSigmaCmp` is a single scalar at `c`, valued in `ℝ`,
     discharged from a single `paper.eq4` field projection;
   - `hLambdaBridgeWindow` is a window-uniform family
     `∀ ρ ∈ (c, 1)`, valued in `Prop`, discharged from a uniform
     application of `paper.eq8`/`paper.eq9` via
     `eq8eq9_sigma_to_circleBridge_of_eq8_eq9`.

   Sprint 039 is the **first reducer whose witness existential
   simultaneously requires a scalar oracle target and a
   window-uniform oracle-target family**. The structural pattern is
   novel: every prior sprint-035-style reducer lifts a single
   oracle-shaped cell (sprint 035 alone, sprint 038 alone), or no
   oracle cells (all earlier reducers).

3. **Structural completion of the descending paper-axiom-signature
   sequence on `valid_of_*` reducers.** The workspace's `valid_of_*`
   reducers have followed a descending paper-axiom-signature path on
   the disk side: `{eq2, eq3, eq4}` → `{eq3, eq4}` → `{eq4}` → `{}`
   modulo `hSigmaCmp` (sprint 035). Sprint 039 closes the analogous
   sequence on the annulus side: `{eq8, eq9}` → `{}` modulo
   `hLambdaBridgeWindow`. The combined `valid_of_*` paper-axiom
   signature drops from sprint 014's `{eq3, eq4, eq8, eq9}` to sprint
   039's `{}` modulo `{hSigmaCmp, hLambdaBridgeWindow}` — the
   workspace's first `valid_of_*` reducer at the structural floor of
   "no paper axioms on either side".

4. **Immediate prerequisite for an oracle-driven raise of `c_value`.**
   Per the bulletin's high-value direction #3 ("Prepare a precise
   oracle-backed subclaim that directly supports a future increase in
   `c_value`"), sprint 039 is the unique missing structural piece
   between *paper-axiom-free pointwise/integrated bounds on each side
   modulo two oracle-shaped cells* (sprints 034–038) and *an
   oracle-driven `ValidKorenblumBound c` route at any `c` for which
   the kernel inequality and oracles are jointly satisfied*. Without
   sprint 039, an oracle on `hSigmaCmp` would still need to be
   composed with sprint 006 (which still uses `paper.eq8`/`paper.eq9`),
   making the oracle's payoff partial; with sprint 039, an oracle on
   `hSigmaCmp` and an oracle on `hLambdaBridgeWindow` together
   discharge the full reducer with zero `paper.eq*` invocations.

   Concretely, this means a future planner can file two independent
   numerical-oracle proposals:
   - one on `Σ⁺(c) ≤ Σ⁻(c)` at a target `c > 0.3554`,
   - one on `∀ ρ ∈ (c, 1), Σ⁻(ρ) ≤ Λ(c, ρ)·circleGap ρ` at the same
     target `c`,

   and slot them into sprint 039's witness existential without
   requiring any further structural Lean work — the kernel inequality
   `c^4 ≤ ∫_{ρ₁..ρ₂} 2ρ'^3/Λ(c,ρ')` plus the integrability cells are
   the only remaining gates. (Sprint 039 itself does not file those
   oracles; that is queueable separately.)

5. **First reducer to demonstrate the disk/annulus paper-axiom-free
   chain composes cleanly.** Sprints 034 (disk integrated, modulo
   `hSigmaCmp`) and 038 (annulus integrated, modulo
   `hLambdaBridgeWindow`) were each shipped standalone — their
   compatibility as building blocks for a single closing reducer was
   structural conjecture, not a verified composition. Sprint 039
   verifies it: the type signatures align (sprint 038's open-window
   `c < ρ < 1` shape is exactly what the side-slice non-negativity
   step needs in sprint 035's body), the integrability premises
   match, and the kernel inequality/Z-monotonicity scaffold composes
   verbatim through sprint 035's body. **Without sprint 039, the
   workspace has the disk-half and annulus-half of a paper-axiom-free
   closing reducer but no proof they combine.** This is the
   verification step.

Why this is **not** a numerical-budget push:

* `c_value` stays at `3554/10000`; V39 still discharges the sink
  theorem via `valid_of_eq15` so the score is preserved at
  `1777/5000`.
* The new theorem is purely structural: a closing reducer whose
  closed-form kernel inequality is identical to sprints 014/035, only
  the type-level provenance of the annulus-side bound changes.

Why this is **not** "the same chain" as sprint 035:

* **Different annulus-side body.** Sprint 035 invokes
  `annulusExcess_lower_bound_of_eq8_eq9 paper …` (transitively
  invoking `paper.eq8`, `paper.eq9`, and
  `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9 paper`). Sprint 039
  invokes `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
  …` (paper-axiom-free body, modulo `hLambdaBridgeWindow`).
* **Different witness existential.** Sprint 035 has a 12-cell
  existential; sprint 039 has a 13-cell existential with the new
  `hLambdaBridgeWindow` cell.
* **Different downstream consumer pattern.** Sprint 035 cannot be
  consumed without `paper.eq8`/`paper.eq9` (the annulus side still
  uses them); sprint 039 *can* be consumed without those (e.g., via
  a future oracle on `hLambdaBridgeWindow`).

Why this is **not** "the same chain" as sprint 038:

* **Sprint 038 is an integrated annulus bound** (output type
  `∫ … ≤ annulusExcess …`); sprint 039 is a **closing reducer**
  (output type `ValidKorenblumBound c`). Different layers.
* **Sprint 038 has no disk-side body**; sprint 039 fuses sprint 034's
  disk side with sprint 038's annulus side into a single end-to-end
  reducer. Sprint 039 is the **composition step**, not the standalone
  annulus-side step.
* **Sprint 038's signature has no `valid_of_*` shape**; sprint 039's
  conclusion is `ValidKorenblumBound c`. Sprint 038 cannot discharge
  the candidate contract on its own.

Why this is **not** "the same chain" as sprint 014:

* **Sprint 014's body invokes `diskExcess_upper_bound_via_eq3_eq4`
  (sprint 013, paper-axiom signature `{eq3, eq4}`) and
  `annulusExcess_lower_bound_of_eq8_eq9` (sprint 006, paper-axiom
  signature `{eq8, eq9}`).** Sprint 039's body invokes
  `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
  (sprint 034, paper-axiom-free) and
  `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
  (sprint 038, paper-axiom-free). The **transitive paper-axiom
  signature drops from `{eq3, eq4, eq8, eq9}` to `{}` modulo
  `{hSigmaCmp, hLambdaBridgeWindow}`**.
* **Sprint 014's witness existential has 8 cells**; sprint 039's has
  13. The two new disk-side cells (`hSummable`, `hSummable_n1_c`) and
  the disk-side scalar (`hSigmaCmp`) come from sprint 035; the new
  annulus-side cell (`hLambdaBridgeWindow`) is the structural novelty
  of sprint 039.

Why this is **bounded enough for one Generator session**:

* Sprint 035's body is ~150 lines (lines 5353–5505 of `Reduction.lean`).
  Sprint 039's body is sprint 035's body **verbatim** with **exactly
  one targeted substitution**: lines 5487–5489 (the
  `annulusExcess_lower_bound_of_eq8_eq9 paper hc_pos hcρ₁ hρ₁₂
  hρ₂_lt_one hIntCircle hIntLambdaZ` invocation) replaced with
  `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
  hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
  hLambdaBridgeWindow`. The witness existential
  destructure pattern at line 5389–5392 gains one cell
  (`hLambdaBridgeWindow`). The `paper` parameter is no longer needed by
  the annulus call but is **still required** by the witness existential's
  outer quantifier (the witness must be a `Section2Assumptions`-aware
  family because the disk-side `hSigmaCmp` and the integrability
  hypotheses are still per-`paper`); the only change is dropping the
  `paper` argument from one call site.
* The new generic theorem is ~155 lines (sprint 035's body + 1 new
  cell in destructure + 1 substituted call line + minor signature
  bookkeeping). The new candidate file V39 adds ~50–80 lines per side
  lemma. Total V39 size: ≤ 280 lines.
* All Lean idioms used (`refine`, `obtain`, `intervalIntegral.*`,
  `linarith`, `field_simp`, `calc`) are verbatim from sprint 035.
  No new idioms required.
* The **discharge route at the seed** for `_witness_at_seed` reuses
  V35's `hSigmaCmp` discharge from `paper.eq4_sigmaPlus_bound` and
  V38's `hLambdaBridgeWindow` discharge from
  `eq8eq9_sigma_to_circleBridge_of_eq8_eq9 paper.eq8_sigma_to_liftGap
  paper.eq9_liftGap_to_circleGap` lifted to the universal-quantifier
  shape — both routes are already proved out at the seed in V35 and
  V38, so combining them is trivial (no new analytical content).

### Note on the witness existential shape

Sprint 039's witness existential is sprint 035's existential
(12 cells) with **one new cell** `hLambdaBridgeWindow` inserted **before
`hIntDisk`** (i.e., between `hSigmaCmp` and `hIntDisk` in the
destructure). Concretely the destructure becomes:

```lean
obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hSummable, hSummable_n1_c,
    hSigmaCmp, hLambdaBridgeWindow, hIntDisk, hIntCircle, hIntLambdaZ,
    hIntLambda, hSummable_top, hKernel⟩ := h_witness paper
```

This is a 13-tuple existential: 4 geometric (`ρ₁, ρ₂, hcρ₁, hρ₁₂`),
1 upper-edge (`hρ₂_lt_one`), 2 disk-side summability (`hSummable`,
`hSummable_n1_c`), 1 disk-side scalar oracle (`hSigmaCmp`), **1
annulus-side window-uniform oracle (`hLambdaBridgeWindow`)** ← new,
4 integrability/summability cells (`hIntDisk`, `hIntCircle`,
`hIntLambdaZ`, `hIntLambda`, `hSummable_top` — note that's 5 cells in
the destructure but groups as the integrability/right-edge bundle), and
1 kernel inequality (`hKernel`). Total: 13 cells in the destructure
after `ρ₁, ρ₂`. (Sprint 035 has 12 cells in the destructure after
`ρ₁, ρ₂`.)

### Note on the `paper` parameter

Sprint 035's body still requires the `paper : Section2Assumptions a b
K c` parameter because the witness existential is a
**`Section2Assumptions`-aware family**: the witness's choice of
`ρ₁`, `ρ₂`, integrability cells, summability cells, `hSigmaCmp`, and
`hKernel` may all depend on the specific `(a, b, K, paper)`. Sprint
039 keeps this contract — the witness existential signature is
unchanged in the outer quantifier shape, only the inner conjunction
gains one more cell.

The `paper` parameter is **no longer threaded into the disk-side or
annulus-side body** of the reducer (both calls are paper-axiom-free).
It only appears in the `intro a b K paper` step and in the
`h_witness paper` invocation. This is the structural marker that the
reducer's transitive proof body invokes zero `paper.eq*` field
projections.

### Note on the `_compiles` side lemma

V39's `_compiles` side lemma should exhibit the new reducer's
*type-shape* compilation at the seed without committing to a specific
discharge route for `hSigmaCmp` or `hLambdaBridgeWindow` — it takes
both as universally-quantified Lean hypotheses (along with the
integrability/summability cells) and feeds them into the new reducer
to produce `ValidKorenblumBound c_value`. Concrete witness:
instantiate the witness existential with `ρ₁ := 1/2`, `ρ₂ := 7/10`,
and the integrability/kernel cells as universally-quantified
hypotheses on the side lemma. The `_compiles` side lemma does **not**
use a `paper` instance directly; it asserts the existential abstractly
as a universally-quantified family.

### Note on the `_witness_at_seed` side lemma

V39's `_witness_at_seed` side lemma takes a
`Section2Assumptions a b K c_value` instance, discharges:

- `hSigmaCmp` from `paper.eq4_sigmaPlus_bound` (extract the
  `Σ⁺(c) ≤ Σ⁻(c)` conjunct — the same extraction V35 performs),
- `hLambdaBridgeWindow` from
  `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
  paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap`
  lifted to the universal-quantifier shape (the same lift V38
  performs),

and applies the new reducer to recover sprint 014's exact end-to-end
conclusion at the seed (`c_value`, `ρ₁ := 1/2`, `ρ₂ := 7/10`, plus the
integrability/summability cells as hypotheses). The integrability and
summability cells are taken as additional universally-quantified
hypotheses on the side lemma.

This side lemma serves **two roles**:
(a) confirms the new reducer is a strict generalisation of sprints
014, 035, and 038 (any consumer with `paper.eq4` + `paper.eq8` +
`paper.eq9` access can recover sprint 014's conclusion through the new
chain);
(b) demonstrates the precise discharge route a future
oracle-bearing consumer would substitute (replace the `paper.eq4`
extraction with the disk-side oracle's witness; replace the
`paper.eq8`/`paper.eq9` lift with the annulus-side oracle's witness;
every other cell remains identical).

### Note on the integrability cells

Sprint 035's `hIntCircle` (integrability of
`fun ρ' => 2 * ρ' * circleGap a b ρ'` on `[c, 1]`) is **shared**
between the unused-by-sprint-035-now-used-by-sprint-039 invocation of
sprint 038 (sprint 038 takes `hIntCircle` on the **full** interval
`[c, 1]` for the side-slice non-negativity proofs over `[c, ρ₁]` and
`[ρ₂, 1]`). The cell is already in sprint 035's existential under the
exact shape sprint 038 needs. No new integrability cell is required;
this is a verified composition.

### Note on hypothesis-count and analytical structure

Sprint 035 has 12 cells in the witness destructure after `ρ₁, ρ₂`.
Sprint 039 has 13 cells (one new `hLambdaBridgeWindow` cell). The
hypothesis-count delta is +1. Net: paper-axiom signature on the
**transitive proof body** drops from `{eq8, eq9}` (sprint 035's
annulus side) to `{}`, traded for one window-uniform hypothesis cell.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: Append a new
  generic theorem
  ```lean
  theorem valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window
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
              (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
                PaperAxioms.sigmaMinus a b ρ ≤
                  WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ) ∧
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
  Estimated location: append after sprint 038's
  `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
  (at the current end of `Reduction.lean`, after line ~5800).
  Estimated ~155 lines.

  The proof body is structurally **sprint 035's body verbatim**
  (lines 5386–5505 of `Reduction.lean`) with the following targeted
  substitutions:

  1. **Extend the destructure pattern at lines 5389–5392** to include
     `hLambdaBridgeWindow` between `hSigmaCmp` and `hIntDisk`:

     ```lean
     obtain ⟨ρ₁, ρ₂, hcρ₁, hρ₁₂, hρ₂_lt_one, hSummable, hSummable_n1_c,
         hSigmaCmp, hLambdaBridgeWindow, hIntDisk, hIntCircle,
         hIntLambdaZ, hIntLambda, hSummable_top, hKernel⟩ :=
       h_witness paper
     ```

  2. **Replace the `hAnn` step at lines 5487–5489** (which calls
     `annulusExcess_lower_bound_of_eq8_eq9 paper hc_pos hcρ₁ hρ₁₂
     hρ₂_lt_one hIntCircle hIntLambdaZ`) with a call to sprint 038
     consuming `hLambdaBridgeWindow`:

     ```lean
     have hAnn :=
       annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge
         hc_pos hcρ₁ hρ₁₂ hρ₂_lt_one hIntCircle hIntLambdaZ
         hLambdaBridgeWindow
     ```

     Note the `paper` argument is dropped (sprint 038 has no `paper`
     parameter), and `hLambdaBridgeWindow` is the new final argument.

  3. **Leave everything else byte-for-byte identical** to sprint
     035's body: the `refine`, `intro a b K paper`, the geometric
     scaffolding (`hρ₁_lt_one`, `hcρ₂`, `hc_le_ρ₁`), the disk-side
     `hDisk` invocation of sprint 034, the `hZ_c_nonneg`,
     `hStepA`, `hStepB`, `hZmono`, `hIntLambda_mul`, `hPointwise`,
     `hStepC` blocks, and the final `change` + `calc` chain (the
     `calc` chain's structure is unchanged: `diskExcess ≤ c^4·Z_c ≤
     (∫…)·Z_c = ∫(…·Z_c) ≤ ∫(…·Z_ρ') ≤ annulusExcess`, with the
     final inequality now provided by sprint 038's `hAnn` instead of
     sprint 006's).

- `ProofRefinement/Korenblum/Candidates/V39.lean`: Create a new
  candidate file at the same `c = 0.3554` that:
  1. Imports `ProofRefinement.Korenblum.Proof.Main`,
  2. Defines `c_value : ℝ := 3554 / 10000` (verbatim from V38),
  3. Re-declares the seed `axiom hEq15_seed_3554` (verbatim from V38),
  4. Adds two side lemmas exercising the new generic reducer:
     - `v39_valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window_compiles`:
       exhibits the new reducer's witness-existential shape at the
       seed by feeding a universally-quantified family of `(a, b, K,
       paper) → (witness conjunction)` and obtaining
       `ValidKorenblumBound c_value`. The integrability,
       summability, scalar oracle, and window-uniform oracle cells are
       all taken as universally-quantified hypotheses on the side
       lemma. Concrete instantiation: `ρ₁ := 1/2`, `ρ₂ := 7/10`,
       `K := paper.K` (or any concrete `K` per the witness shape).
     - `v39_valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window_witness_at_seed`:
       takes a `Section2Assumptions a b K c_value` instance and the
       same integrability/summability/kernel hypotheses as
       universally-quantified cells, **discharges `hSigmaCmp` from
       `paper.eq4_sigmaPlus_bound`** (extracting the
       `Σ⁺(c) ≤ Σ⁻(c)` conjunct), **discharges `hLambdaBridgeWindow`
       from `PaperAxioms.eq8eq9_sigma_to_circleBridge_of_eq8_eq9
       paper.eq8_sigma_to_liftGap paper.eq9_liftGap_to_circleGap`
       lifted to the universal-quantifier shape**, and applies the new
       reducer at `ρ₁ := 1/2`, `ρ₂ := 7/10` to recover sprint 014's
       end-to-end conclusion via the new chain.
  5. Discharges `korenblum_constant_search : ValidKorenblumBound c_value`
     via `valid_of_eq15` (verbatim from V38) — the new reducer is
     materialised in side lemmas, **not** as the sink theorem's
     discharge route, since neither `hSigmaCmp` nor `hLambdaBridgeWindow`
     is yet discharged via an oracle (they are still discharged from
     `paper.eq4`, `paper.eq8`, `paper.eq9` field projections in the
     side lemma's discharge route, so going through the new reducer
     for the sink theorem would not change the seed-axiom usage but
     would add structural overhead — sprint 039 is about isolating the
     two oracle cells, not about substituting the sink theorem's
     discharge route).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V39` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run ProofRefinement/Korenblum/Evaluator.py --file ProofRefinement/Korenblum/Candidates/V39.lean` succeeds.
3. The evaluator reports `score = 1777/5000` (i.e., V39 ties V38 at the
   seed; the new theorem is structural and does not change `c_value`).
4. The evaluator's `axioms_used` list is exactly the V0 seed plus
   standard Lean axioms: `{propext, Classical.choice, Quot.sound,
   ProofRefinement.Korenblum.Candidates.V39.hEq15_seed_3554}`. No new
   free-floating axioms, no oracle entries.
5. The new theorem
   `valid_of_disk_series_modulo_sigma_compare_annulus_series_modulo_lambda_bridge_full_window`
   appears in `ProofRefinement/Korenblum/Proof/Reduction.lean` and is
   exercised in `Candidates/V39.lean`'s side lemmas.
6. The proof body of the new theorem **does not invoke** any
   `paper.eq*_*` field projection — body is paper-axiom-free.
   Greppable check: in the body of the new theorem, the count of
   `paper.eq` substrings is **0**. (The `paper : Section2Assumptions
   ...` parameter still appears via the `intro a b K paper` step and
   the `h_witness paper` invocation, but no `paper.eq*` field is
   projected anywhere in the body.)
7. The proof body **does not invoke** `annulusExcess_lower_bound_of_eq8_eq9`
   (sprint 006) — sprint 038 is the substitute. Greppable check: count
   of `annulusExcess_lower_bound_of_eq8_eq9` in the body of the new
   theorem is **0**.
8. The proof body **does not invoke**
   `OneModePaperBridge.circleGap_nonneg_of_eq8_eq9` (transitively
   eliminated via sprint 038's body). Greppable check: count of
   `circleGap_nonneg_of_eq8_eq9` in the body of the new theorem is
   **0**.
9. The proof body **does not invoke** `diskExcess_upper_bound_via_eq3_eq4`
   (sprint 013, transitively eliminated via sprint 034). Greppable
   check: count of `diskExcess_upper_bound_via_eq3_eq4` in the body of
   the new theorem is **0**.
10. The proof body invokes
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    (sprint 034) at least once for the disk-side step. Greppable check:
    count of
    `diskExcess_upper_bound_via_series_only_modulo_sigma_compare`
    substrings in the body of the new theorem is ≥ 1.
11. The proof body invokes
    `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
    (sprint 038) at least once for the annulus-side step. Greppable
    check: count of
    `annulusExcess_lower_bound_via_series_only_modulo_lambda_bridge`
    substrings in the body of the new theorem is ≥ 1.
12. The new theorem's signature includes the **window-uniform**
    `hLambdaBridgeWindow` hypothesis cell:
    ```lean
    (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      PaperAxioms.sigmaMinus a b ρ ≤
        WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ)
    ```
    Greppable check: in the new theorem's signature region,
    `WangOuter.paperLambda K c ρ * PaperAxioms.circleGap a b ρ`
    appears.
13. The new theorem's signature includes the disk-side `hSigmaCmp`
    hypothesis cell `(PaperAxioms.sigmaPlus a b c ≤
    PaperAxioms.sigmaMinus a b c)` (verbatim from sprint 035).
    Greppable check: `PaperAxioms.sigmaPlus a b c ≤
    PaperAxioms.sigmaMinus a b c` appears in the signature.
14. The V39 `_witness_at_seed` side lemma takes a
    `Section2Assumptions a b K c_value` instance as parameter and
    invokes both `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` (in the
    discharge of `hLambdaBridgeWindow`) and `paper.eq4_sigmaPlus_bound`
    (in the discharge of `hSigmaCmp`). Greppable check: both
    `eq8eq9_sigma_to_circleBridge_of_eq8_eq9` and
    `eq4_sigmaPlus_bound` appear in the body of the
    `_witness_at_seed` side lemma. This confirms the new reducer
    **strictly generalises** sprint 014 (any consumer with
    `paper.eq4` + `paper.eq8` + `paper.eq9` access can recover sprint
    014's conclusion through the new chain).
15. The new theorem **uses the `paper` parameter** only in the
    `intro a b K paper` step and the `h_witness paper` invocation —
    no `paper.eq*` or `paper.K_*` field projection appears anywhere
    in the body. Greppable check: in the body of the new theorem
    (lines after the destructure pattern), the substring `paper.`
    appears 0 times. (The destructure line itself uses `paper` in
    `h_witness paper`, but that is the existential application, not
    a field projection.)
16. The new theorem invokes `intervalIntegral.integral_mono_on_of_le_Ioo`
    at least once (verbatim from sprint 035's body). Greppable check:
    count of `intervalIntegral.integral_mono_on_of_le_Ioo` in the
    body of the new theorem is ≥ 1.
17. The new theorem invokes `sigmaZeroMinus_monotone_of_summable`
    (sprint 011) at least once for the `Z_c → Z_ρ'` cascade. Greppable
    check: count of `sigmaZeroMinus_monotone_of_summable` in the body
    of the new theorem is ≥ 1.
18. The new theorem's witness existential has **13 cells** after
    `ρ₁, ρ₂` (compared to sprint 035's 12). Greppable check: the
    `obtain ⟨ρ₁, ρ₂, …⟩` pattern in the body has 15 names total
    (`ρ₁, ρ₂` + 13 cells).

## Out of scope

- Edit older candidates V0–V38.
- Change the final theorem statement.
- Add a free-floating new axiom; the only allowed axiom in V39 is the
  same `hEq15_seed_3554` that V0–V38 use.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- File a proposal for an oracle on `hSigmaCmp` or `hLambdaBridgeWindow`.
  Sprint 039 isolates the two cells but does not file the oracles.
  Future planners may file `Proposals/proposal_<NNN>_*.md` for
  numerical oracles on these cells; sprint 039 is decoupled from
  those proposals.
- Land any candidate at `c > 0.3554`. Sprint 039 does not raise
  `c_value`. The eventual numerical push is the *consumer* of sprint
  039 combined with future oracles on `hSigmaCmp` and
  `hLambdaBridgeWindow`, not sprint 039 itself.
- Switch the sink theorem's discharge route from `valid_of_eq15` to
  the new reducer. Going through the new reducer would currently
  require discharging `hSigmaCmp` and `hLambdaBridgeWindow` from
  `paper.eq4`/`paper.eq8`/`paper.eq9` projections (the routes
  exhibited in `_witness_at_seed`), which uses the same paper axioms
  the seed `valid_of_eq15` route already uses indirectly through
  `eq14_combined`. The structural payoff of sprint 039 is the
  isolation of two oracle cells, not the substitution of the sink
  theorem's discharge route.
- Land a paper-axiom-free closing reducer through any *other* chain
  (e.g., a branch-1 or branch-2 sub-window variant, or a variant
  fusing sprint 026's `{eq4}`-only disk bound with sprint 038). The
  full-window `{hSigmaCmp, hLambdaBridgeWindow}`-cell chain is the
  unique closing reducer we ship in sprint 039.
- Strengthen either oracle cell (e.g., to a strict inequality or to
  an uniformly-bounded family on a closed window). Sprint 039's
  hypothesis shapes mirror sprints 035 and 038 exactly; alternative
  shapes would introduce signature-mismatch bookkeeping with the
  upstream lemmas.
- Series-derive `eq8` or `eq9` themselves (i.e., produce a workspace
  lemma `eq8eq9_sigma_to_circleBridge_via_series` paper-axiom-free).
  This is structurally out of scope (sprint 038's "Out of scope"
  notes the same).
- Series-derive `Σ⁺(c) ≤ Σ⁻(c)` from termwise structure alone (i.e.,
  produce a paper-axiom-free workspace lemma giving the inequality
  without `paper.eq4`). This is the analytical content of `eq4`'s
  second conjunct; sprints 028, 032, 033 explored the surrounding
  `Σ⁺`/`Σ⁻` structure but the cross-`Σ⁺(c) ≤ Σ⁻(c)` inequality
  itself is non-derivable from termwise arguments on N1 alone (it
  involves summation over both partitions). This is the precise
  reason the bulletin lists oracle/proposal-backed numerical
  certificates as the right discharge route.
- Materialise sprint 039 with a different choice of disk-side or
  annulus-side lemma (e.g., sprint 026 + sprint 038, or sprint 030 +
  sprint 038). Sprint 039 commits to the sprint 034 + sprint 038
  pairing as the unique paper-axiom-free pair. Other pairings are
  queueable separately.

## Time budget

≤ 60 minutes runtime. (Sprint 035's body is ~150 lines; sprint 039's
body is sprint 035's body verbatim with one cell added to the
destructure and one call site swapped. The new theorem signature is
sprint 035's signature with one new cell added to the witness
existential conjunction. V39 candidate adds two side lemmas at
~50–80 lines each, both reusing discharge routes from V35 and V38.
Total V39 size: ≤ 280 lines.)

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`
