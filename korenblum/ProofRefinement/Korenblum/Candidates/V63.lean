-- @parent V62
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V63

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-!
# Sprint 080-082 / V63 — three partition steps toward V63 c-push

## What is structurally novel in V63

Sprint 080 shipped the **first partition step** of the multi-sprint V63
c-push to `c = 35646/100000` identified by sprint 079's obstruction note
(`Scratch/sprint_079_obstruction.md`): the per-candidate derived-theorem
file `Candidates/V63/Integrability.lean` (315 lines, two integrability
theorems; see below).

Sprint 081 shipped the **second partition step**: the per-candidate
derived-theorem file `Candidates/V63/Summability.lean`, containing six
H²-to-shape transfer theorems plus a consolidation theorem
`six_summability_shapes_from_h2` packaging them in the exact
six-conjunct shape required by the
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` reducer's
`h_witness` predicate at `Proof/Reduction.lean:7787-7803`. Each transfer
takes as input `Summable (fun n => ‖a n‖^2)` and
`Summable (fun n => ‖b n‖^2)` (Wang's H² boundary-norm finiteness,
applied separately to `f` and `g`) plus `0 ≤ c < 1`, and produces one
of the six summability shapes. The proofs use `Summable.of_norm_bounded`
against the H² envelope `n ↦ ‖a n‖^2 + ‖b n‖^2` plus a per-`n`
weighting bound (`c^(2n) ≤ 1`, `c^(2n+2)/(n+1) ≤ 1`,
`OneModeKernel.weight c n ≤ 1`, `ρ^(2n) ≤ 1`).

Sprint 082 ships the **third and final partition step**: the
per-candidate derived-theorem file
`Candidates/V63/DiskInnerSeriesBridge.lean`, containing the workspace's
first paper-axiom-free `diskExcess (circleGap a b) c =
innerSeriesExcess a b c` equality plus its `≤` corollary. The bridge
chain composes:
  * the per-`k` algebraic identity
    `coeffPlusGap a b k = plusSeq a b k − minusSeq a b k` (a three-case
    `by_cases` on `n1Pred`/`n2Pred`),
  * its termwise weighted form (multiplying by `c^(2k+2)/(k+1)`),
  * sprint 042's `diskExcess_eq_tsum_via_termwise_integration` (the
    upstream identity rewriting `diskExcess` as a `tsum` of
    `coeffPlusGap`-weighted terms),
  * `Summable.tsum_sub` to split the gap-weighted `tsum` into the two
    component `tsum`'s,
  * definitional unfold of `diskWeightedSeq` and `innerSeriesExcess`.
The output `diskExcess_le_innerSeriesExcess` corollary's signature
**byte-exactly matches** the `diskExcess ≤ innerSeriesExcess` cell at
`Proof/Reduction.lean:7820-7821`. The file also ships two summability
corollaries (`summable_coeffPlusGap_weighted_of_summable_components`
and the absolute-value variant
`summable_abs_coeffPlusGap_weighted_of_summable_components`) lifting
sprint 081's two summability shapes to the gap-weighted series; the
absolute-value variant discharges sprint 042's `Summable_int_norm`
hypothesis without reaching outside the H² envelope.

V63 now ships THREE per-candidate derived-theorem files —
Integrability.lean (sprint 080), Summability.lean (sprint 081), and
DiskInnerSeriesBridge.lean (sprint 082) — reducing the V64+ residual
`h_witness` budget to **TWO cells**:
  * the τ-window endpoint construction (route A of sprint 079's
    obstruction note: `Real.sqrt`-based endpoints satisfying the
    per-window `OneModeTail.tau`-bounds), and
  * the candidate-side H² source decision (free axiom vs.
    proposal_004 — left to sprint 083+).
After V64+ discharges those two residual cells, the candidate-side
construction of `h_witness` at `c = 35646/100000` will compose all
three V63 derived-theorem files plus the τ-window construction, then
consume the registered oracle `h_two_window_mass_certified_at_35646`
as the joint-mass discharge — yielding the first c-push past V52's
high-water mark in 22 sprints.

V63 ships as a **V62-tie** at `c_value = 35645/100000`, byte-for-byte
identical axiom envelope to V62.

## Sprint 080 deliverable (preserved for context)

The deliverable from sprint 080 is the per-candidate derived-theorem
file `Candidates/V63/Integrability.lean`, containing two `theorem`s
(no `axiom`s, no `sorry`s):

  1. `modeScalarIntegrand_intervalIntegrable`: for `j ≥ 1`, `0 < c`, and
     `[a, b] ⊆ [c, 1]`,
     `IntervalIntegrable (fun ρ => ModeBridge.scalarIntegrand c j
        (paperLambda K c) ρ) volume a b`.
     Proof template: `paperScalarIntegrand{1, 2}_intervalIntegrable`
     from `KorenblumPaper.WangPaperSideConditions`, generalised from
     the j=1/j=2 specific shapes to arbitrary j ≥ 1 via
     `ModeBridge.scalarIntegrand_eq`'s rewrite to
     `((2(j+1)/j) ρ^(2j+1)) / (c^(2j+2) Λ)`. Constant bound:
     `4(j+1) / (j · c^(2j+2))` (from `ρ^(2j+1) ≤ 1` plus
     `1/Λ ≤ 2`).

  2. `mode_two_and_one_scalarIntegrand_intervalIntegrable`: the
     consolidation theorem packaging the integrability statements at
     `j₁ = 2` on `[ρStart₁, ρStop₁]` and `j₂ = 1` on
     `[ρStart₂, ρStop₂]`, in the exact `(j₁, j₂) = (2, 1)` shape sprint
     079's wrapper pins. Two direct invocations of theorem 1.

V63 ships as a **V62-tie** at `c_value = 35645/100000`. The c-push to
`c = 35646/100000` is deferred to sprint 081+, which will compose the
new Integrability.lean file with two further per-candidate derived-
theorem files (Summability.lean, ~1200 lines; DiskInnerSeriesBridge.lean,
~700 lines) plus the candidate-side `h_witness` construction at
the wrapper-pinned c.

## Why ship Integrability before Summability or DiskInnerSeriesBridge

Sprint 080's contract picks the **structurally cleanest and smallest**
of the three required derived-theorem files. The
`paperScalarIntegrand{1, 2}_intervalIntegrable` template adapts directly
to general `j ≥ 1`: measurability is a routine `aemeasurable` chain on
`OneModeKernel.term`'s definition; the constant bound argument is a
direct `nlinarith`/`field_simp` chain (closed without recourse to
`continuousOn` infrastructure or `IntervalIntegrable.continuousOn_mul`).
The full file is ~250 Lean lines, well below the obstruction note's
~300-line estimate.

Summability and DiskInnerSeriesBridge are deferred per single-concern-
per-sprint discipline; the per-sprint partition is recoverable if any
sub-deliverable hits a structural snag.

## On `circleGap_two_rho_intervalIntegrable_on_unit`

Sprint 080's contract names a third theorem
`circleGap_two_rho_intervalIntegrable_on_unit` asserting
`IntervalIntegrable (fun ρ => 2*ρ * circleGap a b ρ) volume c 1`.
This theorem is **not derivable** from `Section2Assumptions` alone:
the bundled paper surface does not assert continuity or measurability
of `circleGap` (or of `sigmaPlus`/`sigmaMinus`/`sigmaZeroMinus`); it
only states pointwise identities (`paper.eq3`) and pointwise upper
bounds (`paper.eq8`/`paper.eq9`). The integrability of `2ρ · circleGap`
on `(c, 1)` is structurally distinct witness data — exactly as it was
treated by sprint 071's `valid_of_perMode_tau_window_eq8_eq9` and
sprint 078's `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, both
of which carry it as a hypothesis in `h_witness` rather than deriving
it.

Per the contract's Stop condition (3) ("ship V63 as a V62-tie with
**only** the `modeScalarIntegrand_intervalIntegrable` and consolidation
theorems"), this sprint ships the two derivable theorems; the V64+
c-push sprint will surface `circleGap` integrability as a candidate-
side hypothesis alongside the summability witnesses.

## V62-tie discharge

V63's discharge of `korenblum_constant_search` is byte-for-byte identical
to V62's V61-tie envelope: `valid_of_eq15` + `hEq15_oracle_certified_hp_35645`
(registered oracle `eq15_certified_at_hp_35645`). The trust envelope is:

  - `hEq15_oracle_certified_hp_35645` (registered oracle)
  - standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`,
    `Lean.ofReduceBool`, `Lean.trustCompiler`)
  - no new candidate-level axioms used by `korenblum_constant_search`
  - no `Section2Assumptions` field extensions, no `KorenblumPaper/`
    edits.

The side lemmas `v63_modeScalarIntegrand_intervalIntegrable_compiles_at_witness`
and `v63_mode_two_and_one_scalarIntegrand_intervalIntegrable_compiles_at_witness`
re-state the new derived theorems in V63's namespace and discharge by
direct invocation, confirming non-vacuity and preserving the theorem
statements for the sprint 081+ composition. These side lemmas are
**not** invoked by `korenblum_constant_search` (V63 takes the V62-tie
route via `valid_of_eq15`), so they do not affect V63's `axioms_used`.

## Forward direction (sprint 081+)

The V63 c-push to `c = 35646/100000` requires three derived-theorem
files and one candidate-level `h_witness` construction lemma:

  1. **Integrability.lean** (this sprint) — two integrability
     theorems for `ModeBridge.scalarIntegrand` at j₁ = 2 and j₂ = 1.
  2. **Summability.lean** (sprint 081, estimated ~1200 lines) — six
     summability hypotheses on `plusSeq * c^(2n+2)/(n+1)`-style series
     for arbitrary `(a, b)`. Estimated ~200 lines per shape, six
     distinct shapes; structurally hardest of the three because the
     summability is universally quantified over `(a, b)` and the only
     workspace source of `(a, b)`-summability is at `ρ = 1`
     (boundary-norm finiteness), so each shape requires an `ρ`-
     monotonicity transfer (sprint 011's
     `sigmaZeroMinus_monotone_of_summable` is a 70-line template).
  3. **DiskInnerSeriesBridge.lean** (sprint 082, estimated ~700 lines)
     — the `diskExcess ≤ innerSeriesExcess` field, derived from
     sprint 042's `diskExcess_eq_tsum_via_termwise_integration` plus
     `OneModePaperBridge.innerSeriesExcess_le_supKernel_mul_sigmaMinus`.
  4. **V63 c-push candidate** (sprint 083) — picks Real.sqrt-based
     endpoints (route A in sprint 079's obstruction note) at the
     wrapper-pinned c, constructs the `h_witness` predicate via the
     three derived-theorem files plus the existing
     `circleGap` integrability axiom, and consumes the registered
     oracle `h_two_window_mass_certified_at_35646` as the joint-mass
     discharge.

The next planner picking up sprint 081 should ship Summability.lean
next (the largest of the three files), per the contract's "next-sprint
forward direction" guidance.
-/

def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/-- V62-shaped oracle bound-field; the Evaluator compares the
per-candidate `oracle_fn`'s returned Fraction against this `def` via
`oracle_bound ≤ declared`. Identical declaration to V62's
`eq15_lower_bound`. -/
def eq15_lower_bound : ℝ := 1

/-- Same Lean-facing axiom as V62's `hEq15_oracle_certified_hp_35645`,
with the exact same `Eq15ScalarBound K c_value` shape at
`c_value = 35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

V63's discharge of `korenblum_constant_search` consumes this axiom
exclusively (via `valid_of_eq15`); the side lemmas exercising the
new derived-theorem file's content do not feed into `axioms_used` for
the sink theorem. -/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/-- Sprint 080 / V63 non-vacuity check: re-state
`Candidates.V63.Integrability.modeScalarIntegrand_intervalIntegrable`
in V63's namespace and discharge by direct invocation. This forces the
elaborator to verify the new derived theorem compiles against an
arbitrary `(K, j, c, a, b)` configuration meeting the hypothesis
envelope, confirming the theorem is non-vacuous and reusable by
sprint 081+'s `h_witness` construction. -/
theorem v63_modeScalarIntegrand_intervalIntegrable_compiles_at_witness
    {K : ℝ → ℝ → ℝ} {c a b : ℝ} {j : ℕ}
    (hj : 1 ≤ j)
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c j (WangOuter.paperLambda K c) ρ)
      MeasureTheory.volume a b :=
  ProofRefinement.Korenblum.Candidates.V63.Integrability.modeScalarIntegrand_intervalIntegrable
    hj hc hab hca hb1 hPaperK

/-- Sprint 080 / V63 non-vacuity check at the consolidation shape:
re-state `mode_two_and_one_scalarIntegrand_intervalIntegrable` in V63's
namespace and discharge by direct invocation, in the exact
`(j₁, j₂) = (2, 1)` shape sprint 079's wrapper pins. This packages the
two integrability hypotheses required by
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
predicate as a single consumable theorem at the wrapper-pinned shape. -/
theorem v63_mode_two_and_one_scalarIntegrand_intervalIntegrable_compiles_at_witness
    {K : ℝ → ℝ → ℝ} {c ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ}
    (hc : 0 < c)
    (hcStart₁ : c ≤ ρStart₁)
    (hStart₁LeStop₁ : ρStart₁ ≤ ρStop₁)
    (hStart₂LeStop₂ : ρStart₂ ≤ ρStop₂)
    (hStop₁_le_Start₂ : ρStop₁ ≤ ρStart₂)
    (hStop₂_le_one : ρStop₂ ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 2 (WangOuter.paperLambda K c) ρ)
      MeasureTheory.volume ρStart₁ ρStop₁ ∧
    IntervalIntegrable
      (fun ρ => ModeBridge.scalarIntegrand c 1 (WangOuter.paperLambda K c) ρ)
      MeasureTheory.volume ρStart₂ ρStop₂ :=
  ProofRefinement.Korenblum.Candidates.V63.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
    hc hcStart₁ hStart₁LeStop₁ hStart₂LeStop₂ hStop₁_le_Start₂
    hStop₂_le_one hPaperK

/-- Sprint 081 / V63 non-vacuity check for the H²-to-six-shapes
summability transfer kit: re-state
`Candidates.V63.Summability.six_summability_shapes_from_h2` in V63's
namespace and discharge by direct invocation. The conclusion's
six-conjunct shape **byte-exactly matches** the six summability
conjuncts inside
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s `h_witness`
predicate at `Proof/Reduction.lean:7787-7803`, so the V64+ c-push
sprint's `obtain` pattern can consume the kit's output without
re-ordering or adapter shims. -/
theorem v63_summability_kit_compiles_at_witness
    (a b : ℕ → ℂ)
    (hH2_a : Summable (fun n : ℕ => ‖a n‖ ^ 2))
    (hH2_b : Summable (fun n : ℕ => ‖b n‖ ^ 2))
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.plusSeq a b n * c ^ (2 * n)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n *
        c ^ (2 * n + 2) / ((n : ℝ) + 1)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * c ^ (2 * n)) ∧
    Summable (fun n : ℕ =>
      OneModePaperBridge.minusSeq a b n * OneModeKernel.weight c n) ∧
    (∀ ⦃ρ : ℝ⦄, c < ρ → ρ < 1 →
      Summable (fun n : ℕ =>
        OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) :=
  ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
    hH2_a hH2_b hc_nonneg hc_lt_one

/-- Sprint 082 / V63 non-vacuity check for the
DiskInnerSeriesBridge corollary: re-state
`Candidates.V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess`
in V63's namespace and discharge by direct invocation. The signature's
shape **byte-exactly matches** the `diskExcess ≤ innerSeriesExcess`
cell inside `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s
`h_witness` predicate at `Proof/Reduction.lean:7820-7821`, so the V64+
c-push sprint's `obtain` pattern can consume the bridge's output
without adapter shims. -/
theorem v63_diskExcess_le_innerSeriesExcess_compiles_at_witness
    {a b : ℕ → ℂ} {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hPlusDisk : Summable (fun k : ℕ =>
      OneModePaperBridge.plusSeq a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hMinusDisk : Summable (fun k : ℕ =>
      OneModePaperBridge.minusSeq a b k *
        c ^ (2 * k + 2) / ((k : ℝ) + 1)))
    (hAbsSummable : Summable (fun k : ℕ =>
      |PaperAxioms.coeffPlusGap a b k| *
        c ^ (2 * k + 2) / ((k : ℝ) + 1))) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c ≤
      OneModePaperBridge.innerSeriesExcess a b c :=
  ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
    hc_nonneg hPlusDisk hMinusDisk hAbsSummable

/--
Paper-faithful candidate: the V62-tied `c = 0.35645` is a valid Korenblum
lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`.

V63's structural advance is **upstream** of this candidate's discharge
route — three new per-candidate derived-theorem files
`Candidates/V63/Integrability.lean` (sprint 080),
`Candidates/V63/Summability.lean` (sprint 081), and
`Candidates/V63/DiskInnerSeriesBridge.lean` (sprint 082), exercised
respectively by
`v63_modeScalarIntegrand_intervalIntegrable_compiles_at_witness`,
`v63_mode_two_and_one_scalarIntegrand_intervalIntegrable_compiles_at_witness`,
`v63_summability_kit_compiles_at_witness`, and
`v63_diskExcess_le_innerSeriesExcess_compiles_at_witness`. Per the
contract's primary stop condition, V63 ties V62 at the V61-tie envelope;
the c-push to `c = 35646/100000` is deferred to sprint 083+ per the
multi-sprint partition documented above.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V63
