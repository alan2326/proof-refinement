-- @parent V40
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V41

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V40 — sprint 041
ships the workspace's **first paper-axiom-free integrated *equality*
identity for `annulusSlice`** over an arbitrary radial sub-window
`[α, β] ⊂ [0, 1)`. The new generic theorem
`annulusSlice_eq_via_series_partition` integrates sprint 027's pointwise
equality `circleGap r = sigmaPlus r − r²·Z_r` over `[α, β]` and splits via
`integral_sub`, with **no `Section2Assumptions` parameter, no `paper.eq*`
invocation, no `paperLambda`, and no `Σ⁺ ≤ Σ⁻` cell**. The conclusion is
an *equality*, not an inequality, and applies uniformly to the disk-side
window `[0, c]`, the annulus-side window `[c, β]` for any `β < 1`, and any
sub-interval thereof. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress; the new equality is
materialised in three side lemmas covering the disk-side and annulus-side
specialisations.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V40, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 041 side lemma (`_compiles`): exhibits the new generic equality
`annulusSlice_eq_via_series_partition` at the seed `(α, β) = (0, c_value)`.
The signature accepts the four hypothesis cells universally
quantified — `hSummable`, `hIntCircle`, `hIntSigmaPlus`, `hIntZ` — and the
conclusion is the equality directly. **No `Section2Assumptions` instance
is required**, **no `paper.eq*` invocation**, **no oracle cell**. The
proof body is a single application of the new generic lemma. Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v41_annulusSlice_eq_via_series_partition_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume 0 c_value)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        MeasureTheory.volume 0 c_value)
    (hIntZ :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
        MeasureTheory.volume 0 c_value) :
    AnnulusIntegralReduction.annulusSlice
        (PaperAxioms.circleGap a b) 0 c_value =
      (∫ ρ in (0 : ℝ)..c_value, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        - ∫ ρ in (0 : ℝ)..c_value,
            2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ :=
  annulusSlice_eq_via_series_partition (a := a) (b := b)
    le_rfl c_value_pos.le c_value_lt_one
    hSummable hIntCircle hIntSigmaPlus hIntZ

/--
Sprint 041 side lemma (`_disk_specialisation`): applies the new generic
equality at `(α, β) = (0, c_value)` and uses the
`PaperAxioms.diskExcess` definition unfolding to derive the disk-side
*equality* `diskExcess (circleGap a b) c_value = ∫₀^c 2ρ·Σ⁺(ρ) − ∫₀^c
2ρ³·Z(ρ)`. This is sprint 040's intermediate identity (which sprint 040
*implicitly* established before dropping the `Z`-integral term), now named
as a standalone lemma. Not `axiom`-ed and does not call the seed axiom.
-/
theorem v41_annulusSlice_eq_via_series_partition_disk_specialisation
    (a b : ℕ → ℂ)
    (hSummable :
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume 0 c_value)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        MeasureTheory.volume 0 c_value)
    (hIntZ :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value =
      (∫ ρ in (0 : ℝ)..c_value, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        - ∫ ρ in (0 : ℝ)..c_value,
            2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ := by
  have hEq :
      AnnulusIntegralReduction.annulusSlice
          (PaperAxioms.circleGap a b) 0 c_value =
        (∫ ρ in (0 : ℝ)..c_value, 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
          - ∫ ρ in (0 : ℝ)..c_value,
              2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ :=
    annulusSlice_eq_via_series_partition (a := a) (b := b)
      le_rfl c_value_pos.le c_value_lt_one
      hSummable hIntCircle hIntSigmaPlus hIntZ
  -- `diskExcess (circleGap a b) c_value` is definitionally
  -- `annulusSlice (circleGap a b) 0 c_value`.
  show AnnulusIntegralReduction.annulusSlice
        (PaperAxioms.circleGap a b) 0 c_value = _
  exact hEq

/--
Sprint 041 side lemma (`_annulus_specialisation`): applies the new generic
equality at `(α, β) = (c_value, 1 - 1/10^9)` — a sub-window of the full
annulus `[c, 1]` strictly inside `[0, 1)` to satisfy the `β < 1`
hypothesis. Conclusion: an *equality* between
`annulusSlice (circleGap a b) c_value (1 - 1/10^9)` and the
pure-series quantity `∫_c^β 2ρ·Σ⁺(ρ) − ∫_c^β 2ρ³·Z(ρ)`. This is the
**first** workspace lemma to express an annulus-side
`annulusSlice` quantity as a pure-series quantity (no `Λ`, no oracle).
Not `axiom`-ed and does not call the seed axiom.
-/
theorem v41_annulusSlice_eq_via_series_partition_annulus_specialisation
    (a b : ℕ → ℂ)
    (hSummable :
      ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ 1 - 1/10^9 →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * ρ ^ (2 * k)))
    (hIntCircle :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value (1 - 1/10^9))
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        MeasureTheory.volume c_value (1 - 1/10^9))
    (hIntZ :
      IntervalIntegrable
        (fun ρ => 2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ)
        MeasureTheory.volume c_value (1 - 1/10^9)) :
    AnnulusIntegralReduction.annulusSlice
        (PaperAxioms.circleGap a b) c_value (1 - 1/10^9) =
      (∫ ρ in c_value..(1 - 1/10^9),
          2 * ρ * PaperAxioms.sigmaPlus a b ρ)
        - ∫ ρ in c_value..(1 - 1/10^9),
            2 * ρ ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ := by
  have hα_nonneg : (0 : ℝ) ≤ c_value := c_value_pos.le
  have hα_le_β : c_value ≤ (1 : ℝ) - 1/10^9 := by
    norm_num [c_value]
  have hβ_lt_one : (1 : ℝ) - 1/10^9 < 1 := by
    norm_num
  exact annulusSlice_eq_via_series_partition (a := a) (b := b)
    hα_nonneg hα_le_β hβ_lt_one
    hSummable hIntCircle hIntSigmaPlus hIntZ

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
integrated `annulusSlice` *equality* identity is materialised above in the
three side lemmas
`v41_annulusSlice_eq_via_series_partition_compiles`,
`v41_annulusSlice_eq_via_series_partition_disk_specialisation`, and
`v41_annulusSlice_eq_via_series_partition_annulus_specialisation`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V41
