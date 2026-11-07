-- @parent V39
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V40

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V39 — sprint 040
ships the workspace's **first integrated `diskExcess` upper bound of shape
`c²·sigmaPlus a b c`** (every prior integrated disk bound lands on the
`Z_c` / `Z_ρ` / two-`Z` family), the **first integrated disk bound with
empty paper-axiom signature *and* no `Σ⁺ ≤ Σ⁻` oracle cell**, the **first
workspace `intervalIntegral.integral_sub` invocation in a `diskExcess`
upper bound**, and the **first downstream consumer of sprint 027's
*equality* in an integrated bound** (vs sprint 025's *inequality* used by
sprints 026, 034). The new generic theorem
`diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
integrates sprint 027's pointwise equality
`circleGap r = sigmaPlus r − r²·Z_r` over `[0, c]`, splits via
`integral_sub`, bounds the `2r·sigmaPlus` integrand via sprint 032's
`sigmaPlus_monotone_of_summable`, and drops the non-negative
`2r³·Z_r` summand via `sigmaZeroMinus_nonneg_of_pos`. The sink theorem
is still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V39, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 040 side lemma: exercise the brand-new paper-axiom-free integrated
disk bound `diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only`
at the seed `c = c_value`. The signature exhibits the new lemma's
hypothesis shape — five cells: `hSummable` (universal-over-`[0, c_value)`
series summability of the unconditioned `coeffPlusGap · r^(2k)`),
`hSummable_n1_c` (N1-restricted summability at the upper anchor `c_value`,
needed for sprint 032's monotonicity), `hIntCircle`
(integrability of `2r·circleGap` on `[0, c_value]`), `hIntSigmaPlus`
(integrability of `2r·sigmaPlus` on `[0, c_value]`), and `hIntZ`
(integrability of `2r³·Z_r` on `[0, c_value]`). Crucially, **no
`Section2Assumptions` instance is needed** — this side lemma does not use
a `paper` parameter, and **no oracle-shaped cell** (`Σ⁺ ≤ Σ⁻`) appears.
The proof body is a single application of the new generic lemma. Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_compiles
    (a b : ℕ → ℂ)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hIntCircle :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r)
        MeasureTheory.volume 0 c_value)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b r)
        MeasureTheory.volume 0 c_value)
    (hIntZ :
      IntervalIntegrable
        (fun r => 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 2 * PaperAxioms.sigmaPlus a b c_value :=
  diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only
    c_value_pos hSummable hSummable_n1_c hIntCircle hIntSigmaPlus hIntZ

/--
Sprint 040 structural witness lemma: demonstrate that any candidate
carrying a `Section2Assumptions a b K c_value` instance can use
`paper.eq4_sigmaPlus_bound`'s second and third conjuncts to upper-bound
the new bound's RHS `c_value^2 · sigmaPlus a b c_value` by sprint 026's
exact closed-form RHS `c_value^4 · sigmaZeroMinus a b c_value`.

This confirms the new theorem **strictly generalises (or matches)** sprint
026: any consumer with `paper.eq4` access can recover sprint 026's exact
conclusion at the seed through the new chain. The chain is:

  diskExcess (circleGap a b) c_value
    ≤ c_value^2 · sigmaPlus a b c_value           -- by sprint 040
    ≤ c_value^2 · sigmaMinus a b c_value           -- by paper.eq4 second conjunct
    = c_value^2 · (c_value^2 · sigmaZeroMinus a b c_value)  -- by paper.eq4 third conjunct
    = c_value^4 · sigmaZeroMinus a b c_value.

Any consumer **without** `paper.eq4` access (or with a stronger
oracle/proposal that proves the kernel inequality
`c_value^2 · Σ⁺(c_value) ≤ ∫…` directly) can consume the new bound's
`c_value^2 · Σ⁺(c_value)` shape **without ever invoking `paper.eq4`** —
this is the consumer pattern that sprint 040 unlocks for the first time.
Not `axiom`-ed and does not call the seed axiom.
-/
theorem v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_recovers_via_eq4_at_seed
    (a b : ℕ → ℂ) (K : ℝ → ℝ → ℝ)
    (paper : Section2Assumptions a b K c_value)
    (hSummable :
      ∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      Summable (fun k : ℕ =>
        if PaperAxioms.n1Pred a b k then
          PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
        else 0))
    (hIntCircle :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r)
        MeasureTheory.volume 0 c_value)
    (hIntSigmaPlus :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.sigmaPlus a b r)
        MeasureTheory.volume 0 c_value)
    (hIntZ :
      IntervalIntegrable
        (fun r => 2 * r ^ 3 * PaperAxioms.sigmaZeroMinus a b r)
        MeasureTheory.volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hc_lt_one : c_value < 1 := c_value_lt_one
  -- Step 1: apply sprint 040's new generic bound.
  have hSprint040 :
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
        c_value ^ 2 * PaperAxioms.sigmaPlus a b c_value :=
    diskExcess_upper_bound_via_series_eq3_partition_sigmaPlus_only
      hc_pos hSummable hSummable_n1_c hIntCircle hIntSigmaPlus hIntZ
  -- Step 2: chain `paper.eq4_sigmaPlus_bound`'s second and third
  -- conjuncts to lift the RHS from `c²·Σ⁺(c)` to `c⁴·Z_c`.
  have h4 :=
    paper.eq4_sigmaPlus_bound (r := 0) (le_refl 0) hc_pos hc_lt_one
  have h4_unfold :
      PaperAxioms.sigmaPlus a b 0 ≤ PaperAxioms.sigmaPlus a b c_value ∧
        PaperAxioms.sigmaPlus a b c_value ≤
            PaperAxioms.sigmaMinus a b c_value ∧
          PaperAxioms.sigmaMinus a b c_value =
            c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value := by
    simpa [PaperAxioms.Eq4SigmaPlusBound] using h4
  have hSigmaCmp :
      PaperAxioms.sigmaPlus a b c_value ≤
        PaperAxioms.sigmaMinus a b c_value :=
    h4_unfold.2.1
  have hSigmaIdent :
      PaperAxioms.sigmaMinus a b c_value =
        c_value ^ 2 * PaperAxioms.sigmaZeroMinus a b c_value :=
    h4_unfold.2.2
  -- Step 3: assemble the algebraic chain.
  have hc2_nonneg : (0 : ℝ) ≤ c_value ^ 2 := by positivity
  have hSigmaPlus_le :
      c_value ^ 2 * PaperAxioms.sigmaPlus a b c_value ≤
        c_value ^ 2 * PaperAxioms.sigmaMinus a b c_value :=
    mul_le_mul_of_nonneg_left hSigmaCmp hc2_nonneg
  have hRhsEq :
      c_value ^ 2 * PaperAxioms.sigmaMinus a b c_value =
        c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value := by
    rw [hSigmaIdent]; ring
  calc
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value
        ≤ c_value ^ 2 * PaperAxioms.sigmaPlus a b c_value := hSprint040
    _ ≤ c_value ^ 2 * PaperAxioms.sigmaMinus a b c_value := hSigmaPlus_le
    _ = c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value := hRhsEq

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new paper-axiom-free
integrated disk bound of shape `c²·sigmaPlus a b c` is materialised above
in
`v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_compiles` and
`v40_disk_bound_via_series_eq3_partition_sigmaPlus_only_recovers_via_eq4_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V40
