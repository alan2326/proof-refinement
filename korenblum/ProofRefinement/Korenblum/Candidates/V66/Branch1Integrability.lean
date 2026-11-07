-- Sprint 088 / V66 — Branch.one scalar integrand integrability.
--
-- Per-candidate derived-theorem file (`AGENT_BRIEF.md` lines 154-204) shipping
-- the Branch.one integrand integrability hypotheses required by V66's
-- `h_witness` construction at `c = v66CValue = 356562/1000000` for the
-- `valid_of_mixedKernel_multiWindow_tau_partition_eq5_eq8_eq9` reducer
-- (sprint 086) at the three Branch.one fallback windows
-- (`i ∈ {0, 1, 2}` of the V38 seven-window split).
--
-- The Branch.one integrand
-- `Korenblum.scalarIntegrand1 c Λ ρ = 12 ρ³(ρ²-c²) / (c⁶ Λ(ρ))`
-- (defined in `KorenblumPaper.PaperEq15`) is already proved
-- `IntervalIntegrable` over any `[a, b] ⊆ [c, 1]` by
-- `KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
-- (constant bound `24/c⁶` from `12·ρ³ ≤ 12`, `|ρ²-c²| ≤ 1`, and
-- `1/(c⁶·Λ) ≤ 2/c⁶` via `paperLambda_ge_half`).
--
-- This file packages the three per-window invocations as a single
-- consumable theorem `v66_branch1_three_window_intervalIntegrable`,
-- analogous to V63/Integrability's
-- `mode_two_and_one_scalarIntegrand_intervalIntegrable`. The proof is a
-- thin wrapper around `paperScalarIntegrand1_intervalIntegrable` that
-- bookkeeping-checks the per-window endpoint inequalities against the
-- V66 SevenWindowEndpoints geometric-ordering theorems.
--
-- No `axiom`s, no `sorry`s, no `Section2Assumptions` field extensions.

import KorenblumPaper.PaperAxioms
import KorenblumPaper.PaperEq15
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability

open KorenblumPaper
open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.Candidates.V66.SevenWindowEndpoints

/-- Sprint 088 / V66 — generic Branch.one scalar integrand integrability
on `[a, b] ⊆ [c, 1]`.

Thin wrapper around
`KorenblumPaper.WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`
(which proves the same statement directly with constant bound `24/c⁶`).
This wrapper exists so that the V66 candidate body can invoke the
Branch.one integrability through a per-candidate derived-theorem name,
mirroring V63's `modeScalarIntegrand_intervalIntegrable` pattern. -/
theorem branch1ScalarIntegrand_intervalIntegrable
    {K : ℝ → ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c)
    (hab : a ≤ b)
    (hca : c ≤ a)
    (hb1 : b ≤ 1)
    (hPaperK : WangKernelExact.PaperKFormula K c) :
    IntervalIntegrable
      (fun ρ => Korenblum.scalarIntegrand1 c (WangOuter.paperLambda K c) ρ)
      volume a b :=
  WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable
    hc hab hca hb1 hPaperK

/-- Sprint 088 / V66 — consolidation theorem packaging
`branch1ScalarIntegrand_intervalIntegrable` for the three Branch.one
windows of the V66 seven-window split (`i = 0, 1, 2`). The three
windows are, with `c = v66CValue`:

  * `i = 0`: `[c · (1 + 1e-6),     c · sqrt(50/49)]`
  * `i = 1`: `[c · sqrt(50/49),    c · sqrt(36/35)]`
  * `i = 2`: `[c · sqrt(36/35),    c · sqrt(25/24)]`

All three lie within `[v66CValue, branchSplit v66CValue] ⊆ [v66CValue, 1]`
by `v66_stop_le_branchSplit` and `v66_branchSplit_lt_one` from
`SevenWindowEndpoints`. -/
theorem v66_branch1_three_window_intervalIntegrable
    {K : ℝ → ℝ → ℝ}
    (hPaperK : WangKernelExact.PaperKFormula K v66CValue) :
    IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 v66CValue
          (WangOuter.paperLambda K v66CValue) ρ)
        volume (v66SevenWindowStart 0) (v66SevenWindowStop 0) ∧
    IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 v66CValue
          (WangOuter.paperLambda K v66CValue) ρ)
        volume (v66SevenWindowStart 1) (v66SevenWindowStop 1) ∧
    IntervalIntegrable
        (fun ρ => Korenblum.scalarIntegrand1 v66CValue
          (WangOuter.paperLambda K v66CValue) ρ)
        volume (v66SevenWindowStart 2) (v66SevenWindowStop 2) := by
  have hc_pos := v66CValue_pos
  refine ⟨?_, ?_, ?_⟩
  · exact branch1ScalarIntegrand_intervalIntegrable
      hc_pos
      (v66_start_le_stop 0)
      (v66_c_le_start 0)
      (v66_stop_le_one 0)
      hPaperK
  · exact branch1ScalarIntegrand_intervalIntegrable
      hc_pos
      (v66_start_le_stop 1)
      (v66_c_le_start 1)
      (v66_stop_le_one 1)
      hPaperK
  · exact branch1ScalarIntegrand_intervalIntegrable
      hc_pos
      (v66_start_le_stop 2)
      (v66_c_le_start 2)
      (v66_stop_le_one 2)
      hPaperK

end ProofRefinement.Korenblum.Candidates.V66.Branch1Integrability
