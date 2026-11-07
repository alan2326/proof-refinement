-- @parent V12
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V13

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V12 — sprint 013 ships
the workspace's *first single-`Z_c` disk-side upper bound*
(`diskExcess_upper_bound_via_eq3_eq4`, `diskExcess ≤ c⁴ · sigmaZeroMinus c`).
The bound uses only `eq3` and `eq4` (avoiding `eq2`) and drops the `r²·Z_r`
term via sprint 005 non-negativity. Unlike sprint 003's two-`Z` bound and
sprint 007's single-`Z_ρ` collapse on the branch-split sub-regime, this
bound carries only `Z_c`, has no `ρ`-dependence, and is valid on the full
disk regime `c ∈ (0, 1)`. The sink theorem is still discharged via
`valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V12, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 013 side lemma: exercise the new single-`Z_c` disk-side upper bound
`diskExcess_upper_bound_via_eq3_eq4` at the seed `c_value`. Materialises the
*workspace's first single-`Z_c` disk-side upper bound* in V13's call graph.
The side lemma is not `axiom`-ed and does not call the seed axiom; it exists
purely to verify that the new lemma typechecks at the seed `c_value`.
-/
theorem v13_diskExcess_upper_bound_via_eq3_eq4_compiles
    {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
    (paper : Section2Assumptions a b K c_value)
    (hInt :
      IntervalIntegrable
        (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
      c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
  diskExcess_upper_bound_via_eq3_eq4 paper c_value_pos c_value_lt_one hInt

/--
Sprint 013 side lemma: exhibit the new closed-form structural identity at the
seed in a name the next sprint can pattern-match on. Materialises the bound
under a `∀`-quantified `Section2Assumptions` instance, against an abstract
universal integrability hypothesis. Both side lemmas are not `axiom`-ed and
do not call the seed axiom.
-/
theorem v13_diskExcess_upper_bound_via_eq3_eq4_chain_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (_paper : Section2Assumptions a b K c_value),
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value) :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (paper : Section2Assumptions a b K c_value),
      PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
        c_value ^ 4 * PaperAxioms.sigmaZeroMinus a b c_value :=
  fun {a b K} paper =>
    diskExcess_upper_bound_via_eq3_eq4 paper c_value_pos c_value_lt_one
      (h_witness paper)

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new single-`Z_c` disk-side
upper bound is materialised above in
`v13_diskExcess_upper_bound_via_eq3_eq4_compiles` and
`v13_diskExcess_upper_bound_via_eq3_eq4_chain_compiles`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V13
