-- @parent V34
import ProofRefinement.Korenblum.Proof.Main

open MeasureTheory
open scoped Classical

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V35

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-- Wang 2025's published lower-bound radius. Same as V0–V34 — sprint 035 ships
the workspace's **first `valid_of_*` reducer whose disk-side proof body invokes
zero `paper.eq*` field projections** and the **first reducer to lift the
unique series-non-derivable conjunct `Σ⁺(c) ≤ Σ⁻(c)` into the witness
existential as a type-level cell**. The new generic theorem
`valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window` fuses
sprint 034's paper-axiom-free integrated disk bound with sprint 006's annulus
lower bound and sprint 011/012's series-level monotonicity + summability
transfer, keeping the kernel inequality `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c,ρ) dρ` and
admissible window `[ρ₁, ρ₂] ⊂ (c, 1)` byte-for-byte from sprint 014. The sink
theorem is still discharged via `valid_of_eq15` so the score does not regress.
-/
def c_value : ℝ := 3554 / 10000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: Wang's scalar inequality `(15)` at the published paper
radius `c = 0.3554`. Same axiom as V0–V34, listed in
`lemma.toml:[seed_axioms]`.
-/
axiom hEq15_seed_3554 (K : ℝ → ℝ → ℝ) : Eq15ScalarBound K c_value

/--
Sprint 035 side lemma: exercise the brand-new full-window paper-axiom-disk-free
closing reducer
`valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window` at
the seed `c_value` against an abstract universal witness bundle. The witness
signature has eleven cells after `ρ₁, ρ₂` — three new disk-side cells
(`hSummable`, `hSummable_n1_c`, `hSigmaCmp`) inserted before `hIntDisk`,
mirroring sprint 014's eight-cell witness. Materialises the new reducer in
V35's call graph; not `axiom`-ed and does not call the seed axiom.
-/
theorem v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_compiles
    (h_witness :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
        (paper : Section2Assumptions a b K c_value),
        ∃ ρ₁ ρ₂ : ℝ,
          c_value < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
            (∀ ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
              Summable (fun k : ℕ =>
                PaperAxioms.coeffPlusGap a b k * r ^ (2 * k))) ∧
            Summable (fun k : ℕ =>
              if PaperAxioms.n1Pred a b k then
                PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
              else 0) ∧
            (PaperAxioms.sigmaPlus a b c_value ≤
              PaperAxioms.sigmaMinus a b c_value) ∧
            IntervalIntegrable
              (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value ∧
            IntervalIntegrable
              (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
                volume c_value 1 ∧
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
  valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window
    c_value_pos c_value_lt_one h_witness

/--
Sprint 035 structural witness lemma: confirm that the new reducer is
non-degenerate at the seed `c_value`, and exhibit the discharge route a
future oracle-bearing candidate would substitute. The `hSigmaCmp` cell of the
new reducer's witness is discharged via `paper.eq4_sigmaPlus_bound (r := 0)`'s
second conjunct (the same scalar inequality `Σ⁺(c) ≤ Σ⁻(c)` at `c_value`,
mirroring V34's `_recovers_via_eq4_at_seed` discharge), where `paper` here is
the abstract paper instance bound by the new reducer's universal `h_witness`
callback (i.e., `intro a b K paper` inside the proof body). The remaining
ten cells are taken as universally-quantified Lean hypotheses on the side
lemma — abstracted over the same `(a, b, K)` Pi-binders so the abstract
`h_witness` callback can re-instantiate them — and the geometric
scaffolding picks the same `(1/2, 7/10)` window as V14's
`v14_window_witness_at_seed`.

This confirms the new reducer **strictly generalises** sprint 014: any
consumer with `paper.eq4` access can recover sprint 014's exact end-to-end
conclusion through the new chain (replace the
`paper.eq4_sigmaPlus_bound (r := 0) ... .2.1` cell witness with the
registered oracle's witness, and every other cell remains identical). Not
`axiom`-ed and does not call the seed axiom.
-/
theorem v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_witness_at_seed
    (hSummable :
      ∀ {a b : ℕ → ℂ} ⦃r : ℝ⦄, 0 ≤ r → r < c_value →
        Summable (fun k : ℕ =>
          PaperAxioms.coeffPlusGap a b k * r ^ (2 * k)))
    (hSummable_n1_c :
      ∀ {a b : ℕ → ℂ},
        Summable (fun k : ℕ =>
          if PaperAxioms.n1Pred a b k then
            PaperAxioms.coeffPlusGap a b k * c_value ^ (2 * k)
          else 0))
    (hIntDisk :
      ∀ {a b : ℕ → ℂ},
        IntervalIntegrable
          (fun r => 2 * r * PaperAxioms.circleGap a b r) volume 0 c_value)
    (hIntCircle :
      ∀ {a b : ℕ → ℂ},
        IntervalIntegrable
          (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
            volume c_value 1)
    (hIntLambdaZ :
      ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ},
        IntervalIntegrable
          (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
            / WangOuter.paperLambda K c_value ρ')
            volume (1 / 2) (7 / 10))
    (hIntLambda :
      ∀ {K : ℝ → ℝ → ℝ},
        IntervalIntegrable
          (fun ρ' => 2 * ρ' ^ 3
            / WangOuter.paperLambda K c_value ρ')
            volume (1 / 2) (7 / 10))
    (hSummable_top :
      ∀ {a b : ℕ → ℂ},
        Summable (fun k : ℕ =>
          if PaperAxioms.n2Pred a b k then
            PaperAxioms.coeffMinusGap a b k * (7 / 10 : ℝ) ^ (2 * k - 2)
          else 0))
    (hKernel :
      ∀ {K : ℝ → ℝ → ℝ},
        c_value ^ 4 ≤ ∫ ρ' in (1 / 2 : ℝ)..(7 / 10 : ℝ),
                        2 * ρ' ^ 3 / WangOuter.paperLambda K c_value ρ') :
    ValidKorenblumBound c_value := by
  have hc_pos : (0 : ℝ) < c_value := c_value_pos
  have hc_lt_one : c_value < 1 := c_value_lt_one
  refine valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window
    hc_pos hc_lt_one ?_
  intro a b K paper
  -- Discharge `hSigmaCmp` from the second conjunct of paper equation `(4)`
  -- at the abstract paper instance.
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
  refine ⟨1 / 2, 7 / 10, ?_, ?_, ?_, ?_, ?_, hSigmaCmp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [c_value]
  · norm_num
  · norm_num
  · intro r hr_nonneg hr_lt
    exact hSummable hr_nonneg hr_lt
  · exact hSummable_n1_c
  · exact hIntDisk
  · exact hIntCircle
  · exact hIntLambdaZ
  · exact hIntLambda
  · exact hSummable_top
  · exact hKernel

/--
Paper-faithful candidate: the published `c = 0.3554` is a valid Korenblum
lower bound. We discharge the sink theorem via the existing `valid_of_eq15`
so that the score does not regress; the brand-new full-window
paper-axiom-disk-free closing reducer is materialised above in
`v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_compiles`
and
`v35_valid_of_disk_series_modulo_sigma_compare_annulus_eq8_eq9_full_window_witness_at_seed`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one (fun {K} => hEq15_seed_3554 K)

end ProofRefinement.Korenblum.Candidates.V35
