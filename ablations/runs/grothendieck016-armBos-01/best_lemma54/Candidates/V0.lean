/-
  Candidates/V0.lean — production-faithful seed for Lemma 5.4.

  Mirrors `ProofGraph/Effective/Lemma54Effective.lean` (the production
  effective companion). Same constants, same oracle rectangle, same
  `Cr_paper` formula. The candidate framework explores DEPARTURES from
  this baseline:

  - Tighten `M_val` (currently 4000; the certified `compute_M_rigorous`
    on `Ω(57/1000, 293/250)` returns ≈ 3531).
  - Use a different `Cr` formulation (`Cr_refined`, `K2`-based, etc.).
  - Replace one of the 12 trusted analytic axioms with a Lean proof,
    dropping it from `axioms_used`.
  - Pick a tighter `(δ, B)` rectangle (must remain Rouché-certified).

  Score: `Cr_val ≈ 8.19·10¹⁴`.

  Trust base (matches production minus the paper-faithful header):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  The two oracle axioms are runner-witnessed in production via
  `--run-all`; the per-candidate Evaluator's `compute_M_bound` rechecks
  the M-bound against the chosen rectangle.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (matching production) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
oracle rectangle `Ω(δ_val, B_val)`. Set to `4000`, dominating the
certified `compute_M_rigorous` ≈ 3531 with a comfortable safety
buffer. Candidates may tighten this. -/
def M_val : ℝ := 4000

/-- Real-width parameter for the oracle rectangle. Production value. -/
def delta_val : ℝ := 57 / 1000

/-- Imaginary-height parameter for the oracle rectangle. Production value. -/
def B_val : ℝ := 293 / 250

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-! ## Section 2: Score (paper's `Cr_paper` formula at the chosen tuple) -/

/-- `Cr_val := Cr_paper r M_val (R_val_paper r)`. The paper's literal
closed-form constant, identical to `Braverman.Effective.Cr_val`. -/
def Cr_val : ℝ :=
  Braverman.Paper.Cr_paper Braverman.SearchConfig.r M_val
    (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)

theorem Cr_val_nn : 0 ≤ Cr_val :=
  Braverman.Paper.Cr_paper_nonneg
    Braverman.SearchConfig.r_lt_one
    M_val_nn
    (Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos)

/-! ## Section 3: Oracle rectangle (the M-bound domain) -/

/-- The Step-1/Step-2 rectangle `Ω(δ_val, B_val)`. Same set production
uses; certified by `certify_invertibility` to contain the
`F_inv_paper` image on `disk r`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed in production) -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`.
Witnessed by Step 1 of the certified-arb pipeline (Rouché on `r_outer
= (1+r)/2`). Same shape as
`Braverman.Effective.h_oracle_domain_contains_image`. -/
axiom h_oracle_domain_contains_image :
    ∀ q ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        Braverman.Paper.F_inv_paper
            Braverman.SearchConfig.eta Braverman.SearchConfig.r
            Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
            q z
          ∈ oracle_domain

/-- Certified single-`M` sup-norm bound: `|H_0|, |H_η|, |H_0'|,
|H_η'| ≤ M_val` on `Ω(δ_val, B_val)`. Witnessed numerically by
`compute_M_rigorous`; the per-candidate Evaluator's `compute_M_bound`
oracle re-derives this on every run. Same shape as
`Braverman.Effective.h_M_oracle`. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem** (matches production
`Braverman.Effective.lemma_5_4_effective`). Same conclusion shape;
proved by direct delegation to
`Braverman.Paper.lemma_5_4_paper_on_domain` at the same constants. -/
theorem lemma_5_4_search :
    ∃ pr : ℝ, 0 < pr ∧ ∀ p, 0 < p → p < pr →
      ∀ z ∈ Braverman.disk Braverman.SearchConfig.r,
        ∃ F_inv : ℂ → ℂ,
          Braverman.F_p Braverman.SearchConfig.eta p (F_inv z) = z ∧
          F_inv z ∈ Braverman.S ∧
          ‖F_inv z - Complex.sin z -
              ↑p * ((z -
                Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                  Complex.cos z)‖
            ≤ Cr_val * p ^ 2 :=
  Braverman.Paper.lemma_5_4_paper_on_domain
    Braverman.SearchConfig.eta Braverman.SearchConfig.r
    Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
    M_val M_val_nn oracle_domain h_oracle_domain_contains_image h_M_oracle

end Braverman.PaperV0
