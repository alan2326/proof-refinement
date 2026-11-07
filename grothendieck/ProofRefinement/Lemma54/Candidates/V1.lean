/-
  Candidates/V1.lean — tight Rouché-certified rectangle, M_val tightened to 432.

  -- @parent Candidates/V0.lean
  -- @sprint Sprint_Contracts/sprint_002.md

  V1 switches from the production rectangle `Ω(57/1000, 293/250)` to the
  tighter Rouché-certified rectangle `Ω(163/1000, 1115/1000)`, and
  retargets the M-oracle from `compute_M_bound_production` to
  `compute_M_bound_tight`. The certified floor on this smaller
  rectangle is `compute_M_bound_tight ≈ 431.81`; we set `M_val := 432`
  (its integer ceiling), the smallest integer admitted by the gate.

  This is a coordinated structural move (rectangle change + M_val
  retarget), not a same-rectangle M-only tightening. `Cr_val` re-evaluates
  automatically because it consumes `M_val` and `R_val_paper` only — the
  latter depends on `SearchConfig.r` and is unchanged.

  Score: `Cr_val ≈ 9.55·10¹²` — an ≈ 86× reduction vs V0's ≈ 8.19·10¹⁴.

  Rouché justification (Scratch/planner_rouche_tight.py at prec=200):
  the tight rectangle Ω(δ=163/1000, B=1115/1000) passes all four Step-1
  / Rouché checks at `r_outer = (1+r)/2 = 24/25`: containment of
  `sin(r_outer·D)`, positive Rouché margin `m ≈ 2.63·10⁻⁴`, and a
  feasible `p_candidate ≈ 9.5·10⁻⁶` with `p·M_d < m` certified — so
  `h_oracle_domain_contains_image` remains a structurally sound seed
  axiom on this smaller rectangle.

  Trust base (unchanged from V0):
    - 3 Lean primitives.
    - 12 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_M_oracle` (single-M sup bound on `Ω(δ, B)`).
    - `Braverman.PaperV0.h_oracle_domain_contains_image`
      (`F_inv_paper` image lands in `Ω(δ, B)`).

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (tight rectangle) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`.
Set to `432`, the integer ceiling of the certified
`compute_M_bound_tight ≈ 431.81` — the smallest integer admitted by
the per-candidate Evaluator's oracle gate on this rectangle. -/
def M_val : ℝ := 432

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Set to `163/1000`, the tightened value that still passes
all four Step-1/Rouché checks at `r_outer = (1+r)/2 = 24/25`
(planner_rouche_tight.py at prec=200). -/
def delta_val : ℝ := 163 / 1000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Set to `1115/1000`, the tightened value that still passes
all four Step-1/Rouché checks at `r_outer = (1+r)/2 = 24/25`
(planner_rouche_tight.py at prec=200). -/
def B_val : ℝ := 1115 / 1000

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

/-! ## Section 2: Score (paper's `Cr_paper` formula at the chosen tuple) -/

/-- `Cr_val := Cr_paper r M_val (R_val_paper r)`. The paper's literal
closed-form constant. With `M_val = 432` (down from V0's 4000), this
evaluates to ≈ 9.55·10¹² — an ≈ 86× reduction vs V0. -/
def Cr_val : ℝ :=
  Braverman.Paper.Cr_paper Braverman.SearchConfig.r M_val
    (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)

theorem Cr_val_nn : 0 ≤ Cr_val :=
  Braverman.Paper.Cr_paper_nonneg
    Braverman.SearchConfig.r_lt_one
    M_val_nn
    (Braverman.Paper.R_val_paper_nonneg Braverman.SearchConfig.r_pos)

/-! ## Section 3: Oracle rectangle (the M-bound domain) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(163/1000, 1115/1000)`. Verified by
`planner_rouche_tight.py` to contain the `F_inv_paper` image on
`disk r` for `q ≤ p_candidate ≈ 9.5·10⁻⁶`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed) -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`.
Witnessed on the tight rectangle by `planner_rouche_tight.py`
(Rouché on `r_outer = (1+r)/2 = 24/25` at the tight Ω). -/
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
|H_η'| ≤ M_val` on the tight rectangle `Ω(163/1000, 1115/1000)`.
Witnessed numerically by `compute_M_bound_tight`; the per-candidate
Evaluator's oracle re-derives this on every run. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0; proved by
direct delegation to `Braverman.Paper.lemma_5_4_paper_on_domain` at
the same constants but the new tight `oracle_domain` and tightened
`M_val`. -/
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
