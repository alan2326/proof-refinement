/-
  Candidates/V12.lean — split `M_pp` into its exact closed-form `H_0''` part
  plus an η-small Cauchy remainder, and tighten `inv_F_p_z` to its certified
  ceiling; `Cr_val` drops from V11's `1` to `1/14`.

  -- @parent Candidates/V11.lean

  Structure is identical to V11: same sink delegation to
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, same oracle rectangle
  `Ω(1635/10000, 1115/1000)`, same trusted-analytic surface. Only two
  numerical inputs change, each backed by a re-verified oracle.

  1. `M_pp_tight_val := 10` (NEW oracle `h_M_pp_tight_oracle`, witnessed by
     `Numerical_Library.compute_M_pp_tight_bound`), replacing V11's
     `M_pp_val = 5608/100 = 56.08`.

     Why the old bound was loose: `compute_M_pp_bound` uses
        sup‖∂²_z F_p‖ ≤ sup‖H_0''‖ + sup‖H_η''‖
     and bounds the *second* summand by Cauchy on an enlarged rectangle,
     `sup‖H_η'‖_out / (δ/4) ≈ 2.08/0.0409 ≈ 51`. But
        ∂²_z F_p(η,p,w) = (1-p)·H_0''(w) + p·H_η''(w)
                        = H_0''(w) + p·(H_η'' - H_0'')(w),
     so the triangle step should be applied to the *difference*, which is
     O(η). With `p ≤ pr_paper ≤ 1` (seed axiom `pr_paper_le_one`):
        ‖∂²_z F_p‖ ≤ sup_Ω‖H_0''‖ + sup_{Ω_out}‖H_η' - H_0'‖ / (δ/4).
     The first summand is closed form, `H_0''(w) = w·(1-w²)^(-3/2)`, with
     sup ≈ 5.084 over Ω (attained at `w = ±(1-δ)` real, where `|1-w²| =
     0.30027` is smallest); the second is ≈ 0.08/0.040875 ≈ 1.97, because
     `sup_Ω‖H_η'-H_0'‖ ≈ 0.0541` (exactly the certified `M_phi_prime`) and
     the enlargement `|Re| ≤ 0.8365 → 0.877375` inflates it only mildly.
     Certified total ≈ 7.1, well under the declared `10`.

  2. `inv_F_p_z_val := 7/4` (was `2`), same oracle `h_inv_F_p_z_oracle` /
     `compute_inv_F_p_z_bound`, whose certified value is
        1/(inf‖H_0'‖ - p_max·sup‖H_η'-H_0'‖) ≈ 1/(0.64267 - 0.0541) ≈ 1.699,
     rationalised ≈ 1.7009 ≤ 7/4 (≈ 2.9 % margin).

  Resulting literal bound at r = 23/25, M_phi = 239/5000,
  M_phi_prime = 543/10000, inv_F_p_z = 7/4, M_pp_tight = 10:

     Cr_phi_uzz = M_phi·M_phi_prime·inv² + (1/2)·M_pp·inv³·M_phi²
                = (239/5000)(543/10000)(49/16)
                    + (1/2)(10)(343/64)(57121/25000000)
                = 6359073/800000000 + 97962515/1600000000
                = 110680661/1600000000 = 0.0691754...
  and 110680661 · 14 = 1549529254 ≤ 1600000000, so `Cr_phi_uzz ≤ 1/14`.

  Trust base (V11's, with one oracle row added):
    - 3 Lean primitives;
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family);
    - `h_oracle_domain_contains_image` (structural / Rouché, seed);
    - `h_M_phi_oracle`, `h_M_phi_prime_oracle` (proposal_001);
    - `h_inv_F_p_z_oracle` (sprint_014);
    - `h_M_pp_tight_oracle` (NEW; same shape as `h_M_pp_oracle`, tighter
      bound, re-verified by `compute_M_pp_tight_bound`).
  `h_M_oracle` and `h_M_pp_oracle` are retained as declarations for parity
  with V11's numerical-witness surface; neither is on the sink's proof path.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the tight
oracle rectangle. Carried over from V11 byte-identical for parity; not on the
sink's proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter of the Rouché-certified oracle rectangle. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter of the Rouché-certified oracle rectangle. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle
(certified ≈ 0.0476). -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle rectangle
(certified ≈ 0.0541). -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- Uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over `p ∈ [0, 1]`,
`w ∈ oracle_domain`. Tightened from V11's integer ceiling `2` to `7/4`; the
certified `compute_inv_F_p_z_bound` returns ≈ 1.7009. -/
def inv_F_p_z_val : ℝ := 7 / 4

/-- V11's `M_pp` witness (loose; kept for parity, unused on the proof path). -/
def M_pp_val : ℝ := 5608 / 100

/-- Uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over `p ∈ [0, 1]`,
`w ∈ oracle_domain`, via the exact-`H_0''` + Cauchy-on-`(H_η' - H_0')`
decomposition. Certified `compute_M_pp_tight_bound` ≈ 7.1. -/
def M_pp_tight_val : ℝ := 10

theorem M_val_pos : 0 < M_val := by unfold M_val; norm_num
theorem M_val_nn : 0 ≤ M_val := le_of_lt M_val_pos
theorem delta_val_pos : 0 < delta_val := by unfold delta_val; norm_num
theorem B_val_pos : 0 < B_val := by unfold B_val; norm_num

theorem M_phi_val_pos : 0 < M_phi_val := by unfold M_phi_val; norm_num
theorem M_phi_val_nn : 0 ≤ M_phi_val := le_of_lt M_phi_val_pos
theorem M_phi_prime_val_pos : 0 < M_phi_prime_val := by
  unfold M_phi_prime_val; norm_num
theorem M_phi_prime_val_nn : 0 ≤ M_phi_prime_val :=
  le_of_lt M_phi_prime_val_pos

theorem inv_F_p_z_val_pos : 0 < inv_F_p_z_val := by
  unfold inv_F_p_z_val; norm_num
theorem inv_F_p_z_val_nn : 0 ≤ inv_F_p_z_val := le_of_lt inv_F_p_z_val_pos

theorem M_pp_val_pos : 0 < M_pp_val := by unfold M_pp_val; norm_num
theorem M_pp_val_nn : 0 ≤ M_pp_val := le_of_lt M_pp_val_pos

theorem M_pp_tight_val_pos : 0 < M_pp_tight_val := by
  unfold M_pp_tight_val; norm_num
theorem M_pp_tight_val_nn : 0 ≤ M_pp_tight_val := le_of_lt M_pp_tight_val_pos

/-! ## Section 2: Score -/

/-- `Cr_val := 1/14`, dominating the literal rational
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
 = 110680661/1600000000 ≈ 0.06918`; margin ≈ 3.2 %. -/
def Cr_val : ℝ := 1 / 14

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle -/

/-- The tight Step-1/Rouché-certified rectangle `Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

/-- Certified containment: `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. -/
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

/-- Certified single-`M` sup-norm bound on the rectangle. Retained from V11
for parity; not consumed by the `_phi_uzz` wrapper. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_bound`. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_prime_bound`. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- Uniform-in-`p` bound on `1/‖∂_z F_p(η, p, w)‖`, in the multiplicative
form `1 ≤ ‖∂_z F_p‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound` (certified ≈ 1.7009 ≤ 7/4).
The Python oracle certifies for `p ∈ [0, 1]`, which subsumes
`p ∈ Ioo 0 pr_paper` via the seed axiom `pr_paper_le_one`. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- V11's loose `M_pp` oracle. Retained for parity; not consumed by the
sink's proof path in this candidate. -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-- **NEW.** Tight uniform-in-`p` sup-norm bound on `∂²_z F_p(η, p, w)` over
the oracle rectangle. Same statement shape as `h_M_pp_oracle`, with the
tighter witness `M_pp_tight_val = 10`.

Runner-witnessed by `Numerical_Library.compute_M_pp_tight_bound`, which
certifies
    sup_Ω ‖H_0''‖ + sup_{Ω_out} ‖H_η' - H_0'‖ / (δ/4)  ≈ 5.09 + 1.97 ≈ 7.1,
a valid upper bound on `sup_{p ∈ [0,1], w ∈ Ω} ‖(1-p)·H_0'' + p·H_η''‖` since
`(1-p)·H_0'' + p·H_η'' = H_0'' + p·(H_η'' - H_0'')` and Cauchy's estimate on
the disk of radius `δ/4` around any `w ∈ Ω` (contained in `Ω_out`) bounds
`‖H_η'' - H_0''‖` by `sup_{Ω_out}‖H_η' - H_0'‖ / (δ/4)`. The `p ∈ [0,1]`
range subsumes `Ioo 0 pr_paper` via the seed axiom `pr_paper_le_one`. -/
axiom h_M_pp_tight_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_tight_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V11; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, threading
the tight `h_M_pp_tight_oracle` in place of V11's `h_M_pp_oracle` and the
tightened `inv_F_p_z_val = 7/4`. The conclusion's
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (1/14) * p^2` by exact rational
arithmetic on the literal constants. -/
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
            ≤ Cr_val * p ^ 2 := by
  obtain ⟨pr, hpr_pos, h_main⟩ :=
    Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz
      Braverman.SearchConfig.eta Braverman.SearchConfig.r
      Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one
      M_phi_val M_phi_prime_val M_phi_val_nn M_phi_prime_val_nn
      inv_F_p_z_val inv_F_p_z_val_nn
      M_pp_tight_val M_pp_tight_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle h_inv_F_p_z_oracle
      h_M_pp_tight_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_tight_val
    -- LHS = (239/5000)(543/10000)(49/16) + (1/2)(10)(343/64)(239/5000)²
    --     = 6359073/800000000 + 97962515/1600000000
    --     = 110680661/1600000000 ≈ 0.0691754
    -- RHS = 1/14 ≈ 0.0714286, and 110680661·14 = 1549529254 ≤ 1600000000.
    show 239 / 5000 * (543 / 10000) * (7 / 4 : ℝ) ^ 2 +
        1 / 2 * (10 : ℝ) * (7 / 4 : ℝ) ^ 3 * (239 / 5000) ^ 2 ≤ 1 / 14
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
