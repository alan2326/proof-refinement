/-
  Candidates/V12.lean — attack the two remaining loose numerical inputs of
  V11's `Cr_phi_uzz` bound, dropping `Cr_val` from `1` to `9/100`
  (an 11.1× reduction; V11's own literal bound was ≈ 0.523, so the genuine
  tightening here is ≈ 5.9×).

  -- @parent Candidates/V11.lean

  V11 proved

      ‖…‖ ≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp · p²,
      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi²

  and instantiated it at `inv_F_p_z = 2`, `M_pp = 5608/100`, giving
  ≈ 0.0104 + 0.5126 ≈ 0.5230, declared as `Cr_val := 1`.

  Two observations drive V12; NO Lean infrastructure changes are needed
  (`lemma_5_4_paper_on_domain_phi_uzz` is already polymorphic in both
  `inv_F_p_z` and `M_pp`).

  (1) `inv_F_p_z_val` was the integer ceiling `2` of a bound the existing
      `Numerical_Library.compute_inv_F_p_z_bound` oracle already certifies
      at ≈ 1.7035. Declaring `9/5 = 1.8` keeps ≈ 5.5 % headroom over the
      certified value and needs no new numerics. Effect: `inv²` 4 → 3.24
      and `inv³` 8 → 5.832.

  (2) `M_pp_val = 5608/100 ≈ 56.08` was by far the dominant loss (term-2
      carried 98 % of V11's bound). That number comes from
      `compute_M_pp_bound`, which splits

          ‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

      and then Cauchy-bounds `sup‖H_η''‖ ≤ sup_outer‖H_η'‖ / d` with
      `d = δ/4 ≈ 0.0409` and `sup‖H_η'‖ ≈ 2.08`, i.e. ≈ 51 — swamping the
      ≈ 5.08 contribution of `sup‖H_0''‖` (closed form `|w|/|1−w²|^{3/2}`,
      maximised at `w = 1−δ` on the real axis).

      V12 instead uses the affine decomposition

          (1−p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0''),

      valid for every `p`, and Cauchy-bounds the *difference*:

          ‖H_η''(w) − H_0''(w)‖ = ‖(H_η' − H_0')'(w)‖
            ≤ sup_{Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d.

      At η = 1/100 the difference `H_η' − H_0'` has sup ≈ 0.054 on Ω (this
      is exactly the quantity `h_M_phi_prime_oracle` certifies), ~38×
      smaller than `H_η'` itself, so the Cauchy contribution drops from
      ≈ 51 to ≈ 1.5 and the total from ≈ 56 to ≈ 6.6. The new oracle
      `Numerical_Library.compute_M_pp_tight_bound` implements exactly this
      route; `M_pp_tight_val := 12` is declared with ~1.8× headroom.

  At V12 parameters:
    r_val            = 23/25
    M_phi_val        = 239/5000        (unchanged from V9–V11)
    M_phi_prime_val  = 543/10000       (unchanged from V9–V11)
    inv_F_p_z_val    = 9/5             (was 2)
    M_pp_tight_val   = 12              (was M_pp_val = 5608/100)
  giving
    Cr_phi_uzz ≤ (239/5000)·(543/10000)·(81/25)
                   + (1/2)·12·(729/125)·(239/5000)²
               = 10511937/1250000000 + 249847254/3125000000
               = 552254193/6250000000
               ≈ 0.0084095 + 0.0799511 = 0.0883607,
  comfortably below `Cr_val := 9/100 = 0.09` (margin ≈ 0.00164, exact
  rational arithmetic so `norm_num` closes it).

  Trust base (same shape as V11; one oracle swapped, none added in kind):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (seed).
    - `Braverman.PaperV0.h_M_oracle` (declared for parity with V9–V11;
      not consumed by the `_phi_uzz` proof path).
    - `Braverman.PaperV0.h_M_phi_oracle`        (unchanged, proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle`  (unchanged, proposal_001).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle`    (unchanged statement, tighter
                                                 declared constant).
    - `Braverman.PaperV0.h_M_pp_tight_oracle`   (NEW: same sup-norm claim as
      V11's `h_M_pp_oracle` — `‖∂²_z F_p(η, p, w)‖ ≤ M_pp` on the SAME
      rectangle for the SAME `p`-range — backed by the tighter
      `compute_M_pp_tight_bound`. It replaces `h_M_pp_oracle`; it does not
      add a claim of a new shape, and the rectangle is byte-identical.)

  The oracle rectangle `Ω(1635/10000, 1115/1000)`, `eta = 1/100` and
  `r = 23/25` are all unchanged from V9–V11.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V9–V11 byte-identical for parity; the `_phi_uzz`
proof path does not consume it. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`239/5000 = 0.0478` is exactly the rational the certified
`compute_M_phi_bound` emits at production-grade precision (arb ball
≈ 0.0476, rationalised at `max_denom = 10000`), so there is no slack
left on this axis. Unchanged from V9–V11. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. `543/10000 = 0.0543` is likewise exactly the rational the
certified `compute_M_phi_prime_bound` emits (arb ball ≈ 0.0541).
Unchanged from V9–V11. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `2` to `9/5 = 1.8`.** The backing oracle
`Numerical_Library.compute_inv_F_p_z_bound` is unchanged (same function,
same defaults, same rectangle); it certifies

    inf‖∂_z F_p‖ ≥ inf‖H_0'‖ − sup‖H_η' − H_0'‖ ≈ 0.643 − 0.054 = 0.589,

hence `sup 1/‖∂_z F_p‖ ≤ 1.7035`. V9–V11 declared the integer ceiling
`2`; `9/5` retains ≈ 5.5 % headroom over the certified value while
shrinking `inv_F_p_z²` from 4 to 81/25 = 3.24 and `inv_F_p_z³` from 8 to
729/125 = 5.832. -/
def inv_F_p_z_val : ℝ := 9 / 5

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `5608/100 ≈ 56.08` to `12`**, backed by the new
`Numerical_Library.compute_M_pp_tight_bound`. Same sup-norm claim, same
rectangle, same `p`-range as V11's `M_pp_val`; only the *route* to the
certificate changed:

* V11's `compute_M_pp_bound` used the triangle split
  `‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖` and then bounded
  `sup‖H_η''‖ ≤ sup_outer‖H_η'‖ / (δ/4) ≈ 2.08 / 0.0409 ≈ 51`, dwarfing
  the ≈ 5.08 contribution of `sup‖H_0''‖`.
* V12's `compute_M_pp_tight_bound` uses the affine identity
  `(1−p) H_0'' + p H_η'' = H_0'' + p (H_η'' − H_0'')` and Cauchy-bounds
  the difference: `‖H_η'' − H_0''‖ ≤ sup_outer‖H_η' − H_0'‖ / (δ/4)`.
  Since `sup‖H_η' − H_0'‖ ≈ 0.054` (the `M_phi_prime` quantity) is ~38×
  smaller than `sup‖H_η'‖`, the Cauchy contribution collapses to ≈ 1.5
  and the total to ≈ 6.6.

`12` leaves ≈ 1.8× headroom over that estimate. -/
def M_pp_tight_val : ℝ := 12

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

theorem M_pp_tight_val_pos : 0 < M_pp_tight_val := by
  unfold M_pp_tight_val; norm_num
theorem M_pp_tight_val_nn : 0 ≤ M_pp_tight_val := le_of_lt M_pp_tight_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 9/100`) -/

/-- `Cr_val := 9/100 = 0.09`, dominating the literal rational

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (239/5000)·(543/10000)·(81/25)
          + (1/2)·12·(729/125)·(239/5000)²
      = 10511937/1250000000 + 249847254/3125000000
      = 552254193/6250000000
      ≈ 0.0084095 + 0.0799511
      ≈ 0.0883607.

Margin to `9/100` is ≈ 0.0016393 — small in absolute terms, but the
closing step is exact rational arithmetic (`norm_num`), so no tolerance
is required. -/
def Cr_val : ℝ := 9 / 100

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V11) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. Byte-identical to
V9/V10/V11 — V12 does not touch the rectangle. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`.
Seed axiom, unchanged. -/
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

/-- Certified single-`M` sup-norm bound on the tight rectangle. Carried
over from V9–V11 for parity; the `_phi_uzz` wrapper does not consume it,
so it should not appear in the transitive axiom set of the sink. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_bound`.
Unchanged from V9–V11. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_prime_bound`.
Unchanged from V9–V11. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound` (certified ≈ 1.7035).

Statement byte-identical to V10/V11; only the declared constant
`inv_F_p_z_val` tightened from `2` to `9/5`. The Python oracle certifies
the bound for `p ∈ [0, 1]` (using `pr_paper ≤ 1` from the seed axiom
`pr_paper_le_one`), so the quantifier over `Ioo 0 pr_paper` is
subsumed. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`‖∂²_z F_p(η, p, w)‖ ≤ M_pp_tight_val`.

This is the SAME sup-norm claim, over the SAME rectangle and the SAME
`p`-range, as V11's `h_M_pp_oracle`; it is restated here only so that it
can be witnessed by the tighter
`Numerical_Library.compute_M_pp_tight_bound`, which routes the Cauchy
step through the difference `H_η' − H_0'` (sup ≈ 0.054) instead of
through `H_η'` (sup ≈ 2.08), via the affine identity

    (1 − p) H_0'' + p H_η'' = H_0'' + p · (H_η'' − H_0'').

Certified estimate ≈ 6.6 versus V11's ≈ 56.08; `M_pp_tight_val := 12`
leaves ≈ 1.8× headroom. -/
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
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (the
η-aware wrapper introduced for V11), threading the tightened
`inv_F_p_z_val = 9/5` and the tightened `M_pp_tight_val = 12` through the
same oracle-hypothesis slots V11 used. No Lean infrastructure changed:
`lemma_5_4_paper_on_domain_phi_uzz` is already polymorphic in both
constants.

The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (9/100) * p^2` by the monotonicity step
`Cr_phi_uzz … ≤ 9/100`, which is pure rational arithmetic on the literal
constants. -/
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
  -- chain `≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_tight_val
    -- LHS = (239/5000)·(543/10000)·(9/5)² + (1/2)·12·(9/5)³·(239/5000)²
    --     = 10511937/1250000000 + 249847254/3125000000
    --     = 552254193/6250000000
    --     ≈ 0.0084095 + 0.0799511 ≈ 0.0883607 ≤ 0.09
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
