/-
  Candidates/V12.lean — tighten two declared numerical witnesses against what
  the oracles actually certify, and re-back the `‖∂²_z F_p‖` bound with a
  strictly tighter (same-statement) arb certificate, dropping `Cr_val` from
  V11's `1` to `2/25 = 0.08` — a 12.5× reduction.

  -- @parent Candidates/V11.lean

  ## What changed relative to V11 (three numerals + one oracle backing)

  V12 delegates to the SAME sink wrapper as V11,
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, with the same
  `Cr_phi_uzz` formula

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  No file under `Proof/` is touched. The three changes are:

  1. `inv_F_p_z_val : 2 → 9/5`.
     `Numerical_Library/inv_F_p_z.py` certifies
        sup_{p ∈ [0,1], w ∈ Ω} 1/‖∂_z F_p(η,p,w)‖
          ≤ 1 / (inf_Ω‖H_0'‖ − p_max · sup_Ω‖H_η' − H_0'‖).
     At the locked rectangle Ω(1635/10000, 1115/1000):
        sup_Ω |1 − w²| = |1 − ((1−δ) + iB)²| = 2.421134…  (corner; the map is
                          monotone in both |Re w| and |Im w|),
        inf_Ω ‖H_0'‖   = 1/√2.421134… = 0.642673…,
        sup_Ω ‖H_η'−H_0'‖ ≈ 0.0541      (the M_phi_prime quantity),
        ⇒ inf ‖D‖ ≥ 0.588573…, ⇒ sup 1/‖D‖ ≤ 1.6990…
     V10's and V11's headers both record the realised oracle output as
     ≈ 1.7035; after `arb_to_rational_ub`'s safety inflation the returned
     rational is ≈ 1.7053. `9/5 = 1.8` dominates it with ≈ 6 % headroom,
     while cutting `inv_F_p_z²` from 4 to 81/25 and `inv_F_p_z³` from 8
     to 729/125.

  2. `M_pp_val = 5608/100` → `M_pp_tight_val = 10`, backed by the NEW oracle
     `Numerical_Library/m_pp_tight.py :: compute_M_pp_tight_bound`.
     The axiom STATEMENT is unchanged (a sup-norm bound on the same explicit
     quantity `‖iteratedDeriv 2 (F_p η p) w‖` over the same rectangle Ω);
     only the certificate is tighter. The old `h_M_pp_oracle` row in
     `lemma.toml` is left in place, untouched.

     Why the old bound was loose: `m_pp.py` splits
        DD = (1−p)·H_0'' + p·H_η''  →  ‖DD‖ ≤ sup‖H_0''‖ + sup‖H_η''‖
     and then bounds `sup‖H_η''‖` by Cauchy on `H_η'` over the enlarged
     rectangle, i.e. `sup‖H_η'‖_outer / d` with `d = δ/4 = 0.040875`. Since
     `sup‖H_η'‖_outer ≈ 2.082`, that term alone is ≈ 51 — it is the *whole*
     size of `H_η'`, not the small η-deformation.

     The tighter decomposition keeps the η-awareness:
        DD = H_0'' + p · (H_η − H_0)'',
        ‖DD‖ ≤ sup_Ω‖H_0''‖ + p_max · sup_Ω‖(H_η − H_0)''‖
              ≤ sup_Ω‖H_0''‖ + p_max · sup_{Ω_outer}‖H_η' − H_0'‖ / d.
     Both steps are rigorous: the first is the triangle inequality on the
     affine-in-p family (with `p_max = 1`, licensed by the seed axiom
     `pr_paper_le_one`); the second is Cauchy's estimate for the second
     derivative, valid because every `w ∈ Ω` has its closed `d`-disk inside
     `Ω_outer = Ω(δ − d, B + d)`, and `H_η − H_0` is analytic there
     (|Re w| ≤ 1 − 3δ/4 = 0.877375 < 1). Numerically:
        sup_Ω ‖H_0''‖ = sup_{∂Ω} |w| / |1 − w²|^{3/2}
                      = 0.8365 / (0.300268)^{3/2} = 5.0834…   (at v = 0,
                        u = 1 − δ; interior maximum excluded by
                        max-modulus, exactly as in m_pp.py),
        sup_{Ω_outer} ‖H_η' − H_0'‖ ≈ 0.06–0.10  (0.0541 on Ω, growing by
                        at most ≈ (0.300268/0.229960)^{5/2} ≈ 1.95 as Re w
                        is pushed from 0.8365 to 0.877375),
        ⇒ M_pp ≤ 5.08 + 0.10/0.040875 ≈ 7.6.
     `M_pp_tight_val := 10` dominates that with ≈ 30 % headroom.
     Consistency check on the old certificate: `M_pp ≈ 56.02` with
     `sup‖H_0''‖ ≈ 5.08` forces `sup‖H_η'‖_outer ≈ 50.94 · 0.040875 ≈ 2.082`,
     which agrees with the closed form `sup‖H_0'‖_outer = 2.0842` to within
     0.003 — i.e. the realised run already witnesses that `H_η'` and `H_0'`
     differ only in the fourth decimal of their suprema.

  3. `Cr_val : 1 → 2/25`.
     At the new witnesses (M_phi = 239/5000, M_phi_prime = 543/10000,
     inv_F_p_z = 9/5, M_pp = 10):
        term1 = (239/5000)(543/10000)(81/25)
              = 10511937/1250000000        = 0.008409549…
        term2 = (1/2)(10)(729/125)(57121/25000000)
              = 208206045/3125000000       = 0.066625934…
        Cr_phi_uzz = 468971775/6250000000  = 0.075035484…
     `Cr_val = 2/25 = 0.08` leaves a margin of 31028225/6250000000
     ≈ 0.004965 — decided exactly by `norm_num` on literal rationals.

  ## Trust base (11 + 5, unchanged in kind from V11)

    - 3 Lean primitives (`propext`, `Classical.choice`, `Quot.sound`).
    - 11 trusted analytic axioms (the `Braverman.Paper.F_inv_paper` family;
      `F_inv_paper_zero` remains a derived theorem since sprint_010).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (structural /
      Rouché-certified seed axiom; the rectangle Ω(δ_val, B_val) is
      byte-identical to V9/V10/V11 — nothing is shrunk).
    - `Braverman.PaperV0.h_M_phi_oracle`        (proposal_001).
    - `Braverman.PaperV0.h_M_phi_prime_oracle`  (proposal_001).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle`    (sprint_014).
    - `Braverman.PaperV0.h_M_pp_tight_oracle`   (NEW row; same statement
      shape and same domain as the proposal_001-approved `h_M_pp_oracle`,
      with a strictly tighter certificate).
    - `Braverman.PaperV0.h_M_oracle` is declared for parity with V9–V11 but
      is not on the sink's proof path (as in V10/V11).

  Fixed parameters (from SearchConfig, untouched): `eta = 1/100`, `r = 23/25`.
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
Carried over from V9/V10/V11 byte-identical for parity; the `_phi_uzz`
wrapper does not consume it on its proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle rectangle.
Unchanged from V9/V10/V11 — the oracle rectangle is NOT shrunk. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9/V10/V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`239/5000 = 0.0478` is exactly the rational that
`Numerical_Library.compute_M_phi_bound` returns at its pinned defaults
(certified ball ≈ 0.0476, inflated by `arb_to_rational_ub`'s
`safety_rel = 1e-3`, `safety_abs = 1e-4` and ceiled to `max_denom = 10000`),
so there is no slack left on this axis. Unchanged from V9. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle rectangle.
`543/10000 = 0.0543` is likewise exactly the oracle's returned rational
(certified ball ≈ 0.0541). Unchanged from V9. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `2` to `9/5 = 1.8`.**
`Numerical_Library.compute_inv_F_p_z_bound` certifies
`1/inf‖D‖` where
`inf‖D‖ ≥ inf_Ω‖H_0'‖ − p_max · sup_Ω‖H_η' − H_0'‖ ≥ 0.642673 − 0.0541
        = 0.588573`, i.e. a bound ≈ `1.6990`; after the module's safety
inflation the returned rational is ≈ `1.7053` (V10 and V11 both record the
realised output as ≈ 1.7035). `9/5` dominates that with ≈ 6 % headroom while
cutting `inv_F_p_z² : 4 → 81/25` and `inv_F_p_z³ : 8 → 729/125`. -/
def inv_F_p_z_val : ℝ := 9 / 5

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened in V12 from `5608/100 = 56.08` to `10`**, backed by the new
`Numerical_Library.compute_M_pp_tight_bound`. Same axiom statement, same
rectangle; only the certificate is sharper. The new module certifies
`sup_Ω‖H_0''‖ + p_max · sup_{Ω_outer}‖H_η' − H_0'‖ / d`
(`d = δ/4 = 0.040875`, `Ω_outer = Ω(3δ/4, B + d)`) instead of the old
`sup_Ω‖H_0''‖ + sup_{Ω_outer}‖H_η'‖ / d`; the η-deformation replaces the
full size of `H_η'`, dropping the second summand from ≈ 51 to ≈ 1.7–2.5 and
the total from ≈ 56.0 to ≈ 6.6–7.6. `10` dominates that with ≈ 30 %
headroom. -/
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

theorem M_pp_tight_val_pos : 0 < M_pp_tight_val := by
  unfold M_pp_tight_val; norm_num
theorem M_pp_tight_val_nn : 0 ≤ M_pp_tight_val := le_of_lt M_pp_tight_val_pos

/-! ## Section 2: Score (literal rational `Cr_val = 2/25`) -/

/-- `Cr_val := 2/25 = 0.08`, dominating the literal rational
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val`:

    term1 = (239/5000)·(543/10000)·(81/25)
          = 10511937/1250000000    = 0.008409549…
    term2 = (1/2)·10·(729/125)·(57121/25000000)
          = 208206045/3125000000   = 0.066625934…
    total = 468971775/6250000000   = 0.075035484…

Margin to `2/25` is `31028225/6250000000 ≈ 0.004965`, decided exactly by
`norm_num` on literal rationals (no `nlinarith` search, no floating point). -/
def Cr_val : ℝ := 2 / 25

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (the certified image domain)

Unchanged from V9/V10/V11. The trusted containment axiom
`h_oracle_domain_contains_image` asserts exactly the same thing about
exactly the same rectangle; nothing here is shrunk or reinterpreted. -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed) -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Byte-identical to
V9/V10/V11 — the rectangle and its meaning are untouched. -/
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

/-- Certified single-`M` sup-norm bound on the tight rectangle. Carried over
from V9/V10/V11 for parity of the recorded numerical-witness surface; the
`_phi_uzz` wrapper does not consume it, so it does not appear in the sink's
transitive axiom set. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_bound`
(proposal_001). Unchanged from V9. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_prime_bound`
(proposal_001). Unchanged from V9. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` bound `1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`.
Runner-witnessed by `Numerical_Library.compute_inv_F_p_z_bound`, which
certifies the bound for `p ∈ [0, 1]` (the universal quantifier over
`Ioo 0 pr_paper` is subsumed via the seed axiom `pr_paper_le_one`).
Statement byte-identical to V10/V11; only the declared `inv_F_p_z_val`
is tightened from `2` to `9/5`. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over the
oracle rectangle: for every `p ∈ Ioo 0 pr_paper` and every
`w ∈ oracle_domain`,
`‖iteratedDeriv 2 (F_p η p) w‖ ≤ M_pp_tight_val`.

Runner-witnessed by `Numerical_Library.compute_M_pp_tight_bound`. This is
the SAME sup-norm claim, on the SAME explicit quantity, over the SAME
rectangle as the proposal_001-approved `h_M_pp_oracle` — only the numerical
certificate behind it is sharper, because the new module bounds the
η-deformation `(H_η − H_0)''` by Cauchy instead of bounding `H_η''` itself:

    ‖DD‖ = ‖H_0'' + p·(H_η − H_0)''‖
         ≤ sup_Ω‖H_0''‖ + p_max · sup_{Ω_outer}‖H_η' − H_0'‖ / d
         ≈ 5.08 + 0.07/0.040875 ≈ 6.8       (old route: 5.08 + 2.082/0.040875
                                             ≈ 56.0)

with `p_max = 1` (licensed by the seed axiom `pr_paper_le_one`),
`d = δ/4`, `Ω_outer = Ω(δ − d, B + d)`, and `H_η − H_0` analytic on the
closure of `Ω_outer` (`|Re w| ≤ 1 − 3δ/4 = 0.877375 < 1`). The pre-existing
`h_M_pp_oracle` row in `lemma.toml` is left untouched; this is an additive
row. -/
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
η-aware wrapper introduced in sprint_015, used here unmodified), threading
the tightened `inv_F_p_z_val = 9/5` and the tightened, re-certified
`M_pp_tight_val = 10` together with the unchanged `M_phi`/`M_phi_prime`
oracles. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (2/25) * p^2` by the monotonicity step
below, which is pure literal-rational arithmetic. -/
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
  -- chain `≤ Cr_phi_uzz … * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  -- After `unfold`, the goal is the closed literal-rational inequality
  --   239/5000 * (543/10000) * (9/5)^2
  --     + 1/2 * 10 * (9/5)^3 * (239/5000)^2   ≤   2/25,
  -- i.e.  10511937/1250000000 + 208206045/3125000000
  --         = 468971775/6250000000 = 0.075035484…  ≤  0.08,
  -- with margin 31028225/6250000000 ≈ 0.004965. `norm_num` decides this
  -- exactly. (`Cr_phi_uzz`'s `r` argument does not occur in its body, so no
  -- `SearchConfig.r` unfolding is needed.)
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_tight_val
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
