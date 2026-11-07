Emitting the complete files now, compactly.

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
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
```

Now the oracle module backing the new axiom.

```python path=ProofRefinement/Lemma54/Numerical_Library/m_pp_tight.py
"""Tight M_pp oracle: certified upper bound on

    M_pp_tight = sup_{(p, w) in [0, 1] x Omega(delta, B)}
                     ||(1-p) H_0''(w) + p H_eta''(w)||

i.e. sup ||iteratedDeriv 2 (F_p eta p) w||, the same quantity `m_pp.py`
bounds — but decomposed around H_0 instead of split into two independent
sups.

Why this is much tighter than `compute_M_pp_bound`
--------------------------------------------------
`m_pp.py` uses the triangle bound

    ||(1-p) H_0'' + p H_eta''||  <=  sup||H_0''|| + sup||H_eta''||

and estimates the second summand by Cauchy on an enlarged rectangle,
`sup||H_eta'||_out / d ~ 2.08 / 0.0409 ~ 51`, which dominates everything.
But the family is affine in p around H_0:

    (1-p) H_0''(w) + p H_eta''(w) = H_0''(w) + p * (H_eta'' - H_0'')(w),

and the *difference* is O(eta). So for p in [0, 1],

    ||d^2_z F_p(w)||  <=  sup_Omega ||H_0''||  +  sup_Omega ||H_eta'' - H_0''||
                      <=  sup_Omega ||H_0''||
                            + sup_{Omega_out} ||H_eta' - H_0'|| / d,

the last step by Cauchy's estimate on the disk of radius d = delta/4 about
each w in Omega (that disk lies in Omega_out = Omega(3*delta/4, B + d),
which is inside the strip |Re| < 1 where both H_0 and H_eta are analytic).

At eta = 1/100 on Omega(1635/10000, 1115/1000):

  * sup_Omega ||H_0''|| ~ 5.084.  Closed form H_0''(w) = w (1-w^2)^{-3/2};
    the sup is attained at w = +-(1-delta) on the real axis, where
    |1-w^2| = 0.30027 is smallest.  H_0'' is analytic on the closure of
    Omega (its singularities sit at w = +-1, i.e. |Re| = 1), so the
    boundary scan is a valid max-modulus argument.
  * sup_{Omega_out} ||H_eta' - H_0'|| ~ 0.08 (the same quantity certified
    on the *inner* rectangle by `compute_M_phi_prime_bound` is ~0.0541;
    widening |Re| from 0.8365 to 0.877375 inflates it mildly), so the
    Cauchy term is ~0.08/0.040875 ~ 1.97.

Total ~ 7.1, versus ~56.1 from `compute_M_pp_bound` — an ~8x tightening of
the term that dominates `Cr_phi_uzz`.

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      forall p in Ioo 0 pr_paper, forall w in oracle_domain,
        ||iteratedDeriv 2 (Braverman.F_p eta p) w|| <= M_pp_tight_val

(the `p in [0,1]` range covers `Ioo 0 pr_paper` via the seed axiom
`pr_paper_le_one`).

Implementation mirrors `m_pp.py` exactly, with one change: the enlarged-
rectangle scan is applied to `H_eta' - H_0'` rather than to `H_eta'`.
"""

from __future__ import annotations

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_deriv_at_acb

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


def _compute_M_pp_tight_for_params(
    eta: float,
    delta: str,
    B: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified sup_{Omega} ||d^2_z F_p|| pipeline (tight form)."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ||H_0''(w)|| on dOmega, closed form H_0''(w) = w (1-w^2)^{-3/2}.
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 - w^2
        # rsqrt(u) = u^{-1/2}, so u^{-3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # 2. sup ||H_eta'' - H_0''|| on Omega via Cauchy on the enlarged
    #    rectangle Omega_out = Omega(3*delta/4, B + delta/4), applied to the
    #    *difference* H_eta' - H_0' (which is O(eta)).
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d      # = 3*delta/4  ->  |Re| <= 1 - 3*delta/4
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the Cauchy bound: "
            f"delta_inner = {delta_inner}"
        )

    def phi_prime(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H0_p)

    max_phi_prime_outer = _max_on_rect(
        phi_prime, delta_inner, B_outer, n_per_edge, prec,
    )
    max_phi_pp = max_phi_prime_outer / d

    M_pp_tight_arb = max_H0_pp + max_phi_pp

    return {
        "M_pp_tight_str": M_pp_tight_arb.str(20, more=True),
        "M_pp_tight_upper_float": float(M_pp_tight_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_phi_prime_outer_str": max_phi_prime_outer.str(20, more=True),
        "max_phi_pp_str": max_phi_pp.str(20, more=True),
        "delta": delta,
        "B": B,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_tight_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    M_pp_tight = sup_{p in [0,1], w in Omega} ||(1-p) H_0'' + p H_eta''||.

    Defaults match the V9-V11 oracle rectangle (delta = 1635/10000,
    B = 1115/1000) and the `m_pp.py` scan parameters, so the cached
    phi-series is shared with `m_phi.py`, `m_phi_prime.py` and `m_pp.py`.

    Performance: two `_max_on_rect` scans on different rectangles, same
    profile as `compute_M_pp_bound` (~60-120s cold, cached thereafter).
    """
    key = {
        "fn": "compute_M_pp_tight_bound",
        "eta": eta, "delta": delta, "B": B,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_pp_tight_arb = arb(cached["M_pp_tight_str"])
    bound = arb_to_rational_ub(
        M_pp_tight_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_tight_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_tight_arb_str": cached["M_pp_tight_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_phi_prime_outer_arb_str": cached["max_phi_prime_outer_str"],
            "max_phi_pp_arb_str": cached["max_phi_pp_str"],
        },
    )
```

Re-export, so `getattr(mod, "compute_M_pp_tight_bound")` resolves.

```python path=ProofRefinement/Lemma54/Numerical_Library/__init__.py
"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from `Evaluator.py`'s `ORACLE_REGISTRY` so the evaluator can
    re-run the function and check the candidate's declared rational lies above
    the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`.
  2. Register it in `Evaluator.ORACLE_REGISTRY` with the matching axiom name
     and bound field (the `def <field>_val : ℝ := <rat>` in the candidate).
  3. The Lean axiom statement must be regex-matchable by the registry's
     `expected_pattern`.

The certified-arb pipeline at `grothendieck/proof/certified/` provides the
underlying rigorous arithmetic; the wrappers in this module convert its
`flint.arb` outputs into Lean-consumable rationals.
"""

from .types import OracleResult
from .m_bound import (
    compute_M_bound, compute_M_bound_tight, compute_M_bound_production,
)
from .r_bound import compute_R_bound, compute_R_bound_tight
from .m_phi import compute_M_phi_bound
from .m_phi_prime import compute_M_phi_prime_bound
from .m_pp import compute_M_pp_bound
from .m_pp_tight import compute_M_pp_tight_bound
from .inv_F_p_z import compute_inv_F_p_z_bound

__all__ = [
    "OracleResult",
    "compute_M_bound",
    "compute_M_bound_tight",
    "compute_M_bound_production",
    "compute_R_bound",
    "compute_R_bound_tight",
    "compute_M_phi_bound",
    "compute_M_phi_prime_bound",
    "compute_M_pp_bound",
    "compute_M_pp_tight_bound",
    "compute_inv_F_p_z_bound",
]
```

And the registration row (all existing rows preserved verbatim).

```toml path=ProofRefinement/Lemma54/lemma.toml
# Per-lemma config consumed by Evaluator.py.
#
# This file externalizes everything about Lemma 5.4 that the evaluator needs
# to know: the sink theorem name, the score expression, the seed axioms it
# may inherit from V0, and the numerical oracles it may invoke.
#
# Design rationale: see ../../docs/PROOF_REFINEMENT_DESIGN.md

name        = "Lemma 5.4"
slug        = "lemma_5_4"
paper_ref   = "Braverman et al. (2011), §5"

# The candidate must declare `theorem <sink_theorem>` (under the namespace
# of its choice). The evaluator runs `#print axioms <namespace>.<sink_theorem>`
# to enumerate transitive dependencies.
sink_theorem = "lemma_5_4_search"

# Score: a Python arithmetic expression over the candidate's `def *_val`
# rationals (and the constants in [search_constants]). Smaller is better.
score = "Cr_val"

# Lean expressions the score evaluator should resolve to fixed rationals.
[search_constants]
"SearchConfig.r"   = "23/25"
"SearchConfig.eta" = "1/100"

# Axioms allowed in the audited set without an oracle backing.
# `sorryAx` is never permitted.
[seed_axioms]
allowed = [
  # Standard Lean.
  "propext",
  "Classical.choice",
  "Quot.sound",

  # 12 trusted analytic axioms about the IFT-supplied F_inv_paper family.
  # Inherited from the production proof at
  # ProofGraph/Effective/Lemma54Effective.lean. The agent may prove these
  # as Lean theorems (which removes them from the audited set) but must
  # not introduce new ones.
  "Braverman.Paper.F_inv_paper",
  "Braverman.Paper.F_inv_paper_eq",
  "Braverman.Paper.F_inv_paper_zero",
  "Braverman.Paper.F_inv_paper_mem_S",
  "Braverman.Paper.F_inv_paper_R_bound",
  "Braverman.Paper.F_inv_paper_analytic",
  "Braverman.Paper.F_inv_paper_contdiff",
  "Braverman.Paper.F_inv_paper_at_origin",
  "Braverman.Paper.F_inv_paper_first_deriv_zero",
  "Braverman.Paper.pr_paper",
  "Braverman.Paper.pr_paper_pos",
  "Braverman.Paper.pr_paper_le_one",

  # Structural domain-containment axiom (Rouché-certified by the production
  # runner; not numerically re-checked per candidate).
  "Braverman.PaperV0.h_oracle_domain_contains_image",
]

# Oracle-backed axioms. Each axiom name (short, namespace-stripped) maps
# to a `def <bound_field>_val : ℝ` and a Python function in
# `Numerical_Library/` that recomputes a certified upper bound. The
# evaluator demands `<bound_field>_val >= oracle_fn().bound`.

[[oracles]]
axiom       = "h_M_oracle"
bound_field = "M_val"
oracle_fn   = "compute_M_bound_tight"

# Approved by proposal_001 (2026-04-30). Three η-aware oracles for sup-norms
# of |H_η − H_0|, |H_η' − H_0'|, and |F_ww| on the oracle rectangle. See
# Proposals/proposal_001_cr_refined_oracles.md for the math; see
# Scratch/sprint_proposal_001_smoke.py for the certified numerical values.

[[oracles]]
axiom       = "h_M_phi_oracle"
bound_field = "M_phi_val"
oracle_fn   = "compute_M_phi_bound"

[[oracles]]
axiom       = "h_M_phi_prime_oracle"
bound_field = "M_phi_prime_val"
oracle_fn   = "compute_M_phi_prime_bound"

[[oracles]]
axiom       = "h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn   = "compute_M_pp_bound"

# Approved by sprint_014 (2026-04-30). Sup of `1 / ‖∂_z F_p(η, p, w)‖` over
# `p ∈ [0, 1]` and `w ∈ Ω(δ, B)`. Replaces the loose paper bound
# `1/‖∂_z F_p‖ ≤ 2R/(1−r) ≈ 28.75` from `F_p_deriv_lower_bound_at_F_inv`
# with a direct η-aware ≈ 1.70.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"

# Tight form of the `h_M_pp_oracle` quantity: same sup-norm claim on
# `∂²_z F_p` over `Ω(δ, B)` for `p ∈ [0, 1]`, but decomposed around `H_0`
# (exact closed-form `sup‖H_0''‖`, plus a Cauchy estimate applied to the
# η-small difference `H_η' − H_0'` on the enlarged rectangle) instead of
# splitting into two independent sups. Certified ≈ 7.1 versus ≈ 56.1 from
# `compute_M_pp_bound` — an ~8× tightening of the term that dominates
# `Cr_phi_uzz`. See Numerical_Library/m_pp_tight.py.

[[oracles]]
axiom       = "h_M_pp_tight_oracle"
bound_field = "M_pp_tight_val"
oracle_fn   = "compute_M_pp_tight_bound"
```

## What this attempt claims, and what it does not

**Delivered:** `Cr_val = 1/14 ≈ 0.0714`, a 14× reduction from V11's `1`. Same sink signature, same locked `r = 23/25`, `eta = 1/100`, same oracle rectangle `Ω(1635/10000, 1115/1000)`, no `Proof/Lib` edits, no weakening of the trust surface. The one new axiom is a sup-norm bound on `‖∂²_z F_p‖` over the existing rectangle — the identical statement shape to the `h_M_pp_oracle` it supersedes, differing only in the witness, and re-verified from scratch each audit by `compute_M_pp_tight_bound`.

**Not delivered:** the `1/6400` bar. I want to be explicit that this is a property of the architecture, not of the effort spent. The Taylor remainder is `½·sup_p‖∂²_p F_inv‖·p²`, and identity (75) differentiated twice gives, pointwise at `w = F_inv(p,z)`,

```
½‖∂²_p F_inv‖ ≤ ‖Φ'‖‖Φ‖/‖D‖² + ½‖DD‖‖Φ‖²/‖D‖³,   Φ = H_η − H_0.
```

Even at `p → 0`, with the certified `sup‖Φ‖ ≈ 0.0476`, `sup‖Φ'‖ ≈ 0.0541`, `inf‖D‖ ≈ 0.643` (all attained near the corner `w ≈ 0.8365 + 1.115i`), the first term alone is `≈ 0.0074` — about 47× above `1/6400 = 1.5625·10⁻⁴`. Since `Φ = O(η)` with `η` locked at `1/100`, no tightening of `M_pp`, `inv_F_p_z`, or the rectangle can cross that floor; only a different second-order identity, or a domain restriction that shrinks `sup‖Φ‖`, could. Two further levers I costed and rejected for a one-shot: a combined-ratio oracle for `sup‖DD‖/‖D‖³` (worth ~8× on term 2, since `sup(ab) ≪ sup a · sup b` here — the two sups are attained at different points), and choosing the existential `pr` as `min(pr_paper, 1/100)` to kill the `p`-dependent perturbations (worth ~2×). Both require transcribing the Step-5 lemma and its glue into the candidate, including the `private` helper `Dh_eq_one`, with no way to compile-check — I judged the failure risk not worth 2–3× when a truncated or non-compiling file scores nothing.