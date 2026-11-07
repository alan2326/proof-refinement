## What I'm doing and why

I read the arithmetic before writing anything. V11's score decomposes as

```
Cr_phi_uzz = M_phi·M_phi_prime·invD²  +  ½·M_pp·invD³·M_phi²
           = 0.0104                   +  0.5125            = 0.5229   (declared 1)
```

Two of the five declared constants are loose against what the oracles actually certify, and one oracle is itself loose:

1. **`inv_F_p_z_val = 2`** but `compute_inv_F_p_z_bound` certifies `1/inf‖D‖ ≈ 1/(0.6427 − 0.0541) ≈ 1.700` (V10/V11 both record ≈ 1.7035). Declaring `9/5` is safe and cuts `invD³` from 8 to 5.832.
2. **`M_pp_val = 56.08`** is dominated by `m_pp.py`'s Cauchy step on **`H_η'`** itself: `sup‖H_η'‖_outer/d ≈ 2.082/0.0409 ≈ 51`. But `DD = H_0'' + p·(H_η−H_0)''`, and Cauchy applied to the **difference** gives `sup‖H_η'−H_0'‖_outer/d ≈ 0.07/0.0409 ≈ 1.7` instead of 51. With `sup‖H_0''‖ = |0.8365|/(1−0.8365²)^{3/2} ≈ 5.08` (attained on ∂Ω at `v=0`, hit by the boundary scan), the same rigorous triangle+Cauchy argument yields `M_pp ≈ 6.6–7.6`. That is a strictly *tighter* certificate for the *same* axiom statement — a new oracle row, not a weakened trust surface.
3. `M_phi_val`/`M_phi_prime_val` are already exactly the oracles' rationalized outputs (`0.0476·1.001+10⁻⁴` ceils to `239/5000`; likewise `543/10000`), so there is no room there — I left them alone.

Result: `Cr_phi_uzz = 0.0084 + 0.0666 = 0.075035…`, declared `Cr_val = 2/25`. **No Lean infrastructure changes** — V12 reuses `lemma_5_4_paper_on_domain_phi_uzz` verbatim; only three numerals and one axiom name change, so compile risk is near zero.

I should state plainly: **`Cr_val ≤ 1/6400` is not reachable on this trust surface.** Term 1 alone is `‖Φ‖·‖Φ'‖·sup‖h‖²`; with the certified sups `‖Φ‖ ≈ 0.0476`, `‖Φ'‖ ≈ 0.0541` and `sup‖h‖ ≥ 1/sup‖D‖ = 1/1.825`, *any* bound of this shape is `≥ 7.7·10⁻⁴ > 1.5625·10⁻⁴`, even granting a perfect joint oracle — and the realistic value is `7.5·10⁻³`. Getting under the bar would need a smaller `η`, a smaller oracle rectangle (both locked), or a remainder estimate that exploits cancellation rather than factoring through `sup|Φ|·sup|Φ'|`. So I optimized for a large, high-confidence recorded improvement (**12.5×**, `1 → 0.08`) instead of a coin-flip on an unreachable bar.

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
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
```

```python path=ProofRefinement/Lemma54/Numerical_Library/m_pp_tight.py
"""M_pp_tight oracle: a strictly tighter certificate for the SAME sup-norm
claim that `m_pp.py` backs, namely

    M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖(1−p) H_0''(w) + p H_η''(w)‖
         = sup_{(p, w)} ‖∂²_z F_p(η, p, w)‖.

Backs the Lean axiom

    axiom h_M_pp_tight_oracle :
      ∀ p ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper …),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_tight_val

with the same domain `oracle_domain = Braverman.Omega delta_val B_val` and
the same quantity as `h_M_pp_oracle`. Nothing about the claim is weakened;
only the numerical route to it is sharper.

Why `m_pp.py` is loose
----------------------
`m_pp.py` uses the triangle split

    ‖(1−p) H_0'' + p H_η''‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

and then bounds `sup‖H_η''‖` by Cauchy on `H_η'` over the enlarged
rectangle: `sup_{∂Ω_outer}‖H_η'‖ / d` with `d = δ/4`. At the production
rectangle Ω(1635/10000, 1115/1000) that is ≈ 2.082 / 0.040875 ≈ 51 — the
*whole* size of `H_η'`, which is ≈ `H_0'` and has nothing to do with η. The
`H_0''` term contributes only ≈ 5.08, so the certificate lands at ≈ 56.

The tighter decomposition
-------------------------
`F_p` is affine in `p`, so

    DD(η, p, w) = ∂²_z F_p = H_0''(w) + p · (H_η − H_0)''(w),

whence, for `p ∈ [0, p_max]`,

    ‖DD‖ ≤ sup_Ω ‖H_0''‖ + p_max · sup_Ω ‖(H_η − H_0)''‖            (1)
         ≤ sup_Ω ‖H_0''‖ + p_max · sup_{Ω_outer} ‖H_η' − H_0'‖ / d.  (2)

(1) is the triangle inequality on the affine family; `p_max = 1` is licensed
on the Lean side by the seed axiom `pr_paper_le_one`. (2) is Cauchy's
estimate for a second derivative: for `w ∈ Ω`, the closed disk of radius `d`
about `w` lies in `Ω_outer = Ω(δ − d, B + d)` (which widens the real half-
width by exactly `d` and the imaginary half-height by exactly `d`), and
`H_η − H_0` is analytic on the closure of `Ω_outer` because
`|Re w| ≤ 1 − (δ − d) < 1`. Sup on `∂Ω_outer` bounds sup on the closure by
max-modulus — the same justification `m_pp.py` and `m_phi.py` already rely on.

The point is that (2) measures the η-deformation rather than `H_η'` itself:
`sup_Ω ‖H_η' − H_0'‖ ≈ 0.054` (the `M_phi_prime` quantity), growing only
mildly on the slightly larger `Ω_outer`, so the second summand drops from
≈ 51 to ≈ 1.5–2.5 and the total from ≈ 56.0 to ≈ 6.6–7.6.

Both summands are computed with the same primitives `m_pp.py` uses, so this
module adds no new numerical machinery — only a different (sharper) algebraic
split before the interval arithmetic.
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
    p_max: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    """Run the certified `sup_{[0,p_max] × Ω} ‖∂²_z F_p‖` pipeline via the
    η-aware split (1)–(2) of the module docstring."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # --- Term 1: sup ‖H_0''(w)‖ on ∂Ω via the closed form
    #             H_0''(w) = w · (1 − w²)^{−3/2}.
    # `H_0''` is analytic on the closure of Ω (its only singularities are at
    # w = ±1, and |Re w| ≤ 1 − δ < 1), so the boundary scan bounds the sup on
    # Ω̄ by max-modulus. Same expression as m_pp.py's first component.
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z          # 1 − w²
        # rsqrt(u) = u^{−1/2}, so u^{−3/2} = rsqrt(u) / u.
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # --- Term 2: sup ‖(H_η − H_0)''(w)‖ on Ω via Cauchy on Ω_outer.
    # d = δ/4 matches m_pp.py's enlargement, so the enlarged rectangle here is
    # exactly the one m_pp.py already evaluates the phi-series on.
    d = delta_arb / arb(4)
    delta_inner = delta_arb - d   # widens the real half-width by d
    B_outer = B_arb + d           # widens the imaginary half-height by d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the (H_η − H_0)'' Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H0_p)

    max_phi_prime_outer = _max_on_rect(
        phi_prime, delta_inner, B_outer, n_per_edge, prec,
    )
    max_phi_pp = max_phi_prime_outer / d

    # --- Combine per (1): ‖DD‖ ≤ sup‖H_0''‖ + p_max · sup‖(H_η − H_0)''‖.
    M_pp_arb = max_H0_pp + p_max_arb * max_phi_pp

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_phi_prime_outer_str": max_phi_prime_outer.str(20, more=True),
        "max_phi_pp_str": max_phi_pp.str(20, more=True),
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_tight_bound(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 512,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on
    `M_pp = sup_{p ∈ [0, p_max], w ∈ Ω(δ, B)} ‖∂²_z F_p(η, p, w)‖`,
    via the η-aware split of the module docstring.

    Defaults match the V9–V12 oracle rectangle (`δ = 1635/10000`,
    `B = 1115/1000`) and `p_max = 1` (licensed on the Lean side by the seed
    axiom `pr_paper_le_one`). Precision settings mirror
    `compute_inv_F_p_z_bound` (`n_per_edge = 512`, `prec = 200`,
    `K_max = 80`), which is known to evaluate the phi-series happily on the
    enlarged rectangle. Callable with no arguments; the JSON cache in
    `.cache/` makes repeat calls free.

    Expected magnitude at the pinned defaults: `sup_Ω‖H_0''‖ ≈ 5.08`
    (attained on ∂Ω at `Re w = 1 − δ`, `Im w = 0`) plus
    `sup_{Ω_outer}‖H_η' − H_0'‖ / d ≈ 0.06–0.10 / 0.040875 ≈ 1.5–2.5`,
    for a total ≈ 6.6–7.6 — versus ≈ 56.0 from `compute_M_pp_bound`.
    """
    key = {
        "fn": "compute_M_pp_tight_bound",
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_pp_arb = arb(cached["M_pp_str"])
    bound = arb_to_rational_ub(
        M_pp_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )
    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_phi_prime_outer_arb_str": cached["max_phi_prime_outer_str"],
            "max_phi_pp_arb_str": cached["max_phi_pp_str"],
        },
    )
```

```python path=ProofRefinement/Lemma54/Numerical_Library/__init__.py
"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from a `[[oracles]]` row in `lemma.toml` (`oracle_fn`) so the
    evaluator can re-run the function and check the candidate's declared
    rational lies above the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`, callable
     with no arguments (all parameters keyword-only with pinned defaults).
  2. Add a matching `[[oracles]]` row in `lemma.toml` with the axiom name
     (namespace-stripped), the candidate's `bound_field` def, and `oracle_fn`.
  3. Declare the corresponding axiom in the candidate and use it in the proof.

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
# with a direct η-aware ≈ 2 — a ~14× tightening of `invFp` (~196× of
# `invFp²`), driving `Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z` down
# from 3.79 to ≈ 1.65 at the V9 parameters.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"

# Added by V12 (inline oracle). SAME claim as `h_M_pp_oracle` above — a
# sup-norm bound on `‖∂²_z F_p(η, p, w)‖` over `p ∈ [0, 1]` and the SAME
# rectangle `Ω(1635/10000, 1115/1000)` — with a strictly tighter certificate.
# `compute_M_pp_bound` bounds `sup‖H_η''‖` by Cauchy on `H_η'` itself
# (`sup‖H_η'‖_outer / d ≈ 2.082/0.040875 ≈ 51`, i.e. the full size of `H_η'`,
# nothing to do with η). `compute_M_pp_tight_bound` instead uses the affine-
# in-p split `DD = H_0'' + p·(H_η − H_0)''` and applies Cauchy to the
# η-deformation:
#     ‖DD‖ ≤ sup_Ω‖H_0''‖ + p_max · sup_{Ω_outer}‖H_η' − H_0'‖ / d
#          ≈ 5.08 + 0.07/0.040875 ≈ 6.8   (vs ≈ 56.0),
# with `p_max = 1` licensed by the seed axiom `pr_paper_le_one`, `d = δ/4`,
# `Ω_outer = Ω(δ − d, B + d)`, and `H_η − H_0` analytic on `Ω_outer`'s closure
# (`|Re w| ≤ 1 − 3δ/4 = 0.877375 < 1`). The `h_M_pp_oracle` row above is left
# untouched; this row is additive.

[[oracles]]
axiom       = "h_M_pp_tight_oracle"
bound_field = "M_pp_tight_val"
oracle_fn   = "compute_M_pp_tight_bound"
```

## Summary

| | V11 (current) | V12 (this attempt) |
|---|---|---|
| `inv_F_p_z_val` | 2 | **9/5** (oracle certifies ≈1.705) |
| `M_pp` bound | 56.08 (`compute_M_pp_bound`) | **10** (`compute_M_pp_tight_bound`, ≈6.6–7.6) |
| `Cr_phi_uzz` | 0.5229 | **0.075035** |
| **`Cr_val`** | **1** | **2/25 = 0.08** (12.5× better) |

Zero edits to `Proof/`, `Evaluator.py`, `SearchConfig.lean`, or any prior candidate; the oracle rectangle `Ω(1635/10000, 1115/1000)`, `r = 23/25`, `eta = 1/100`, and every trusted-axiom statement are byte-identical to V11. The new `[[oracles]]` row is additive and its axiom asserts the same sup-norm claim on the same domain as the already-approved `h_M_pp_oracle`, with a sharper certificate. The one closing proof obligation is the literal-rational inequality `468971775/6250000000 ≤ 2/25` (margin ≈ 0.004965), decided exactly by `norm_num`.

Residual risk, stated honestly: the only step I could not verify is the new oracle's returned value, since I cannot execute anything. Its two summands are computed with the identical primitives `m_pp.py` already uses on the identical rectangles, and the old certificate's own arithmetic (56.02 with `sup‖H_0''‖ ≈ 5.08` forces `sup‖H_η'‖_outer ≈ 2.082`, matching the closed form `sup‖H_0'‖_outer = 2.0842` to three decimals) independently witnesses that `H_η'` and `H_0'` differ by well under 0.1 on the enlarged rectangle — which is what `M_pp_tight_val = 10` needs, with roughly 30% headroom.