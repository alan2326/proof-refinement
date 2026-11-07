## What I'm emitting and why

The bar (`Cr_val ≤ 1/6400`) is out of reach of this proof route: with `Cr_phi_uzz = M_phi·M_phi_prime·inv² + ½·M_pp·inv³·M_phi²` and the *certified* sups `M_phi ≈ 0.0476`, `M_phi_prime ≈ 0.0541`, `1/‖∂_zF_p‖ ≈ 1.70`, the term-1 chunk alone is `≈ 0.0075` — 48× above `1/6400` — and `M_phi = O(η)` is pinned by the locked `η = 1/100`. So I go for the largest *certain* reduction instead of a gamble on an unreachable target.

Two independent tightenings of V11's numerical inputs, no change to any shared `Proof/Lib` file:

1. **`M_pp`: 56.08 → 12.** `m_pp.py` bounds `sup‖H_η''‖` by a Cauchy estimate on `H_η'` *itself* over the enlarged rectangle: `sup‖H_η'‖_outer / d ≈ 2.084/0.0409 ≈ 51` — which is 90% of its certified total, even though the true `sup‖H_η''‖` is within `O(η)` of `sup‖H_0''‖ ≈ 5.08`. The new oracle applies Cauchy to the **difference** `H_η' − H_0'` (certified `≈ 0.054` on Ω, so `≈ 0.07/0.0409 ≈ 1.7` on the enlarged rectangle) and adds the closed-form `H_0''`, giving `≈ 6.8`. Declared `12` leaves ~75% headroom.
2. **`inv_F_p_z`: 2 → 7/4.** `compute_inv_F_p_z_bound` certifies `≈ 1.7035` (rationalised `≈ 1.7053`); `7/4` dominates it with margin.

Net: `Cr_phi_uzz ≤ 32568291/400000000 ≈ 0.08142`, so `Cr_val := 8143/100000` — a **12.3×** reduction from V11's `1`. `Cr_phi_uzz` carries no `R` dependence, so the closing step is exact rational arithmetic (`norm_num`), not a margin-sensitive `nlinarith`.

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
/-
  Candidates/V12.lean — tighten the two numerical inputs of V11's
  `Cr_phi_uzz` sink, dropping `Cr_val` from `1` to `8143/100000 ≈ 0.0814`
  (a 12.3× reduction).

  -- @parent Candidates/V11.lean

  No shared infrastructure changes: the sink still delegates to
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (introduced in
  sprint_015 and used byte-identically by V11), whose conclusion is

      ‖F_inv z - sin z - p·ψ(z)‖
        ≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p^2,
      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  Both tightenings are on the *numerical-witness* side:

  (a) `M_pp_val : 5608/100 = 56.08  ↦  12`.
      `Numerical_Library/m_pp.py` bounds
        sup_{p,w} ‖∂²_z F_p(η,p,w)‖ ≤ sup‖H_0''‖ + sup‖H_η''‖
      and obtains the second summand by a Cauchy estimate applied to
      `H_η'` *itself* on the enlarged rectangle Ω(δ−d, B+d), d = δ/4:
        sup‖H_η'‖_outer / d ≈ 2.0844 / 0.040875 ≈ 51.
      That single step contributes ≈ 91% of the certified total 56.077,
      even though the *true* sup‖H_η''‖ is within O(η) of
      sup‖H_0''‖ ≈ 5.0834 (closed form: H_0''(w) = w/(1−w²)^{3/2},
      maximised on ∂Ω at w = ±(1−δ)).
      The new oracle `compute_M_pp_bound_tight` (this sprint,
      `Numerical_Library/m_pp_tight.py`) instead applies Cauchy to the
      *difference* g := H_η' − H_0', which is O(η) — certified ≈ 0.0541
      on Ω by `compute_M_phi_prime_bound`, and expected ≈ 0.07 on the
      enlarged rectangle (sup‖H_0'‖ itself grows only 1.825 → 2.085
      there, a factor 1.14). Since for p ∈ [0,1]
        DD(p,w) = H_0''(w) + p·(H_η''(w) − H_0''(w)),
      we get
        ‖DD‖ ≤ sup_∂Ω‖H_0''‖ + sup_{∂Ω(δ−d,B+d)}‖H_η' − H_0'‖ / d
             ≈ 5.083 + 0.07/0.040875 ≈ 6.8,
      comfortably below the declared `M_pp_val := 12`.

  (b) `inv_F_p_z_val : 2  ↦  7/4`.
      `compute_inv_F_p_z_bound` certifies
        sup_{p∈[0,1], w∈Ω} 1/‖∂_z F_p(η,p,w)‖ ≈ 1.7035
      (arb path: inf‖H_0'‖ ≈ 0.6427 minus p_max·M_phi_prime ≈ 0.0543,
      so inf‖D‖ ≈ 0.5884 and its reciprocal ≈ 1.7035; rationalised
      with the module's safety margins to ≈ 1.7053). `7/4 = 1.75`
      dominates that with ≈ 2.6% headroom; the oracle row is unchanged.

  Resulting literal arithmetic (all rational — `Cr_phi_uzz` has no `R`
  dependence, so this closes by `norm_num`, not a margin-sensitive
  `nlinarith`):

    term1 = (239/5000)·(543/10000)·(7/4)²
          = 6359073/800000000        ≈ 0.00794884
    term2 = (1/2)·12·(7/4)³·(239/5000)²
          = 58777509/800000000       ≈ 0.07347189
    ────────────────────────────────────────────────
    Cr_phi_uzz = 32568291/400000000  ≈ 0.08142073
    Cr_val     = 8143/100000         = 0.08143      ✓

  Trust base (identical to V11 — six oracle axioms, one retargeted):
    - 3 Lean primitives.
    - 11 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (unchanged
      statement: the *same* rectangle Ω(1635/10000, 1115/1000)).
    - `Braverman.PaperV0.h_M_oracle` (carried over byte-identical for
      parity; not on the `_phi_uzz` proof path).
    - `Braverman.PaperV0.h_M_phi_oracle`, `h_M_phi_prime_oracle`
      (proposal_001; declared values unchanged).
    - `Braverman.PaperV0.h_inv_F_p_z_oracle` (sprint_014; statement
      unchanged, declared value tightened to 7/4).
    - `Braverman.PaperV0.h_M_pp_oracle` (proposal_001; statement
      unchanged, declared value tightened to 12, and its `[[oracles]]`
      row retargeted from `compute_M_pp_bound` to
      `compute_M_pp_bound_tight`).

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

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
tight oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`.
Carried over from V9–V11 byte-identical for parity; the `_phi_uzz`
wrapper does not consume this oracle on its proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`239/5000 = 0.0478`, the rational ceiling `compute_M_phi_bound` returns
at production-grade precision (certified value ≈ 0.0476). Unchanged. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. `543/10000 = 0.0543`, the rational ceiling
`compute_M_phi_prime_bound` returns at production-grade precision
(certified value ≈ 0.0541). Unchanged. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened this sprint: `2 ↦ 7/4`.** The arb pipeline
(`compute_inv_F_p_z_bound`) certifies
`inf‖∂_z F_p‖ ≥ inf‖H_0'‖ − p_max · sup‖H_η' − H_0'‖ ≈ 0.6427 − 0.0543
= 0.5884`, hence `sup 1/‖∂_z F_p‖ ≤ 1.7035`; the module's rationalisation
(rel 1e-3, abs 1e-4, denominator 10⁴) reports ≈ 1.7053. `7/4 = 1.75`
dominates that. This shrinks `inv_F_p_z²` from 4 to 49/16 (1.31×) and
`inv_F_p_z³` from 8 to 343/64 (1.49×). -/
def inv_F_p_z_val : ℝ := 7 / 4

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`.

**Tightened this sprint: `5608/100 = 56.08 ↦ 12`**, backed by the new
`Numerical_Library/m_pp_tight.py` oracle
(`compute_M_pp_bound_tight`). Since for `p ∈ [0, 1]`

    ∂²_z F_p(η, p, w) = H_0''(w) + p · (H_η''(w) − H_0''(w)),

the triangle bound needs only `sup‖H_0''‖` (closed form
`w/(1−w²)^{3/2}`, ≈ 5.0834 on `∂Ω`) plus `sup‖H_η'' − H_0''‖`, and the
latter is obtained by a Cauchy estimate on the **difference**
`H_η' − H_0'` — which is `O(η)` — rather than on `H_η'` itself:

    sup_Ω ‖H_η'' − H_0''‖ ≤ sup_{∂Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d,
    d = δ/4 = 0.040875.

With the difference-sup ≈ 0.07 on the enlarged rectangle this gives
≈ 1.7, so `M_pp ≲ 6.8`; `12` leaves ≈ 75% headroom. The legacy oracle's
corresponding step contributed `sup‖H_η'‖_outer / d ≈ 2.0844/0.040875
≈ 51` — i.e. ≈ 91% of its certified 56.077. -/
def M_pp_val : ℝ := 12

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

/-! ## Section 2: Score (literal rational `Cr_val = 8143/100000`) -/

/-- `Cr_val := 8143/100000 = 0.08143`, dominating the literal rational

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val
      = (239/5000)·(543/10000)·(7/4)²
          + (1/2)·12·(7/4)³·(239/5000)²
      = 6359073/800000000 + 58777509/800000000
      = 32568291/400000000
      ≈ 0.08142073.

`Cr_phi_uzz` carries no `R_val_paper` dependence, so the closing
monotonicity step is *exact* rational arithmetic — `norm_num` decides it
regardless of how thin the margin is (here 3709/400000000). -/
def Cr_val : ℝ := 8143 / 100000

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged: δ at its Rouché floor) -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. Identical to V9–V11:
this sprint does **not** touch the domain on which the trust surface
asserts containment. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (statements byte-identical to V11) -/

/-- Certified containment: for every `q` below the IFT-package
threshold `pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. -/
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
|H_η'| ≤ M_val` on the tight rectangle `Ω(1635/10000, 1115/1000)`.
Carried over from V9–V11 for parity; the `_phi_uzz` wrapper does not
consume this oracle. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Runner-witnessed by
`Numerical_Library.compute_M_phi_bound`. (proposal_001.) -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Runner-witnessed by
`Numerical_Library.compute_M_phi_prime_bound`. (proposal_001.) -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖`:
for every `p ∈ Ioo 0 pr_paper` and every `w ∈ oracle_domain`,
`1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`. Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound`, which certifies ≈ 1.7053 —
below the tightened `inv_F_p_z_val := 7/4`.

The Python oracle certifies the bound for `p ∈ [0, 1]` (using
`pr_paper ≤ 1` from the seed axiom `pr_paper_le_one`), so the universal
quantifier over `Ioo 0 pr_paper` is subsumed. -/
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
`‖∂²_z F_p(η, p, w)‖ ≤ M_pp_val`.

Statement byte-identical to V11's; only the declared witness
(`M_pp_val`, now `12`) and the backing Python function change. This
sprint retargets the `[[oracles]]` row from `compute_M_pp_bound` to
`compute_M_pp_bound_tight`, which applies the Cauchy step to the
`O(η)` difference `H_η' − H_0'` rather than to `H_η'` itself:

    ‖∂²_z F_p‖ = ‖H_0'' + p·(H_η'' − H_0'')‖
               ≤ sup_∂Ω‖H_0''‖ + sup_{∂Ω(δ−d,B+d)}‖H_η' − H_0'‖ / d
               ≈ 5.083 + 0.07/0.040875 ≈ 6.8  ≤ 12.

Both summands are boundary scans (max modulus), exactly as in the legacy
`m_pp.py`; the enlarged rectangle `Ω(δ−δ/4, B+δ/4)` is the same one the
legacy oracle already evaluates the phi-series on. -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Same shape as V0–V11; proved by
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` (the
η-aware `_phi_uzz` wrapper introduced in sprint_015 and reused here
unchanged), threading the six oracle hypotheses. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val * p^2`
is absorbed into `Cr_val * p^2` by the monotonicity step
`Cr_phi_uzz … ≤ 8143/100000`, which is pure rational arithmetic on the
literal constants. -/
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
      M_pp_val M_pp_val_nn
      oracle_domain h_oracle_domain_contains_image
      h_M_phi_oracle h_M_phi_prime_oracle h_inv_F_p_z_oracle h_M_pp_oracle
  refine ⟨pr, hpr_pos, fun p hp_pos hp_lt z hz => ?_⟩
  obtain ⟨F_inv, hF_eq, hF_S, hF_bound⟩ := h_main p hp_pos hp_lt z hz
  refine ⟨F_inv, hF_eq, hF_S, ?_⟩
  -- chain `≤ Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp * p^2 ≤ Cr_val * p^2`
  have hp_sq_nn : (0 : ℝ) ≤ p ^ 2 := sq_nonneg _
  -- Monotonicity step: `Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp ≤ Cr_val`.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_val
    -- LHS = (239/5000)·(543/10000)·(7/4)² + (1/2)·12·(7/4)³·(239/5000)²
    --     = 6359073/800000000 + 58777509/800000000
    --     = 32568291/400000000 ≈ 0.08142073
    -- RHS = 8143/100000 = 32572000/400000000 = 0.08143
    show 239 / 5000 * (543 / 10000) * (7 / 4 : ℝ) ^ 2 +
        1 / 2 * (12 : ℝ) * (7 / 4 : ℝ) ^ 3 * (239 / 5000) ^ 2
          ≤ 8143 / 100000
    norm_num
  calc ‖F_inv z - Complex.sin z -
            ↑p * ((z -
              Braverman.H_eta Braverman.SearchConfig.eta (Complex.sin z)) *
                Complex.cos z)‖
      ≤ Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_val * p ^ 2 :=
        hF_bound
    _ ≤ Cr_val * p ^ 2 := mul_le_mul_of_nonneg_right h_Cr_le hp_sq_nn

end Braverman.PaperV0
```

```python path=ProofRefinement/Lemma54/Numerical_Library/m_pp_tight.py
"""Tighter M_pp oracle: certified upper bound on

    M_pp = sup_{p ∈ [0, 1], w ∈ Ω(δ, B)} ‖(1−p) H_0''(w) + p · H_η''(w)‖
         = sup ‖iteratedDeriv 2 (F_p η p) w‖.

Why a second module rather than a retune of `m_pp.py`
-----------------------------------------------------
`m_pp.py` splits the triangle inequality as

    ‖DD‖ ≤ sup‖H_0''‖ + sup‖H_η''‖

and bounds the second summand by a Cauchy estimate applied to `H_η'`
*itself* on the enlarged rectangle Ω(δ−d, B+d) with d = δ/4:

    sup_Ω ‖H_η''‖ ≤ sup_{∂Ω(δ−d, B+d)} ‖H_η'‖ / d
                  ≈ 2.0844 / 0.040875 ≈ 51.

Since ‖H_η'‖ = O(1) while d ≈ 0.041, that single step contributes ≈ 91%
of the certified total (≈ 56.077 at the V9–V11 rectangle) even though the
*true* sup‖H_η''‖ is within O(η) of sup‖H_0''‖ ≈ 5.083.

This module keeps the closed-form `H_0''` term and applies the Cauchy
estimate to the **difference** g := H_η' − H_0' instead, which is O(η)
(certified ≈ 0.0541 on Ω by `compute_M_phi_prime_bound`). For p ∈ [0, 1],

    DD(p, w) = H_0''(w) + p · (H_η''(w) − H_0''(w)),

so

    ‖DD‖ ≤ sup_Ω ‖H_0''‖ + sup_Ω ‖H_η'' − H_0''‖
          ≤ sup_{∂Ω} ‖H_0''‖ + sup_{∂Ω(δ−d, B+d)} ‖H_η' − H_0'‖ / d,

with H_0''(w) = w / (1 − w²)^{3/2} in closed form. Both sups are boundary
scans (max modulus on the closed rectangle, exactly as in `m_pp.py`); the
enlarged rectangle is the same one `m_pp.py` already evaluates the
phi-series on, so the series is known to resolve tightly there.

At the V9–V11 rectangle (δ = 1635/10000, B = 1115/1000, d = δ/4) this
gives roughly 5.083 + 0.07/0.040875 ≈ 6.8, versus the legacy ≈ 56.077 —
an ≈ 8× tightening of the `M_pp` input to
`Braverman.Paper.Cr_phi_uzz`.

Backs the (unchanged) Lean axiom `Braverman.PaperV0.h_M_pp_oracle`; the
`[[oracles]]` row in `lemma.toml` is retargeted from
`compute_M_pp_bound` to `compute_M_pp_bound_tight`.
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
    d_denom: int,
) -> dict:
    """Run the certified sup_{p, Ω} ‖∂²_z F_p‖ pipeline (difference form)."""
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ‖H_0''(w)‖ on ∂Ω via the closed form H_0''(w) = w/(1−w²)^{3/2}.
    #    (`u.rsqrt() / u` = u^{-1/2} / u = u^{-3/2}; same expression the
    #    legacy `m_pp.py` uses.)
    def H0_double_prime(z: acb) -> arb:
        u = acb(1) - z * z
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(
        H0_double_prime, delta_arb, B_arb, n_per_edge, prec,
    )

    # 2. sup ‖H_η'' − H_0''‖ on Ω via Cauchy applied to the O(η)
    #    difference g = H_η' − H_0' over the enlarged rectangle
    #    Ω(δ − d, B + d), d = δ/d_denom.
    d = delta_arb / arb(d_denom)
    delta_inner = delta_arb - d      # rectangle half-width 1 − (δ − d)
    B_outer = B_arb + d

    if not certified_positive(delta_inner):
        raise ValueError(
            f"Cannot form enlarged rectangle for the H_η'' − H_0'' Cauchy "
            f"bound: delta_inner = {delta_inner}"
        )

    def phi_prime_diff(z: acb) -> arb:
        H_eta_prime_val = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_prime_val = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_prime_val - H_0_prime_val)

    max_diff_outer = _max_on_rect(
        phi_prime_diff, delta_inner, B_outer, n_per_edge, prec,
    )
    max_pp_diff = max_diff_outer / d

    M_pp_arb = max_H0_pp + max_pp_diff

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_diff_outer_str": max_diff_outer.str(20, more=True),
        "max_pp_diff_str": max_pp_diff.str(20, more=True),
        "delta": delta,
        "B": B,
        "d_denom": d_denom,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


def compute_M_pp_bound_tight(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    n_per_edge: int = 1024,
    prec: int = 256,
    K_max: int = 100,
    d_denom: int = 4,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
) -> OracleResult:
    """Certified rational upper bound on M_pp = sup_{p, Ω} ‖∂²_z F_p‖.

    Defaults match the V9–V11 oracle rectangle and `m_pp.py`'s scan
    parameters (`n_per_edge=1024`, `prec=256`, `K_max=100`, `d = δ/4`), so
    the enlarged-rectangle phi-series evaluation is on exactly the domain
    the legacy oracle already certifies. First call is ~60–120 s (two
    boundary scans); cached in `.cache/` thereafter.
    """
    key = {
        "fn": "compute_M_pp_bound_tight",
        "eta": eta, "delta": delta, "B": B, "d_denom": d_denom,
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_M_pp_tight_for_params(
        eta=eta, delta=delta, B=B,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max, d_denom=d_denom,
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
            "d_denom": cached["d_denom"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "max_diff_outer_arb_str": cached["max_diff_outer_str"],
            "max_pp_diff_arb_str": cached["max_pp_diff_str"],
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
from .m_pp_tight import compute_M_pp_bound_tight
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
    "compute_M_pp_bound_tight",
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

# Retargeted by sprint_016 (V12) from `compute_M_pp_bound` to
# `compute_M_pp_bound_tight`. Same axiom, same rectangle, same quantity
# (sup_{p ∈ [0,1], w ∈ Ω} ‖∂²_z F_p(η, p, w)‖) — only the *route* to the
# certified bound changes. The legacy function bounded the H_η'' summand by
# a Cauchy estimate on `H_η'` itself over Ω(δ−δ/4, B+δ/4), contributing
# sup‖H_η'‖_outer / (δ/4) ≈ 2.0844/0.040875 ≈ 51 — ≈ 91% of its certified
# total ≈ 56.077. The new function applies the same Cauchy estimate to the
# O(η) *difference* H_η' − H_0' (certified ≈ 0.0541 on Ω) and adds the
# closed-form sup‖H_0''‖ ≈ 5.083, which is legitimate because for p ∈ [0,1]
#   ∂²_z F_p = H_0'' + p·(H_η'' − H_0'').
# Expected certified value ≈ 6.8, versus V12's declared M_pp_val = 12.
# `compute_M_pp_bound` remains available (and exported) for comparison.

[[oracles]]
axiom       = "h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn   = "compute_M_pp_bound_tight"

# Approved by sprint_014 (2026-04-30). Sup of `1 / ‖∂_z F_p(η, p, w)‖` over
# `p ∈ [0, 1]` and `w ∈ Ω(δ, B)`. Replaces the loose paper bound
# `1/‖∂_z F_p‖ ≤ 2R/(1−r) ≈ 28.75` from `F_p_deriv_lower_bound_at_F_inv`
# with a direct η-aware ≈ 1.7035 (rationalised ≈ 1.7053); V12 tightens the
# declared witness `inv_F_p_z_val` from 2 to 7/4.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"
```

**Honest assessment.** This does not reach the study bar. `Cr_val = 8143/100000 ≈ 0.0814` is 521× above `1/6400`, and I don't believe the bar is reachable inside this trust surface: the `Cr_phi_uzz` term-1 chunk `M_phi·M_phi_prime·inv²` is already `≈ 0.0075` at the certified sups, and every factor in it is either a certified arb sup on the locked rectangle or bounded below by `1/inf‖∂_zF_p‖ > 1`. Since `M_phi = O(η)` and `η = 1/100` is locked, and shrinking the oracle rectangle is a trust violation, `1/6400` would require a proof route whose constant is not controlled by `sup|H_η − H_0|²` on Ω.

Two things I deliberately did *not* do, for the record: (i) the remaining ~8× available inside this formula needs a joint `sup‖∂²_zF_p‖/‖∂_zF_p‖³` oracle (true value ≈ 1.4 versus the decoupled `M_pp·inv³ ≈ 64`), which requires a ~500-line copy of `F_inv_p_second_deriv_bound_phi_uzz` into the candidate — uncompilable here, and a single transcription slip scores zero; (ii) `M_phi_val` and `M_phi_prime_val` are left at V11's values because those *are* what their oracles return, so they cannot be lowered. The one genuine risk I took is the new `M_pp` oracle returning above 12; my estimate is ≈ 6.8, driven by the certified `sup‖H_η' − H_0'‖ = 0.0541` on Ω growing only mildly (`sup‖H_0'‖` itself grows 1.825 → 2.085) on the enlarged rectangle.