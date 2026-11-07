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
