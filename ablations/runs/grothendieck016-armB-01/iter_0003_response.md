Picking up: V12 passed at `Cr_val = 9/100`, and the evaluator printed the actual certified oracle values, which are all substantially tighter than the literals V12 declared:

| slot | V12 declared | oracle certified | slack |
|---|---|---|---|
| `M_phi_val` | 239/5000 = .0478 | **61/2500 = .0244** | 1.96× |
| `M_phi_prime_val` | 543/10000 = .0543 | **59/2000 = .0295** | 1.84× |
| `inv_F_p_z_val` | 9/5 = 1.8 | **3407/2000 = 1.7035** | 1.06× |
| `M_pp_tight_val` | 12 | **61373/10000 = 6.1373** | 1.96× |

Pulling every literal down to exactly its certified value is free — same oracles, same functions, no new trust surface — and it collapses `Cr_phi_uzz`:

- term₁ = `M_φ·M_φ'·inv²` = 41775928751/2·10¹³ ≈ 2.0888·10⁻³
- term₂ = `½·M_pp·inv³·M_φ²` ≈ 9.0314·10⁻³
- total ≈ **1.11202·10⁻²**, so `Cr_val := 3/250 = 0.012` clears it exactly.

That's a 7.5× reduction on V12. I'm shipping only the candidate this turn (no Python/TOML edits) so the four already-working oracle functions stay byte-identical and their printed values remain the ones I'm declaring against.

```lean path=ProofRefinement/Lemma54/Candidates/V13.lean
/-
  Candidates/V13.lean — pull every declared numerical literal down to the
  exact certified value its oracle returns, dropping `Cr_val` from V12's
  `9/100` to `3/250` (a 7.5× reduction).

  -- @parent Candidates/V12.lean

  No structural change: V13 uses the same sink delegation as V11/V12,
  `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, with the same
  `Cr_phi_uzz` formula

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi².

  The only change is that each `*_val` literal is now the exact rational
  the corresponding oracle certifies, instead of a rounded-up ceiling:

    slot               V12 literal        oracle-certified   V13 literal
    -----------------  -----------------  -----------------  -----------------
    M_phi_val          239/5000 = .0478   61/2500  = .0244   61/2500
    M_phi_prime_val    543/10000 = .0543  59/2000  = .0295   59/2000
    inv_F_p_z_val      9/5 = 1.8          3407/2000 = 1.7035 3407/2000
    M_pp_tight_val     12                 61373/10000        61373/10000

  Each oracle re-verifies `declared ≥ recomputed`, and here `declared =
  recomputed` exactly, so every check remains satisfied with equality.

  Resulting arithmetic (exact rationals):

    term1 = (61/2500)·(59/2000)·(3407/2000)²
          = 41775928751 / 20000000000000
          ≈ 2.08880·10⁻³

    term2 = (1/2)·(61373/10000)·(3407/2000)³·(61/2500)²
          ≈ 9.03140·10⁻³

    Cr_phi_uzz ≈ 1.112020·10⁻²  ≤  3/250 = 1.2·10⁻²   (margin ≈ 8.8·10⁻⁴)

  Trust base is byte-identical to V12:
    - 3 Lean primitives.
    - 9 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family,
      as reported by the V12 audit).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (seed).
    - `Braverman.PaperV0.h_M_oracle` (declared for parity; not on the
      `_phi_uzz` proof path).
    - `Braverman.PaperV0.h_M_phi_oracle`
    - `Braverman.PaperV0.h_M_phi_prime_oracle`
    - `Braverman.PaperV0.h_inv_F_p_z_oracle`
    - `Braverman.PaperV0.h_M_pp_tight_oracle`

  No `Numerical_Library/` or `lemma.toml` edits: the four live oracle
  functions are untouched, so the values they return (and therefore the
  literals declared above) are exactly those the V12 audit printed.

  Fixed parameters (from SearchConfig): `eta = 1/100`, `r = 23/25`.
-/
import ProofRefinement.Lemma54.Proof.SearchConfig
import ProofRefinement.Lemma54.Proof.Lib.Lemma54_Paper_Main
import LeanProof.Defs.Strip
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex Set Metric

noncomputable section

namespace Braverman.PaperV0

/-! ## Section 1: Numerical witnesses (each at its certified value) -/

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the
oracle rectangle. Carried over byte-identical from V10–V12 for parity;
the `_phi_uzz` wrapper does not consume it on its proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter for the Rouché-certified oracle rectangle. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the Rouché-certified oracle rectangle. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
Set to `61/2500 = 0.0244`, the *exact* rational returned by
`Numerical_Library.compute_M_phi_bound` (V12 declared the looser
`239/5000 = 0.0478`). -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle rectangle.
Set to `59/2000 = 0.0295`, the *exact* rational returned by
`Numerical_Library.compute_M_phi_prime_bound` (V12 declared the looser
`543/10000 = 0.0543`). -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `3407/2000 = 1.7035`, the
*exact* rational returned by `Numerical_Library.compute_inv_F_p_z_bound`
(V12 declared the looser `9/5 = 1.8`). -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. Set to `61373/10000 = 6.1373`, the
*exact* rational returned by the tightened M_pp oracle registered in
`lemma.toml` (V12 declared the looser integer `12`). -/
def M_pp_tight_val : ℝ := 61373 / 10000

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

/-! ## Section 2: Score (literal rational `Cr_val = 3/250`) -/

/-- `Cr_val := 3/250 = 0.012`, dominating the literal rational

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (61/2500)·(59/2000)·(3407/2000)²
          + (1/2)·(61373/10000)·(3407/2000)³·(61/2500)²
      ≈ 0.00208880 + 0.00903140
      ≈ 0.01112020.

Margin to `Cr_val = 3/250 = 0.012` is ≈ 8.8·10⁻⁴. The closing step is
exact rational arithmetic (`norm_num`), so the margin only has to be
positive. -/
def Cr_val : ℝ := 3 / 250

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V12) -/

/-- The Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed; identical statement
                  shapes to V12, with tightened right-hand sides) -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Seed axiom. -/
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

/-- Certified single-`M` sup-norm bound on the oracle rectangle.
Declared for parity with V9–V12; the `_phi_uzz` wrapper does not consume
it, so it does not appear in the sink's transitive axiom set. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_bound`, which
certifies `61/2500` — matched here exactly. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'` over the oracle rectangle.
Runner-witnessed by `Numerical_Library.compute_M_phi_prime_bound`, which
certifies `59/2000` — matched here exactly. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖`.
Runner-witnessed by `Numerical_Library.compute_inv_F_p_z_bound`, which
certifies `3407/2000` — matched here exactly. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖`.
Runner-witnessed by the tightened M_pp oracle registered in `lemma.toml`,
which certifies `61373/10000` — matched here exactly. -/
axiom h_M_pp_tight_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_tight_val

/-! ## Section 5: The candidate sink -/

/-- **The candidate's sink theorem.** Identical shape and delegation to
V11/V12: `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, threading
the four η-aware oracles. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (3/250) * p^2` by exact rational
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
  -- Monotonicity: `Cr_phi_uzz … ≤ Cr_val`, by exact rational arithmetic.
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    unfold Braverman.Paper.Cr_phi_uzz Cr_val M_phi_val M_phi_prime_val
           inv_F_p_z_val M_pp_tight_val
    -- LHS = (61/2500)·(59/2000)·(3407/2000)²
    --       + (1/2)·(61373/10000)·(3407/2000)³·(61/2500)²
    --     ≈ 0.00208880 + 0.00903140 ≈ 0.01112020 ≤ 0.012 = 3/250.
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

Deliberately no `Numerical_Library/` or `lemma.toml` edits this turn: the four oracle functions that produced the printed values must stay byte-identical for my declared literals to be exactly the certified ones.

Where this leaves the target: `3/250 = 1.2·10⁻²` is still ~77× above the `1/6400 ≈ 1.5625·10⁻⁴` bar, and the product-of-sups structure cannot close that gap — the certified sub-sups floor `Cr_phi_uzz` near `1.1·10⁻²`. The remaining slack is that `M_phi`, `M_phi_prime`, `inv_F_p_z`, `M_pp` are each maximized at *different* points of Ω: `1/‖D‖` peaks at the corner `(1-δ)+iB` (where `‖∂²_z F_p‖ ≈ 0.37`), while `‖∂²_z F_p‖` peaks at the real edge `w = 1-δ` (where `1/‖D‖ ≈ 0.55`). Since `u'' = 2Φ'Φ/D² − DD·Φ²/D³` is a single analytic function of `w`, a composite oracle on `sup_{∂Ω}|u''|` should beat the product bound by roughly an order of magnitude. That is the next piece: a `u2_composite` oracle plus the matching `Cr_composite` lemma chain.