/-
  Candidates/V12.lean — replace the triangle-split `M_pp` oracle with a
  difference-decomposition oracle, and tighten `inv_F_p_z_val` from 2 to
  7/4, dropping `Cr_val` from V11's `1` to `1/10` (a 10× reduction).

  -- @parent Candidates/V11.lean

  ## What changes vs V11

  V11's score is dominated by the second chunk of

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        = M_phi · M_phi_prime · inv_F_p_z²
            + (1/2) · M_pp · inv_F_p_z³ · M_phi²,

  namely `(1/2) · M_pp · inv_F_p_z³ · M_phi² ≈ 0.5126` out of `≈ 0.5230`
  (98%). Both factors of that chunk are attacked here.

  ### (a) A tighter `M_pp` (the 8×-loose factor)

  `M_pp` bounds `‖iteratedDeriv 2 (F_p η p) w‖` on the oracle rectangle,
  uniformly in `p ∈ Ioo 0 pr_paper` (and `pr_paper ≤ 1` by the seed axiom
  `pr_paper_le_one`). Since

      iteratedDeriv 2 (F_p η p) w = (1 - p) · H_0''(w) + p · H_η''(w)

  (proved in `Lemma54_Paper_Pderiv.lean` as `iteratedDeriv_2_F_p_eq`), the
  registered `compute_M_pp_bound` splits this by the *triangle*
  inequality,

      ‖DD‖ ≤ sup_Ω ‖H_0''‖ + sup_Ω ‖H_η''‖,

  and obtains the second summand by Cauchy on `H_η'` over a δ/4
  enlargement of `Ω`: `sup‖H_η'‖ / (δ/4) ≈ 2.08 / 0.0409 ≈ 51`. That
  single term is what makes `M_pp ≈ 56.08`.

  The *difference* decomposition is far better:

      (1 - p) H_0'' + p H_η'' = H_0'' + p · (H_η'' - H_0''),

  so for `p ≤ 1`,

      ‖DD‖ ≤ sup_Ω ‖H_0''‖ + sup_Ω ‖H_η'' - H_0''‖
           ≤ sup_Ω ‖H_0''‖ + (sup_{Ω_d} ‖H_η' - H_0'‖) / d,

  the last step being Cauchy's estimate for the analytic function
  `Φ' = H_η' - H_0'` on the `d`-neighbourhood `Ω_d` of `Ω` (for `w ∈ Ω`
  the closed `d`-disc about `w` lies in `Ω_d`, and `d < δ` keeps `Ω_d`
  inside the strip `S`). The point is that `Φ'` is `O(η²)` — the
  certified `sup_Ω ‖Φ'‖ ≈ 0.054` at `η = 1/100`, versus `‖H_η'‖ ≈ 2` —
  so the Cauchy summand shrinks by ≈ 40×.

  Numerically: `sup_Ω ‖H_0''‖ = sup |w| / |1 - w²|^{3/2}` is attained on
  the vertical edge at `w = (1 - δ) + 0i`, giving ≈ 5.09 (the horizontal
  edges contribute ≤ 0.73, since there `|1 - w²| ≥ 1.54`), and Lemma 4.2's
  growth bound (43) shows `H_η` grows only polynomially in `|Im w|`, so
  `sup_{Ω_d} ‖Φ'‖` stays within a small factor of `sup_Ω ‖Φ'‖`. That puts
  the certified `M_pp` in the 6–8 range; `M_pp_tight_val := 15` is
  declared with ≥ 2× margin. The backing oracle
  `Numerical_Library.compute_M_pp_tight_bound` takes the *minimum* over
  two enlargements `d ∈ {δ/4, δ/2}`, so the reported bound is robust to
  how fast `Φ'` grows off `Ω`.

  ### (b) A tighter `inv_F_p_z`

  `compute_inv_F_p_z_bound` certifies `sup 1/‖∂_z F_p‖` via
  `inf‖H_0'‖ - p_max · sup‖H_η' - H_0'‖ ≈ 0.643 - 0.054 = 0.589`, i.e. a
  bound `≈ 1.7035` (rationalised `≈ 1.7053`). V10/V11 declared the
  integer ceiling `2`; `7/4 = 1.75` retains ≈ 3% headroom and cuts
  `inv_F_p_z³` from `8` to `343/64 = 5.359375` (a further 1.49× off the
  dominant chunk) and `inv_F_p_z²` from `4` to `49/16`.

  ### Resulting score

      term1 = (239/5000)·(543/10000)·(7/4)²      =   6359073/800000000
      term2 = (1/2)·15·(7/4)³·(239/5000)²        = 293887545/3200000000
      Cr_phi_uzz                                 = 319323837/3200000000
                                                 ≈ 0.0997887

  so `Cr_val := 1/10` closes with margin `≈ 2.1·10⁻⁴` under exact
  rational arithmetic (`norm_num`), a 10× reduction from V11's `1`.

  ## Trust base (V11's seven oracles, one retargeted)

    - 3 Lean primitives.
    - 11 trusted analytic axioms (the `Braverman.Paper.F_inv_paper`
      family — unchanged).
    - `h_oracle_domain_contains_image` — unchanged, byte-identical: the
      oracle rectangle `Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`
      is exactly V9/V10/V11's, and `delta_val`, `B_val`, `r`, `eta` are
      untouched.
    - `h_M_phi_oracle`, `h_M_phi_prime_oracle` — unchanged (proposal_001).
    - `h_inv_F_p_z_oracle` — unchanged statement, tighter declared bound
      (`7/4` in place of `2`); the same certified oracle re-verifies it.
    - `h_M_pp_tight_oracle` (NEW statement-shape-identical sibling of
      `h_M_pp_oracle`) — same sup-norm claim on the same rectangle,
      certified by `compute_M_pp_tight_bound` at `M_pp_tight_val = 15`.

  `M_val` / `h_M_oracle` and `M_pp_val` / `h_M_pp_oracle` are retained
  verbatim from V11 (unused on the sink's proof path, exactly as
  `h_M_oracle` already was in V9–V11) so that every `[[oracles]]` row in
  `lemma.toml` continues to resolve against a declared constant that its
  oracle certifies.

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
Carried over from V9–V11 byte-identical; not consumed on the sink's proof
path (the `_phi_uzz` wrapper is η-aware), but kept so the audit/log
surface and the `h_M_oracle` oracle row are unchanged. -/
def M_val : ℝ := 428

/-- Real-width parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the tight Rouché-certified oracle
rectangle. Unchanged from V9–V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`239/5000 = 0.0478`, the rational ceiling of the certified
`compute_M_phi_bound ≈ 0.0476`. Unchanged from V9–V11. -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle
rectangle. `543/10000 = 0.0543`, the rational ceiling of the certified
`compute_M_phi_prime_bound ≈ 0.0541`. Unchanged from V9–V11. -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. **Tightened from V11's `2` to
`7/4 = 1.75`.**

`compute_inv_F_p_z_bound` certifies this by

    inf‖∂_z F_p‖ ≥ inf‖H_0'‖ − p_max · sup‖H_η' − H_0'‖
                 ≈ 0.6428 − 0.0541 = 0.5887,

hence `sup 1/‖∂_z F_p‖ ≤ 1.7035`, rationalised to `≈ 1.7053` by
`arb_to_rational_ub`'s safety inflation. `7/4` dominates that with ≈ 3%
headroom, and cuts `inv_F_p_z³` from `8` to `343/64 = 5.359375`. -/
def inv_F_p_z_val : ℝ := 7 / 4

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` via the
*triangle* split (V11's value; `5608/100 = 56.08` dominates the certified
`compute_M_pp_bound = 35048/625 ≈ 56.077`). Retained verbatim so the
`h_M_pp_oracle` row still resolves; superseded on the sink's proof path
by `M_pp_tight_val`. -/
def M_pp_val : ℝ := 5608 / 100

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` via the
*difference* decomposition — the load-bearing new constant.

    ‖(1-p) H_0'' + p H_η''‖ = ‖H_0'' + p (H_η'' - H_0'')‖
        ≤ sup_Ω ‖H_0''‖ + p_max · (sup_{Ω_d} ‖H_η' - H_0'‖) / d

with `p_max = 1` (`pr_paper ≤ 1`) and `d ∈ {δ/4, δ/2}`, the last step
being Cauchy's estimate for `Φ' = H_η' - H_0'` on the `d`-neighbourhood
`Ω_d` of `Ω` (legitimate because `d < δ` keeps `Ω_d ⊆ S`). Certified by
`Numerical_Library.compute_M_pp_tight_bound`, which returns the minimum
over the two enlargements.

Numerically `sup_Ω ‖H_0''‖ = sup |w|/|1-w²|^{3/2} ≈ 5.09` (attained at
`w = (1-δ) + 0i`; the horizontal edges give `≤ 0.73`) and the Cauchy
summand is `≈ 0.054·g/d ≈ 1–3` for the modest off-`Ω` growth factor `g`
implied by Lemma 4.2's polynomial-in-`|Im|` bound (43) — so the certified
value sits near 6–8, and `15` is declared with ≥ 2× margin. Against V11's
`56.08` this is an ≈ 3.7× cut on the dominant `Cr_phi_uzz` chunk. -/
def M_pp_tight_val : ℝ := 15

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

/-! ## Section 2: Score (literal rational `Cr_val = 1/10`) -/

/-- `Cr_val := 1/10`, dominating the literal rational

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (239/5000)·(543/10000)·(7/4)² + (1/2)·15·(7/4)³·(239/5000)²
      =   6359073/800000000 + 293887545/3200000000
      = 319323837/3200000000
      ≈ 0.0997887,

leaving margin `≈ 2.1·10⁻⁴` under exact rational arithmetic. Ten times
smaller than V11's `Cr_val = 1`. -/
def Cr_val : ℝ := 1 / 10

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V11)

`Cr_phi_uzz` has no `R` dependence, so V11's
`R_val_paper_le_twentythree_twentieths` helper — which V11 itself
documented as unused at the candidate level — is dropped here. -/

/-- The tight Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. Identical to
V9/V10/V11: the oracle rectangle is *not* shrunk. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

/-- Certified containment: for every `q` below the IFT-package threshold
`pr_paper`, `F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`. Byte-identical to
V9/V10/V11 — the trust surface's assertion is unchanged. -/
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
over from V9–V11 for parity; not consumed by the `_phi_uzz` wrapper. -/
axiom h_M_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H0 w‖ ≤ M_val ∧
      ‖Braverman.H_eta Braverman.SearchConfig.eta w‖ ≤ M_val ∧
      ‖deriv Braverman.H0 w‖ ≤ M_val ∧
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w‖ ≤ M_val

/-- η-aware sup-norm bound on `H_η - H_0`. Runner-witnessed by
`Numerical_Library.compute_M_phi_bound` (proposal_001). Unchanged. -/
axiom h_M_phi_oracle :
    ∀ w ∈ oracle_domain,
      ‖Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w‖
        ≤ M_phi_val

/-- η-aware sup-norm bound on `H_η' - H_0'`. Runner-witnessed by
`Numerical_Library.compute_M_phi_prime_bound` (proposal_001). Unchanged. -/
axiom h_M_phi_prime_oracle :
    ∀ w ∈ oracle_domain,
      ‖deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
          - deriv Braverman.H0 w‖
        ≤ M_phi_prime_val

/-- η-aware uniform-in-`p` bound `1 ≤ ‖∂_z F_p(η, p, w)‖ · inv_F_p_z_val`.
Statement unchanged from V10/V11; only the declared constant tightens
(`2 → 7/4`). Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound`, which certifies `≈ 1.7035`
(rationalised `≈ 1.7053`) — comfortably below `7/4`. The Python oracle
certifies for `p ∈ [0, 1]`, which subsumes `Ioo 0 pr_paper` via the seed
axiom `pr_paper_le_one`. -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- V11's triangle-split `‖∂²_z F_p‖` bound. Retained verbatim (unused on
this candidate's proof path) so the `h_M_pp_oracle` row keeps resolving
against a declared constant its oracle certifies. -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-- **The load-bearing new oracle axiom.** Same sup-norm claim, same
rectangle, same `p`-range as `h_M_pp_oracle` — only the declared constant
is smaller, because the backing computation uses the difference
decomposition rather than the triangle split:

    ‖(1-p) H_0''(w) + p H_η''(w)‖
        ≤ sup_Ω ‖H_0''‖ + p_max · (sup_{Ω_d} ‖H_η' - H_0'‖) / d,

with `p_max = 1` (from `pr_paper_le_one`) and `Ω_d` the `d`-enlargement
of `Ω` for `d ∈ {δ/4, δ/2}` (both `< δ`, so `Ω_d ⊆ S`). Runner-witnessed
by `Numerical_Library.compute_M_pp_tight_bound`, which returns the
minimum over the two enlargements; the certified value sits near 6–8,
against the declared `M_pp_tight_val = 15`. -/
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
`inv_F_p_z_val = 7/4` and the new `h_M_pp_tight_oracle` at
`M_pp_tight_val = 15` in place of `h_M_pp_oracle` at `56.08`. The
conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is then absorbed into `Cr_val * p^2 = (1/10) * p^2` by the monotonicity
step below, which is exact rational arithmetic on the literal constants
(`Cr_phi_uzz = 319323837/3200000000 ≈ 0.0997887 ≤ 1/10`). -/
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
  -- Monotonicity step: literal rational arithmetic.
  --   term1 = (239/5000)·(543/10000)·(7/4)²  =   6359073/800000000
  --   term2 = (1/2)·15·(7/4)³·(239/5000)²    = 293887545/3200000000
  --   sum                                     = 319323837/3200000000
  --                                           ≈ 0.0997887 ≤ 1/10
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
