Re-emitting `V12.lean` complete in a single block (the previous one was cut mid-file, so that partial text must be ignored — this is the file to write). Comments trimmed to keep it whole.

```lean path=ProofRefinement/Lemma54/Candidates/V12.lean
/-
  Candidates/V12.lean — two independent tightenings of V11's `Cr_phi_uzz`
  sink, dropping `Cr_val` from `1` to `11/100` (a 9.1× reduction).

  -- @parent Candidates/V11.lean

  (1) `inv_F_p_z_val : 2 → 9/5`.  The existing arb oracle
      `compute_inv_F_p_z_bound` certifies `sup_{p,w} 1/‖∂_z F_p‖ ≈ 1.7035`
      (rationalised ≈ 1.7054); V10/V11 rounded up to the integer `2`,
      leaving ≈ 15 % slack in a quantity entering `Cr_phi_uzz` quadratically
      (term 1) and cubically (term 2).  `9/5 = 1.8` keeps a ≈ 5.5 % cushion
      over the certified value while recovering 1.23× on term 1 and 1.37× on
      term 2.

  (2) `M_pp : 5608/100 ≈ 56.08 → 14`, via a new oracle
      `h_M_pp_tight_oracle` that certifies *the same* sup-norm sub-claim as
      `h_M_pp_oracle` on *the same* rectangle `Ω(delta_val, B_val)`, through
      a tighter numerical route (≈ 8× smaller constant).

  Mathematical content of (2).  `Cr_phi_uzz`'s dominant chunk is
  `(1/2) · M_pp · inv_F_p_z³ · M_phi²`, coming from the aux-z-identity bound
  `‖u_zz‖ ≤ M_pp · inv_F_p_z³` with
  `M_pp ≥ sup_{p ∈ [0,1], w ∈ Ω} ‖∂²_z F_p(η, p, w)‖`.  The existing
  `compute_M_pp_bound` splits by the triangle inequality and Cauchy-bounds
  `sup‖H_η''‖ ≤ sup_{Ω(3δ/4, B+δ/4)}‖H_η'‖ / (δ/4) ≈ 2/0.041 ≈ 51`, giving
  ≈ 56.08 — nearly all slack, since `‖u_zz‖ ≈ 1.4` in truth (at `p = 0`,
  `H_0''/(H_0')³ = w`).  But `F_p` is a convex combination, so with
  `Φ := H_η − H_0`,

      (1 − p) H_0'' + p H_η''  =  H_0'' + p · Φ'',

  hence for `p ∈ [0,1]`

      ‖∂²_z F_p(w)‖ ≤ sup_Ω‖H_0''‖ + sup_{Ω(3δ/4, B+δ/4)}‖Φ'‖ / (δ/4).

  The Cauchy step now acts on the η-small difference `Φ'` (certified ≈ 0.054
  on `Ω` by `compute_M_phi_prime_bound`, ≈ 40× smaller than `H_η'`), so the
  second summand collapses from ≈ 51 to ≈ 2 and `M_pp_tight ≈ 5.08 + 2 ≈ 7`.
  `M_pp_tight_val := 14` is declared with a ≈ 2× cushion.  Same shape of
  claim as every other oracle here (a sup-norm bound on an explicit quantity
  over the explicit, unchanged rectangle): a tighter certificate for an
  existing claim, no new analytic content.

  Score:
    Cr_phi_uzz r M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (239/5000)·(543/10000)·(9/5)² + (1/2)·14·(9/5)³·(239/5000)²
      = 10511937/1250000000 + 291488463/3125000000
      = 0.0084096 + 0.0932763 = 0.1016859  ≤  11/100 = Cr_val.

  Trust base: V11's, with one oracle row substituted.  3 Lean primitives;
  11 trusted analytic axioms (the `Braverman.Paper.F_inv_paper` family);
  `h_oracle_domain_contains_image` on the SAME rectangle
  `Ω(1635/10000, 1115/1000)` (not shrunk, meaning untouched);
  `h_M_phi_oracle`, `h_M_phi_prime_oracle` (proposal_001, unchanged);
  `h_inv_F_p_z_oracle` (unchanged statement, tighter declared constant);
  `h_M_pp_tight_oracle` (new numerical backing for V11's `h_M_pp_oracle`
  claim).  `h_M_oracle` and `h_M_pp_oracle` remain declared byte-identical
  to V11 for witness-surface parity; they are simply off this proof path.

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

/-- Single-`M` sup bound on `{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the oracle
rectangle.  Carried over from V10/V11 byte-identical for parity; not on this
candidate's proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter of the Rouché-certified oracle rectangle.
Unchanged from V9/V10/V11. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter of the Rouché-certified oracle rectangle.
Unchanged from V9/V10/V11. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle;
exactly the rational returned by `compute_M_phi_bound` (ball ≈ 0.0476). -/
def M_phi_val : ℝ := 239 / 5000

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle rectangle;
exactly the rational returned by `compute_M_phi_prime_bound` (≈ 0.0541). -/
def M_phi_prime_val : ℝ := 543 / 10000

/-- Uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over `p ∈ [0, 1]`,
`w ∈ oracle_domain`.  Tightened from V10/V11's `2` to `9/5 = 1.8`; the
pipeline certifies `inf‖∂_z F_p‖ ≥ 0.6427 − 0.0541 = 0.5886`, i.e.
`sup 1/‖∂_z F_p‖ ≤ 1.7035` (rationalised ≈ 1.7054). -/
def inv_F_p_z_val : ℝ := 9 / 5

/-- Uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` from the LOOSE
`compute_M_pp_bound` (≈ 56.077).  Declared for parity with V11; superseded
here by `M_pp_tight_val`. -/
def M_pp_val : ℝ := 5608 / 100

/-- Uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` — the SAME quantity
as `M_pp_val` — certified through the tighter `Φ'`-Cauchy route of
`Numerical_Library/m_pp_tight.py`:
`sup_Ω‖H_0''‖ + sup_{Ω(3δ/4, B+δ/4)}‖Φ'‖/(δ/4) ≈ 5.08 + 2 ≈ 7`. -/
def M_pp_tight_val : ℝ := 14

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

/-- `Cr_val := 11/100`, dominating the literal rational
`Cr_phi_uzz r M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
= 0.0084096 + 0.0932763 = 0.1016859` (margin ≈ 0.0083).  A 9.1× reduction
over V11's `Cr_val = 1`. -/
def Cr_val : ℝ := 11 / 100

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9/V10/V11) -/

/-- The Rouché-certified rectangle `Ω(1635/10000, 1115/1000)`, identical to
V9–V11: this candidate neither shrinks nor otherwise weakens it. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms -/

/-- Certified containment: for every `q` below the IFT threshold `pr_paper`,
`F_inv_paper q (disk r) ⊆ Ω(δ_val, B_val)`.  Byte-identical to V9/V10/V11. -/
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

/-- Certified single-`M` sup-norm bound on the oracle rectangle.  Declared
for parity with V10/V11; not consumed by this candidate's proof. -/
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

/-- η-aware uniform-in-`p` bound on `1/‖∂_z F_p(η, p, w)‖`, stated
multiplicatively.  Statement byte-identical to V10/V11; only the declared
constant tightens (`2 → 9/5`).  Runner-witnessed by
`Numerical_Library.compute_inv_F_p_z_bound` (certified ≈ 1.7035). -/
axiom h_inv_F_p_z_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        1 ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖
              * inv_F_p_z_val

/-- η-aware uniform-in-`p` bound on `‖∂²_z F_p(η, p, w)‖` from the loose
`compute_M_pp_bound` route (≈ 56.077).  Declared for parity with V11; not
consumed by this candidate's proof. -/
axiom h_M_pp_oracle :
    ∀ p ∈ Set.Ioo (0 : ℝ)
        (Braverman.Paper.pr_paper
          Braverman.SearchConfig.eta Braverman.SearchConfig.r
          Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w‖
          ≤ M_pp_val

/-- η-aware uniform-in-`p` bound on `‖∂²_z F_p(η, p, w)‖` over the oracle
rectangle — the same sup-norm sub-claim as `h_M_pp_oracle`, on the same
rectangle, with the tighter certified constant produced by
`Numerical_Library.compute_M_pp_tight_bound`:

    sup_Ω ‖∂²_z F_p‖ ≤ sup_Ω ‖H_0''‖ + sup_{Ω(3δ/4, B+δ/4)} ‖Φ'‖ / (δ/4)

(the convexity identity `(1−p)H_0'' + pH_η'' = H_0'' + p·Φ''` lets the
Cauchy enlargement act on the η-small `Φ' = H_η' − H_0'` rather than on
`H_η'`), which evaluates to ≈ 7 versus ≈ 56.08 for the `H_η'` route. -/
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
delegating to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` with the
tightened `inv_F_p_z_val = 9/5` and the tighter `M_pp_tight_val = 14`.  The
conclusion's `Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val
M_pp_tight_val * p^2` is absorbed into `Cr_val * p^2 = (11/100) * p^2` by
literal rational arithmetic. -/
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
  have h_Cr_le :
      Braverman.Paper.Cr_phi_uzz Braverman.SearchConfig.r M_phi_val
          M_phi_prime_val inv_F_p_z_val M_pp_tight_val
        ≤ Cr_val := by
    -- LHS = (239/5000)·(543/10000)·(9/5)² + (1/2)·14·(9/5)³·(239/5000)²
    --     = 10511937/1250000000 + 291488463/3125000000
    --     = 0.0084096 + 0.0932763 = 0.1016859 ≤ 11/100.
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

That completes the bundle. The four files to write are: `Candidates/V12.lean` (above, complete), `Numerical_Library/m_pp_tight.py`, `Numerical_Library/__init__.py`, `lemma.toml` (all three emitted earlier in this response and unchanged).

Summary of what this attempt claims, stated plainly:

- **Accepted-path risk.** The sink is V11's proof verbatim except for two numerals and one substituted oracle argument, so the Lean risk is confined to a single `norm_num` on literal rationals (`0.1016859 ≤ 0.11`, verified by hand twice above). The new Python module is a mechanical splice of the already-passing `m_pp.py` (the `H_0''` scan, the `d = δ/4` enlargement, the `certified_positive` guard, the arb→JSON round-trip) and `m_phi_prime.py` (the `Φ'` integrand), with a fresh `cached_run` key (`fn = "compute_M_pp_tight_bound"`) so no stale cached value from `m_pp.py` can be read back.
- **Result if accepted.** `Cr_val = 11/100`, versus the workspace's current `1` — a 9.1× improvement, recorded as progress.
- **The success bar is not met, and I do not think it is reachable here.** With Ω frozen (shrinking it is the stated trust violation), the certified inputs are `‖H_η−H_0‖ ≈ 0.0476`, `‖H_η'−H_0'‖ ≈ 0.0541`, `1/‖∂_zF_p‖ ≈ 1.70`, and the Lagrange-remainder shape forces `Cr ≥ ‖Φ‖‖Φ'‖/‖D‖² + ½‖u_zz‖‖Φ‖² ≈ 0.0067` even with a *perfect* `‖u_zz‖ ≈ 1.4` — roughly 43× above `1/6400`. Closing that gap needs a different remainder argument (or an `η`-aware bound on the actual `∂²_p F_inv` cancellation), not a tighter constant in this chain.
- **Two declared constants carry numerical risk I could not test:** `inv_F_p_z_val = 9/5` must dominate the recomputed ≈ 1.7054 (cushion ≈ 5.5 %), and `M_pp_tight_val = 14` must dominate `sup_Ω‖H_0''‖ + sup_outer‖Φ'‖/(δ/4)`, which I estimate at ≈ 7 — the declaration tolerates `sup_outer‖Φ'‖` up to ≈ 0.36, i.e. a 6.7× blow-up over its value on Ω. If either estimate is wrong the oracle gate rejects the candidate and this attempt scores nothing; that is the deliberate trade I took over the risk-free alternative (`inv_F_p_z = 9/5`, existing `M_pp = 56.08`, `Cr_val = 2/5`, only 2.5× progress).