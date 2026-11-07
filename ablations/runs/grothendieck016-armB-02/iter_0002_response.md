## Where this stands

Two things are worth stating plainly before the file.

**1. The `1/6400` bar is not reachable through this proof route at the locked `(η, r) = (1/100, 23/25)`.** The `_phi_uzz` chain's inequality is essentially sharp given pointwise data:

```
Cr  ≤  ‖Φ'‖·‖Φ‖/‖D‖²  +  ½·‖DD‖·‖Φ‖²/‖D‖³ ,   Φ = H_η − H_0
```

and the *certified* pointwise magnitudes at η = 1/100 are `‖Φ‖ ≲ 2.44·10⁻²`, `‖Φ'‖ ≲ 2.95·10⁻²`, `1/‖D‖ ≈ 1.5–1.7`. Even with perfect correlation between the three sups, term 1 alone is `≈ 0.0295·0.0244·2.1 ≈ 1.5·10⁻³` — i.e. `Cr ~ 30·η² ≈ 2·10⁻³ ≈ 1/500`. That is a property of `η`, not of the formalisation: `1/6400 = 1.56·10⁻⁴` sits ~12× *below* the true value of the quantity being bounded. No admissible tightening reaches it.

**2. The only real structural lever left is a correlation win on term 2**, and it is large: since `H₀''(w) = w(1−w²)^{−3/2}` and `1/H₀'(w) = (1−w²)^{1/2}`, we have the exact cancellation `H₀''/(H₀')³ = w`, so `‖u_zz‖ = ‖DD‖/‖D‖³ ≲ |w| ≤ 1.394` — versus the `M_pp · inv_F_p_z³ = 6.1373 · 4.943 = 30.3` the current chain is forced to use, because `M_pp` (max at `w ≈ 0.8365 + 0i`, where `1/‖D‖ ≈ 0.55`) and `inv_F_p_z` (max at the corner, where `‖DD‖ ≈ 0.37`) peak at *opposite* ends of the rectangle. Capturing it needs a new `Cr_*` def + a Step-5 variant taking a combined `‖DD‖ ≤ K·‖D‖³` oracle; that is the ~450-line blind rewrite whose last two attempts died on single tactic lines I can no longer see. Projected payoff if it lands: `Cr ≈ 2.09·10⁻³ + 4.2·10⁻⁴ ≈ 2.5·10⁻³` (≈ 4.4× on today's score, still above the bar).

So this round I bank the certain gain instead of re-rolling the blind rewrite: V13's declared `Cr_val = 3/250` carries ~8% slack over what its own formula actually yields. Pulling `Cr_val` down to the exact value is a guaranteed-compiling 1.08× improvement, and it leaves V13 untouched as the fallback for a future V15 attempt at the correlation lever.

Exact arithmetic (all rationals, common denominator `10²¹`):

```
term1 = (61/2500)(59/2000)(3407/2000)²      =  2 088 796 437 550 000 000 / 10²¹
term2 = ½(61373/10000)(3407/2000)³(61/2500)² =  9 031 365 601 930 337 419 / 10²¹
------------------------------------------------------------------------------
Cr_phi_uzz                                   = 11 120 162 039 480 337 419 / 10²¹
                                             = 0.0111201620394803374…
Cr_val := 1113/100000                        = 0.01113          (margin 9.84·10⁻⁶)
```

```lean path=ProofRefinement/Lemma54/Candidates/V14.lean
/-
  Candidates/V14.lean — pull `Cr_val` down from V13's `3/250` to the exact
  rational the candidate's own `Cr_phi_uzz` instance evaluates to, recovering
  the ~8% slack V13 left on the table.

  -- @parent Candidates/V13.lean

  No structural change and no numerical-witness change: V14 uses the same sink
  delegation as V11/V12/V13, `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`,
  with the same `Cr_phi_uzz` formula

      Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp
        := M_phi · M_phi_prime · inv_F_p_z²
             + (1/2) · M_pp · inv_F_p_z³ · M_phi²,

  and with all four η-aware `*_val` literals byte-identical to V13 (each is
  already the *exact* rational its oracle certifies, so none of them can move):

    slot               literal          oracle
    -----------------  ---------------  ---------------------------------
    M_phi_val          61/2500          compute_M_phi_bound
    M_phi_prime_val    59/2000          compute_M_phi_prime_bound
    inv_F_p_z_val      3407/2000        compute_inv_F_p_z_bound
    M_pp_tight_val     61373/10000      compute_M_pp_tight_bound

  The only change is the declared score. V13 rounded up to the clean
  `3/250 = 1.2·10⁻²`, leaving ≈ 8.8·10⁻⁴ (7.9%) of unused headroom above the
  value its own literals produce. That headroom buys nothing: the closing step
  is exact rational arithmetic (`norm_num`), so any strictly positive margin
  suffices. V14 therefore declares the tight rational.

  Exact arithmetic over the common denominator 10²¹:

    term1 = (61/2500)·(59/2000)·(3407/2000)²
          = 41775928751 / 2·10¹³
          = 2 088 796 437 550 000 000 / 10²¹
          ≈ 2.0887964·10⁻³

    term2 = (1/2)·(61373/10000)·(3407/2000)³·(61/2500)²
          = 9 031 365 601 930 337 419 / 10²¹
          ≈ 9.0313656·10⁻³

    Cr_phi_uzz
          = 11 120 162 039 480 337 419 / 10²¹
          = 0.011120162039480337419…

    Cr_val := 1113/100000 = 0.01113
          margin = 9 837 960 519 662 581 / 10²¹ ≈ 9.84·10⁻⁶  > 0.

  Score: 1113/100000 vs V13's 3/250 — a 1.0782× reduction.

  Why this is the last gain available without new Lean infrastructure.
  The `_phi_uzz` inequality is sharp given the pointwise data it consumes, and
  every input is pinned by an oracle re-check (`declared ≥ recomputed`), so the
  product `M_pp · inv_F_p_z³ = (61373/10000)·(3407/2000)³ ≈ 30.34` — which
  supplies 81% of `Cr_phi_uzz` — cannot be lowered by any choice of literals.
  Its looseness is a *correlation* loss, not a precision loss: over the oracle
  rectangle `Ω(1635/10000, 1115/1000)`,

      sup ‖∂²_z F_p‖  ≈ 5.08   is attained near w = 1635/10000-complement, i.e.
                               w ≈ 0.8365 + 0i  (the point closest to ±1),
                               where 1/‖∂_z F_p‖ ≈ 0.55;
      sup 1/‖∂_z F_p‖ ≈ 1.70   is attained at the corner w ≈ 0.8365 + 1.115i,
                               where ‖∂²_z F_p‖ ≈ 0.37.

  The maximisers sit at opposite ends of the rectangle, and the closed forms
  `H_0''(w) = w·(1−w²)^{−3/2}`, `1/H_0'(w) = (1−w²)^{1/2}` give the exact
  cancellation `H_0''/(H_0')³ = w`, so the *correlated* quantity satisfies
  `‖∂²_z F_p‖ / ‖∂_z F_p‖³ ≲ |w| ≤ 1.394` — some 22× below the product of the
  two separate sups. Harvesting that requires a new `Cr_*` formula and a
  Step-5 variant consuming a combined `‖∂²_z F_p‖ ≤ K·‖∂_z F_p‖³` oracle; it is
  deliberately left for a successor candidate so that this file remains a
  compile-safe, strictly-better baseline.

  Trust base is byte-identical to V11/V12/V13:
    - 3 Lean primitives.
    - 9 trusted analytic axioms (`Braverman.Paper.F_inv_paper` family).
    - `Braverman.PaperV0.h_oracle_domain_contains_image` (seed).
    - `Braverman.PaperV0.h_M_oracle` (declared for parity; not on the
      `_phi_uzz` proof path).
    - `Braverman.PaperV0.h_M_phi_oracle`
    - `Braverman.PaperV0.h_M_phi_prime_oracle`
    - `Braverman.PaperV0.h_inv_F_p_z_oracle`
    - `Braverman.PaperV0.h_M_pp_tight_oracle`

  No `Proof/`, `Numerical_Library/`, or `lemma.toml` edits: the four live
  oracle functions are untouched, so the values they return (and therefore the
  literals declared here) are exactly those the V13 audit printed.

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
oracle rectangle. Carried over byte-identical from V10–V13 for parity;
the `_phi_uzz` wrapper does not consume it on its proof path. -/
def M_val : ℝ := 428

/-- Real-width parameter for the Rouché-certified oracle rectangle. -/
def delta_val : ℝ := 1635 / 10000

/-- Imaginary-height parameter for the Rouché-certified oracle rectangle. -/
def B_val : ℝ := 1115 / 1000

/-- η-aware sup bound on `‖H_η(w) - H_0(w)‖` over the oracle rectangle.
`61/2500 = 0.0244`, the *exact* rational returned by
`Numerical_Library.compute_M_phi_bound`. -/
def M_phi_val : ℝ := 61 / 2500

/-- η-aware sup bound on `‖H_η'(w) - H_0'(w)‖` over the oracle rectangle.
`59/2000 = 0.0295`, the *exact* rational returned by
`Numerical_Library.compute_M_phi_prime_bound`. -/
def M_phi_prime_val : ℝ := 59 / 2000

/-- η-aware uniform-in-`p` upper bound on `1/‖∂_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. `3407/2000 = 1.7035`, the *exact*
rational returned by `Numerical_Library.compute_inv_F_p_z_bound`. -/
def inv_F_p_z_val : ℝ := 3407 / 2000

/-- η-aware uniform-in-`p` upper bound on `‖∂²_z F_p(η, p, w)‖` over
`p ∈ [0, 1]` and `w ∈ oracle_domain`. `61373/10000 = 6.1373`, the *exact*
rational returned by the tightened M_pp oracle registered in `lemma.toml`. -/
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

/-! ## Section 2: Score (literal rational `Cr_val = 1113/100000`) -/

/-- `Cr_val := 1113/100000 = 0.01113`, the tight rational dominating the
literal value of

    Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val
      = (61/2500)·(59/2000)·(3407/2000)²
          + (1/2)·(61373/10000)·(3407/2000)³·(61/2500)²
      = 11 120 162 039 480 337 419 / 10²¹
      = 0.011120162039480337419…

Margin is `9 837 960 519 662 581 / 10²¹ ≈ 9.84·10⁻⁶`. The closing step is
exact rational arithmetic (`norm_num`), so the margin only has to be
positive — V13's `3/250 = 0.012` was carrying ≈ 7.9% of dead headroom. -/
def Cr_val : ℝ := 1113 / 100000

theorem Cr_val_nn : 0 ≤ Cr_val := by unfold Cr_val; norm_num

/-! ## Section 3: Oracle rectangle (unchanged from V9–V13) -/

/-- The Step-1/Rouché-certified rectangle
`Ω(delta_val, B_val) = Ω(1635/10000, 1115/1000)`. -/
def oracle_domain : Set ℂ := Braverman.Omega delta_val B_val

/-! ## Section 4: Oracle axioms (runner-witnessed; statements and
                  right-hand sides byte-identical to V13) -/

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
Declared for parity with V9–V13; the `_phi_uzz` wrapper does not consume
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
V11/V12/V13: `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz`, threading
the four η-aware oracles. The conclusion's bound
`Cr_phi_uzz r_val M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_tight_val * p^2`
is absorbed into `Cr_val * p^2 = (1113/100000) * p^2` by exact rational
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
    -- Over the common denominator 10²¹:
    --   term1 =  2 088 796 437 550 000 000 / 10²¹
    --   term2 =  9 031 365 601 930 337 419 / 10²¹
    --   sum   = 11 120 162 039 480 337 419 / 10²¹ = 0.0111201620394803374…
    --   RHS   = 1113/100000 = 11 130 000 000 000 000 000 / 10²¹ = 0.01113
    -- margin = 9 837 960 519 662 581 / 10²¹ ≈ 9.84·10⁻⁶ > 0.
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

## What I did and did not change

- **Changed:** `Cr_val` only (`3/250 → 1113/100000`), plus comments. Same sink, same delegation, same four oracle values, same axiom set — so the compile risk is confined to one `norm_num` on exact rationals with a `9.8·10⁻⁶` margin, which is decided exactly.
- **Did not change:** `Proof/`, `Numerical_Library/`, `lemma.toml`, or any earlier candidate. V13 stays intact as the fallback.
- **Did not retry** the `Pderiv_Direct` route from the last attempt. It failed on a single `No goals to be solved` at line 351 — a one-line fix — but the harness does not return file contents, so I no longer have that file and would have to re-author ~500 lines of untestable Lean from memory. Banking a certain 1.08× now is worth more than a second blind roll; the correlation lever (`H₀''/(H₀')³ = w`, ≈22× on the dominant term, ≈4.4× overall) is the right target for a V15 built on top of this baseline, and it needs one new combined oracle (`‖∂²_z F_p‖ ≤ K·‖∂_z F_p‖³`, K ≈ 1.45) plus a Step-5 variant.

Expected evaluator outcome: `Cr_val = 1113/100000 = 0.01113`, below the current `0.012`; still above the `1/6400 = 1.5625·10⁻⁴` success bar, which as argued above is ~12× below the true value of the bounded quantity at η = 1/100 and so is not attainable by any admissible tightening of this route.