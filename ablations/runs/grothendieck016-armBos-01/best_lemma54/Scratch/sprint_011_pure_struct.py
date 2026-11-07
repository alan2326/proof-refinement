"""
Sprint 011 planner exploration: can we use Cr_refined with the *existing*
M oracle alone (no new axioms/oracles), bounding M_diff and M_diffp via
the triangle inequality M_diff ≤ 2M, M_diffp ≤ 2M, and M_pp via Cauchy
+ existing M?

Cr_refined formula (from Lemma54_Paper.lean:431):
    Cr_refined r M_diff M_diffp M_pp R
       = M_diff · M_diffp · invFp²  +  M_pp · M_diff² · invFp³ / 2
    where invFp = 2R/(1-r).

Substitute M_diff = 2M, M_diffp = 2M, plus M_pp bound to investigate:

What's M_pp = sup ‖∂²_p F‖? F(η, p, w) = (1-p) H_0(w) + p H_η(w), so
∂_p F = H_η(w) - H_0(w), ∂²_p F = 0.   So M_pp = 0!!

Wait. F is LINEAR in p:
    F_p η p w = (1 - p) H_0(w) + p H_η(w)
    ∂_p F_p = -H_0(w) + H_η(w) = (H_η - H_0)(w)
    ∂²_p F_p = 0.

So at our F (which is genuinely linear in p), M_pp = 0 EXACTLY. No oracle
needed!

Then Cr_refined becomes:
    Cr_refined = M_diff · M_diffp · invFp² + 0
               = M_diff · M_diffp · invFp²

With M_diff ≤ 2M, M_diffp ≤ 2M (triangle):
    ≤ 4 M² · invFp²

invFp = 2R/(1-r), so invFp² = 4 R² / (1-r)²:
    ≤ 4 M² · 4 R² / (1-r)² = 16 M² R² / (1-r)²

Compare to current Cr_tight = 16 M² R (R+1) / (1-r)².

Cr_refined / Cr_tight = R / (R+1).

At R = sinh(49/50) ≈ 1.144 (or rationally 23/20 = 1.15):
    R/(R+1) ≈ 1.15/2.15 ≈ 0.5349

So Cr_refined (with M_diff = 2M, M_diffp = 2M, M_pp = 0) ≈ 0.5349 · Cr_tight.

At V8's Cr_val = 1132310000, the projected new value is:
    ~ 1132310000 · 23/(20+23) · ... let me compute exactly with R = 23/20.
"""

# The exact arithmetic at our parameters:
M = 428
R_num, R_den = 23, 20
one_minus_r_num, one_minus_r_den = 2, 25  # (1-r) = 2/25 since r = 23/25

# Cr_tight = 16 M² R (R+1) / (1-r)²
# At R = 23/20, (R+1) = 43/20, R(R+1) = 989/400.
# (1-r)² = 4/625.
# Cr_tight = 16 · 428² · (989/400) / (4/625) = 16 · 183184 · 989 · 625 / (400 · 4)
from fractions import Fraction
R = Fraction(R_num, R_den)
one_minus_r = Fraction(one_minus_r_num, one_minus_r_den)
M2 = M * M

Cr_tight = Fraction(16) * M2 * R * (R + 1) / (one_minus_r ** 2)
print(f"Cr_tight = {Cr_tight} = {float(Cr_tight):.6e}")

# Cr_refined with M_diff = 2M, M_diffp = 2M, M_pp = 0:
#   = 2M · 2M · invFp²  +  0  =  4 M² invFp²
# invFp = 2R/(1-r), invFp² = 4 R² / (1-r)².
invFp = 2 * R / one_minus_r
Cr_refined_via_triangle = Fraction(4) * M2 * invFp ** 2
print(f"Cr_refined (with M_diff = M_diffp = 2M, M_pp = 0) = {Cr_refined_via_triangle} = {float(Cr_refined_via_triangle):.6e}")

# Ratio:
ratio = Cr_refined_via_triangle / Cr_tight
print(f"Ratio (Cr_refined_triangle / Cr_tight) = {ratio} = {float(ratio):.6f}")

# Win: Cr_val could drop from 1132310000 to ⌈Cr_refined_via_triangle⌉:
import math
Cr_min_new = float(Cr_refined_via_triangle)
Cr_val_new_proposed = int(math.ceil(Cr_min_new / 10000)) * 10000
print(f"\nProposed new Cr_val (next 10⁴ multiple above Cr_refined_triangle) = {Cr_val_new_proposed}")
print(f"V8 baseline Cr_val = 1132310000")
print(f"Reduction: {1132310000 / Cr_val_new_proposed:.4f}× = {(1 - Cr_val_new_proposed/1132310000)*100:.2f}% off")

# Now: what does the *Lean side* require?
print("""
WIN ANALYSIS for sprint_011:
============================

Replace Cr_tight (= 16 M² R(R+1) / (1-r)²) by Cr_refined (= M_diff · M_diffp · invFp² + M_pp · M_diff² · invFp³ / 2)
in lemma_5_4_paper_on_domain (or a new variant lemma_5_4_paper_on_domain_refined),
INSTANTIATED with M_diff = 2M, M_diffp = 2M, M_pp = 0.

Mathematical content:
- M_pp = 0 EXACTLY because F(η, p, w) = (1-p) H_0(w) + p H_η(w) is LINEAR in p.
  So ∂²_p F ≡ 0 pointwise — no oracle needed; this is a Lean-provable algebraic fact.
- M_diff = ‖H_η - H_0‖ ≤ ‖H_η‖ + ‖H_0‖ ≤ M + M = 2M (triangle, no new axiom).
- M_diffp = ‖H_η' - H_0'‖ ≤ M + M = 2M (triangle, no new axiom).

Required Lean infrastructure:
- F_inv_p_second_deriv_bound (refined version) is ALREADY PROVED at
  Lemma54_Paper_Pderiv.lean:140 (line 140-167). Its conclusion is:
      ‖iteratedDeriv 2 (fun q => F_inv q z) p‖ ≤ 2 · Cr_refined r M_diff M_diffp M_pp (R_val_paper r)
  parametric in M_diff, M_diffp, M_pp.
- A "lemma_5_4_paper_on_domain_refined" variant in Lemma54_Paper_Main.lean that
  threads through F_inv_p_second_deriv_bound (refined) instead of
  F_inv_p_second_deriv_bound_tight, with hypotheses M_diff, M_diffp, M_pp
  set to (2M, 2M, 0) at the instantiation site.
- The sup bound `‖H_η(F_inv) - H_0(F_inv)‖ ≤ 2M` follows from the existing
  h_M_oracle (which already gives ‖H_0 w‖ ≤ M and ‖H_η w‖ ≤ M for w in the
  oracle domain) plus norm_sub_le.
- The sup bound on ‖∂²_p F_p‖ = 0 is a one-line algebraic identity:
  F_p η p w = (1-p) H_0 w + p H_η w is linear in p, so its second p-derivative
  is 0 identically.

Numerical impact:
- Cr_refined (with M_diff = 2M, M_diffp = 2M, M_pp = 0) at our params (M=428, R=23/20, 1-r=2/25):
  = 4 M² · (2R/(1-r))² = 4·183184·(2·1.15/0.08)² = 4·183184·(28.75)² ≈ 6.057·10⁸.
- Cr_val_new ≈ 6.06·10⁸, vs current 1.132·10⁹ — a 1.87× reduction.
- This is NOT the 12× of full Cr_refined (which uses η-aware oracles for
  M_diff, M_diffp), but it IS a structural-form replacement using ONLY existing infrastructure.

Trust base impact:
- No new axioms, no new oracles. Same audit count as V8 (3 Lean primitives + 11 trusted analytic + 2 oracle = 16).

Direction policy (Bulletin):
- Direction 1: "Replace the bound's structural form" — YES, this is a structural form
  replacement (Cr_tight → Cr_refined-with-trivial-M_pp).
- Mechanism: NOT a parameter-tweak; the formula itself changes from
  `16 M²R(R+1)/(1-r)²` to `4M²·(2R/(1-r))²` = `16 M²R²/(1-r)²` (drop the +1 factor in R+1).
- Rule satisfied: not in the forbidden parameter-tweak family.
""")
