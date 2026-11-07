"""
Sprint 011 arithmetic check: verify that Cr_refined at various M_pp values
either beats or loses to Cr_tight, under different M_diff/M_diffp choices.

Cr_tight  = 16 M² R(R+1) / (1-r)²
Cr_refined = M_diff · M_diffp · invFp² + M_pp · M_diff² · invFp³ / 2
           where invFp = 2R/(1-r)
"""
from fractions import Fraction

M_val = 428
M = Fraction(M_val)
R = Fraction(23, 20)         # R_rat upper bound on R_val_paper r
one_minus_r = Fraction(2, 25)
invFp = 2 * R / one_minus_r  # = 23/20 * 25 = 575/20 = 28.75

Cr_tight = Fraction(16) * M**2 * R * (R + 1) / one_minus_r**2
print(f"Cr_tight = {Cr_tight} ≈ {float(Cr_tight):.4e}")
print(f"invFp = {invFp} = {float(invFp)}")

print()
print("=== Scenario A: M_diff = M_diffp = 2M (triangle), M_pp varies ===")
for M_pp_val in [0, 1, 10, 100, 1000, 10000]:
    M_diff = 2 * M
    M_diffp = 2 * M
    M_pp = Fraction(M_pp_val)
    Cr_refined = M_diff * M_diffp * invFp**2 + M_pp * M_diff**2 * invFp**3 / 2
    ratio = Cr_refined / Cr_tight
    print(f"  M_pp = {M_pp_val:>6}: Cr_refined = {float(Cr_refined):.4e}, ratio_to_Cr_tight = {float(ratio):.4f}")

print()
print("=== Scenario B: η-aware M_diff = M_diffp = 2η·M ≈ 8.56, M_pp varies ===")
# H_eta - H_0 ≈ η · ψ where ψ is some bounded function. At η = 0.01 and on our rect,
# |H_eta - H_0| ~ η · max|ψ| ≈ 0.01 · 100 = 1 (very roughly). Conservatively ~η · 2M = 8.56.
for M_pp_val in [0, 1, 10, 100, 1000]:
    M_diff = Fraction(857, 100)  # ≈ 2 · η · M_val = 0.02 · 428 = 8.56
    M_diffp = Fraction(857, 100)
    M_pp = Fraction(M_pp_val)
    Cr_refined = M_diff * M_diffp * invFp**2 + M_pp * M_diff**2 * invFp**3 / 2
    ratio = Cr_refined / Cr_tight
    print(f"  M_pp = {M_pp_val:>6}: Cr_refined = {float(Cr_refined):.4e}, ratio_to_Cr_tight = {float(ratio):.4f}")

print()
print("=== Threshold: at M_diff = M_diffp = 2M, what M_pp keeps Cr_refined < Cr_tight? ===")
# Cr_refined < Cr_tight
# 4M² · invFp² + M_pp · 4 M² · invFp³ / 2 < 16 M² R(R+1)/(1-r)²
# 4M² invFp² (1 + M_pp · invFp / 2) < 16 M² R(R+1)/(1-r)²
# (1 + M_pp · invFp/2) < 4 R(R+1)/((1-r)² · invFp²)
#                     = 4 R(R+1) / ((1-r)² · 4R²/(1-r)²) = (R+1)/R
# So: M_pp · invFp / 2 < (R+1)/R - 1 = 1/R
# M_pp < 2/(R · invFp) = 2/(R · 2R/(1-r)) = (1-r)/R²
threshold = (one_minus_r) / (R**2)
print(f"  M_pp threshold = (1-r)/R² = {threshold} ≈ {float(threshold):.6f}")

# At M_diff = η-aware, threshold is much higher:
# Cr_refined < Cr_tight
# M_diff² invFp² (1 + M_pp · invFp/2) < 16 M² R(R+1)/(1-r)²
# At M_diff = 8.56 vs 2M = 856, M_diff²/M² = (8.56/856)² = 0.0001 = 10⁻⁴.
# So the LHS is 10⁻⁴ smaller, and the threshold M_pp is correspondingly larger:
# ~ 10⁴ · (1-r)/R² ≈ 10⁴ · 0.0605 ≈ 605.
M_diff_eta = Fraction(857, 100)
threshold_eta = (Cr_tight - M_diff_eta**2 * invFp**2) * 2 / (M_diff_eta**2 * invFp**3)
print(f"  M_pp threshold @ η-aware M_diff = 8.57: {float(threshold_eta):.4f}")

print()
print("=== CONCLUSION ===")
print("With M_diff = M_diffp = 2M (triangle): M_pp must be < 0.06 to win, infeasible.")
print("With η-aware M_diff (proposal_001's full ask): M_pp can be up to ~600 and still win.")
print("Therefore: proposal_002's single-oracle M_pp scope DOES NOT WIN.")
print("Only proposal_001 (full three-oracle) gives a real Cr_val reduction.")
