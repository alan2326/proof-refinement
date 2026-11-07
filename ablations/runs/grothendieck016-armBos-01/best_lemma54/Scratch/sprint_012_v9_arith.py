"""Sprint 012: Verify Cr_phi arithmetic at V9 parameters.

We need Cr_phi(r_val, M_phi_val, M_phi_prime_val, R_val_paper(r_val)) <= 5.

Cr_phi(r, M_phi, M_phi_prime, R) :=
    M_phi * M_phi_prime * invFp^2 + (4*R/(1-r)^2) * M_phi^2,
where invFp = 2*R/(1-r).

Constants:
    r_val           = 23/25
    M_phi_val       = 239/5000   (oracle bound, dominates 0.0476)
    M_phi_prime_val = 543/10000  (oracle bound, dominates 0.0541)
    R_val_paper(r)  <= 23/20     (already proved as R_val_paper_le_twentythree_twentieths)

To make the upper bound tightest, we use R = 23/20.
"""
from fractions import Fraction


r = Fraction(23, 25)
M_phi = Fraction(239, 5000)
M_phi_prime = Fraction(543, 10000)
R = Fraction(23, 20)

one_minus_r = 1 - r
print(f"1 - r = {one_minus_r} = {float(one_minus_r)}")

invFp = 2 * R / one_minus_r
print(f"invFp = 2R/(1-r) = {invFp} = {float(invFp)}")

invFp_sq = invFp ** 2
print(f"invFp^2 = {invFp_sq} = {float(invFp_sq)}")

# Term 1: M_phi * M_phi_prime * invFp^2
term1 = M_phi * M_phi_prime * invFp_sq
print(f"term1 = M_phi * M_phi_prime * invFp^2 = {term1} = {float(term1)}")

# Term 2: (4*R/(1-r)^2) * M_phi^2
factor2 = 4 * R / (one_minus_r ** 2)
print(f"4*R/(1-r)^2 = {factor2} = {float(factor2)}")
term2 = factor2 * (M_phi ** 2)
print(f"term2 = (4R/(1-r)^2) * M_phi^2 = {term2} = {float(term2)}")

Cr_phi = term1 + term2
print(f"Cr_phi = term1 + term2 = {Cr_phi} = {float(Cr_phi)}")

# Cr_val = 5
Cr_val = 5
margin = Cr_val - Cr_phi
print(f"Cr_val - Cr_phi = {margin} = {float(margin)}")
print(f"  margin (positive means feasible): {float(margin)}")

# Also compute the equivalent inequality:
# Cr_phi <= Cr_val
# i.e. M_phi * M_phi_prime * (2R)^2 / (1-r)^2 + 4R * M_phi^2 / (1-r)^2 <= Cr_val
# Multiply both sides by (1-r)^2:
# 4R^2 * M_phi * M_phi_prime + 4R * M_phi^2 <= Cr_val * (1-r)^2
lhs = 4 * (R ** 2) * M_phi * M_phi_prime + 4 * R * (M_phi ** 2)
rhs = Cr_val * (one_minus_r ** 2)
print()
print(f"After multiplying by (1-r)^2:")
print(f"  LHS = 4R^2 M_phi M_phi_prime + 4R M_phi^2 = {lhs} = {float(lhs)}")
print(f"  RHS = Cr_val * (1-r)^2 = {rhs} = {float(rhs)}")
print(f"  RHS - LHS = {rhs - lhs} = {float(rhs - lhs)}")
