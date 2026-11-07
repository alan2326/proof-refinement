"""Sprint 009 arithmetic verification.

Computes the Cr_min, Cr_val margins for M_val=428, R=23/20.
"""

from fractions import Fraction

M = Fraction(428)
R = Fraction(23, 20)
R_p1 = R + 1  # = 43/20
one_minus_r = Fraction(2, 25)  # 1 - 23/25 = 2/25

# Cr_min = 16 * M^2 * R * (R+1) / (1-r)^2
Cr_min = 16 * M * M * R * R_p1 / (one_minus_r ** 2)
print(f"Cr_min       = {Cr_min} = {float(Cr_min)}")

Cr_val = Fraction(1132310000)
print(f"Cr_val       = {Cr_val} = {float(Cr_val)}")
print(f"Cr_val >= Cr_min? {Cr_val >= Cr_min} (diff = {float(Cr_val - Cr_min)})")

# nlinarith margin: Cr_val * (2/25)^2 - 16*M^2*R*(R+1)
LHS_max = 16 * M * M * R * R_p1  # 16 * 183184 * 989/400 = ?
RHS = Cr_val * (one_minus_r ** 2)
margin = RHS - LHS_max
print(f"LHS_max      = {LHS_max} = {float(LHS_max)}")
print(f"RHS          = {RHS} = {float(RHS)}")
print(f"margin       = {margin} = {float(margin)}")

# And quick check: 1132310000 = clean multiple of 10^4 above Cr_min
import math
ceil_to_10000 = math.ceil(float(Cr_min) / 10000) * 10000
print(f"ceil(Cr_min/10000)*10000 = {ceil_to_10000}")

# Verify against contract claim: Cr_min stated as 1132306100
print(f"Cr_min (round)= {round(float(Cr_min))}")
