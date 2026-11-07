"""Sprint 012 Planner — verify the Cr_refined win at V8 params.

Question: with proposal_001 oracles approved (M_phi, M_phi_prime, M_pp),
what literal Cr_val do we get from `Cr_refined` instantiated at the
post-oracle smoke values, and what literal upper bound on Cr_refined
can the candidate use?

Cr_refined (r, M_diff, M_diffp, M_pp, R) :=
    M_diff * M_diffp * invFp² + (M_pp * M_diff² * invFp³) / 2,
where invFp = 2R/(1-r).

V8 params: r = 23/25, R ≤ 23/20, M_diff ≤ M_phi, M_diffp ≤ M_phi_prime,
M_pp ≤ M_pp_oracle.

From sprint_proposal_001_smoke.py at production-grade params (n_per_edge=512,
prec=200, K_max=80, on the V8 oracle rectangle Ω(1635/10000, 1115/1000)):
  M_phi       ≈ 0.0476  (rationalized 239/5000)
  M_phi_prime ≈ 0.0541  (rationalized 543/10000)
  M_pp        ≈ 56.31

Compute:
  invFp = 2 · (23/20) / (2/25) = 2 · 23/20 · 25/2 = 23·25/20 = 575/20 = 28.75
  invFp² = 826.5625
  invFp³ = 23763.671875
"""
from fractions import Fraction

# V8 parameters
r = Fraction(23, 25)
R = Fraction(23, 20)  # upper bound on R_val_paper(23/25) = sinh(49/50)
one_minus_r = 1 - r
invFp = 2 * R / one_minus_r
invFp_sq = invFp ** 2
invFp_cube = invFp ** 3

print(f"r = {r} = {float(r):.4f}")
print(f"R = {R} = {float(R):.4f}")
print(f"1-r = {one_minus_r}")
print(f"invFp = {invFp} = {float(invFp):.4f}")
print(f"invFp² = {invFp_sq} = {float(invFp_sq):.4f}")
print(f"invFp³ = {invFp_cube} = {float(invFp_cube):.4f}")
print()

# Smoke test outputs (already certified by the production oracle).
# Use rationalized upper bounds with safety margins.
# From smoke test:
#   M_phi ≈ 0.0476       -> safe rational upper bound: 239/5000 = 0.0478
#   M_phi_prime ≈ 0.0541 -> safe rational upper bound: 543/10000 = 0.0543
#   M_pp ≈ 56.31         -> safe rational upper bound: 113/2 = 56.5

# Conservative integer-friendly upper bounds for the candidate:
M_phi_val = Fraction(239, 5000)   # ≥ M_phi smoke output
M_phi_prime_val = Fraction(543, 10000)  # ≥ M_phi_prime smoke output
M_pp_val = Fraction(57, 1)        # ≥ M_pp smoke output

print(f"Candidate-side declarations (rational upper bounds on smoke values):")
print(f"  M_phi_val = {M_phi_val} ≈ {float(M_phi_val):.4f}")
print(f"  M_phi_prime_val = {M_phi_prime_val} ≈ {float(M_phi_prime_val):.4f}")
print(f"  M_pp_val = {M_pp_val} = {float(M_pp_val):.4f}")
print()

# Compute Cr_refined exactly
term1 = M_phi_prime_val * M_phi_val * invFp_sq
term2 = M_pp_val * M_phi_val ** 2 * invFp_cube / 2
Cr_refined_exact = term1 + term2
Cr_refined_2x = 2 * Cr_refined_exact  # because Step 5's bound is 2 * Cr_refined; Lagrange's 1/2! kills the factor 2

print(f"Cr_refined arithmetic (full):")
print(f"  term1 = M_phi_prime * M_phi * invFp²")
print(f"        = {M_phi_prime_val} * {M_phi_val} * {invFp_sq}")
print(f"        = {term1} ≈ {float(term1):.4f}")
print()
print(f"  term2 = (1/2) * M_pp * M_phi² * invFp³")
print(f"        = (1/2) * {M_pp_val} * {M_phi_val**2} * {invFp_cube}")
print(f"        = {term2} ≈ {float(term2):.4f}")
print()
print(f"  Cr_refined = term1 + term2 = {Cr_refined_exact} ≈ {float(Cr_refined_exact):.4f}")
print()

# Round to a clean rational that exceeds Cr_refined_exact.
# The sink theorem closes via `Cr_refined ≤ Cr_val`.
# Pick a small integer ≥ Cr_refined_exact.

import math
Cr_val_int = math.ceil(float(Cr_refined_exact)) + 1
print(f"Suggested literal Cr_val (integer ceiling + safety): {Cr_val_int}")
print()

# V8 score: 1132310000
V8_Cr = 1132310000
print(f"V8 Cr_val: {V8_Cr}")
print(f"Win factor: {V8_Cr} / {Cr_val_int} ≈ {V8_Cr / Cr_val_int:.2e}×")
print()

# Check: what does the proposal_001 status log say about M_pp NOT helping?
# Compare to Cr_refined_with_Cauchy_step (i.e. ‖u_zz‖ bounded by 8R/(1-r)² instead of M_pp · invFp³):
Cr_via_Cauchy = M_phi_prime_val * M_phi_val * invFp_sq + (8 * R / one_minus_r**2) * M_phi_val**2 / 2
print(f"For comparison, Cr via Cauchy step (replacing only M_phi/M_phi_prime, leaving 8R/(1-r)² Cauchy):")
print(f"  Cr_via_Cauchy = M_phi_prime * M_phi * invFp² + (1/2) * (8R/(1-r)²) * M_phi²")
print(f"                = {Cr_via_Cauchy} ≈ {float(Cr_via_Cauchy):.4f}")
print()
print(f"  ratio Cr_refined / Cr_via_Cauchy = {float(Cr_refined_exact / Cr_via_Cauchy):.4f}×")
print()

# Decision: which is smaller?
if Cr_refined_exact < Cr_via_Cauchy:
    print("RESULT: Cr_refined (full M_pp path) is SMALLER → use the full refined formula.")
else:
    print("RESULT: Cr_via_Cauchy is SMALLER → keep Cauchy step for u_zz.")
    print("        Implementation: a 'hybrid' Cr_refined that retains the Cauchy step")
    print("        (`8R/(1-r)²`) for `‖u_zz‖`, replacing M·M with M_phi·M_phi_prime")
    print("        and M_phi² in the second term. This is what proposal_001's status")
    print("        log recommends.")
print()

# Hybrid path: define a "Cr_hybrid" that mirrors Cr_refined but uses Cauchy for u_zz.
# Cr_hybrid := M_diff * M_diffp * invFp² + (1/2) * (8R/(1-r)²) * M_diff²
#            = M_phi_prime * M_phi * invFp² + (4R/(1-r)²) * M_phi²
Cr_hybrid = M_phi_prime_val * M_phi_val * invFp_sq + (4 * R / one_minus_r**2) * M_phi_val**2
Cr_hybrid_int = math.ceil(float(Cr_hybrid)) + 1
print(f"Hybrid Cr (M_phi+M_phi_prime oracles + retained Cauchy on u_zz):")
print(f"  Cr_hybrid = {Cr_hybrid} ≈ {float(Cr_hybrid):.4f}")
print(f"  Suggested int Cr_val: {Cr_hybrid_int}")
print(f"  Win vs V8: {V8_Cr / Cr_hybrid_int:.2e}×")
