"""Sprint 015 planner experiment v2: u_zz oracle using existing inv_F_p_z and
M_pp oracles (the latter approved via proposal_001 and present in lemma.toml
but unused in V10).

Aux z-identity: DD·h² + D·u_zz = 0 → u_zz = -DD/D³, so
    ‖u_zz‖ ≤ ‖DD‖ / ‖D‖³ ≤ M_pp · inv_F_p_z³

where M_pp ≥ sup_w ‖∂²_z F_p(η, p, w)‖ uniformly in p, and inv_F_p_z ≥
sup_w 1/‖∂_z F_p‖ uniformly in p. Both already exist as approved oracles
(proposal_001 + sprint_014).

This means we can derive a u_zz bound in pure Lean (using existing
infrastructure) WITHOUT needing a NEW oracle. The bound is just:
    ‖u_zz‖ ≤ M_pp · inv_F_p_z³

V10 has inv_F_p_z_val = 2 (certified ≈ 1.7035) and M_pp can be re-obtained
from the existing m_pp.py at the V10 rectangle.

We need: what is M_pp at V10's rectangle (δ=1635/10000, B=1115/1000)?
The previous sprint_011 figure of 56 was at a different rectangle.

This planner script computes the relevant arithmetic ONLY (assuming smoke-
test M_pp values). The Generator will call compute_M_pp_bound to get the
exact certified value.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

import mpmath as mp

mp.mp.dps = 50

# V10 parameters.
delta = mp.mpf("1635") / mp.mpf("10000")
B = mp.mpf("1115") / mp.mpf("1000")
r = mp.mpf("23") / mp.mpf("25")
M_phi_val = mp.mpf("239") / mp.mpf("5000")
M_phi_prime_val = mp.mpf("543") / mp.mpf("10000")
inv_F_p_z_val = mp.mpf(2)

R_val = mp.sinh(mp.mpf(24)/mp.mpf(25))

print(f"V10 params: r={r}, δ={delta}, B={B}")
print(f"  inv_F_p_z_val = {inv_F_p_z_val}")
print(f"  M_phi_val = {M_phi_val}, M_phi_prime_val = {M_phi_prime_val}")
print(f"  R_val_paper(r) ≈ {R_val}")
print()

# === The numerical heart of the matter ===
# We re-bound u_zz via: ‖u_zz‖ ≤ M_pp · inv_F_p_z³.
# The Cauchy paper bound is ‖u_zz‖ ≤ 8R/(1-r)².
# For the new bound to be useful, we need M_pp · inv_F_p_z³ < 8R/(1-r)².

paper_uzz_bound = 8 * R_val / (1 - r) ** 2
print(f"Paper Cauchy bound: ‖u_zz‖ ≤ 8R/(1-r)² = {paper_uzz_bound}")

# Try a few candidate M_pp values to see what M_pp threshold the new
# approach beats the paper bound at.
print()
print("=== Threshold M_pp for new bound to win ===")
print(f"  M_pp · inv_F_p_z³ < 8R/(1-r)² requires M_pp < {paper_uzz_bound / inv_F_p_z_val**3}")
print(f"  i.e. M_pp < {float(paper_uzz_bound / inv_F_p_z_val**3):.4f}")
print()

# Smoke estimate: M_pp at V10 rectangle. The closed-form sup ‖H_0''‖
# on Ω(δ,B) at corner (1-δ) + iB.
print("Direct sup ‖H_0''‖ on Ω at corner (1-δ) + iB...")
w_corner = mp.mpc(1 - delta, B)
val_corner = w_corner / (1 - w_corner**2) ** mp.mpf("1.5")
print(f"  H_0''((1-δ)+iB) = {val_corner}")
print(f"  |H_0''((1-δ)+iB)| = {abs(val_corner)}")

# Scan boundary
def sup_on_boundary(f, n=2000):
    re_lo, re_hi = -(1-delta), +(1-delta)
    im_lo, im_hi = -B, +B
    M = mp.mpf(0)
    # Top + bottom edges
    for k in range(n+1):
        u = re_lo + (re_hi - re_lo) * k / n
        for v in (im_lo, im_hi):
            w = mp.mpc(u, v)
            try:
                vmag = abs(f(w))
                if vmag > M:
                    M = vmag
            except Exception:
                pass
    # Left + right edges
    for k in range(n+1):
        v = im_lo + (im_hi - im_lo) * k / n
        for u in (re_lo, re_hi):
            w = mp.mpc(u, v)
            try:
                vmag = abs(f(w))
                if vmag > M:
                    M = vmag
            except Exception:
                pass
    return M

def H0_pp(w):
    return w / (1 - w*w) ** mp.mpf("1.5")

print("\nScanning ∂Ω for sup ‖H_0''‖ at n=2000...")
sup_H0_pp = sup_on_boundary(H0_pp, n=2000)
print(f"  sup ‖H_0''‖ on ∂Ω ≈ {sup_H0_pp}")

# H_eta'' is bounded via Cauchy on enlarged rectangle (matching m_pp.py):
# sup ‖H_eta''‖ ≤ sup ‖H_eta'‖_outer / d, where d = δ/4 and outer = (3δ/4, B+d).
# Heuristic: at η = 1/100, sup ‖H_eta'‖ ≈ sup ‖H_0'‖ + M_phi_prime (≈ corner-attained).
# Use the same closed-form for H_0' on the enlarged rectangle.

d_outer = delta / 4
delta_inner = 3 * delta / 4   # |Re w| < 1 - delta_inner = 1 - 3δ/4
B_outer = B + d_outer

# At enlarged rectangle, sup ‖H_0'‖ at corner (1 - 3δ/4) + i(B+d).
w_corner_outer = mp.mpc(1 - delta_inner, B_outer)
H0p_outer_corner = abs(1 / mp.sqrt(1 - w_corner_outer**2))
print(f"  Enlarged rectangle: |Re w| < {1-delta_inner}, |Im w| < {B_outer}")
print(f"  |H_0'| at outer corner ≈ {H0p_outer_corner}")

# Add M_phi_prime upper bound on |H_eta' - H_0'| (the same M_phi_prime works
# but only on Ω, not on enlarged. For the heuristic, assume it's similar
# magnitude on enlarged ≤ ~0.06):
sup_H_eta_p_outer = H0p_outer_corner + mp.mpf("0.06")
sup_H_eta_pp = sup_H_eta_p_outer / d_outer
print(f"  sup ‖H_eta''‖ ≤ {sup_H_eta_p_outer} / {d_outer} = {sup_H_eta_pp}")

# Now sup ‖DD‖ over (η fixed, p ∈ [0,1], w ∈ Ω):
# DD = (1-p)·H_0'' + p·H_eta'' so sup ‖DD‖ ≤ max(sup‖H_0''‖, sup‖H_eta''‖)
# (convex combination)
# Wait: for general p ∈ [0,1], sup over p of |(1-p)·a + p·b| = max(|a|,|b|)
# pointwise, then sup over w. Conservative: sup_w max(‖H_0''‖, ‖H_eta''‖)
# ≤ max(sup‖H_0''‖, sup‖H_eta''‖).
#
# Actually the M_pp oracle in m_pp.py uses sup‖H_0''‖ + sup‖H_eta''‖
# (a TRIANGLE bound — overestimates for convex combos but matches our
# cleanest path).
M_pp_oracle_estimate = sup_H0_pp + sup_H_eta_pp  # matches m_pp.py path
print(f"  M_pp (oracle path: triangle) ≈ {M_pp_oracle_estimate}")

# Better: we could mint a Cauchy-on-enlarged-rectangle bound directly on DD,
# avoiding the triangle inequality split. That's the same machinery, just
# applied to (1-p)·H_0' + p·H_eta' on the outer rectangle. The result is
# that sup_w |D(η, p, w)| on enlarged is ≤ sup_w |H_0'| + p·M_phi_prime ≈
# the same bound as for H_eta' alone (within η correction). Then
# sup ‖DD‖ ≤ that / d_outer ≈ sup_H_eta_pp ≈ 39 (a 50% reduction over the
# triangle bound).

print()
print("=== Cr_phi_uzz = M_phi · M_phi_prime · inv_F_p_z² + (1/2)·u_zz_bound · M_phi² ===")
# Lagrange /2 on second term: paper has 8R/(1-r)² and the formula is /2; new bound has u_zz_bound and /2.
term1 = M_phi_val * M_phi_prime_val * inv_F_p_z_val ** 2
print(f"  term1 = M_phi · M_phi_prime · inv_F_p_z² = {term1}")

for label, M_pp_used in [
    ("triangle (m_pp.py path)", M_pp_oracle_estimate),
    ("Cauchy-on-DD (cleanest)", sup_H_eta_pp),  # ~39
    ("optimistic (≈ paper-bound /50)", paper_uzz_bound / 50),
]:
    u_zz_bound = M_pp_used * inv_F_p_z_val ** 3
    term2 = mp.mpf("0.5") * u_zz_bound * M_phi_val ** 2
    total = term1 + term2
    print(f"  M_pp = {float(M_pp_used):.2f}: u_zz_bound = {float(u_zz_bound):.2f}, "
          f"term2 = {float(term2):.4f}, total Cr ≈ {float(total):.4f}")

# Alternative: avoid the triangle entirely. Note:
# 4R/(1-r)² · M_phi² (CURRENT, paper Cauchy on F_inv directly with R)
#   = 1.591
# Compare against:
#   M_pp · inv_F_p_z³ · M_phi² / 2  (proposed)
print()
print("=== Bottom line ===")
M_pp_realistic = mp.mpf(56)  # from sprint_011 docs (approximate)
u_zz_via_oracle = M_pp_realistic * inv_F_p_z_val ** 3
term2_old = mp.mpf(4) * R_val / (1 - r) ** 2 * M_phi_val ** 2
term2_new = mp.mpf("0.5") * u_zz_via_oracle * M_phi_val ** 2
print(f"  At M_pp = 56, inv_F_p_z = 2:")
print(f"    u_zz ≤ M_pp · inv_F_p_z³ = 56 · 8 = 448")
print(f"    term2_new = (1/2) · 448 · (239/5000)² = {term2_new}")
print(f"    term2_old = (4R/(1-r)²) · M_phi² = {term2_old}")
print(f"    Ratio: {term2_old / term2_new}  (>1 means new is better)")
print(f"    Cr_phi_uzz total ≈ term1 ({term1}) + term2_new ({term2_new}) = {term1 + term2_new}")

# What if we tighten M_pp (e.g., direct Cauchy on F_ww = (1-p)H_0'' + p·H_eta''
# uniformly, or compute closed-form sup more carefully)?
# Actually the closed-form sup of |H_0''| on Ω is large (≈ 5+) per our scan.
# Adding the H_eta'' Cauchy enlargement gives the triangle 56 figure.
#
# Suppose we get a tighter M_pp by using DIRECT Cauchy on F_ww (not split).
# This would give M_pp ≈ sup |D| / d_outer where sup |D| ≈ inf|H_0'| level
# on outer rectangle ≈ 1.55, and d_outer = δ/4 = 0.04. So M_pp ≈ 1.55/0.04 = 38.7.
# Then u_zz ≤ 38.7 · 8 = 310. Term2 ≈ 0.5·310·0.00229 = 0.354. Total ≈ 0.36.
# Cr_val ≤ 1 still feasible.
