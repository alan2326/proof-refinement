"""Sprint 015 planner experiment: numerical sup of ‖u_zz(p,z)‖ via the
auxiliary z-identity, evaluated over (p, z) ∈ [0,1] × disk(r).

We have, from the aux z-identity DD·h² + D·u_zz = 0,
    u_zz = - DD · h² / D = - DD / D³
where
    D  = (1-p)·H_0'(F_inv(p,z)) + p·H_η'(F_inv(p,z))
    DD = iteratedDeriv 2 (F_p η p) (F_inv(p,z))
       = (1-p)·H_0''(F_inv(p,z)) + p·H_η''(F_inv(p,z))
    h  = ∂_z F_inv(p,z) = 1/D
and F_inv(p,z) ∈ Ω(δ,B) for z ∈ disk r (oracle_domain_contains_image).

So
    sup_{z ∈ disk r, p ∈ [0,1]} ‖u_zz‖
        = sup_{w ∈ image(F_inv) ⊆ Ω(δ,B), p ∈ [0,1]} ‖DD(η,p,w)‖ / ‖D(η,p,w)‖^3
        ≤ sup_{w ∈ Ω(δ,B), p ∈ [0,1]} ‖DD(η,p,w)‖ / ‖D(η,p,w)‖^3.

We bound this above by:
    sup_w ‖DD‖ / (inf_w ‖D‖)^3
  ≤ (sup_w ‖H_0''‖ + p_max · sup_w ‖H_η'' − H_0''‖) / (inf_w ‖H_0'‖ − p_max · M_phi_prime)^3

with p_max = 1.

H_0''(w) = w / (1-w²)^{3/2} (closed form). Sup of ‖H_0''‖ over Ω(δ,B):
  attained at the corner w = (1-δ) + iB.
H_0'(w) = (1-w²)^{-1/2}; inf ‖H_0'‖ also at the corner.

This script just sanity-checks the orders of magnitude. The Lean candidate
will use an arb-certified oracle.
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
p_max = mp.mpf("1")
M_phi_val = mp.mpf("239") / mp.mpf("5000")
M_phi_prime_val = mp.mpf("543") / mp.mpf("10000")

print(f"V10 params: r={r}, δ={delta}, B={B}")
print(f"Oracle rectangle Ω: |Re w| < {1-delta}, |Im w| < {B}")
print()

def H0(w):
    return mp.asin(w)

def H0_p(w):  # H_0'(w) = 1 / sqrt(1-w²)
    return 1 / mp.sqrt(1 - w*w)

def H0_pp(w):  # H_0''(w) = w / (1-w²)^{3/2}
    return w / (1 - w*w) ** mp.mpf("1.5")

# Sample on a 200x200 grid over Ω(δ,B).
def sup_on_rect(f_abs, n=400):
    re_lo = -(1 - delta)
    re_hi = +(1 - delta)
    im_lo = -B
    im_hi = +B
    M = mp.mpf(0)
    for i in range(n+1):
        for j in range(n+1):
            u = re_lo + (re_hi - re_lo) * mp.mpf(i) / n
            v = im_lo + (im_hi - im_lo) * mp.mpf(j) / n
            w = mp.mpc(u, v)
            try:
                val = abs(f_abs(w))
                if val > M:
                    M = val
            except Exception:
                pass
    return M

def inf_on_rect(f_abs, n=400):
    re_lo = -(1 - delta)
    re_hi = +(1 - delta)
    im_lo = -B
    im_hi = +B
    m = mp.mpf("inf")
    for i in range(n+1):
        for j in range(n+1):
            u = re_lo + (re_hi - re_lo) * mp.mpf(i) / n
            v = im_lo + (im_hi - im_lo) * mp.mpf(j) / n
            w = mp.mpc(u, v)
            try:
                val = abs(f_abs(w))
                if val < m:
                    m = val
            except Exception:
                pass
    return m

# Coarse grid first.
print("Computing inf |H_0'| on Ω (coarse, n=80)...")
inf_H0p = inf_on_rect(H0_p, n=80)
print(f"  inf |H_0'| ≈ {inf_H0p}")

print("Computing sup |H_0''| on Ω (coarse, n=80)...")
sup_H0pp = sup_on_rect(H0_pp, n=80)
print(f"  sup |H_0''| ≈ {sup_H0pp}")

# Estimate inf |D| ≥ inf|H_0'| - p_max · M_phi_prime
inf_D_lb = inf_H0p - p_max * M_phi_prime_val
print(f"  inf |D| ≥ {inf_D_lb}")

# Estimate sup |DD| ≤ sup|H_0''| + p_max · sup|H_η'' - H_0''|.
# We don't have an oracle for sup|H_η'' - H_0''| yet, but at η = 1/100
# the η/p perturbation on the SECOND derivative is small. Estimate it
# heuristically: |H_η''(w) - H_0''(w)| / η is bounded (since H_η = H_0 + O(η)
# and similarly for derivatives). For our purposes, treat the perturbation
# as small (≈ 0.5 say, comparable to M_phi_prime in magnitude scale).
sup_M_pp_perturb = mp.mpf("0.5")  # ROUGH estimate
sup_DD_ub = sup_H0pp + p_max * sup_M_pp_perturb
print(f"  sup |DD| ≤ {sup_DD_ub}  (with η perturbation rough ≤ {sup_M_pp_perturb})")

# u_zz bound
u_zz_bound = sup_DD_ub / inf_D_lb ** 3
print(f"\n  ‖u_zz‖ via aux-z-identity ≤ {u_zz_bound}")

# Compare with the paper's Cauchy bound 8R/(1-r)²
R_val = mp.sinh(mp.mpf(24)/mp.mpf(25))
print(f"\n  R_val_paper(r) ≈ {R_val}")
paper_uzz_bound = 8 * R_val / (1 - r) ** 2
print(f"  Paper Cauchy bound 8R/(1-r)² = {paper_uzz_bound}")
print(f"  Loose factor (paper / aux-z) ≈ {paper_uzz_bound / u_zz_bound}")

# Bound on Cr_phi_invD's term-2 with the new u_zz oracle:
# Term-2 (current) = (4R/(1-r)²) · M_phi² ≈ 4·1.15·156.25 · (239/5000)²
#                  = 4·1.15·156.25 · 0.002284 ≈ 1.642
# Term-2 (with u_zz oracle) = (1/2)·u_zz_bound · M_phi²
# (Lagrange factor /2 absorbed)
term2_current = mp.mpf(4) * R_val / (1 - r) ** 2 * M_phi_val ** 2
term2_new = mp.mpf("0.5") * u_zz_bound * M_phi_val ** 2
print()
print("=== Cr_phi term-2 comparison ===")
print(f"  Current: (4R/(1-r)²) · M_phi² = {term2_current}")
print(f"  New:     (1/2) · u_zz_bound · M_phi² = {term2_new}")
print(f"  Reduction factor: {term2_current / term2_new}")

# Total Cr_phi_invD with new term-2:
inv_F_p_z_val = mp.mpf(2)
term1 = M_phi_val * M_phi_prime_val * inv_F_p_z_val ** 2
total_new = term1 + term2_new
total_current = term1 + term2_current
print()
print(f"  Cr_phi_invD (V10):   term1={term1} + term2={term2_current} = {total_current}")
print(f"  Cr_phi_uzz (new):    term1={term1} + term2={term2_new} = {total_new}")
print()
print(f"  Cr_val candidate (ceiling): {int(total_new) + 1 if total_new > int(total_new) else int(total_new)}")
