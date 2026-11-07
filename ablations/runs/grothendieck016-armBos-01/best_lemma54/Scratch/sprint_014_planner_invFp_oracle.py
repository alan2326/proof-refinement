"""
sprint_014 Planner exploration: numerical viability of an inline-oracle
sprint that tightens `invFp = 1/inf|D|` directly.

CONTEXT
-------
The sink Cr_phi at V9 is

    Cr_phi := M_phi · M_phi_prime · invFp^2 + (4R/(1-r)^2) · M_phi^2

with V9 values M_phi=239/5000, M_phi_prime=543/10000, R≤23/20, 1-r=2/25.

The current `invFp = 2R/(1-r)` ≈ 28.75 is a paper-worst-case derived
from F_p_deriv_lower_bound_at_F_inv : ‖D‖ ≥ (1-r)/(2R), giving
1/‖D‖ ≤ 2R/(1-r). At η=1/100 and small p, the *actual* `D` is

    D(η,p,w) = (1-p)·H_0'(w) + p·H_eta'(w) ≈ H_0'(w)  (since p ≪ 1)

and H_0(w) = arcsin(w) (per Kernel.lean comment, Lemma 4.3), so
H_0'(w) = 1/sqrt(1-w^2). On Ω(δ,B) = { |Re w| < 1-δ, |Im w| < B },
|1-w^2| is bounded BELOW (since w stays away from ±1), hence |H_0'|
is bounded ABOVE, and 1/|D| is bounded ABOVE by a small constant.

This script computes:
1. The infimum of |H_0'(w)| over Ω(δ,B) (a lower bound -> 1/sup of inv).
2. The infimum of |D(η,p,w)| over (η,p,w) for p ∈ [0, pr_paper] and
   w ∈ Ω(δ,B), to check that the η/p perturbation doesn't kill the bound.
3. The resulting Cr_phi at the proposed tightened invFp.

TARGET: confirm that Cr_phi drops to < 2 at V9 parameters, justifying
a Cr_val := 2 sprint via the new oracle.
"""
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 50

# V9 parameters (rationals)
delta = Fraction(1635, 10000)         # 0.1635
B = Fraction(1115, 1000)              # 1.115
r = Fraction(23, 25)                  # 0.92
M_phi_q = Fraction(239, 5000)         # 0.0478
M_phi_prime_q = Fraction(543, 10000)  # 0.0543
R_max_q = Fraction(23, 20)            # 1.15  (R_val_paper r ≤ 23/20)
one_minus_r = Fraction(1, 1) - r      # 2/25 = 0.08
eta = Fraction(1, 100)                # 0.01

# Convert to mpmath
delta_m = mp.mpf(delta.numerator) / mp.mpf(delta.denominator)
B_m = mp.mpf(B.numerator) / mp.mpf(B.denominator)
one_m_r_m = mp.mpf(one_minus_r.numerator) / mp.mpf(one_minus_r.denominator)
R_m = mp.sinh(mp.mpf(49) / mp.mpf(50))  # actual R_val_paper(23/25) = sinh(49/50)

# === Step 1: Current Cr_phi at V9 (sanity check, should match V9's 3.79) ===

invFp_old = 2 * R_m / one_m_r_m
print(f"=== Current invFp (paper bound 2R/(1-r)) ===")
print(f"  invFp_old = 2*sinh(49/50)/(2/25) = {invFp_old} ≈ {float(invFp_old):.4f}")

R_max_m = mp.mpf(R_max_q.numerator) / mp.mpf(R_max_q.denominator)
M_phi_m = mp.mpf(M_phi_q.numerator) / mp.mpf(M_phi_q.denominator)
M_phi_prime_m = mp.mpf(M_phi_prime_q.numerator) / mp.mpf(M_phi_prime_q.denominator)

# Use R_max=23/20 (the rationalized upper bound) to mirror Lean's literal
invFp_old_at_Rmax = 2 * R_max_m / one_m_r_m
print(f"  invFp_old @ R≤23/20 = 2*(23/20)/(2/25) = {invFp_old_at_Rmax} = 28.75")
term1_old = M_phi_m * M_phi_prime_m * invFp_old_at_Rmax**2
term2_old = (4 * R_max_m / one_m_r_m**2) * M_phi_m**2
Cr_phi_old = term1_old + term2_old
print(f"  term1 = M_phi*M_phi_prime*invFp^2 = {float(term1_old):.4f}")
print(f"  term2 = (4R/(1-r)^2)*M_phi^2     = {float(term2_old):.4f}")
print(f"  Cr_phi_old = {float(Cr_phi_old):.4f} (should be ≈ 3.79)")

# === Step 2: Inf of |H_0'(w)| = inf 1/|sqrt(1-w^2)| = 1/sup|sqrt(1-w^2)| ===
#
# H_0(w) = arcsin(w), H_0'(w) = 1/sqrt(1-w^2). For w in Ω(δ,B):
#   w = u + iv, |u| ≤ 1-δ = 0.8365, |v| ≤ B = 1.115.
#
# 1 - w^2 = 1 - (u+iv)^2 = (1 - u^2 + v^2) - 2iuv
# |1-w^2|^2 = (1-u^2+v^2)^2 + 4u^2v^2
#
# inf |H_0'(w)|  ⟺  sup |1-w^2|  (over the closed rectangle).

print()
print(f"=== Step 2: sup |1-w^2| on Ω(δ,B), δ=1635/10000, B=1115/1000 ===")
def mod_one_minus_w2(u, v):
    A = 1 - u**2 + v**2
    return mp.sqrt(A**2 + 4 * u**2 * v**2)

# Search corners and edges (analytic optimum on a rectangle for this function
# is at corners / edge interior critical points).
sup_one_m_w2 = mp.mpf(0)
inf_one_m_w2 = mp.mpf("inf")
um = float(1 - delta_m)
vm = float(B_m)
N = 200
for i in range(N+1):
    u = mp.mpf(-um) + (2*um) * mp.mpf(i) / N
    for j in range(N+1):
        v = mp.mpf(-vm) + (2*vm) * mp.mpf(j) / N
        x = mod_one_minus_w2(u, v)
        if x > sup_one_m_w2: sup_one_m_w2 = x
        if x < inf_one_m_w2: inf_one_m_w2 = x

print(f"  sup |1-w^2| (grid 200x200) ≈ {float(sup_one_m_w2):.6f}")
print(f"  inf |1-w^2| (grid 200x200) ≈ {float(inf_one_m_w2):.6f}")

# Closed-form sup: for the function f(u,v) = (1-u^2+v^2)^2 + 4u^2v^2
# the maximum on the rectangle is attained at a corner: u=±(1-δ), v=±B.
u_corner = 1 - delta_m
v_corner = B_m
sup_corner = mod_one_minus_w2(u_corner, v_corner)
print(f"  closed-form @ corner u=1-δ, v=B: {float(sup_corner):.6f}")

# inf |H_0'(w)| = 1/sup|sqrt(1-w^2)| = 1/sqrt(sup|1-w^2|)
inf_H0p = 1 / mp.sqrt(sup_one_m_w2)
sup_H0p_inv = 1 / inf_H0p  # = sqrt(sup|1-w^2|)

# Wait: H_0'(w) = 1/sqrt(1-w^2). |H_0'(w)| = 1/|sqrt(1-w^2)| = 1/sqrt(|1-w^2|).
# inf |H_0'| = 1/sqrt(sup |1-w^2|). 1/|H_0'| = sqrt(|1-w^2|).
# sup 1/|H_0'| = sqrt(sup |1-w^2|).

print(f"  sup 1/|H_0'(w)| = sqrt(sup|1-w^2|) ≈ {float(mp.sqrt(sup_one_m_w2)):.6f}")
print(f"  inf 1/|H_0'(w)| = sqrt(inf|1-w^2|) ≈ {float(mp.sqrt(inf_one_m_w2)):.6f}")

# === Step 3: Now D = (1-p)*H_0'(w) + p*H_eta'(w). For small p, |D| ≥ |H_0'|·(1-p) - p*|H_eta'|.
# We need a lower bound on |D| valid for all p ∈ [0, pr_paper].
# pr_paper at η=1/100 is bounded above by... hmm, hard to say without a numerical handle.
# In production, p_explicit_rat = 1e-30, so p effectively is 0. But the contract has p < pr_paper
# which is some certified positive (≈ 2.4e-4 in the production runner).
# For p ≤ 1e-3, |D| ≥ 0.999*|H_0'| - 0.001*|H_eta'|. M_val = 428 dominates |H_eta'|, so:
#   |D| ≥ inf|H_0'| - p_max*(M_val + |H_0'|) ≈ inf|H_0'| - p_max·428
# At p_max ≈ 2.4e-4, this is ≈ inf|H_0'| - 0.103. We'd need inf|H_0'| > 0.103.

print()
print("=== Step 3: |D| accounting under η/p perturbation ===")
inf_H0p_m = mp.sqrt(inf_one_m_w2)  # this is inf 1/|H_0'|, NOT inf |H_0'|!
# Wait. |H_0'(w)| = 1/sqrt(|1-w^2|), so inf|H_0'| = 1/sqrt(sup|1-w^2|).
inf_abs_H0p = 1 / mp.sqrt(sup_one_m_w2)
sup_abs_H0p = 1 / mp.sqrt(inf_one_m_w2)
print(f"  inf |H_0'(w)| over Ω = 1/sqrt(sup|1-w^2|) ≈ {float(inf_abs_H0p):.6f}")
print(f"  sup |H_0'(w)| over Ω = 1/sqrt(inf|1-w^2|) ≈ {float(sup_abs_H0p):.6f}")
print(f"  sup 1/|H_0'(w)| = sup|sqrt(1-w^2)| = sqrt(sup|1-w^2|) ≈ {float(mp.sqrt(sup_one_m_w2)):.6f}")
print()

# So 1/|H_0'(w)| ≤ sqrt(sup|1-w^2|) ≈ 1.55
# Then 1/|D(η,p,w)| ≤ 1/(|H_0'(w)| - p·M_val) ≤ 1/(inf|H_0'| - p·M_val) for p small.
# We want a sup bound on 1/|D(η,p,w)| valid for all p ∈ [0, pr]. For p=0, it's just sup 1/|H_0'|.
# For p > 0, it's slightly worse but bounded.

# Key insight: the existing F_p_deriv_lower_bound_at_F_inv gives ‖D‖ ≥ (1-r)/(2R) ≈ 0.0348.
# So 1/‖D‖ ≤ 2R/(1-r) = 28.75. Replacing this with sup 1/|H_0'| ≈ 1.55 (and accounting for
# p-perturbation) gives ~18x tightening for invFp; in invFp^2, that's ~324x.

# Tightened invFp candidates:
invFp_new_clean = mp.sqrt(sup_one_m_w2)  # sqrt(sup|1-w^2|) ≈ 1.55 — η=p=0 case
invFp_new_safe = 2  # generous integer ceiling, accommodates p-perturbation safely

print(f"=== Step 4: Cr_phi at tightened invFp ===")
for invFp_new, label in [(invFp_new_clean, "clean (η=p=0)"), (mp.mpf(invFp_new_safe), "safe ceiling 2")]:
    term1_new = M_phi_m * M_phi_prime_m * invFp_new**2
    term2_new = (4 * R_max_m / one_m_r_m**2) * M_phi_m**2  # unchanged
    Cr_phi_new = term1_new + term2_new
    print(f"  invFp = {label} = {float(invFp_new):.4f}")
    print(f"    term1 = {float(term1_new):.6f}")
    print(f"    term2 = {float(term2_new):.6f}")
    print(f"    Cr_phi_new = {float(Cr_phi_new):.4f}")
    if float(Cr_phi_new) < 2:
        print(f"    ==> Cr_val := 2 feasible (margin {2-float(Cr_phi_new):.4f})")
    elif float(Cr_phi_new) < 3:
        print(f"    ==> Cr_val := 3 feasible (margin {3-float(Cr_phi_new):.4f})")

# Closed-form rational invFp upper bound for Lean:
# We need a rational q ≥ sup 1/|H_0'(w)| valid on the closed rectangle.
# sup 1/|H_0'| = sqrt(sup|1-w^2|).
# At corner u=1-δ=8365/10000, v=B=1115/1000:
#   1-u^2 = 1 - (8365/10000)^2 = 1 - 69973225/10^8 = 30026775/10^8
#   v^2 = (1115/1000)^2 = 1243225/10^6 = 124322500/10^8
#   1 - u^2 + v^2 = (30026775 + 124322500)/10^8 = 154349275/10^8
#   2uv = 2*(8365/10000)*(1115/1000) = 18653950/10^7 ≈ 1.8654
#   2uv squared = (2uv)^2 ... I'll just compute numerically.

print()
print("=== Step 5: rational ceiling for an oracle bound ===")
sup_1mw2_corner = mod_one_minus_w2(1 - delta_m, B_m)
sup_one_over_D_clean = mp.sqrt(sup_1mw2_corner)
print(f"  sqrt(|1 - (1-δ+iB)^2|) at corner = {float(sup_one_over_D_clean):.10f}")
# A rational ceiling: 16/10 = 1.6 (covers the η=p=0 sup of ~1.554)
# but we need to account for p-perturbation. For p ≤ pr_paper ≈ 2.4e-4 and |H_eta'| ≤ M_val=428:
#   |D| ≥ |H_0'|·(1-p) - p·|H_eta'|·1 ≥ |H_0'| - p·(|H_0'| + |H_eta'|) ≈ |H_0'|(1 - 2p) - p·M
# So 1/|D| ≤ 1/(|H_0'| - p·(M+|H_0'|)) ≤ 1/(inf|H_0'| - p·(M+sup|H_0'|))
# Numerically: inf|H_0'| ≈ 0.643, sup|H_0'| ≈ 1.95(?), M=428.
# At p_max = 2.4e-4: denominator = 0.643 - 2.4e-4 * (428 + 1.95) ≈ 0.643 - 0.103 = 0.540.
# So 1/|D| ≤ 1/0.540 ≈ 1.85. This is the realistic sup over the *full* range p ∈ [0, pr].

# Closed-form better bound: pick a tighter pr (smaller) so the perturbation is negligible.
# Note: pr_paper is what the candidate's sink theorem promises p < pr; the candidate doesn't
# control pr. So we have to bound 1/|D| uniformly in p ∈ (0, pr_paper).
# The "safe" bound is to take the p-perturbed value.

p_max_realistic = mp.mpf("2.4e-4")  # pr_paper estimate from production runner
M_val_m = mp.mpf(428)
inf_abs_D = inf_abs_H0p - p_max_realistic * (M_val_m + sup_abs_H0p)
print(f"  At p_max ≈ {float(p_max_realistic):.4e}, inf|D| ≈ {float(inf_abs_D):.4f}")
print(f"  sup 1/|D| ≈ {float(1/inf_abs_D):.4f}")

# So the realistic bound: invFp_new ≤ 1.85 (with safety, take 2 or 5/2).
invFp_real = 1 / inf_abs_D
print(f"  -> realistic invFp_new = {float(invFp_real):.4f}")

# At invFp = 2, term1 = 0.0478 * 0.0543 * 4 = 0.01038. Cr_phi = 0.01038 + 1.66 = 1.67.
# Cr_val := 2 with margin 0.33. Tight but ok for nlinarith.

print()
print("=== CONCLUSION ===")
print("Inline-oracle direction is viable. New oracle `inv_F_p_z_oracle` certifying")
print(" sup_{p ∈ [0,pr_paper]} sup_{w ∈ Ω(δ,B)} 1/‖∂_z F(η,p,w)‖ ≤ inv_F_p_z_val ≈ 2")
print("would replace the loose paper bound 28.75 with ~2, an 14× reduction in invFp,")
print("a 196× reduction in invFp², and would drop Cr_phi from 3.79 to ≈ 1.67.")
print("Setting Cr_val := 2 yields a 2.5× win over V9's Cr_val=5.")
print()
print("HOWEVER: the new oracle requires bounding inf|D| over the FULL p-range [0,pr_paper],")
print("not just at p=0. This requires knowing pr_paper or pinning it. Two paths:")
print("  (a) `Numerical_Library/inv_F_p_z.py` parameterizes by p_max and certifies for")
print("      all p ≤ p_max. The candidate then declares an axiom with a hypothesis p < p_max.")
print("      The plumbing into Cr_phi must thread p_max through F_p_deriv_lower_bound_at_F_inv.")
print("  (b) Use only the η-derivative direction: the new oracle bounds")
print("      `sup |H_0'(w)|^{-1}` on Ω, and a SEPARATE inequality 1/|D(η,p,w)| ≤")
print("      1/|H_0'(w)| · (1 + O(p)), proved analytically. This adds an analytic step in Lean.")
print()
print("For sprint_014, we'll commit to (a): an oracle that parameterizes over p_max ≤ pr_paper.")
