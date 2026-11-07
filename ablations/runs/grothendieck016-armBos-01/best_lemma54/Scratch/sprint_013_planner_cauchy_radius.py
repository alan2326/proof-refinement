"""sprint_013 Planner — examine the Cauchy radius slack on ‖u_zz‖.

KEY INSIGHT (verified by reading Lemma54_Paper_Cauchy.lean lines 32, 92, 124):
The current proof of `F_inv_second_deriv_bound_core` uses a recentered Cauchy
radius of (1-r)/2, giving:
   ‖u_zz‖ ≤ 2 · R / ((1-r)/2)² = 8 R / (1-r)²

But the recentered ball at z₀ ∈ disk r needs only to lie inside disk r₁ = 1
(open). The triangle inequality:
   ‖z₀ + w‖ ≤ ‖z₀‖ + ‖w‖ < r + ρ
needs r + ρ ≤ 1, i.e., ρ ≤ 1 - r.

So we can use radius ρ = 1 - r (the FULL gap), giving:
   ‖u_zz‖ ≤ 2 · R / (1-r)² = 2 R / (1-r)²

A factor of 4 reduction!

Why does the existing proof use (1-r)/2? Likely an inheritance from a
different scenario where z₀ ranges over a larger ball, or just a
conservative-by-default choice. The actual hypothesis `z₀ ∈ disk r`
permits the full radius.

Wait — actually the issue is that the recentered ball must be a CLOSED
ball, and we need it inside an OPEN disk. So we need `r + ρ < 1` strictly,
not `r + ρ ≤ 1`. With ρ = 1-r exactly, the recentered closedBall has
points at exactly distance ρ + r = 1 from origin, which is ON the boundary
of disk r₁ (open ball), so NOT inside.

Resolution: use any ρ < 1-r, e.g., ρ = (1-r)·(1-ε) for small ε. As ε → 0,
‖u_zz‖ ≤ 2R/(ρ)² → 2R/(1-r)². For computability, pick ρ = (1-r)·k where
k = 1 - 1/N for some integer N; the bound becomes 2R/((1-r)·k)² = 2R/(1-r)²/k².

But actually... the recentered map's analyticity is on the OPEN disk
ball 0 (something), and Cauchy uses the CLOSED ball. The question is
the contour of integration: it's the circle of radius ρ. We need the
circle (and the closed ball it bounds) to be IN the analyticity domain.
Open ball is fine for circles strictly inside.

Mathematically the cleanest thing is: take any ρ < 1-r, derive the bound
2R/ρ², then take inf over ρ → 1-r⁻. The Cauchy integral formula gives
us exactly 2R/ρ² for any valid ρ, so the bound 2R/(1-r)² is achievable
in the LIMIT. But for a concrete Lean theorem, we need a fixed ρ.

Practical choice: ρ = (1-r) · (1 - 1/(M_ratio_steps)). Or, more cleanly,
use the following: the existing infrastructure computes the bound at
ρ = (1-r)/2. We can change it to ρ = (1-r) · k for any rational k < 1
without changing the proof structure — just substitute k everywhere in
Lemma54_Paper_Cauchy.lean.

Pragmatic plan: change ρ = (1-r)/2 to ρ = (1-r) · 99/100 (or ρ = (1-r) · 9/10),
yielding ‖u_zz‖ ≤ 2R/((1-r)·k)² = 2R/(1-r)² / k² = 2R · (10000/9801) / (1-r)²
≈ 2.04 · R/(1-r)². Compared to the current 8R/(1-r)², that's a factor
of ~3.92 reduction (close to optimal 4×).

NUMERICAL IMPACT on Cr_phi at V9 parameters:
   term2 = (4R/(1-r)²) · M_phi²
This term comes from:
   ‖u_zz‖ · ‖Φ‖² ≤ (8R/(1-r)²) · M_phi²
   = 2 · (4R/(1-r)²) · M_phi²
The "2" is because the lemma bounds ‖∂²ₚ F_inv‖ ≤ 2 · Cr_phi (Lagrange
remainder absorbs 1/2!), so what enters Cr_phi is half of 8R/(1-r)² = 4R/(1-r)².

If we tighten 8R → 8R · k_factor where k_factor = 1/k² (and k = 99/100,
k_factor ≈ 1/0.9801 ≈ 1.0203), then we lose. Wait — we want to REDUCE 8R,
so we use the OPPOSITE: recentered radius (1-r)·k for k as large as possible
< 1, giving 2R/((1-r)·k)² = (2/k²) R/(1-r)². For k = 99/100, that's
2.0408 R/(1-r)². For k = 999/1000, it's 2.004 R/(1-r)². Compared to
current 8R/(1-r)², the factor is k²·8/2 = 8k²/2 ... no wait.

Current: ‖u_zz‖ ≤ 8R/(1-r)² (using ρ = (1-r)/2, gives 2R/((1-r)/2)² = 8R/(1-r)²)
Proposed: ‖u_zz‖ ≤ 2R/((1-r)·k)² (using ρ = (1-r)·k)
Ratio: proposed / current = 2/((1-r)²·k²) ÷ 8/((1-r)²)
                          = 2/k² ÷ 8 = 1/(4k²)

For k = 99/100: 1/(4·(99/100)²) = 1/(4·0.9801) = 0.255 — so proposed ≈ 0.255 × current.
That's a 3.92× reduction in ‖u_zz‖.

So term2 of Cr_phi becomes:
   term2 (new) = (R/((1-r)·k)²) · M_phi²
              = (R / (1-r)²) · (1/k²) · M_phi²
"""
from __future__ import annotations
from fractions import Fraction
import math

# V9 baseline params
M_phi = Fraction(239, 5000)
M_phi_prime = Fraction(543, 10000)
R_max = Fraction(23, 20)
one_minus_r = Fraction(2, 25)

invFp = 2 * R_max / one_minus_r
invFp_sq = invFp ** 2

# CURRENT: ‖u_zz‖ ≤ 8R/(1-r)², so term2 = (1/2) · 8R/(1-r)² · M_phi² = 4R/(1-r)² · M_phi²
term1 = M_phi * M_phi_prime * invFp_sq
term2_current = (4 * R_max / one_minus_r ** 2) * M_phi ** 2
Cr_phi_current = term1 + term2_current

print(f"V9 Cr_phi (current): term1={float(term1):.4f}, term2={float(term2_current):.4f}, total={float(Cr_phi_current):.4f}")
print()

# PROPOSED: ‖u_zz‖ ≤ 2R/((1-r)·k)² for k < 1
# In Cr_phi terms: term2_new = (R/((1-r)·k)²) · M_phi²
# We have:
#   term2_current = 4 R / (1-r)² · M_phi²
#   term2_new     = R / ((1-r)² · k²) · M_phi² = (1/(4k²)) · 4R/(1-r)² · M_phi²
#                = (1/(4k²)) · term2_current

for k_num, k_den in [(1, 2), (9, 10), (99, 100), (999, 1000), (9999, 10000)]:
    k = Fraction(k_num, k_den)
    term2_new = (R_max / (one_minus_r ** 2 * k ** 2)) * M_phi ** 2
    Cr_phi_new = term1 + term2_new
    print(f"  k = {k_num}/{k_den}  ({float(k):.4f}):  term2 = {float(term2_new):.4f}, Cr_phi = {float(Cr_phi_new):.4f}, "
          f"ratio_to_current = {float(Cr_phi_new/Cr_phi_current):.4f}")

print()
print("=" * 72)
print("If we go to k → 1 (the limit), term2 drops 4× from 1.6422 to ≈ 0.4106.")
print("Cr_phi → 2.1454 + 0.4106 ≈ 2.5560.")
print("Cr_val could drop to 3 (from 5), a 1.67× reduction.")
print()
print("Practical: k = 9/10 gives term2 = 4·R·(1-r)⁻²·(1/(4·81/100))·M_phi²")
print("             = (term2_current) · (100/(4·81))")
print("             = term2_current · 0.3086")
print()

# Practical choice: k = 9/10 keeps the arithmetic clean.
k_target = Fraction(9, 10)
term2_target = (R_max / (one_minus_r ** 2 * k_target ** 2)) * M_phi ** 2
Cr_phi_target = term1 + term2_target
print(f"AT k = 9/10: Cr_phi = {Cr_phi_target} ≈ {float(Cr_phi_target):.6f}")
print(f"  Cr_val = 3 margin: {3 - float(Cr_phi_target):.6f}")
print(f"  Cr_val = 5/2 margin: {2.5 - float(Cr_phi_target):.6f}")
print()

k_target = Fraction(99, 100)
term2_target = (R_max / (one_minus_r ** 2 * k_target ** 2)) * M_phi ** 2
Cr_phi_target = term1 + term2_target
print(f"AT k = 99/100: Cr_phi = {Cr_phi_target} ≈ {float(Cr_phi_target):.6f}")
print(f"  Cr_val = 3 margin: {3 - float(Cr_phi_target):.6f}")
print(f"  Cr_val = 5/2 margin: {2.5 - float(Cr_phi_target):.6f}")
print()

# Closer to optimal (limit ≈ 2.556):
print("=" * 72)
print("STRUCTURAL LEVER: lift Cauchy radius from (1-r)/2 to (1-r)·k for k → 1.")
print()
print("Lean changes required:")
print("  - In Lemma54_Paper_Cauchy.lean: parameterize the Cauchy radius by")
print("    a ratio k ∈ (0, 1), or hard-code a specific k (e.g., 9/10).")
print("  - Change `half_one_sub_pos`, `add_mem_disk_r1`,")
print("    `differentiableOn_recentered`, `norm_recentered_le`, and both")
print("    `F_inv_*_deriv_bound_core` lemmas to use the new ρ.")
print("  - Update `Lemma54_Paper_Pderiv_Single.lean`:")
print("    line 367 `‖u_zz‖ ≤ 8R/(1-r)²` → `‖u_zz‖ ≤ 2R/((1-r)·k)²` (or numeric")
print("    evaluation at k = 9/10: 2R · 100/81 / (1-r)²).")
print("  - Update Cr_phi formula in Lemma54_Paper.lean:")
print("    Cr_phi = M_phi · M_phi_prime · invFp² + (R/((1-r)·k)²) · M_phi²")
print("    (note: was 4R/(1-r)², now R/((1-r)·k)² = 4R/(1-r)²·(1/(4k²)))")
print()
print("Direction: structural — Cauchy contour optimization, exploits unused")
print("slack from (1-r)/2 → (1-r)·k. Tier: ambitious (multiple Lean files,")
print("careful re-statement of Step 3 lemmas).")
