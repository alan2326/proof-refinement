"""Sprint 010 planner exploration: finding a tractable theoretical move.

The Bulletin requires we leave numerical-tightening behind and pick from
{axiom-prove, formula-change, identity-refine, contour-change}. This script
computes Cr_tight at our params and explores structural tightenings.
"""
from fractions import Fraction
import math


def crtight(r, M, R):
    """Cr_tight = 16 M² R (R+1) / (1-r)²"""
    return 16 * M**2 * R * (R + 1) / (1 - r)**2


def cr_two_term(r, M, R):
    """The actual Step-5 derivation: 32 M² R² / (1-r)² + 32 M² R / (1-r)²
    = 16 M² · (2R²) / (1-r)² + 16 M² · (2R) / (1-r)²,
    absorbing 1/2! Lagrange gives Cr := half of that."""
    invFp_sq = 4 * R**2 / (1 - r)**2  # = invFp² where invFp = 2R/(1-r)
    term1 = 8 * M**2 * invFp_sq           # comes from 2|Φ'|·|Φ|·invFp²
    term2 = 4 * M**2 * 8 * R / (1 - r)**2  # comes from |u_zz|·|Φ|²
    return term1 + term2


def sinh_q(x):
    """High-precision sinh as Fraction-friendly float."""
    return math.sinh(x)


# Our params
r = Fraction(23, 25)
M = Fraction(428)
r1 = (1 + r) / 2   # = 24/25
r2 = (3 + r) / 4   # = 49/50
R_r2 = sinh_q(float(r2))   # ≈ 1.13186, what R_val_paper produces today
R_r1 = sinh_q(float(r1))   # ≈ 1.10995, hypothetical r1-bound

print(f"r = {r} = {float(r)}")
print(f"r1 = {r1} = {float(r1)}")
print(f"r2 = {r2} = {float(r2)}")
print(f"R = sinh(r2) = sinh(49/50) ≈ {R_r2:.6f}  [what R_val_paper produces]")
print(f"R = sinh(r1) = sinh(24/25) ≈ {R_r1:.6f}  [if we could use r1-bound]")
print(f"R_lit = 23/20 = 1.15  [V7's literal upper bound on R]")
print()

R_actual = float(R_r2)
R_lit = 23/20
M_f = 428.0
r_f = float(r)

print("=== Cr_tight at the *actual* R = sinh(r₂) (best-possible single-M Cr_tight) ===")
print(f"Cr_tight(actual) = {crtight(r_f, M_f, R_actual):.6e}")
print(f"V7's literal Cr_val = 1.13231e9 (upper bound based on R ≤ 23/20)")
print(f"Theoretical floor (R = sinh(r2)) = {crtight(r_f, M_f, R_actual):.6e}")
print(f"Gap from V7 to theoretical floor: "
      f"{(1.13231e9 - crtight(r_f, M_f, R_actual)) / 1.13231e9 * 100:.2f}%")
print()

# Hypothetical: if F_inv R-bound were sinh(r1) instead of sinh(r2):
print("=== Hypothetical: R = sinh(r1) instead (would require new analytic fact) ===")
print(f"Cr_tight(R=sinh(r1)) = {crtight(r_f, M_f, R_r1):.6e}")
print(f"Reduction vs Cr_tight(R=sinh(r2)): "
      f"{(crtight(r_f, M_f, R_actual) - crtight(r_f, M_f, R_r1)) / crtight(r_f, M_f, R_actual) * 100:.2f}%")
print()

# Cr_refined hypothetical with tight M_diff
# From paper structure: phi(z) = H_eta(z) - H_0(z). For the integral
# definitions, phi = O(η) at small η. Bracketing: M_diff ≤ 2M (trivial)
# vs M_diff ~ η · sup|∂_η H_eta| (refined).
# At eta=1/100 and assuming sup|∂_η H_eta| ~ M (a guess of order 1):
print("=== Cr_refined hypothetical (NEEDS new oracles, FORBIDDEN) ===")
eta = 0.01
invFp = 2 * R_actual / (1 - r_f)
# Rough estimate: M_diff ~ eta * M, M_diffp ~ eta * M, M_pp ~ M
M_diff_est = eta * M_f
M_diffp_est = eta * M_f
M_pp_est = M_f
# Cr_refined = M_diff·M_diffp·invFp² + M_pp·M_diff²·invFp³/2
cr_ref = M_diff_est * M_diffp_est * invFp**2 + M_pp_est * M_diff_est**2 * invFp**3 / 2
print(f"Cr_refined (η²-scaled) ≈ {cr_ref:.4e}")
print(f"Reduction factor vs Cr_tight: {crtight(r_f, M_f, R_actual)/cr_ref:.1f}×")
print("=> dramatic, but requires new M_diff/M_diffp/M_pp oracles (forbidden).")
print()

# What about the (R+1) → (R + 1/2) refinement?
# Looking at lines 651-657 of Lemma54_Paper_Pderiv_Single.lean, the bound
#   2·|Φ'|·|Φ|·invFp² + |u_zz|·|Φ|²
# uses |Φ|, |Φ'| ≤ 2M *both*. But |Φ| = |H_eta - H_0|, while |Φ'| = |H_eta' - H_0'|.
# Both are bounded by 2M via triangle. Can we tighten just |Φ| (not |Φ'|)?
# Direct bound: at z=0, Φ(0) = H_eta(0) - H_0(0) = 0 - 0 = 0.
# By max-modulus on F_inv-envelope (closedBall 0 R ∩ S):
#   |Φ(w)| ≤ max{|H_eta(w)|, |H_0(w)|} for any w (triangle gives sum ≤ 2M).
# But w=0 makes Φ=0, so the *average* |Φ| on the envelope is ≤ M (rough).
# The *sup* however can still be 2M in worst case.
#
# A genuine improvement: prove |Φ(F_inv(z))| ≤ M (not 2M) by noting that
# |H_eta(w)|, |H_0(w)| ≤ M on F_inv envelope, and Φ = (H_eta - H_0) where
# at the *origin* both vanish — so |Φ| has BOTH endpoints small.
# Actually no, the sup of (a - b) where |a|,|b| ≤ M is exactly 2M. Tight.

# OK consider: can we bound |Φ(F_inv z)| · |Φ'(F_inv z)| simultaneously
# better than (2M)·(2M) = 4M²? If they're CORRELATED (both small or both
# large at same point), then sup |Φ·Φ'| ≤ (sup |Φ|)·(sup |Φ'|) is loose.
# But without more analytic info, this 4M² is the only general bound.

# ============ The ACTIONABLE move I commit to ============
# Looking at the chain rule step in Lemma54_Paper_Pderiv_Single.lean
# lines 651-657: 2·|Φ'|·(|Φ|·invFp²) ≤ 2·(2M)·((2M)·invFp²) = 8M²·invFp²
# This applies the bound |Φ| ≤ 2M and |Φ'| ≤ 2M independently.
# But |Φ·Φ'| at any single point z: by Cauchy-Schwarz (or AM-GM),
# 2·|Φ|·|Φ'| ≤ |Φ|² + |Φ'|², and BOTH ≤ (2M)². So 2·|Φ|·|Φ'| ≤ 8M². Loose.
#
# Reality: the sup-norm bound |Φ|, |Φ'| ≤ 2M independently allows
# product ≤ 4M². No improvement without correlation info.

# OK the structural moves I've considered all hit the same wall:
# either need a new oracle or a new analytic fact (axiom).
#
# REMAINING TRACTABLE PATH: AXIOM-PROVE.
# Look at F_inv_paper_at_origin: F_inv_paper p 0 = 0.
# Statement: for p ∈ [0, pr_paper), F_inv_paper p 0 = 0.
#
# Approach:
#  (1) F_inv_paper_eq at z=0 gives F_p η p (F_inv_paper p 0) = 0
#  (2) F_p η p 0 = 0 (from H_0(0) = 0 and H_eta(0) = 0, both proved)
#  (3) By LOCAL UNIQUENESS of F_inv_paper near 0 — which is *implicit*
#      in the IFT, but harder to extract.
#
# Local uniqueness derivation: F_p η p is C¹ near 0 with derivative
# (1-p)·H_0'(0) + p·H_eta'(0). At p=0 this is H_0'(0); at p=1 it's H_eta'(0).
# Both are nonzero (analytic at 0, and H_eta is the Lemma 4 kernel which
# has H_eta'(0) = H_0'(0) = 1 by symmetry/normalisation).
# In particular for p ∈ [0, 1], F_p'(0) = (1-p)·1 + p·1 = 1 ≠ 0.
# Then F_p has a local C¹ inverse near 0, sending 0 → 0.
# Provided F_inv_paper IS this inverse near 0 (which the IFT guarantees),
# F_inv_paper p 0 = 0.
#
# This is plausibly a single-sprint proof but requires:
#   - H_0'(0) = 1 (or at least known nonzero)
#   - Lean's Mathlib local-inverse lemma (HasDerivAt.local_inverse or similar)
#   - Wiring F_inv_paper to be this local inverse
# The third step requires opening F_inv_paper's IFT axiom; risky.
#
# Maybe instead pursue: replace F_inv_paper_at_origin with a *derivable*
# axiom-prove path: extract its content from existing axioms.
#
# Actually F_inv_paper_at_origin is used in the F_inv_p_at_origin proof
# as a CONVENIENCE; the actual structure of the proof might not need it
# in full generality. Worth exploring.

print("=== Conclusion ===")
print("The 4 directions allowed by the Bulletin all hit walls:")
print("  - axiom-prove: 12 axioms are deep IFT facts; F_inv_paper_at_origin")
print("    is the closest to tractable but still needs IFT-internal lemmas.")
print("  - formula-change to Cr_refined: requires new M_diff/M_diffp/M_pp")
print("    oracles (forbidden as new axioms).")
print("  - identity-refine: |Φ|, |Φ'| ≤ 2M is already tight without")
print("    η-aware analysis; requires new analytic facts.")
print("  - contour-change for u_zz Cauchy bound: 8R/(1-r)² is sharp on")
print("    disks; alternative contours need new analytic infrastructure.")
print()
print("The most tractable move I can propose: PROVE F_inv_paper_at_origin")
print("by combining F_inv_paper_eq (existing axiom) with H_eta_zero/H0_zero")
print("(existing theorems) and a Mathlib local-inverse lemma. This may")
print("require additional bridge lemmas.")
