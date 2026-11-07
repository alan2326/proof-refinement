"""
Proof module for certifying bounds on analytic functions.

This module contains tools for:
- Estimating lower bounds on the radius of convergence of inverse functions
- Computing the B_K bilinear form using Hermite diagonalization
- Finding optimal perturbations that maximize B_K
"""

from grothendieck.proof.inverse_radius import (
    estimate_inverse_radius,
    InverseRadiusResult,
    SingleRResult,
    load_coefficients,
)

from grothendieck.proof.bk_kernel import (
    BK_from_hermite,
    BK_hyperplane_baseline,
    compute_BK_from_results,
    find_max_eta,
    BKResult,
)

from grothendieck.proof.bk_semi_analytic import (
    compute_Delta,
    compute_Delta_direct,
    compute_G_complex,
    compute_H_over_i,
    compute_H_0_over_i,
    compute_C_S,
    E_inner_integral,
    GaussLegendre,
    precompute_E_matrix,
    BKSemiAnalyticResult,
    verify_quadrature,
    h3,
    h5,
    hermite_h,
)

from grothendieck.proof.cauchy_bound import (
    sample_G_on_circle,
    extract_g_coefficient,
    compute_remainder_bound,
    certify_delta,
    CauchyCertificationResult,
)
