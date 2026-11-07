"""
Step 3: Compute Taylor coefficients of φ(z) = (z - H_eta(sin z)) * cos z.

φ is odd (only odd Taylor coefficients are nonzero).

Pipeline:
  1. Compute sin(z), cos(z) as arb_series
  2. Compose H_eta with sin(z) via Horner
  3. Form (z - H_eta(sin z)) * cos z
  4. Extract coefficients c_{2k+1}

Since H_eta(z) = (pi/2) * sum b_k z^k where b_k are the sigma coefficients,
we have for the baseline (H_0 = arcsin):
  H_0(sin z) = z, so φ_0 = 0.

For perturbed H_eta, φ captures the deviation from arcsin.
"""

from __future__ import annotations

from flint import arb, acb, arb_series, ctx as flint_ctx

from grothendieck.proof.certified.h_eta_evaluator import compose_series_horner


def compute_phi_coefficients(
    h_eta_series: arb_series,
    K_max: int = 50,
    prec: int = 128,
    verbose: bool = False,
) -> arb_series:
    """Compute Taylor coefficients of φ(z) = (z - H_eta(sin z)) * cos z.

    Args:
        h_eta_series: Taylor series of H_eta(z) as arb_series.
        K_max: Number of terms in output series.
        prec: Precision in bits.

    Returns:
        arb_series representing φ(z).
    """
    old_prec = flint_ctx.prec
    old_cap = flint_ctx.cap
    flint_ctx.prec = prec
    flint_ctx.cap = K_max + 1

    # Create z as identity series
    z = arb_series([arb(0), arb(1)], K_max + 1)

    # sin(z) and cos(z) as truncated power series
    sin_z = z.sin()
    cos_z = z.cos()

    if verbose:
        sin_coeffs = sin_z.coeffs()
        print(f"Step 3: Computing φ(z) Taylor coefficients")
        print(f"  K_max = {K_max}")
        print(f"  sin(z) leading: {sin_coeffs[1] if len(sin_coeffs) > 1 else 'N/A'}")

    # Compose H_eta with sin(z) using Horner's method
    h_coeffs = h_eta_series.coeffs()
    # Pad to K_max if needed
    while len(h_coeffs) < K_max:
        h_coeffs.append(arb(0))

    h_of_sin = compose_series_horner(h_coeffs[:K_max], sin_z, K_max)

    if verbose:
        hos_coeffs = h_of_sin.coeffs()
        print(f"  H_eta(sin z) leading: {hos_coeffs[1] if len(hos_coeffs) > 1 else 'N/A'}")
        # For baseline: H_0(sin z) = z, so coefficient of z should be 1
        if len(hos_coeffs) > 1:
            print(f"  (baseline reference: coeff of z should be ~1)")

    # Form φ(z) = (z - H_eta(sin z)) * cos z
    diff = z - h_of_sin
    phi = diff * cos_z

    # Truncate to K_max
    phi_coeffs = phi.coeffs()
    if len(phi_coeffs) > K_max:
        phi_coeffs = phi_coeffs[:K_max]
    phi = arb_series(phi_coeffs, K_max)

    if verbose:
        pc = phi.coeffs()
        print(f"  φ coefficients (first few odd):")
        for k in range(min(10, len(pc))):
            if k % 2 == 1 and k < len(pc):
                print(f"    c_{k} = {pc[k]}")

    flint_ctx.prec = old_prec
    flint_ctx.cap = old_cap
    return phi


def extract_odd_coefficients(phi: arb_series) -> list:
    """Extract odd coefficients c_{2k+1} from φ.

    Returns list of (k, c_{2k+1}) pairs.
    """
    coeffs = phi.coeffs()
    odd_coeffs = []
    for k in range(len(coeffs)):
        idx = 2 * k + 1
        if idx < len(coeffs):
            odd_coeffs.append((k, coeffs[idx]))
    return odd_coeffs


def verify_phi_baseline(K_max: int = 50, prec: int = 128) -> bool:
    """Verify that for H_0 = arcsin, φ(z) ≈ 0.

    This is a sanity check: arcsin(sin z) = z, so φ = 0.
    All coefficients should be within their error balls of 0.
    """
    old_prec = flint_ctx.prec
    old_cap = flint_ctx.cap
    flint_ctx.prec = prec
    flint_ctx.cap = K_max + 1

    # H_0(z) = arcsin(z) as arb_series
    z = arb_series([arb(0), arb(1)], K_max + 1)
    h0_series = z.asin()

    phi = compute_phi_coefficients(h0_series, K_max, prec)
    coeffs = phi.coeffs()

    all_near_zero = True
    for k, c in enumerate(coeffs):
        if not c.contains(arb(0)):
            all_near_zero = False
            break

    flint_ctx.prec = old_prec
    flint_ctx.cap = old_cap
    return all_near_zero
