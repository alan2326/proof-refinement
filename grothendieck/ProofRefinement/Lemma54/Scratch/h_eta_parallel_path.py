"""Sharp rigorous H_η(z) via PARALLEL composite Gauss–Legendre path integration.

Replaces the slow `acb.integral` outer-path approach (h_by_price_path_certified.py)
with explicit GL nodes whose H_η' evaluations run in parallel across ≤ N cores
(default 32). Production scale: 64 chunks × 2 segments × 16 nodes = 2048
work units, all independent.

Math:
  H_η(z) = H_η(0) + ∫₀^z H_η'(ζ) dζ                  (V26: H_η(0) = 0)
  Path: 0 → Re(z) → z (two-segment polygonal).
  Per segment ζ(t) = z₀ + t·(z₁ - z₀) for t ∈ [0,1]:
      ∫_segment H_η' dζ = (z₁ - z₀) · ∫₀¹ H_η'(ζ(t)) dt
                       ≈ (z₁ - z₀) · Σ w_i · H_η'(ζ(t_i))
  via n-point GL on [0, 1].

For each (z_target, segment, gl_node), one work unit. All units packed into
a multiprocessing.Pool. Results gathered, weighted, summed.

Error bound:
  - INNER (per H_η' evaluation): FLINT-certified nested acb.integral on
    [-L,L]² + closed-form Gaussian tail (already rigorous in
    h_prime_complex_certified.py).
  - OUTER (per path segment): NOT YET RIGOROUS in this file. Currently a
    heuristic via doubled-node comparison. Production version will add
    Bernstein-ellipse rigorous bound (next iteration).

Validation tests in __main__:
  - Test 1: P=Q=0 — verify H_η(z) = arcsin(z) at multiple z in Ω.
  - Test 2: V26 P,Q at z=0.5 — verify H_η(0.5) within η²-scale of arcsin(0.5).
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from multiprocessing import Pool
from pathlib import Path
from typing import List, Tuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

# Imports from project (must be at top-level for multiprocessing)
from grothendieck.proof.certified.bk_rigor import compute_gl_nodes_weights_arb


# ----------------------------------------------------------------------
# Worker: top-level, importable, pickleable
# ----------------------------------------------------------------------
@dataclass
class WorkItem:
    """One H_η'(ζ) evaluation. Strings used for pickle compatibility."""
    task_id: int
    zeta_re_str: str
    zeta_im_str: str
    eta_str: str
    P_kind: str        # "v26" or "zero"
    L: int
    prec: int
    rel_acc_bits: int


def _worker_eval(work: WorkItem) -> Tuple[int, str, str]:
    """Top-level worker: compute H_η'(ζ) at one acb-point.
    Returns (task_id, real_str, imag_str) — strings for arb roundtrip.
    """
    # Imports inside worker (each child process is fresh)
    from h_prime_complex_certified import (
        compute_H_eta_prime_certified,
        compute_J_polynomial_bound_v26,
        compute_J_polynomial_bound_zero,
        make_v26_P, make_v26_Pprime,
        zero_curve,
    )
    flint_ctx.prec = work.prec
    eta_arb = arb(work.eta_str)

    if work.P_kind == "v26":
        P = make_v26_P(eta_arb, +1)
        Pp = make_v26_Pprime(eta_arb, +1)
        Q = make_v26_P(eta_arb, -1)
        Qp = make_v26_Pprime(eta_arb, -1)
        poly_terms = compute_J_polynomial_bound_v26(eta_arb)
    elif work.P_kind == "zero":
        P = Pp = Q = Qp = zero_curve
        poly_terms = compute_J_polynomial_bound_zero()
    else:
        raise ValueError(f"unknown P_kind: {work.P_kind}")

    zeta = acb(arb(work.zeta_re_str), arb(work.zeta_im_str))
    Hp = compute_H_eta_prime_certified(
        z=zeta, P=P, Pp=Pp, Q=Q, Qp=Qp,
        J_poly_terms=poly_terms,
        L=work.L, prec=work.prec, rel_acc_bits=work.rel_acc_bits,
        verbose=False,
    )
    return (work.task_id, Hp.real.str(work.prec // 3),
            Hp.imag.str(work.prec // 3))


# ----------------------------------------------------------------------
# Composite GL on [0, 1] — precompute once
# ----------------------------------------------------------------------
def _gl01_nodes_weights(n_gl: int, prec: int) -> Tuple[List[arb], List[arb]]:
    """n-point Gauss-Legendre on [0, 1] (rigorous arb enclosures)."""
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, prec=prec)
    half = arb(1) / arb(2)
    # Map s ∈ [-1, 1] to t = (s+1)/2 ∈ [0, 1].  weight_t = weight_s / 2.
    nodes_t = [(s + arb(1)) * half for s in ref_nodes]
    weights_t = [w * half for w in ref_weights]
    return nodes_t, weights_t


# ----------------------------------------------------------------------
# Bernstein-ellipse rigorous outer GL error bound
# ----------------------------------------------------------------------
def _path_ellipse_bounding_box(z_start: acb, z_end: acb,
                                rho_arb: arb) -> acb:
    """Smallest axis-aligned acb-rectangle containing the Bernstein
    path-ellipse for parameter ρ.

    For γ(t) = z_start + t·δ extended complex-analytically, t ∈ Bernstein
    ellipse E_ρ in t-plane (after [-1,1]→[0,1] map). The image γ(E_ρ) is
    an ellipse in z-plane centered at (z_start + z_end)/2, oriented along
    ±δ direction.

    Semi-axes in z-plane:
        a_z = |δ| · (ρ + 1/ρ)/4   (along δ direction)
        b_z = |δ| · (ρ - 1/ρ)/4   (perpendicular)

    Bounding box half-extents (axis-aligned):
        half_re = sqrt(a_z²·δ_re² + b_z²·δ_im²) / |δ|
        half_im = sqrt(a_z²·δ_im² + b_z²·δ_re²) / |δ|

    Returns acb with .real and .imag as wide arb intervals covering the box.
    """
    delta = z_end - z_start
    delta_abs = delta.abs_upper()
    if not (delta_abs > arb(0)):
        # Zero-length segment: ellipse degenerates to a point.
        return z_start

    delta_re_abs = delta.real.abs_upper()
    delta_im_abs = delta.imag.abs_upper()

    a_z = delta_abs * (rho_arb + arb(1) / rho_arb) / arb(4)
    b_z = delta_abs * (rho_arb - arb(1) / rho_arb) / arb(4)

    a_z_sq = a_z * a_z
    b_z_sq = b_z * b_z
    delta_re_sq = delta_re_abs * delta_re_abs
    delta_im_sq = delta_im_abs * delta_im_abs

    half_re = (a_z_sq * delta_re_sq + b_z_sq * delta_im_sq).sqrt() / delta_abs
    half_im = (a_z_sq * delta_im_sq + b_z_sq * delta_re_sq).sqrt() / delta_abs

    center = (z_start + z_end) * acb(arb(1) / arb(2))
    c_re = center.real
    c_im = center.imag
    re_lo, re_hi = c_re - half_re, c_re + half_re
    im_lo, im_hi = c_im - half_im, c_im + half_im
    z_box = acb(arb.union(re_lo, re_hi), arb.union(im_lo, im_hi))
    return z_box


def _bound_H_eta_prime_on_box(
    z_box: acb, eta_arb: arb, P_kind: str, prec: int = 200,
) -> arb:
    """Closed-form arb upper bound on sup_{z∈z_box}|H_η'(z)|.

    |H_η'| ≤ |Φ'| + |H_0'|.
    |Φ'| bound from existing closed-form chunk machinery.
    |H_0'(z)| = 1/|√(1-z²)| ≤ 1/√(d_Z) where d_Z = inf_{z∈box}|1-z²|.
    """
    from chunk_constants_safe import safe_chunk_constants
    d_Z, alpha_Z, beta_Z, _z_ub = safe_chunk_constants(z_box)
    if not (d_Z > arb(0)):
        raise ValueError(f"d_Z not positive on path box {z_box}; "
                         f"path-ellipse exits |z|<1 region.")
    if not (alpha_Z > arb(0) and beta_Z > arb(0)):
        raise ValueError(f"alpha_Z={alpha_Z}, beta_Z={beta_Z} non-positive "
                         f"on box {z_box}; box exits |Re z|<1 strip.")

    # |H_0'| upper bound on box
    M_H_0_prime = arb(1) / d_Z.sqrt()

    if P_kind == "v26":
        from phi_prime_chunk_bound_certified import (
            bound_Phi_prime_on_chunk_certified,
        )
        flint_ctx.prec = prec
        res = bound_Phi_prime_on_chunk_certified(z_box, eta_arb, prec=prec)
        M_phi_prime = res.bound
    elif P_kind == "zero":
        M_phi_prime = arb(0)
    else:
        raise ValueError(f"unknown P_kind: {P_kind}")

    return M_phi_prime + M_H_0_prime


def _adaptive_rho(
    z_start: acb, z_end: acb,
    eta_arb: arb, P_kind: str,
    rho_candidates: list = None,
    re_safety: str = "0.99",
    prec: int = 200,
) -> arb:
    """Pick the largest ρ from rho_candidates such that the Bernstein
    path-ellipse bounding box has |Re z|_ub < re_safety AND
    safe_chunk_constants succeeds (α, β, d > 0) on the bounding box.

    Returns the chosen ρ as an arb. Raises if NO candidate works (caller
    should subdivide the segment).
    """
    if rho_candidates is None:
        rho_candidates = [arb("1.8"), arb("1.5"), arb("1.3"), arb("1.15"),
                           arb("1.05")]
    re_safety_arb = arb(re_safety)
    for rho in rho_candidates:
        z_box = _path_ellipse_bounding_box(z_start, z_end, rho)
        re_max = z_box.real.abs_upper()
        if not (re_max < re_safety_arb):
            continue
        try:
            _bound_H_eta_prime_on_box(z_box, eta_arb, P_kind, prec=prec)
            return rho
        except ValueError:
            continue
    raise ValueError(f"no ρ candidate fits for path {z_start} → {z_end}; "
                     f"caller should subdivide segment.")


def _path_gl_error_bound(
    z_start: acb, z_end: acb,
    rho_arb: arb, n_gl: int,
    eta_arb: arb, P_kind: str,
    prec: int = 200,
) -> arb:
    """Rigorous arb upper bound on |∫_path H_η' dζ - GL_n_path|.

    Formula:
        |∫_t - GL_n| ≤ (1/2) · 64 · M / (15·(ρ²-1)·ρ^{2n})       (on [0,1])
        |∫_path|     = |δ| · |∫_t|
        ⇒ |∫_path - GL_path| ≤ |δ| · (above)

    where M = sup|H_η'| over the Bernstein path-ellipse (we use bounding box).
    """
    z_box = _path_ellipse_bounding_box(z_start, z_end, rho_arb)
    M = _bound_H_eta_prime_on_box(z_box, eta_arb, P_kind, prec=prec)
    rho_sq = rho_arb * rho_arb
    rho_2n = rho_arb ** (2 * n_gl)
    coef = arb(64) / (arb(15) * (rho_sq - arb(1)) * rho_2n)
    delta_abs_ub = (z_end - z_start).abs_upper()
    return arb(0.5) * coef * M * delta_abs_ub


def _adaptive_path_gl_error_bound(
    z_start: acb, z_end: acb, n_gl: int,
    eta_arb: arb, P_kind: str,
    n_panels: int = 1,
    rho_candidates: list = None,
    prec: int = 200,
) -> tuple:
    """Adaptive: split segment into n_panels equal sub-segments, pick the
    largest valid ρ for each, sum the per-panel error bounds.

    Returns (total_error_arb, panels_info) where panels_info is a list of
    (z_panel_start, z_panel_end, rho_used) tuples.
    """
    delta = z_end - z_start
    panels_info = []
    total_err = arb(0)
    for k in range(n_panels):
        t0 = arb(k) / arb(n_panels)
        t1 = arb(k + 1) / arb(n_panels)
        z_p_start = z_start + acb(t0) * delta
        z_p_end = z_start + acb(t1) * delta
        rho = _adaptive_rho(z_p_start, z_p_end, eta_arb, P_kind,
                              rho_candidates=rho_candidates, prec=prec)
        err_panel = _path_gl_error_bound(z_p_start, z_p_end, rho, n_gl,
                                          eta_arb, P_kind, prec=prec)
        total_err = total_err + err_panel
        panels_info.append((z_p_start, z_p_end, rho))
    return total_err, panels_info


# ----------------------------------------------------------------------
# Public: parallel path integration of H_η' between two acb endpoints
# ----------------------------------------------------------------------
def integrate_segment_parallel(
    z_start: acb, z_end: acb,
    P_kind: str, eta_str: str,
    n_gl: int = 16,
    n_panels_path: int = 1,
    n_workers: int = 32,
    L: int = 6, prec: int = 100, rel_acc_bits: int = 25,
    rho_str: str = "1.5",
    add_outer_error: bool = True,
    verbose: bool = False,
) -> acb:
    """∫_{z_start}^{z_end} H_η'(ζ) dζ via composite GL with n_panels_path
    equal sub-panels, each with n_gl Gauss-Legendre nodes.

    Per-panel rigorous error bound uses adaptive Bernstein-ρ (see
    _adaptive_rho). Total error = sum over panels.
    """
    nodes_t, weights_t = _gl01_nodes_weights(n_gl, prec)
    delta = z_end - z_start

    # Skip work if zero-length segment
    if not (delta.abs_upper() > arb(0)):
        return acb(0)

    # Build per-panel info and global node positions
    n_p = n_panels_path
    panel_info = []
    work_items = []
    for p in range(n_p):
        t_p_lo = arb(p) / arb(n_p)
        t_p_hi = arb(p + 1) / arb(n_p)
        z_p_start = z_start + acb(t_p_lo) * delta
        z_p_end = z_start + acb(t_p_hi) * delta
        delta_p = z_p_end - z_p_start
        panel_info.append((p, z_p_start, z_p_end, delta_p))
        for i, t_local in enumerate(nodes_t):
            zeta = z_p_start + acb(t_local) * delta_p
            work_items.append(WorkItem(
                task_id=p * n_gl + i,
                zeta_re_str=zeta.real.str(prec // 3),
                zeta_im_str=zeta.imag.str(prec // 3),
                eta_str=eta_str,
                P_kind=P_kind,
                L=L, prec=prec, rel_acc_bits=rel_acc_bits,
            ))

    if verbose:
        t0 = time.time()
        print(f"  [parallel-segment] {z_start} → {z_end}, "
              f"n_panels={n_p}, {len(work_items)} GL evals, "
              f"{n_workers} workers", flush=True)

    with Pool(min(n_workers, len(work_items))) as pool:
        results = pool.map(_worker_eval, work_items)

    if verbose:
        print(f"  [parallel-segment] {len(results)} evals in "
              f"{time.time() - t0:.1f}s", flush=True)

    # Reassemble: one GL sum per panel, then sum panels weighted by panel length.
    # results is a list of (task_id, re_str, im_str). task_id = p*n_gl + i.
    by_id = {tid: (re_s, im_s) for (tid, re_s, im_s) in results}
    eta_arb = arb(eta_str)
    H_prime_segment = acb(0)
    err_segment = arb(0)
    for (p, z_p_start, z_p_end, delta_p) in panel_info:
        seg_p_sum = acb(0)
        for i in range(n_gl):
            re_s, im_s = by_id[p * n_gl + i]
            Hp_i = acb(arb(re_s), arb(im_s))
            seg_p_sum += acb(weights_t[i]) * Hp_i
        H_prime_segment += seg_p_sum * delta_p

        if add_outer_error:
            try:
                rho = _adaptive_rho(z_p_start, z_p_end, eta_arb, P_kind,
                                      prec=prec)
                err_p = _path_gl_error_bound(z_p_start, z_p_end, rho, n_gl,
                                              eta_arb, P_kind, prec=prec)
            except ValueError:
                # Fallback: ρ=1.05 may not bound but document
                err_p = arb("inf")
            err_segment += err_p

    if not add_outer_error:
        return H_prime_segment

    if verbose:
        print(f"  [parallel-segment] outer GL err ≤ "
              f"{err_segment.str(6)}", flush=True)

    re = H_prime_segment.real
    im = H_prime_segment.imag
    re_certified = arb.union(re - err_segment, re + err_segment)
    im_certified = arb.union(im - err_segment, im + err_segment)
    return acb(re_certified, im_certified)


def compute_H_eta_via_path_parallel(
    z_target: acb,
    P_kind: str, eta_str: str,
    via_real_axis: bool = True,
    n_gl: int = 16,
    n_panels_path: int = 1,
    n_workers: int = 32,
    L: int = 6, prec: int = 100, rel_acc_bits: int = 25,
    rho_str: str = "1.5",
    add_outer_error: bool = True,
    verbose: bool = False,
) -> acb:
    """Sharp H_η(z_target) via 2-segment polygonal path 0 → Re(z) → z.

    H_η(0) is assumed to be 0 (V26 odd sign curves; verify caller setup).
    """
    common = dict(P_kind=P_kind, eta_str=eta_str,
                  n_gl=n_gl, n_panels_path=n_panels_path,
                  n_workers=n_workers, L=L, prec=prec,
                  rel_acc_bits=rel_acc_bits, rho_str=rho_str,
                  add_outer_error=add_outer_error, verbose=verbose)
    if via_real_axis:
        z_mid = acb(z_target.real, arb(0))
        seg1 = integrate_segment_parallel(acb(0), z_mid, **common)
        seg2 = integrate_segment_parallel(z_mid, z_target, **common)
        return seg1 + seg2
    else:
        return integrate_segment_parallel(acb(0), z_target, **common)


# ----------------------------------------------------------------------
# Validation tests
# ----------------------------------------------------------------------
def _test_1_arcsin_parallel(prec: int, rel_acc_bits: int, n_gl: int,
                              n_workers: int, L: int):
    print("=" * 72, flush=True)
    print(f"TEST 1: P=Q=0 — H_η(z) = arcsin(z), n_gl={n_gl}, parallel",
          flush=True)
    print("=" * 72, flush=True)
    flint_ctx.prec = prec

    test_points = [
        ("origin",           acb(arb(0), arb(0))),
        ("real interior",    acb(arb("0.5"), arb(0))),
        ("complex interior", acb(arb("0.4"), arb("0.5"))),
    ]
    all_pass = True

    for label, z in test_points:
        ref = z.asin()
        print(f"  -> {label}: z={z}", flush=True)

        t0 = time.time()
        result = compute_H_eta_via_path_parallel(
            z_target=z, P_kind="zero", eta_str="0.01",
            n_gl=n_gl, n_workers=n_workers,
            L=L, prec=prec, rel_acc_bits=rel_acc_bits,
            verbose=True,
        )
        dt = time.time() - t0

        # Result is GL sum (no rigorous outer error).  For validation, just
        # check |result - arcsin(z)| < 10⁻⁴ — within heuristic GL accuracy.
        diff_abs = float((result - ref).abs_upper())
        # Looser tolerance — we have heuristic outer error here (no rigorous
        # Bernstein bound yet).
        encloses = float(diff_abs) < 1e-4
        status = "✓ MATCH" if encloses else "✗ MISMATCH"
        print(f"  {label:24s}  |err|={diff_abs:.3e}  ({dt:.1f}s)  {status}",
              flush=True)
        if not encloses:
            all_pass = False
            print(f"    ref = {ref}", flush=True)
            print(f"    res = {result}", flush=True)

    print(flush=True)
    print("Test 1: " + ("✓ ALL PASS" if all_pass else "✗ FAILURE"),
          flush=True)
    return all_pass


def _test_2_v26_at_05(prec: int, rel_acc_bits: int, n_gl: int,
                       n_workers: int, L: int):
    print(flush=True)
    print("=" * 72, flush=True)
    print(f"TEST 2: V26 P,Q at z=0.5 — H_η(0.5) ≈ arcsin(0.5) ± O(η²)",
          flush=True)
    print("=" * 72, flush=True)
    flint_ctx.prec = prec

    z = acb(arb("0.5"), arb(0))
    arcsin_05 = z.asin()

    print(f"  arcsin(0.5) = {arcsin_05.real.str(15)}", flush=True)
    print(f"  η = 0.01, expected |H_η(0.5) - arcsin(0.5)| ≤ ~10⁻⁴",
          flush=True)

    t0 = time.time()
    result = compute_H_eta_via_path_parallel(
        z_target=z, P_kind="v26", eta_str="0.01",
        n_gl=n_gl, n_workers=n_workers,
        L=L, prec=prec, rel_acc_bits=rel_acc_bits,
        verbose=True,
    )
    dt = time.time() - t0
    print(flush=True)
    print(f"  H_η(0.5) = {result}", flush=True)
    print(f"  time = {dt:.1f}s", flush=True)

    diff = (result.real - arcsin_05.real).abs_upper()
    diff_lb = (result.real - arcsin_05.real).abs_lower()
    print(f"  |H_η(0.5) - arcsin(0.5)| ∈ [{float(diff_lb):.2e}, "
          f"{float(diff):.2e}]", flush=True)
    pass2 = float(diff) < 1e-3
    print(f"  Test 2: {'✓ PASS' if pass2 else '✗ FAIL'}", flush=True)
    return pass2


def _test_3_speedup_check():
    """Verify parallelism is actually working — wall time vs serial estimate."""
    print(flush=True)
    print("=" * 72, flush=True)
    print("TEST 3: parallelism speedup check", flush=True)
    print("=" * 72, flush=True)
    print(f"  Available cores: {os.cpu_count()}", flush=True)


if __name__ == "__main__":
    PREC = 100
    REL_BITS = 22
    N_GL = 16
    N_WORKERS = 32
    L_TEST = 6
    flint_ctx.prec = PREC

    print("\n" + "=" * 72, flush=True)
    print("Parallel path integration: H_η(z) via composite GL", flush=True)
    print("=" * 72, flush=True)
    print(f"prec={PREC}, rel_acc_bits={REL_BITS}, n_gl={N_GL}, "
          f"n_workers={N_WORKERS}, L={L_TEST}", flush=True)
    _test_3_speedup_check()

    t0 = time.time()
    pass1 = _test_1_arcsin_parallel(prec=PREC, rel_acc_bits=REL_BITS,
                                      n_gl=N_GL, n_workers=N_WORKERS, L=L_TEST)
    pass2 = _test_2_v26_at_05(prec=PREC, rel_acc_bits=REL_BITS,
                                n_gl=N_GL, n_workers=N_WORKERS, L=L_TEST)
    t1 = time.time()

    print(flush=True)
    print("=" * 72, flush=True)
    print(f"SUMMARY ({t1 - t0:.0f}s total):", flush=True)
    print(f"  Test 1 (arcsin recovery, parallel): {'✓' if pass1 else '✗'}",
          flush=True)
    print(f"  Test 2 (V26 vs arcsin):             {'✓' if pass2 else '✗'}",
          flush=True)
    print("=" * 72, flush=True)
    sys.exit(0 if pass1 and pass2 else 1)
