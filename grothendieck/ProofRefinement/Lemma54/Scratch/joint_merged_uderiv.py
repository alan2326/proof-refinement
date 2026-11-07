"""Joint per-(p, w)-cell oracle for merged_uderiv.

Step 10.4 of SESSION_HANDOFF.md plan.

Computes a rigorous arb upper bound on
    Cr = (1/2) · sup_{(p, w) ∈ [0, p_max] × ∂Ω}  |numerator(p, w)| / |D(p, w)|³
where
    numerator = 2 · Φ(w) · Φ'(w) · D(p, w) − DD(p, w) · Φ(w)²
    D(p, w)   = H_0'(w) + p · Φ'(w)
    DD(p, w)  = H_0''(w) + p · Φ''(w)

Strategy:
  • Load per-chunk sharp values (Φ(c), Φ'(c)) and chunk bound M_2 ≥
    sup|H_η''| from the parallel chunk certifier output.
  • For each (chunk, p-cell), evaluate the formula at midpoint
    (c_chunk, p_mid) using sharp values, treating |Φ''| via interval
    arithmetic with [-M_2_phi, +M_2_phi].
  • Add Lipschitz padding for w-variation across the chunk: every
    quantity (Φ, Φ', H_0, H_0', H_0'', Φ'') is replaced by its enclosing
    arb-interval over the chunk:
        Φ(w)  ∈ Φ(c) ± chunk_radius · sup_{w}|Φ'(w)|     (= sharp + radius·M_phi_p)
        Φ'(w) ∈ Φ'(c) ± chunk_radius · sup_{w}|Φ''(w)|   (= sharp + radius·M_2_phi)
        ...
  • Take max over all cells.

This recovers the V26 sign-cancellation in the numerator that the
triangle decomposition of Step 3b lost.

Output: certified Cr.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import List

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))


# --------------------- Closed-form H_0 and derivatives -----------------
def _h0_closed(z: acb) -> acb:
    """H_0(z) = arcsin(z) (closed form via acb)."""
    return z.asin()


def _h0_prime_closed(z: acb) -> acb:
    """H_0'(z) = 1/√(1-z²)."""
    return acb(1) / (acb(1) - z * z).sqrt()


def _h0_pp_closed(z: acb) -> acb:
    """H_0''(z) = z/(1-z²)^{3/2}."""
    one_minus_z2 = acb(1) - z * z
    return z / (one_minus_z2 * one_minus_z2.sqrt())


# --------------------- Chunk-bound interval Φ', Φ'', Φ -----------------
def _phi_pp_min_bound(z_box: acb, eta_arb: arb, sup_H0pp: arb,
                       prec: int) -> arb:
    """min(η²-tight Φ'' bound, |H_η''|+|H_0''| triangle bound)."""
    from h_eta_pp_chunk_bound_certified import (
        bound_H_eta_pp_on_chunk_certified,
    )
    from phi_pp_chunk_bound_eta_tight import (
        bound_Phi_pp_eta_tight_certified,
    )
    M_h_eta_pp = bound_H_eta_pp_on_chunk_certified(z_box, eta_arb,
                                                     prec=prec).bound
    M_phi_pp_triangle = M_h_eta_pp + sup_H0pp
    try:
        M_phi_pp_eta_tight = bound_Phi_pp_eta_tight_certified(
            z_box, eta_arb, prec=prec).bound
    except ValueError:
        M_phi_pp_eta_tight = arb("inf")
    if M_phi_pp_eta_tight.upper() < M_phi_pp_triangle.upper():
        return M_phi_pp_eta_tight
    return M_phi_pp_triangle


def _phi_ppp_cauchy_bound(c_re: arb, c_im: arb, hr: arb, hi: arb,
                            eta_arb: arb, prec: int) -> arb:
    """Cauchy-derived sup|Φ'''(z)| over chunk Z:
        sup_Z |Φ'''| ≤ (1/ρ) · sup_{Z^{+ρ}} |Φ''|
    where Z^{+ρ} is Z grown by ρ in real and imag directions.
    Pick the best ρ from a small candidate set, keeping Z^{+ρ} inside
    the strip |Re z| < 1.
    """
    from chunk_constants_safe import safe_chunk_constants  # noqa: F401

    re_lo = c_re - hr
    re_hi = c_re + hr
    abs_re_max = arb.max(re_lo.abs_upper(), re_hi.abs_upper())
    rho_strip_max = (arb(1) - abs_re_max) * arb("0.45")

    candidates = [arb("0.005"), arb("0.01"), arb("0.02"),
                  arb("0.04"), arb("0.06"), arb("0.08")]

    best = arb("inf")
    for rho in candidates:
        if not (rho > arb(0) and rho < rho_strip_max):
            continue
        z_big = acb(arb.union(c_re - hr - rho, c_re + hr + rho),
                     arb.union(c_im - hi - rho, c_im + hi + rho))
        try:
            d_Z_big, _, _, z_ub_big = safe_chunk_constants(z_big)
        except Exception:
            continue
        if not (d_Z_big > arb(0)):
            continue
        sqrt_dZ_big = d_Z_big.sqrt()
        sup_H0pp_big = z_ub_big / (d_Z_big * sqrt_dZ_big)
        try:
            M_pp_big = _phi_pp_min_bound(z_big, eta_arb, sup_H0pp_big,
                                          prec)
        except Exception:
            continue
        cand = M_pp_big / rho
        if cand.upper() < best.upper():
            best = cand
    return best


def _chunk_sup_bounds(z_box: acb, eta_arb: arb, c_re: arb, c_im: arb,
                       hr: arb, hi: arb, prec: int) -> dict:
    """Closed-form arb upper bounds on sup_{z ∈ z_box}|·| for several
    quantities, plus inf bounds on |H_0'|, |H_0''|, and a Cauchy-derived
    sup|Φ'''|.

    H_0 derivatives:
        sup|H_0'(z)|   ≤ 1/√(inf|1-z²|) = 1/√d_Z
        sup|H_0''(z)|  ≤ |z|_ub / d_Z^{3/2}
        sup|H_0'''(z)| ≤ (1 + 2|z|_ub²) / d_Z^{5/2}
    Reverse direction (using sup|1-z²|):
        inf|H_0'(z)|   ≥ 1/√(sup|1-z²|)
        inf|H_0''(z)|  ≥ inf|z| / sup|1-z²|^{3/2}
    """
    from phi_prime_chunk_bound_certified import (
        bound_Phi_prime_on_chunk_certified,
    )
    from h_eta_pp_chunk_bound_certified import (
        bound_H_eta_pp_on_chunk_certified,
    )
    from chunk_constants_safe import safe_chunk_constants
    flint_ctx.prec = prec

    d_Z, _, _, z_ub = safe_chunk_constants(z_box)
    if not (d_Z > arb(0)):
        raise ValueError(f"d_Z not positive: {d_Z}")

    sqrt_dZ = d_Z.sqrt()
    dZ_3half = d_Z * sqrt_dZ
    dZ_5half = dZ_3half * d_Z

    sup_H0p = arb(1) / sqrt_dZ
    sup_H0pp = z_ub / dZ_3half
    sup_H0ppp = (arb(1) + arb(2) * z_ub * z_ub) / dZ_5half

    # inf|1-z²| over chunk → upper bound on |1-z²|^{1/2}
    one_minus_z_sq = acb(1) - z_box * z_box
    sup_abs_1_minus_z2 = one_minus_z_sq.abs_upper()
    if sup_abs_1_minus_z2 > arb(0):
        inf_H0p = arb(1) / sup_abs_1_minus_z2.sqrt()
    else:
        inf_H0p = arb(0)
    # |z|_lb for inf|H_0''|. acb has no abs_lower; use re_lo² + im_lo² lb.
    re_lo = z_box.real
    im_lo = z_box.imag
    re_abs_lb = arb.max(re_lo.lower(), -re_lo.upper())  # |re|.lower
    if re_abs_lb < arb(0):
        re_abs_lb = arb(0)  # interval crosses 0 in Re → |re|.lower = 0
    im_abs_lb = arb.max(im_lo.lower(), -im_lo.upper())
    if im_abs_lb < arb(0):
        im_abs_lb = arb(0)
    z_lb = (re_abs_lb * re_abs_lb + im_abs_lb * im_abs_lb).sqrt()
    if sup_abs_1_minus_z2 > arb(0):
        sup_abs_1_minus_z2_3half = (sup_abs_1_minus_z2
                                      * sup_abs_1_minus_z2.sqrt())
        inf_H0pp = z_lb / sup_abs_1_minus_z2_3half
    else:
        inf_H0pp = arb(0)

    M_phi_p = bound_Phi_prime_on_chunk_certified(z_box, eta_arb,
                                                    prec=prec).bound
    M_h_eta_pp = bound_H_eta_pp_on_chunk_certified(z_box, eta_arb,
                                                     prec=prec).bound
    M_phi_pp = _phi_pp_min_bound(z_box, eta_arb, sup_H0pp, prec)

    # Cauchy-derived sup|Φ'''|
    M_phi_ppp = _phi_ppp_cauchy_bound(c_re, c_im, hr, hi, eta_arb, prec)

    return {
        "d_Z": d_Z,
        "z_ub": z_ub,
        "sup_H0p": sup_H0p,
        "sup_H0pp": sup_H0pp,
        "sup_H0ppp": sup_H0ppp,
        "inf_H0p": inf_H0p,
        "inf_H0pp": inf_H0pp,
        "M_phi_p": M_phi_p,
        "M_h_eta_pp": M_h_eta_pp,
        "M_phi_pp": M_phi_pp,
        "M_phi_ppp": M_phi_ppp,
    }


def _inflate_acb(value: acb, pad: arb) -> acb:
    """Return acb-ball that contains value ± pad (added to both real and
    imag parts as a Lipschitz pad)."""
    re = value.real
    im = value.imag
    return acb(arb.union(re - pad, re + pad),
                arb.union(im - pad, im + pad))


def _acb_abs_box(M: arb) -> acb:
    """Return an acb interval [-M, +M] + i·[-M, +M] enclosing every complex
    number with modulus ≤ M (in fact every value with |re|, |im| ≤ M).
    Used as a rigorous direct enclosure when only sup|·| is known."""
    return acb(arb.union(-M, M), arb.union(-M, M))


# --------------------- Joint oracle per (chunk, p-cell) ----------------
def _eval_merged_at_cell(
    H_eta_re: arb, H_eta_im: arb,
    Hp_re: arb, Hp_im: arb,
    Hpp_re: arb, Hpp_im: arb,
    c_re: arb, c_im: arb,
    half_re: arb, half_im: arb,
    chunk_sup: dict,
    p_mid: arb, p_rad: arb,
    prec: int,
    chunk_w_pad: bool = True,
) -> arb:
    """Upper bound on |numerator(p, w)| / |D(p, w)|³ over (p, w) ∈
    [p_mid - p_rad, p_mid + p_rad] × chunk_box.

    With chunk_w_pad=True (default, fully rigorous):
        2nd-order Taylor pad (uses sharp Φ'(c), Φ''(c) plus M_phi_ppp Cauchy):
            Φ(w)   = Φ(c) + dz·Φ'(c) + (dz²/2)·Φ''(c) + R₃,  |R₃| ≤ r³/6 · M₃
            Φ'(w)  = Φ'(c) + dz·Φ''(c) + R₂,                |R₂| ≤ r²/2 · M₃
            Φ''(w) = Φ''(c) + R₁,                          |R₁| ≤ r · M₃
            (also fall back to Φ''(w) ∈ box(M_phi_pp) if tighter)
        H_0', H_0'' use 1st-order Lipschitz pad (analytic, can refine later).
        Denominator uses |D(p,w)| ≥ inf|H_0'| - p_hi · M_phi_p, so its lower
        bound is independent of the (wider) Φ' interval.
        Score is min(interval-numerator / denom³, norm-numerator / denom³).

    With chunk_w_pad=False (indicative midpoint-only, NOT rigorous-over-chunk):
        Evaluates merged_uderiv at sharp midpoint w=c with sharp Φ, Φ', Φ''.
    """
    flint_ctx.prec = prec

    # Sharp values at midpoint c
    c = acb(c_re, c_im)
    H_eta_c = acb(H_eta_re, H_eta_im)
    Hp_c = acb(Hp_re, Hp_im)
    Hpp_c = acb(Hpp_re, Hpp_im)
    H0_c = _h0_closed(c)
    H0p_c = _h0_prime_closed(c)
    H0pp_c = _h0_pp_closed(c)
    Phi_mid = H_eta_c - H0_c
    Phi_p_mid = Hp_c - H0p_c
    Phi_pp_mid = Hpp_c - H0pp_c

    p_hi = p_mid + p_rad
    p_arb = arb.union(p_mid - p_rad, p_mid + p_rad)

    if not chunk_w_pad:
        Phi = Phi_mid
        Phi_p = Phi_p_mid
        Phi_pp = Phi_pp_mid
        H0p = H0p_c
        H0pp = H0pp_c
        # Midpoint-only: just evaluate the rational expression
        D = H0p + acb(p_arb) * Phi_p
        DD = H0pp + acb(p_arb) * Phi_pp
        Phi_sq = Phi * Phi
        numer = acb(2) * Phi * Phi_p * D - DD * Phi_sq
        denom = D * D * D
        abs_denom_lb = denom.abs_lower()
        if not (abs_denom_lb > arb(0)):
            return arb("inf")
        return numer.abs_upper() / abs_denom_lb

    # ---- chunk_w_pad=True: rigorous over (p, w) ∈ p-cell × chunk ----
    # 2nd-order Taylor pad in w using sharp Φ'(c), Φ''(c) and M_phi_ppp.
    chunk_radius = (half_re * half_re + half_im * half_im).sqrt()
    r = chunk_radius
    r2 = r * r
    r3 = r2 * r
    M2 = chunk_sup["M_phi_pp"]
    M3 = chunk_sup["M_phi_ppp"]

    dz = acb(arb.union(-half_re, half_re), arb.union(-half_im, half_im))
    half_arb = arb(1) / arb(2)
    sixth_arb = arb(1) / arb(6)

    # Φ(w):  Φ(c) + dz·Φ'(c) + (dz²/2)·Φ''(c)  ± r³/6 · M_phi_ppp
    Phi_taylor = Phi_mid + dz * Phi_p_mid + (dz * dz) * Phi_pp_mid * acb(half_arb)
    pad_phi = r3 * M3 * sixth_arb
    Phi = _inflate_acb(Phi_taylor, pad_phi)

    # Φ'(w): Φ'(c) + dz·Φ''(c) ± r²/2 · M_phi_ppp
    Phi_p_taylor = Phi_p_mid + dz * Phi_pp_mid
    pad_phi_p = r2 * M3 * half_arb
    Phi_p = _inflate_acb(Phi_p_taylor, pad_phi_p)

    # Φ''(w): Φ''(c) ± r · M_phi_ppp.  Or direct box(M_phi_pp).  Take tighter.
    pad_phi_pp = r * M3
    Phi_pp_taylor = _inflate_acb(Phi_pp_mid, pad_phi_pp)
    Phi_pp_box = _acb_abs_box(M2)
    if Phi_pp_taylor.abs_upper().upper() < Phi_pp_box.abs_upper().upper():
        Phi_pp = Phi_pp_taylor
    else:
        Phi_pp = Phi_pp_box

    # H_0', H_0'' Lipschitz pad
    pad_H0p = r * chunk_sup["sup_H0pp"]
    pad_H0pp = r * chunk_sup["sup_H0ppp"]
    H0p = _inflate_acb(H0p_c, pad_H0p)
    H0pp = _inflate_acb(H0pp_c, pad_H0pp)

    # ---- Denominator lower bound (LLM patch #1) ----
    # |D(p,w)| ≥ inf|H_0'(w)| - p_hi · sup|Φ'(w)|.
    # Use chunk-bound M_phi_p (no dependency blow-up).
    D_abs_lb = chunk_sup["inf_H0p"] - p_hi * chunk_sup["M_phi_p"]
    if not (D_abs_lb > arb(0)):
        return arb("inf")
    denom_lb = D_abs_lb * D_abs_lb * D_abs_lb

    # ---- Numerator: take min of interval form and norm form ----
    # Interval form (preserves sign cancellation when intervals tight):
    D = H0p + acb(p_arb) * Phi_p
    DD = H0pp + acb(p_arb) * Phi_pp
    Phi_sq = Phi * Phi
    numer_interval = acb(2) * Phi * Phi_p * D - DD * Phi_sq
    score_interval = numer_interval.abs_upper() / denom_lb

    # Norm form (no dependency blow-up, but no cancellation):
    Phi_abs = Phi.abs_upper()
    Phi_p_abs_taylor = Phi_p.abs_upper()
    # Cap by chunk bound where it's tighter
    Phi_p_abs = Phi_p_abs_taylor
    if chunk_sup["M_phi_p"].upper() < Phi_p_abs_taylor.upper():
        Phi_p_abs = chunk_sup["M_phi_p"]
    D_abs_ub = chunk_sup["sup_H0p"] + p_hi * chunk_sup["M_phi_p"]
    DD_abs_ub = chunk_sup["sup_H0pp"] + p_hi * chunk_sup["M_phi_pp"]
    score_norm = (
        arb(2) * Phi_abs * Phi_p_abs * D_abs_ub
        + DD_abs_ub * Phi_abs * Phi_abs
    ) / denom_lb

    if score_interval.upper() < score_norm.upper():
        return score_interval
    return score_norm


# --------------------- Main: compose Cr from chunk certifier output ----
def compose_cr_from_chunks(
    chunks_json_path: Path,
    n_p_cells: int = 16,
    p_max_str: str = "1",
    prec: int = 100,
    chunk_w_pad: bool = True,
    verbose: bool = True,
) -> dict:
    """Load chunk-certifier output and compute joint-oracle Cr.

    Returns dict with Cr value, max-cell info, per-cell scores.
    """
    flint_ctx.prec = prec

    with open(chunks_json_path) as f:
        data = json.load(f)
    eta_arb = arb(data["params"]["eta"])
    p_max = arb(p_max_str)

    n_chunks = len(data["chunks"])
    if verbose:
        print(f"[joint-oracle] Loaded {n_chunks} chunks from "
              f"{chunks_json_path}", flush=True)

    # Pre-compute closed-form chunk sup bounds for each chunk
    chunk_intervals = []
    for ch in data["chunks"]:
        c_re = arb(ch["center_re"])
        c_im = arb(ch["center_im"])
        hr = arb(ch["half_re"])
        hi = arb(ch["half_im"])
        z_box = acb(arb.union(c_re - hr, c_re + hr),
                     arb.union(c_im - hi, c_im + hi))
        try:
            sup_bounds = _chunk_sup_bounds(z_box, eta_arb, c_re, c_im,
                                             hr, hi, prec)
        except Exception as e:
            if verbose:
                print(f"  chunk {ch['chunk_id']}: chunk sup ERROR {e}",
                      flush=True)
            sup_bounds = {
                "d_Z": arb(0), "z_ub": arb("inf"),
                "sup_H0p": arb("inf"), "sup_H0pp": arb("inf"),
                "sup_H0ppp": arb("inf"),
                "inf_H0p": arb(0), "inf_H0pp": arb(0),
                "M_phi_p": arb("inf"), "M_h_eta_pp": arb("inf"),
                "M_phi_pp": arb("inf"), "M_phi_ppp": arb("inf"),
            }
        chunk_intervals.append({"ch": ch, "sup": sup_bounds})

    # Iterate over (chunk, p-cell)
    p_lo_arr = []
    for k in range(n_p_cells):
        p_lo = p_max * arb(k) / arb(n_p_cells)
        p_hi = p_max * arb(k + 1) / arb(n_p_cells)
        p_lo_arr.append((p_lo, p_hi))

    max_score = arb(0)
    max_info = None
    cell_scores = []

    for ci in chunk_intervals:
        ch = ci["ch"]
        H_eta_re = arb(ch["H_eta_re"])
        H_eta_im = arb(ch["H_eta_im"])
        Hp_re = arb(ch["Hp_re"])
        Hp_im = arb(ch["Hp_im"])
        # H_η''(c) sharp values from chunk certifier; default to 0 if missing
        Hpp_re = arb(ch.get("Hpp_re", "0"))
        Hpp_im = arb(ch.get("Hpp_im", "0"))
        c_re = arb(ch["center_re"])
        c_im = arb(ch["center_im"])
        hr = arb(ch["half_re"])
        hi = arb(ch["half_im"])

        for k, (p_lo, p_hi) in enumerate(p_lo_arr):
            p_mid = (p_lo + p_hi) / arb(2)
            p_rad = (p_hi - p_lo) / arb(2)
            score = _eval_merged_at_cell(
                H_eta_re, H_eta_im, Hp_re, Hp_im,
                Hpp_re, Hpp_im,
                c_re, c_im, hr, hi,
                ci["sup"],
                p_mid, p_rad, prec,
                chunk_w_pad=chunk_w_pad,
            )
            cell_scores.append({
                "chunk_id": ch["chunk_id"],
                "p_cell": k,
                "score": score.str(8),
            })
            if score.upper() > max_score.upper():
                max_score = score
                max_info = (ch["chunk_id"], ch["edge"], k,
                            float(p_mid.upper()))

    Cr = max_score / arb(2)

    if verbose:
        print(f"[joint-oracle] max_score = {max_score.str(8)}", flush=True)
        print(f"[joint-oracle] max_info  = {max_info}", flush=True)
        print(f"[joint-oracle] Cr_certified = {Cr.str(8)}", flush=True)

    return {
        "n_chunks": n_chunks,
        "n_p_cells": n_p_cells,
        "Cr_str": Cr.str(20, more=True),
        "Cr_float": float(Cr.upper()),
        "max_score_str": max_score.str(20, more=True),
        "max_info": max_info,
        "cell_scores": cell_scores,
    }


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunks", type=str,
        default=str(_HERE.parent / "Cache" /
                    "v26_chunk_certifier_npe16.json"))
    parser.add_argument("--n_p_cells", type=int, default=16)
    parser.add_argument("--midpoint_only", action="store_true",
        help="Skip chunk-w Lipschitz padding (NOT RIGOROUS — indicative only)")
    args = parser.parse_args()

    result = compose_cr_from_chunks(
        chunks_json_path=Path(args.chunks),
        n_p_cells=args.n_p_cells,
        chunk_w_pad=not args.midpoint_only,
    )
    suffix = "_midpoint" if args.midpoint_only else "_rigorous"
    out_path = Path(args.chunks).parent / f"joint_merged_cr{suffix}.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)
    print(f"[joint-oracle] Saved → {out_path}", flush=True)
