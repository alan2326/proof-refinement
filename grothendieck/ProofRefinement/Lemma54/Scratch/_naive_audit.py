"""Faithful audit of V9-V26 candidates: compute the *actual* value of
each candidate's score formula using truncation-free oracles applied to
the cached chunks output (production or subdivided).

For each candidate V_K, we look up the exact `Cr_phi_*` formula that
the candidate's Lean file uses, then evaluate it with patched (no K_max
truncation) oracle values computed from the cached chunk JSON.

V14-V24's `joint_phi_phip_invD2` and `uzz_phi_sq` are computed
*per-cell* (chunk × p-cell) using the same 2nd-order Taylor pad that
joint_merged_uderiv.py uses for the merged numerator. This makes the
audit's V14-V24 numbers directly comparable to V25/V26's merged number,
i.e. V24's audit value ≥ V26's audit value as required by triangle.

Formulas (verbatim from `Proof/Lib/Lemma54_Paper.lean`):
  Cr_phi(r, M_phi, M_phi_prime, R) =
      M_phi · M_phi_prime · invFp² + (4R/(1-r)²) · M_phi²
      where invFp = 2R/(1-r)
  Cr_phi_invD(r, M_phi, M_phi_prime, R, inv_F_p_z) =
      M_phi · M_phi_prime · inv_F_p_z² + (4R/(1-r)²) · M_phi²
  Cr_phi_uzz(_, M_phi, M_phi_prime, inv_F_p_z, M_pp) =
      M_phi · M_phi_prime · inv_F_p_z² + (1/2) · M_pp · inv_F_p_z³ · M_phi²
  Cr_phi_uzz_direct(_, M_phi, M_phi_prime, inv_F_p_z, u_zz_bound) =
      M_phi · M_phi_prime · inv_F_p_z² + (1/2) · u_zz_bound · M_phi²
  Cr_phi_uzz_direct_joint(_, M_phi, joint, u_zz_bound) =
      joint + (1/2) · u_zz_bound · M_phi²
  Cr_phi_uzz_direct_joint2(joint, uzz_phi_sq) =
      joint + (1/2) · uzz_phi_sq
  Cr_phi_uzz_merged(merged_uderiv) =
      (1/2) · merged_uderiv

Constants: r = 23/25, R = 23/20 (R_val_paper r ≤ 23/20), p_max = 1.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))


def _eval_three_at_cell(
    H_eta_re: arb, H_eta_im: arb,
    Hp_re: arb, Hp_im: arb,
    Hpp_re: arb, Hpp_im: arb,
    c_re: arb, c_im: arb,
    half_re: arb, half_im: arb,
    chunk_sup: dict,
    p_mid: arb, p_rad: arb,
    prec: int,
):
    """Compute three sups at a single (chunk, p-cell):
       - score_joint     = sup |Phi · Phi' / D²| over (p, w)
       - score_uzz_phi_sq= sup |DD · Phi² / D³|
       - score_merged    = sup |2·Phi·Phi'·D - DD·Phi²| / |D|³
    using the same 2nd-order Taylor pad in w and joint p-interval
    arithmetic as joint_merged_uderiv.py.

    Each sup is min(interval-form, triangle-norm-form) so we capture
    cancellation when intervals are tight.
    """
    from joint_merged_uderiv import (_h0_closed, _h0_prime_closed,
                                       _h0_pp_closed, _inflate_acb,
                                       _acb_abs_box)
    flint_ctx.prec = prec

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

    # 2nd-order Taylor pad in w
    chunk_radius = (half_re * half_re + half_im * half_im).sqrt()
    r = chunk_radius
    r2 = r * r
    r3 = r2 * r
    M2 = chunk_sup["M_phi_pp"]
    M3 = chunk_sup["M_phi_ppp"]

    dz = acb(arb.union(-half_re, half_re), arb.union(-half_im, half_im))
    half_arb = arb(1) / arb(2)
    sixth_arb = arb(1) / arb(6)

    # Φ(w):  Φ(c) + dz·Φ'(c) + (dz²/2)·Φ''(c)  ± r³/6·M_phi_ppp
    Phi_taylor = Phi_mid + dz * Phi_p_mid + (dz * dz) * Phi_pp_mid * acb(half_arb)
    pad_phi = r3 * M3 * sixth_arb
    Phi = _inflate_acb(Phi_taylor, pad_phi)

    # Φ'(w): Φ'(c) + dz·Φ''(c) ± r²/2·M_phi_ppp
    Phi_p_taylor = Phi_p_mid + dz * Phi_pp_mid
    pad_phi_p = r2 * M3 * half_arb
    Phi_p = _inflate_acb(Phi_p_taylor, pad_phi_p)

    # Φ''(w): min(Taylor pad ±r·M_phi_ppp, direct box(M_phi_pp))
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

    # Denominator lower bound (joint over p ∈ p-cell, w ∈ chunk)
    D_abs_lb = chunk_sup["inf_H0p"] - p_hi * chunk_sup["M_phi_p"]
    if not (D_abs_lb > arb(0)):
        return {"joint": arb("inf"), "uzz_phi_sq": arb("inf"),
                 "merged": arb("inf")}

    D_lb_sq = D_abs_lb * D_abs_lb
    D_lb_cu = D_lb_sq * D_abs_lb

    # D, DD intervals (joint over p)
    D = H0p + acb(p_arb) * Phi_p
    DD = H0pp + acb(p_arb) * Phi_pp

    # ---- Norm-form bounds for each quantity ----
    Phi_abs = Phi.abs_upper()
    Phi_p_abs_taylor = Phi_p.abs_upper()
    Phi_p_abs = Phi_p_abs_taylor
    if chunk_sup["M_phi_p"].upper() < Phi_p_abs_taylor.upper():
        Phi_p_abs = chunk_sup["M_phi_p"]
    DD_abs_ub = chunk_sup["sup_H0pp"] + p_hi * chunk_sup["M_phi_pp"]

    # --- joint = |Phi·Phi'/D²| ---
    score_joint_norm = Phi_abs * Phi_p_abs / D_lb_sq
    Phi_Phi_p = Phi * Phi_p
    score_joint_interval = Phi_Phi_p.abs_upper() / D_lb_sq
    score_joint = score_joint_interval if (
        score_joint_interval.upper() < score_joint_norm.upper()
    ) else score_joint_norm

    # --- uzz_phi_sq = |DD·Phi²/D³| ---
    Phi_sq = Phi * Phi
    score_uzz_norm = DD_abs_ub * Phi_abs * Phi_abs / D_lb_cu
    score_uzz_interval = (DD * Phi_sq).abs_upper() / D_lb_cu
    score_uzz = score_uzz_interval if (
        score_uzz_interval.upper() < score_uzz_norm.upper()
    ) else score_uzz_norm

    # --- merged = |2·Phi·Phi'·D - DD·Phi²|/D³ ---
    # Norm form on merged: triangle (no cancellation), but use 1/D_lb²
    # for the joint piece (tighter than the original oracle's |D|_ub/D_lb³).
    score_merged_norm = (
        arb(2) * Phi_abs * Phi_p_abs / D_lb_sq
        + DD_abs_ub * Phi_abs * Phi_abs / D_lb_cu
    )
    numer_interval = acb(2) * Phi_Phi_p * D - DD * Phi_sq
    score_merged_interval = numer_interval.abs_upper() / D_lb_cu
    score_merged = score_merged_interval if (
        score_merged_interval.upper() < score_merged_norm.upper()
    ) else score_merged_norm

    return {"joint": score_joint, "uzz_phi_sq": score_uzz,
             "merged": score_merged}


def main():
    flint_ctx.prec = 200
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--chunks", type=Path,
        default=Path("/home/rsaha/projects/grothendieck/ProofRefinement/"
                      "Lemma54/Cache/Backups/2026-05-03_subdivision/"
                      "round3_v26_corner_split_v3.json"))
    parser.add_argument("--n_p_cells", type=int, default=8)
    parser.add_argument("--out", type=Path,
        default=Path("/home/rsaha/projects/grothendieck/ProofRefinement/"
                      "Lemma54/Cache/Backups/2026-05-03_subdivision/"
                      "audit_naive_results.json"))
    parser.add_argument("--label", type=str, default="round3_subdivided")
    args = parser.parse_args()

    print(f"[audit] chunks: {args.chunks}", flush=True)
    data = json.load(open(args.chunks))
    chunks = data["chunks"]

    # Paper constants
    r_val = arb("23") / arb("25")
    R_val = arb("23") / arb("20")
    one_minus_r = arb(1) - r_val
    invFp_paper = arb(2) * R_val / one_minus_r
    coef_term2_paper = arb(4) * R_val / (one_minus_r * one_minus_r)
    p_max = arb(1)

    print(f"[audit] r=23/25, R=23/20, "
          f"invFp_paper={float(invFp_paper.upper()):.4f}, "
          f"coef_term2={float(coef_term2_paper.upper()):.4f}")
    print(f"[audit] n_p_cells={args.n_p_cells}, p_max=1")

    from joint_merged_uderiv import (_chunk_sup_bounds,
                                       _h0_closed, _h0_prime_closed,
                                       _h0_pp_closed)

    eta_arb = arb(data["params"]["eta"])
    n_chunks = len(chunks)
    print(f"[audit] processing {n_chunks} chunks, computing chunk sup bounds...",
          flush=True)

    # Pre-compute chunk-level data
    chunk_data = []
    for i, ch in enumerate(chunks):
        if i % 16 == 0:
            print(f"  chunk_sup {i}/{n_chunks}", flush=True)
        c_re = arb(ch["center_re"])
        c_im = arb(ch["center_im"])
        hr = arb(ch["half_re"])
        hi = arb(ch["half_im"])
        z_box = acb(arb.union(c_re - hr, c_re + hr),
                     arb.union(c_im - hi, c_im + hi))
        try:
            sup = _chunk_sup_bounds(z_box, eta_arb, c_re, c_im, hr, hi, 200)
        except Exception as e:
            print(f"  chunk {ch['chunk_id']}: sup ERROR {e}", flush=True)
            continue
        chunk_data.append({"ch": ch, "sup": sup,
                             "c_re": c_re, "c_im": c_im, "hr": hr, "hi": hi})

    # Global per-chunk scalar oracles (M_phi, M_phi_prime, M_pp,
    # inv_F_p_z, u_zz_bound) for V9-V13.
    M_phi = arb(0)
    M_phi_prime = arb(0)
    M_pp = arb(0)
    inf_D_global = arb("inf")

    for cd in chunk_data:
        ch = cd["ch"]
        sup = cd["sup"]
        c_re, c_im, hr, hi = cd["c_re"], cd["c_im"], cd["hr"], cd["hi"]
        chunk_radius = (hr * hr + hi * hi).sqrt()
        c = acb(c_re, c_im)
        H_eta_c = acb(arb(ch["H_eta_re"]), arb(ch["H_eta_im"]))
        H0_c = _h0_closed(c)
        Phi_c = H_eta_c - H0_c
        Phi_abs_chunk = Phi_c.abs_upper() + chunk_radius * sup["M_phi_p"]
        if Phi_abs_chunk.upper() > M_phi.upper():
            M_phi = Phi_abs_chunk
        if sup["M_phi_p"].upper() > M_phi_prime.upper():
            M_phi_prime = sup["M_phi_p"]
        M_pp_chunk = sup["sup_H0pp"] + p_max * sup["M_phi_pp"]
        if M_pp_chunk.upper() > M_pp.upper():
            M_pp = M_pp_chunk
        D_lb_chunk = sup["inf_H0p"] - p_max * sup["M_phi_p"]
        if D_lb_chunk.upper() < inf_D_global.upper():
            inf_D_global = D_lb_chunk

    if not (inf_D_global > arb(0)):
        print("ERROR: inf|D| ≤ 0 globally")
        return
    inv_F_p_z = arb(1) / inf_D_global
    u_zz_bound = M_pp * inv_F_p_z * inv_F_p_z * inv_F_p_z

    # Per-cell joint sups (V14-V26 oracle quantities)
    print(f"[audit] sweeping {n_chunks} chunks × {args.n_p_cells} p-cells "
          f"= {n_chunks * args.n_p_cells} cells...", flush=True)

    p_cells = []
    for k in range(args.n_p_cells):
        p_lo = p_max * arb(k) / arb(args.n_p_cells)
        p_hi = p_max * arb(k + 1) / arb(args.n_p_cells)
        p_cells.append((p_lo, p_hi))

    sup_joint = arb(0)
    sup_uzz_phi_sq = arb(0)
    sup_merged = arb(0)
    info_joint = info_uzz = info_merged = None

    cells_done = 0
    total_cells = len(chunk_data) * args.n_p_cells
    for cd in chunk_data:
        ch = cd["ch"]
        sup = cd["sup"]
        c_re, c_im, hr, hi = cd["c_re"], cd["c_im"], cd["hr"], cd["hi"]
        H_eta_re = arb(ch["H_eta_re"]); H_eta_im = arb(ch["H_eta_im"])
        Hp_re = arb(ch["Hp_re"]);       Hp_im = arb(ch["Hp_im"])
        Hpp_re = arb(ch.get("Hpp_re", "0"))
        Hpp_im = arb(ch.get("Hpp_im", "0"))
        for k, (p_lo, p_hi) in enumerate(p_cells):
            p_mid = (p_lo + p_hi) / arb(2)
            p_rad = (p_hi - p_lo) / arb(2)
            scores = _eval_three_at_cell(
                H_eta_re, H_eta_im, Hp_re, Hp_im, Hpp_re, Hpp_im,
                c_re, c_im, hr, hi, sup, p_mid, p_rad, 200,
            )
            if scores["joint"].upper() > sup_joint.upper():
                sup_joint = scores["joint"]
                info_joint = (ch["chunk_id"], ch["edge"], k)
            if scores["uzz_phi_sq"].upper() > sup_uzz_phi_sq.upper():
                sup_uzz_phi_sq = scores["uzz_phi_sq"]
                info_uzz = (ch["chunk_id"], ch["edge"], k)
            if scores["merged"].upper() > sup_merged.upper():
                sup_merged = scores["merged"]
                info_merged = (ch["chunk_id"], ch["edge"], k)
            cells_done += 1
        if cells_done % 64 == 0:
            print(f"  cells {cells_done}/{total_cells}: "
                  f"joint={float(sup_joint.upper()):.3e} "
                  f"uzz={float(sup_uzz_phi_sq.upper()):.3e} "
                  f"merged={float(sup_merged.upper()):.3e}", flush=True)

    # ---- Print oracle table ----
    print()
    print("=" * 78)
    print(f"Patched (truncation-free) oracles  [{args.label}]")
    print("=" * 78)

    def prt(name, val):
        print(f"  {name:<32} = {float(val.upper()):.6e}")

    prt("M_phi", M_phi)
    prt("M_phi_prime", M_phi_prime)
    prt("M_pp", M_pp)
    prt("inf|D| (p_max=1)", inf_D_global)
    prt("inv_F_p_z", inv_F_p_z)
    prt("u_zz_bound", u_zz_bound)
    print()
    print(f"  joint_phi_phip_invD2 (per-cell, Taylor pad):")
    print(f"    sup = {float(sup_joint.upper()):.6e}  "
          f"@ chunk {info_joint[0]} ({info_joint[1]}), p-cell {info_joint[2]}")
    print(f"  uzz_phi_sq (per-cell, Taylor pad):")
    print(f"    sup = {float(sup_uzz_phi_sq.upper()):.6e}  "
          f"@ chunk {info_uzz[0]} ({info_uzz[1]}), p-cell {info_uzz[2]}")
    print(f"  merged_uderiv (per-cell, Taylor pad):")
    print(f"    sup = {float(sup_merged.upper()):.6e}  "
          f"@ chunk {info_merged[0]} ({info_merged[1]}), p-cell {info_merged[2]}")
    print()
    print(f"  Sanity: 2·joint + uzz_phi_sq = "
          f"{float((arb(2)*sup_joint + sup_uzz_phi_sq).upper()):.6e}  "
          f"(must be ≥ merged)")
    print()

    # ---- Per-candidate formula ----
    def Cr_phi_paper(M_phi, M_phi_prime):
        return (M_phi * M_phi_prime * invFp_paper * invFp_paper
                + coef_term2_paper * M_phi * M_phi)

    def Cr_phi_invD_paper(M_phi, M_phi_prime, inv_F_p_z):
        return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
                + coef_term2_paper * M_phi * M_phi)

    def Cr_phi_uzz_(M_phi, M_phi_prime, inv_F_p_z, M_pp):
        return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
                + (arb(1)/arb(2)) * M_pp * inv_F_p_z**3 * M_phi * M_phi)

    def Cr_phi_uzz_direct_(M_phi, M_phi_prime, inv_F_p_z, u_zz):
        return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
                + (arb(1)/arb(2)) * u_zz * M_phi * M_phi)

    def Cr_phi_uzz_direct_joint_(M_phi, joint, u_zz):
        return joint + (arb(1)/arb(2)) * u_zz * M_phi * M_phi

    def Cr_phi_uzz_direct_joint2_(joint, uzz_phi_sq):
        return joint + (arb(1)/arb(2)) * uzz_phi_sq

    def Cr_phi_uzz_merged_(merged):
        return (arb(1)/arb(2)) * merged

    candidates = [
        (9,  "Cr_phi",                    "5"),
        (10, "Cr_phi_invD",               "2"),
        (11, "Cr_phi_uzz",                "1"),
        (12, "Cr_phi_uzz_direct",         "1/32"),
        (13, "Cr_phi_uzz_direct",         "1/300"),
        (14, "Cr_phi_uzz_direct_joint",   "1/1300"),
        (15, "Cr_phi_uzz_direct_joint2",  "1/2600"),
        (16, "Cr_phi_uzz_direct_joint2",  "1/3500"),
        (17, "Cr_phi_uzz_direct_joint2",  "1/3500"),
        (18, "Cr_phi_uzz_direct_joint2",  "1/11700"),
        (19, "Cr_phi_uzz_direct_joint2",  "1/31500"),
        (20, "Cr_phi_uzz_direct_joint2",  "1/66500"),
        (21, "Cr_phi_uzz_direct_joint2",  "1/71900"),
        (22, "Cr_phi_uzz_direct_joint2",  "1/124000"),
        (23, "Cr_phi_uzz_direct_joint2",  "1/169000"),
        (24, "Cr_phi_uzz_direct_joint2",  "1/169000"),
        (25, "Cr_phi_uzz_merged",         "1/240000"),
        (26, "Cr_phi_uzz_merged",         "1/268000"),
    ]

    rows = []
    print("=" * 92)
    print(f"{'Candidate':>9} {'Formula':>27} {'Cr_decl':>14} "
          f"{'Cr_patched':>16} {'ratio':>10}")
    print("=" * 92)
    for v, formula, cr_decl_str in candidates:
        cr_decl_arb = arb(cr_decl_str)
        if formula == "Cr_phi":
            naive = Cr_phi_paper(M_phi, M_phi_prime)
        elif formula == "Cr_phi_invD":
            naive = Cr_phi_invD_paper(M_phi, M_phi_prime, inv_F_p_z)
        elif formula == "Cr_phi_uzz":
            naive = Cr_phi_uzz_(M_phi, M_phi_prime, inv_F_p_z, M_pp)
        elif formula == "Cr_phi_uzz_direct":
            naive = Cr_phi_uzz_direct_(M_phi, M_phi_prime, inv_F_p_z,
                                          u_zz_bound)
        elif formula == "Cr_phi_uzz_direct_joint":
            naive = Cr_phi_uzz_direct_joint_(M_phi, sup_joint, u_zz_bound)
        elif formula == "Cr_phi_uzz_direct_joint2":
            naive = Cr_phi_uzz_direct_joint2_(sup_joint, sup_uzz_phi_sq)
        elif formula == "Cr_phi_uzz_merged":
            naive = Cr_phi_uzz_merged_(sup_merged)
        else:
            naive = arb("inf")

        ratio = float(naive.upper()) / float(cr_decl_arb.upper())
        print(f"{f'V{v}':>9} {formula:>27} {cr_decl_str:>14} "
              f"{float(naive.upper()):>16.6e} {ratio:>10.2e}")
        rows.append({
            "candidate": f"V{v}",
            "formula":   formula,
            "Cr_decl":   cr_decl_str,
            "Cr_decl_float": float(cr_decl_arb.upper()),
            "Cr_patched_str": naive.str(20, more=True),
            "Cr_patched_float": float(naive.upper()),
            "ratio_patched_over_decl": ratio,
        })

    out_data = {
        "label": args.label,
        "chunks_path": str(args.chunks),
        "n_p_cells": args.n_p_cells,
        "constants": {
            "r": "23/25", "R": "23/20", "p_max": "1",
            "invFp_paper_float": float(invFp_paper.upper()),
            "coef_term2_paper_float": float(coef_term2_paper.upper()),
        },
        "oracles": {
            "M_phi": M_phi.str(20, more=True),
            "M_phi_prime": M_phi_prime.str(20, more=True),
            "M_pp": M_pp.str(20, more=True),
            "inf_D_global": inf_D_global.str(20, more=True),
            "inv_F_p_z": inv_F_p_z.str(20, more=True),
            "u_zz_bound": u_zz_bound.str(20, more=True),
            "joint_phi_phip_invD2": sup_joint.str(20, more=True),
            "uzz_phi_sq": sup_uzz_phi_sq.str(20, more=True),
            "merged_uderiv": sup_merged.str(20, more=True),
        },
        "candidates": rows,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(out_data, f, indent=2)
    print(f"\nSaved → {args.out}", flush=True)


if __name__ == "__main__":
    main()
