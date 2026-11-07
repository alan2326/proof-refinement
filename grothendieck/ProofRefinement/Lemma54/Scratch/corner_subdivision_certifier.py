"""Replace 8 corner chunks of an existing chunks-JSON with 4-way subdivisions.

Workflow:
  1. Load existing chunks JSON (the production output of parallel_chunk_certifier).
  2. Identify the 8 corner-adjacent chunks (top/bottom edges nearest re=±δ; left/right edges
     nearest im=±B).
  3. For each corner chunk, generate 4 sub-chunks: split each chunk in half along
     re and im. Each sub-chunk has half-radii hr/2, hi/2.
  4. Run parallel_chunk_certifier.certify_all_chunks(chunks_override=sub_chunks) on
     just the 32 corner sub-chunks. Reuses the same incremental cache + Pool machinery.
  5. Merge: emit a NEW chunks JSON with the 56 unchanged non-corner chunks + the 32
     corner sub-chunks (88 chunks total).

Usage:
  uv run --with python-flint python -u corner_subdivision_certifier.py \
      --in_chunks /path/to/v26_chunk_certifier_npe16.json \
      --out_chunks /path/to/v26_chunk_certifier_npe16_corner_split4.json \
      --n_workers 96
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import List, Tuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from parallel_chunk_certifier import (
    certify_all_chunks, DEFAULT_N_WORKERS,
    N_GL_PATH, N_PANELS_PATH, RHO_PATH_STR, L_INNER, PREC, REL_ACC_BITS,
    ETA_STR, DELTA_STR, B_STR,
)


def _identify_corner_chunks(chunks: List[dict],
                              delta: arb, B: arb,
                              tol_rel: arb = arb("0.5")) -> List[int]:
    """Return list of chunk_ids that lie nearest the 4 corners of the boundary
    rectangle [-δ, δ] × [-B, B]. The 8 corner chunks are the chunks on the top
    and bottom edges with center re closest to ±δ, and the chunks on the left
    and right edges with center im closest to ±B.

    More robust strategy: per (edge, sign of re or im), pick the chunk whose
    center coordinate has the largest absolute value.
    """
    by_edge = {"top": [], "bottom": [], "left": [], "right": []}
    for ch in chunks:
        edge = ch["edge"]
        if edge not in by_edge:
            continue
        by_edge[edge].append(ch)

    corner_ids = set()
    for edge in ("top", "bottom"):
        # corner chunks on top/bottom: extremes of re
        es = by_edge[edge]
        if not es:
            continue
        re_vals = [(arb(ch["center_re"]).upper(), ch["chunk_id"]) for ch in es]
        re_vals.sort()
        corner_ids.add(re_vals[0][1])    # leftmost
        corner_ids.add(re_vals[-1][1])   # rightmost
    for edge in ("left", "right"):
        es = by_edge[edge]
        if not es:
            continue
        im_vals = [(arb(ch["center_im"]).upper(), ch["chunk_id"]) for ch in es]
        im_vals.sort()
        corner_ids.add(im_vals[0][1])    # bottommost
        corner_ids.add(im_vals[-1][1])   # topmost
    return sorted(corner_ids)


def _split_chunk_4_way(ch: dict, prec: int) -> List[Tuple]:
    """Split a boundary chunk into sub-chunks. Boundary chunks live on edges
    of the rectangle, so one of (hr, hi) is zero for any single chunk:
        right/left edge:  hr = 0,  hi > 0  → split in Im → 2 sub-chunks
        top/bottom edge:  hr > 0,  hi = 0  → split in Re → 2 sub-chunks
    A general 2D chunk would split into 4. Here we always get 2.
    Returns list of (cid, edge, a, b, hr, hi) tuples with cid placeholder.
    """
    flint_ctx.prec = prec
    a = arb(ch["center_re"])
    b = arb(ch["center_im"])
    hr = arb(ch["half_re"])
    hi = arb(ch["half_im"])
    edge = ch["edge"]
    half = arb(1) / arb(2)

    out = []
    is_vertical = (hr.upper() == arb(0).upper() and hi > arb(0))
    is_horizontal = (hi.upper() == arb(0).upper() and hr > arb(0))

    if is_vertical:
        new_hi = hi * half
        for (na, nb) in [(a, b - new_hi), (a, b + new_hi)]:
            out.append((-1, edge, na, nb, hr, new_hi))
    elif is_horizontal:
        new_hr = hr * half
        for (na, nb) in [(a - new_hr, b), (a + new_hr, b)]:
            out.append((-1, edge, na, nb, new_hr, hi))
    else:
        # General 2D chunk: 4-way split
        new_hr = hr * half
        new_hi = hi * half
        for (na, nb) in [(a - new_hr, b - new_hi), (a + new_hr, b - new_hi),
                          (a - new_hr, b + new_hi), (a + new_hr, b + new_hi)]:
            out.append((-1, edge, na, nb, new_hr, new_hi))
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--in_chunks", type=Path, required=True,
                         help="Input chunks JSON (production output)")
    parser.add_argument("--out_chunks", type=Path, required=True,
                         help="Output chunks JSON (with corners subdivided)")
    parser.add_argument("--n_workers", type=int, default=DEFAULT_N_WORKERS)
    parser.add_argument("--n_gl_path", type=int, default=N_GL_PATH)
    parser.add_argument("--n_panels_path", type=int, default=N_PANELS_PATH)
    parser.add_argument("--prec", type=int, default=PREC)
    parser.add_argument("--rel_acc_bits", type=int, default=REL_ACC_BITS)
    parser.add_argument("--extra_chunk_ids", type=str, default="",
                         help="Comma-separated extra chunk IDs to subdivide "
                              "(in addition to auto-identified corners). E.g. "
                              "--extra_chunk_ids 1,14,17,30 for next-to-corner.")
    args = parser.parse_args()

    print(f"[corner-split] Loading {args.in_chunks}", flush=True)
    with open(args.in_chunks) as f:
        in_data = json.load(f)
    in_chunks = in_data["chunks"]
    params = in_data["params"]
    eta_str = params["eta"]
    delta_str = params.get("delta", DELTA_STR)
    B_str_val = params.get("B", B_STR)
    delta = arb(delta_str)
    B = arb(B_str_val)
    prec = args.prec

    flint_ctx.prec = prec
    corner_ids = set(_identify_corner_chunks(in_chunks, delta, B))
    if args.extra_chunk_ids:
        for x in args.extra_chunk_ids.split(","):
            x = x.strip()
            if x:
                corner_ids.add(int(x))
    corner_ids = sorted(corner_ids)
    print(f"[corner-split] Subdividing {len(corner_ids)} chunks: "
          f"{corner_ids}", flush=True)

    # Build sub-chunks list, with new sequential cids.
    # Use V26 4-fold symmetry: H_η is odd, H_η(z̄) = ̄H_η(z). Pick only
    # the sub-chunks with center in the first quadrant (a ≥ 0, b ≥ 0)
    # — these are 1/4 of the 32 sub-chunks. After certifier finishes,
    # populate the other 3 quadrants from these via:
    #   H_η(-z̄) = -̄H_η(z),    H_η(z̄) = ̄H_η(z),    H_η(-z) = -H_η(z)
    #   H_η'(-z̄) = ̄H_η'(z),   H_η'(z̄) = ̄H_η'(z),   H_η'(-z) = H_η'(z)
    #   H_η''(-z̄) = -̄H_η''(z), H_η''(z̄) = ̄H_η''(z), H_η''(-z) = -H_η''(z)
    all_subs = []   # list of (orig_cid, edge, a, b, hr, hi) for ALL 32
    for ch in in_chunks:
        if ch["chunk_id"] in corner_ids:
            for (_, edge, a, b, hr, hi) in _split_chunk_4_way(ch, prec):
                all_subs.append((ch["chunk_id"], edge, a, b, hr, hi))

    # Pick "primary" sub-chunks: a > 0 and b > 0 (first quadrant centers)
    primary_subs = []   # tuples (cid, edge, a, b, hr, hi) in first quadrant
    cid_counter = 0
    primary_keys = []   # parallel list of (orig_cid, sub_index_within_chunk)
    for (orig_cid, edge, a, b, hr, hi) in all_subs:
        if a.lower() >= arb(0) and b.lower() >= arb(0):
            primary_subs.append((cid_counter, edge, a, b, hr, hi))
            primary_keys.append((orig_cid, edge, a, b, hr, hi))
            cid_counter += 1

    new_chunks_tuples = primary_subs
    print(f"[corner-split] Symmetry: computing {len(primary_subs)}/{len(all_subs)} "
          f"primary sub-chunks (first quadrant); rest via reflection",
          flush=True)
    print(f"[corner-split] Running certifier on sub-chunks "
          f"(n_workers={args.n_workers})", flush=True)

    sub_out_path = args.out_chunks.with_name(
        args.out_chunks.stem + "_subchunks_only.json")
    certify_all_chunks(
        n_workers=args.n_workers,
        n_gl_path=args.n_gl_path,
        n_panels_path=args.n_panels_path,
        prec=prec,
        rel_acc_bits=args.rel_acc_bits,
        eta_str=eta_str,
        delta_str=delta_str,
        B_str=B_str_val,
        out_path=sub_out_path,
        chunks_override=new_chunks_tuples,
        verbose=True,
    )

    # Merge: 56 unchanged non-corner chunks + 16 corner sub-chunks
    # (all 16 from 4 primaries via 4-fold symmetry).
    print(f"[corner-split] Merging non-corner chunks with sub-chunks (with "
          f"symmetry reflection)", flush=True)
    with open(sub_out_path) as f:
        sub_data = json.load(f)
    sub_chunks = sub_data["chunks"]

    # Map from Q1 primary (a_str, b_str) → certified chunk dict
    primary_dict = {}   # key: (a.str, b.str) of primary
    for sc in sub_chunks:
        a_key = sc["center_re"]
        b_key = sc["center_im"]
        primary_dict[(a_key, b_key)] = sc

    def _reflect_chunk(primary: dict, edge: str, a_str: str, b_str: str,
                        flip_re: bool, flip_im: bool) -> dict:
        """Build a reflected chunk dict from primary using V26 symmetries.
        flip_re=True means a_target = -a_primary; similarly flip_im.
        H_η(z̄) = ̄H_η(z), H_η(-z) = -H_η(z) gives, for any flip pattern:
            H_η: real *= sign_re*sign_im,  imag *= sign_re   (sign_re flips → odd in z; conj → flips imag of H_η)
            H_η': real *= sign_im,         imag *= sign_re*sign_im   (even in z → no sign_re flip for real; conj → imag flips)
            H_η'': real *= sign_re*sign_im, imag *= sign_re  (odd in z again)
        Cleanest: derive the 3 cases explicitly.
            primary at z, target at z' = ε_a a + ε_b b i with ε ∈ {±1}.
            ε_a=+1, ε_b=-1: z' = z̄ (conj)
              H_η(z') = ̄H_η(z),       H_η'(z') = ̄H_η'(z),    H_η''(z') = ̄H_η''(z)
            ε_a=-1, ε_b=-1: z' = -z (neg)
              H_η(z') = -H_η(z),      H_η'(z') = +H_η'(z),    H_η''(z') = -H_η''(z)
            ε_a=-1, ε_b=+1: z' = -z̄ (neg-conj)
              H_η(z') = -̄H_η(z),     H_η'(z') = +̄H_η'(z),   H_η''(z') = -̄H_η''(z)
        """
        out = dict(primary)
        out["edge"] = edge
        out["center_re"] = a_str
        out["center_im"] = b_str

        H_re = arb(primary["H_eta_re"])
        H_im = arb(primary["H_eta_im"])
        Hp_re = arb(primary["Hp_re"])
        Hp_im = arb(primary["Hp_im"])
        Hpp_re = arb(primary["Hpp_re"])
        Hpp_im = arb(primary["Hpp_im"])

        if (not flip_re) and (not flip_im):    # Q1, primary itself
            new_H = (H_re, H_im)
            new_Hp = (Hp_re, Hp_im)
            new_Hpp = (Hpp_re, Hpp_im)
        elif (not flip_re) and flip_im:        # conj: z → z̄
            new_H = (H_re, -H_im)
            new_Hp = (Hp_re, -Hp_im)
            new_Hpp = (Hpp_re, -Hpp_im)
        elif flip_re and flip_im:               # neg: z → -z
            new_H = (-H_re, -H_im)
            new_Hp = (Hp_re, Hp_im)
            new_Hpp = (-Hpp_re, -Hpp_im)
        else:                                    # neg-conj: z → -z̄
            new_H = (-H_re, H_im)
            new_Hp = (Hp_re, -Hp_im)
            new_Hpp = (-Hpp_re, Hpp_im)
        prec_str = primary.get("M_2", "0")  # Use to extract precision indirectly
        # Use the same precision string format
        from parallel_chunk_certifier import PREC
        s = lambda x: x.str(PREC // 3)
        out["H_eta_re"] = s(new_H[0])
        out["H_eta_im"] = s(new_H[1])
        out["Hp_re"] = s(new_Hp[0])
        out["Hp_im"] = s(new_Hp[1])
        out["Hpp_re"] = s(new_Hpp[0])
        out["Hpp_im"] = s(new_Hpp[1])
        return out

    def _edge_for(a: arb, b: arb, delta: arb, B: arb) -> str:
        # Pick edge label by which axis is at the boundary (within tolerance)
        re_bound = arb(1) - delta
        if abs(float(a.upper())) > float(re_bound.upper()) - 1e-6:
            return "right" if float(a.upper()) > 0 else "left"
        return "top" if float(b.upper()) > 0 else "bottom"

    merged = []
    next_cid = 0
    for ch in in_chunks:
        if ch["chunk_id"] not in corner_ids:
            new_ch = dict(ch)
            new_ch["chunk_id"] = next_cid
            merged.append(new_ch)
            next_cid += 1

    # For each of the 16 sub-chunks (all_subs), find Q1 primary and reflect.
    for (orig_cid, edge, a, b, hr, hi) in all_subs:
        a_abs = a if a.lower() >= arb(0) else -a
        b_abs = b if b.lower() >= arb(0) else -b
        flip_re = a.upper() < arb(0).upper()
        flip_im = b.upper() < arb(0).upper()
        # Find primary by matching (a_abs.str, b_abs.str)
        a_str_target = a_abs.str(prec // 3)
        b_str_target = b_abs.str(prec // 3)
        if (a_str_target, b_str_target) in primary_dict:
            primary = primary_dict[(a_str_target, b_str_target)]
        else:
            # Approximate match (string truncation differences)
            primary = None
            for (k_a, k_b), sc in primary_dict.items():
                if abs(float(arb(k_a).upper()) - float(a_abs.upper())) < 1e-6 \
                   and abs(float(arb(k_b).upper()) - float(b_abs.upper())) < 1e-6:
                    primary = sc
                    break
            if primary is None:
                print(f"  WARN: no primary for sub at ({a_str_target}, "
                      f"{b_str_target})", flush=True)
                continue
        a_str = a.str(prec // 3)
        b_str = b.str(prec // 3)
        reflected = _reflect_chunk(primary, edge, a_str, b_str,
                                      flip_re, flip_im)
        reflected["chunk_id"] = next_cid
        merged.append(reflected)
        next_cid += 1

    out_data = dict(in_data)
    out_data["n_chunks"] = len(merged)
    out_data["chunks"] = merged
    out_data["params"] = dict(params)
    out_data["params"]["corner_subdivisions"] = 4
    out_data["params"]["original_chunks"] = len(in_chunks)
    out_data["params"]["corner_chunk_ids"] = list(corner_ids)

    with open(args.out_chunks, "w") as f:
        json.dump(out_data, f, indent=2)
    print(f"[corner-split] Wrote merged chunks → {args.out_chunks}",
          flush=True)
    print(f"[corner-split] {len(merged)} chunks total "
          f"({len(in_chunks) - len(corner_ids)} unchanged + "
          f"{len(sub_chunks)} sub-chunks)", flush=True)


if __name__ == "__main__":
    main()
