"""Assemble a chunks JSON from a raw cache, INCLUDING ONLY chunks that have
all 66 work units done (1 center + 1 center_pp + 64 path nodes for
n_gl_path=16, n_panels_path=2). Useful for getting a joint-oracle preview
before the full production run finishes.

Output format matches parallel_chunk_certifier.py's chunks JSON, so it
can be fed directly to joint_merged_uderiv.py.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from parallel_chunk_certifier import (
    boundary_chunks, _gl01_nodes_weights,
    DELTA_STR, B_STR, ETA_STR, RHO_PATH_STR,
    L_INNER, PREC, REL_ACC_BITS,
    _m2_chunk_bound,
)
from h_eta_parallel_path import _adaptive_rho, _path_gl_error_bound


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw_cache", type=Path,
        default=Path("/home/rsaha/projects/grothendieck/ProofRefinement/"
                      "Lemma54/Cache/v26_chunk_certifier_npe16_raw.json"))
    parser.add_argument("--out", type=Path,
        default=Path("/home/rsaha/projects/grothendieck/ProofRefinement/"
                      "Lemma54/Cache/v26_chunk_certifier_npe16_partial.json"))
    parser.add_argument("--n_per_edge", type=int, default=16)
    parser.add_argument("--n_gl_path", type=int, default=16)
    parser.add_argument("--n_panels_path", type=int, default=2)
    parser.add_argument("--prec", type=int, default=PREC)
    parser.add_argument("--rel_acc_bits", type=int, default=REL_ACC_BITS)
    args = parser.parse_args()

    flint_ctx.prec = args.prec
    eta_arb = arb(ETA_STR)
    delta = arb(DELTA_STR)
    B = arb(B_STR)
    n_gl_path = args.n_gl_path
    n_panels_path = args.n_panels_path

    print(f"[assemble] Loading raw cache: {args.raw_cache}", flush=True)
    raw = json.load(open(args.raw_cache))
    print(f"[assemble] {len(raw)} entries in cache", flush=True)

    # Index by key
    Hp_center = {}
    Hpp_center = {}
    Hp_path = {}
    error_count = 0
    for r in raw:
        kind = r["kind"]
        if kind == "error":
            error_count += 1
            continue
        cid = r["chunk_id"]
        val = acb(arb(r["re_str"]), arb(r["im_str"]))
        if kind == "center":
            Hp_center[cid] = val
        elif kind == "center_pp":
            Hpp_center[cid] = val
        elif kind == "path_node":
            Hp_path[(cid, r["segment_id"], r["panel_id"],
                      r["node_id"])] = val

    print(f"[assemble] {error_count} error entries skipped", flush=True)

    # Build chunk geometry
    chunks = list(boundary_chunks(delta, B, args.n_per_edge))
    nodes_t, weights_t = _gl01_nodes_weights(n_gl_path, args.prec)

    # Identify fully-done chunks
    n_path_units_per_chunk = 2 * n_panels_path * n_gl_path
    done_cids = []
    for (cid, edge, a, b, hr, hi) in chunks:
        if cid not in Hp_center or cid not in Hpp_center:
            continue
        path_complete = True
        for seg_id in (0, 1):
            for p_id in range(n_panels_path):
                for nid in range(n_gl_path):
                    if (cid, seg_id, p_id, nid) not in Hp_path:
                        path_complete = False
                        break
                if not path_complete:
                    break
            if not path_complete:
                break
        if path_complete:
            done_cids.append(cid)

    print(f"[assemble] {len(done_cids)}/{len(chunks)} chunks fully done",
          flush=True)

    # Build seg/panel endpoints (same logic as parallel_chunk_certifier)
    seg_endpoints = {}
    panel_endpoints = {}
    for (cid, edge, a, b, hr, hi) in chunks:
        c = acb(a, b)
        z_mid_real = acb(c.real, arb(0))
        seg_endpoints[(cid, 0)] = (acb(0), z_mid_real)
        seg_endpoints[(cid, 1)] = (z_mid_real, c)
        for seg_id, (z_s, z_e) in [(0, (acb(0), z_mid_real)),
                                     (1, (z_mid_real, c))]:
            delta_seg = z_e - z_s
            if not (delta_seg.abs_upper() > arb(0)):
                continue
            for p_id in range(n_panels_path):
                t_p_lo = arb(p_id) / arb(n_panels_path)
                t_p_hi = arb(p_id + 1) / arb(n_panels_path)
                z_p_start = z_s + acb(t_p_lo) * delta_seg
                z_p_end = z_s + acb(t_p_hi) * delta_seg
                panel_endpoints[(cid, seg_id, p_id)] = (z_p_start, z_p_end)

    # Assemble H_η, error, M_2 per done chunk
    out_chunks = []
    t0 = time.time()
    chunks_dict = {cid: (edge, a, b, hr, hi)
                    for (cid, edge, a, b, hr, hi) in chunks}
    for n_assembled, cid in enumerate(done_cids):
        edge, a, b, hr, hi = chunks_dict[cid]

        H_eta = acb(0)
        total_err = arb(0)
        for seg_id in (0, 1):
            if (cid, seg_id) not in seg_endpoints:
                continue
            for p_id in range(n_panels_path):
                key_p = (cid, seg_id, p_id)
                if key_p not in panel_endpoints:
                    continue
                z_p_start, z_p_end = panel_endpoints[key_p]
                delta_p = z_p_end - z_p_start
                if not (delta_p.abs_upper() > arb(0)):
                    continue
                seg_p_sum = acb(0)
                for nid in range(n_gl_path):
                    key = (cid, seg_id, p_id, nid)
                    if key not in Hp_path:
                        continue
                    seg_p_sum += acb(weights_t[nid]) * Hp_path[key]
                panel_value = seg_p_sum * delta_p
                H_eta += panel_value

                try:
                    rho = _adaptive_rho(z_p_start, z_p_end, eta_arb, "v26",
                                          prec=args.prec)
                    err_p = _path_gl_error_bound(z_p_start, z_p_end, rho,
                                                   n_gl_path, eta_arb,
                                                   "v26", prec=args.prec)
                except ValueError:
                    err_p = arb("inf")
                total_err = total_err + err_p

        re = H_eta.real
        im = H_eta.imag
        H_eta_certified = acb(arb.union(re - total_err, re + total_err),
                                arb.union(im - total_err, im + total_err))

        # M_2 chunk bound (closed-form, fast)
        re_lo, re_hi = a - hr, a + hr
        im_lo, im_hi = b - hi, b + hi
        z_box = acb(arb.union(re_lo, re_hi), arb.union(im_lo, im_hi))
        try:
            m2 = _m2_chunk_bound(z_box, eta_arb, args.prec)
        except Exception:
            m2 = arb(0)

        Hp = Hp_center[cid]
        Hpp = Hpp_center[cid]
        out_chunks.append({
            "chunk_id": cid,
            "status": "ok",
            "edge": edge,
            "center_re": a.str(args.prec // 3),
            "center_im": b.str(args.prec // 3),
            "half_re": hr.str(args.prec // 3),
            "half_im": hi.str(args.prec // 3),
            "H_eta_re": H_eta_certified.real.str(args.prec // 3),
            "H_eta_im": H_eta_certified.imag.str(args.prec // 3),
            "Hp_re": Hp.real.str(args.prec // 3),
            "Hp_im": Hp.imag.str(args.prec // 3),
            "Hpp_re": Hpp.real.str(args.prec // 3),
            "Hpp_im": Hpp.imag.str(args.prec // 3),
            "M_2": m2.str(args.prec // 3),
        })
        if (n_assembled + 1) % 5 == 0 or n_assembled == len(done_cids) - 1:
            print(f"  assembled {n_assembled+1}/{len(done_cids)} "
                  f"({time.time() - t0:.1f}s)", flush=True)

    output = {
        "n_chunks": len(out_chunks),
        "wall_time_s": time.time() - t0,
        "params": {
            "eta": ETA_STR, "delta": DELTA_STR, "B": B_STR,
            "n_per_edge": args.n_per_edge,
            "n_gl_path": n_gl_path, "n_panels_path": n_panels_path,
            "rho_path": RHO_PATH_STR, "L_inner": L_INNER,
            "prec": args.prec, "rel_acc_bits": args.rel_acc_bits,
            "PARTIAL_PREVIEW": True,
            "n_chunks_total_expected": len(chunks),
            "missing_chunk_ids": sorted(set(c[0] for c in chunks)
                                          - set(done_cids)),
        },
        "chunks": out_chunks,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(output, f, indent=2)
    print(f"[assemble] Wrote → {args.out}", flush=True)
    print(f"[assemble] Wall: {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
