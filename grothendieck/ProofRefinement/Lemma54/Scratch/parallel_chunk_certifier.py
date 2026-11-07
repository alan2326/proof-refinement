"""Parallel chunk certifier for V26 boundary chunks.

For each of the 64 V26 boundary chunks (4 edges × 16 chunks/edge with
δ=1635/10000, B=1115/1000), compute:
  • H_η(c)  sharp via parallel path integration of H_η' from 0
  • H_η'(c) sharp via Price-formula nested acb.integral (1 call)
  • M_2 = sup_{z ∈ Z}|H_η''(z)|  closed-form arb chunk bound

These three quantities, together with closed-form H_0(c), H_0'(c), H_0''(c)
and chunk bounds for M_φ, M_φ', M_pp from the existing pipeline, feed the
joint per-(p,w)-cell oracle (Step 10.4).

Architecture:
  • Pre-compute all M_2 values in main thread (fast, closed-form).
  • Pack ALL sharp-eval work units (path nodes + H_η' midpoint) into one
    multiprocessing.Pool.  64 chunks × (32 path nodes + 1 H_η' midpoint)
    = 2,112 work units.  At ~100 s per V26 H_η' eval and 128 cores: wall
    time ≈ 17 evals/core × 100 s = ~30 min.
  • Gather, assemble, save per-chunk results to JSON cache.

Output cache schema:
  {
    "n_chunks": 64,
    "params": { "eta": "0.01", "delta": "1635/10000", "B": "1115/1000",
                 "n_per_edge": 16, "n_gl_path": 16, "rho_path": "1.5",
                 "L_inner": 6, "prec": 100, "rel_acc_bits": 22 },
    "chunks": [
       {
         "chunk_id": 0,
         "edge": "right",
         "center_re": "0.8365", "center_im": "...",
         "half_re": "0",       "half_im": "0.069...",
         "H_eta_re": "...", "H_eta_im": "...",
         "Hp_re": "...",    "Hp_im": "...",
         "M_2": "..."
       },
       ...
    ]
  }
"""

from __future__ import annotations

import json
import os
import sys
import time
from dataclasses import dataclass, asdict
from multiprocessing import Pool
from pathlib import Path
from typing import List, Tuple

from flint import arb, acb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parents[2]))
sys.path.insert(0, str(_HERE))

from grothendieck.proof.certified.bk_rigor import compute_gl_nodes_weights_arb


# --------------------- V26 parameters (production scale) ---------------
PREC = 100
ETA_STR = "0.01"
DELTA_STR = "1635/10000"
B_STR = "1115/1000"
N_PER_EDGE = 16
N_GL_PATH = 16
N_PANELS_PATH = 2     # split each segment into 2 panels (so edge-chunk
                       # vertical segments fit ρ=1.5 Bernstein box in Ω)
RHO_PATH_STR = "1.5"  # Bernstein-ellipse parameter for path GL bound
L_INNER = 6
REL_ACC_BITS = 22

OUT_PATH = (_HERE.parent / "Cache" /
            f"v26_chunk_certifier_npe{N_PER_EDGE}.json")
# Reserve cores for SSH/system; saturating all 128 cores can stall login.
DEFAULT_N_WORKERS = min(96, os.cpu_count() or 32)


# --------------------- Chunk geometry ----------------------------------
def boundary_chunks(delta: arb, B: arb, n_per_edge: int):
    """Yield (chunk_id, edge, center_re, center_im, half_re, half_im) for the
    4·n_per_edge V26 boundary chunks."""
    re_bound = arb(1) - delta
    half = arb(1) / arb(2)
    half_im = B / arb(n_per_edge)
    cid = 0
    for sign in [+1, -1]:
        a = arb(sign) * re_bound
        edge = "right" if sign > 0 else "left"
        for k in range(n_per_edge):
            b_mid = -B + arb(2) * B * (arb(k) + half) / arb(n_per_edge)
            yield (cid, edge, a, b_mid, arb(0), half_im)
            cid += 1
    half_re = re_bound / arb(n_per_edge)
    for sign in [+1, -1]:
        b = arb(sign) * B
        edge = "top" if sign > 0 else "bottom"
        for k in range(n_per_edge):
            a_mid = -re_bound + arb(2) * re_bound * (arb(k) + half) / arb(n_per_edge)
            yield (cid, edge, a_mid, b, half_re, arb(0))
            cid += 1


# --------------------- Worker work-units --------------------------------
@dataclass
class PathNodeUnit:
    """Compute H_η'(ζ) at one path-GL node."""
    kind: str              # always "path_node"
    chunk_id: int
    segment_id: int        # 0 = real-axis, 1 = vertical
    panel_id: int          # 0..n_panels_path-1
    node_id: int           # 0..n_gl-1
    zeta_re_str: str
    zeta_im_str: str
    eta_str: str
    L: int
    prec: int
    rel_acc_bits: int


@dataclass
class CenterUnit:
    """Compute H_η'(c) (kind='center') or H_η''(c) (kind='center_pp')
    at chunk center."""
    kind: str
    chunk_id: int
    panel_id: int          # ignored (-1)
    node_id: int           # ignored (-1)
    c_re_str: str
    c_im_str: str
    eta_str: str
    L: int
    prec: int
    rel_acc_bits: int


def _worker_h_eta_prime(item) -> Tuple[str, int, int, int, int, str, str]:
    """Top-level worker. Dispatches by item.kind:
        path_node, center  → compute H_η'(ζ) via h_prime_complex_certified
        center_pp          → compute H_η''(c) via h_pp_complex_certified

    Exceptions are caught and returned as ("error", chunk_id, seg, panel, node,
    error_str, kind_str) so the parent Pool does not die on one bad chunk.
    """
    try:
        return _worker_h_eta_prime_impl(item)
    except Exception as e:
        import traceback
        seg = getattr(item, "segment_id", -1)
        panel = getattr(item, "panel_id", -1)
        node = getattr(item, "node_id", -1)
        return ("error", item.chunk_id, seg, panel, node,
                f"{type(e).__name__}: {e}", item.kind)


def _worker_h_eta_prime_impl(item) -> Tuple[str, int, int, int, int, str, str]:
    flint_ctx.prec = item.prec
    eta_arb = arb(item.eta_str)

    if item.kind == "path_node":
        zeta = acb(arb(item.zeta_re_str), arb(item.zeta_im_str))
    else:
        zeta = acb(arb(item.c_re_str), arb(item.c_im_str))

    if item.kind == "center_pp":
        from h_pp_complex_certified import compute_H_eta_pp_certified
        from h_prime_complex_certified import (
            make_v26_P, make_v26_Pprime,
        )
        P = make_v26_P(eta_arb, +1)
        Pp = make_v26_Pprime(eta_arb, +1)
        Q = make_v26_P(eta_arb, -1)
        Qp = make_v26_Pprime(eta_arb, -1)
        H_pp = compute_H_eta_pp_certified(
            z=zeta, P=P, Pp=Pp, Q=Q, Qp=Qp,
            P_kind="v26", eta_arb=eta_arb,
            L=item.L, prec=item.prec, rel_acc_bits=item.rel_acc_bits,
            verbose=False,
        )
        return ("center_pp", item.chunk_id, -1, -1, -1,
                H_pp.real.str(item.prec // 3),
                H_pp.imag.str(item.prec // 3))

    # path_node or center → H_η'
    from h_prime_complex_certified import (
        compute_H_eta_prime_certified,
        compute_J_polynomial_bound_v26,
        make_v26_P, make_v26_Pprime,
    )
    P = make_v26_P(eta_arb, +1)
    Pp = make_v26_Pprime(eta_arb, +1)
    Q = make_v26_P(eta_arb, -1)
    Qp = make_v26_Pprime(eta_arb, -1)
    poly_terms = compute_J_polynomial_bound_v26(eta_arb)

    Hp = compute_H_eta_prime_certified(
        z=zeta, P=P, Pp=Pp, Q=Q, Qp=Qp,
        J_poly_terms=poly_terms,
        L=item.L, prec=item.prec, rel_acc_bits=item.rel_acc_bits,
        verbose=False,
    )
    if item.kind == "path_node":
        return ("path_node", item.chunk_id, item.segment_id,
                item.panel_id, item.node_id,
                Hp.real.str(item.prec // 3), Hp.imag.str(item.prec // 3))
    else:
        return ("center", item.chunk_id, -1, -1, -1,
                Hp.real.str(item.prec // 3), Hp.imag.str(item.prec // 3))


# --------------------- M_2 closed-form chunk bound --------------------
def _m2_chunk_bound(z_box: acb, eta_arb: arb, prec: int) -> arb:
    """sup_{z ∈ Z} |H_η''(z)| ≤ sup|Φ''| + sup|H_0''|, closed-form arb."""
    from h_eta_pp_chunk_bound_certified import (
        bound_H_eta_pp_on_chunk_certified,
    )
    flint_ctx.prec = prec
    res = bound_H_eta_pp_on_chunk_certified(z_box, eta_arb, prec=prec)
    return res.bound


# --------------------- GL nodes/weights once ---------------------------
def _gl01_nodes_weights(n_gl: int, prec: int):
    ref_nodes, ref_weights = compute_gl_nodes_weights_arb(n_gl, prec=prec)
    half = arb(1) / arb(2)
    nodes_t = [(s + arb(1)) * half for s in ref_nodes]
    weights_t = [w * half for w in ref_weights]
    return nodes_t, weights_t


# --------------------- Path GL outer error bound (per segment) --------
def _segment_outer_err(z_start, z_end, n_panels_path, n_gl, eta_arb, prec):
    """Adaptive per-panel ρ; sum errors over panels."""
    from h_eta_parallel_path import _adaptive_path_gl_error_bound
    err, _info = _adaptive_path_gl_error_bound(
        z_start, z_end, n_gl, eta_arb, "v26",
        n_panels=n_panels_path, prec=prec,
    )
    return err


# --------------------- Main certifier ---------------------------------
def certify_all_chunks(
    n_workers: int = DEFAULT_N_WORKERS,
    n_per_edge: int = N_PER_EDGE,
    n_gl_path: int = N_GL_PATH,
    n_panels_path: int = N_PANELS_PATH,
    rho_path_str: str = RHO_PATH_STR,
    L_inner: int = L_INNER,
    prec: int = PREC,
    rel_acc_bits: int = REL_ACC_BITS,
    eta_str: str = ETA_STR,
    delta_str: str = DELTA_STR,
    B_str: str = B_STR,
    out_path: Path = OUT_PATH,
    raw_cache_path: Path = None,
    chunks_override: List = None,
    verbose: bool = True,
) -> dict:
    """Run the full parallel certifier. Saves JSON to out_path.

    If chunks_override is provided, use that list of
    (cid, edge, a, b, hr, hi) tuples instead of generating from
    boundary_chunks. Useful for corner-subdivision runs.
    """
    flint_ctx.prec = prec

    delta = arb(delta_str)
    B = arb(B_str)
    eta_arb = arb(eta_str)
    rho_arb = arb(rho_path_str)

    if chunks_override is not None:
        chunks = list(chunks_override)
    else:
        chunks = list(boundary_chunks(delta, B, n_per_edge))
    if verbose:
        print(f"[chunk-certifier] {len(chunks)} chunks, {n_workers} workers,"
              f" prec={prec}, rel_acc_bits={rel_acc_bits},"
              f" n_gl_path={n_gl_path}, n_panels_path={n_panels_path},"
              f" ρ={rho_path_str}", flush=True)
    # Default raw cache path: alongside out_path
    if raw_cache_path is None:
        raw_cache_path = out_path.with_name(out_path.stem + "_raw.json")

    # ---------- Step 1: M_2 chunk bounds (main thread, closed-form) -----
    t0 = time.time()
    m2_per_chunk = {}
    if verbose:
        print(f"[chunk-certifier] Step 1: M_2 closed-form chunk bounds...",
              flush=True)
    for (cid, edge, a, b, hr, hi) in chunks:
        re_lo, re_hi = a - hr, a + hr
        im_lo, im_hi = b - hi, b + hi
        z_box = acb(arb.union(re_lo, re_hi), arb.union(im_lo, im_hi))
        t_chunk = time.time()
        try:
            m2 = _m2_chunk_bound(z_box, eta_arb, prec)
        except Exception as e:
            if verbose:
                print(f"  chunk {cid:3d}: M_2 ERROR {e}", flush=True)
            m2 = arb(0)
        m2_per_chunk[cid] = m2
        if verbose and (cid % max(1, len(chunks) // 8) == 0
                        or cid == len(chunks) - 1):
            print(f"  M_2 chunk {cid:3d}/{len(chunks)}: "
                  f"{time.time() - t_chunk:.1f}s "
                  f"(total {time.time() - t0:.1f}s)", flush=True)
    if verbose:
        print(f"  M_2 chunk bounds: {len(chunks)} done in "
              f"{time.time() - t0:.1f}s", flush=True)

    # ---------- Step 2: build all sharp-eval work units ---------------
    nodes_t, weights_t = _gl01_nodes_weights(n_gl_path, prec)

    work_units: List = []
    seg_endpoints = {}  # (chunk_id, seg_id) -> (z_start, z_end)
    panel_endpoints = {}  # (cid, seg_id, panel_id) -> (z_p_start, z_p_end)

    for (cid, edge, a, b, hr, hi) in chunks:
        c = acb(a, b)
        # H_η'(c) at midpoint (1 unit)
        work_units.append(CenterUnit(
            kind="center", chunk_id=cid, panel_id=-1, node_id=-1,
            c_re_str=c.real.str(prec // 3),
            c_im_str=c.imag.str(prec // 3),
            eta_str=eta_str, L=L_inner, prec=prec,
            rel_acc_bits=rel_acc_bits,
        ))
        # H_η''(c) at midpoint (1 unit)
        work_units.append(CenterUnit(
            kind="center_pp", chunk_id=cid, panel_id=-1, node_id=-1,
            c_re_str=c.real.str(prec // 3),
            c_im_str=c.imag.str(prec // 3),
            eta_str=eta_str, L=L_inner, prec=prec,
            rel_acc_bits=rel_acc_bits,
        ))

        # Path 0 → Re(c) → c.  Two segments × n_panels_path panels each.
        z_mid = acb(c.real, arb(0))
        seg_endpoints[(cid, 0)] = (acb(0), z_mid)
        seg_endpoints[(cid, 1)] = (z_mid, c)

        for seg_id, (z_s, z_e) in [(0, (acb(0), z_mid)),
                                     (1, (z_mid, c))]:
            delta_seg = z_e - z_s
            if not (delta_seg.abs_upper() > arb(0)):
                continue  # zero-length segment
            for p_id in range(n_panels_path):
                t_p_lo = arb(p_id) / arb(n_panels_path)
                t_p_hi = arb(p_id + 1) / arb(n_panels_path)
                z_p_start = z_s + acb(t_p_lo) * delta_seg
                z_p_end = z_s + acb(t_p_hi) * delta_seg
                delta_p = z_p_end - z_p_start
                panel_endpoints[(cid, seg_id, p_id)] = (z_p_start, z_p_end)
                for nid, t_local in enumerate(nodes_t):
                    zeta = z_p_start + acb(t_local) * delta_p
                    work_units.append(PathNodeUnit(
                        kind="path_node", chunk_id=cid, segment_id=seg_id,
                        panel_id=p_id, node_id=nid,
                        zeta_re_str=zeta.real.str(prec // 3),
                        zeta_im_str=zeta.imag.str(prec // 3),
                        eta_str=eta_str, L=L_inner, prec=prec,
                        rel_acc_bits=rel_acc_bits,
                    ))

    if verbose:
        print(f"[chunk-certifier] {len(work_units)} sharp-eval units "
              f"submitted to Pool({n_workers})…", flush=True)

    # ---------- Step 3: run Pool.map (with raw cache) -------------------
    t1 = time.time()
    raw_cache_path.parent.mkdir(parents=True, exist_ok=True)

    # Load any existing partial cache; build set of done keys to skip
    results: List[Tuple] = []
    done_keys: set = set()
    if raw_cache_path.exists():
        try:
            with open(raw_cache_path) as f:
                raw_data = json.load(f)
            for r in raw_data:
                tup = (r["kind"], r["chunk_id"], r["segment_id"],
                       r["panel_id"], r["node_id"], r["re_str"], r["im_str"])
                results.append(tup)
                done_keys.add((r["kind"], r["chunk_id"], r["segment_id"],
                               r["panel_id"], r["node_id"]))
            if verbose:
                print(f"[chunk-certifier] Loaded {len(results)} cached "
                      f"results from {raw_cache_path}", flush=True)
        except Exception as e:
            if verbose:
                print(f"[chunk-certifier] WARN: could not load raw cache "
                      f"({e}); starting fresh", flush=True)
            results = []
            done_keys = set()

    # Filter work_units to those not in done_keys
    def _wu_key(item):
        if item.kind == "path_node":
            return ("path_node", item.chunk_id, item.segment_id,
                    item.panel_id, item.node_id)
        elif item.kind == "center_pp":
            return ("center_pp", item.chunk_id, -1, -1, -1)
        else:
            return ("center", item.chunk_id, -1, -1, -1)

    pending = [w for w in work_units if _wu_key(w) not in done_keys]
    n_total = len(work_units)
    n_pending = len(pending)
    n_errors = sum(1 for r in results if r[0] == "error")
    if verbose:
        print(f"[chunk-certifier] {n_pending}/{n_total} work units pending "
              f"({len(results)} already done, {n_errors} prior errors)",
              flush=True)

    if n_pending == 0:
        if verbose:
            print(f"[chunk-certifier] All work units cached — skipping Pool",
                  flush=True)
    else:
        report_every = max(1, n_pending // 50)  # ~50 progress lines
        save_every = max(20, n_pending // 100)  # snapshot ~100 times
        last_save_idx = 0
        tmp_path = raw_cache_path.with_suffix(raw_cache_path.suffix + ".tmp")

        def _flush_cache(current_results):
            raw_dump = [{"kind": k, "chunk_id": c, "segment_id": s,
                          "panel_id": p, "node_id": n,
                          "re_str": r, "im_str": i}
                         for (k, c, s, p, n, r, i) in current_results]
            with open(tmp_path, "w") as f:
                json.dump(raw_dump, f)
            os.replace(tmp_path, raw_cache_path)

        with Pool(min(n_workers, n_pending)) as pool:
            for idx, r in enumerate(
                pool.imap_unordered(_worker_h_eta_prime, pending,
                                    chunksize=1)):
                results.append(r)
                if r[0] == "error":
                    n_errors += 1
                    if verbose:
                        print(f"  WORKER ERROR cid={r[1]} seg={r[2]} "
                              f"panel={r[3]} node={r[4]} kind={r[6]}: {r[5]}",
                              flush=True)
                # Incremental save
                if (idx + 1) - last_save_idx >= save_every \
                        or idx + 1 == n_pending:
                    _flush_cache(results)
                    last_save_idx = idx + 1
                # Progress
                if verbose and ((idx + 1) % report_every == 0
                                or idx + 1 == n_pending):
                    elapsed = time.time() - t1
                    rate = (idx + 1) / max(elapsed, 1e-9)
                    eta = (n_pending - (idx + 1)) / max(rate, 1e-9)
                    print(f"  [{idx + 1:5d}/{n_pending}] "
                          f"{elapsed:6.1f}s elapsed, "
                          f"{rate:.2f} items/s, "
                          f"ETA {eta:6.0f}s, "
                          f"errors={n_errors}, "
                          f"cached={last_save_idx}", flush=True)
        if verbose:
            print(f"[chunk-certifier] Pool done in {time.time() - t1:.1f}s,"
                  f" {n_errors} errors", flush=True)
            print(f"[chunk-certifier] Final raw cache → {raw_cache_path}",
                  flush=True)

    # ---------- Step 4: assemble per-chunk results --------------------
    Hp_center = {}      # cid -> acb (sharp H_η'(c))
    Hpp_center = {}     # cid -> acb (sharp H_η''(c))
    Hp_path = {}        # (cid, seg_id, panel_id, node_id) -> acb
    bad_chunks = set()  # chunks with at least one worker error
    for tup in results:
        kind = tup[0]
        cid = tup[1]
        if kind == "error":
            bad_chunks.add(cid)
            continue
        seg, p_id, nid, re_s, im_s = tup[2], tup[3], tup[4], tup[5], tup[6]
        val = acb(arb(re_s), arb(im_s))
        if kind == "center":
            Hp_center[cid] = val
        elif kind == "center_pp":
            Hpp_center[cid] = val
        else:
            Hp_path[(cid, seg, p_id, nid)] = val
    if verbose and bad_chunks:
        print(f"[chunk-certifier] Skipping {len(bad_chunks)} bad chunks: "
              f"{sorted(bad_chunks)}", flush=True)

    # Assemble H_η(c) per chunk: per-panel GL sum × panel length, plus
    # adaptive-ρ Bernstein outer error bound per panel.
    from h_eta_parallel_path import _adaptive_rho, _path_gl_error_bound
    H_eta_per_chunk = {}
    chunks_dict = {cid: (edge, a, b, hr, hi) for (cid, edge, a, b, hr, hi)
                    in chunks}
    for cid, (edge, a, b, hr, hi) in chunks_dict.items():
        H_eta = acb(0)
        total_err = arb(0)
        for seg_id in [0, 1]:
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

                # Per-panel adaptive-ρ error bound
                try:
                    rho = _adaptive_rho(z_p_start, z_p_end, eta_arb, "v26",
                                          prec=prec)
                    err_p = _path_gl_error_bound(z_p_start, z_p_end, rho,
                                                   n_gl_path, eta_arb, "v26",
                                                   prec=prec)
                except ValueError as e:
                    if verbose:
                        print(f"  chunk {cid:3d} seg {seg_id} panel {p_id}:"
                              f" ρ search failed: {e}", flush=True)
                    err_p = arb("inf")
                total_err = total_err + err_p

        # Inflate radius by total path GL error
        re = H_eta.real
        im = H_eta.imag
        H_eta_certified = acb(arb.union(re - total_err, re + total_err),
                                arb.union(im - total_err, im + total_err))
        H_eta_per_chunk[cid] = H_eta_certified

    # ---------- Step 5: serialize and save ----------------------------
    chunks_out = []
    for (cid, edge, a, b, hr, hi) in chunks:
        H_eta = H_eta_per_chunk.get(cid, acb(0))
        Hp = Hp_center.get(cid, acb(0))
        Hpp = Hpp_center.get(cid, acb(0))
        m2 = m2_per_chunk.get(cid, arb(0))
        status = "error" if cid in bad_chunks else "ok"
        chunks_out.append({
            "chunk_id": cid,
            "status": status,
            "edge": edge,
            "center_re": a.str(prec // 3),
            "center_im": b.str(prec // 3),
            "half_re": hr.str(prec // 3),
            "half_im": hi.str(prec // 3),
            "H_eta_re": H_eta.real.str(prec // 3),
            "H_eta_im": H_eta.imag.str(prec // 3),
            "Hp_re": Hp.real.str(prec // 3),
            "Hp_im": Hp.imag.str(prec // 3),
            "Hpp_re": Hpp.real.str(prec // 3),
            "Hpp_im": Hpp.imag.str(prec // 3),
            "M_2": m2.str(prec // 3),
        })

    output = {
        "n_chunks": len(chunks),
        "wall_time_s": time.time() - t0,
        "params": {
            "eta": eta_str, "delta": delta_str, "B": B_str,
            "n_per_edge": n_per_edge, "n_gl_path": n_gl_path,
            "n_panels_path": n_panels_path,
            "rho_path": rho_path_str, "L_inner": L_inner,
            "prec": prec, "rel_acc_bits": rel_acc_bits,
        },
        "chunks": chunks_out,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    if verbose:
        print(f"[chunk-certifier] Saved → {out_path}", flush=True)
        print(f"[chunk-certifier] Wall time: {output['wall_time_s']:.0f}s",
              flush=True)
    return output


# --------------------- Smoke test (limited n_per_edge) ----------------
def _smoke_test(n_per_edge: int = 4, n_workers: int = 16):
    """Run the certifier on a smaller chunk count for a quick smoke test."""
    print("\n" + "=" * 72, flush=True)
    print(f"SMOKE TEST: n_per_edge={n_per_edge} → "
          f"{4 * n_per_edge} chunks", flush=True)
    print("=" * 72, flush=True)
    out_path = (_HERE.parent / "Cache" /
                f"v26_chunk_certifier_smoke_npe{n_per_edge}.json")
    output = certify_all_chunks(
        n_workers=n_workers,
        n_per_edge=n_per_edge,
        out_path=out_path,
        verbose=True,
    )
    # Print first chunk's results
    print(flush=True)
    print(f"Sample chunk #0:", flush=True)
    c0 = output["chunks"][0]
    for k, v in c0.items():
        if isinstance(v, str) and len(v) > 60:
            v = v[:55] + "…"
        print(f"  {k:12s}: {v}", flush=True)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--smoke", action="store_true",
                         help="Run smoke test with reduced n_per_edge")
    parser.add_argument("--n_per_edge", type=int, default=N_PER_EDGE)
    parser.add_argument("--n_workers", type=int, default=DEFAULT_N_WORKERS)
    parser.add_argument("--n_gl_path", type=int, default=N_GL_PATH)
    parser.add_argument("--n_panels_path", type=int, default=N_PANELS_PATH)
    args = parser.parse_args()

    if args.smoke:
        out_path = (_HERE.parent / "Cache" /
                    f"v26_chunk_certifier_smoke_npe{args.n_per_edge}.json")
        certify_all_chunks(
            n_workers=args.n_workers,
            n_per_edge=args.n_per_edge,
            n_gl_path=args.n_gl_path,
            n_panels_path=args.n_panels_path,
            out_path=out_path,
            verbose=True,
        )
    else:
        certify_all_chunks(
            n_workers=args.n_workers,
            n_per_edge=args.n_per_edge,
            n_gl_path=args.n_gl_path,
            n_panels_path=args.n_panels_path,
            verbose=True,
        )
