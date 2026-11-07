#!/usr/bin/env python3
"""P1 of the sprint-016 ablation (design doc sect. 13.2): measure the no-Lean
envelope of the frozen S0^16 surface and fix the BAR.

The envelope is the best (lowest) Cr_val reachable with ZERO new Lean: keep
V11's Lean proof routes byte-identical and only (a) re-pin declared `_val`s
down to certified oracle bounds, (b) tighten the oracles' resolution /
precision (a Numerical_Library numeral edit, which the sect. 12 Arm B
demonstrably performs). That is exactly: every route formula frozen in
`Lemma54_Paper.lean`, evaluated at each oracle's CONVERGED certified bound,
minimized over routes.

Runs inside the throwaway `groth16_envelope` workspace so that the arm
workspaces never see high-resolution .cache entries (information-leak guard).

Modes:
  sweep --oracle {M,M_phi,M_phi_prime,M_pp,inv_F_p_z}
      run the oracle at {1x, 2x, 4x, 8x} its module default n_per_edge,
      write runs/groth16_envelope/<name>.json
  combine
      read all sweeps, build the convergence table, evaluate every frozen
      route, propose BAR (largest "round" rational <= envelope/2), write
      runs/groth16_envelope/envelope.json
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

WS = Path(__file__).resolve().parents[1] / "workspaces" / "groth16_envelope"
L54 = WS / "ProofRefinement" / "Lemma54"
OUT = Path(__file__).resolve().parents[1] / "runs" / "groth16_envelope"

# oracle registry: name -> (module fn name, MODULE-DEFAULT n_per_edge, mults)
# (module default = what the evaluator's no-arg recompute uses; verified:
#  Evaluator.verify_oracle_axioms calls `fn()`. compute_M_bound_tight's real
#  defaults are n=8192/prec=600 per its sprint-009 retarget docstring.)
ORACLES = {
    "M":           ("compute_M_bound_tight",       8192, (1, 2)),
    "M_phi":       ("compute_M_phi_bound",         1024, (1, 2, 4, 8)),
    "M_phi_prime": ("compute_M_phi_prime_bound",   1024, (1, 2, 4, 8)),
    "M_pp":        ("compute_M_pp_bound",          1024, (1, 2, 4, 8)),
    "inv_F_p_z":   ("compute_inv_F_p_z_bound",      512, (1, 2, 4, 8)),
}

# V11's declared values (the re-pin-only baseline; from Candidates/V11.lean).
DECLARED = {
    "M": Fraction(428),
    "M_phi": Fraction(239, 5000),
    "M_phi_prime": Fraction(543, 10000),
    "M_pp": Fraction(5608, 100),
    "inv_F_p_z": Fraction(2),
}
R_VAL = None  # sinh-based; only the dominated legacy routes need it (float ok)


def sweep(name: str, ns: list[int] | None = None):
    sys.path.insert(0, str(L54))
    import importlib
    nl = importlib.import_module("Numerical_Library")
    fn_name, base_n, mults = ORACLES[name]
    fn = getattr(nl, fn_name)
    OUT.mkdir(parents=True, exist_ok=True)
    prior = OUT / f"{name}.json"
    rows = json.loads(prior.read_text())["rows"] if prior.exists() else []
    done = {r["n_per_edge"] for r in rows}
    todo = ns if ns else [base_n * m for m in mults]
    for n in todo:
        if n in done:
            continue
        t0 = time.time()
        res = fn(n_per_edge=n)
        dt = time.time() - t0
        bound = Fraction(res.bound) if not isinstance(res.bound, Fraction) else res.bound
        rows.append({"n_per_edge": n, "bound": str(bound),
                     "bound_float": float(bound),
                     "ball_value": str(getattr(res, "ball_value", "")),
                     "elapsed_s": round(dt, 1)})
        print(f"[envelope:{name}] n={n}: bound={bound} ({float(bound):.10g}) "
              f"in {dt:.1f}s", flush=True)
        rows.sort(key=lambda r: r["n_per_edge"])
        (OUT / f"{name}.json").write_text(json.dumps(
            {"oracle": name, "fn": fn_name, "default_n": base_n,
             "rows": rows}, indent=2))


def _routes(v: dict[str, Fraction], r: Fraction, R_hi: Fraction) -> dict[str, Fraction]:
    """Every Cr route frozen in the S0^16 Lemma54_Paper.lean, exactly."""
    one_m_r = 1 - r
    invFp_paper = 2 * R_hi / one_m_r
    return {
        # def Cr_phi_uzz r M_phi M_phi_prime inv_F_p_z M_pp  (V11's route)
        "Cr_phi_uzz": (v["M_phi"] * v["M_phi_prime"] * v["inv_F_p_z"] ** 2
                       + Fraction(1, 2) * v["M_pp"] * v["inv_F_p_z"] ** 3
                       * v["M_phi"] ** 2),
        # def Cr_phi_invD r M_phi M_phi_prime R inv_F_p_z    (V10's route)
        "Cr_phi_invD": (v["M_phi"] * v["M_phi_prime"] * v["inv_F_p_z"] ** 2
                        + 4 * R_hi / one_m_r ** 2 * v["M_phi"] ** 2),
        # def Cr_phi r M_phi M_phi_prime R                    (V9's route)
        "Cr_phi": (v["M_phi"] * v["M_phi_prime"] * invFp_paper ** 2
                   + 4 * R_hi / one_m_r ** 2 * v["M_phi"] ** 2),
        # def Cr_tight r M R
        "Cr_tight": 16 * v["M"] ** 2 * R_hi * (R_hi + 1) / one_m_r ** 2,
    }


def combine():
    import mpmath as mp
    mp.mp.dps = 50
    r = Fraction(23, 25)
    # R = R_val_paper(r): rational ceiling of the era R bound. Only the
    # dominated legacy routes consume it; a tight float->Fraction ceiling of
    # sinh-based R suffices and is conservative for THEIR envelope (any error
    # here cannot affect the winning route, which does not use R).
    R_hi = Fraction(str(mp.nstr(mp.sinh(mp.mpf(24) / 25) * (1 + mp.mpf("1e-6")), 12)))

    conv, defres, table = {}, {}, {}
    for name in ORACLES:
        d = json.loads((OUT / f"{name}.json").read_text())
        rows = sorted(d["rows"], key=lambda r: r["n_per_edge"])
        bounds = [Fraction(r["bound"]) for r in rows]
        best = min(bounds)                     # certified bounds only tighten
        conv[name] = best
        base_n = d.get("default_n", ORACLES[name][1])
        defrow = next((r for r in rows if r["n_per_edge"] == base_n), rows[0])
        defres[name] = Fraction(defrow["bound"])
        last, prev = bounds[-1], bounds[-2]
        rel = float(abs(last - prev) / (abs(prev) if prev else 1))
        table[name] = {"declared_v11": str(DECLARED[name]),
                       "rows": rows,
                       "default_res_bound": str(defres[name]),
                       "converged_bound": str(best),
                       "last_step_rel_change": rel,
                       "slack_vs_declared": float(DECLARED[name] / best)
                       if best else None}

    routes_conv = _routes(conv, r, R_hi)
    routes_defres = _routes(defres, r, R_hi)
    routes_decl = _routes(DECLARED, r, R_hi)
    envelope = min(routes_conv.values())
    winner = min(routes_conv, key=lambda k: routes_conv[k])

    # BAR: the largest "round" rational <= envelope/2 (sect. 13.2). Round =
    # unit fractions plus half-steps, so the paper can state it in one token.
    cands = sorted({Fraction(1, k) for k in
                    (2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 25, 32, 40, 50, 64,
                     80, 100, 128, 160, 200, 250, 256, 320, 400, 500, 640,
                     800, 1000, 1250, 1600, 2000, 2500, 3200, 4000, 5000,
                     6400, 8000, 10000, 12500, 16000, 20000, 25000, 32000,
                     40000, 50000, 64000, 100000)},
                   reverse=True)
    half = envelope / 2
    bar = next(c for c in cands if c <= half)

    out = {
        "protocol": "design doc sect. 13.2 (P1)",
        "workspace": str(WS),
        "parent": "V11, Cr_val = 1",
        "oracle_convergence": table,
        "routes_at_converged_bounds": {k: [str(x), float(x)]
                                       for k, x in routes_conv.items()},
        "routes_at_default_res_bounds": {k: [str(x), float(x)]
                                         for k, x in routes_defres.items()},
        "routes_at_declared_values": {k: [str(x), float(x)]
                                      for k, x in routes_decl.items()},
        "R_hi_used_for_legacy_routes": str(R_hi),
        "envelope": [str(envelope), float(envelope)],
        "envelope_route": winner,
        "repin_only_floor": [str(min(routes_decl.values())),
                             float(min(routes_decl.values()))],
        "improvement_at_envelope_vs_parent": float(1 / envelope),
        "BAR": [str(bar), float(bar)],
        "bar_margin_vs_envelope": float(envelope / bar),
        "original_sprint016_result": "1/32 = 0.03125",
        "original_clears_bar_by": float(bar / Fraction(1, 32)),
    }
    (OUT / "envelope.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["sweep", "combine"])
    ap.add_argument("--oracle", choices=list(ORACLES))
    ap.add_argument("--ns", help="comma list of explicit n_per_edge values")
    a = ap.parse_args()
    if a.mode == "sweep":
        ns = [int(x) for x in a.ns.split(",")] if a.ns else None
        sweep(a.oracle, ns)
    else:
        combine()
