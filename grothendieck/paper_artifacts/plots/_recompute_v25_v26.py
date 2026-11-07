"""Recompute ΔK_G for V25 and V26 using their patched Cr ≈ 0.3734
(post-K_max patch, round-3 audit), then save into a small JSON.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from flint import arb, ctx as flint_ctx

_HERE = Path(__file__).resolve().parent
REPO = _HERE.parents[1]  # paper_artifacts/plots/ → repo root
SCRATCH = REPO / "ProofRefinement" / "Lemma54" / "Scratch"
sys.path.insert(0, str(SCRATCH))

CERT = Path("/home/rsaha/projects/grothendieck/ProofGraph/runs/"
            "2026-04-29T22-27-00/certificate.json")
B_SERIES = Path("/home/rsaha/projects/grothendieck/outputs/"
                "b_series_eta0p01_K250_dps100.json")

from grothendieck_what_if import load_certificate_inputs
from plot_cr_progression import compute_delta_gamma_for

PREC = 256
flint_ctx.prec = PREC

CR_PATCHED = "[0.37338044944511220646 +/- 2.76e-21]"

inputs = load_certificate_inputs(CERT)
cached_se: dict[int, object] = {}

results = {}
for v in (25, 26):
    print(f"Computing V{v} with Cr = {CR_PATCHED} ...", flush=True)
    dg, x = compute_delta_gamma_for(
        CR_PATCHED, inputs=inputs, cached_se=cached_se, verbose=False,
    )
    two_over_pi = arb(2) / arb.pi()
    dKG = two_over_pi * dg
    results[f"V{v}"] = {
        "Cr_str": CR_PATCHED,
        "Cr_float": float(arb(CR_PATCHED).lower()),
        "p_x": x,
        "delta_gamma_str": dg.str(30, more=True),
        "delta_gamma_float": float(dg.lower()),
        "delta_KG_str": dKG.str(30, more=True),
        "delta_KG_float": float(dKG.lower()),
    }
    print(f"  V{v}: p=10^-{x}, ΔK_G = {float(dKG.lower()):.4e}")

out_path = _HERE / "v25_v26_patched.json"
json.dump(results, open(out_path, "w"), indent=2)
print(f"\nWrote {out_path}")
