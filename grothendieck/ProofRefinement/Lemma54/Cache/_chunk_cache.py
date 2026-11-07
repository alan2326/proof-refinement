"""Per-chunk cache for V26 max|H_η| certification.

Stores rigorous arb-ball results keyed by (eta, rectangle, GL_params,
chunk_position). Avoids redundant 60s integral evaluations across runs.

Schema:
    {
      "version": 1,
      "eta": "0.01",
      "rectangle": {"delta": "1635/10000", "B": "1115/1000"},
      "argmax": {  # certified sharp value at boundary argmax
        "w_re": str, "w_im": str,
        "H_re_mid": str, "H_re_rad": str,
        "H_im_mid": str, "H_im_rad": str,
        "gl_err": str, "tail_err": str,
        "params_key": "L=10,n_panels=10,n_gl=24,prec=200,gl_dps=80",
        "compute_time": float
      },
      "chunks": {
        "<canonical_key>": {
          "edge": str, "z_mid_re": str, "z_mid_im": str,
          "half_re": str, "half_im": str,
          "H_mid_re_mid": str, ...,
          "Hp_bound": str, "U_chunk": str,
          "params_key": str, "compute_time": float
        }
      }
    }
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

from flint import arb, acb, ctx as flint_ctx


def params_key(L_outer: int, n_panels: int, n_gl: int,
               prec: int, gl_dps: int) -> str:
    return (f"L={L_outer},n_panels={n_panels},n_gl={n_gl},"
            f"prec={prec},gl_dps={gl_dps}")


def chunk_key(edge: str, z_mid: acb, half_re: arb, half_im: arb) -> str:
    """Canonical key for a chunk."""
    return (f"{edge}|re={z_mid.real.str(20)}|im={z_mid.imag.str(20)}"
            f"|hre={half_re.str(20)}|him={half_im.str(20)}")


def acb_to_strs(z: acb, dps: int = 60) -> dict[str, str]:
    """Serialize an acb ball to a dict of decimal strings."""
    return {
        "re_mid": z.real.mid().str(dps),
        "re_rad": z.real.rad().str(20),
        "im_mid": z.imag.mid().str(dps),
        "im_rad": z.imag.rad().str(20),
    }


def acb_from_strs(d: dict[str, str], prec: int) -> acb:
    """Reconstruct acb from decimal-string dict."""
    flint_ctx.prec = prec
    re = arb(d["re_mid"])
    re_rad = arb(d["re_rad"])
    re = arb.union(re - re_rad, re + re_rad)
    im = arb(d["im_mid"])
    im_rad = arb(d["im_rad"])
    im = arb.union(im - im_rad, im + im_rad)
    return acb(re, im)


def arb_to_str(x: arb, dps: int = 60) -> dict[str, str]:
    return {"mid": x.mid().str(dps), "rad": x.rad().str(20)}


def arb_from_str(d: dict[str, str], prec: int) -> arb:
    flint_ctx.prec = prec
    mid = arb(d["mid"])
    rad = arb(d["rad"])
    return arb.union(mid - rad, mid + rad)


def load_cache(path: Path) -> dict:
    if not path.exists():
        return {
            "version": 1,
            "eta": None,
            "rectangle": None,
            "argmax": None,
            "chunks": {},
        }
    with path.open() as f:
        return json.load(f)


def save_cache(path: Path, cache: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w") as f:
        json.dump(cache, f, indent=2)
    tmp.replace(path)
