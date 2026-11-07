"""Core truncation-free oracle bundle.

`TruncFreeBundle` holds the eight oracle quantities derived from a
single chunks JSON; `compute_bundle` produces one (writing an
`audit_naive_results.json` next to the chunks for cache reuse);
`round3()` / `production()` pull from the canonical 2026-05-03
backups.

This module imports the patched chunk-bound chain from `Scratch/`
(`joint_merged_uderiv`, `phi_pp_chunk_bound_eta_tight`,
`phi_prime_chunk_bound_certified`, `h_eta_pp_chunk_bound_certified`,
`chunk_constants_safe`, `gaussian_tail_bounds`) by adding
`ProofRefinement/Lemma54/Scratch/` to `sys.path`. None of those
files import the K_max-truncated `eval_H_eta_at_acb`; they stand on
the path-integration / Price-formula / closed-form-tail evaluators
described in `PATCH_NOTES.md` §2a.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from flint import arb, acb, ctx as flint_ctx

from .._arb_helpers import arb_to_rational_ub
from ..types import OracleResult


# --- Path injection ---------------------------------------------------------
# Scratch/ holds the truncation-free chunk-bound chain. It is intentionally
# kept under Scratch/ (rather than ported into Numerical_Library/) so future
# rigor patches can land without disturbing the harness's oracle audit
# pipeline. The path is added once at module load.
_LEMMA54 = Path(__file__).resolve().parents[2]
_SCRATCH = _LEMMA54 / "Scratch"
if str(_SCRATCH) not in sys.path:
    sys.path.insert(0, str(_SCRATCH))


# --- Canonical caches (PATCH_NOTES §2e) -------------------------------------
_BACKUP_PRODUCTION = (_LEMMA54 / "Cache" / "Backups"
                       / "2026-05-03_production")
_BACKUP_SUBDIVISION = (_LEMMA54 / "Cache" / "Backups"
                        / "2026-05-03_subdivision")

_PRESETS = {
    "production": {
        "chunks": _BACKUP_PRODUCTION / "v26_chunk_certifier_npe16.json",
        "audit":  _BACKUP_PRODUCTION / "audit_naive_results.json",
        "merged_cr": _BACKUP_PRODUCTION
                      / "joint_merged_cr_rigorous_full64.json",
        "label": "production_no_subdiv",
    },
    "round3": {
        "chunks": _BACKUP_SUBDIVISION / "round3_v26_corner_split_v3.json",
        "audit":  _BACKUP_SUBDIVISION / "audit_naive_results.json",
        "merged_cr": _BACKUP_SUBDIVISION
                      / "round3_joint_merged_cr_rigorous.json",
        "label": "round3_subdivided",
    },
}


def canonical_chunks_path(source: str = "round3") -> Path:
    """Return the canonical chunks JSON for `source ∈ {round3, production}`."""
    if source not in _PRESETS:
        raise ValueError(f"unknown source {source!r}; "
                          f"valid: {sorted(_PRESETS)}")
    return _PRESETS[source]["chunks"]


def canonical_audit_path(source: str = "round3") -> Path:
    """Return the canonical audit JSON for `source ∈ {round3, production}`."""
    if source not in _PRESETS:
        raise ValueError(f"unknown source {source!r}; "
                          f"valid: {sorted(_PRESETS)}")
    return _PRESETS[source]["audit"]


# --- Bundle dataclass -------------------------------------------------------
_ORACLE_NAMES = (
    "M_phi", "M_phi_prime", "M_pp", "inv_F_p_z", "u_zz_bound",
    "joint_phi_phip_invD2", "uzz_phi_sq", "merged_uderiv",
)


@dataclass
class TruncFreeBundle:
    """All eight truncation-free oracles computed from one chunks JSON.

    Each `arb` field is an interval-arithmetic upper bound on the named
    sup-norm quantity. Use `as_oracle_result(name, ...)` to rationalise
    one into a Lean-consumable `OracleResult`.
    """

    M_phi: arb
    M_phi_prime: arb
    M_pp: arb
    inv_F_p_z: arb
    u_zz_bound: arb
    joint_phi_phip_invD2: arb
    uzz_phi_sq: arb
    merged_uderiv: arb
    inf_D: arb
    label: str
    chunks_path: str
    n_p_cells: int
    n_chunks: int
    prec: int = 200
    audit_json_path: Optional[str] = None
    info: dict[str, Any] = field(default_factory=dict)

    def as_arb(self, name: str) -> arb:
        if name not in _ORACLE_NAMES:
            raise ValueError(f"unknown oracle {name!r}; "
                              f"valid: {_ORACLE_NAMES}")
        return getattr(self, name)

    def as_oracle_result(
        self,
        name: str,
        *,
        safety_rel: float = 1e-3,
        safety_abs: float = 1e-4,
        max_denom: int = 10_000_000,
    ) -> OracleResult:
        """Rationalise the named oracle to an `OracleResult`."""
        x = self.as_arb(name)
        bound = arb_to_rational_ub(
            x,
            safety_rel=safety_rel,
            safety_abs=safety_abs,
            max_denom=max_denom,
        )
        return OracleResult(
            bound=bound,
            ball_value=float(x.upper()),
            prec=self.prec,
            meta={
                "oracle": name,
                "source_label": self.label,
                "chunks_path": self.chunks_path,
                "n_p_cells": self.n_p_cells,
                "n_chunks": self.n_chunks,
                "audit_json_path": self.audit_json_path,
                "ball_str": x.str(20, more=True),
            },
        )

    def as_dict(self) -> dict[str, Any]:
        """JSON-friendly snapshot (matches `audit_naive_results.json`)."""
        return {
            "label": self.label,
            "chunks_path": self.chunks_path,
            "n_p_cells": self.n_p_cells,
            "n_chunks": self.n_chunks,
            "prec": self.prec,
            "oracles": {
                name: getattr(self, name).str(20, more=True)
                for name in _ORACLE_NAMES
            } | {
                "inf_D_global": self.inf_D.str(20, more=True),
            },
            "info": self.info,
        }

    def summary(self) -> str:
        """Human-readable one-block summary."""
        lines = [
            f"TruncFreeBundle [{self.label}]",
            f"  chunks: {self.chunks_path}",
            f"  n_chunks={self.n_chunks}, n_p_cells={self.n_p_cells}, "
            f"prec={self.prec}",
        ]
        for name in _ORACLE_NAMES:
            v = getattr(self, name)
            lines.append(f"  {name:<24} = {float(v.upper()):.6e}")
        lines.append(f"  {'inf|D|':<24} = {float(self.inf_D.upper()):.6e}")
        return "\n".join(lines)


# --- Audit-JSON serialisation ----------------------------------------------
def from_audit_json(audit_path: str | Path) -> TruncFreeBundle:
    """Load a previously-computed audit JSON into a TruncFreeBundle.

    Reads the schema written by `Scratch/_naive_audit.py` (and by
    `compute_bundle` below). No flint computation; just JSON parsing.
    """
    flint_ctx.prec = 200  # parsing arb strings needs adequate precision
    p = Path(audit_path)
    data = json.load(open(p))
    o = data["oracles"]

    def _get(name: str) -> arb:
        if name in o:
            return arb(o[name])
        raise KeyError(f"audit JSON missing oracle {name!r}")

    return TruncFreeBundle(
        M_phi=_get("M_phi"),
        M_phi_prime=_get("M_phi_prime"),
        M_pp=_get("M_pp"),
        inv_F_p_z=_get("inv_F_p_z"),
        u_zz_bound=_get("u_zz_bound"),
        joint_phi_phip_invD2=_get("joint_phi_phip_invD2"),
        uzz_phi_sq=_get("uzz_phi_sq"),
        merged_uderiv=_get("merged_uderiv"),
        inf_D=arb(o["inf_D_global"]),
        label=data.get("label", p.stem),
        chunks_path=data.get("chunks_path", "<unknown>"),
        n_p_cells=int(data.get("n_p_cells", 8)),
        n_chunks=int(data.get("n_chunks", 0)),
        prec=int(data.get("prec", 200)),
        audit_json_path=str(p),
        info=data.get("info", {}),
    )


# --- Compute from chunks JSON ----------------------------------------------
def compute_bundle(
    chunks_path: str | Path,
    *,
    n_p_cells: int = 8,
    prec: int = 200,
    p_max_str: str = "1",
    use_cache: bool = True,
    audit_path: Optional[str | Path] = None,
    label: Optional[str] = None,
    verbose: bool = False,
) -> TruncFreeBundle:
    """Compute the eight truncation-free oracles from a chunks JSON.

    The chunks JSON must follow the schema produced by
    `Scratch/parallel_chunk_certifier.py` /
    `Scratch/corner_subdivision_certifier.py` (each chunk has
    `chunk_id`, `edge`, `center_re`, `center_im`, `half_re`, `half_im`,
    sharp `H_eta_*`, `Hp_*`, `Hpp_*`).

    Caching: if `use_cache=True` (default) and `audit_path` already
    exists with matching `(chunks_path, n_p_cells, prec)`, the cached
    bundle is returned immediately. Pass `audit_path=None` to derive
    the default location (next to the chunks JSON).

    Returns a `TruncFreeBundle` and writes/updates the audit JSON on
    every fresh compute.
    """
    chunks_p = Path(chunks_path).resolve()
    if audit_path is None:
        audit_p = chunks_p.with_name(
            f"{chunks_p.stem}__truncfree_audit.json"
        )
    else:
        audit_p = Path(audit_path).resolve()

    # Cache-hit?
    if use_cache and audit_p.exists():
        try:
            cached = json.load(open(audit_p))
            ok = (cached.get("chunks_path") == str(chunks_p)
                   and int(cached.get("n_p_cells", -1)) == n_p_cells
                   and int(cached.get("prec", -1)) == prec)
            if ok:
                if verbose:
                    print(f"[truncfree] cache hit: {audit_p}", flush=True)
                bundle = from_audit_json(audit_p)
                # Replace label if user passed one
                if label is not None:
                    bundle.label = label
                return bundle
        except (json.JSONDecodeError, KeyError, ValueError) as e:
            if verbose:
                print(f"[truncfree] cache invalid ({e}); recomputing",
                      flush=True)

    # Compute fresh
    bundle = _compute_bundle_fresh(
        chunks_path=chunks_p,
        n_p_cells=n_p_cells,
        prec=prec,
        p_max_str=p_max_str,
        label=label,
        verbose=verbose,
    )
    # Persist audit JSON (include the candidate table so the saved file
    # is a drop-in replacement for the legacy _naive_audit.py output).
    audit_p.parent.mkdir(parents=True, exist_ok=True)
    out = bundle.as_dict()
    out["audit_json_path"] = str(audit_p)
    out["constants"] = {
        "r": "23/25", "R": "23/20", "p_max": p_max_str,
    }
    # Lazy import to avoid circular dependency at module load.
    from .candidate_audit import audit_all_candidates  # noqa: E402
    out["candidates"] = [r.to_dict() for r in audit_all_candidates(bundle=bundle)]
    with open(audit_p, "w") as f:
        json.dump(out, f, indent=2)
    bundle.audit_json_path = str(audit_p)
    if verbose:
        print(f"[truncfree] wrote → {audit_p}", flush=True)
    return bundle


def _compute_bundle_fresh(
    chunks_path: Path,
    n_p_cells: int,
    prec: int,
    p_max_str: str,
    label: Optional[str],
    verbose: bool,
) -> TruncFreeBundle:
    """Heavy lifting: chunk_sup_bounds + per-cell joint sweep."""
    # These come from Scratch/ (path injected at module load)
    from joint_merged_uderiv import (  # noqa: E402
        _chunk_sup_bounds, _h0_closed,
    )
    # _eval_three_at_cell is in Scratch/_naive_audit.py; reuse to avoid
    # duplicating the merged + joint + uzz_phi_sq evaluator.
    from _naive_audit import _eval_three_at_cell  # noqa: E402

    flint_ctx.prec = prec
    data = json.load(open(chunks_path))
    chunks = data["chunks"]
    eta_arb = arb(data["params"]["eta"])
    p_max = arb(p_max_str)
    n_chunks = len(chunks)
    if verbose:
        print(f"[truncfree] processing {n_chunks} chunks "
              f"× {n_p_cells} p-cells = {n_chunks * n_p_cells} cells",
              flush=True)

    # Per-chunk sup bounds (slow part)
    chunk_data = []
    for i, ch in enumerate(chunks):
        if verbose and i % 16 == 0:
            print(f"  chunk_sup {i}/{n_chunks}", flush=True)
        c_re = arb(ch["center_re"])
        c_im = arb(ch["center_im"])
        hr = arb(ch["half_re"])
        hi = arb(ch["half_im"])
        z_box = acb(arb.union(c_re - hr, c_re + hr),
                     arb.union(c_im - hi, c_im + hi))
        try:
            sup = _chunk_sup_bounds(z_box, eta_arb, c_re, c_im, hr, hi, prec)
        except Exception as e:
            if verbose:
                print(f"  chunk {ch['chunk_id']}: sup ERROR {e}", flush=True)
            continue
        chunk_data.append({"ch": ch, "sup": sup,
                             "c_re": c_re, "c_im": c_im,
                             "hr": hr, "hi": hi})

    # Global per-chunk scalars
    M_phi = arb(0); M_phi_prime = arb(0); M_pp = arb(0)
    inf_D_global = arb("inf")
    for cd in chunk_data:
        ch = cd["ch"]; sup = cd["sup"]
        c_re, c_im, hr, hi = cd["c_re"], cd["c_im"], cd["hr"], cd["hi"]
        chunk_radius = (hr * hr + hi * hi).sqrt()
        c = acb(c_re, c_im)
        H_eta_c = acb(arb(ch["H_eta_re"]), arb(ch["H_eta_im"]))
        Phi_c = H_eta_c - _h0_closed(c)
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
        raise RuntimeError("inf|D| ≤ 0 globally — denominator unsafe")
    inv_F_p_z = arb(1) / inf_D_global
    u_zz_bound = M_pp * inv_F_p_z * inv_F_p_z * inv_F_p_z

    # Per-(chunk, p-cell) joint sups
    p_cells = []
    for k in range(n_p_cells):
        p_lo = p_max * arb(k) / arb(n_p_cells)
        p_hi = p_max * arb(k + 1) / arb(n_p_cells)
        p_cells.append((p_lo, p_hi))

    sup_joint = arb(0); sup_uzz_phi_sq = arb(0); sup_merged = arb(0)
    info = {"binding": {}}
    cells_done = 0
    total_cells = len(chunk_data) * n_p_cells
    for cd in chunk_data:
        ch = cd["ch"]; sup = cd["sup"]
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
                c_re, c_im, hr, hi, sup, p_mid, p_rad, prec,
            )
            if scores["joint"].upper() > sup_joint.upper():
                sup_joint = scores["joint"]
                info["binding"]["joint"] = (ch["chunk_id"], ch["edge"], k)
            if scores["uzz_phi_sq"].upper() > sup_uzz_phi_sq.upper():
                sup_uzz_phi_sq = scores["uzz_phi_sq"]
                info["binding"]["uzz_phi_sq"] = (ch["chunk_id"],
                                                   ch["edge"], k)
            if scores["merged"].upper() > sup_merged.upper():
                sup_merged = scores["merged"]
                info["binding"]["merged"] = (ch["chunk_id"], ch["edge"], k)
            cells_done += 1
        if verbose and cells_done % 64 == 0:
            print(f"  cells {cells_done}/{total_cells}: "
                  f"joint={float(sup_joint.upper()):.3e} "
                  f"uzz={float(sup_uzz_phi_sq.upper()):.3e} "
                  f"merged={float(sup_merged.upper()):.3e}", flush=True)

    return TruncFreeBundle(
        M_phi=M_phi,
        M_phi_prime=M_phi_prime,
        M_pp=M_pp,
        inv_F_p_z=inv_F_p_z,
        u_zz_bound=u_zz_bound,
        joint_phi_phip_invD2=sup_joint,
        uzz_phi_sq=sup_uzz_phi_sq,
        merged_uderiv=sup_merged,
        inf_D=inf_D_global,
        label=label or chunks_path.stem,
        chunks_path=str(chunks_path),
        n_p_cells=n_p_cells,
        n_chunks=len(chunk_data),
        prec=prec,
        info=info,
    )


# --- Presets ----------------------------------------------------------------
def round3(*, recompute: bool = False, verbose: bool = False) -> TruncFreeBundle:
    """Canonical round-3 subdivided chunks (Cr ≈ 0.38).

    By default loads the cached audit JSON in
    `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json`.
    Pass `recompute=True` to force a fresh sweep over the chunks JSON.
    """
    return _load_preset("round3", recompute=recompute, verbose=verbose)


def production(*, recompute: bool = False,
                verbose: bool = False) -> TruncFreeBundle:
    """Canonical production chunks (Cr ≈ 34.47, no subdivision).

    By default loads the cached audit JSON in
    `Cache/Backups/2026-05-03_production/audit_naive_results.json`.
    Pass `recompute=True` to force a fresh sweep.
    """
    return _load_preset("production", recompute=recompute, verbose=verbose)


def _load_preset(name: str, *, recompute: bool, verbose: bool) -> TruncFreeBundle:
    cfg = _PRESETS[name]
    audit = cfg["audit"]
    chunks = cfg["chunks"]
    if not recompute and audit.exists():
        if verbose:
            print(f"[truncfree] loading preset {name!r} from {audit}",
                  flush=True)
        bundle = from_audit_json(audit)
        bundle.label = cfg["label"]
        return bundle
    if verbose:
        print(f"[truncfree] computing preset {name!r} from {chunks}",
              flush=True)
    return compute_bundle(
        chunks,
        n_p_cells=8,
        prec=200,
        use_cache=not recompute,
        audit_path=audit,
        label=cfg["label"],
        verbose=verbose,
    )


# --- Per-oracle compute_*_bound wrappers (OracleResult shape) ---------------
def _make_compute_fn(oracle_name: str):
    def _compute(
        *,
        source: str = "round3",
        recompute: bool = False,
        safety_rel: float = 1e-3,
        safety_abs: float = 1e-4,
        max_denom: int = 10_000_000,
        verbose: bool = False,
    ) -> OracleResult:
        bundle = _load_preset(source, recompute=recompute, verbose=verbose)
        return bundle.as_oracle_result(
            oracle_name,
            safety_rel=safety_rel,
            safety_abs=safety_abs,
            max_denom=max_denom,
        )
    _compute.__name__ = f"compute_{oracle_name}_truncfree_bound"
    _compute.__doc__ = (
        f"Truncation-free OracleResult for `{oracle_name}` "
        f"derived from cached chunks. `source ∈ {{round3, production}}`. "
        f"Set `recompute=True` to force a fresh sweep."
    )
    return _compute


compute_M_phi_truncfree_bound = _make_compute_fn("M_phi")
compute_M_phi_prime_truncfree_bound = _make_compute_fn("M_phi_prime")
compute_M_pp_truncfree_bound = _make_compute_fn("M_pp")
compute_inv_F_p_z_truncfree_bound = _make_compute_fn("inv_F_p_z")
compute_u_zz_bound_truncfree_bound = _make_compute_fn("u_zz_bound")
compute_joint_phi_phip_invD2_truncfree_bound = _make_compute_fn(
    "joint_phi_phip_invD2"
)
compute_uzz_phi_sq_truncfree_bound = _make_compute_fn("uzz_phi_sq")
compute_merged_uderiv_truncfree_bound = _make_compute_fn("merged_uderiv")
