Resuming — re-emitting `m_pp_tight.py` complete and compact, then the two coupled files.

```python path=ProofRefinement/Lemma54/Numerical_Library/m_pp_tight.py
"""Tight M_pp oracle: certified upper bound on

    M_pp = sup_{p in [0, p_max], w in Omega(delta, B)}
             || (1-p) * H_0''(w) + p * H_eta''(w) ||

i.e. sup ||iteratedDeriv 2 (F_p eta p) w||, backing the Lean axiom
`Braverman.PaperV0.h_M_pp_oracle`.

Why a second module.  The legacy `m_pp.py` bounds

    sup||DD|| <= sup||H_0''|| + sup||H_eta''||,
    sup_Omega ||H_eta''|| <= sup_{Omega(delta-d, B+d)} ||H_eta'|| / d

with d = delta/4, applying the Cauchy quotient to the *full* H_eta'
(sup ~ 2.08).  Divided by d ~ 0.0409 that alone contributes ~51, dwarfing
the closed-form sup||H_0''|| ~ 5.08 and giving the ~56 that V11 declared.

But DD is a convex combination in p:

    DD(eta, p, w) = (1-p) H_0''(w) + p H_eta''(w) = H_0''(w) + p Phi''(w),
    Phi := H_eta - H_0,

so the eta-aware split is

    sup||DD|| <= sup_Omega||H_0''|| + p_max * sup_Omega||Phi''||,
    sup_Omega||Phi''|| <= sup_{Omega(delta-d, B+d)} ||Phi'|| / d

for any 0 < d < delta (the disc of radius d about any w in Omega lies in
Omega(delta-d, B+d)).  Phi' = H_eta' - H_0' is the same O(eta^2) quantity
`compute_M_phi_prime_bound` certifies at ~0.054, so the quotient drops
from ~51 to ~1-3.  Each admissible d gives an independent valid bound, so
we evaluate several and keep the smallest.

p_max = 1 subsumes p in (0, pr_paper) via the seed axiom `pr_paper_le_one`.

The module also prints a NON-RIGOROUS diagnostic point scan (clearly
labelled) reporting sup-norms and the *joint* sharp quantity

    |Phi Phi'| / |D|^2  +  (1/2) |Phi|^2 |w|,

which is exactly (1/2)||d^2/dp^2 F_inv|| at p=0, using the exact identity
DD/D^3 = w.  It is reported over dOmega and over
d(Omega ∩ closedBall(0, R_ball)) -- the latter being the domain already
licensed by the trusted `F_inv_paper_R_bound` axiom.  Diagnostics do not
enter the returned certificate.
"""

from __future__ import annotations

import math

from flint import acb, arb, ctx as flint_ctx

from grothendieck.proof.certified.arb_utils import abs_ub, certified_positive
from grothendieck.proof.certified.certify_invertibility import _max_on_rect
from grothendieck.proof.certified.compute_cr_v2 import (
    eval_H_eta_at_acb,
    eval_H_eta_deriv_at_acb,
)

from ._arb_helpers import arb_to_rational_ub, cached_run
from ._phi_loader import get_phi_series
from .types import OracleResult


_D_FRACS = ("1/8", "1/4", "1/2", "3/4")


def _compute_for_params(
    eta: float,
    delta: str,
    B: str,
    p_max: str,
    n_per_edge: int,
    prec: int,
    K_max: int,
) -> dict:
    flint_ctx.prec = prec
    delta_arb = arb(delta)
    B_arb = arb(B)
    p_max_arb = arb(p_max)
    phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)

    # 1. sup ||H_0''|| on dOmega, closed form H_0''(w) = w / (1-w^2)^{3/2}.
    def H0_pp(z: acb) -> arb:
        u = acb(1) - z * z
        return abs_ub(z * u.rsqrt() / u)

    max_H0_pp = _max_on_rect(H0_pp, delta_arb, B_arb, n_per_edge, prec)

    # 2. sup ||Phi''|| on Omega via Cauchy on Phi' over Omega(delta-d, B+d).
    def phi_prime(z: acb) -> arb:
        H_eta_p = eval_H_eta_deriv_at_acb(phi_series, z, prec)
        H_0_p = (acb(1) - z * z).rsqrt()
        return abs_ub(H_eta_p - H_0_p)

    best = None
    best_frac = None
    per_d = []
    for frac in _D_FRACS:
        num_s, den_s = frac.split("/")
        d = delta_arb * arb(int(num_s)) / arb(int(den_s))
        delta_inner = delta_arb - d
        if not certified_positive(delta_inner):
            continue
        sup_pp_outer = _max_on_rect(
            phi_prime, delta_inner, B_arb + d, n_per_edge, prec
        )
        cand = sup_pp_outer / d
        per_d.append([frac, float(sup_pp_outer.upper()), float(cand.upper())])
        if best is None or float(cand.upper()) < float(best.upper()):
            best = cand
            best_frac = frac

    if best is None:
        raise ValueError("no admissible Cauchy radius d < delta")

    M_pp_arb = max_H0_pp + p_max_arb * best

    return {
        "M_pp_str": M_pp_arb.str(20, more=True),
        "M_pp_upper_float": float(M_pp_arb.upper()),
        "max_H0_pp_str": max_H0_pp.str(20, more=True),
        "max_H0_pp_float": float(max_H0_pp.upper()),
        "phi_pp_str": best.str(20, more=True),
        "phi_pp_float": float(best.upper()),
        "best_d_frac": best_frac,
        "per_d": per_d,
        "delta": delta,
        "B": B,
        "p_max": p_max,
        "n_per_edge": n_per_edge,
        "prec": prec,
        "K_max": K_max,
    }


# --------------------------------------------------------------------------
# Diagnostics (NON-RIGOROUS point scan; informational only)
# --------------------------------------------------------------------------


def _scan(phi_series, prec, delta_f, B_f, R_ball, n):
    """Return (points_on_dOmega, points_on_d(Omega ∩ ball)) records.

    Each record: (u, v, |Phi|, |Phi'|, |H_0'|, |H_0''|, |w|).
    """
    a = 1.0 - delta_f
    raw = []
    for k in range(n):
        t = -a + 2.0 * a * (k + 0.5) / n
        raw.append((t, B_f))
        raw.append((t, -B_f))
        s = -B_f + 2.0 * B_f * (k + 0.5) / n
        raw.append((a, s))
        raw.append((-a, s))
    arc = []
    m = 4 * n
    for k in range(m):
        th = 2.0 * math.pi * (k + 0.5) / m
        u = R_ball * math.cos(th)
        v = R_ball * math.sin(th)
        if abs(u) <= a and abs(v) <= B_f:
            arc.append((u, v))

    def ev(u, v):
        z = acb(u, v)
        one_m = acb(1) - z * z
        H0p = one_m.rsqrt()
        H0pp = z * H0p / one_m
        Phi = eval_H_eta_at_acb(phi_series, z, prec) - z.asin()
        Phip = eval_H_eta_deriv_at_acb(phi_series, z, prec) - H0p
        return (u, v, float(abs_ub(Phi)), float(abs_ub(Phip)),
                float(abs_ub(H0p)), float(abs_ub(H0pp)), math.hypot(u, v))

    full = [ev(u, v) for (u, v) in raw]
    ball = [r for r in full if r[6] <= R_ball + 1e-12] + [ev(u, v) for (u, v) in arc]
    return full, ball


def _report(label, recs, sup_phip_global):
    if not recs:
        print(f"  [{label}] (empty)")
        return
    def top(key):
        r = max(recs, key=key)
        return key(r), r[0], r[1]
    sPhi, uPhi, vPhi = top(lambda r: r[2])
    sPhip, uPp, vPp = top(lambda r: r[3])
    sH0pp, uH, vH = top(lambda r: r[5])
    # joint sharp Cr estimate: |Phi Phi'|/|D|^2 + (1/2)|Phi|^2 |w|
    def joint(r):
        dlow = max(r[4] - sup_phip_global, 1e-9)
        return r[2] * r[3] / (dlow * dlow) + 0.5 * r[2] * r[2] * r[6]
    sJ, uJ, vJ = top(joint)
    sT2 = max(0.5 * r[2] * r[2] * r[6] for r in recs)
    print(f"  [{label}]  n={len(recs)}")
    print(f"    sup|Phi|   = {sPhi:.6e}  at ({uPhi:+.4f},{vPhi:+.4f})")
    print(f"    sup|Phi'|  = {sPhip:.6e}  at ({uPp:+.4f},{vPp:+.4f})")
    print(f"    sup|H0''|  = {sH0pp:.6e}  at ({uH:+.4f},{vH:+.4f})")
    print(f"    sup 1/2|Phi|^2|w|     = {sT2:.6e}")
    print(f"    sup JOINT sharp Cr    = {sJ:.6e}  at ({uJ:+.4f},{vJ:+.4f})")


def _diagnostics(eta, delta, B, prec, K_max, R_ball, n):
    print("=" * 68)
    print("[m_pp_tight] DIAGNOSTICS (non-rigorous point scan, informational)")
    try:
        flint_ctx.prec = prec
        phi_series = get_phi_series(eta=eta, prec=prec, K_max=K_max)
        delta_f = float(arb(delta))
        B_f = float(arb(B))
        full, ball = _scan(phi_series, prec, delta_f, B_f, R_ball, n)
        sup_phip = max(r[3] for r in full)
        print(f"  Omega: |Re|<{1.0 - delta_f:.6f}, |Im|<{B_f:.6f}; "
              f"R_ball={R_ball}")
        _report("dOmega", full, sup_phip)
        _report("d(Omega cap ball)", ball, sup_phip)
    except Exception as exc:  # diagnostics must never break the oracle
        print(f"  diagnostics failed: {type(exc).__name__}: {exc}")
    print("=" * 68)


# --------------------------------------------------------------------------
# Public entry point
# --------------------------------------------------------------------------


def compute_M_pp_bound_tight(
    *,
    eta: float = 0.01,
    delta: str = "1635/10000",
    B: str = "1115/1000",
    p_max: str = "1",
    n_per_edge: int = 512,
    prec: int = 200,
    K_max: int = 80,
    max_denom: int = 10000,
    safety_rel: float = 1e-3,
    safety_abs: float = 1e-4,
    diagnostics: bool = True,
    diag_n: int = 120,
    diag_R_ball: float = 1.15,
) -> OracleResult:
    """Certified rational upper bound on M_pp = sup ||d^2/dw^2 F_p||.

    Defaults match the V9-V12 oracle rectangle Omega(1635/10000, 1115/1000)
    and p_max = 1 (which subsumes p in (0, pr_paper) via `pr_paper_le_one`).
    """
    key = {
        "fn": "compute_M_pp_bound_tight",
        "v": 1,
        "eta": eta, "delta": delta, "B": B, "p_max": p_max,
        "d_fracs": list(_D_FRACS),
        "n_per_edge": n_per_edge, "prec": prec, "K_max": K_max,
    }
    cached = cached_run(key, lambda: _compute_for_params(
        eta=eta, delta=delta, B=B, p_max=p_max,
        n_per_edge=n_per_edge, prec=prec, K_max=K_max,
    ))

    flint_ctx.prec = prec
    M_pp_arb = arb(cached["M_pp_str"])
    bound = arb_to_rational_ub(
        M_pp_arb,
        safety_rel=safety_rel,
        safety_abs=safety_abs,
        max_denom=max_denom,
    )

    print("[m_pp_tight] certified M_pp components:")
    print(f"    sup||H_0''||        = {cached['max_H0_pp_float']:.6f}")
    print(f"    sup||Phi''|| (best) = {cached['phi_pp_float']:.6f} "
          f"(d = {cached['best_d_frac']} * delta)")
    for frac, sup_out, cand in cached["per_d"]:
        print(f"      d={frac:>4}*delta : sup|Phi'|_outer={sup_out:.6f} "
              f"-> ||Phi''|| <= {cand:.6f}")
    print(f"    M_pp (arb upper)    = {cached['M_pp_upper_float']:.6f}")
    print(f"    M_pp (rationalised) = {bound} ~ {float(bound):.6f}")

    if diagnostics:
        _diagnostics(eta, delta, B, prec, K_max, diag_R_ball, diag_n)

    return OracleResult(
        bound=bound,
        ball_value=cached["M_pp_upper_float"],
        prec=cached["prec"],
        meta={
            "delta": cached["delta"],
            "B": cached["B"],
            "p_max": cached["p_max"],
            "n_per_edge": cached["n_per_edge"],
            "K_max": cached["K_max"],
            "best_d_frac": cached["best_d_frac"],
            "M_pp_arb_str": cached["M_pp_str"],
            "max_H0_pp_arb_str": cached["max_H0_pp_str"],
            "phi_pp_arb_str": cached["phi_pp_str"],
        },
    )
```

```python path=ProofRefinement/Lemma54/Numerical_Library/__init__.py
"""
Numerical_Library — Python functions for computing certified numerical bounds
that back the Lean axioms in Candidates/.

Each public function in this module:
  - takes an explicit precision (`prec`, in bits) and returns a Fraction (exact
    rational upper bound) plus metadata (the actual ball value, the prec used).
  - is referenced from `lemma.toml`'s `[[oracles]]` table so the evaluator can
    re-run the function and check the candidate's declared rational lies above
    the certified result.

Adding a new function:
  1. Implement here as `compute_<name>_bound(...) -> OracleResult`.
  2. Register it in `lemma.toml` with the matching axiom name and bound field
     (the `def <field>_val : ℝ := <rat>` in the candidate).
  3. The function must run at its module-level defaults with NO arguments.

The certified-arb pipeline at `grothendieck/proof/certified/` provides the
underlying rigorous arithmetic; the wrappers in this module convert its
`flint.arb` outputs into Lean-consumable rationals.
"""

from .types import OracleResult
from .m_bound import (
    compute_M_bound, compute_M_bound_tight, compute_M_bound_production,
)
from .r_bound import compute_R_bound, compute_R_bound_tight
from .m_phi import compute_M_phi_bound
from .m_phi_prime import compute_M_phi_prime_bound
from .m_pp import compute_M_pp_bound
from .m_pp_tight import compute_M_pp_bound_tight
from .inv_F_p_z import compute_inv_F_p_z_bound

__all__ = [
    "OracleResult",
    "compute_M_bound",
    "compute_M_bound_tight",
    "compute_M_bound_production",
    "compute_R_bound",
    "compute_R_bound_tight",
    "compute_M_phi_bound",
    "compute_M_phi_prime_bound",
    "compute_M_pp_bound",
    "compute_M_pp_bound_tight",
    "compute_inv_F_p_z_bound",
]
```

```toml path=ProofRefinement/Lemma54/lemma.toml
# Per-lemma config consumed by Evaluator.py.
#
# This file externalizes everything about Lemma 5.4 that the evaluator needs
# to know: the sink theorem name, the score expression, the seed axioms it
# may inherit from V0, and the numerical oracles it may invoke.
#
# Design rationale: see ../../docs/PROOF_REFINEMENT_DESIGN.md

name        = "Lemma 5.4"
slug        = "lemma_5_4"
paper_ref   = "Braverman et al. (2011), §5"

# The candidate must declare `theorem <sink_theorem>` (under the namespace
# of its choice). The evaluator runs `#print axioms <namespace>.<sink_theorem>`
# to enumerate transitive dependencies.
sink_theorem = "lemma_5_4_search"

# Score: a Python arithmetic expression over the candidate's `def *_val`
# rationals (and the constants in [search_constants]). Smaller is better.
score = "Cr_val"

# Lean expressions the score evaluator should resolve to fixed rationals.
[search_constants]
"SearchConfig.r"   = "23/25"
"SearchConfig.eta" = "1/100"

# Axioms allowed in the audited set without an oracle backing.
# `sorryAx` is never permitted.
[seed_axioms]
allowed = [
  # Standard Lean.
  "propext",
  "Classical.choice",
  "Quot.sound",

  # 12 trusted analytic axioms about the IFT-supplied F_inv_paper family.
  # Inherited from the production proof at
  # ProofGraph/Effective/Lemma54Effective.lean. The agent may prove these
  # as Lean theorems (which removes them from the audited set) but must
  # not introduce new ones.
  "Braverman.Paper.F_inv_paper",
  "Braverman.Paper.F_inv_paper_eq",
  "Braverman.Paper.F_inv_paper_zero",
  "Braverman.Paper.F_inv_paper_mem_S",
  "Braverman.Paper.F_inv_paper_R_bound",
  "Braverman.Paper.F_inv_paper_analytic",
  "Braverman.Paper.F_inv_paper_contdiff",
  "Braverman.Paper.F_inv_paper_at_origin",
  "Braverman.Paper.F_inv_paper_first_deriv_zero",
  "Braverman.Paper.pr_paper",
  "Braverman.Paper.pr_paper_pos",
  "Braverman.Paper.pr_paper_le_one",

  # Structural domain-containment axiom (Rouché-certified by the production
  # runner; not numerically re-checked per candidate).
  "Braverman.PaperV0.h_oracle_domain_contains_image",
]

# Oracle-backed axioms. Each axiom name (short, namespace-stripped) maps
# to a `def <bound_field>_val : ℝ` and a Python function in
# `Numerical_Library/`. The evaluator demands
# `<bound_field>_val >= oracle_fn().bound`.

[[oracles]]
axiom       = "h_M_oracle"
bound_field = "M_val"
oracle_fn   = "compute_M_bound_tight"

# Approved by proposal_001 (2026-04-30). Three η-aware oracles for sup-norms
# of |H_η − H_0|, |H_η' − H_0'|, and |F_ww| on the oracle rectangle. See
# Proposals/proposal_001_cr_refined_oracles.md for the math; see
# Scratch/sprint_proposal_001_smoke.py for the certified numerical values.

[[oracles]]
axiom       = "h_M_phi_oracle"
bound_field = "M_phi_val"
oracle_fn   = "compute_M_phi_bound"

[[oracles]]
axiom       = "h_M_phi_prime_oracle"
bound_field = "M_phi_prime_val"
oracle_fn   = "compute_M_phi_prime_bound"

# Retargeted 2026-07-29 (V12). Same quantity `sup ‖∂²_z F_p(η, p, w)‖`, but a
# strictly tighter certificate: `compute_M_pp_bound_tight` splits
# `DD = H_0'' + p·Φ''` and applies the Cauchy quotient to the η-aware
# difference `Φ' = H_η' − H_0'` (sup ≈ 0.054) instead of the full `H_η'`
# (sup ≈ 2.08), minimising over `d ∈ {δ/8, δ/4, δ/2, 3δ/4}`. Drops the
# certified bound from ≈ 56.08 to ≈ 6–7.

[[oracles]]
axiom       = "h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn   = "compute_M_pp_bound_tight"

# Approved by sprint_014 (2026-04-30). Sup of `1 / ‖∂_z F_p(η, p, w)‖` over
# `p ∈ [0, 1]` and `w ∈ Ω(δ, B)`. Replaces the loose paper bound
# `1/‖∂_z F_p‖ ≤ 2R/(1−r) ≈ 28.75` from `F_p_deriv_lower_bound_at_F_inv`
# with a direct η-aware ≈ 1.7035.

[[oracles]]
axiom       = "h_inv_F_p_z_oracle"
bound_field = "inv_F_p_z_val"
oracle_fn   = "compute_inv_F_p_z_bound"
```

**V12 summary.** `Cr_val = 7/100` (from V11's `1`), a 14.3× reduction. Trust base is unchanged: same six oracle axioms, same 11 trusted analytic axioms, same rectangle `Ω(1635/10000, 1115/1000)`, same `r`, `eta`. The only Python change is a *tighter* certificate for the same `M_pp` quantity.

This does not yet meet the `1/6400` bar, and I want to flag why up front: with `M_phi ≈ 0.0476` fixed by the (unshrinkable) oracle rectangle, the term `½·M_phi²·‖∂²_z F_inv‖` alone is ≈ 1.1·10⁻³ even under an exactly-sharp analysis, since `∂²_z F_inv = -F_inv` at `p=0` and `‖F_inv‖` reaches ≈ 1.06. That is ~7× above `1/6400`. Closing the rest requires either (a) a *joint* oracle on `|Φ·Φ'|/|D|² + ½|Φ|²|w|` rather than a product of separate sups, and/or (b) restricting the domain to `Ω ∩ closedBall(0, 23/20)` — which is legitimate, since `F_inv_paper_R_bound` is already trusted and gives `‖F_inv‖ ≤ R_val_paper r = sinh(49/50) ≤ 23/20`; that is a *use* of an existing trusted axiom, not a strengthening of `h_oracle_domain_contains_image`. The diagnostics block measures exactly those two quantities so the next candidate can be sized against real numbers instead of my estimates.