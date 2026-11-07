"""Closed-form formulas matching the Lean `def`s in `ProofGraph/Effective/`.

The runner uses these to evaluate symbolic Lean defs (those that aren't
literal rationals) at a given assignment of literals.

Each function uses **arb arithmetic** (`flint.arb`) — never `float` —
because (a) the Lean side is `noncomputable` over ℝ and rationals don't
suffice for `sinh`, and (b) propagating float precision through the
chain loses the certified ~10⁻³⁸ improvement margin we care about.
The Lean side is `noncomputable`; we mirror its semantics exactly so
that comparing `lean_value` to `python_value` is meaningful.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Mapping


def _to_arb(x: Any) -> Any:
    """Coerce a Python value (Fraction, int, str, arb) into an arb."""
    from flint import arb
    if isinstance(x, arb):
        return x
    if isinstance(x, Fraction):
        return arb(x.numerator) / arb(x.denominator)
    if isinstance(x, (int, str)):
        return arb(x)
    if isinstance(x, float):
        # Floats are inexact — strongly discouraged. Convert via str() to
        # preserve the literal value rather than the binary IEEE float.
        return arb(str(x))
    raise TypeError(f"Cannot coerce to arb: {type(x).__name__}: {x!r}")


def R_val_paper(r: Any, prec: int = 256) -> Any:
    """`R_val_paper r := Real.sinh ((3 + r) / 4)` (from `Lemma54_Paper.lean`).

    Returns an arb interval. Use `arb_to_rational_ub` to extract a sound
    rational upper bound for downstream comparison with Lean rationals.
    """
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = prec
        r_a = _to_arb(r)
        return ((arb(3) + r_a) / arb(4)).sinh()
    finally:
        ctx.prec = old


def Cr_paper(r: Any, M: Any, R: Any, prec: int = 256) -> Any:
    """`Cr_paper r M R` from `Lemma54_Paper.lean` (paper-faithful single-`M`).

        Cr_paper r M R := 8 * M^2 * R / (1 - r)^2 * (1 + 16 * R / (1 - r)^3)

    Where `M ≥ max{|H_0|, |H_η|, |H_0'|, |H_η'|}` over the F_inv envelope.
    Returns an arb interval.
    """
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = prec
        r_a, M_a, R_a = _to_arb(r), _to_arb(M), _to_arb(R)
        one_minus_r = arb(1) - r_a
        lead = arb(8) * M_a ** 2 * R_a / one_minus_r ** 2
        inner = arb(1) + arb(16) * R_a / one_minus_r ** 3
        return lead * inner
    finally:
        ctx.prec = old


def Cr_refined(r: Any, M_diff: Any, M_diffp: Any, M_pp: Any, R: Any,
               prec: int = 256) -> Any:
    """`Cr_refined r M_diff M_diffp M_pp R` from `Lemma54_Paper.lean`.

        invFp := 2 * R / (1 - r)
        Cr_refined := M_diff * M_diffp * invFp^2 + M_pp * M_diff^2 * invFp^3 / 2

    The refined (tighter) form using sup-norms of *differences* `H_η - H_0`.
    Returns an arb interval.
    """
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = prec
        r_a, Md, Mdp, Mpp, R_a = (_to_arb(r), _to_arb(M_diff), _to_arb(M_diffp),
                                    _to_arb(M_pp), _to_arb(R))
        invFp = arb(2) * R_a / (arb(1) - r_a)
        return Md * Mdp * invFp ** 2 + Mpp * Md ** 2 * invFp ** 3 / arb(2)
    finally:
        ctx.prec = old


def KG_upper(gamma: Any, prec: int = 256) -> Any:
    """`KG_upper_val := π / (2 · γ)` from `KGBound.lean`. Returns arb."""
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = prec
        return arb.pi() / (arb(2) * _to_arb(gamma))
    finally:
        ctx.prec = old


def Krivine_bound(prec: int = 256) -> Any:
    """`KrivineBound := π / (2 · log(1+√2))` from `MainTheorem.lean`. Returns arb."""
    from flint import arb, ctx
    old = ctx.prec
    try:
        ctx.prec = prec
        return arb.pi() / (arb(2) * (arb(1) + arb(2).sqrt()).log())
    finally:
        ctx.prec = old


# --- Symbolic evaluator -----------------------------------------------------


def evaluate_symbolic(expr: str, env: dict[str, Any], prec: int = 256) -> Any | None:
    """Try to evaluate a symbolic Lean expression at an env mapping each
    Lean name to a Python value (Fraction or arb). Returns None if the
    expression isn't recognized; otherwise returns an arb.

    Currently recognizes:
      - `Cr_paper r M (R_val_paper r)` — paper-faithful single-`M` form.
      - `Cr_refined r M_diff M_diffp M_pp (R_val_paper r)` — refined form.
      - `Real.pi / (2 * gamma)` — requires `gamma` in env.
      - `R_val_paper r`.
    """
    s = expr.replace("Braverman.Paper.", "").replace("Braverman.Effective.", "").strip()
    s = s.replace("Braverman.", "")

    # Special: KG_upper-style. The denominator is the Theorem 5.1 witness,
    # historically named `gamma_val`, renamed to `gamma_explicit` after the
    # rational-sandwich refactor.
    if "Real.pi" in s and ("gamma_explicit" in s or "gamma_val" in s):
        gamma_key = "gamma_explicit" if "gamma_explicit" in env else "gamma_val"
        if gamma_key not in env:
            return None
        return KG_upper(env[gamma_key], prec=prec)
    if "KrivineBound" in s:
        return Krivine_bound(prec=prec)

    # Cr_refined r M_diff M_diffp M_pp (R_val_paper r)  — checked first since
    # `Cr_paper` is a prefix substring.
    if s.startswith("Cr_refined "):
        body = s[len("Cr_refined "):]
        if "(" not in body:
            return None
        before, after = body.rsplit("(", 1)
        names = before.strip().split()
        if len(names) != 4:
            return None
        r_n, md_n, mdp_n, mpp_n = names
        if not after.strip().startswith("R_val_paper"):
            return None
        try:
            r_v = env[r_n]
            md_v = env[md_n]
            mdp_v = env[mdp_n]
            mpp_v = env[mpp_n]
        except KeyError:
            return None
        R_v = R_val_paper(r_v, prec=prec)
        return Cr_refined(r_v, md_v, mdp_v, mpp_v, R_v, prec=prec)

    # Cr_paper r M (R_val_paper r)
    if s.startswith("Cr_paper "):
        body = s[len("Cr_paper "):]
        if "(" not in body:
            return None
        before, after = body.rsplit("(", 1)
        names = before.strip().split()
        if len(names) != 2:
            return None
        r_n, m_n = names
        if not after.strip().startswith("R_val_paper"):
            return None
        try:
            r_v = env[r_n]
            m_v = env[m_n]
        except KeyError:
            return None
        R_v = R_val_paper(r_v, prec=prec)
        return Cr_paper(r_v, m_v, R_v, prec=prec)

    # `R_val_paper r`
    if s.startswith("R_val_paper "):
        rest = s[len("R_val_paper "):].strip()
        if rest in env:
            return R_val_paper(env[rest], prec=prec)
        return None

    return None
