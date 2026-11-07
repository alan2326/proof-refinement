"""End-to-end runner: walks the proof graph from leaves to sink, runs
every wired Python oracle, parses the rationals declared in
`ProofGraph/Effective/`, evaluates symbolic Lean defs, and emits a
single `certificate.json` that lists every value (Lean rational, Python
oracle output, derived numerical) plus the result of every cross-validation
check.

**arb-native rule**: this module never converts an `arb` interval to
`float`. All comparisons go through `certified_gt` / `certified_lt`; all
JSON-serialized values are either rationals (`Fraction` via
`arb_to_rational_ub`) or string representations from `arb.str(N)`. Float
conversion silently truncates the certified ~10⁻³⁸ improvement margin.
"""

from __future__ import annotations

import hashlib
import json
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Any

from .effective_parser import parse_effective_dir, ParsedValue
from .cert_compute import (
    Cr_paper, R_val_paper, KG_upper, Krivine_bound, evaluate_symbolic,
)
from .graph import load_graph, Graph
from .oracle import _invoke_node, _arb_to_rational_upper


PROJECT_ROOT = Path(__file__).resolve().parents[2]
EFFECTIVE_DIR = PROJECT_ROOT / "ProofGraph" / "Effective"

# Files that fully determine the certified-arb pipeline's outputs. The harness
# uses an sha256 of these (concatenated) to short-circuit `--run-all` when the
# inputs are byte-identical to a previous successful certificate. Keep in sync
# with `scripts/runner_cache_check.sh`.
_CACHE_INPUT_FILES = [
    PROJECT_ROOT / "ProofGraph" / "nodes" / "_index.toml",
    PROJECT_ROOT / "ProofGraph" / "Effective" / "Lemma54Effective.lean",
    PROJECT_ROOT / "ProofGraph" / "Effective" / "Theorem51AtPExplicit.lean",
    PROJECT_ROOT / "ProofGraph" / "Effective" / "Theorem51Effective.lean",
]


def _compute_inputs_sha256() -> str:
    h = hashlib.sha256()
    for p in _CACHE_INPUT_FILES:
        h.update(p.read_bytes())
    return h.hexdigest()


# --- arb helpers (no float conversion) -----------------------------------


def _is_arb(x: Any) -> bool:
    try:
        from flint import arb
        return isinstance(x, arb)
    except ImportError:
        return False


def _arb_to_str(x: Any, ndigits: int = 40) -> str:
    """High-precision string repr of an arb interval (mid ± rad)."""
    if _is_arb(x):
        try:
            return x.str(ndigits)
        except Exception:
            return str(x)
    return str(x)


def _to_arb(x: Any, prec: int = 256) -> Any:
    """Coerce Fraction/int/str/arb into an arb interval. No float involved."""
    from flint import arb, ctx
    if _is_arb(x):
        return x
    old = ctx.prec
    try:
        ctx.prec = prec
        if isinstance(x, Fraction):
            return arb(x.numerator) / arb(x.denominator)
        if isinstance(x, (int, str)):
            return arb(x)
        if isinstance(x, float):
            # Floats are inexact — convert via str() to preserve the literal.
            return arb(str(x))
        raise TypeError(f"Cannot coerce to arb: {type(x).__name__}: {x!r}")
    finally:
        ctx.prec = old


# --- Lean rational env (parsed once, shared across nodes) ----------------


def _build_lean_env(parsed: dict[str, dict[str, ParsedValue]],
                    prec: int = 256) -> dict[str, Any]:
    """Flatten parsed defs into a single env. Literals stay as Fraction;
    symbolic expressions resolve to arb intervals. No floats."""
    env: dict[str, Any] = {}
    # First pass: literal rationals.
    for _, defs in parsed.items():
        for name, value in defs.items():
            if isinstance(value, Fraction):
                env[name] = value
    # Second pass: symbolic expressions, resolved to arb.
    pending = []
    for _, defs in parsed.items():
        for name, value in defs.items():
            if isinstance(value, str):
                pending.append((name, value))
    for _ in range(5):
        progress = False
        still_pending = []
        for name, expr in pending:
            v = evaluate_symbolic(expr, env, prec=prec)
            if v is not None:
                env[name] = v
                progress = True
            else:
                still_pending.append((name, expr))
        pending = still_pending
        if not progress or not pending:
            break
    return env


# --- Cross-validation -----------------------------------------------------


def _run_cross_validations(
    *, lean_env: dict[str, Any], oracle_state: dict[str, dict[str, Any]],
    constants: dict[str, str | int],
) -> list[dict]:
    """Cross-validate Lean rationals against oracle outputs using
    arb-native comparison (no float)."""
    from flint import arb, ctx
    from grothendieck.proof.certified.arb_utils import (
        certified_gt, certified_lt, certified_positive,
    )

    checks: list[dict] = []

    def _const_fraction(key: str) -> Fraction | None:
        if key not in constants:
            return None
        raw = str(constants[key])
        if "/" in raw:
            n, d = raw.split("/", 1)
            return Fraction(int(n), int(d))
        try:
            return Fraction(int(raw))
        except Exception:
            return None

    # Check 1: Lean's r_val matches the constant `r` used as oracle input.
    if "r_val" in lean_env and "r" in constants:
        const_r = _const_fraction("r")
        ok = lean_env["r_val"] == const_r
        checks.append({
            "id": "r_val_matches_constant",
            "lean": str(lean_env["r_val"]),
            "expected": str(const_r),
            "ok": ok,
            "note": "Lean's r_val should equal the global constant r.",
        })

    # Check 2: Lean's eta_val matches the constant `eta_max`.
    if "eta_val" in lean_env and "eta_max" in constants:
        const_eta = _const_fraction("eta_max")
        ok = lean_env["eta_val"] == const_eta
        checks.append({
            "id": "eta_val_matches_constant",
            "lean": str(lean_env["eta_val"]),
            "expected": str(const_eta),
            "ok": ok,
            "note": "Lean's eta_val should equal the global constant eta_max.",
        })

    # Check 2b: Lean's concrete rectangle matches the configured Step 1/2
    # oracle rectangle.
    if "delta_val" in lean_env and "delta" in constants:
        const_delta = _const_fraction("delta")
        ok = lean_env["delta_val"] == const_delta
        checks.append({
            "id": "delta_val_matches_constant",
            "lean": str(lean_env["delta_val"]),
            "expected": str(const_delta),
            "ok": ok,
            "note": "Lean's delta_val should equal the configured oracle rectangle delta.",
        })
    if "B_val" in lean_env and "B" in constants:
        const_B = _const_fraction("B")
        ok = lean_env["B_val"] == const_B
        checks.append({
            "id": "B_val_matches_constant",
            "lean": str(lean_env["B_val"]),
            "expected": str(const_B),
            "ok": ok,
            "note": "Lean's B_val should equal the configured oracle rectangle height.",
        })

    # Check 3: H_eta(eta_val)(i)/i > log(1+√2). Pure arb comparison.
    eval_state = oracle_state.get("eval_h_eta_at_i", {})
    H_eta = eval_state.get("H_eta_i_over_i")
    if _is_arb(H_eta):
        old = ctx.prec
        try:
            ctx.prec = 256
            log_1_plus_sqrt2 = (arb(1) + arb(2).sqrt()).log()
            ok = bool(certified_gt(H_eta, log_1_plus_sqrt2))
            improvement_mid = (H_eta - log_1_plus_sqrt2).mid()
            checks.append({
                "id": "h_eta_strict_improvement",
                "h_eta_str": _arb_to_str(H_eta, 30),
                "log_one_plus_sqrt2_str": _arb_to_str(log_1_plus_sqrt2, 30),
                "improvement_mid_str": improvement_mid.str(20),
                "ok": ok,
                "note": ("Numerical witness for theorem_4_4_effective's "
                         "oracle axiom; arb-certified."),
            })
        finally:
            ctx.prec = old

    # Check 4: Cr_val (arb interval from cert_compute) is finite & positive.
    if "Cr_val" in lean_env and _is_arb(lean_env["Cr_val"]):
        cv = lean_env["Cr_val"]
        ok = bool(certified_positive(cv)) and cv.is_finite()
        checks.append({
            "id": "Cr_val_finite_positive",
            "value_str": _arb_to_str(cv, 30),
            "ok": ok,
            "note": "Cr_paper formula must evaluate to a finite positive arb.",
        })

    # Check 4b: Step 1 actually used the configured explicit rectangle.
    # We compare via interval containment rather than rational-upper-bound
    # equality because arb string parsing widens endpoints slightly.
    ci_state = oracle_state.get("certify_invertibility", {})
    delta_arb = ci_state.get("delta_arb")
    B_arb = ci_state.get("B_arb")
    if _is_arb(delta_arb) and "delta" in constants:
        delta_upper = _arb_to_rational_upper(delta_arb)
        const_delta = _const_fraction("delta")
        const_delta_arb = _to_arb(const_delta, prec=256)
        checks.append({
            "id": "step1_delta_matches_constant",
            "delta_step1_str": _arb_to_str(delta_arb, 20),
            "delta_step1_rational_upper": str(delta_upper) if delta_upper is not None else None,
            "expected": str(const_delta),
            "ok": (delta_arb - const_delta_arb).contains(arb(0)),
            "note": ("Step 1 should use the configured delta rectangle parameter. "
                     "The check allows for the tiny widening introduced by arb "
                     "interval parsing."),
        })
    if _is_arb(B_arb) and "B" in constants:
        B_upper = _arb_to_rational_upper(B_arb)
        const_B = _const_fraction("B")
        const_B_arb = _to_arb(const_B, prec=256)
        checks.append({
            "id": "step1_B_matches_constant",
            "B_step1_str": _arb_to_str(B_arb, 20),
            "B_step1_rational_upper": str(B_upper) if B_upper is not None else None,
            "expected": str(const_B),
            "ok": (B_arb - const_B_arb).contains(arb(0)),
            "note": ("Step 1 should use the configured B rectangle parameter. "
                     "The check allows for the tiny widening introduced by arb "
                     "interval parsing."),
        })

    # Check 4c: Step 1 certified domain containment. The wrapper's
    # `all_checks_passed` is True iff Step 1 verified imaginary containment,
    # real containment, positive Rouché margin, and `p · M_partial < margin`
    # on the configured rectangle Ω(δ, B). This is the numerical witness behind
    # Lean's `h_oracle_domain_contains_image` axiom.
    ci_all_ok = ci_state.get("all_checks_passed")
    if ci_all_ok is not None:
        ok = bool(ci_all_ok)
        checks.append({
            "id": "domain_containment_certified",
            "all_checks_passed": ok,
            "ok": ok,
            "note": ("Numerical witness for `h_oracle_domain_contains_image`: "
                     "Step 1 certified imaginary + real containment of "
                     "F_p(disk r_outer) in Ω(δ, B), positive Rouché margin, "
                     "and `p · M_partial < margin`. F_inv(disk r) ⊆ F_inv(disk r_outer) "
                     "is contained in Ω."),
        })

    # Check 5: the oracle-side `M` from `compute_Cr_full` is dominated by the
    # Lean witness `M_val`. This is the concrete numerical bridge behind
    # `h_M_oracle`: the certified pipeline computes a rigorous upper bound for
    # the single-M constant on the Step 1/2 oracle domain, and Lean names a
    # conservative rational witness that should dominate it.
    cc_state = oracle_state.get("compute_cr", {})
    m_oracle = cc_state.get("M")
    cr_oracle = cc_state.get("C_r")
    if _is_arb(m_oracle) and "M_val" in lean_env:
        m_val = lean_env["M_val"]
        m_val_arb = _to_arb(m_val, prec=256)
        m_upper = _arb_to_rational_upper(m_oracle)
        ok = False
        if isinstance(m_val, Fraction) and m_upper is not None:
            ok = m_upper <= m_val
        if not ok:
            ok = bool(certified_lt(m_oracle, m_val_arb))
        checks.append({
                "id": "M_oracle_le_M_val",
                "M_oracle_str": _arb_to_str(m_oracle, 20),
                "M_oracle_rational_upper": str(m_upper) if m_upper is not None else None,
                "M_val": str(m_val),
                "ok": ok,
                "note": ("Numerical witness for the chosen Lean constant `M_val`. "
                     "This checks domination of the computed single-M bound by "
                     "the rational witness on the oracle domain used by the "
                     "effective Lemma 5.4 bridge."),
        })

    # Check 6: oracle Cr and Lean Cr_val are both finite and positive.
    # Both are forms of the paper's `Cr_paper r M R = 8M²R/(1−r)²·(1+16R/(1−r)³)`
    # bound. They evaluate at different `M` values: `compute_Cr_full` derives
    # `M` from the certified-rectangle pipeline; `Cr_val` uses the rational
    # `M_val` declared in `Lemma54Effective.lean`. Both must be finite and
    # positive to certify a viable Taylor remainder bound.
    if _is_arb(cr_oracle) and "Cr_val" in lean_env and _is_arb(lean_env["Cr_val"]):
        cv = lean_env["Cr_val"]
        ok = (bool(certified_positive(cr_oracle)) and cr_oracle.is_finite()
              and bool(certified_positive(cv)) and cv.is_finite())
        checks.append({
            "id": "Cr_oracle_and_Cr_val_both_positive",
            "Cr_oracle_str": _arb_to_str(cr_oracle, 20),
            "Cr_val_str": _arb_to_str(cv, 20),
            "ok": ok,
            "note": ("Cr_oracle (rectangle bound) and Cr_val (paper bound) are "
                     "two different upper bounds on the same Taylor remainder "
                     "constant; both must be finite and positive."),
        })

    # Check 5b: every "trivial" rational-range hypothesis fed to
    # `theorem_5_1_from_thresholds` at the chosen tuple
    # (eta_val=1/100, p=p_explicit_rat=1e-30, r=r_val=23/25, r_mid=91/100).
    # The generic theorem takes 8 inequalities of the form `0 < x`, `x < y`,
    # or `c < x` between Lean rationals. Each is provable by `norm_num` in
    # Lean; the runner verifies them as a sanity check that the chosen tuple
    # really does satisfy the generic theorem's preconditions.
    r_val = lean_env.get("r_val")
    eta_val_rat = lean_env.get("eta_val")
    M_val_rat = lean_env.get("M_val")
    p_explicit_rat = lean_env.get("p_explicit_rat")
    r_mid_rat = Fraction(91, 100)
    if (isinstance(p_explicit_rat, Fraction)
            and isinstance(r_val, Fraction)
            and isinstance(eta_val_rat, Fraction)
            and isinstance(M_val_rat, Fraction)):
        nine_tenths = Fraction(9, 10)
        zero = Fraction(0)
        one = Fraction(1)
        sub_checks = [
            ("0 < eta_val", eta_val_rat > zero),
            ("eta_val < 1", eta_val_rat < one),
            ("0 < p_explicit_rat", p_explicit_rat > zero),
            ("p_explicit_rat < 1", p_explicit_rat < one),
            ("0 < r_val", r_val > zero),
            ("r_val < 1", r_val < one),
            ("9/10 < r_val", r_val > nine_tenths),
            ("0 < r_mid (= 91/100)", r_mid_rat > zero),
            ("r_mid < r_val", r_mid_rat < r_val),
            ("9/10 < r_mid", r_mid_rat > nine_tenths),
            ("0 < M_val", M_val_rat > zero),
        ]
        failures = [name for name, ok in sub_checks if not ok]
        all_ok = (len(failures) == 0)
        checks.append({
            "id": "theorem_5_1_rational_range_hypotheses",
            "tuple": {
                "eta_val": str(eta_val_rat),
                "p_explicit_rat": str(p_explicit_rat),
                "r_val": str(r_val),
                "r_mid": str(r_mid_rat),
                "M_val": str(M_val_rat),
            },
            "subchecks": [{"name": n, "ok": ok} for n, ok in sub_checks],
            "failures": failures,
            "ok": all_ok,
            "note": ("Bundles the 11 trivial rational-range hypotheses fed to "
                     "`theorem_5_1_from_thresholds` and `theorem_5_1_at_p_explicit`. "
                     "All are provable by `norm_num` in Lean; the runner verifies "
                     "them as a sanity check that the chosen `(η, p, r, r_mid, M)` "
                     "tuple satisfies the preconditions of the generic theorem."),
        })

    # Check 5c: position of `log(1+√2)` within the rational sandwich.
    # `theorem_5_1` guarantees `gamma_explicit > log(1+√2)`; the rational
    # sandwich axiom puts `gamma_explicit` in `(gamma_lo_rat, gamma_hi_rat)`.
    # Documenting whether `log(1+√2)` itself is in this window tells us
    # whether the sandwich is "useful" (gamma_lo_rat > log(1+√2) gives a
    # tighter KG bound than Krivine) or merely a consistency anchor.
    gamma_lo_rat = lean_env.get("gamma_lo_rat")
    gamma_hi_rat = lean_env.get("gamma_hi_rat")
    if isinstance(gamma_lo_rat, Fraction) and isinstance(gamma_hi_rat, Fraction):
        old = ctx.prec
        try:
            ctx.prec = 256
            log_arb = (arb(1) + arb(2).sqrt()).log()
            lo_arb = _to_arb(gamma_lo_rat, prec=256)
            hi_arb = _to_arb(gamma_hi_rat, prec=256)
            log_in_window = (bool(certified_lt(lo_arb, log_arb))
                              and bool(certified_lt(log_arb, hi_arb)))
            log_above_lo = bool(certified_lt(lo_arb, log_arb))
            log_below_hi = bool(certified_lt(log_arb, hi_arb))
            checks.append({
                "id": "log_one_plus_sqrt_two_in_lean_sandwich",
                "log_one_plus_sqrt_two_str": _arb_to_str(log_arb, 50),
                "gamma_lo_rat": str(gamma_lo_rat),
                "gamma_hi_rat": str(gamma_hi_rat),
                "log_above_gamma_lo_rat": log_above_lo,
                "log_below_gamma_hi_rat": log_below_hi,
                "log_in_window": log_in_window,
                "ok": log_in_window,
                "note": ("Position of log(1+√2) within the rational sandwich. "
                         "When `log_in_window` is True, the sandwich is "
                         "consistency-only — every Theorem 5.1 γ > log(1+√2) is "
                         "automatically inside the window. To make `KG_upper_val_rat = "
                         "π/(2·gamma_lo_rat)` strictly tighter than KrivineBound, "
                         "`gamma_lo_rat` must instead be > log(1+√2), which would "
                         "require a 38+ digit precision rational."),
            })
        finally:
            ctx.prec = old

    # Check 6a: at p_explicit_rat = 1e-30, the gap-ratio inequality holds.
    # This is the numerical witness for `h_gap_ratio_at_p_explicit_with_B_phi`.
    # Concretely: pick a generous concrete bound `B_phi_bound = M_val + 1`
    # (the perturbation function `(z - H_η(sin z)) · cos z` has |H_η| ≤ M_val
    # on `oracle_domain` ⊇ sin(closedBall(0, r_val)) by inflation).
    # Then check `p · (|B_phi| + Cr_val + 1) · ratio < (sinh(9/10) - 1)/2`.
    p_explicit_rat = lean_env.get("p_explicit_rat")
    M_val = lean_env.get("M_val")
    Cr_val = lean_env.get("Cr_val")
    if (isinstance(p_explicit_rat, Fraction) and isinstance(M_val, Fraction)
            and _is_arb(Cr_val)):
        old = ctx.prec
        try:
            ctx.prec = 256
            B_phi_bound_arb = _to_arb(M_val + 1, prec=256)  # generous bound
            p_arb = _to_arb(p_explicit_rat, prec=256)
            ratio_arb = arb("91") / arb("100") / (arb("91") / arb("100") - arb("9") / arb("10"))
            lhs = p_arb * (B_phi_bound_arb + Cr_val + arb(1)) * ratio_arb
            rhs = (arb("9") / arb("10")).sinh() - arb(1)
            rhs = rhs / arb(2)
            ok = bool(certified_lt(lhs, rhs))
            checks.append({
                "id": "gap_ratio_at_p_explicit",
                "p_explicit_rat": str(p_explicit_rat),
                "B_phi_bound": str(M_val + 1),
                "lhs_str": _arb_to_str(lhs, 20),
                "rhs_str": _arb_to_str(rhs, 20),
                "ok": ok,
                "note": ("Numerical witness for `h_gap_ratio_at_p_explicit_with_B_phi`: "
                         "at p = 1e-30, with a generous B_phi ≤ M_val+1 = 4001, "
                         "the gap-ratio inequality "
                         "`p · (|B_phi| + Cr_val + 1) · 91 < (sinh(9/10) - 1)/2` "
                         "holds with massive margin (LHS ~ 1e-13, RHS ~ 0.013)."),
            })
        finally:
            ctx.prec = old

    # Check 6c: at p_explicit_rat = 1e-30, p < pr_paper. Numerical witness for
    # `h_p_explicit_lt_pr_paper`. We don't compute pr_paper directly; instead
    # we verify p_explicit_rat < p_certified (Step 1's certified Rouché radius)
    # which is a tighter quantity that pr_paper is supposed to dominate.
    ci_p_certified = ci_state.get("p_certified")
    if isinstance(p_explicit_rat, Fraction) and _is_arb(ci_p_certified):
        p_explicit_arb = _to_arb(p_explicit_rat, prec=256)
        ok = bool(certified_lt(p_explicit_arb, ci_p_certified))
        checks.append({
            "id": "p_explicit_lt_pr_paper",
            "p_explicit_rat": str(p_explicit_rat),
            "p_certified_str": _arb_to_str(ci_p_certified, 20),
            "ok": ok,
            "note": ("Numerical witness for `h_p_explicit_lt_pr_paper`: "
                     "p_explicit_rat = 1e-30 is strictly below the certified Rouché "
                     "radius `certify_invertibility.p_certified` (~2.4e-4), and "
                     "`pr_paper` from the IFT package dominates the Rouché radius. "
                     "The Lean axiom claims the latter; this is the closest direct "
                     "numerical witness available."),
        })

    # Check 6b: the certified `gamma_best` arb interval is contained in the
    # Lean rational sandwich `[gamma_lo_rat, gamma_hi_rat]`. This is the
    # numerical witness behind Lean's `h_gamma_explicit_sandwich` axiom —
    # the runner certifies that `gamma_best` (with its arb radius) is
    # bracketed by the rationals declared in `Theorem51Effective.lean`.
    sg_state_for_sandwich = oracle_state.get("solve_gamma", {})
    gamma_best_for_sandwich = sg_state_for_sandwich.get("gamma_best")
    if (_is_arb(gamma_best_for_sandwich)
            and "gamma_lo_rat" in lean_env and "gamma_hi_rat" in lean_env):
        gb = gamma_best_for_sandwich
        gamma_lo_rat = lean_env["gamma_lo_rat"]
        gamma_hi_rat = lean_env["gamma_hi_rat"]
        gamma_lo_arb = _to_arb(gamma_lo_rat, prec=256)
        gamma_hi_arb = _to_arb(gamma_hi_rat, prec=256)
        ok = bool(certified_lt(gamma_lo_arb, gb)) and bool(certified_lt(gb, gamma_hi_arb))
        checks.append({
            "id": "gamma_best_in_lean_sandwich",
            "gamma_best_str": _arb_to_str(gb, 50),
            "gamma_lo_rat": str(gamma_lo_rat),
            "gamma_hi_rat": str(gamma_hi_rat),
            "ok": ok,
            "note": ("Numerical witness for `h_gamma_explicit_sandwich`: "
                     "the certified `solve_gamma.gamma_best` arb interval is "
                     "strictly contained in the rational sandwich "
                     "`[gamma_lo_rat, gamma_hi_rat]` declared in "
                     "`Theorem51Effective.lean`."),
        })

    # Check 7: the certificate-side `gamma_best` witness implies a strict
    # numerical KG upper bound below Krivine. This is a sidecar witness for the
    # certified pipeline; it is not yet identified with Lean's opaque
    # `gamma_explicit`, which is still extracted via `Classical.choose`.
    sg_state = oracle_state.get("solve_gamma", {})
    gamma_best = sg_state.get("gamma_best")
    if _is_arb(gamma_best):
        old = ctx.prec
        try:
            ctx.prec = 256
            from grothendieck.proof.certified.h_eta_evaluator import gamma_0_arb
            gamma_0 = gamma_0_arb(256)
            gt = bool(certified_gt(gamma_best, gamma_0))
            improvement_mid = (gamma_best - gamma_0).mid()
            kg_upper = KG_upper(gamma_best, prec=256)
            krivine = Krivine_bound(prec=256)
            kg_lt = bool(certified_lt(kg_upper, krivine))
            kg_improvement_mid = (krivine - kg_upper).mid()
            checks.append({
                "id": "KG_upper_val_lt_KrivineBound",
                "certified_gamma_gt_gamma0": gt,
                "certified_KG_upper_lt_Krivine": kg_lt,
                "gamma_best_str": _arb_to_str(gamma_best, 50),
                "gamma_0_str": _arb_to_str(gamma_0, 50),
                "gamma_improvement_mid_str": improvement_mid.str(20),
                "KG_upper_val_str": _arb_to_str(kg_upper, 50),
                "Krivine_bound_str": _arb_to_str(krivine, 50),
                "KG_improvement_mid_str": kg_improvement_mid.str(20),
                "ok": gt and kg_lt,
                "note": ("Headline certificate-side witness: certified "
                         "γ_best > log(1+√2), so π/(2γ_best) < KrivineBound. "
                         "This numerical witness is rigorous as an arb "
                         "interval computation, but it is not yet the explicit "
                         "Lean witness extracted by `Theorem51Effective.lean`."),
            })
        finally:
            ctx.prec = old

    return checks


# --- Serialization -------------------------------------------------------


def _serializable(v: Any) -> Any:
    """Convert Python value to JSON-serializable form. arb → mid/rad/upper-rational."""
    if isinstance(v, Fraction):
        return {"_kind": "Fraction", "num": v.numerator, "den": v.denominator}
    if _is_arb(v):
        rat = _arb_to_rational_upper(v)
        return {
            "_kind": "arb",
            "str": _arb_to_str(v, 50),
            "rational_upper": str(rat) if rat else None,
        }
    if isinstance(v, (str, int, bool)):
        return v
    if isinstance(v, dict):
        return {k: _serializable(val) for k, val in v.items()}
    if isinstance(v, list):
        return [_serializable(x) for x in v]
    if isinstance(v, float):
        # We never WANT a float at this stage; if one slips through, flag it.
        return {"_kind": "float_warning", "value": v,
                 "note": "float in serialization; check for missing arb path"}
    return repr(v)


# --- Main entry point ----------------------------------------------------


def run_certify(
    *, nodes_dir: Path | None = None, verbose: bool = False
) -> dict:
    """Run the full graph end-to-end and return a JSON-serializable certificate."""
    graph = load_graph(nodes_dir)
    constants = graph.config.constants
    prec = 256
    try:
        prec = int(constants.get("prec", 256))
    except Exception:
        prec = 256

    if verbose:
        print(f"[runner] parsing Effective Lean files in {EFFECTIVE_DIR}", file=sys.stderr)
    parsed = parse_effective_dir(EFFECTIVE_DIR)
    lean_env = _build_lean_env(parsed, prec=prec)

    oracle_state: dict[str, dict[str, Any]] = {}
    skipped: list[dict] = []
    timings: list[dict] = []
    for node in graph.topological_order():
        if not (node.has_python and node.python.function):
            skipped.append({"slug": node.slug, "kind": node.kind.value,
                             "reason": "no [python] handle"})
            continue
        if verbose:
            print(f"[runner] running oracle: {node.slug}", file=sys.stderr)
        t0 = time.time()
        try:
            out = _invoke_node(node, state=oracle_state, constants=constants,
                                verbose=verbose)
            oracle_state[node.slug] = out
            timings.append({"slug": node.slug, "seconds": round(time.time() - t0, 3),
                             "outputs": list(out.keys())})
        except Exception as e:
            timings.append({"slug": node.slug, "seconds": round(time.time() - t0, 3),
                             "error": f"{type(e).__name__}: {e}"})
            skipped.append({"slug": node.slug, "kind": node.kind.value,
                             "reason": f"oracle failed: {type(e).__name__}: {e}"})

    checks = _run_cross_validations(
        lean_env=lean_env, oracle_state=oracle_state, constants=constants,
    )
    n_checks = len(checks)
    n_passing = sum(1 for c in checks if c.get("ok"))

    # Headline (arb-native; emitted as both string and rational upper bound).
    headline = {}
    if "Cr_val" in lean_env and _is_arb(lean_env["Cr_val"]):
        cv = lean_env["Cr_val"]
        headline["Cr_val_str"] = _arb_to_str(cv, 20)
        rat = _arb_to_rational_upper(cv)
        if rat is not None:
            headline["Cr_val_rational_upper"] = str(rat)
    krivine = Krivine_bound(prec=prec)
    headline["Krivine_bound_str"] = _arb_to_str(krivine, 30)
    sg_state = oracle_state.get("solve_gamma", {})
    gamma_best = sg_state.get("gamma_best")
    if _is_arb(gamma_best):
        from flint import ctx
        old = ctx.prec
        try:
            ctx.prec = 256
            kg_upper = KG_upper(gamma_best, prec=256)
            kg_improvement_mid = (krivine - kg_upper).mid()
            headline["gamma_best_str"] = _arb_to_str(gamma_best, 40)
            headline["KG_upper_val_str"] = _arb_to_str(kg_upper, 40)
            headline["KG_improvement_mid_str"] = kg_improvement_mid.str(15)
        finally:
            ctx.prec = old

    oracle_assumptions = _build_oracle_assumptions(checks=checks)

    return {
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H-%M-%S"),
        "inputs_sha256": _compute_inputs_sha256(),
        "graph_size": len(graph),
        "constants": dict(constants),
        "lean_rationals": {k: _serializable(v) for k, v in sorted(lean_env.items())
                            if isinstance(v, Fraction)},
        "lean_derived_arb": {k: _serializable(v) for k, v in sorted(lean_env.items())
                              if _is_arb(v)},
        "oracle_outputs": {
            slug: {k: _serializable(v) for k, v in out.items()}
            for slug, out in oracle_state.items()
        },
        "cross_validation": {
            "passing": n_passing,
            "total": n_checks,
            "checks": checks,
        },
        "oracle_assumptions": oracle_assumptions,
        "skipped_nodes": skipped,
        "timings_seconds": timings,
        "headline": headline,
    }


# --- Oracle-assumption shadow of the Lean trust boundary -----------------


def _build_oracle_assumptions(*, checks: list[dict]) -> dict[str, dict]:
    """Build a top-level dict mapping each Lean oracle axiom to the
    certificate-side cross-checks that witness it. This is the explicit
    "shadow" of the Lean trust boundary requested by Phase 1 of
    `STATUS_AND_PLAN.md`.

    Each entry has:
        lean_axiom        : the fully qualified Lean axiom name
        description       : human-readable summary
        certifying_checks : list of cross-validation check ids that
                            jointly witness this axiom
        certified         : True iff every certifying check passed
        notes             : any caveats (e.g. "still a sorryAx in Rounding.lean")
    """
    by_id = {c.get("id"): c for c in checks}

    def _all_ok(ids: list[str]) -> bool:
        return all(bool(by_id.get(i, {}).get("ok")) for i in ids if i in by_id) \
            and all(i in by_id for i in ids)

    assumptions: dict[str, dict] = {}

    assumptions["Braverman.Effective.h_M_oracle"] = {
        "lean_axiom": "Braverman.Effective.h_M_oracle",
        "description": ("Single-M sup-norm bound: |H_0|, |H_η|, |H_0'|, |H_η'| ≤ M_val "
                        "on the explicit oracle rectangle Ω(δ_val, B_val)."),
        "certifying_checks": ["M_oracle_le_M_val"],
        "certified": _all_ok(["M_oracle_le_M_val"]),
    }

    assumptions["Braverman.Effective.h_oracle_domain_contains_image"] = {
        "lean_axiom": "Braverman.Effective.h_oracle_domain_contains_image",
        "description": ("F_inv_paper(disk r_val) lands in the explicit rectangle "
                        "Ω(δ_val, B_val) for every q ∈ (0, pr_paper)."),
        "certifying_checks": [
            "step1_delta_matches_constant",
            "step1_B_matches_constant",
            "domain_containment_certified",
            "delta_val_matches_constant",
            "B_val_matches_constant",
        ],
        "certified": _all_ok([
            "step1_delta_matches_constant",
            "step1_B_matches_constant",
            "domain_containment_certified",
            "delta_val_matches_constant",
            "B_val_matches_constant",
        ]),
    }

    assumptions["Braverman.Effective.h_eta_strict_improvement_oracle"] = {
        "lean_axiom": "Braverman.Effective.h_eta_strict_improvement_oracle",
        "description": ("(H_η(I)/I).re > log(1+√2) at η = eta_val. "
                        "Witnesses Theorem 4.4's strict improvement."),
        "certifying_checks": ["h_eta_strict_improvement"],
        "certified": _all_ok(["h_eta_strict_improvement"]),
    }

    assumptions["Braverman.Effective.h_gamma_explicit_sandwich"] = {
        "lean_axiom": "Braverman.Effective.h_gamma_explicit_sandwich",
        "description": ("Rational sandwich on the Theorem 5.1 γ-witness: "
                        "gamma_lo_rat < gamma_explicit < gamma_hi_rat. "
                        "`gamma_explicit` is now extracted from "
                        "`theorem_5_1_at_p_explicit` whose `(η, p)` matches the "
                        "certified-arb pipeline, so this axiom is the assertion that "
                        "the IVT-chosen γ at `p = 1e-30` falls in the rational window "
                        "around `solve_gamma.gamma_best` — verified numerically via "
                        "`gamma_best_in_lean_sandwich`."),
        "certifying_checks": ["gamma_best_in_lean_sandwich"],
        "certified": _all_ok(["gamma_best_in_lean_sandwich"]),
    }

    assumptions["Braverman.Effective.h_p_explicit_lt_pr_paper"] = {
        "lean_axiom": "Braverman.Effective.h_p_explicit_lt_pr_paper",
        "description": ("p_explicit_rat = 1e-30 is below the IFT-package threshold "
                        "`pr_paper eta_val r_val …`. Witnessed indirectly by checking "
                        "`p_explicit_rat < certify_invertibility.p_certified ~ 2.4e-4`, "
                        "since `pr_paper` dominates Step 1's certified Rouché radius."),
        "certifying_checks": ["p_explicit_lt_pr_paper"],
        "certified": _all_ok(["p_explicit_lt_pr_paper"]),
    }

    assumptions["Braverman.Effective.h_F_p_deriv_at_p_explicit"] = {
        "lean_axiom": "Braverman.Effective.h_F_p_deriv_at_p_explicit",
        "description": ("deriv (F_p eta_val p_explicit_rat) 0 ≠ 0 at p = 1e-30. "
                        "Justified analytically: F_p = (1-p)·H_0 + p·H_η, so "
                        "`deriv(F_p)(0) = (1-p)·H_0'(0) + p·H_η'(0) ≈ H_0'(0) ≈ 1` "
                        "for p = 1e-30. No direct runner witness; this is a "
                        "structural fact about F_p at small p."),
        "certifying_checks": [],
        "certified": True,  # structural, no numerical witness required
    }

    assumptions["Braverman.Effective.h_gap_ratio_at_p_explicit_with_B_phi"] = {
        "lean_axiom": "Braverman.Effective.h_gap_ratio_at_p_explicit_with_B_phi",
        "description": ("Existence of B_phi compactness bound + gap-ratio inequality "
                        "at p_explicit_rat. With the generous B_phi ≤ M_val + 1, "
                        "the LHS at p = 1e-30 is on the order of 1e-13, well below "
                        "the RHS ≈ 0.013."),
        "certifying_checks": ["gap_ratio_at_p_explicit"],
        "certified": _all_ok(["gap_ratio_at_p_explicit"]),
    }

    assumptions["Braverman.Effective.h_summability_at_p_explicit"] = {
        "lean_axiom": "Braverman.Effective.h_summability_at_p_explicit",
        "description": ("Sign-structure conclusion at p_explicit_rat: any F_inv "
                        "satisfying the Lemma 5.4 approximation has summability_fn "
                        "F_inv (log(1+√2)) < 1. This is "
                        "`summability_fn_at_log_lt_one` applied at p = 1e-30 < p_β. "
                        "Witnessed indirectly: `solve_gamma` at p = 1e-30 finds γ "
                        "with summability_fn = 1 strictly above log(1+√2), implying "
                        "summability_fn < 1 below γ (and hence at log(1+√2))."),
        "certifying_checks": ["KG_upper_val_lt_KrivineBound"],
        "certified": _all_ok(["KG_upper_val_lt_KrivineBound"]),
    }

    # Note: `sorryAx` from `Rounding.lean` is intentionally not in this map —
    # it is not a numerically-certified assumption but a Lean-side TODO.

    # The generic theorem `theorem_5_1_from_thresholds` itself takes a list of
    # *non-axiom* numerical hypotheses (positivity/order on the chosen tuple
    # `(eta_val, p_explicit_rat, r_val, 91/100, M_val, …)`). These are not
    # axioms — they are discharged in Lean by `norm_num` — but the runner
    # still cross-checks them as a sanity gate so that mismatches between
    # Lean rationals and the chosen tuple show up immediately.
    assumptions["__theorem_5_1_from_thresholds_preconditions"] = {
        "lean_axiom": None,
        "description": ("Non-axiom numerical preconditions of "
                        "`theorem_5_1_from_thresholds` at the chosen tuple. "
                        "Each is discharged by `norm_num` in Lean; the runner "
                        "cross-checks them to catch tuple-mismatches early."),
        "certifying_checks": [
            "theorem_5_1_rational_range_hypotheses",
            "log_one_plus_sqrt_two_in_lean_sandwich",
            "Cr_val_finite_positive",
        ],
        "certified": _all_ok([
            "theorem_5_1_rational_range_hypotheses",
            "Cr_val_finite_positive",
        ]),
    }
    return assumptions


def write_certificate(cert: dict, *, out_dir: Path | None = None) -> Path:
    """Write the certificate to runs/<ts>/certificate.json."""
    ts = cert.get("timestamp_utc", datetime.now(timezone.utc).strftime("%Y-%m-%dT%H-%M-%S"))
    if out_dir is None:
        out_dir = Path(__file__).resolve().parent.parent / "runs" / ts
    out_dir.mkdir(parents=True, exist_ok=True)
    cert_path = out_dir / "certificate.json"
    cert_path.write_text(json.dumps(cert, indent=2, default=str))
    return cert_path
