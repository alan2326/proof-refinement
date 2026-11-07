"""Per-candidate Cr-formula audit (PATCH_NOTES R5 / Evaluator G7.b).

Wraps the eight truncation-free oracles in a `TruncFreeBundle` and
applies each candidate's exact `Cr_phi_*` formula from
`Proof/Lib/Lemma54_Paper.lean` to produce the patched `Cr_val`.

Quick start:

    from Numerical_Library.truncfree import round3, audit_candidate

    b = round3()
    a = audit_candidate("V11", bundle=b)
    print(a.Cr_patched_float, a.Cr_decl_float, a.formula)

    # Audit all V9..V26 against round-3 chunks
    from Numerical_Library.truncfree import audit_all_candidates
    rows = audit_all_candidates(bundle=b)
    for r in rows:
        print(f"{r.candidate}: {r.Cr_patched_float:.3e}  ({r.formula})")

The candidate → formula mapping is `CANDIDATE_FORMULAS` (verbatim
from each `Candidates/V<N>.lean` file). The Lean Cr_phi_* formula
defs are in `PAPER_FORMULAS` (verbatim from
`Lemma54_Paper.lean:464-603`).
"""

from __future__ import annotations

from dataclasses import dataclass, asdict
from typing import Optional

from flint import arb, ctx as flint_ctx

from .oracle import TruncFreeBundle, round3 as _round3_preset


# --- Paper constants (from Lemma54_Paper.lean / PATCH_NOTES) ----------------
PAPER_CONSTANTS = {
    "r": "23/25",          # SearchConfig.r
    "R": "23/20",          # R_val_paper r ≤ 23/20
    "p_max": "1",          # joint sup p ∈ [0, p_max]
}


def _paper_invFp() -> arb:
    """invFp_paper = 2R/(1-r) = 28.75 (exact)."""
    R = arb(PAPER_CONSTANTS["R"])
    r = arb(PAPER_CONSTANTS["r"])
    return arb(2) * R / (arb(1) - r)


def _paper_coef_term2() -> arb:
    """coef_term2_paper = 4R/(1-r)² = 718.75 (exact)."""
    R = arb(PAPER_CONSTANTS["R"])
    r = arb(PAPER_CONSTANTS["r"])
    one_minus_r = arb(1) - r
    return arb(4) * R / (one_minus_r * one_minus_r)


# --- Candidate → formula mapping (verified vs Candidates/V*.lean) -----------
# Each entry: candidate name → (formula identifier, declared Cr_val literal).
CANDIDATE_FORMULAS = {
    "V9":  ("Cr_phi",                    "5"),
    "V10": ("Cr_phi_invD",               "2"),
    "V11": ("Cr_phi_uzz",                "1"),
    "V12": ("Cr_phi_uzz_direct",         "1/32"),
    "V13": ("Cr_phi_uzz_direct",         "1/300"),
    "V14": ("Cr_phi_uzz_direct_joint",   "1/1300"),
    "V15": ("Cr_phi_uzz_direct_joint2",  "1/2600"),
    "V16": ("Cr_phi_uzz_direct_joint2",  "1/3500"),
    "V17": ("Cr_phi_uzz_direct_joint2",  "1/3500"),
    "V18": ("Cr_phi_uzz_direct_joint2",  "1/11700"),
    "V19": ("Cr_phi_uzz_direct_joint2",  "1/31500"),
    "V20": ("Cr_phi_uzz_direct_joint2",  "1/66500"),
    "V21": ("Cr_phi_uzz_direct_joint2",  "1/71900"),
    "V22": ("Cr_phi_uzz_direct_joint2",  "1/124000"),
    "V23": ("Cr_phi_uzz_direct_joint2",  "1/169000"),
    "V24": ("Cr_phi_uzz_direct_joint2",  "1/169000"),
    "V25": ("Cr_phi_uzz_merged",         "1/240000"),
    "V26": ("Cr_phi_uzz_merged",         "1/268000"),
}


# --- Cr_phi_* formula evaluators (verbatim from Lemma54_Paper.lean) --------
def _Cr_phi(M_phi, M_phi_prime) -> arb:
    """Cr_phi(r, M_phi, M_phi_prime, R) = M_phi·M_phi_prime·invFp²
    + (4R/(1-r)²)·M_phi²  with invFp = 2R/(1-r). r=23/25, R=23/20."""
    invFp = _paper_invFp()
    return (M_phi * M_phi_prime * invFp * invFp
            + _paper_coef_term2() * M_phi * M_phi)


def _Cr_phi_invD(M_phi, M_phi_prime, inv_F_p_z) -> arb:
    """Same Cr_phi shape but with abstract inv_F_p_z replacing invFp."""
    return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
            + _paper_coef_term2() * M_phi * M_phi)


def _Cr_phi_uzz(M_phi, M_phi_prime, inv_F_p_z, M_pp) -> arb:
    """M_phi·M_phi_prime·inv² + (1/2)·M_pp·inv³·M_phi²."""
    return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
            + (arb(1) / arb(2)) * M_pp * inv_F_p_z**3 * M_phi * M_phi)


def _Cr_phi_uzz_direct(M_phi, M_phi_prime, inv_F_p_z, u_zz_bound) -> arb:
    """M_phi·M_phi_prime·inv² + (1/2)·u_zz_bound·M_phi²."""
    return (M_phi * M_phi_prime * inv_F_p_z * inv_F_p_z
            + (arb(1) / arb(2)) * u_zz_bound * M_phi * M_phi)


def _Cr_phi_uzz_direct_joint(M_phi, joint, u_zz_bound) -> arb:
    """joint + (1/2)·u_zz_bound·M_phi²."""
    return joint + (arb(1) / arb(2)) * u_zz_bound * M_phi * M_phi


def _Cr_phi_uzz_direct_joint2(joint, uzz_phi_sq) -> arb:
    """joint + (1/2)·uzz_phi_sq."""
    return joint + (arb(1) / arb(2)) * uzz_phi_sq


def _Cr_phi_uzz_merged(merged) -> arb:
    """(1/2)·merged_uderiv."""
    return (arb(1) / arb(2)) * merged


def _eval_formula(formula: str, b: TruncFreeBundle) -> arb:
    if formula == "Cr_phi":
        return _Cr_phi(b.M_phi, b.M_phi_prime)
    if formula == "Cr_phi_invD":
        return _Cr_phi_invD(b.M_phi, b.M_phi_prime, b.inv_F_p_z)
    if formula == "Cr_phi_uzz":
        return _Cr_phi_uzz(b.M_phi, b.M_phi_prime, b.inv_F_p_z, b.M_pp)
    if formula == "Cr_phi_uzz_direct":
        return _Cr_phi_uzz_direct(b.M_phi, b.M_phi_prime,
                                     b.inv_F_p_z, b.u_zz_bound)
    if formula == "Cr_phi_uzz_direct_joint":
        return _Cr_phi_uzz_direct_joint(
            b.M_phi, b.joint_phi_phip_invD2, b.u_zz_bound,
        )
    if formula == "Cr_phi_uzz_direct_joint2":
        return _Cr_phi_uzz_direct_joint2(
            b.joint_phi_phip_invD2, b.uzz_phi_sq,
        )
    if formula == "Cr_phi_uzz_merged":
        return _Cr_phi_uzz_merged(b.merged_uderiv)
    raise ValueError(f"unknown formula {formula!r}")


# --- Public API ------------------------------------------------------------
@dataclass
class CandidateAudit:
    candidate: str
    formula: str
    Cr_decl: str
    Cr_decl_float: float
    Cr_patched_str: str
    Cr_patched_float: float
    ratio_patched_over_decl: float

    def to_dict(self) -> dict:
        return asdict(self)

    def __repr__(self) -> str:
        return (
            f"CandidateAudit({self.candidate}, {self.formula}, "
            f"Cr_decl={self.Cr_decl}, "
            f"Cr_patched={self.Cr_patched_float:.3e}, "
            f"ratio={self.ratio_patched_over_decl:.2e})"
        )


def audit_candidate(
    candidate: str,
    *,
    bundle: Optional[TruncFreeBundle] = None,
    formula: Optional[str] = None,
    Cr_decl: Optional[str] = None,
) -> CandidateAudit:
    """Apply the candidate's formula to the truncation-free bundle.

    `candidate` is a name like "V11"; if it is not in
    `CANDIDATE_FORMULAS`, you must pass `formula=` and `Cr_decl=`
    explicitly (e.g. for a custom V27 you're drafting).
    """
    flint_ctx.prec = 200
    if bundle is None:
        bundle = _round3_preset()

    if candidate in CANDIDATE_FORMULAS:
        f0, c0 = CANDIDATE_FORMULAS[candidate]
        formula = formula or f0
        Cr_decl = Cr_decl or c0
    else:
        if formula is None or Cr_decl is None:
            raise ValueError(
                f"unknown candidate {candidate!r}; "
                f"pass formula= and Cr_decl= explicitly"
            )

    naive = _eval_formula(formula, bundle)
    cr_decl_arb = arb(Cr_decl)
    naive_f = float(naive.upper())
    decl_f = float(cr_decl_arb.upper())
    return CandidateAudit(
        candidate=candidate,
        formula=formula,
        Cr_decl=Cr_decl,
        Cr_decl_float=decl_f,
        Cr_patched_str=naive.str(20, more=True),
        Cr_patched_float=naive_f,
        ratio_patched_over_decl=naive_f / decl_f,
    )


def audit_all_candidates(
    *,
    bundle: Optional[TruncFreeBundle] = None,
) -> list[CandidateAudit]:
    """Audit every V9..V26 against the bundle (default: round-3 preset)."""
    if bundle is None:
        bundle = _round3_preset()
    return [audit_candidate(name, bundle=bundle)
            for name in CANDIDATE_FORMULAS]
