The Python cut off mid-function. Rather than re-emit the whole 1900-line `rigorous_scalar.py` (which is what blew the budget), I'm shipping the new wrapper as a **short standalone module** that imports the existing rigorous arb helpers. `Candidates/V65.lean` as emitted above is complete and unchanged; only the `oracle_fn` path in `lemma.toml` moves.

```python path=ProofRefinement/Korenblum/Numerical_Library/two_window_v65.py
"""
V65 joint two-window tau-partition mass oracle at ``c = 35648/100000``.

This module is a thin driver on top of the rigorous ``flint.arb``
interval-quadrature machinery already shipped in ``rigorous_scalar``
(``_two_window_mass_window_lower_arb`` and friends). It exists as its own
module so the c-push does not require rewriting that file.

Certified statement
-------------------

    1  <=  int_{rho_start_1 .. rho_stop_1} 2 rho / (H_2(c, rho) * Lambda(c, rho)) drho
         + int_{rho_stop_1  .. rho_stop_2} 2 rho / (H_1(c, rho) * Lambda(c, rho)) drho

with

    c           = 35648/100000
    rho_start_1 = c * sqrt(9/8)        (irrational; c^2/rho_start_1^2 = 8/9 = tau(2))
    rho_stop_1  = c * sqrt(4/3)        (irrational; c^2/rho_stop_1^2  = 3/4 = tau(1))
                = rho_start_2          (adjacency)
    rho_stop_2  = 999999/1000000
    H_j(c, rho) = (j/(j+1)) c^(2j+2) / rho^(2j)
    Lambda      = the Wang truncated paper-product ``paperLambda K c rho``.

These are the algebraically forced canonical tau-breakpoint endpoints for a
two-window tau-partition at ``(j_1, j_2) = (2, 1)`` under the adjacency
constraint ``rho_stop_1 = rho_start_2``.

Rigour
------

The joint mass is bounded **from below** by left-Riemann arb lower sums with a
monotonicity-aware Lambda-upper dispatch (K is single-peaked at rho = sqrt(c)).
Truncating the Wang product at ``n_trunc`` factors is conservative in the
correct direction: every factor is <= 1, so K_trunc >= K_true, hence
Lambda_trunc >= Lambda_true, hence the integrand ``2 rho / (H_j * Lambda)`` is
under-estimated and the certified total is a genuine lower bound on the true
joint mass. The subdivision count is doubled from 256 up to 16384 until the
certified lower bound clears the strict-margin floor ``1 + 10^(-30)``; on
failure the driver raises ``RuntimeError`` so the Evaluator records an
oracle-check failure rather than silently accepting an unverified Lean axiom.

Numerical basis
---------------

Sprint 078's Phase 0 sweep (``Scratch/sprint_078_two_window_tau_mass_sweep.txt``,
mp.quad, dps=30, n_trunc=200) records joint two-window mass margin ``>= 1e-3``
at ``c in {0.35646, 0.35647, 0.35648}`` on exactly these canonical endpoints
``rho_j(c) = c / sqrt(tau(j))``, with the mass crossing below ``1`` only near
``c ~ 0.35654``. ``c = 0.35648`` is the largest directly-swept value with
recorded headroom.

Falsifiability
--------------

A wrapper returning True at ``c >= 0.35655`` with this same sqrt-pin shape
would not be verifying anything: the joint mass is below 1 there.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx, fmpq

from .rigorous_scalar import (
    _arb_exact,
    _pow_cached,
    _two_window_mass_window_lower_arb,
)


# Pinned parameters of the V65 oracle.
C_NUM = 35648
C_DEN = 100000
RHO_STOP_2 = Fraction(999999, 1000000)
J1 = 2
J2 = 1
N_TRUNC = 200
DPS = 80
SUBDIVISION_START = 256
SUBDIVISION_CAP = 16384

_AXIOM = "h_two_window_mass_certified_at_35648_sqrt"


def certify_two_window_mass_at_35648_sqrt() -> Fraction:
    """
    Zero-argument Evaluator-facing shim for the registered oracle
    ``h_two_window_mass_certified_at_35648_sqrt``.

    Returns ``Fraction(1, 1)`` iff the rigorous arb lower bound on the joint
    two-window mass at the pinned sqrt endpoints exceeds ``1 + 10^(-30)``.
    Raises ``RuntimeError`` otherwise.
    """
    c = Fraction(C_NUM, C_DEN)
    rt2 = RHO_STOP_2

    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(f"{_AXIOM}: pinned c is not in (0, 1).")
    if not (rt2 < Fraction(1)):
        raise RuntimeError(f"{_AXIOM}: pinned rho_stop_2 is not below 1.")

    with ctx.workdps(int(DPS)):
        c_arb = _arb_exact(c)
        rt2_arb = _arb_exact(rt2)

        # Sqrt-pinned endpoints. `arb.sqrt()` returns a rigorous enclosure of
        # the irrational square root.
        rho_start_1_arb = c_arb * arb(fmpq(9, 8)).sqrt()
        rho_meet_arb = c_arb * arb(fmpq(4, 3)).sqrt()
        sqrt_c_arb = c_arb.sqrt()

        # Structural ordering checks (rigorous arb comparisons). Each gap is
        # well above 1e-3, so no endpoint enclosures overlap.
        if not ((c_arb < rho_start_1_arb) is True):
            raise RuntimeError(f"{_AXIOM}: ordering c < rho_start_1 fails.")
        if not ((rho_start_1_arb <= rho_meet_arb) is True):
            raise RuntimeError(
                f"{_AXIOM}: ordering rho_start_1 <= rho_stop_1 fails."
            )
        if not ((rho_meet_arb <= rt2_arb) is True):
            raise RuntimeError(
                f"{_AXIOM}: ordering rho_stop_1 <= rho_stop_2 fails."
            )

        # Pre-compute c-powers once: the paper factor at index n reaches
        # c^(2n+3), and the H_j term reaches c^(2j+2); n_trunc dominates.
        c_pows = _pow_cached(c_arb, 2 * N_TRUNC + 3)

        floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

        n_subdivisions = SUBDIVISION_START
        last_total = None
        while True:
            m1_lower = _two_window_mass_window_lower_arb(
                c_arb, c_pows, J1, rho_start_1_arb, rho_meet_arb,
                sqrt_c_arb, N_TRUNC, n_subdivisions,
            )
            m2_lower = _two_window_mass_window_lower_arb(
                c_arb, c_pows, J2, rho_meet_arb, rt2_arb,
                sqrt_c_arb, N_TRUNC, n_subdivisions,
            )
            total_lower = m1_lower + m2_lower
            last_total = total_lower
            if (total_lower > floor_arb) is True:
                return Fraction(1, 1)
            if n_subdivisions >= SUBDIVISION_CAP:
                break
            n_subdivisions *= 2

        raise RuntimeError(
            f"{_AXIOM}: rigorous arb lower bound on joint mass = "
            f"{last_total} (margin = {last_total - arb(1)}) failed to clear "
            f"the strict-margin floor 1 + 10^(-30) at n_subdivisions = "
            f"{n_subdivisions} (cap = {SUBDIVISION_CAP}); refusing to certify "
            "the Lean axiom to keep the trust surface honest."
        )
```

```toml path=ProofRefinement/Korenblum/lemma.toml
name = "Korenblum Constant"
slug = "korenblum"
paper_ref = "Wang (2025), Section 2 / equation (15)"

sink_theorem = "korenblum_constant_search"
constant_def = "c_value"
score = "c_value"
score_direction = "maximize"

[search_constants]

[import_policy]
# Candidate-side import surface enforced by `Evaluator.py` against every
# `Candidates/V<N>.lean`. Per-candidate derived-theorem modules under
# `Candidates/V<N>/` are registered here as candidates start importing them.
allowed_exact = [
  "ProofRefinement.Korenblum.Candidates.V53.ThetaStep",
  "ProofRefinement.Korenblum.Candidates.V54.LiftIdentity",
  "ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge",
  "ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated",
  "ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated",
  "ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity",
  "ProofRefinement.Korenblum.Candidates.V63.Integrability",
  "ProofRefinement.Korenblum.Candidates.V63.Summability",
  "ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge",
  "ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints",
]
allowed_prefixes = [
  "ProofRefinement.Korenblum.Proof",
  "Mathlib",
]

[workspace_import_policy]
allowed_exact = [
  "KorenblumPaper.PaperAxioms",
  "KorenblumPaper.PaperEq15",
  "KorenblumPaper.OneModePaperBridge",
]
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[seed_axioms]
allowed = [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
  "Lean.trustCompiler",

  # V0 seed: Wang's equation (15) at c = 0.3554.
  "hEq15_seed_3554",

  # eq15 oracle cascade (sprints 053-059).
  "hEq15_oracle_certified_3554",
  "hEq15_oracle_certified_3560",
  "hEq15_oracle_certified_3562",
  "hEq15_oracle_certified_hp_3564",
  "hEq15_oracle_certified_hp_35645",

  # Sprint 079: joint two-window tau-partition mass at c = 35646/100000,
  # exact-rational endpoints (378083, 411605, 999999)/1000000, (j1, j2) = (2, 1).
  "h_two_window_mass_certified_at_35646",

  # Sprint 083: sqrt-endpoint sibling at c = 35646/100000 with
  # rho_start_1 = c*sqrt(9/8), rho_stop_1 = rho_start_2 = c*sqrt(4/3),
  # rho_stop_2 = 999999/1000000.
  "h_two_window_mass_certified_at_35646_sqrt",

  # Sprint 083 free candidate-side axioms: Wang's Hypothesis 1 of Section 2
  # (H^2 boundary-norm finiteness) and the paper-implicit
  # `2*rho*circleGap`-density integrability on (c_value, 1).
  "hH2_v64",
  "hCircleGapInt_v64",

  # V65: sqrt-endpoint joint two-window mass oracle re-pinned at
  # c = 35648/100000 (same endpoint geometry as the 35646 sqrt sibling).
  # Sprint 078's Phase 0 sweep records joint-mass margin >= 1e-3 at
  # c in {0.35646, 0.35647, 0.35648} on exactly these canonical endpoints,
  # with the mass crossing below 1 only near c ~ 0.35654; c = 0.35648 is the
  # largest directly-swept value with recorded headroom.
  "h_two_window_mass_certified_at_35648_sqrt",

  # V65 siblings of the two free candidate-side axioms, re-pinned at
  # c_value = 35648/100000.
  "hH2_v65",
  "hCircleGapInt_v65",
]

# Oracle rows. `Evaluator.py:load_workspace_config` reads
# (`axiom`, `bound_field`, `oracle_fn`); it invokes `oracle_fn` with no
# arguments and compares the returned Fraction against the candidate-side
# `def <bound_field> : R := ...` via `oracle_bound <= declared`.

# Sprint 053: eq15 at the seed, (3554, 10000, dps=50, n_trunc=200).
# Falsifiability: the wrapper rejects (3565, 10000) at the same envelope.
[[oracles]]
axiom = "hEq15_oracle_certified_3554"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_seed"

# Sprint 055: (1780, 5000, dps=50, n_trunc=200).
[[oracles]]
axiom = "hEq15_oracle_certified_3560"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3560"

# Sprint 056: (1781, 5000, dps=50, n_trunc=200).
[[oracles]]
axiom = "hEq15_oracle_certified_3562"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3562"

# Sprint 057: (1782, 5000, dps=100, n_trunc=500) — first non-default envelope.
[[oracles]]
axiom = "hEq15_oracle_certified_hp_3564"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_3564"

# Sprint 059: (35645, 100000, dps=100, n_trunc=500).
[[oracles]]
axiom = "hEq15_oracle_certified_hp_35645"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_35645"

# Sprint 079: first non-eq15 oracle. Joint two-window tau-partition mass at
# exact-rational endpoints, (dps, n_trunc) = (30, 200):
#   total := int_{rs1..rt1} 2rho/(H_2*Lam) + int_{rt1..rt2} 2rho/(H_1*Lam)
# returns Fraction(1,1) iff total >= 1 + 10^(-min(dps,30)).
# Falsifiability: the joint mass crosses below 1 near c ~ 0.35654.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646"

# Sprint 083: sqrt-endpoint sibling at c = 35646/100000, discharged by
# rigorous `flint.arb` interval quadrature (left-Riemann lower sums with a
# monotonicity-aware Lambda-upper dispatch), refining the subdivision count
# until the certified lower bound clears 1 + 10^(-30).
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646_sqrt"

# V65: sqrt-endpoint joint two-window mass at c = 35648/100000.
#
# Same rigorous arb machinery as the 35646 sqrt sibling (it imports the
# `_two_window_mass_window_lower_arb` helper directly from `rigorous_scalar`),
# re-pinned at
#   c           = 35648/100000
#   rho_start_1 = c * sqrt(9/8)     (c^2/rho_start_1^2 = 8/9 = tau(2))
#   rho_stop_1  = c * sqrt(4/3)     (c^2/rho_stop_1^2  = 3/4 = tau(1))
#              = rho_start_2        (adjacency)
#   rho_stop_2  = 999999/1000000
#   (j_1, j_2)  = (2, 1)
#   (dps, n_trunc) = (80, 200)
#   subdivisions: 256 -> 16384, strict-margin floor 1 + 10^(-30).
#
# Truncating the Wang product at n_trunc factors is conservative in the correct
# direction: every factor is <= 1, so K_trunc >= K_true, hence Lambda_trunc >=
# Lambda_true, hence the integrand 2rho/(H_j*Lambda) is under-estimated and the
# certified total is a genuine lower bound on the true joint mass.
#
# Falsifiability is preserved: the joint mass crosses below 1 near
# c ~ 0.35654, so a wrapper returning True at c >= 0.35655 with the same
# sqrt-pin shape would not be verifying anything.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35648_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "two_window_v65.certify_two_window_mass_at_35648_sqrt"
```

**Files this attempt ships**, three total:

1. `ProofRefinement/Korenblum/Candidates/V65.lean` — emitted complete above; unchanged. `c_value = 35648/100000 = 0.35648 > 17823/50000`. Sink discharges via `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, composing the three existing V63 derived-theorem files (integrability, summability, disk/inner-series bridge) with inlined `Real.sqrt`-pinned τ-window endpoint lemmas, two free candidate-side axioms (`hH2_v65`, `hCircleGapInt_v65`), and one oracle axiom.
2. `ProofRefinement/Korenblum/Numerical_Library/two_window_v65.py` — new, short; reuses `rigorous_scalar`'s rigorous arb helpers rather than duplicating them.
3. `ProofRefinement/Korenblum/lemma.toml` — full file, with the three new `[seed_axioms].allowed` entries and the new `[[oracles]]` row pointing at the new module.

`rigorous_scalar.py` is **not** modified, so the existing oracle rows and their wrappers are untouched.

Two honest caveats about where this could fail: the new oracle row uses a submodule path (`two_window_v65.…`) that is documented as supported but is the first non-`rigorous_scalar` module registered here — if the loader only resolves `rigorous_scalar`, the oracle check fails. And the certified margin at `c = 0.35648` is the recorded sweep's ~1e-3, roughly an order of magnitude above the arb left-Riemann quadrature loss at the refined subdivision counts, so it should clear the `1 + 10^(-30)` floor, but that headroom is thinner than V64's.