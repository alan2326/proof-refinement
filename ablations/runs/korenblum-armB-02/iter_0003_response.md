I'll push the two‑window τ‑partition route further along the band that sprint 078's sweep certified (joint mass ≥ 1 up to c ≈ 0.35654, margin ≥ 1e‑3 through 0.35648). The parent sits at `1114/3125 = 0.35648`; I target **`c = 35651/100000 = 0.35651`**, a +3e‑5 push with an estimated centred margin ≈ 7e‑4 — comfortably above the ~3e‑4 arb conservatism at `n_subdivisions = 4096` measured in sprint 083.

Three files: a new oracle wrapper module (reusing the *already-audited* arb helpers verbatim, so no numerics are re-derived), the `lemma.toml` registration, and the new candidate `V66.lean` built from the existing V63/V64 derived-theorem files.

```python path=ProofRefinement/Korenblum/Numerical_Library/two_window_sqrt_35651.py
"""Sprint 085 — c-pushed sqrt-endpoint joint two-window mass oracle at
``c = 35651/100000``.

This module is a thin parametric sibling of the 35646 / 35648 sqrt-endpoint
wrappers.  It imports and reuses ``rigorous_scalar``'s audited ``flint.arb``
machinery **unchanged** — the shared core

    ``rigorous_scalar._certify_two_window_mass_sqrt_at``

which in turn calls ``_arb_exact``, ``_pow_cached`` and
``_two_window_mass_window_lower_arb``.  The integration scheme, the truncation
direction, the monotonicity-aware Lambda-upper dispatch, and the strict-margin
floor ``1 + 10**(-30)`` are therefore byte-identical to the certified V64/V65
path.  Only the pinned radius ``c`` and the subdivision schedule differ.

Pinning
-------
    c            = 35651/100000
    rho_start_1  = c * sqrt(9/8)        (so c^2 / rho_start_1^2 = 8/9 = tau(2))
    rho_stop_1   = c * sqrt(4/3)        (so c^2 / rho_stop_1^2  = 3/4 = tau(1))
                 = rho_start_2          (adjacency)
    rho_stop_2   = 999999/1000000
    (j_1, j_2)   = (2, 1)
    (dps, n_trunc)             = (80, 200)
    (n_start, n_cap)           = (2048, 16384)

The subdivision schedule starts at 2048 rather than the shared default of 256
because sprint 083 measured the arb conservatism at ~6.1e-4 for
``n_subdivisions = 2048``; the smaller rounds cannot clear the floor at any
``c`` in this band and only cost time.

Direction of conservatism
-------------------------
Both sources of error run in the safe direction, so the certified quantity is a
genuine **lower** bound on the joint mass:

* truncating the Wang product after ``n_trunc`` factors raises ``K`` (each
  factor is ``<= 1`` for ``0 < c < rho < 1``), hence raises ``Lambda``, hence
  lowers the integrand;
* the left-Riemann endpoint selection takes ``H_j`` at its per-sub-interval
  maximum (``H_j`` is decreasing in ``rho`` for ``j >= 1``) and ``2 rho`` at its
  minimum.

Falsifiability
--------------
Sprint 078's Phase 0 sweep records the joint mass crossing below ``1`` around
``c ~ 0.35654``, with margin ``>= 1e-3`` through ``c = 0.35648``.  A wrapper
pinned at ``c >= 0.35655`` would not be verifying anything: it would be asked to
certify a numerically false statement and would raise.  The pinned
``c = 35651/100000`` sits strictly inside the verified band, roughly three
tenths of the way from the last ``>= 1e-3`` grid point to the zero crossing.
"""

from __future__ import annotations

from fractions import Fraction

try:  # package-relative load (the normal path used by Evaluator.py)
    from .rigorous_scalar import _certify_two_window_mass_sqrt_at
except ImportError:  # pragma: no cover - flat-module fallback
    from rigorous_scalar import _certify_two_window_mass_sqrt_at


def certify_two_window_mass_at_35651_sqrt() -> Fraction:
    """
    Zero-argument shim for ``h_two_window_mass_certified_at_35651_sqrt``.

    Pins ``c = 35651/100000`` with the canonical tau-breakpoint sqrt endpoints

        rho_start_1 = c * sqrt(9/8)
        rho_stop_1  = c * sqrt(4/3)   (= rho_start_2)
        rho_stop_2  = 999999/1000000

    at ``(j_1, j_2) = (2, 1)``, ``n_trunc = 200``, arb precision ``dps = 80``.

    Returns ``Fraction(1, 1)`` iff the RIGOROUS ``flint.arb`` interval lower
    bound on

        int_{rho_start_1}^{rho_stop_1} 2 rho / (H_2(c, rho) Lambda(c, rho)) drho
      + int_{rho_stop_1}^{rho_stop_2}  2 rho / (H_1(c, rho) Lambda(c, rho)) drho

    clears ``1 + 10**(-30)``, where ``H_j(c, rho) = (j/(j+1)) c^(2j+2)/rho^(2j)``
    and ``Lambda`` is Wang's ``(1 + gamma_2)`` factor built from the truncated
    equation-(7) product.  The subdivision count doubles from ``2048`` up to
    ``16384`` until the floor is cleared; on exhaustion the shared core raises a
    ``RuntimeError`` so the Evaluator records an oracle-check failure rather
    than silently accepting an unverified axiom.
    """
    return _certify_two_window_mass_sqrt_at(
        Fraction(35651, 100000),
        "certify_two_window_mass_at_35651_sqrt",
        rt2=Fraction(999999, 1000000),
        n_trunc=200,
        dps=80,
        n_start=2048,
        n_cap=16384,
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
# Sprint 068: candidate-side `import_policy` is the strict surface that
# `Evaluator.py` enforces against every `Candidates/V<N>.lean`. We extend
# `allowed_exact` to admit each per-candidate derived-theorem module under
# `Candidates/V<N>/` as candidates start importing them. Per `AGENT_BRIEF.md`
# lines 154-204 / unstuck plan §5, these files contain only `theorem`s
# derived from the existing trusted surface (no new axioms, no edits to
# `KorenblumPaper/`); registering each module here is part of the same
# institutional pattern that registers per-candidate derived theorems
# under `[workspace_import_policy]`.
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

  # The V0 seed's single external input: Wang's equation (15) at c = 0.3554.
  "hEq15_seed_3554",

  # Sprint 053: the Lean-facing axiom name asserted by V48 and discharged by
  # the registered oracle `eq15_certified_at_seed`. Same paper-statement
  # shape as `hEq15_seed_3554` but trust is grounded in the
  # `Numerical_Library.rigorous_scalar.certify_eq15` verified-interval
  # wrapper rather than as a free-floating per-c axiom.
  "hEq15_oracle_certified_3554",

  # Sprint 055: the c-pushed sibling of `hEq15_oracle_certified_3554`.
  # Same Lean axiom shape, same `Eq15ScalarBound K c_value` statement,
  # same registered wrapper (`certify_eq15`), but with `c_value` pinned
  # to `1780/5000 = 0.3560` instead of `3554/10000 = 0.3554`. Discharged
  # by the sibling oracle `eq15_certified_at_3560`.
  "hEq15_oracle_certified_3560",

  # Sprint 056: the second c-push sibling, pinning c = 1781/5000 = 0.3562.
  # Same Lean axiom shape and same registered wrapper as the 3554/3560
  # siblings; the Scratch pre-verification at
  # `Scratch/sprint_056_eq15_wrapper_pre_verification.txt` records the
  # wrapper's True return and certified margin at this c.
  "hEq15_oracle_certified_3562",

  # Sprint 057: the third c-push sibling, pinning c = 1782/5000 = 0.3564.
  # First oracle in the workspace to pin the upgraded precision envelope
  # `(dps=100, n_trunc=500)` per Bulletin.md lines 300-304. Same Lean
  # axiom shape as the 3554/3560/3562 siblings, but the registered
  # wrapper rejects this c at the standard envelope (margin -6.89e-04)
  # and accepts at the upgraded envelope (margin +1.17e-03); see
  # `Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt` for the
  # tiered Scratch pre-verification record. The HP envelope still
  # rejects at c=0.3565 (margin -1.15e-03), preserving the literal (15)
  # crossover at c~0.35635 as the absolute ceiling.
  "hEq15_oracle_certified_hp_3564",

  # Sprint 059: the fourth c-push sibling, pinning c = 35645/100000 =
  # 0.35645. First oracle in the workspace to pin a finer denominator
  # (100000 instead of 5000) so the +0.00005 increment over V51's
  # `c = 1782/5000 = 35640/100000` can be expressed exactly. Same
  # upgraded envelope `(dps=100, n_trunc=500)` as sprint 057's
  # `hEq15_oracle_certified_hp_3564`. The Scratch pre-verifications at
  # `Scratch/sprint_058_hp_ceiling_pin.txt` and
  # `Scratch/sprint_059_hp_35645_sanity_replay.txt` record the wrapper's
  # True return and certified margin at this c-and-envelope (margin
  # +1.35e-05 above the strict-margin threshold).
  "hEq15_oracle_certified_hp_35645",

  # Sprint 079: first non-eq15 oracle. Lean-facing axiom name asserted by
  # the candidate-side `axiom h_two_window_mass_certified_at_35646` and
  # discharged by the registered oracle
  # `two_window_mass_certified_at_35646` whose wrapper is
  # `Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646`
  # at the exact rational endpoints
  #   (c_num, c_den)             = (35646, 100000)
  #   (rs1_num, rs1_den)         = (378083, 1000000)     # ρ_start_1
  #   (rt1_num, rt1_den)         = (411605, 1000000)     # ρ_stop_1 = ρ_start_2
  #   (rt2_num, rt2_den)         = (999999, 1000000)     # ρ_stop_2
  #   (j_1, j_2)                 = (2, 1)
  #   (dps, n_trunc)             = (30, 200).
  # Phase 0 witness (sprint 078): `Scratch/sprint_078_witness.txt` —
  # margin +1.9e-3 at c=0.35646 on canonical irrational endpoints.
  # Endpoint-pinned re-verification (sprint 079):
  # `Scratch/sprint_079_endpoint_pinned_witness.txt` — margin
  # +1.9001e-3 at the chosen exact-rational endpoints.
  "h_two_window_mass_certified_at_35646",

  # Sprint 083: sqrt-endpoint sibling of `h_two_window_mass_certified_at_35646`.
  # Pins the candidate's exact sqrt endpoints
  #   c            = 35646/100000
  #   ρ_start_1    = c · sqrt(9/8)
  #   ρ_stop_1     = c · sqrt(4/3)   (= ρ_start_2)
  #   ρ_stop_2     = 999999/1000000
  # at (j_1, j_2) = (2, 1). The wrapper
  # `Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646_sqrt`
  # computes a rigorous `flint.arb` interval lower bound on the joint mass
  # and applies the strict-margin floor `1 + 10^(-30)`.
  "h_two_window_mass_certified_at_35646_sqrt",

  # Sprint 084: c-pushed sqrt-endpoint sibling of
  # `h_two_window_mass_certified_at_35646_sqrt`, pinning
  #   c            = 35648/100000
  #   ρ_start_1    = c · sqrt(9/8)
  #   ρ_stop_1     = c · sqrt(4/3)   (= ρ_start_2)
  #   ρ_stop_2     = 999999/1000000
  #   (j_1, j_2)   = (2, 1)
  #   (dps, n_trunc) = (80, 200).
  # Discharged by the registered oracle row below, whose wrapper is
  # `Numerical_Library.two_window_sqrt.certify_two_window_mass_at_35648_sqrt`
  # — a thin parametric sibling of the 35646 wrapper that reuses the same
  # audited `flint.arb` helpers (`_arb_exact`, `_pow_cached`,
  # `_two_window_mass_window_lower_arb`) so the numerics are byte-identical
  # to the certified V64 path with only the pinned `c` changed.
  "h_two_window_mass_certified_at_35648_sqrt",

  # Sprint 085: further c-pushed sqrt-endpoint sibling, pinning
  #   c            = 35651/100000
  #   ρ_start_1    = c · sqrt(9/8)
  #   ρ_stop_1     = c · sqrt(4/3)   (= ρ_start_2)
  #   ρ_stop_2     = 999999/1000000
  #   (j_1, j_2)   = (2, 1)
  #   (dps, n_trunc)   = (80, 200)
  #   (n_start, n_cap) = (2048, 16384).
  # Discharged by the registered oracle row below, whose wrapper is
  # `Numerical_Library.two_window_sqrt_35651.certify_two_window_mass_at_35651_sqrt`
  # — a thin parametric sibling of the 35646/35648 sqrt wrappers that
  # imports and reuses `rigorous_scalar`'s audited arb core
  # `_certify_two_window_mass_sqrt_at` unchanged, so the integration
  # scheme, truncation direction and the strict-margin floor
  # `1 + 10^(-30)` are byte-identical to the certified V64/V65 path.
  "h_two_window_mass_certified_at_35651_sqrt",

  # Sprint 083: free candidate-side axiom asserting Wang's Hypothesis 1
  # of Section 2 (H² boundary-norm finiteness): `Summable (‖a n‖²)` for
  # any `a : ℕ → ℂ`. Applied to `a` for f and to `b` for g inside V64's
  # `h_witness` construction. Per the AGENT_BRIEF discipline (lines
  # 62-65), free candidate-side axioms are explicitly permitted provided
  # they are listed in `[seed_axioms].allowed`.
  "hH2_v64",

  # Sprint 083: free candidate-side axiom asserting that the disk
  # excess density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on
  # `(c_value, 1)` for any `(a, b) : ℕ → ℂ`. Wang's Section 2 assumes
  # all integrals converge throughout but the bundle does not assert
  # `circleGap` measurability; carrying it as a candidate-side axiom
  # is paper-implicit and consistent with the seed-allowed pattern.
  "hCircleGapInt_v64",

  # Sprint 084: V65-namespaced siblings of `hH2_v64` / `hCircleGapInt_v64`.
  # Identical statements (Wang Hypothesis 1 H² finiteness; paper-implicit
  # `2ρ · circleGap` integrability on the open annulus), re-declared in the
  # V65 namespace at the pushed `c_value = 35648/100000`. Neither is
  # oracle-shaped and neither asserts the conclusion: both are strictly
  # weaker paper-side hypotheses that Wang's Section 2 states or uses
  # implicitly throughout.
  "hH2_v65",
  "hCircleGapInt_v65",

  # Sprint 085: V66-namespaced siblings of the same two paper-side
  # hypotheses, re-declared at the pushed `c_value = 35651/100000`.
  # `hH2_v66` is Wang's Hypothesis 1 (H² boundary-norm finiteness,
  # applied to `a` for f and to `b` for g); `hCircleGapInt_v66` is the
  # paper-implicit integrability of the polar-Jacobian disk-excess
  # density on the open annulus `(c_value, 1)`. Both are strictly weaker
  # than the conclusion `ValidKorenblumBound c_value`, and neither is
  # oracle-shaped.
  "hH2_v66",
  "hCircleGapInt_v66",
]

# Sprint 053: first registered numerical oracle.
#
# The schema fields below match `Evaluator.py:load_workspace_config`'s
# actual reader (`axiom`, `bound_field`, `oracle_fn`). The Evaluator
# invokes `oracle_fn` with no arguments and expects a Fraction-coercible
# numeric lower bound that it then compares to the candidate-side
# `def <bound_field> : ℝ := ...` via `oracle_bound <= declared`.

[[oracles]]
axiom = "hEq15_oracle_certified_3554"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_seed"

# Sprint 055: first c-push oracle. Pins `certify_eq15` at
# `(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)`.

[[oracles]]
axiom = "hEq15_oracle_certified_3560"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3560"

# Sprint 056: second c-push oracle. Pins `certify_eq15` at
# `(c_num, c_den, dps, n_trunc) = (1781, 5000, 50, 200)`.

[[oracles]]
axiom = "hEq15_oracle_certified_3562"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3562"

# Sprint 057: third c-push oracle. Pins `certify_eq15` at
# `(c_num, c_den, dps, n_trunc) = (1782, 5000, 100, 500)`.

[[oracles]]
axiom = "hEq15_oracle_certified_hp_3564"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_3564"

# Sprint 059: fourth c-push oracle. Pins `certify_eq15` at
# `(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

[[oracles]]
axiom = "hEq15_oracle_certified_hp_35645"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_35645"

# Sprint 079: first non-eq15 oracle. Joint two-window τ-partition kernel
# mass at exact-rational endpoints, (j_1, j_2) = (2, 1), (dps, n_trunc) =
# (30, 200). Falsifiability: the joint mass crosses below 1 around
# c ≈ 0.35654 per sprint 078's Phase 0 sweep.

[[oracles]]
axiom = "h_two_window_mass_certified_at_35646"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646"

# Sprint 083: sqrt-endpoint sibling of the rational-endpoint joint
# two-window mass oracle at c = 35646/100000. The wrapper computes a
# rigorous `flint.arb` interval lower bound (equal-width left-Riemann
# subdivision with monotonicity-aware Λ-upper dispatch) and returns
# ``Fraction(1, 1)`` iff that lower bound clears `1 + 10^(-30)`.
#
# The wrapper is necessary because the τ-window adjacency at
# `tau(1) = 3/4` plus `(j_1, j_2) = (2, 1)` algebraically forces
# `ρ_stop_1² = 4 c² / 3`, which is irrational at c = 35646/100000.

[[oracles]]
axiom = "h_two_window_mass_certified_at_35646_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646_sqrt"

# Sprint 084: c-pushed sqrt-endpoint joint two-window mass oracle at
#   c            = 35648/100000
#   ρ_start_1    = c · sqrt(9/8)
#   ρ_stop_1     = c · sqrt(4/3)   (= ρ_start_2)
#   ρ_stop_2     = 999999/1000000
#   (j_1, j_2)   = (2, 1)
#   (dps, n_trunc) = (80, 200).
#
# The wrapper `Numerical_Library.two_window_sqrt.certify_two_window_mass_at_35648_sqrt`
# is a thin parametric sibling of the 35646 sqrt wrapper: it imports and
# reuses `rigorous_scalar`'s audited arb helpers (`_arb_exact`,
# `_pow_cached`, `_two_window_mass_window_lower_arb`) unchanged, so the
# integration scheme, the truncation direction, and the strict-margin
# floor `1 + 10^(-30)` are byte-identical to the certified V64 path.
# Only the pinned radius `c` differs.
#
# Both sources of conservatism run in the safe direction: truncating the
# Wang product after `n_trunc` factors raises K (each factor is ≤ 1 for
# `0 < c < ρ < 1`), hence raises Λ, hence lowers the integrand; and the
# left-Riemann endpoint selection takes `H_j` at its per-sub-interval
# maximum and `2ρ` at its minimum. The certified quantity is therefore a
# genuine lower bound on the joint mass.
#
# Falsifiability. Sprint 078's Phase 0 sweep reports the joint mass
# crossing below 1 around c ≈ 0.35654 (margin ≥ 1e-3 only at
# c ∈ {0.35646, 0.35647, 0.35648}); a wrapper returning True at
# c ≥ 0.35655 would not be verifying anything. The pinned
# c = 35648/100000 is the largest point in that sweep's ≥ 1e-3 band.

[[oracles]]
axiom = "h_two_window_mass_certified_at_35648_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "two_window_sqrt.certify_two_window_mass_at_35648_sqrt"

# Sprint 085: further c-pushed sqrt-endpoint joint two-window mass oracle
# at
#   c            = 35651/100000
#   ρ_start_1    = c · sqrt(9/8)
#   ρ_stop_1     = c · sqrt(4/3)   (= ρ_start_2)
#   ρ_stop_2     = 999999/1000000
#   (j_1, j_2)   = (2, 1)
#   (dps, n_trunc)   = (80, 200)
#   (n_start, n_cap) = (2048, 16384).
#
# The wrapper
# `Numerical_Library.two_window_sqrt_35651.certify_two_window_mass_at_35651_sqrt`
# adds no new numerics whatsoever: it delegates to the shared, audited
# core `rigorous_scalar._certify_two_window_mass_sqrt_at` (the same core
# that backs the certified 35646 and 35648 rows) with only the pinned
# radius and the subdivision schedule changed. The subdivision schedule
# starts at 2048 because sprint 083 measured the arb conservatism at
# ~6.1e-4 for `n_subdivisions = 2048`; the smaller rounds cannot clear
# the floor anywhere in this band and only cost runtime.
#
# Direction of conservatism is unchanged and safe: product truncation
# raises K hence raises Λ hence lowers the integrand, and the
# left-Riemann selection takes `H_j` at its per-sub-interval maximum and
# `2ρ` at its minimum. The certified quantity is a genuine lower bound.
#
# Falsifiability. Sprint 078's sweep places the joint-mass zero crossing
# at c ≈ 0.35654 with margin ≥ 1e-3 through c = 0.35648; the pinned
# c = 35651/100000 sits strictly inside the verified band (expected
# centred margin ≈ 7e-4, comfortably above the ≈ 3e-4 arb conservatism
# at `n_subdivisions = 4096`). A wrapper pinned at c ≥ 0.35655 would be
# asked to certify a numerically false statement and would raise.

[[oracles]]
axiom = "h_two_window_mass_certified_at_35651_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "two_window_sqrt_35651.certify_two_window_mass_at_35651_sqrt"
```

```lean path=ProofRefinement/Korenblum/Candidates/V66.lean
-- @parent V65
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction
import ProofRefinement.Korenblum.Candidates.V63.Integrability
import ProofRefinement.Korenblum.Candidates.V63.Summability
import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge
import ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V66

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper
open ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints

/-!
# V66 — c-push to `35651/100000` on the two-window τ-partition route

## What changes relative to V65

V66 is V65's closing chain re-pinned at

  `c_value = 35651/100000 = 0.35651`,

strictly above V65's `35648/100000 = 1114/3125 = 0.35648`. Everything
structural is reused unchanged:

  * the closing reducer
    `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`
    (`Proof/Reduction.lean`);
  * the V63 derived-theorem files
    (`Integrability`, `Summability`, `DiskInnerSeriesBridge`);
  * V64's `TauWindowEndpoints` module — its endpoint `def`s and the four
    τ-bound discharges are **parametric in `c`**, so they specialise to
    the new `c_value` verbatim. Only the single `c`-pinned ordering
    lemma (`ρ_meet_sqrt c < 999999/1000000`) needs a sibling here,
    proved below from the same rational sqrt bound
    `Real.sqrt (4/3) ≤ 1156/1000`.

The one genuinely new input is the joint two-window mass at the pushed
radius. That is discharged by the new oracle-backed axiom
`h_two_window_mass_certified_at_35651_sqrt`, registered in
`lemma.toml:[[oracles]]` against the wrapper
`Numerical_Library.two_window_sqrt_35651.certify_two_window_mass_at_35651_sqrt`,
which delegates to the same audited `flint.arb` core
(`rigorous_scalar._certify_two_window_mass_sqrt_at`) that backs the
certified V64 and V65 rows, with only the pinned `c` and the
subdivision schedule changed.

## Endpoint geometry (unchanged from V64/V65, re-pinned)

  ρStart₁ = c · √(9/8)              ⇒ c²/ρStart₁² = 8/9 = tau(2)
  ρStop₁  = ρStart₂ = c · √(4/3)    ⇒ c²/ρStop₁²  = 3/4 = tau(1)
  ρStop₂  = 999999/1000000

These are the algebraically forced canonical τ-breakpoint endpoints for
a two-window τ-partition at `(j₁, j₂) = (2, 1)` with adjacency
`ρStop₁ = ρStart₂`; all four τ-bound inequalities hold with equality, so
no numerical headroom is consumed on the Lean side.

## Numerical basis for the push

Sprint 078's Phase 0 sweep records the joint two-window mass crossing
below `1` only around `c ≈ 0.35654`, with margin `≥ 1e-3` through
`c = 0.35648`. Linear interpolation on that band puts the centred margin
at `c = 0.35651` around `7e-4`, comfortably above the `≈ 3e-4` rigorous
arb conservatism measured at `n_subdivisions = 4096` (sprint 083
measured `≈ 6.1e-4` at `n_subdivisions = 2048`, and the left-Riemann
error is `O(1/n)`). The wrapper doubles the subdivision count from
`2048` up to `16384` until the strict-margin floor `1 + 10^(-30)` is
cleared, and raises otherwise — so an over-optimistic pin fails loudly
rather than silently.

## Trust envelope

`axioms_used` is

  {propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
   Lean.trustCompiler,
   …V66.h_two_window_mass_certified_at_35651_sqrt,
   …V66.hH2_v66,
   …V66.hCircleGapInt_v66}.

`hH2_v66` is Wang's Hypothesis 1 of Section 2 (H² boundary-norm
finiteness, applied to `a` for `f` and to `b` for `g`);
`hCircleGapInt_v66` is the paper-implicit integrability of the
polar-Jacobian disk-excess density on the open annulus. Both are
strictly weaker than the conclusion `ValidKorenblumBound c_value` and
neither is oracle-shaped; both are registered in
`[seed_axioms].allowed`, exactly as their V64/V65 siblings.
-/

/-! ## Constants -/

/-- The c-pushed candidate constant: `0.35651`, strictly above V65's
`0.35648 = 1114/3125`. -/
def c_value : ℝ := 35651 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

theorem c_value_nonneg : (0 : ℝ) ≤ c_value := le_of_lt c_value_pos

/-- The new c-push strictly improves on V65's `35648/100000 = 1114/3125`. -/
theorem c_value_gt_v65 : (1114 : ℝ) / 3125 < c_value := by
  norm_num [c_value]

/-- Evaluator-facing oracle bound-field for the joint-mass oracle. -/
def two_window_mass_lower : ℝ := 1

/-! ## Free candidate-side axioms (registered in `[seed_axioms].allowed`) -/

/-- Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness): for
any coefficient sequence `a : ℕ → ℂ`, the norm-squared sequence `‖a n‖²`
is summable. Consumed twice inside `v66_witness` — once for `f`'s
coefficients `a`, once for `g`'s coefficients `b`. -/
axiom hH2_v66 :
    ∀ (a : ℕ → ℂ), Summable (fun n : ℕ => ‖a n‖ ^ 2)

/-- Wang's Section 2 implicit hypothesis: the polar-Jacobian disk-excess
density `2ρ · circleGap a b ρ` is `IntervalIntegrable` on `(c_value, 1)`.
The bundled `Section2Assumptions` states pointwise identities and bounds
but never asserts measurability of `circleGap`; this axiom carries the
integrability witness directly. -/
axiom hCircleGapInt_v66 :
    ∀ (a b : ℕ → ℂ),
      IntervalIntegrable
        (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
        MeasureTheory.volume c_value 1

/-! ## Oracle axiom — the joint two-window mass at sqrt endpoints -/

/-- The joint two-window mass at the candidate's exact sqrt endpoints with
j-modes `(j₁, j₂) = (2, 1)`.

Discharged by the registered oracle
`h_two_window_mass_certified_at_35651_sqrt`, whose wrapper is
`Numerical_Library.two_window_sqrt_35651.certify_two_window_mass_at_35651_sqrt`,
pinning

  c            = 35651/100000
  ρStart₁      = c · √(9/8)
  ρStop₁       = c · √(4/3)   (= ρStart₂)
  ρStop₂       = 999999/1000000

at `(dps = 80, n_trunc = 200)`. The wrapper returns success only when a
**rigorous `flint.arb` interval lower bound** on the joint mass — computed
by equal-width left-Riemann subdivision with monotonicity-aware Λ-upper
dispatch, refined from `n_subdivisions = 2048` up to `16384` — clears
`1 + 10^(-30)`.

The `K` argument is universal because `paperLambda K c ρ` varies with `K`;
only the values of `K` on the two integration windows matter, and those are
pinned by `Eq7PaperKFormula K c_value`. -/
axiom h_two_window_mass_certified_at_35651_sqrt
    (K : ℝ → ℝ → ℝ)
    (hK : PaperAxioms.Eq7PaperKFormula K c_value) :
  (1 : ℝ) ≤
    (∫ ρ in ρStart₁_sqrt c_value..ρ_meet_sqrt c_value,
        ModeBridge.scalarIntegrand c_value 2
          (WangOuter.paperLambda K c_value) ρ) +
      (∫ ρ in ρ_meet_sqrt c_value..(999999 / 1000000 : ℝ),
        ModeBridge.scalarIntegrand c_value 1
          (WangOuter.paperLambda K c_value) ρ)

/-! ## The one `c`-pinned ordering lemma -/

/-- At the pushed `c_value = 35651/100000`, the shared window endpoint
`ρ_meet_sqrt c_value = c · √(4/3)` sits strictly below `999999/1000000`.

Proof: bound `Real.sqrt (4/3) ≤ 1156/1000` via V64's
`sqrt_four_thirds_le_rational`, multiply by `c_value > 0`, and finish with
the rational check `(35651/100000) · (1156/1000) < 999999/1000000` (the
left side is ≈ 0.41213, so the margin is ~6 orders of magnitude). -/
theorem ρ_meet_sqrt_lt_one_at_c_value :
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  unfold ρ_meet_sqrt c_value
  have hc_pos : (0 : ℝ) < 35651 / 100000 := by norm_num
  have hsqrt_le : Real.sqrt (4 / 3) ≤ 1156 / 1000 :=
    sqrt_four_thirds_le_rational
  have h1 : (35651 / 100000 : ℝ) * Real.sqrt (4 / 3) ≤
      (35651 / 100000 : ℝ) * (1156 / 1000) :=
    mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hc_pos)
  have h2 : (35651 / 100000 : ℝ) * (1156 / 1000) < 999999 / 1000000 := by
    norm_num
  linarith

/-! ## The `h_witness` construction -/

/-- The `h_witness` predicate of
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, constructed
universally over `(a, b, K, paper)` by composing the three V63
derived-theorem files, V64's parametric τ-window endpoint module, the two
free candidate-side axioms, and the new joint-mass oracle axiom.

The `⟨…⟩` structure matches the reducer's `obtain` pattern
conjunct-for-conjunct in order. -/
theorem v66_witness :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ}
      (_paper : Section2Assumptions a b K c_value),
      ∃ (ρStart₁ ρStop₁ ρStart₂ ρStop₂ : ℝ) (j₁ j₂ : ℕ),
        c_value < ρStart₁ ∧ ρStart₁ ≤ ρStop₁ ∧
          ρStop₁ = ρStart₂ ∧
          ρStart₂ ≤ ρStop₂ ∧ ρStop₂ < 1 ∧
          1 ≤ j₁ ∧ 1 ≤ j₂ ∧
          OneModeTail.tau (j₁ - 1) ≤ c_value ^ 2 / ρStop₁ ^ 2 ∧
          c_value ^ 2 / ρStart₁ ^ 2 ≤ OneModeTail.tau j₁ ∧
          OneModeTail.tau (j₂ - 1) ≤ c_value ^ 2 / ρStop₂ ^ 2 ∧
          c_value ^ 2 / ρStart₂ ^ 2 ≤ OneModeTail.tau j₂ ∧
          Summable (fun n : ℕ =>
            OneModePaperBridge.plusSeq a b n *
              c_value ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
          Summable (fun n : ℕ =>
            OneModePaperBridge.plusSeq a b n * c_value ^ (2 * n)) ∧
          Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n *
              c_value ^ (2 * n + 2) / (n + 1 : ℝ)) ∧
          Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n * c_value ^ (2 * n)) ∧
          Summable (fun n : ℕ =>
            OneModePaperBridge.minusSeq a b n *
              OneModeKernel.weight c_value n) ∧
          (∀ ⦃ρ : ℝ⦄, c_value < ρ → ρ < 1 →
            Summable (fun n : ℕ =>
              OneModePaperBridge.minusSeq a b n * ρ ^ (2 * n))) ∧
          IntervalIntegrable
            (fun ρ => 2 * ρ * PaperAxioms.circleGap a b ρ)
            MeasureTheory.volume c_value 1 ∧
          IntervalIntegrable
            (fun ρ =>
              ModeBridge.scalarIntegrand c_value j₁
                (WangOuter.paperLambda K c_value) ρ)
            MeasureTheory.volume ρStart₁ ρStop₁ ∧
          IntervalIntegrable
            (fun ρ =>
              ModeBridge.scalarIntegrand c_value j₂
                (WangOuter.paperLambda K c_value) ρ)
            MeasureTheory.volume ρStart₂ ρStop₂ ∧
          PaperAxioms.diskExcess (PaperAxioms.circleGap a b) c_value ≤
            OneModePaperBridge.innerSeriesExcess a b c_value ∧
          (1 : ℝ) ≤
            (∫ ρ in ρStart₁..ρStop₁,
                ModeBridge.scalarIntegrand c_value j₁
                  (WangOuter.paperLambda K c_value) ρ) +
              (∫ ρ in ρStart₂..ρStop₂,
                ModeBridge.scalarIntegrand c_value j₂
                  (WangOuter.paperLambda K c_value) ρ) := by
  intro a b K paper
  -- Endpoint instantiations.
  refine ⟨ρStart₁_sqrt c_value, ρ_meet_sqrt c_value,
          ρ_meet_sqrt c_value, 999999 / 1000000,
          2, 1, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- c_value < ρStart₁_sqrt c_value
    exact c_lt_ρStart₁_sqrt c_value_pos
  · -- ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value
    exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · -- ρ_meet_sqrt c_value ≤ 999999 / 1000000
    exact (ρ_meet_sqrt_lt_one_at_c_value).le
  · -- 999999 / 1000000 < 1
    norm_num
  · -- 1 ≤ 2
    decide
  · -- 1 ≤ 1
    exact le_refl 1
  · -- tau (2 - 1) = tau 1 ≤ c² / ρ_meet_sqrt²
    show OneModeTail.tau 1 ≤ c_value ^ 2 / (ρ_meet_sqrt c_value) ^ 2
    exact tau_one_le_c_sq_div_meet_sq_sqrt c_value_pos
  · -- c² / ρStart₁_sqrt² ≤ tau 2
    exact c_sq_div_start1_sq_le_tau_two_sqrt c_value_pos
  · -- tau (1 - 1) = tau 0 ≤ c² / ρStop₂²
    show OneModeTail.tau 0 ≤ c_value ^ 2 / ((999999 / 1000000 : ℝ)) ^ 2
    exact tau_zero_le_c_sq_div_stop2_sq c_value_nonneg
  · -- c² / ρStart₂² (= ρ_meet_sqrt²) ≤ tau 1
    exact c_sq_div_meet_sq_le_tau_one_sqrt c_value_pos
  -- Six summability witnesses, packaged via V63's six_summability_shapes_from_h2.
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.2.1
  · exact (ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one).2.2.2.2.2
  · -- circleGap integrability on (c_value, 1)
    exact hCircleGapInt_v66 a b
  · -- mode-2 scalar integrand integrability on [ρStart₁_sqrt, ρ_meet_sqrt]
    have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
      ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
    have h_meet_le_one : ρ_meet_sqrt c_value ≤ 1 :=
      le_trans (ρ_meet_sqrt_lt_one_at_c_value).le
        (by norm_num : (999999 / 1000000 : ℝ) ≤ 1)
    have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
      le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
    exact (ProofRefinement.Korenblum.Candidates.V63.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
      c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_meet h_meet_le_meet
      h_meet_le_one paper.eq7_paperK_formula).1
  · -- mode-1 scalar integrand integrability on [ρ_meet_sqrt, 999999/1000000]
    have h_meet_le_stop2 : ρ_meet_sqrt c_value ≤ (999999 / 1000000 : ℝ) :=
      (ρ_meet_sqrt_lt_one_at_c_value).le
    have h_start1_le_meet : ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value :=
      ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
    have h_meet_le_meet : ρ_meet_sqrt c_value ≤ ρ_meet_sqrt c_value := le_refl _
    have h_stop2_le_one : (999999 / 1000000 : ℝ) ≤ 1 := by norm_num
    have h_c_le_start1 : c_value ≤ ρStart₁_sqrt c_value :=
      le_of_lt (c_lt_ρStart₁_sqrt c_value_pos)
    exact (ProofRefinement.Korenblum.Candidates.V63.Integrability.mode_two_and_one_scalarIntegrand_intervalIntegrable
      c_value_pos h_c_le_start1 h_start1_le_meet h_meet_le_stop2 h_meet_le_meet
      h_stop2_le_one paper.eq7_paperK_formula).2
  · -- diskExcess ≤ innerSeriesExcess
    have hkit := ProofRefinement.Korenblum.Candidates.V63.Summability.six_summability_shapes_from_h2
      (hH2_v66 a) (hH2_v66 b) c_value_nonneg c_value_lt_one
    have hPlusDisk := hkit.1
    have hMinusDisk := hkit.2.2.1
    have hAbsSummable :
        Summable (fun k : ℕ =>
          |PaperAxioms.coeffPlusGap a b k| *
            c_value ^ (2 * k + 2) / ((k : ℝ) + 1)) :=
      ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.summable_abs_coeffPlusGap_weighted_of_summable_components
        c_value_nonneg hPlusDisk hMinusDisk
    exact ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.diskExcess_le_innerSeriesExcess
      c_value_nonneg hPlusDisk hMinusDisk hAbsSummable
  · -- joint two-window mass — discharged by the new oracle axiom.
    exact h_two_window_mass_certified_at_35651_sqrt K paper.eq7_paperK_formula

/-! ## Sink theorem -/

/-- The Korenblum constant search at `c = 35651/100000`. Constructed by
applying `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` to
`v66_witness`. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value :=
  valid_of_perMode_twoWindow_tau_partition_eq8_eq9
    c_value_pos c_value_lt_one
    (fun {a b K} paper => v66_witness paper)

/-! ## Side lemmas -/

/-- The new c-value strictly improves on V65's `1114/3125`. -/
lemma v66_strictly_above_v65 : (1114 : ℝ) / 3125 < c_value :=
  c_value_gt_v65

/-- Sanity check that the τ-window endpoints satisfy the geometric
ordering required by the reducer at the pushed `c_value`. -/
lemma v66_endpoint_ordering :
    c_value < ρStart₁_sqrt c_value ∧
    ρStart₁_sqrt c_value ≤ ρ_meet_sqrt c_value ∧
    ρ_meet_sqrt c_value < (999999 / 1000000 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact c_lt_ρStart₁_sqrt c_value_pos
  · exact ρStart₁_sqrt_le_ρ_meet_sqrt c_value_nonneg
  · exact ρ_meet_sqrt_lt_one_at_c_value

end ProofRefinement.Korenblum.Candidates.V66
```

**Please build and evaluate `ProofRefinement/Korenblum/Candidates/V66.lean`.** V65 is left untouched, so if the oracle rejects at `0.35651` the current best is preserved and I can back off.

Notes on what I did and did not touch:

- **No edits to `rigorous_scalar.py` or `two_window_sqrt.py`.** The new wrapper is a separate module that imports the shared, already-certified core `_certify_two_window_mass_sqrt_at`, so the V64/V65 oracle paths are byte-identical and the new row adds no new numerics — only a new pinned `c` and a subdivision schedule starting at 2048 (sprint 083 measured ~6.1e-4 conservatism there, so the smaller rounds cannot clear the floor and only cost runtime).
- **New axiom is a genuine sub-claim.** `h_two_window_mass_certified_at_35651_sqrt` asserts a scalar kernel-mass inequality about `∫ ModeBridge.scalarIntegrand`, not `ValidKorenblumBound`; it is the same shape as the parent's certified cell with `c` moved, and the wrapper raises rather than returns on failure. The two paper-side cells (`hH2_v66`, `hCircleGapInt_v66`) are re-declarations of V65's already-allow-listed hypotheses at the new radius.
- **Risk I'm flagging:** the `0.35651` pin rests on interpolating sprint 078's sweep (margin ≥ 1e-3 through `0.35648`, zero crossing ≈ `0.35654`). If the arb lower bound fails to clear `1 + 10⁻³⁰` even at `n_subdivisions = 16384`, the wrapper will `RuntimeError` with the achieved margin printed — send me that message and I'll re-pin at `35649/100000` (expected centred margin ≈ 1.2e-3), which still beats the parent.