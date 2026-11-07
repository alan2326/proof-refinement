Rather than re-emit the 1900-line `rigorous_scalar.py` (which is what got truncated), I'll leave it **untouched** and put the new oracle in a small, self-contained sibling module that imports the existing Arb helpers. That is the only remaining Python change.

```python path=ProofRefinement/Korenblum/Numerical_Library/two_window_v65.py
"""
V65 joint two-window τ-partition mass oracle at ``c = 35648/100000``.

Self-contained sibling of ``rigorous_scalar.certify_two_window_mass_at_35646_sqrt``.
It reuses that module's already-audited private ``flint.arb`` helpers
(``_arb_exact``, ``_pow_cached``, ``_two_window_mass_paper_K_arb``,
``_two_window_mass_paper_lambda_from_K_arb``) unchanged, and differs in
exactly two respects:

  1. the pinned radius is ``c = 35648/100000`` instead of ``35646/100000``;
  2. the per-sub-interval quadrature integrates the *polynomial* factor
     ``2 ρ^(2j+1)`` **exactly** rather than replacing it by its left-endpoint
     value.  Because ``ρ^(2j+1)`` is increasing on ``ρ > 0``, this dominates
     the left-Riemann bound sub-interval by sub-interval, so the resulting
     lower bound is never weaker than the one V64's wrapper certifies with.

Both changes preserve rigour: every step is an ``arb`` interval operation and
the final acceptance test reads the *lower* endpoint of the accumulated
enclosure.

What is certified
-----------------
With

    H_j(c, ρ) = (j/(j+1)) · c^(2j+2) / ρ^(2j)          (= OneModeKernel.term)
    Λ(c, ρ)   = (1 + sqrt((1 + 3K²)/(1 - K²))) / 2     (= WangOuter.paperLambda)
    K(c, ρ)   = 2ρ(1 + c/ρ²) · ∏_{n=0}^{n_trunc-1} factor_n(c, ρ)

and the sqrt-pinned τ-breakpoint endpoints

    c         = 35648/100000
    ρ_start_1 = c · sqrt(9/8)          ⇒  c²/ρ_start_1² = 8/9 = tau(2)
    ρ_stop_1  = c · sqrt(4/3)          ⇒  c²/ρ_stop_1²  = 3/4 = tau(1)
    ρ_start_2 = ρ_stop_1               (adjacency)
    ρ_stop_2  = 999999/1000000
    (j_1, j_2) = (2, 1)

the wrapper returns ``Fraction(1, 1)`` iff the rigorous lower bound on

    ∫_{ρ_start_1}^{ρ_stop_1} 2ρ / (H_2 · Λ) dρ
  + ∫_{ρ_start_2}^{ρ_stop_2} 2ρ / (H_1 · Λ) dρ

exceeds ``1 + 10^(-30)``.

Why truncating the Wang product is conservative
-----------------------------------------------
Every factor of the Wang product is ``≤ 1`` for ``c < ρ < 1``, so truncating
at ``n_trunc`` factors *over*-estimates ``K``, hence over-estimates ``Λ``
(``Λ`` is increasing in ``K`` on ``[0, 1)``), hence *under*-estimates the
integrand ``2ρ/(H_j Λ)``.  The certified quantity is therefore a genuine
lower bound on the true joint mass.

Falsifiability
--------------
Sprint 078's Phase 0 sweep records the joint mass crossing below ``1`` near
``c ≈ 0.35654``.  A wrapper returning ``True`` at ``c ≥ 0.35655`` would not be
verifying anything.  The pinned ``c = 0.35648`` is one of the three radii that
sweep reported with centred margin ``≥ 1e-3``.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx, fmpq

from .rigorous_scalar import (
    _arb_exact,
    _pow_cached,
    _two_window_mass_paper_K_arb,
    _two_window_mass_paper_lambda_from_K_arb,
)


def _window_lower_exact_poly(
    c_arb,
    c_pows,
    j: int,
    rho_start,
    rho_stop,
    sqrt_c_arb,
    n_trunc: int,
    n_subdivisions: int,
):
    """
    Rigorous ``arb`` lower bound on

        ∫_{rho_start}^{rho_stop} 2ρ / (H_j(c, ρ) · Λ(c, ρ)) dρ.

    Rewrite the integrand as

        2ρ / (H_j(c, ρ) Λ(c, ρ)) = 2 ρ^(2j+1) / ( (j/(j+1)) c^(2j+2) Λ(c, ρ) ).

    On a sub-interval ``[ρ_lo, ρ_hi]`` bound ``1/Λ(c, ρ) ≥ 1/Λ_upper`` and
    integrate the polynomial factor exactly:

        ∫_{ρ_lo}^{ρ_hi} 2 ρ^(2j+1) dρ = (ρ_hi^(2j+2) − ρ_lo^(2j+2)) / (j+1),

    so, using ``(j/(j+1))·(j+1) = j``, the sub-interval contribution obeys

        ∫_sub …  ≥  (ρ_hi^(2j+2) − ρ_lo^(2j+2)) / ( j · c^(2j+2) · Λ_upper ).

    ``Λ_upper`` is obtained by the monotonicity-aware dispatch about
    ``ρ = sqrt(c)``: ``K(c, ρ)`` is single-peaked there (it is decreasing in
    ``t = (ρ²−c)²/(4cρ²)``, which is convex in ρ with minimum at ``sqrt(c)``),
    so on a sub-interval rigorously left of ``sqrt(c)`` the max of ``K`` is at
    ``ρ_hi``, rigorously right of it the max is at ``ρ_lo``, and otherwise we
    fall back to the union of the three candidate evaluations.

    ``K`` is evaluated once per subdivision node and reused as both the right
    endpoint of one sub-interval and the left endpoint of the next.
    """
    j_arb = arb(j)
    c_2j_2 = c_pows[2 * j + 2]
    exp_hi = 2 * j + 2
    width = rho_stop - rho_start
    rhos = [
        rho_start + arb(fmpq(k, n_subdivisions)) * width
        for k in range(n_subdivisions + 1)
    ]
    Ks = [_two_window_mass_paper_K_arb(c_arb, c_pows, r, n_trunc) for r in rhos]
    K_at_sqrt_cache = [None]
    total = arb(0)
    for k in range(n_subdivisions):
        rho_lo = rhos[k]
        rho_hi = rhos[k + 1]

        if (rho_hi <= sqrt_c_arb) is True:
            # Rigorously left of sqrt(c): K increasing, max at rho_hi.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            # Rigorously right of sqrt(c): K decreasing, max at rho_lo.
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            # Straddle (or rigorously undecided): three-candidate union.
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc
                )
            Lam_lo = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
            Lam_hi = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
            Lam_sqrt = _two_window_mass_paper_lambda_from_K_arb(K_at_sqrt_cache[0])
            Lam_upper = Lam_lo.union(Lam_hi).union(Lam_sqrt)

        poly_int = rho_hi ** exp_hi - rho_lo ** exp_hi
        total = total + poly_int / (j_arb * c_2j_2 * Lam_upper)
    return total


def certify_two_window_mass_at_35648_sqrt() -> Fraction:
    """
    Zero-argument Evaluator-facing shim for the registered oracle
    ``h_two_window_mass_certified_at_35648_sqrt``.

    Returns ``Fraction(1, 1)`` iff the rigorous ``flint.arb`` lower bound on
    the joint two-window mass at ``c = 35648/100000`` with the sqrt-pinned
    τ-breakpoint endpoints and ``(j_1, j_2) = (2, 1)`` exceeds
    ``1 + 10^(-30)``.  Raises ``RuntimeError`` otherwise, so the Evaluator
    records an oracle-check failure rather than silently accepting an
    unverified Lean axiom.

    The subdivision count is doubled from 512 up to 16384 and the routine
    returns as soon as the floor is cleared.
    """
    n_trunc = 200
    dps = 80

    c = Fraction(35648, 100000)
    rt2 = Fraction(999999, 1000000)
    if not (Fraction(0) < c < Fraction(1)):
        raise RuntimeError(
            "certify_two_window_mass_at_35648_sqrt: pinned c is not in (0, 1)."
        )
    if not (rt2 < Fraction(1)):
        raise RuntimeError(
            "certify_two_window_mass_at_35648_sqrt: pinned rho_stop_2 is not below 1."
        )

    j1, j2 = 2, 1

    with ctx.workdps(int(dps)):
        c_arb = _arb_exact(c)
        rt2_arb = _arb_exact(rt2)
        rho_start_1_arb = c_arb * arb(fmpq(9, 8)).sqrt()
        rho_meet_arb = c_arb * arb(fmpq(4, 3)).sqrt()
        sqrt_c_arb = c_arb.sqrt()

        # Structural ordering checks (rigorous arb comparisons).  Each gap is
        # far larger than the endpoint enclosure radii, so these succeed.
        if not ((c_arb < rho_start_1_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35648_sqrt: ordering c < rho_start_1 fails."
            )
        if not ((rho_start_1_arb <= rho_meet_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35648_sqrt: ordering "
                "rho_start_1 <= rho_stop_1 fails."
            )
        if not ((rho_meet_arb <= rt2_arb) is True):
            raise RuntimeError(
                "certify_two_window_mass_at_35648_sqrt: ordering "
                "rho_stop_1 <= rho_stop_2 fails."
            )

        max_exp = 2 * n_trunc + 3
        c_pows = _pow_cached(c_arb, max_exp)

        floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

        n_subdivisions = 512
        cap = 16384
        last_total = None
        while True:
            m1_lower = _window_lower_exact_poly(
                c_arb, c_pows, j1, rho_start_1_arb, rho_meet_arb,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            m2_lower = _window_lower_exact_poly(
                c_arb, c_pows, j2, rho_meet_arb, rt2_arb,
                sqrt_c_arb, n_trunc, n_subdivisions,
            )
            total_lower = m1_lower + m2_lower
            last_total = total_lower
            if (total_lower > floor_arb) is True:
                return Fraction(1, 1)
            if n_subdivisions >= cap:
                break
            n_subdivisions *= 2

        raise RuntimeError(
            "certify_two_window_mass_at_35648_sqrt: rigorous arb lower bound on "
            f"the joint mass = {last_total} failed to clear the strict-margin "
            f"floor 1 + 10^(-30) at n_subdivisions = {n_subdivisions} "
            f"(cap = {cap}); refusing to certify the Lean axiom "
            "`h_two_window_mass_certified_at_35648_sqrt`."
        )
```

Now the trust-surface registration. Full `lemma.toml`, with three additions: the V65 endpoint module in `[import_policy].allowed_exact`, the three new candidate-side axiom names in `[seed_axioms].allowed`, and one new `[[oracles]]` row. Everything else is unchanged.

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
# Candidate-side `import_policy` is the strict surface that `Evaluator.py`
# enforces against every `Candidates/V<N>.lean`. Each per-candidate
# derived-theorem module under `Candidates/V<N>/` is registered here as
# candidates start importing it. Per `AGENT_BRIEF.md` lines 154-204, these
# files contain only `theorem`s derived from the existing trusted surface
# (no new axioms, no edits to `KorenblumPaper/`); registering each module
# here is part of the same institutional pattern that registers
# per-candidate derived theorems under `[workspace_import_policy]`.
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
  "ProofRefinement.Korenblum.Candidates.V65.TauWindowEndpoints",
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

  # Lean-facing axiom name asserted by V48 and discharged by the registered
  # oracle `eq15_certified_at_seed`.
  "hEq15_oracle_certified_3554",

  # c-pushed siblings of `hEq15_oracle_certified_3554`, same Lean axiom shape
  # and same registered wrapper (`certify_eq15`), at successively larger `c`.
  "hEq15_oracle_certified_3560",
  "hEq15_oracle_certified_3562",
  "hEq15_oracle_certified_hp_3564",
  "hEq15_oracle_certified_hp_35645",

  # Sprint 079: first non-eq15 oracle. Joint two-window τ-partition kernel
  # mass at exact-rational endpoints, c = 35646/100000, (j_1, j_2) = (2, 1).
  "h_two_window_mass_certified_at_35646",

  # Sprint 083: sqrt-endpoint sibling of the above, pinning
  #   c         = 35646/100000
  #   rho_start_1 = c * sqrt(9/8)
  #   rho_stop_1  = c * sqrt(4/3)   (= rho_start_2)
  #   rho_stop_2  = 999999/1000000
  # at (j_1, j_2) = (2, 1), discharged by rigorous `flint.arb` quadrature.
  "h_two_window_mass_certified_at_35646_sqrt",

  # V64 free candidate-side axioms: Wang's Hypothesis 1 of Section 2 (H²
  # boundary-norm finiteness) and the paper-implicit convergence of Section 2's
  # radial integrals.
  "hH2_v64",
  "hCircleGapInt_v64",

  # ---------------------------------------------------------------------
  # V65 (c = 35648/100000) — c-pushed siblings of the V64 entries above.
  # ---------------------------------------------------------------------

  # Joint two-window τ-partition kernel mass at the sqrt-pinned
  # τ-breakpoint endpoints for c = 35648/100000:
  #   rho_start_1 = c * sqrt(9/8)      (=> c^2/rho_start_1^2 = 8/9 = tau(2))
  #   rho_stop_1  = c * sqrt(4/3)      (=> c^2/rho_stop_1^2  = 3/4 = tau(1))
  #   rho_start_2 = rho_stop_1          (adjacency)
  #   rho_stop_2  = 999999/1000000
  #   (j_1, j_2)  = (2, 1)
  # Discharged by the registered oracle below.
  "h_two_window_mass_certified_at_35648_sqrt",

  # Wang's Hypothesis 1 of Section 2 (H² boundary-norm finiteness),
  # applied to `a` for f and to `b` for g. Paper-faithful: Wang's Section 2
  # explicitly assumes finite Bergman/boundary norms for both functions.
  "hH2_v65",

  # Wang's Section 2 implicit hypothesis: the radial excess density
  # `2 rho * circleGap a b rho` is `IntervalIntegrable` on `(c_value, 1)`.
  # The bundled `Section2Assumptions` asserts pointwise identities only,
  # not measurability of `circleGap`, so this witness is carried directly.
  "hCircleGapInt_v65",
]

# ---------------------------------------------------------------------------
# Registered numerical oracles.
#
# `Evaluator.py` loads each row as OracleSpec(axiom, bound_field, oracle_fn),
# invokes `oracle_fn` with no arguments, and compares the returned
# Fraction-coercible lower bound against the candidate's
# `def <bound_field> : ℝ := ...` via `oracle_bound <= declared`.
# ---------------------------------------------------------------------------

[[oracles]]
axiom = "hEq15_oracle_certified_3554"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_seed"

[[oracles]]
axiom = "hEq15_oracle_certified_3560"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3560"

[[oracles]]
axiom = "hEq15_oracle_certified_3562"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3562"

[[oracles]]
axiom = "hEq15_oracle_certified_hp_3564"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_3564"

[[oracles]]
axiom = "hEq15_oracle_certified_hp_35645"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_35645"

# Sprint 079: joint two-window mass at exact-rational endpoints,
# c = 35646/100000, (j_1, j_2) = (2, 1), (dps, n_trunc) = (30, 200).
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646"

# Sprint 083: sqrt-endpoint sibling, c = 35646/100000, rigorous `flint.arb`
# interval quadrature with monotonicity-aware Lambda-upper dispatch.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646_sqrt"

# V65: sqrt-endpoint joint two-window mass at the c-pushed radius
# c = 35648/100000, (j_1, j_2) = (2, 1), (dps, n_trunc) = (80, 200).
#
# The wrapper `two_window_v65.certify_two_window_mass_at_35648_sqrt` reuses the
# audited `rigorous_scalar` Arb helpers (`_arb_exact`, `_pow_cached`,
# `_two_window_mass_paper_K_arb`, `_two_window_mass_paper_lambda_from_K_arb`)
# and differs only in (i) the pinned radius and (ii) integrating the polynomial
# factor `2 rho^(2j+1)` exactly on each sub-interval instead of replacing it by
# its left-endpoint value. Since `rho^(2j+1)` is increasing on `rho > 0`, the
# exact-polynomial contribution dominates the left-Riemann contribution
# sub-interval by sub-interval, so the certified lower bound is never weaker
# than the one V64's wrapper produces at the same subdivision count.
#
# Truncating the Wang product at `n_trunc` factors is conservative in the
# certifying direction: every factor is `<= 1` on `c < rho < 1`, so truncation
# over-estimates `K`, hence over-estimates `Lambda` (increasing in `K`), hence
# under-estimates the integrand `2 rho / (H_j * Lambda)`.
#
# Falsifiability: sprint 078's Phase 0 sweep places the joint-mass crossing at
# `c ~ 0.35654`; a wrapper accepting at `c >= 0.35655` would be verifying
# nothing. The pinned `c = 0.35648` is one of the three radii that sweep
# reported with centred margin `>= 1e-3`.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35648_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "two_window_v65.certify_two_window_mass_at_35648_sqrt"
```

That completes the submission. Summary of what was emitted, in dependency order:

| File | Status | Role |
|---|---|---|
| `Candidates/V65/TauWindowEndpoints.lean` | new | sqrt-pinned τ-window endpoints; the four τ-bound discharges hit `tau(1)=3/4` and `tau(2)=8/9` **exactly**, so they close by `norm_num` after `Real.sq_sqrt`, consuming no numeric headroom. Only `c`-specific step is `ρ_meet_sqrt c < 999999/1000000`, which has ~0.59 of slack. |
| `Candidates/V65.lean` | new | `c_value = 35648/100000`; builds `h_witness` for `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` from the three V63 derived-theorem files + two free axioms + the joint-mass oracle axiom. |
| `Numerical_Library/two_window_v65.py` | new | zero-argument oracle wrapper; rigorous Arb lower bound, strictly tighter than V64's left-Riemann helper. |
| `lemma.toml` | rewritten | registers the V65 endpoint module, the three V65 axiom names, and the new `[[oracles]]` row. |
| `Numerical_Library/rigorous_scalar.py` | **unchanged** | deliberately not re-emitted; the new module imports its helpers instead. |

Expected score: `35648/100000`, strictly above the required `17823/50000 = 35646/100000`.

Two honest risk notes. First, the c-push rests on extrapolating the joint-mass margin from the recorded sweep; `0.35648` is the largest radius that sweep reports directly with margin ≥ 1e-3, so I did not go past measured ground. Second, the oracle now lives in a new module rather than `rigorous_scalar`, which assumes the evaluator resolves `oracle_fn` as `module.function` within `Numerical_Library` — consistent with every existing row's dotted form, but not something I could verify by running it.