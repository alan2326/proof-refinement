# Sprint 102: `mp.quad → arb` interval-arithmetic migration of V66's seven-window joint-mass oracle — re-attempt under sprint 101's monotonicity-aware Λ_upper, plus a new `_branch1_window_mass_lower_arb` helper for the three Branch.one boxA windows

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V66.lean` (sprint 088's seven-window c-push at
`c = 178281/500000 = 356562/1000000`; pre-sprint score and post-sprint score
are required to be byte-identical at `178281/500000`).
**Target file**: `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
(rewrite the body of the existing wrapper
`certify_seven_window_mass_at_356562_sqrt`, currently `mp.quad`-based, into a
rigorous `flint.arb` interval-quadrature lower-bound driver; add one new
private helper `_branch1_window_mass_lower_arb` for the Branch.one windows).
**Direction**: oracle-support (structural / credibility — this is the second
`mp.quad → arb` migration in the post-V52 score-push chain; sprint 099 did
the V64 two-window oracle, sprint 100 attempted the V66 migration and was
BLOCKED by mode1's union-radius scaling, sprint 101 fixed the underlying
`_two_window_mass_window_lower_arb` helper to drop mode1's per-subinterval
Λ_upper radius from `O(width/n_subdivisions)` to arb arithmetic precision).

## Goal

Replace the body of
`Numerical_Library/rigorous_scalar.py:certify_seven_window_mass_at_356562_sqrt`
with a rigorous `flint.arb` interval-quadrature lower bound on the seven-
window joint mass, exactly mirroring sprint 099's V64 template. The wrapper's
external contract is byte-preserved: it returns `Fraction(1, 1)` iff the
rigorous arb lower bound on the joint mass clears `1 + 10^(-30)`, raises
`RuntimeError` otherwise. V66's evaluator score remains `178281/500000` and
its `axioms_used` set is preserved set-theoretically.

The seven windows are (per sprint 087's pinning):

```
boxA1   (Branch.one)   [c · (1 + 1e-6),  c · sqrt(50/49)]
boxA2   (Branch.one)   [c · sqrt(50/49), c · sqrt(36/35)]
boxA3   (Branch.one)   [c · sqrt(36/35), c · sqrt(25/24)]
mode4   (j=4)           [c · sqrt(25/24), c · sqrt(16/15)]
mode3   (j=3)           [c · sqrt(16/15), c · sqrt(9/8)]
mode2   (j=2)           [c · sqrt(9/8),   c · sqrt(4/3)]
mode1   (j=1)           [c · sqrt(4/3),   999999/1000000]
```

The four mode-windows (mode4..mode1) are integrated via the existing
sprint-099 helper `_two_window_mass_window_lower_arb` (now strengthened by
sprint 101's monotonicity-aware Λ_upper dispatch). The three Branch.one
boxA-windows are integrated via a **new** helper
`_branch1_window_mass_lower_arb` whose integrand is
`12 ρ³ (ρ² − c²) / (c⁶ · Λ(c, ρ))`.

The new helper mirrors sprint 099's structure conjunct-for-conjunct: equal-
width left-Riemann subdivision, per-subinterval lower bound built from a
rigorous lower bound on the numerator and a rigorous upper bound on the
denominator's `Λ(c, ρ)` (using sprint 101's three-branch
left-of-√c / right-of-√c / straddle dispatch on the same
`_two_window_mass_paper_K_arb` /
`_two_window_mass_paper_lambda_from_K_arb` chain). The numerator
`12 ρ³ (ρ² − c²)` is increasing on `[c, 1]` (its derivative
`12 ρ² (5ρ² − 3c²)` is `> 0` whenever `ρ² > 3c²/5`, which holds throughout
each boxA window since `ρ ≥ c · (1 + 10^(-6)) > c · sqrt(3/5)` — `sqrt(3/5)
≈ 0.7746 < 1 + 10^(-6)`); therefore the numerator's minimum on each
subinterval `[ρ_lo, ρ_hi]` is at `ρ = ρ_lo`, giving the rigorous
per-subinterval numerator lower bound `12 ρ_lo³ (ρ_lo² − c²)`. Combined with
sprint 101's tightened Λ_upper, the boxA per-subinterval radius is governed
by arb arithmetic precision (~10^(-50) at dps=80) rather than by
subdivision width.

The wrapper iterates `n_subdivisions` in powers of 2 from 256 to 16384 (the
sprint-099 cap) until the rigorous lower bound on the seven-window total
clears the strict-margin floor `1 + 10^(-30)`. Sprint 100's diagnostic
table predicts mode1's radius drops from `9.80e-5` (n=16384, sprint-099-old
helper) to `~10^(-30)` order under sprint 101's helper; the boxA radii
were already `~10^(-10)` at `n=2048` under sprint 100's locally-implemented
`_branch1_window_mass_lower_arb`. V66's centered margin `+1.20e-4` should
clear the floor at `n_subdivisions = 2048` with margin headroom of
`~1.2e-4 − 10^(-9) ≈ 1.2e-4` — about 26 orders of magnitude over the
floor.

## Why

The user's planner-launch context names sprint 102 as the natural follow-up
to sprint 101's helper tightening:

> Sprint 101's "Forward implication": sprint 102 can re-attempt V66's
> BLOCKED migration. The bottleneck `m_1.rad = 9.80e-05` at n=16384 should
> drop to `~10^(-10)` range under the new dispatch. V66's centered margin
> `+1.20e-4` should clear the strict floor with headroom to spare.

Sprint 100 was BLOCKED at the contract cap because `m_1.rad ≥ 9.80e-5` at
`n_subdivisions = 16384`, exceeding V66's `+1.20e-4` envelope. Sprint 101
diagnosed and fixed the root cause: the per-subinterval Λ_upper was a
three-candidate union with radius `≈ (Λ_hi − Λ_lo)/2` accumulated `O(width
/ n_subdivisions)` over the subdivision. Under sprint 101's dispatch, the
mode1 window — which sits entirely right of `sqrt(c)` past its single
straddle subinterval — uses a per-subinterval point evaluation
`Λ(K(ρ_lo))`, eliminating the union radius. The arb-arithmetic precision
then governs the residual radius (~10^(-50) at dps=80), three orders of
magnitude tighter than what V66's centered margin requires.

The auxiliary `_branch1_window_mass_lower_arb` helper that sprint 102 must
re-implement was already designed and verified-locally by sprint 100 (boxA
radii at `n_subdivisions = 2048` were `m_a1 ≈ 3.17e-10, m_a2 ≈ 1.21e-10,
m_a3 ≈ 4.48e-10`, three orders of magnitude tighter than required), but
sprint 100's tree was reverted byte-identical when the wrapper-as-a-whole
failed to clear the floor; the helper needs to be re-implemented in this
sprint. Its shape is fixed by parallel structure with sprint 099's
`_two_window_mass_window_lower_arb`:

```python
def _branch1_window_mass_lower_arb(
    c_arb, c_pows, rho_start, rho_stop, sqrt_c_arb, n_trunc, n_subdivisions,
):
    # ∫_{rho_start..rho_stop} 12 ρ³ (ρ²-c²) / (c⁶ Λ(c, ρ)) dρ
    width = rho_stop - rho_start
    rhos = [rho_start + arb(fmpq(k, n_subdivisions)) * width
            for k in range(n_subdivisions + 1)]
    Ks = [_two_window_mass_paper_K_arb(c_arb, c_pows, r, n_trunc) for r in rhos]
    K_at_sqrt_cache = [None]
    c_6 = c_pows[6]
    total = arb(0)
    for k in range(n_subdivisions):
        rho_lo = rhos[k]
        rho_hi = rhos[k + 1]
        sub_width = rho_hi - rho_lo

        # Sprint 101 monotonicity-aware Λ_upper dispatch (mirrors
        # `_two_window_mass_window_lower_arb`).
        if (rho_hi <= sqrt_c_arb) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
        elif (sqrt_c_arb <= rho_lo) is True:
            Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
        else:
            if K_at_sqrt_cache[0] is None:
                K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                    c_arb, c_pows, sqrt_c_arb, n_trunc)
            Lam_lo = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
            Lam_hi = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
            Lam_sqrt = _two_window_mass_paper_lambda_from_K_arb(
                K_at_sqrt_cache[0])
            Lam_upper = Lam_lo.union(Lam_hi).union(Lam_sqrt)

        # Numerator lower bound: 12 ρ³ (ρ²-c²) is increasing on each
        # boxA window since ρ ≥ c·(1+1e-6) > c·sqrt(3/5); minimum at ρ_lo.
        numer_lower = 12 * rho_lo**3 * (rho_lo**2 - c_arb**2)

        integrand_lower = numer_lower / (c_6 * Lam_upper)
        total = total + sub_width * integrand_lower
    return total
```

The wrapper migration is a faithful port of sprint 099's iterative-driver
pattern, composing the three boxA `_branch1_window_mass_lower_arb` calls
with the four mode `_two_window_mass_window_lower_arb` calls.

The strongest objections to choosing this direction over alternatives:

  (a) **"Why not skip ahead to V67 (eight-window) directly?"** V67's
      eight-window architecture has 1 box0 + 7 modes (vs V66's 3 boxA + 4
      modes). Its mode1 window is wider (`[c·√(4/3), 1−10^(-9)]` vs V66's
      `[c·√(4/3), 999999/1000000]`); same dominant-mode1 picture. But V67
      adds j=7, j=6, j=5 modes whose H_j coefficients require larger
      truncation depth at the same precision, doubling the per-call
      integrand work. Sprint 101 explicitly orders V66 → V67 → V68; V66
      is the smaller scope and the natural test for the sprint-101 helper
      fix. Bundling V67 risks generator session overrun.

  (b) **"Why not migrate V65's `certify_two_window_mass_at_35646`
      (rational-endpoint sibling) instead?"** V65 was demoted in sprint
      101's "Out of scope" line 542–545 as "independent follow-up." V65's
      score is dominated by V66 and beyond; migrating V65 doesn't unlock
      any further score-push. V66's migration is in the score-push chain
      (V64 done by sprint 099, V66 next, V67/V68 follow under the same
      template).

  (c) **"Why not push past V68's `c = 71313/200000` instead?"** Slacks
      1, 3, 5 falsified by sprints 093, 094, 095; Slack 2 settled by
      sprint 077; Slack 4 needs a trust expansion proposal whose math
      is not pinned tightly enough yet. The score-push surface at the
      existing trust surface is exhausted — Bulletin §B is unambiguous.
      A c-push sprint without fresh structural insight recapitulates a
      falsified hypothesis.

  (d) **"Why not discharge `hH2_v66` / `hCircleGapInt_v66` from
      `Section2Assumptions` (Slack 4 / trust-surface compaction)?"**
      Bulletin §B(4) says this requires either a `KorenblumPaper/` edit
      (forbidden by AGENT_BRIEF) or a trust-base expansion proposal
      whose math is not pinned tightly enough. Score-neutral but
      out-of-scope at the current trust surface.

  (e) **"Why not Wang Lemma 2 / Fourier orthogonality in `Proof/`?"**
      Demoted across five prior planners (sprints 096–101) as
      speculative infrastructure absent a Lean consumer. Same demotion
      still holds.

  (f) **"Why not hoist `Branch1Integrability.lean` to `Proof/`?"** Demoted
      by sprints 097, 098, 099, and 101 as architecture-specific (only
      V67/V68 import it; no third cross-architecture consumer). Score-
      neutral structural cleanup with no immediate downstream payoff.

  (g) **"Is this a numerical-budget push in disguise?"** No — it is the
      wrapper-side application of sprint 101's algorithmic improvement.
      The cap `n_subdivisions = 16384` is **inherited** from sprint 099's
      template; no cap raise. No `n_trunc` raise. No `dps` raise. The
      compute budget is **strictly lower** than sprint 100's BLOCKED
      attempt because the per-subinterval point evaluation in the
      well-separated branches saves two K evaluations per non-straddle
      sub-interval (sprint 101's PASS verdict measured no slowdown vs
      sprint 099's V64 wrapper, and likely a slight speedup).

  (h) **"Is there a concrete witness it could succeed?"** Yes. Sprint
      100's diagnostic table at `n_subdivisions = 2048` recorded
      `m_a1 ≈ 3.17e-10, m_a2 ≈ 1.21e-10, m_a3 ≈ 4.48e-10` from a
      locally-implemented `_branch1_window_mass_lower_arb` (boxA radii
      already `~10^(-10)` — three orders of magnitude tighter than V66's
      `+1.20e-4` envelope). The mode4..mode1 radii at the same
      `n_subdivisions` were `m_4 ≈ 1.13e-08, m_3 ≈ 6.67e-08,
      m_2 ≈ 9.34e-07, m_1 ≈ 7.83e-04`; under sprint 101's helper, the
      mode1 radius should drop to arb-arithmetic precision (sprint 101
      witness shows ≥10× reduction at the same n_subdivisions; sprint
      100's BLOCKED note projected ~10^(-25)). Even at the conservative
      "10× reduction" reading from sprint 101's measured-on-V64 floor,
      mode1's radius at `n=16384` drops from `9.80e-5` to `≤ 9.80e-6`,
      and at `n=2048` from `7.83e-4` to `≤ 7.83e-5`. The union of all
      seven radii at `n=2048` would then be `≤ 7.83e-5 + 9.34e-7 + ... ≈
      8e-5`, comfortably inside V66's `+1.20e-4` envelope. The wrapper's
      iterative driver will in any case escalate `n_subdivisions` until
      the floor clears.

  (i) **"Is the closure depending on a Mathlib lemma that doesn't
      exist?"** No Lean change is involved. The whole sprint is a
      Numerical_Library python edit (a new private helper plus the
      rewrite of one wrapper's body).

  (j) **"Is the acceptance criterion falsifiable in one Generator
      session?"** Yes. The wrapper rewrite is ~80 lines (mirroring sprint
      099's wrapper). The new helper is ~100 lines (mirroring sprint
      099's mode helper plus the boxA-specific numerator lower bound).
      The falsifiers are: `lake build` of V66 (Lean side byte-preserved,
      trivially passes); evaluator on V66 with `pass: true,
      score: 178281/500000`, `axioms_used` set unchanged; the migrated
      `certify_seven_window_mass_at_356562_sqrt` returns `Fraction(1, 1)`
      and clears the strict-margin floor `1 + 10^(-30)`. All cheap,
      single-shot evaluator/python runs (V66 evaluator was ~3 minutes
      under the existing wrapper; sprint 101 measured `~10s` per
      `certify_two_window_mass_at_35646_sqrt` invocation at `n_sub=2048`,
      and the seven-window wrapper has `~3.5×` the integrand work, so
      `~30–40s` per single invocation; the iterative driver hits the
      cap at most six times for an all-cap upper bound of `~4 minutes`).

This is the cleanest path forward. It closes the second of the four
post-V52 score-push oracles (V64, V66, V67, V68) under the
arb-rigorous template, sets up sprints 103/104 to follow trivially
under the same shape, and brings the credibility-improvement chain
named by Bulletin §B(3) one step closer to completion.

After this sprint:
- The post-V52 score-push trust surface is half-arb-migrated (V64
  and V66 done; V67 and V68 to follow under the same template).
- Sprint 103 can do V67's eight-window oracle (`certify_seven_window_mass_at_356564_modeJ7`)
  reusing both `_branch1_window_mass_lower_arb` (for box0) and
  `_two_window_mass_window_lower_arb` (for the seven mode windows).
- Sprint 104 can do V68's eleven-window oracle (`certify_seven_window_mass_at_356565_modeJ10`)
  reusing the same two helpers (for box0 and the ten mode windows).
- After all four mass oracles are arb-migrated, Bulletin §B(3)'s
  "mp.quad, not interval arithmetic" caveat closes for the entire
  post-V52 score-push chain.

## Concrete edits expected

- **Add** a new private helper `_branch1_window_mass_lower_arb` in
  `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`,
  immediately after `_two_window_mass_window_lower_arb` and before
  `certify_two_window_mass_at_35646_sqrt` (or, equivalently, immediately
  before `certify_seven_window_mass_at_356562_sqrt` — placement is at
  the generator's discretion as long as the helper is accessible to the
  wrapper). Signature:

  ```python
  def _branch1_window_mass_lower_arb(
      c_arb,
      c_pows,
      rho_start,
      rho_stop,
      sqrt_c_arb,
      n_trunc: int,
      n_subdivisions: int,
  ):
  ```

  Body (verbatim shape, modulo cosmetic whitespace and comments):

  ```python
  width = rho_stop - rho_start
  rhos = [rho_start + arb(fmpq(k, n_subdivisions)) * width
          for k in range(n_subdivisions + 1)]
  Ks = [_two_window_mass_paper_K_arb(c_arb, c_pows, r, n_trunc) for r in rhos]
  K_at_sqrt_cache = [None]
  c_6 = c_pows[6]
  total = arb(0)
  for k in range(n_subdivisions):
      rho_lo = rhos[k]
      rho_hi = rhos[k + 1]
      sub_width = rho_hi - rho_lo
      if (rho_hi <= sqrt_c_arb) is True:
          Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
      elif (sqrt_c_arb <= rho_lo) is True:
          Lam_upper = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
      else:
          if K_at_sqrt_cache[0] is None:
              K_at_sqrt_cache[0] = _two_window_mass_paper_K_arb(
                  c_arb, c_pows, sqrt_c_arb, n_trunc)
          Lam_lo = _two_window_mass_paper_lambda_from_K_arb(Ks[k])
          Lam_hi = _two_window_mass_paper_lambda_from_K_arb(Ks[k + 1])
          Lam_sqrt = _two_window_mass_paper_lambda_from_K_arb(
              K_at_sqrt_cache[0])
          Lam_upper = Lam_lo.union(Lam_hi).union(Lam_sqrt)
      # numerator lower bound: 12 ρ³ (ρ²-c²) is increasing on each
      # boxA window since ρ ≥ c·(1+1e-6) > c·sqrt(3/5).
      rho_lo_2 = rho_lo * rho_lo
      rho_lo_3 = rho_lo_2 * rho_lo
      numer_lower = 12 * rho_lo_3 * (rho_lo_2 - c_arb * c_arb)
      integrand_lower = numer_lower / (c_6 * Lam_upper)
      total = total + sub_width * integrand_lower
  return total
  ```

  The helper's docstring should record:
  - the integrand `12 ρ³ (ρ² − c²) / (c⁶ · Λ(c, ρ))`,
  - the numerator-monotonicity argument (numerator derivative
    `12 ρ² (5ρ² − 3c²) > 0` for `ρ > c·sqrt(3/5)`, satisfied by every
    boxA window since `ρ ≥ c · (1 + 10^(-6)) > c · sqrt(3/5)`),
  - the sprint-101 three-branch Λ_upper dispatch,
  - the K-cache structure (mirrors `_two_window_mass_window_lower_arb`),
  - sprint 100's locally-verified per-window radii at
    `n_subdivisions = 2048` (`m_a1 ≈ 3.17e-10, m_a2 ≈ 1.21e-10,
    m_a3 ≈ 4.48e-10`).

- **Rewrite** the body of
  `Numerical_Library/rigorous_scalar.py:certify_seven_window_mass_at_356562_sqrt`
  (currently `mp.quad`-based, lines 1804–1920) into a rigorous
  arb-quadrature lower-bound driver that mirrors sprint 099's wrapper.
  The wrapper signature, name, return type, structural-ordering check
  pattern, and `RuntimeError` message wording are byte-preserved.
  Skeleton (verbatim shape, modulo cosmetic whitespace):

  ```python
  def certify_seven_window_mass_at_356562_sqrt() -> Fraction:
      """
      Sprint 102 migration: mp.quad → flint.arb interval-quadrature
      rigorous lower bound. External contract byte-preserved...
      """
      n_trunc = 300
      dps = 80

      c = Fraction(356562, 1000000)
      rho_top = Fraction(999999, 1000000)
      delta_lo = Fraction(1, 1_000_000)

      if not (Fraction(0) < c < Fraction(1)):
          raise RuntimeError(
              "certify_seven_window_mass_at_356562_sqrt: pinned c is not in (0, 1)."
          )
      if not (rho_top < Fraction(1)):
          raise RuntimeError(
              "certify_seven_window_mass_at_356562_sqrt: pinned ρ_top is not below 1."
          )

      with ctx.workdps(int(dps)):
          c_arb = _arb_exact(c)
          rho_top_arb = _arb_exact(rho_top)
          delta_lo_arb = _arb_exact(delta_lo)

          # Mode-window τ-breakpoint endpoints (sqrt-pinned).
          rho_4_lo = c_arb * arb(fmpq(25, 24)).sqrt()
          rho_3_lo = c_arb * arb(fmpq(16, 15)).sqrt()
          rho_2_lo = c_arb * arb(fmpq(9, 8)).sqrt()
          rho_1_lo = c_arb * arb(fmpq(4, 3)).sqrt()

          # Branch.one fallbackA box-split endpoints.
          fallback_a_lo = c_arb * (1 + delta_lo_arb)
          rho_a1_split = c_arb * arb(fmpq(50, 49)).sqrt()
          rho_a2_split = c_arb * arb(fmpq(36, 35)).sqrt()

          sqrt_c_arb = c_arb.sqrt()

          # Structural ordering checks (rigorous arb comparisons).
          ordering_checks = [
              ("c < fallback_a_lo",            c_arb < fallback_a_lo),
              ("fallback_a_lo < rho_a1_split", fallback_a_lo < rho_a1_split),
              ("rho_a1_split < rho_a2_split",  rho_a1_split < rho_a2_split),
              ("rho_a2_split < rho_4_lo",      rho_a2_split < rho_4_lo),
              ("rho_4_lo < rho_3_lo",          rho_4_lo < rho_3_lo),
              ("rho_3_lo < rho_2_lo",          rho_3_lo < rho_2_lo),
              ("rho_2_lo < rho_1_lo",          rho_2_lo < rho_1_lo),
              ("rho_1_lo < rho_top_arb",       rho_1_lo < rho_top_arb),
          ]
          for name, ok_arb in ordering_checks:
              if not (ok_arb is True):
                  raise RuntimeError(
                      f"certify_seven_window_mass_at_356562_sqrt: "
                      f"structural ordering check '{name}' failed."
                  )

          max_exp = 2 * n_trunc + 3
          c_pows = _pow_cached(c_arb, max_exp)
          floor_arb = arb(1) + arb(fmpq(1, 10)) ** 30

          n_subdivisions = 256
          cap = 16384
          last_total = None
          while True:
              m_a1 = _branch1_window_mass_lower_arb(
                  c_arb, c_pows, fallback_a_lo, rho_a1_split,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_a2 = _branch1_window_mass_lower_arb(
                  c_arb, c_pows, rho_a1_split, rho_a2_split,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_a3 = _branch1_window_mass_lower_arb(
                  c_arb, c_pows, rho_a2_split, rho_4_lo,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_4 = _two_window_mass_window_lower_arb(
                  c_arb, c_pows, 4, rho_4_lo, rho_3_lo,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_3 = _two_window_mass_window_lower_arb(
                  c_arb, c_pows, 3, rho_3_lo, rho_2_lo,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_2 = _two_window_mass_window_lower_arb(
                  c_arb, c_pows, 2, rho_2_lo, rho_1_lo,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              m_1 = _two_window_mass_window_lower_arb(
                  c_arb, c_pows, 1, rho_1_lo, rho_top_arb,
                  sqrt_c_arb, n_trunc, n_subdivisions)
              total_lower = m_a1 + m_a2 + m_a3 + m_4 + m_3 + m_2 + m_1
              last_total = total_lower
              if (total_lower > floor_arb) is True:
                  return Fraction(1, 1)
              if n_subdivisions >= cap:
                  break
              n_subdivisions *= 2

          raise RuntimeError(
              "certify_seven_window_mass_at_356562_sqrt: rigorous arb lower "
              f"bound on joint mass = {last_total} (margin = "
              f"{last_total - arb(1)}) failed to clear strict-margin floor "
              f"1 + 10^(-30) at n_subdivisions = {n_subdivisions} "
              f"(cap = {cap}); refusing to certify Lean axiom "
              "`h_seven_window_mass_certified_at_356562_sqrt`."
          )
  ```

  The wrapper docstring should record the migration (mp.quad → arb),
  cite sprint 099 as the V64 template, cite sprint 100's BLOCKED
  diagnosis and sprint 101's helper fix as the unblocking
  mechanism, and document the n_subdivisions cap and per-window radii
  expectations. The mp.quad → arb shift, like sprint 099, **does not
  change** the candidate-side `axiom h_seven_window_mass_certified_at_356562_sqrt`
  declaration or the Lean axiom statement; the wrapper's external
  contract (zero-arg, returns `Fraction(1, 1)`, raises on rejection)
  is preserved.

- **Preserve** the legacy `mp.quad`-based helpers
  (`_two_window_mass_paper_factor`, `_two_window_mass_paper_lambda`,
  `_two_window_mass_term_j`, `_two_window_mass_window`,
  `_branch1_window_mass`, `certify_two_window_mass`,
  `certify_two_window_mass_at_35646`) byte-identically — they are still
  consumed by V65's rational-endpoint sibling and by V67/V68's
  eight/eleven-window oracles which are not yet migrated. Do **not**
  delete the legacy helpers.

- **No edits** to:
  - `lemma.toml`: the `[[oracles]]` entry at line 537–540 already points
    to `rigorous_scalar.certify_seven_window_mass_at_356562_sqrt`; the
    wrapper rewrite is internal to that function's body. Byte-preserved.
  - `Candidates/V66.lean`: the candidate-side `axiom
    h_seven_window_mass_certified_at_356562_sqrt` and its use site at
    line 327 (`exact h_seven_window_mass_certified_at_356562_sqrt K`)
    are byte-preserved. The Lean statement of the axiom is unchanged.
  - `Candidates/V64.lean`, `Candidates/V65.lean`, `Candidates/V67.lean`,
    `Candidates/V68.lean`: byte-preserved. V64 was migrated by sprint
    099; V65/V67/V68 have their own (still-`mp.quad`) wrappers untouched.
  - `KorenblumPaper/`: read-only.
  - `Proof/`: unchanged.
  - `Numerical_Library/types.py`, `Numerical_Library/numerical_audit.py`:
    no schema changes.

- **Add** a Phase 0 sanity script at
  `Scratch/sprint_102_arb_seven_window_mass_witness.py`: a standalone
  python script that calls the migrated wrapper end-to-end once, then
  re-runs the underlying arb computation standalone for
  `n_subdivisions ∈ {256, 512, 1024, 2048}` and prints, at each level:

  - per-window arb radii `m_a1.rad, m_a2.rad, m_a3.rad, m_4.rad, m_3.rad,
    m_2.rad, m_1.rad`,
  - per-window arb midpoints,
  - the rigorous total margin lower endpoint,
  - whether the strict-margin floor `1 + 10^(-30)` is cleared at each
    level.

  The script imports `_branch1_window_mass_lower_arb`,
  `_two_window_mass_window_lower_arb`, `_arb_exact`, `_pow_cached` from
  `Numerical_Library.rigorous_scalar` and the same `flint` API as
  `Scratch/sprint_101_monotonic_lambda_witness.py`. The script is
  permitted to print sprint-100's reference table as a side-by-side
  baseline, but should not depend on the existence of any other Scratch
  file.

  Acceptance: the witness script prints non-error output, reports
  `m_1.rad` at `n_subdivisions = 16384` strictly less than
  `9.80e-5` (sprint 100's BLOCKED reading at the same n_subdivisions),
  and either reports `total_lower > 1 + 10^(-30)` at some
  `n_subdivisions ≤ 16384` or terminates with a precise margin-shortfall
  measurement.

- **Re-evaluate V66** by running
  `bash scripts/korenblum_eval_candidate.sh Candidates/V66.lean`
  and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds
    (Lean side byte-preserved).
  - Evaluator returns `pass: true`, `score: 178281/500000` (the
    V66 score, byte-preserved).
  - `axioms_used` set is **identical** (set-theoretically) to V66's
    pre-sprint evaluator log entry's `axioms_used` set: exactly the
    six entries
    - `propext`,
    - `Classical.choice`,
    - `Quot.sound`,
    - `ProofRefinement.Korenblum.h_seven_window_mass_certified_at_356562_sqrt`,
    - `ProofRefinement.Korenblum.Candidates.V66.hH2_v66`,
    - `ProofRefinement.Korenblum.Candidates.V66.hCircleGapInt_v66`.
  - `oracle_checks` table records exactly one entry with
    `axiom = h_seven_window_mass_certified_at_356562_sqrt`,
    `bound_field = seven_window_mass_lower`, `oracle_bound = 1`,
    `declared = 1`, `ok = true`.

- **Re-evaluate V64 and V68** as regression-falsifiers (V64 because
  sprint 099/101 migrated its helper, and any side-effect on the
  helper would be caught here; V68 because it is the live frontier and
  uses a different oracle wrapper, but sits in the same source file
  and a typo or import collapse could break it). The expected outcomes:

  - V64 evaluator: `pass: true`, `score: 17823/50000`, `axioms_used`
    set unchanged (six entries, byte-identical to sprint 101 verdict).
  - V68 evaluator: `pass: true`, `score: 71313/200000`, `axioms_used`
    set unchanged (six entries, byte-identical to sprint 101 verdict).

- **Append** to `Experience.md` a "Sprint 102 — `mp.quad → arb`
  migration of V66's seven-window joint-mass oracle" subsection
  summarizing:
  - the new helper `_branch1_window_mass_lower_arb` (signature, shape,
    numerator-monotonicity argument),
  - the wrapper rewrite (mp.quad → arb iterative driver, parallel to
    sprint 099),
  - the per-window radii table at `n_subdivisions ∈ {256, 512, 1024,
    2048, ..., cap-at-which-floor-cleared}`,
  - the V66/V64/V68 re-evaluation results,
  - the forward implication for sprint 103 (V67 eight-window oracle
    migration follows under the same template; reuses both
    `_branch1_window_mass_lower_arb` and `_two_window_mass_window_lower_arb`).

- **Append** to `Bulletin.md` one row
  `sprint_102 PASS|FAIL: <title>` per the standard pattern.

No edits to:
- `KorenblumPaper/` (read-only).
- `Proposals/` (no proposal filed — this is a Numerical_Library
  algorithmic-rewrite of an existing wrapper's body, preserving the
  external contract conjunct-for-conjunct).
- The mathematical content of any candidate.
- Any candidate-side `axiom` declaration.
- The `[seed_axioms]`, `[[oracles]]`, `[import_policy]`, or
  `[workspace_import_policy]` blocks of `lemma.toml`.
- `Proof/Summability.lean`, `Proof/Integrability.lean`,
  `Proof/DiskInnerSeriesBridge.lean`, `Proof/Reduction.lean`,
  `Proof/Main.lean`, `Proof/CandidateContract.lean`.

## Acceptance criteria

1. The migrated `certify_seven_window_mass_at_356562_sqrt`, called
   standalone (e.g.
   `python -c "from Numerical_Library.rigorous_scalar import
   certify_seven_window_mass_at_356562_sqrt;
   print(certify_seven_window_mass_at_356562_sqrt())"`), returns
   `Fraction(1, 1)` and does not raise.

2. `grep -n 'mp\.quad' ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
   reports **no** matches inside the body of
   `certify_seven_window_mass_at_356562_sqrt` (the legacy mp.quad
   helpers `_branch1_window_mass`, `_two_window_mass_window`, and the
   legacy `certify_two_window_mass*` and `certify_seven_window_mass_at_35656{4,5}*`
   wrappers continue to use mp.quad — out of scope for this sprint).

3. The new private helper `_branch1_window_mass_lower_arb` exists in
   `Numerical_Library/rigorous_scalar.py` with the signature
   `(c_arb, c_pows, rho_start, rho_stop, sqrt_c_arb, n_trunc: int,
   n_subdivisions: int) -> arb` and a body matching the skeleton
   above (modulo cosmetic whitespace and comments).

4. `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds
   (warnings only).

5. `lake build ProofRefinement.Korenblum.Candidates.V64` succeeds
   (warnings only).

6. `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds
   (warnings only).

7. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V66.lean` succeeds with
   `pass: true` and `score: "178281/500000"` (V66's pre-sprint
   score, byte-preserved).

8. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V64.lean` succeeds with
   `pass: true` and `score: "17823/50000"` (= `35646/100000`,
   byte-preserved from sprint 101 verdict).

9. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (V68's score,
   byte-preserved).

10. The post-sprint V66 evaluator log entry's `axioms_used` set
    is **identical** (set-theoretically, comparing the `name`
    field of each entry) to V66's pre-sprint log entry's
    `axioms_used` set: exactly the six entries listed under
    "Re-evaluate V66" above. No new axioms introduced. No old
    axioms removed.

11. The post-sprint V66 evaluator log entry's `oracle_checks`
    table contains exactly one entry with
    `axiom = "h_seven_window_mass_certified_at_356562_sqrt"`,
    `bound_field = "seven_window_mass_lower"`,
    `oracle_bound = "1"`, `declared = "1"`, `ok = true`.

12. The Phase 0 sanity script
    `Scratch/sprint_102_arb_seven_window_mass_witness.py` reports
    per-window radii `m_a1.rad, m_a2.rad, m_a3.rad, m_4.rad,
    m_3.rad, m_2.rad, m_1.rad` and the rigorous total margin
    lower endpoint at `n_subdivisions ∈ {256, 512, 1024, 2048}`
    plus the n_subdivisions level at which the floor is first
    cleared. The witness must show:
    - `m_1.rad` at `n_subdivisions = 2048` is at least one order
      of magnitude smaller than sprint 100's BLOCKED reading at
      the same n_subdivisions (`7.83e-04`); i.e. the new helper's
      m_1 radius at n=2048 is `< 7.83e-05`,
    - the rigorous total margin lower endpoint at the
      first-clearing `n_subdivisions` (in `{256, 512, 1024, 2048,
      ..., 16384}`) is **strictly greater than** `10^(-30)`.

13. The migrated wrapper completes within **~5 minutes** on a
    single end-to-end invocation. (Sprint 099's V64 wrapper:
    ~10s at `n_sub=2048`. The seven-window wrapper has ~3.5×
    integrand work; expected single-invocation time at
    `n_sub=2048` is ~30–40s. The iterative driver hits the cap at
    most six times, all-cap upper bound ~4 minutes.)

14. `Experience.md` and `Bulletin.md` each gain one row per the
    standard pattern.

The sprint is **PASS** if all 14 criteria are met. The sprint is
**FAIL** if V66's evaluator score changes, the `axioms_used`
set diverges, V64 or V68 regresses, the migrated wrapper raises
`RuntimeError` (i.e. the arb-rigorous bound fails to clear the
floor at the cap), or the wrapper exceeds the 5-minute time
ceiling.

The sprint is **BLOCKED** if the wrapper raises `RuntimeError`
even at `n_subdivisions = 16384` despite sprint 101's tightening
(this would indicate the centered margin `+1.20e-4` is genuinely
tighter than the new helper can achieve at the cap; the
generator must record the per-window radii and total enclosure
in `Scratch/sprint_102_obstruction.md` and exit with
`STATUS=BLOCKED`). In that case the next planner can either
raise the cap to 32768 or 65536 (the remaining brute-force
option from sprint 100's table) or further tighten the helper.

## Out of scope

- **Re-attempt V67's eight-window oracle migration**
  (`certify_seven_window_mass_at_356564_modeJ7`). Sprint 103.

- **Re-attempt V68's eleven-window oracle migration**
  (`certify_seven_window_mass_at_356565_modeJ10`). Sprint 104.

- **Migrate V65's `certify_two_window_mass_at_35646`** (the
  rational-endpoint sibling of sprint 099's wrapper). Independent
  follow-up sprint.

- **Migrate any of the `certify_eq15_at_*` family** (5 wrappers:
  seed, 3560, 3562, hp_3564, hp_35645). Independent follow-up.

- **Edit the helper to use a different precision strategy** (e.g.
  raise `dps`, raise `n_trunc`, raise `n_subdivisions` cap). The
  current strategy at `dps = 80` and `n_trunc = 300` is preserved;
  only the wrapper body and the new `_branch1_window_mass_lower_arb`
  helper are added.

- **Edit `Candidates/V66.lean`, `Candidates/V64.lean`,
  `Candidates/V65.lean`, `Candidates/V67.lean`,
  `Candidates/V68.lean`, or any other Lean file**. The migration is
  a Python-side internal change; the candidate-side `axiom`
  declarations and their usages are byte-preserved.

- **Edit the `[[oracles]]` registration in `lemma.toml`**. The
  `oracle_fn` continues to point at the same wrapper name; the
  candidate axiom name is unchanged; the bound field is unchanged.

- **Add or remove free axioms**. The migration preserves the trust
  surface conjunct-for-conjunct.

- **Delete the legacy mp.quad-based helpers**
  (`_two_window_mass_paper_factor`, `_two_window_mass_paper_lambda`,
  `_two_window_mass_term_j`, `_two_window_mass_window`,
  `_branch1_window_mass`). They remain consumed by V65's wrapper
  and by V67/V68's wrappers. Cleanup of unused legacy helpers is
  deferred to after V67/V68 migrations (sprints 103/104).

- **File a `Proposals/` entry**. The change is a Numerical_Library
  algorithmic refinement that preserves the wrapper's external
  contract byte-for-byte. Per AGENT_BRIEF lines 80–86 (oracle-shaped
  additions/edits can be done inline as long as the contract names
  the wrapper, the lemma.toml entry, and the use site), this is an
  inline edit to an existing wrapper's internals.

- **Change the final theorem statement of any candidate**.

- **Hoist `Candidates/V66/Branch1Integrability.lean` to `Proof/`**.
  Demoted by sprints 097/098/099/101.

- **Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`**. No
  current consumer.

- **Push past V68's `c = 71313/200000`**. The score-push surface at
  the existing trust surface remains exhausted. After this sprint,
  the live frontier remains V68 at `71313/200000`.

- **Discharge `hH2_v6×` or `hCircleGapInt_v6×`** from
  `Section2Assumptions` (Slack 4 / Bulletin §B(4)). Out of scope.

## Time budget

≤ 75 minutes wall-clock:
  - New helper `_branch1_window_mass_lower_arb`: ~10 minutes (~100
    lines mirroring `_two_window_mass_window_lower_arb` with the
    boxA-specific numerator lower bound).
  - Wrapper body rewrite (mp.quad → arb iterative driver): ~10
    minutes (~100 lines mirroring sprint 099's V64 wrapper).
  - Migrated-wrapper standalone end-to-end invocation: ~30–60s at
    the floor-clearing `n_subdivisions` (predicted at `n=2048` per
    sprint 100's diagnostic + sprint 101's ≥10× tightening).
  - V66 evaluator: ~3 minutes (typecheck + axiom scan + oracle
    invocation; oracle invocation is the migrated wrapper above).
  - V64 evaluator: ~3 minutes (regression-falsifier).
  - V68 evaluator: ~3 minutes (regression-falsifier).
  - Phase 0 sanity script: ~1–2 minutes (single sweep over
    `n_subdivisions ∈ {256, 512, 1024, 2048}` with seven-window
    integrand work per call).
  - Witness updates to `Experience.md`, `Bulletin.md`: ~10 minutes.

≤ 1 generator session (~1.5–2 hours including: the new helper
(~100 lines), the wrapper rewrite (~100 lines), the Phase 0 sanity
script (~120 lines including the per-window table formatting), the
three evaluator runs (~9 minutes total wall-clock), and the witness
updates).

## Stop conditions

- All 14 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- The migrated wrapper raises `RuntimeError` because the rigorous
  arb-lower bound fails to clear `1 + 10^(-30)` even at
  `n_subdivisions = 16384`: `STATUS=BLOCKED` with the per-window
  radii table and the arb-enclosure of the failing margin recorded
  in `Scratch/sprint_102_obstruction.md`. Most likely cause: V66's
  centered margin `+1.20e-4` is too tight to fit the seven-window
  union of arb radii at the cap, **even after sprint 101's
  tightening** — would warrant either a cap raise (sprint 103
  candidate) or a further helper tightening (e.g. switch to a
  trapezoidal lower bound or a midpoint-corrected Riemann lower
  bound).

- V66's evaluator score changes from `178281/500000` after the
  migration: `STATUS=BLOCKED` with the diff in `axioms_used` and
  the new score. Most likely cause: an accidental edit to V66's
  body or to `lemma.toml`'s oracle entry. The migration is
  intended to be Lean-side and lemma.toml-side byte-preserving.

- V64 or V68's evaluator score changes from
  `17823/50000` / `71313/200000` after the migration: same
  `STATUS=BLOCKED`. Most likely cause: an accidental side-effect
  of the rigorous_scalar.py edit on a shared helper or import.

- The `axioms_used` set diverges from V66's pre-sprint set:
  `STATUS=BLOCKED` with the set-difference. The edit must be
  audit-envelope-preserving by construction.

- The Phase 0 sanity script reports `m_1.rad` at
  `n_subdivisions = 2048` that is **not** at least one order of
  magnitude smaller than sprint 100's reading (`7.83e-04`):
  `STATUS=BLOCKED` with the per-window radii table. Most likely
  cause: the wrapper is calling the wrong helper (e.g.
  `_two_window_mass_paper_lambda_arb` instead of
  `_two_window_mass_window_lower_arb`), or the new helper is
  incorrectly wired (e.g. `c_pows` not threaded, or
  `sqrt_c_arb` shadowed).

- A `flint`/`arb` API surface used by the new helper turns out to
  be unavailable in the current `flint` version pinned by
  `pyproject.toml`/`uv.lock`: `STATUS=BLOCKED_NEEDS_HUMAN`. Note:
  this should not occur — the helper reuses `arb`, `arb.sqrt()`,
  `arb.union()`, `(... <= ...) is True` semantics that are all
  exercised by sprints 099/101, plus `arb.__pow__(int)`,
  `arb.__mul__`, `arb.__sub__` arithmetic that is standard.

- Trust expansion needed (the wrapper rewrite unexpectedly
  requires a new `Numerical_Library` library or a new
  `lemma.toml` entry): `STATUS=BLOCKED_NEEDS_HUMAN`. Note: this
  should not occur — the rewrite reuses existing helpers (now
  including sprint 099's mode helper and sprint 101's monotonicity
  dispatch) and existing arb arithmetic exclusively.
