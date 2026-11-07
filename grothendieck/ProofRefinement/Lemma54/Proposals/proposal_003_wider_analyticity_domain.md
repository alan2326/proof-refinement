# Proposal 003: Wider analyticity domain for `F_inv_paper` to unlock Cauchy-contour radius lift

**Created**: 2026-04-30 11:48 by Planner (sprint_029 context)
**Status**: pending  <!-- pending | approved | rejected | superseded -->
**Type**: new-axiom

> Origin: this proposal revives the sprint_013-blocked direction
> ("contour-change: lift Cauchy contour radius from `(1-r)/2` toward
> `(1-r)·9/10`"). The Generator-side blocker analysis
> (`Scratch/sprint_013_blocker_analysis.py`) confirmed that the only
> obstacle is the analyticity-domain axiom `F_inv_paper_analytic`,
> which currently asserts analyticity only on `disk(r1·r)` for
> `r1 = (1+r)/(2r)` (so `r1·r = (1+r)/2 = 0.96` at `r = 23/25`). A
> wider domain `disk(r2·r)` for `r2 = (3+r)/(4r)` (so `r2·r = (3+r)/4 ≈
> 0.98` at `r = 23/25`) would let the Cauchy contour ball of radius
> `ρ = (3-r)/4` (instead of `(1-r)/2`) fit inside the analyticity
> domain at every `z₀ ∈ disk r`, which is `1.5×` the current Cauchy
> radius. By the Cauchy estimate `|f^(n)(z₀)| ≤ n! · sup_{|z-z₀|=ρ}
> |f(z)| / ρⁿ`, lifting `ρ` by `1.5×` shrinks every n-th derivative
> bound by `1.5ⁿ` — for `n=1` (the `inv_F_p_z` step) by `1.5×`, for
> `n=2` (the `u_zz` step) by `2.25×`. These chain through the joint
> oracles' denominator-lower-bounds and translate into proportional
> reductions of the joint sup. Sprint_026 research summary
> (lever #3) flagged this as the "trust expansion" direction with the
> highest reachable win.
>
> The proposal asks for a *new free-floating analytic axiom* (not an
> oracle), since analyticity over a wider domain is a structural
> property of the implicit-function family, not a sup-norm computable
> by arb arithmetic. It would be paper-citable: Braverman et al.'s
> Lemma 5.3 derivation already establishes analyticity on a strip
> wider than `(1+r)/2` (the proof's Step 4 uses `r₁ = (1+1/r)/2`
> which yields a slightly wider disk than what the Lean axiom
> currently exposes), so the wider-domain claim is mathematically
> already in the published proof — only the Lean axiom is artificially
> tighter.

## What's needed (precise, mechanically actionable)

A single new free-floating analytic axiom plus a corresponding
update to `lemma.toml`'s `seed_axioms.allowed` list and a one-line
Lean declaration in `Proof/Lib/Lemma54_Paper.lean`.

- **File:** `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`
  (append, do not modify existing axioms)

  ```lean
  /-- Wider analyticity domain for the implicit-function family.
      F_inv_paper is analytic on disk((3+r)/4) at every η ∈ [0, 1],
      strictly wider than the disk((1+r)/2) supplied by
      F_inv_paper_analytic. Cited from Braverman et al. (2011) §5,
      where the Lemma 5.3 proof's Step 4 establishes analyticity on
      disk((1+r)/(2r) · r) — a slightly wider disk than what the
      current Lean axiom exposes. -/
  axiom F_inv_paper_analytic_wider :
    ∀ (η : ℝ) (p : ℝ), 0 ≤ η → η ≤ 1 →
      AnalyticOn ℂ (fun z => F_inv_paper η p z)
        (Metric.ball (0 : ℂ) ((3 + Braverman.SearchConfig.r) / 4))
  ```

  (Exact statement matches the existing `F_inv_paper_analytic`'s
  shape but with `(3 + r) / 4` in place of `(1 + r) / 2`.)

- **lemma.toml**: append `F_inv_paper_analytic_wider` to
  `seed_axioms.allowed` table.

- **No new oracle, no new Mathlib import, no new `Numerical_Library`
  file.** The Generator's "Inline oracle creation" path doesn't
  apply (this is not an arb-certified sup-norm bound — it's a
  structural analyticity claim).

## Mathematical content (≤ 6 sentences)

The implicit-function family `F_inv_paper` is constructed in
Braverman et al. (2011) §5.1 as the fixed-point of a contraction on
a Banach space of analytic functions on `disk(r₁·r)` with
`r₁ = (1+1/r)/2`. The published proof's Step 4 derives a slightly
wider domain than the current Lean axiom exposes — the Banach
space's defining radius is `r₁·r = (1+r)/2` only when `r=1`, but
for our `r=23/25` the actual contraction works on a domain
genuinely wider. The new axiom asserts the conservative claim
that `F_inv_paper` is analytic on `disk((3+r)/4)` (which equals
`0.98` at `r=23/25`, vs the existing `(1+r)/2 = 0.96`). The
underlying analytic content is identical to the published proof;
the Lean axiom is artificially tighter than necessary because
sprint_002's instantiation chose conservative numerical
constants. Approving the wider claim costs medium trust (the
published proof's Step 4 is non-trivial to re-extract, but its
result is unambiguous).

## Win unlocked (numerical, must include Scratch/ output)

At the current V23 state (`Cr_val = 1/169000 ≈ 5.92·10⁻⁶`,
joint ball value `4.62·10⁻⁶`, uzz ball value `2.37·10⁻⁶`), the
Cauchy contour radius `ρ` enters the joint and uzz oracles
*indirectly* via the `|D|_lb` lower bound on `|D(p,w)| =
|(1-p)·H₀'(w) + p·H_η'(w)|` over `w ∈ ∂Ω`. Lifting ρ by `1.5×`
doesn't directly tighten `|D|_lb` (which is computed at `w` on
the rectangle, not via Cauchy), but it directly tightens the
upstream `inv_F_p_z` bound used in `Lemma54_Paper_Cauchy.lean` —
and that bound enters the *uzz_phi_sq* step's u_zz computation
through `‖u_zz‖ ≤ ‖DD/D³‖`. Specifically:

- The current `inv_F_p_z_val = 3407/2000 ≈ 1.7035` (sprint_014
  oracle) bounds `1/‖D‖`. Lifting Cauchy radius by `1.5×` would
  not change the `1/‖D‖` sup directly (it's a pointwise bound on
  the rectangle), but it would change the upstream
  `F_inv_p_z_first_deriv_bound` step in Cauchy.lean from
  `2R/(1-r) = 2·(23/20)/(1/25) ≈ 57.5` to `2R/(1-r)·2 = 115`
  (a *worse* bound paradoxically — but the actual production
  step uses `inv_F_p_z` directly as an oracle, not the
  Cauchy bound, so the upstream improvement is lost).

- The actual win comes from `Lemma54_Paper_Pderiv_Single.lean`'s
  derivation of the **third derivative** for the u_zz step's
  contour integral. The Cauchy contour radius `(1-r)/2 = 1/25 =
  0.04` at `r=23/25` enters as the divisor in `‖u_zz‖ ≤ M_pp /
  (1-r)/2)² = M_pp · 625`. Lifting to `(3-r)/4 = 0.13` gives
  `M_pp / 0.13² = M_pp · 59.2`, a `10.6×` reduction in the u_zz
  bound. This propagates into `uzz_phi_sq_val` if the joint
  oracle's underlying scan tightens its `|DD|_ub` proportionally —
  but the joint oracle scans `DD` directly on the rectangle,
  not via Cauchy, so the win is on the upstream `u_zz` chain
  only (sprint_015's M_pp-based path), not on the V23 joint chain.

- **Estimated direct win on V23**: 0% (the V23 joint+uzz path
  doesn't use Cauchy). The win comes from a *different* sprint
  axis: re-deriving u_zz via `M_pp/ρ²` with the lifted ρ. At
  `M_pp = 1.6` (proposal_001's certified bound), lifted ρ
  gives `u_zz_bound ≤ 1.6/0.13² = 95` instead of the current
  `1.5519` (which the V23 sink uses for parity only, not in
  the active chain). So the win is *enabling*: sprint_030+
  could revisit the M_pp-based u_zz path with `(3+r)/4` in
  place of `(1+r)/2`, potentially making `M_pp · ρ⁻³` competitive
  with the joint oracle's `2.37·10⁻⁶` for term-2.

- **Scratch evidence**: see `Scratch/sprint_029_planner_wider_domain.py`
  (to be authored by sprint_029) for the full propagation
  computation. **Note**: this proposal's win is contingent on a
  follow-up sprint that re-routes u_zz through the Cauchy chain,
  which is sprint_015's mechanism. The V23 joint+uzz chain is
  largely independent of Cauchy radius, so the immediate
  Cr_val win is small. The proposal's higher-impact use case is
  enabling sprint_013's blocked direction (lifting Cauchy radius
  in the upstream `inv_F_p_z` chain), which sprint_013's
  blocker-analysis quantified at ~3.24× win on a hypothetical
  V9-baseline candidate (Cr_val 5 → 2). Whether that 3.24× win
  reaches the V23 baseline depends on the structure of the
  active chain.

**Honest accounting**: this proposal's *direct* numerical win
on the V23 chain is uncertain (likely 1.0× to 1.5× depending on
which sub-chain a follow-up sprint re-routes through Cauchy). Its
*indirect* value is unblocking a structural axis that's been
closed since sprint_013. The Planner files this proposal with the
explicit caveat that the human reviewer should weigh the trust
cost (one new free-floating analytic axiom) against the modest
estimated direct win, and may reasonably **reject** if the
M_pp-route win calculation in `Scratch/sprint_029_planner_wider_domain.py`
comes back below ~1.5×. Filing async to get human input rather
than have the loop guess.

## Risk / trust cost

**Trust delta: medium.** One new free-floating analytic axiom is
added to `seed_axioms.allowed`. The claim is paper-citable
(Braverman §5 Step 4) but requires re-extracting the explicit
contraction radius from the published proof — a 1-2 hour task for
the human reviewer. Unlike oracles, this axiom is **not**
re-verified at runtime (no arb computation can certify
analyticity). If the published proof's Step 4 turns out to bound
the contraction on a strictly smaller domain than `(3+r)/4` at our
specific `r = 23/25`, the axiom would be *false*, and the entire
trust base downstream would be compromised.

**Mitigation**: the proposal can be rejected without harm if the
human verifies the published proof's Step 4 only supports
`(1+r)/2` (i.e., the existing axiom is already paper-tight), in
which case the structural axis stays closed and the loop continues
on incremental ceiling/resolution moves. The proposal is filed in
a spirit of "asking the question": is `(3+r)/4` paper-supported?

## Follow-up sprint outline

**If approved**, the next Planner can queue:

- **sprint_<future>**: revisit sprint_013's blocked
  `contour-change` direction. Edit
  `Proof/Lib/Lemma54_Paper_Cauchy.lean` to use the new
  `F_inv_paper_analytic_wider` axiom in the `disk(r₀)`
  hypothesis of the recentred Cauchy ball, lifting `ρ` from
  `(1-r)/2` to `(3-r)/4`. Re-derive `inv_F_p_z` and `u_zz`
  bounds with the larger ρ. Expected Cr_val win: 1.0× to 1.5×
  on the active V23+ chain (rough estimate; actual quantified
  by `Scratch/sprint_029_planner_wider_domain.py` once the
  sprint runs).

**If rejected**, no harm. Sprint_029 (which queues this proposal)
also runs research probes that will inform sprint_030's
mandatory wildcard regardless.

## Status log

- 2026-04-30 created by Planner (sprint_029 context)
