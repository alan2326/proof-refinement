# Proposal 001: Cr_refined via three new η-aware oracles (M_diff, M_diffp, M_pp)

**Created**: 2026-04-30 (filed by harness operator from Planner's prior sprint_010 analysis)
**Status**: approved
**Type**: new-oracle

> Origin: this proposal was distilled from `Scratch/sprint_010_planner_explore.py`
> (the Planner's exploration that informed the now-cancelled sprint_010
> axiom-prove draft). The Planner identified Cr_refined as the
> highest-value direction available, but the harness's no-new-axioms
> rule forbade the Planner from queueing it. Under the new proposal
> mechanism (Proposals/README.md), this is the right form for the
> request.

## What's needed (precise, mechanically actionable)

Three new certified-arb oracle functions plus their `[[oracles]]`
entries and supporting axiom declarations.

- **`Numerical_Library/m_diff.py`** — `compute_M_diff(δ, B, …) -> OracleResult`
  certifying `M_diff = sup_{z ∈ Ω(δ,B)} ‖∂_η F(η, p, z)‖` (the
  η-derivative of the joint family at `p = 0`, evaluated on the Step-2
  rectangle).
- **`Numerical_Library/m_diffp.py`** — `compute_M_diffp(δ, B, …) -> OracleResult`
  certifying `M_diffp = sup_{|p|≤r₁, z∈Ω(δ,B)} ‖∂_η ∂_p F(η, p, z)‖`.
- **`Numerical_Library/m_pp.py`** — `compute_M_pp(δ, B, …) -> OracleResult`
  certifying `M_pp = sup_{|p|≤r₁, z∈Ω(δ,B)} ‖∂²_p F(η, p, z)‖`
  (this *replaces* the M-via-Cauchy chain by giving a direct sup
  bound on the second p-derivative).

Three corresponding `[[oracles]]` entries in
`ProofRefinement/Lemma54/lemma.toml`:

```toml
[[oracles]]
short = "h_M_diff_oracle"
axiom_fq = "Braverman.PaperV0.h_M_diff_oracle"
bound_field = "M_diff_val"
oracle_fn = "compute_M_diff"

[[oracles]]
short = "h_M_diffp_oracle"
axiom_fq = "Braverman.PaperV0.h_M_diffp_oracle"
bound_field = "M_diffp_val"
oracle_fn = "compute_M_diffp"

[[oracles]]
short = "h_M_pp_oracle"
axiom_fq = "Braverman.PaperV0.h_M_pp_oracle"
bound_field = "M_pp_val"
oracle_fn = "compute_M_pp"
```

Three axiom declarations in `Proof/Lib/Lemma54_Paper.lean` (signatures
to be specified precisely in a follow-up: the Planner will draft them
in Scratch/ once the proposal is approved, so the human only needs to
agree to the *shape* of the trust expansion now).

## Mathematical content (≤ 6 sentences)

`Cr_refined` is an η²-scaled refinement of `Cr_paper` derivable from
the joint Taylor expansion of `F` in `(η, p)` at `(η_val, 0)`. The
paper's Step-5 derivation of `Cr_paper` uses only worst-case bounds
on `‖∂²_p F⁻¹‖` via the Cauchy-on-disk-r₁ chain
`‖∂²_p F⁻¹‖ ≤ 2 sup‖F⁻¹‖ / r₁²` and then re-expresses this in terms
of `M = sup‖F‖` and `R = sinh r₂`. The η-aware refinement, in
contrast, separates the contributions: at `η = 1/100`, the leading
behaviour of `‖∂²_p F⁻¹‖` is `O(η²)` because the family deforms
smoothly from `H_0` (where the second-p-derivative of the inverse
vanishes by direct calculation), and the η²-coefficient itself is
bounded by an expression involving `M_diff`, `M_diffp`, and `M_pp`
that admits direct certified-arb evaluation on `Ω(δ, B)`.
Concretely, Cr_refined ≈ `8 (M_diff² · M_pp + 2 M_diff · M_diffp · R + M_diffp² · R²) η² / (1-r)²` (factorization to be confirmed by a careful Step-5 re-derivation when the Planner queues the formula-change sprint).

## Win unlocked (numerical, must include Scratch/ output)

From sprint_010's Planner analysis:

> "(a) Cr_refined (η²-scaled) would shrink Cr_val from 1.132·10⁹
> to ≈ 9.2·10⁷ (12.2× reduction) but requires NEW oracles for
> M_diff/M_diffp/M_pp, FORBIDDEN by the harness's 'no new axioms'
> rule"

Concretely: at the current state (V7's `Cr_val = 1132310000`),
approving this proposal and queueing the follow-up sprint
"replace `Cr_tight` with `Cr_refined` consuming the three new
oracles" would drop `Cr_val` to ≈ `9.2·10⁷` — the **largest
single-sprint win available** in the current regime. The
12.2× factor is dimensionally η² · (loss-factor between
worst-case Cauchy and direct sup), with η = 1/100 supplying
the dominant 10⁴ factor, partially offset by the constant bloat
of three sup-bounds combined.

Re-running the Planner's Scratch script under the proposal-approved
state should produce a sharper number; the 12.2× figure is the
order-of-magnitude commitment.

## Risk / trust cost

Three new certified-arb oracles. **Trust cost: low** — each oracle
is a numerical bound certified on demand by the runner using
`compute_M_rigorous`-style arb pipelines (the same pattern as the
existing `compute_M_bound_tight`). No new mathematical-content
axioms; the underlying claims are *that the supremum of an explicit
analytic expression on an explicit rectangle is bounded by a
certain rational*, which arb can certify mechanically.

The supporting axioms in `Proof/Lib/Lemma54_Paper.lean` are oracle-
witnessed (same pattern as `h_M_oracle`), not free-floating
analytic axioms; they're equivalent in trust-status to the existing
M-oracle.

The genuine cost is **engineering effort**: writing three new
arb-certified bound functions, each requiring careful contour /
parameterization design, is roughly the same labor as the original
`compute_M_rigorous` (multi-day work, not multi-hour). If the
human wants a smaller-step proposal, an interim version with
just `M_pp` (replacing the Cauchy step alone, leaving the M·R
factorization in place) might be a more tractable start; that
variant would be filed as a separate proposal.

## Follow-up sprint outline

If approved, the first sprint would:

1. Define `Cr_refined (r M_diff M_diffp M_pp R η : ℝ) : ℝ := …`
   in `Proof/Lib/Lemma54_Paper.lean`, mirroring the structure of
   `Cr_tight` but consuming the three new oracle bounds.
2. Add `theorem F_inv_p_second_deriv_bound_refined` in
   `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`, proven from the
   three new axioms via the η-Taylor expansion.
3. Add `theorem lemma_5_4_paper_on_domain_refined` in
   `Proof/Lib/Lemma54_Paper_Main.lean`.
4. Create `Candidates/V8.lean` (parent V7) using `Cr_refined` with
   `M_diff_val`, `M_diffp_val`, `M_pp_val` set to the integer
   ceilings of the three new oracles' rational bounds; redefine
   `Cr_val` as the corresponding rational ≈ 9.2·10⁷.

This is a multi-step ambitious sprint (≤ 3 hours Generator); after
the proposal is approved and infrastructure is landed, the
Planner queues exactly this follow-up.

## Status log

- 2026-04-30 created from sprint_010 Planner analysis (filed by harness operator concurrent with the regime shift to theoretical refinement)
- 2026-04-30 **approved** by human; infrastructure landed:
  * `Numerical_Library/_phi_loader.py` (shared b-series → phi-series loader)
  * `Numerical_Library/m_phi.py` (`compute_M_phi_bound`)
  * `Numerical_Library/m_phi_prime.py` (`compute_M_phi_prime_bound`)
  * `Numerical_Library/m_pp.py` (`compute_M_pp_bound`)
  * Three new `[[oracles]]` entries in `lemma.toml` (`h_M_phi_oracle`,
    `h_M_phi_prime_oracle`, `h_M_pp_oracle`)
  * `Scratch/sprint_proposal_001_smoke.py` (smoke test + Cr_refined arithmetic)

  **Smoke results at production-grade params** (n_per_edge=512, prec=200,
  K_max=80, on the V8 oracle rectangle Ω(1635/10000, 1115/1000)):
  * `M_phi       ≈ 0.0476` (rationalized 239/5000)
  * `M_phi_prime ≈ 0.0541` (rationalized 543/10000)
  * `M_pp        ≈ 56.31`  (sup ‖H_0''‖ ≈ 5.10 + sup ‖H_η''‖ ≈ 51.21)

  **Important correction to the original proposal's math.** The original
  proposed Cr_refined formula had an extra `invFp³` factor that does NOT
  appear in `Lemma54_Paper_Pderiv_Single.lean:668-670`. The actual Lean
  inequality is

      ‖u''‖ ≤ 2 · ‖Φ'‖ · ‖Φ‖ · invFp² + ‖u_zz‖ · ‖Φ‖²

  with `Φ = H_η - H_0`. The `M_pp` oracle (sup ‖F_ww‖) only enters via the
  implicit-function chain `‖u_zz‖ ≤ M_pp · invFp³`, which at our parameters
  (`invFp³ ≈ 23764`) is ~1000× *looser* than the existing direct Cauchy
  bound `‖u_zz‖ ≤ 8R/(1-r)² ≈ 1437.5`. Therefore the M_pp oracle does NOT
  help at V8 parameters and should not be used; the M_phi and M_phi_prime
  oracles alone (keeping the existing Cauchy step for ‖u_zz‖) give the
  win. M_pp is registered anyway, in case a future regime with different
  parameters can use it.

  **Win factor (predicted from smoke arithmetic at V8 params):**
  * Cr_refined = `M_phi_prime · M_phi · invFp² + (1/2) · (8R/(1-r)²) · M_phi²`
              ≈ `0.054 · 0.048 · 826.6 + 0.5 · 1437.5 · 0.0023`
              ≈ `2.14 + 1.64 = 3.79`
  * V8 Cr_val = 1.132·10⁹ → **Cr_refined ≈ 4** (or any small rational ≥ 3.79)
  * Win factor: ~3·10⁸× (`Cr_val ≈ 5` would still leave huge margin)

  The Planner is free to evolve the strategy from here — e.g., refine
  M_phi_prime via an even tighter η-aware bound, or revisit M_pp once
  the rectangle shrinks enough to make `invFp` small.
