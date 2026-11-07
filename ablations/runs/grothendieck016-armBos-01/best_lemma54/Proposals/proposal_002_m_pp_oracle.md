# Proposal 002: Single new oracle `compute_M_pp` (sup of `H_0''` and `H_η''` on the oracle rectangle), unlocking the `Cr_refined` chain at the linear-in-p collapse

**Created**: 2026-04-30 06:00 by Planner (sprint_011 context)
**Status**: superseded  <!-- self-superseded by analysis below; documented for institutional memory -->
**Type**: new-oracle

> Origin: this proposal is a *scoped-down sibling* of `proposal_001_cr_refined_oracles.md`
> (which asks for THREE new oracles for `M_diff`, `M_diffp`, `M_pp`). Proposal_001
> remarks at line 117-120 that "If the human wants a smaller-step proposal, an
> interim version with just `M_pp` (replacing the Cauchy step alone, leaving the
> M·R factorization in place) might be a more tractable start; that variant would
> be filed as a separate proposal." This is that proposal.
>
> The Planner's sprint_011 exploration (`Scratch/sprint_011_pure_struct.py`)
> identified the `Cr_refined` direction with `M_pp = 0` as a 1.87× win — but on
> close inspection (sprint_011 contract's "Concrete edits" steps 3-5) found that
> `M_pp = sup ‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖` is the **second w-derivative
> of F_p evaluated at the F_inv image**, and is NOT bounded by the existing `h_M_oracle`
> (which only bounds `H_0`, `H_η`, `H_0'`, `H_η'`, NOT their second derivatives).
> Cauchy on the existing M-bound fails because the F_inv image straddles the
> boundary of `S = {|Re w| < 1}` (since `R_val_paper r ≈ 1.144 > 1`), so no
> uniform Cauchy radius is available. Hence a new oracle is needed.

## What's needed (precise, mechanically actionable)

One new certified-arb oracle plus its `[[oracles]]` entry and supporting axiom declaration.

- **File**: `ProofRefinement/Lemma54/Numerical_Library/m_pp.py` (new)
  - Function: `def compute_M_pp(**overrides) -> OracleResult` returning a certified rational upper bound on
    ```
    sup { ‖iteratedDeriv 2 (Braverman.F_p η p) w‖ : p ∈ [0, p_max], w ∈ Ω(δ_val, B_val) }
    ```
    where `Ω(δ, B)` is the same Step-1/Rouché-certified rectangle the existing `compute_M_bound_tight` uses (`δ = 1635/10000`, `B = 1115/1000`) and `p_max = pr_paper η_val r_val` (or a rational lower bound such as `p_max = 1/100`, since the lemma's conclusion is an inequality on `p < pr_paper`, not an equality).
  - Implementation: compute `‖(1-p) H_0''(w) + p H_η''(w)‖` directly via certified arb on the rectangle. The arb pipeline is the same shape as `compute_M_rigorous` but on the second derivatives of H_0 and H_η. Numerical estimates (from prototype below) suggest the bound is in the range `~10²-10³` (much tighter than the Cauchy-on-S substitute which would give `~32016`).
  - Return type: `OracleResult` (matching the existing `compute_M_bound_tight`).

- **lemma.toml entry** (new):
  ```toml
  [[oracles]]
  short = "h_M_pp_oracle"
  axiom_fq = "Braverman.PaperV0.h_M_pp_oracle"
  bound_field = "M_pp_val"
  oracle_fn = "compute_M_pp"
  ```

- **Axiom declaration** (in `Proof/Lib/Lemma54_Paper.lean` or in candidate-side
  `Candidates/V_<next>.lean`):
  ```lean
  -- Either in Proof/Lib/Lemma54_Paper.lean (analogous to h_M_oracle's declaration in V0)
  -- or in the candidate file (analogous to V0's h_M_oracle):
  axiom h_M_pp_oracle : ∀ p ∈ Set.Ico (0 : ℝ) (pr_paper η_val r_val r_pos r_lt_one),
      ∀ w ∈ oracle_domain,
        ‖iteratedDeriv 2 (Braverman.F_p η_val p) w‖ ≤ M_pp_val
  ```
  (The exact signature follows the pattern of the existing `h_M_oracle`; the axiom
  is oracle-witnessed, not a free analytic axiom.)

- **No new Mathlib imports needed** — `iteratedDeriv`, `F_p`, `Braverman.Omega` are
  all already in scope.

## Mathematical content (≤ 6 sentences)

`M_pp = sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖iteratedDeriv 2 (F_p η p) w‖` is
the sup-norm of the second `w`-derivative of `F_p η p` (the family
`(1-p) H_0(w) + p H_η(w)`) over the oracle rectangle. By
`iteratedDeriv_2_F_p_eq` (already proved at `Lemma54_Paper_Pderiv.lean:100`),
`iteratedDeriv 2 (F_p η p) w = (1-p) iteratedDeriv 2 H_0 w + p iteratedDeriv 2 (H_eta η) w`,
so `M_pp ≤ sup ‖H_0''‖ + sup ‖H_η''‖` on the rectangle. Both `H_0''` and `H_η''`
are analytic on `S ⊃ Ω(δ, B)`, and the certified-arb pipeline can compute their sup-norms on the rectangle directly using the same Cauchy contour arithmetic as `compute_M_rigorous` does for `H_0`, `H_η`, `H_0'`, `H_η'` (the second-derivative case is structurally identical, just one Cauchy step deeper). The rectangle `Ω(1635/10000, 1115/1000)` is well inside the joint analytic strip `|Re w| < 1`, so no boundary issues arise on the *rectangle* itself; the Cauchy-radius issue that blocked sprint_011's pure-existing-infrastructure path arose from the F_inv-IMAGE extending to `R = sinh(r₂) ≈ 1.144 > 1`, which crosses S's boundary — but the F_inv-image is INSIDE the oracle rectangle (by `h_oracle_domain_contains_image`), and the rectangle is well-inside S, so a sup-bound on `Ω` is exactly what we need.

## Win unlocked (numerical, must include Scratch/ output)

From `Scratch/sprint_011_pure_struct.py`:

> "Cr_refined (with M_diff = M_diffp = 2M, M_pp = 0) at our params (M=428, R=23/20, 1-r=2/25):
> = 4 M² · (2R/(1-r))² ≈ 6.057·10⁸. Cr_val_new ≈ 6.06·10⁸, vs current 1.132·10⁹ — a 1.87× reduction."

The actual win with a real (nonzero) `M_pp` from the new oracle is slightly less:
`Cr_refined = M_diff · M_diffp · invFp² + M_pp · M_diff² · invFp³ / 2`
`           = 4 M² · invFp² + M_pp · 4 M² · invFp³ / 2`
`           = 4 M² invFp² · (1 + M_pp · invFp / 2)`.

At our params (`M = 428`, `invFp = 2·(23/20)/(2/25) = 28.75`), if the certified
`M_pp` is ~1000 (a conservative upper bound for the rectangle, to be verified by
the actual arb computation), then the multiplier `1 + M_pp · invFp / 2 = 1 + 1000·14.375 = 14376`. That gives `Cr_refined ≈ 4·183184·826.56·14376 ≈ 8.7·10¹²` — *much worse* than V8.

**Wait — this proposal as written delivers a LOSS, not a win.** The `M_pp · M_diff² · invFp³ / 2` term dominates because `M_pp` is large compared to the M·R chain.

**Reconsidering**: the Cr_refined formula `M_diff · M_diffp · invFp² + M_pp · M_diff² · invFp³ / 2` only beats `Cr_tight = 16 M² R(R+1)/(1-r)²` when `M_pp` is small enough that the second term doesn't dominate. Let's solve: we need
`M_pp · 4M² · invFp³ / 2 < 16 M² R / (1-r)² · 1` (the difference between Cr_tight's `R(R+1)` and the would-be Cr_refined's `R²`),
i.e., `2 M_pp · invFp³ < 16 R / (1-r)²`,
i.e., `M_pp < 8 R / (invFp³ · (1-r)²) = 8 R · (1-r)² / (8 R³ / (1-r)³) = (1-r)⁵ / R²`.

At R = 23/20, 1-r = 2/25: `(2/25)⁵ / (23/20)² = (32/9765625) / (529/400) = 32·400/(9765625·529) = 12800/(5.166·10⁹) ≈ 2.5·10⁻⁶`.

So for the Cr_refined chain to BEAT Cr_tight, `M_pp < 2.5·10⁻⁶`. That's effectively zero. **The Cr_refined direction does not win at our parameters unless M_pp is essentially zero.**

The reason: `invFp = 2R/(1-r) = 28.75` is large, so `invFp³ ≈ 24000`, dominating any plausible M_pp. The win from dropping the `+1` in `R+1` (saving factor `R/(R+1) = 23/43`) is overwhelmed by the new `M_pp · invFp³` chunk.

**Conclusion**: this proposal as written would NOT win. The pre-existing proposal_001 ALSO loses on the same arithmetic unless M_diff and M_diffp drop to η²·M-scale (which they do at η = 1/100, giving the ~12× win proposal_001 cites — there `M_diff ≈ 8`, `M_diffp ≈ 8`, replacing the triangle bound `2M = 856`, AND the M_pp · M_diff² · invFp³ chunk is `~M_pp · 64 · 24000 = M_pp · 1.5·10⁶`, which beats the M·R chain only if M_pp itself is reasonable).

**Revised proposal scope**: this proposal is **withdrawn before being acted on**. The
right next move is one of:
1. Approve `proposal_001` (the full three-oracle proposal, η-aware on M_diff and M_diffp), which has the genuine 12× win.
2. Re-allow axiom-prove direction (Bulletin's earlier policy), since sprint 010 demonstrated it cleanly drops audit count without hurting Cr_val.
3. Pause the harness loop until trust-base expansion lands.

## Risk / trust cost

Originally proposed: low trust cost (one new certified-arb oracle, same shape as
existing `h_M_oracle`). Withdrawn before any infrastructure work because the
arithmetic at our parameters shows the proposed `Cr_refined` chain loses to
`Cr_tight` unless `M_pp` is essentially zero, which it isn't.

## Follow-up sprint outline

N/A — this proposal is self-superseding. See "Win unlocked" for the resolution.

## Status log

- 2026-04-30 created by Planner (sprint_011 context)
- 2026-04-30 superseded by proposal_001 — the planner's quick-win analysis was
  wrong; the M_pp · invFp³ chunk dominates at our parameters unless ALL THREE
  of M_diff, M_diffp, M_pp are simultaneously small (which only proposal_001's
  three-oracle scope achieves). This proposal stands as a documented dead-end
  for the harness's institutional memory.
