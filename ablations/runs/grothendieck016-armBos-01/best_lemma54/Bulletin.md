# Bulletin — proof refinement loop

Volatile signaling between sprints. Capped at ~100 lines; the
`/run-next-sprint` skill trims it to the last 50 when it grows past
the cap. The historical record is `Refinement_Log/log.jsonl`.

Format: one line per event.

```
sprint_<NNN> queued: <title> [direction: <axis>]
sprint_<NNN> PASS: <title>
sprint_<NNN> FAIL: <title> (gate: G<id>)
note: <human note>
```

## Current priority

(human-set; the Planner reads this when deciding the next direction)

> **REGIME: theoretical refinement.** Numerical tightening of the
> existing `Cr_tight = 16 M² R (R+1) / (1-r)²` formula is exhausted
> — sprints 003-009 walked Cr_val from ~8.2·10¹⁴ down to ~1.13·10⁹
> by tweaking the rectangle, R-rationalisation, and M-precision, and
> further parameter tweaks would shave at most a few percent off the
> *same loose formula*. **Sprints whose only mechanism is changing a
> parameter value (M_val, R_rat, δ_val, B_val) within `Cr_tight` are
> now forbidden.**
>
> The next sprints must propose a **new mathematical insight or proof
> method**. Permitted directions:
>
> 1. **Replace the bound's structural form**: derive `Cr_<new>` from
>    a different proof strategy — e.g., direct sup of `∂²ₚ F⁻¹` over
>    the disk instead of the M·R·Cauchy chain; Lagrange remainder of
>    order 3 with a third-derivative bound; Schwarz-Pick / Borel-
>    Carathéodory refinement of the Cauchy step exploiting
>    `F⁻¹(0) = 0`.
> 2. **Refine identity (75)**: the paper's expansion of `∂²ₚ F⁻¹`
>    may have terms whose specific bounds are tighter at our
>    `(η = 1/100, r = 23/25)` than the worst-case used.
> 3. **Replace Cauchy with a tighter sup-bound mechanism**:
>    Cauchy on a disk is sharp on circles, but the actual Taylor
>    coefficients of `F⁻¹` are computable; a direct estimate may
>    beat M²·R-based bounds.
> 4. **Inline oracle creation** (NEW, 2026-04-30): create new
>    arb-certified `[[oracles]]` entries inline in a normal sprint —
>    no proposal needed. Any sup-norm of an analytic expression on
>    the oracle rectangle is fair game; the Generator follows the
>    "Inline oracle creation" recipe in its prompt, modeled on
>    `Numerical_Library/m_phi.py`. The runtime arb pipeline
>    re-verifies every oracle every audit, so the trust delta is
>    essentially zero.
> 5. **File a proposal** (`Proposals/proposal_<NNN>_<slug>.md`)
>    only for *non-oracle* trust expansions — new free-floating
>    analytic axioms, Mathlib import additions requiring
>    justification, reformulations. **Async**: file the proposal AND
>    queue some other allowed sprint in the same invocation; the
>    loop never stalls. Budget: max 3 pending proposals. See
>    [`Proposals/README.md`](../Proposals/README.md).
>
> **Axiom-prove is NOT a permitted direction.** Converting an
> existing trusted axiom into a Lean theorem is not treated as a
> victory in the current regime — the trust base shifts inside the
> harness but `Cr_val` is unaffected, and the engineering hours
> are better spent on structural moves.
>
> **BLOCKED_NEEDS_HUMAN is a last resort.** The harness halts and
> deletes its cron when you return that status. Before resorting to
> it, prefer (in order): inline-oracle sprint → research/Scratch
> sprint → small structural cleanup sprint → file a non-oracle
> proposal AND queue any of the above. See the Planner's "Keeping
> the loop running" section.
>
> Every sprint contract must fill the `## Mathematical insight`
> field (see TEMPLATE.md) describing the *math* being attempted, not
> just the edit. Default `Tier:` is `ambitious` for theoretical
> sprints; `cheap` is fine for surgical edits or research sprints.

## Recent events

(append below; older entries get trimmed)

sprint_003 queued: Switch to tight Rouché-certified rectangle Ω(163/1000, 1115/1000), drop M_val to 432 [direction: rectangle-tighten]
sprint_003 PASS: Switch to tight Rouché-certified rectangle Ω(163/1000, 1115/1000), drop M_val to 432 [direction: rectangle-tighten]
sprint_004 queued: Drop the loose (2R+1)(1-r)^3 ≤ 16R algebraic step; switch to Cr_tight = 16 M² R (R+1) / (1-r)² [direction: Cr-formula-tighten]
sprint_004 FAIL: Drop the loose (2R+1)(1-r)^3 ≤ 16R algebraic step; switch to Cr_tight = 16 M² R (R+1) / (1-r)² [direction: Cr-formula-tighten] [gate: G6]
sprint_005 queued: Define Cr_val := 1451520000 (= Cr_tight at R_rat = 4/3); recover sprint_004's score gain through a directly-scorable rational [direction: Cr-formula-tighten]
sprint_005 PASS: Define Cr_val := 1451520000 (= Cr_tight at R_rat = 4/3); recover sprint_004's score gain through a directly-scorable rational [direction: Cr-formula-tighten]
sprint_006 queued: Tighten R rational upper bound from 4/3 to 6/5 via Real.exp_one_lt_d9; drop Cr_val to 1231718400 [direction: R-rationalisation-tighten]
sprint_006 PASS: Tighten R rational upper bound from 4/3 to 6/5 via Real.exp_one_lt_d9; drop Cr_val to 1231718400 [direction: R-rationalisation-tighten]
sprint_007 queued: Bound sinh(49/50) directly via Real.exp_bound (depth 10 Taylor on ±49/50), R ≤ 23/20; drop Cr_val to 1153569600 [direction: sinh-direct-tighten]
sprint_007 PASS: Bound sinh(49/50) directly via Real.exp_bound (depth 10 Taylor on ±49/50), R ≤ 23/20; drop Cr_val to 1153569600 [direction: sinh-direct-tighten]
sprint_008 queued: Tighten compute_M_bound_tight precision (n_per_edge=4096, prec=400, safety_rel=1e-4); drop M_val from 432 to 431, Cr_val from 1153569600 to 1148240000 [direction: M-precision-tighten]
sprint_008 PASS: Tighten compute_M_bound_tight precision (n_per_edge=4096, prec=400, safety_rel=1e-4); drop M_val from 432 to 431, Cr_val from 1153569600 to 1148240000 [direction: M-precision-tighten]
sprint_009 queued: Push delta to its Rouche-margin floor (163/1000 -> 1635/10000); drop M_val from 431 to 428, Cr_val from 1148240000 to 1132310000 [direction: rectangle-delta-tighten]
sprint_009 PASS: Push delta to its Rouche-margin floor (163/1000 -> 1635/10000); drop M_val from 431 to 428, Cr_val from 1148240000 to 1132310000 [direction: rectangle-delta-tighten]
note: 2026-04-30 — REGIME SHIFT to theoretical refinement (numerical-tightening exhausted on Cr_tight). sprint_009 was the last parameter-tweak under the old regime; verdict_009 PASS at Cr_val=1132310000. The next Planner run must create sprint_010 as a theoretical move (axiom-prove / formula-change / identity-refine / contour-change); see "Current priority" above.
sprint_010 queued: Promote F_inv_paper_zero from axiom to Lean theorem via Braverman.H0_injective + Braverman.H0_sin_eq; Cr_val unchanged at 1132310000 but trusted analytic axiom count drops from 12 to 11 [direction: axiom-prove]
sprint_010 PASS: Promote F_inv_paper_zero from axiom to Lean theorem via Braverman.H0_injective + Braverman.H0_sin_eq; Cr_val unchanged at 1132310000 but trusted analytic axiom count drops from 12 to 11 [direction: axiom-prove]
note: 2026-04-30 — POLICY UPDATE: axiom-prove direction is NO LONGER PERMITTED going forward (sprint_010 was the last axiom-prove run). Asynchronous proposal mechanism added: Planner can file Proposals/proposal_<NNN>_<slug>.md requesting human approval for new axioms/oracles, budget 3 pending; agent never stalls. proposal_001 (Cr_refined / 3 new oracles M_diff/M_diffp/M_pp; 12× win on Cr_val) is filed as the first pending proposal — see Proposals/README.md.
sprint_011 queued: BLOCKED_NEEDS_HUMAN — Cr_refined direction numerically verified to require all three new oracles (M_diff, M_diffp, M_pp) per Scratch/sprint_011_arith_check.py; proposal_001 pending; proposal_002 (M_pp-only) self-superseded as a documented dead-end; loop at fixed point pending human action [direction: structural-form-replacement-blocked]
sprint_011 BLOCKED_NEEDS_HUMAN: loop paused; cron deleted; pending human review of proposal_001 OR alternative structural direction in Bulletin priority list
note: 2026-04-30 — proposal_001 APPROVED. Three η-aware oracles registered in lemma.toml (h_M_phi_oracle, h_M_phi_prime_oracle, h_M_pp_oracle) backed by Numerical_Library/{m_phi,m_phi_prime,m_pp}.py. Smoke results in Scratch/sprint_proposal_001_smoke.py. NOTE: the original proposal's Cr_refined formula was incorrect — it had an extra invFp³ factor that does NOT appear in the actual Lean inequality at Lemma54_Paper_Pderiv_Single.lean:668-670 (`‖u''‖ ≤ 2‖Φ'‖‖Φ‖·invFp² + ‖u_zz‖·‖Φ‖²`); the M_pp oracle only enters via the implicit-function chain `‖u_zz‖ ≤ M_pp·invFp³`, while ‖Φ‖ and ‖Φ'‖ enter directly. See Proposals/proposal_001_cr_refined_oracles.md status log for the full correction. Loop unblocked — Planner is free to experiment with the new oracles however it sees fit.
sprint_012 queued: Replace Cr_tight with η-aware Cr_phi consuming approved proposal_001 oracles (M_phi, M_phi_prime, retaining Cauchy on u_zz); drop Cr_val from 1.13·10⁹ to ≤ 5 [direction: uses-approved-proposal_001]
sprint_012 FAIL: Replace Cr_tight with η-aware Cr_phi consuming approved proposal_001 oracles [direction: uses-approved-proposal_001] [gate: G4]
note: 2026-04-30 — sprint_012 V9 is mathematically sound (would pass G5/G6 with Cr_val=5, a 2.26·10⁸× reduction), but G4 (no-new-axioms) flagged the two introduced oracles h_M_phi_oracle and h_M_phi_prime_oracle. Approved-proposal oracles need an explicit G4 exception path. HUMAN ACTION: revise the no-new-axioms gate to allowlist axioms whose names appear as oracle_fn entries in lemma.toml, then resume.
note: 2026-04-30 — G4 SPEC FIXED. The "no new axioms" gate now exempts `kind = oracle` axioms (registered in lemma.toml's [[oracles]] table) — they are human-approved at proposal-approval time, and G5 independently re-verifies them every run. Spec updated in .claude/agents/refinement-evaluator.md and docs/PROOF_REFINEMENT_HARNESS.md.
sprint_012 PASS: Replace Cr_tight with η-aware Cr_phi consuming approved proposal_001 oracles (revised verdict under corrected G4) [direction: uses-approved-proposal_001]. Cr_val 1.132·10⁹ → 5 (~2.26·10⁸× reduction). V9 is the new latest-PASS candidate; verdict_012.md amended; log.jsonl appended with PASS retcon entry.
note: 2026-04-30 — POLICY UPDATE: oracles are now self-serve. The Generator can mint new arb-certified `[[oracles]]` entries inline (write Numerical_Library/m_<name>.py, append to lemma.toml, declare axiom in candidate, use in proof) without going through the Proposals/ queue. Trust delta is zero — the runtime arb pipeline re-verifies every audit. Templates: Numerical_Library/m_phi.py, m_phi_prime.py, m_pp.py. Proposals/ is now reserved for non-oracle expansions (new free-floating analytic axioms, Mathlib imports requiring justification, reformulations). Also: Planner is told to prefer research/cleanup sprints over BLOCKED_NEEDS_HUMAN — the harness should not halt itself. See refinement-generator.md "Inline oracle creation" and refinement-planner.md "Keeping the loop running" for details.
sprint_013 queued: Lift Cauchy contour radius from (1-r)/2 to (1-r)·9/10 in F_inv_*_deriv_bound_core; drop Cr_val from 5 to 2 (3.24× reduction in Cr_phi via tightened invFp and ‖u_zz‖) [direction: contour-change]
sprint_013 BLOCKED: Lift Cauchy contour radius (1-r)/2 → (1-r)·9/10 [direction: contour-change]
note: 2026-04-30 — sprint_013 BLOCKED by Generator. Contract's premise was wrong: F_inv_paper_analytic only supplies analyticity on disk(r1 r) where r1 r = (1+r)/2, so the recentred Cauchy ball at z₀ ∈ disk r requires ρ ≤ (1-r)/2 to stay in the analyticity domain — the existing radius is already MAXIMAL, not conservative. At V9's r=23/25 and k=9/10 the lifted radius gives r+ρ = 124/125 = 0.992 > 0.96 = r1 r. Lifting requires a NEW (larger) analyticity-domain axiom (e.g. analyticity on disk r2 with r2 = (3+r)/4 → 1.5× lift), which the harness forbids. Generator reverted Lemma54_Paper_Cauchy.lean to byte-identical pre-sprint state; no V10 created. See Scratch/sprint_013_blocker_analysis.py and Experience.md sprint_013 entry. Next Planner must pick a different direction (identity-refine, Cauchy-replacement, inline-oracle, or file a non-oracle proposal for the larger analyticity domain).
sprint_014 queued: Inline new arb-certified inv_F_p_z_oracle (1/‖D‖ bound) replacing paper's loose 2R/(1-r); drop Cr_val from 5 to 2 [direction: inline-oracle]
sprint_014 PASS: Inline new arb-certified inv_F_p_z_oracle (1/‖D‖ bound) replacing paper's loose 2R/(1-r); drop Cr_val from 5 to 2 [direction: inline-oracle]
sprint_015 queued: Replace ‖u_zz‖ ≤ 8R/(1-r)² Cauchy step with aux-z-identity bound ‖u_zz‖ ≤ M_pp · inv_F_p_z³ via the proposal_001-approved h_M_pp_oracle (unused since proposal approval); drop Cr_val from 2 to 1 [direction: formula-change consuming approved-proposal_001 oracle (M_pp)]
sprint_015 PASS: Replace ‖u_zz‖ ≤ 8R/(1-r)² Cauchy step with aux-z-identity bound ‖u_zz‖ ≤ M_pp · inv_F_p_z³ via the proposal_001-approved h_M_pp_oracle; drop Cr_val from 2 to 1 [direction: formula-change consuming approved-proposal_001 oracle (M_pp)]
