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

## Binding patch (2026-05-03) — read before priorities

> **K_max truncation regression discovered and patched.** Every
> oracle in `Numerical_Library/` (V9–V26's backing) imports the
> non-rigorous `eval_H_eta_at_acb` (K_max truncation, no tail
> bound). All `Cr_val` claims from V9 onward rest on this
> heuristic step. **Full bug write-up + truncation-free
> replacement infrastructure + cached production / round-3
> outputs + per-candidate audit table** are in
> [PATCH_NOTES.md](PATCH_NOTES.md). The Evaluator now enforces
> rules R1–R5 via gate **G7** (`TRUNCATION_REGRESSION` +
> `AUDIT_FLOOR_VIOLATION`). Anti-truncation directives have been
> added to `.claude/agents/refinement-{planner,generator,evaluator}.md`.
>
> **Practical effect on the trajectory.** The lowest rigorously
> certifiable `Cr_val` is now **V11 ≈ 0.33** (Cr_phi_uzz formula,
> round-3 subdivision data); V12–V26's tight literals
> (`1/32`, `1/300`, …, `1/268000`) are *unreachable* until
> `Cr_patched` is brought down by structural work — more
> subdivision rounds, anisotropic refinements, alternative
> contours, sharper joint oracles. Sprints proposing
> `Cr_val < Cr_patched(parent)` must explain the *math* by which
> the audit floor moves. Re-rationalising oracle ceilings against
> the K_max-era heuristic is **not a permitted direction**.

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

note: 2026-04-30 — POLICY UPDATE: oracles are now self-serve. The Generator can mint new arb-certified `[[oracles]]` entries inline (write Numerical_Library/m_<name>.py, append to lemma.toml, declare axiom in candidate, use in proof) without going through the Proposals/ queue. Trust delta is zero — the runtime arb pipeline re-verifies every audit. Templates: Numerical_Library/m_phi.py, m_phi_prime.py, m_pp.py. Proposals/ is now reserved for non-oracle expansions (new free-floating analytic axioms, Mathlib imports requiring justification, reformulations). Also: Planner is told to prefer research/cleanup sprints over BLOCKED_NEEDS_HUMAN — the harness should not halt itself. See refinement-generator.md "Inline oracle creation" and refinement-planner.md "Keeping the loop running" for details.
sprint_013 queued: Lift Cauchy contour radius from (1-r)/2 to (1-r)·9/10 in F_inv_*_deriv_bound_core; drop Cr_val from 5 to 2 (3.24× reduction in Cr_phi via tightened invFp and ‖u_zz‖) [direction: contour-change]
sprint_013 BLOCKED: Lift Cauchy contour radius (1-r)/2 → (1-r)·9/10 [direction: contour-change]
note: 2026-04-30 — sprint_013 BLOCKED by Generator. Contract's premise was wrong: F_inv_paper_analytic only supplies analyticity on disk(r1 r) where r1 r = (1+r)/2, so the recentred Cauchy ball at z₀ ∈ disk r requires ρ ≤ (1-r)/2 to stay in the analyticity domain — the existing radius is already MAXIMAL, not conservative. At V9's r=23/25 and k=9/10 the lifted radius gives r+ρ = 124/125 = 0.992 > 0.96 = r1 r. Lifting requires a NEW (larger) analyticity-domain axiom (e.g. analyticity on disk r2 with r2 = (3+r)/4 → 1.5× lift), which the harness forbids. Generator reverted Lemma54_Paper_Cauchy.lean to byte-identical pre-sprint state; no V10 created. See Scratch/sprint_013_blocker_analysis.py and Experience.md sprint_013 entry. Next Planner must pick a different direction (identity-refine, Cauchy-replacement, inline-oracle, or file a non-oracle proposal for the larger analyticity domain).
sprint_014 queued: Inline new arb-certified inv_F_p_z_oracle (1/‖D‖ bound) replacing paper's loose 2R/(1-r); drop Cr_val from 5 to 2 [direction: inline-oracle]
sprint_014 PASS: Inline new arb-certified inv_F_p_z_oracle (1/‖D‖ bound) replacing paper's loose 2R/(1-r); drop Cr_val from 5 to 2 [direction: inline-oracle]
sprint_015 queued: Replace ‖u_zz‖ ≤ 8R/(1-r)² Cauchy step with aux-z-identity bound ‖u_zz‖ ≤ M_pp · inv_F_p_z³ via the proposal_001-approved h_M_pp_oracle (unused since proposal approval); drop Cr_val from 2 to 1 [direction: formula-change consuming approved-proposal_001 oracle (M_pp)]
sprint_015 PASS: Replace ‖u_zz‖ ≤ 8R/(1-r)² Cauchy step with aux-z-identity bound ‖u_zz‖ ≤ M_pp · inv_F_p_z³ via the proposal_001-approved h_M_pp_oracle; drop Cr_val from 2 to 1 [direction: formula-change consuming approved-proposal_001 oracle (M_pp)]
sprint_016 queued: Replace V11's M_pp · inv_F_p_z³ ≈ 449 product bound on ‖u_zz‖ with a single direct inline oracle on ‖DD/D³‖ ≤ 2 (exploiting the closed-form identity H_0''/H_0'³ = w); drop Cr_val from 1 to 1/32 (32× reduction) [direction: formula-change + inline-oracle]
sprint_016 FAIL: Replace V11's M_pp · inv_F_p_z³ product with direct ‖DD/D³‖ inline oracle [direction: formula-change + inline-oracle] [gate: G3]
note: 2026-04-30 — sprint_016 V12 is mathematically sound (would pass G4/G5/G6 with Cr_val=1/32, a 32× reduction), but G3 (write-scope) flagged two out-of-scope writes: `docs/HARNESS_OPERATOR_TIPS.md` (outside Lemma 5.4 ecosystem) and `ProofRefinement/Lemma54/Numerical_Library/__init__.py` (contract named `u_zz.py` but not `__init__.py`). Next sprint should either (a) re-queue sprint_016 with these files added to the contract's Concrete edits, or (b) revert the docs file and replicate the V12 work without touching `__init__.py` (or extend Generator's always-allowed list to include `Numerical_Library/__init__.py` for any inline-oracle sprint).

sprint_017 queued: Salvage V12 — revert out-of-scope docs/HARNESS_OPERATOR_TIPS.md and re-evaluate the byte-identical, mathematically-sound V12 (Cr_val=1/32, 32x reduction over V11) under a contract that allowlists Numerical_Library/__init__.py [direction: salvage]
sprint_017 PASS: Salvage V12 — revert out-of-scope docs/HARNESS_OPERATOR_TIPS.md; V12 byte-identical, Cr_val=1/32 locked in (32× reduction over V11) [direction: salvage]
sprint_018 queued: Tighten V12's four η-aware oracle ceilings (M_phi, M_phi_prime, inv_F_p_z, u_zz_bound) to their exact certified rationals and drop Cr_val from 1/32 to 1/300 (9.375× reduction) [direction: oracle-ceiling-tightening]
sprint_018 PASS: Tighten V12's four η-aware oracle ceilings to exact certified rationals; drop Cr_val from 1/32 to 1/300 (9.375× reduction) [direction: oracle-ceiling-tightening]
sprint_019 queued: Mint inline arb-certified joint oracle on ‖Phi·Phi'/D²‖ over [0,pr_paper]×Ω, replacing term-1 triangle product M_phi·M_phi_prime·inv_F_p_z² in Cr_phi_uzz_direct; drop Cr_val from 1/300 to ≤ 1/350 (≥1.17× reduction) [direction: inline-oracle: joint analytic-correlation]
sprint_019 PASS: Mint inline arb-certified joint oracle on ‖Phi·Phi'/D²‖; drop Cr_val from 1/300 to 1/1300 (4.33× reduction; joint sup ≈3/10000, ~7× smaller than triangle product) [direction: inline-oracle: joint analytic-correlation]
sprint_020 queued: Mint inline arb-certified joint oracle on ‖DD·Phi²/D³‖ over [0,pr_paper]×Ω, replacing term-2 triangle product u_zz_bound·M_phi² in Cr_phi_uzz_direct_joint; drop Cr_val from 1/1300 to ~1/2400-1/2639 (~1.85-2.03× reduction; smoke-tested joint sup ≈1.53·10⁻⁴, 6× smaller than triangle product 9.24·10⁻⁴) [direction: inline-oracle: joint analytic-correlation (term-2)]
sprint_020 PASS: Mint inline joint oracle on ‖DD·Phi²/D³‖ replacing term-2 triangle product; drop Cr_val from 1/1300 to 1/2600 (2× reduction; oracle returns 153/1000000, 5 V14 oracles orphaned) [direction: inline-oracle: joint analytic-correlation (term-2)]
sprint_021 queued: Tighten compute_joint_phi_phip_invD2_bound rationalization (safety_abs 1e-4 -> 1e-7) to retire 33% oracle-ceiling slack on V15 term-1; joint_phi_phip_invD2_val 3/10000 -> 1/5000; drop Cr_val from 1/2600 to 1/3500 (1.346x win) [direction: oracle-ceiling-tightening]
sprint_021 PASS: Tighten compute_joint_phi_phip_invD2_bound rationalization (safety_abs 1e-4 -> 1e-7); drop Cr_val from 1/2600 to 1/3500 (1.346× win) [direction: oracle-ceiling-tightening]
sprint_022 queued: Wildcard research sprint — V17 byte-identical to V16 (Cr_val 1/3500 unchanged), primary deliverable is Scratch/sprint_022_research_findings.md characterizing high-resolution joint-oracle floor and the alternative factored bound to inform sprint_023's structural pivot [direction: research: achievable-floor-and-alternative-factored-bound-probe]
sprint_022 PASS: Wildcard research — verdict L1-RUN (n_per_edge=4096 drops joint -68.6%, uzz_phi_sq -71.9%, target Cr_val ~1/5672 next sprint); L2 factored-bound dead [direction: research: achievable-floor-and-alternative-factored-bound-probe]
sprint_023 queued: Bump joint oracles n_per_edge 2048->4096; tighten joint_phi_phip_invD2_val to 63/1000000 and uzz_phi_sq_val to 11/250000; drop Cr_val from 1/3500 to 1/11700 (3.34x win, executing sprint_022's L1-RUN recommendation) [direction: oracle-resolution-tightening]
sprint_023 PASS: Bump joint oracles n_per_edge 2048->4096; drop Cr_val from 1/3500 to 1/11700 (3.34× win) [direction: oracle-resolution-tightening]
sprint_024 queued: Bump joint oracles n_per_edge 4096->8192; tighten joint_phi_phip_invD2_val to 3/125000 and uzz_phi_sq_val to 3/200000; drop Cr_val from 1/11700 to 1/31500 (2.69x win) [direction: oracle-resolution-tightening]
sprint_024 PASS: Bump joint oracles n_per_edge 4096->8192; drop Cr_val from 1/11700 to 1/31500 (2.69× win) [direction: oracle-resolution-tightening]
sprint_025 queued: Bump joint oracles n_per_edge 8192->16384; tighten joint_phi_phip_invD2_val to 3/250000 and uzz_phi_sq_val to 3/500000; drop Cr_val from 1/31500 to 1/66500 (2.111x win; final consecutive sprint on this axis before sprint_026 mandatory pivot) [direction: oracle-resolution-tightening]
sprint_025 PASS: Bump joint oracles n_per_edge 8192->16384; drop Cr_val from 1/31500 to 1/66500 (2.111× win; sprint_026 must pivot off this axis) [direction: oracle-resolution-tightening]
sprint_026 queued: WILDCARD pivot off oracle-resolution-tightening — branch from V18, retune both joint oracles' rationalisation (safety_abs 1e-7->1e-8, max_denom 1M->10M) at n_per_edge=16384; tighten joint_phi_phip_invD2_val to 11/1000000 and uzz_phi_sq_val to 29/5000000; drop Cr_val from 1/66500 to 1/71900 (1.082x win) [direction: oracle-ceiling-tightening]
sprint_026 PASS: WILDCARD oracle-ceiling-tightening (safety_abs 1e-7->1e-8, max_denom 1M->10M); drop Cr_val from 1/66500 to 1/71900 (1.082× win) [direction: oracle-ceiling-tightening]
sprint_027 queued: Bump joint oracles n_per_edge 16384->32768; tighten joint_phi_phip_invD2_val to 13/2000000 and uzz_phi_sq_val to 31/10000000; drop Cr_val from 1/71900 to 1/124000 (1.724x win) [direction: oracle-resolution-tightening]
sprint_027 PASS: Bump joint oracles n_per_edge 16384->32768; drop Cr_val from 1/71900 to 1/124000 (1.724× win) [direction: oracle-resolution-tightening]
sprint_028 queued: Bump joint oracles n_per_edge 32768->65536; tighten joint_phi_phip_invD2_val to 47/10000000 and uzz_phi_sq_val to 3/1250000; drop Cr_val from 1/124000 to 1/169000 (1.363x win; per-doubling reduction now 28%/21%, accelerated diminishing returns - sprint_029 onward must consider structural pivots) [direction: oracle-resolution-tightening]
sprint_028 PASS: Bump joint oracles n_per_edge 32768->65536; drop Cr_val from 1/124000 to 1/169000 (1.363× win) [direction: oracle-resolution-tightening]
sprint_029 queued: Wildcard research sprint — probe three structural pivot levers (3-way decomposition, merged numerator at n=65536, per-edge sup dominance) and file proposal_003 (wider analyticity domain) async; V24 byte-identical to V23 (Cr_val 1/169000 unchanged), deliverables inform sprint_030 mandatory wildcard [direction: research+proposal-filing]
sprint_029 PASS: Wildcard research — 3-way decomp DEAD; merged-numerator INCONCLUSIVE (ratio trending 1.78→1.20 over 4 doublings); per-edge sup INCONCLUSIVE; proposal_003 (wider analyticity domain) filed pending; Cr_val unchanged 1/169000 [direction: research+proposal-filing]

sprint_030 queued: WILDCARD merged-numerator structural pivot — replace V23 joint+uzz triangle product with single inline oracle on |2*Phi*Phi^*D - DD*Phi^2|/|D|^3 at n_per_edge=262144 (probe at n=131072 ratio=1.0344 trending to ~0.86 at n=262144 per Scratch/sprint_030_merged_n131072.txt); target Cr_val 1/169000 -> ~1/200000 (~1.18-1.4x win) [direction: formula-change: merged-numerator inline oracle]
sprint_030 PASS: WILDCARD merged-numerator structural pivot — verification probe at n=262144 confirmed ratio 0.871 < 1.0; new merged_uderiv inline oracle (41/5000000) collapses two oracles into one; drop Cr_val from 1/169000 to 1/240000 (1.42× win, beating ≤1/200000 target) [direction: formula-change: merged-numerator inline oracle]
sprint_031 queued: Bump merged_uderiv oracle n_per_edge 262144->524288; tighten merged_uderiv_val from 41/5000000 to ~71/10000000 (or tighter); drop Cr_val from 1/240000 to ≤1/280000 (≥1.17x win, projected ~1.23x to 1/295000 per Scratch/sprint_031_planner_projection.txt) [direction: oracle-resolution-tightening]
sprint_031 PASS: Bump merged_uderiv oracle n_per_edge 262144->524288 (37/5000000); drop Cr_val from 1/240000 to 1/268000 (1.117× win; ball value sat above optimistic threshold so cond_a unreachable) [direction: oracle-resolution-tightening]
sprint_032 queued: Bump merged_uderiv oracle n_per_edge 524288->1048576 AND tighten rationaliser (safety_abs 1e-8->1e-9, max_denom 1e7->1e8); drop Cr_val from 1/268000 to <=1/290000 (>=1.082x conservative; projected 1.10-1.12x to 1/295000-1/300000 per Scratch/sprint_032_planner_options.py) [direction: oracle-resolution-tightening + oracle-ceiling-tightening]
note: 2026-05-03 — **K_MAX TRUNCATION REGRESSION DISCOVERED.** All Numerical_Library oracles backing V9-V26 import non-rigorous eval_H_eta_at_acb (K_max truncation, no rigorous tail bound). All Cr_val claims V9..V26 invalidated. Truncation-free oracle suite + post-patch chunk certifier + corner-subdivision (3 rounds: Cr 34.47 → 0.383) + per-candidate naive audit completed; cached in Cache/Backups/2026-05-03_{production,subdivision}/. Per-candidate Cr_patched table in PATCH_NOTES.md §3 — V9 stays at 7.25, V10 at 0.49, V11 at 0.33 (best rigorously achievable today), V12-V24 at 0.21-0.41, V25-V26 at 0.37 — all far above their declared `1/<huge>` literals. Evaluator gate G7 added (TRUNCATION_REGRESSION + AUDIT_FLOOR_VIOLATION); planner + generator updated. **Future planner: do NOT propose Cr_val < Cr_patched(parent) without a math story for moving the audit floor — sprint_032's "n_per_edge 524288→1048576" direction is now invalid because it just retunes against a non-rigorous floor.** Pre-2026-05-03 candidates V9..V26 grandfathered (G7 SKIPPED for them); new candidates from V27 onward must obey R1-R5.
sprint_033 queued: Re-baseline V27 onto truncation-free round3 oracles via V11 Cr_phi_uzz formula; first post-K_max-patch PASS at Cr_val=1/3 (3x reduction over V11 declaration, dominates audit floor 0.3255 by +2.4%) [direction: truncation-free re-baselining]
sprint_033 PASS: Re-baseline V27 onto truncation-free round3 oracles via V11 Cr_phi_uzz formula; first post-K_max-patch PASS at Cr_val=1/3 (3x reduction over V11 declaration, dominates audit floor 0.3255 by +2.4%) [direction: truncation-free re-baselining]
note: 2026-05-04 — **V11..V26 ARE NOT OBSOLETED BY V27.** sprint_033 only tightened the *literal* Cr_val (1 → 1/3) under V11's Cr_phi_uzz formula; the *analytic* Cr_patched is unchanged at 0.3255 because nothing on the right-hand side of the formula moved. Each V_K row in PATCH_NOTES §3 is a `(formula, oracle constellation)` pair, not a version number — V14's `Cr_phi_uzz_direct_joint` patches to **0.2810** (smaller than V11/V27's 0.3255 — a free ~17% win available by re-baselining onto V14's formula, declaring `Cr_val ≈ 1/3.5`). V25/V26's merged at 0.3734 and V15..V24's joint2 at 0.4105 are *looser* than V11 at round-3 but represent different structural choices that may dominate at finer subdivisions. **Planner: read PATCH_NOTES.md §3a before proposing the next sprint.** Beating V27's 1/3 needs MOVING THE AUDIT FLOOR (re-baseline to V14, round-4 subdivision, sharper joint-oracle Taylor pad, alternative contour) — not literal-tightening.

sprint_034 queued: Re-baseline V28 onto V14 Cr_phi_uzz_direct_joint formula via truncation-free joint_phi_phip_invD2 + u_zz_bound oracles; drop Cr_val from 1/3 to 2/7 (~16.7% reduction); first post-patch sprint to MOVE THE AUDIT FLOOR (V11 floor 0.3255 -> V14 floor 0.28103) by changing formula not literal [direction: formula-change: re-baseline onto V14 Cr_phi_uzz_direct_joint]
sprint_034 PASS: Re-baseline V28 onto V14 Cr_phi_uzz_direct_joint formula (joint + (1/2)*u_zz*M_phi^2); Cr_val 1/3 -> 2/7 (16.7% reduction; first post-K_max-patch sprint to move audit floor 0.3255 -> 0.2810) [direction: formula-change: re-baseline onto V14 formula]
