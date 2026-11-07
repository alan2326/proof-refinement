# Sprint 011: BLOCKED_NEEDS_HUMAN — `Cr_refined` direction numerically verified to require new oracles, proposal_001 pending; no other allowed direction yields a `Cr_val` win at current parameters

**Created**: 2026-04-30 06:15 by Planner
**Parent candidate**: `Candidates/V8.lean` (most recent PASS, `Cr_val = 1132310000`, audit = 13 axioms)
**Target file**: *(none — this sprint files no candidate; the Generator's correct response is `STATUS=BLOCKED_NEEDS_HUMAN`)*
**Direction**: structural-form-replacement attempt → BLOCKED. Direction history: 005, 006, 007 = R-axis (parameter); 008 = M-precision (parameter); 009 = rectangle-delta (parameter); 010 = axiom-prove (forbidden going forward by 2026-04-30 POLICY UPDATE in Bulletin). Sprint 011 attempted Bulletin direction 1 (replace bound's structural form, specifically `Cr_tight → Cr_refined`) and verified numerically that it requires new oracles to actually win.
**Tier**: cheap (this contract is a status report, not a Lean-writing task; the Generator's correct response is a one-paragraph BLOCKED message — see "Acceptance criteria" below).

## Goal (one sentence)

Document, via Generator response only, that the structural-form-replacement direction (`Cr_tight = 16 M² R(R+1)/(1-r)² → Cr_refined = M_diff · M_diffp · invFp² + M_pp · M_diff² · invFp³ / 2`) has been numerically verified by the Planner to *not* deliver a `Cr_val` reduction without new oracles for `M_diff`, `M_diffp`, *and* `M_pp` simultaneously (per `Scratch/sprint_011_arith_check.py`); and since `proposal_001_cr_refined_oracles.md` (which asks for exactly these three new oracles) is already pending and no other allowed direction yields a `Cr_val` win at the current parameters, the loop is at a fixed point pending human action on proposal_001 (or a regime-policy revision).

## Mathematical insight (required, ≤ 5 sentences)

The Pderiv-refined bound `F_inv_p_second_deriv_bound` (already a fully-proved Lean theorem at `Lemma54_Paper_Pderiv.lean:140`) yields `‖∂²_p F_inv‖ ≤ 2 · Cr_refined r M_diff M_diffp M_pp R`, parametric in three sup-norms over the F_inv image: `M_diff = sup‖H_η - H_0‖`, `M_diffp = sup‖H_η' - H_0'‖`, `M_pp = sup‖iteratedDeriv 2 (F_p η p) (F_inv p z)‖`. The Planner initially conjectured (`Scratch/sprint_011_pure_struct.py`) that the linear-in-p structure of `F_p η p w = (1-p) H_0 w + p H_η w` would give `M_pp = 0` *exactly*, plus triangle bounds `M_diff = M_diffp = 2M` from the existing oracle, yielding a free 1.87× win. Closer reading revealed that `M_pp` in the Lean signature is the second **w**-derivative of `F_p` (NOT the second p-derivative): `iteratedDeriv 2 (F_p η p) w = (1-p) H_0''(w) + p H_η''(w)` (proved as `iteratedDeriv_2_F_p_eq` at `Lemma54_Paper_Pderiv.lean:100`), which is *not* zero and is *not* bounded by the existing `h_M_oracle` (which covers only `H_0, H_η, H_0', H_η'`). `Scratch/sprint_011_arith_check.py` then confirmed that even with `M_diff = M_diffp = 2M = 856`, the `Cr_refined` formula's sensitivity to `M_pp` is extreme — the threshold `M_pp < (1-r)/R² = 32/529 ≈ 0.06` is required for `Cr_refined < Cr_tight`, infeasible for any non-trivial second-derivative bound (the existing Cauchy-on-S substitute would give `M_pp ≈ 32016`, completely losing). Only the FULL `proposal_001` scope (three new oracles, with η-aware `M_diff = M_diffp ≈ 8.56` *and* `M_pp ≤ ~600`) recovers the projected ~12× win — confirming that no scoped-down proposal (such as the Planner's prototype `proposal_002_m_pp_oracle.md`, now self-superseded) is viable.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_011_arith_check.py` (output below) computes `Cr_refined / Cr_tight` for a sweep of `(M_diff, M_diffp, M_pp)` choices: at `M_diff = M_diffp = 2M = 856`, `M_pp = 0` gives ratio `0.5349` (1.87× win) but `M_pp = 1` already gives ratio `8.22` (8× LOSS), and `M_pp = 1000` gives ratio `7689` (7689× LOSS); the threshold is `M_pp < 32/529 ≈ 0.06`. At η-aware `M_diff = M_diffp ≈ 2η·M = 8.57` (which `proposal_001`'s `compute_M_diff` would supply), `M_pp ≤ ~1297` is acceptable, recovering the 12× win — but this requires ALL THREE new oracles, exactly `proposal_001`'s scope. The Planner attempted a scoped-down `proposal_002` (M_pp-only oracle, retaining triangle on M_diff/M_diffp) but the same Scratch script verified it does NOT win (the `M_pp = 0` "ideal" gives 1.87× but any actual oracle `M_pp ≥ 1` immediately loses by 8×+); proposal_002 has been filed `Status: superseded` to document this dead-end for future Planner runs.

## Concrete edits expected

The Generator's correct response to this sprint is a `STATUS=BLOCKED_NEEDS_HUMAN` paragraph with no Lean edits, no candidate file, no log entry. Specifically:

- **No edits** to any file in `Candidates/`, `Proof/Lib/`, `LeanProof/`, `ProofGraph/`, `Numerical_Library/`, `lemma.toml`, `Evaluator.py`, `Sprint_Contracts/`, `Refinement_Log/`, or `Proposals/`.
- The Generator returns `STATUS=BLOCKED_NEEDS_HUMAN` with a one-paragraph explanation citing this contract's "Mathematical insight" and "Why" sections, plus the Scratch/ script output, and recommending one of the following human actions (in priority order):
  1. **Approve `proposal_001_cr_refined_oracles.md`** (currently `Status: pending`, the only proposal eligible for unblocking the structural-form-replacement direction).
  2. **Revise the Bulletin's REGIME directive** to re-permit the axiom-prove direction (sprint 010 demonstrated it works cleanly: it dropped audit count by 1 with no Cr_val regression and no new axioms; eight axioms remain available to promote — `pr_paper`, `pr_paper_pos`, `pr_paper_le_one`, `F_inv_paper`, `F_inv_paper_eq`, `F_inv_paper_mem_S`, `F_inv_paper_R_bound`, `F_inv_paper_first_deriv_zero`, `F_inv_paper_analytic`, `F_inv_paper_contdiff`, `F_inv_paper_at_origin`).
  3. **Pause the harness loop** until trust-base expansion lands; resume with a fresh sprint after.

## Acceptance criteria

1. The Generator's response begins with `STATUS=BLOCKED_NEEDS_HUMAN`. Verifiable via `grep -q '^STATUS=BLOCKED_NEEDS_HUMAN' <Generator-output-file-or-stdout>` (or whatever the harness's STATUS-extraction mechanism is).

2. No new files are created in `Candidates/`, `Sprint_Contracts/`, `Refinement_Log/`, or `Proposals/`. The Generator writes nothing to disk in this sprint. Verifiable via `git status --porcelain` showing no additions or modifications outside the Generator's own working notes.

3. The Generator's BLOCKED paragraph explicitly cites at least one of: (a) `proposal_001_cr_refined_oracles.md` (recommending its approval as the canonical path forward), (b) the Bulletin's REGIME directive (recommending its revision), or (c) the harness-pause option. The Generator's paragraph does NOT propose creating a fourth proposal or filing yet another scoped-down variant — proposal_002's superseded status documents that the only remaining proposal scope (M_pp-only) does not win.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Add a new `[[oracles]]` entry in `lemma.toml`.
- File a new proposal in `Proposals/` (proposal_002 already documents the M_pp-only dead-end; further variants would just clutter the directory). The Planner is responsible for proposal management, not the Generator.
- Modify any file in `Candidates/`, `Proof/Lib/`, `LeanProof/`, `ProofGraph/`, `Numerical_Library/`, `lemma.toml`, `Evaluator.py`, `Sprint_Contracts/`, or `Refinement_Log/`.
- Create `Candidates/V9.lean`. There is no candidate this sprint.
- Use `sorry` anywhere. The Generator writes nothing.
- Attempt a Cr_val tightening via parameter tweaks (M_val, R_rat, δ_val, B_val) — explicitly forbidden by the Bulletin's REGIME directive.
- Attempt an axiom-prove move (e.g., promote `F_inv_paper_first_deriv_zero`) — explicitly forbidden by the 2026-04-30 POLICY UPDATE note in the Bulletin.
- Attempt to prove `M_pp = 0` or any related "linear-in-p collapse" — the Planner's `Scratch/sprint_011_pure_struct.py` and `Scratch/sprint_011_arith_check.py` confirm that the relevant `M_pp` is the second w-derivative (NOT p-derivative) and is bounded below by the existing `h_M_oracle`'s coverage gap.

## Time budget

≤ 3 minutes runtime; soft cap 10% of context. The Generator's task is to confirm the BLOCKED reasoning by reading this contract plus `Scratch/sprint_011_arith_check.py`'s output, then write the BLOCKED paragraph.

## Stop conditions for the Generator

- Confirms BLOCKED reasoning and writes the paragraph → `STATUS=BLOCKED_NEEDS_HUMAN`. (This is the *expected* outcome.)
- Disagrees with BLOCKED reasoning AND can construct a candidate `V9.lean` that achieves `Cr_val < 1132310000` with no new axioms/oracles → `STATUS=READY_FOR_EVALUATION` with the candidate. This is highly unlikely given the numerical analysis but is not foreclosed; the Generator's freshness on the problem may catch something the Planner missed. Burden of proof is on the Generator.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
