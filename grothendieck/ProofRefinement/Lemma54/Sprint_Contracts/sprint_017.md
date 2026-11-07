# Sprint 017: Salvage V12 — revert out-of-scope `docs/HARNESS_OPERATOR_TIPS.md` and re-evaluate the already-mathematically-sound V12 candidate (Cr_val = 1/32, a 32× reduction over V11) under a contract whose `Concrete edits expected:` correctly enumerates `Numerical_Library/__init__.py`

**Created**: 2026-04-30 16:30 by Planner
**Parent candidate**: `Candidates/V12.lean` (already on disk from sprint_016; mathematically sound; passed G1/G2 of the evaluator with `status: ok` and `Cr_val = 1/32 = 0.03125`; failed only G3 due to write-scope violation on two files). This sprint does NOT create a new candidate file — it merely cleans up the workspace so V12 passes G3, and re-runs the evaluator to log the PASS verdict for sprint_017.
**Target file**: `ProofRefinement/Lemma54/Candidates/V12.lean` (no edits — kept byte-identical to its current state). Workspace remediation only.
**Direction**: salvage — recover the 32× win sprint_016 produced. Direction-history check: 014=inline-oracle, 015=formula-change-uses-approved-proposal_001, 016=formula-change+inline-oracle (FAILed G3). Salvage is a distinct, surgical direction (no-same-axis-3-times-in-a-row rule satisfied — distinct from each of the prior three).
**Tier**: cheap (≤30 min runtime; only two file operations: revert one file, no other Lean writes; the candidate, oracle, and Lean infrastructure are already in place from sprint_016 and remain byte-identical).

## Goal (one sentence)

Revert the out-of-scope `docs/HARNESS_OPERATOR_TIPS.md` modification (which sprint_016 wrote outside the Lemma 5.4 ecosystem in violation of G3) so that re-running the Evaluator on the existing, byte-identical `Candidates/V12.lean` passes all six gates and logs the 32× `Cr_val` reduction (`1` → `1/32 = 0.03125`) as the new latest-PASS state.

## Mathematical insight (required, ≤ 5 sentences)

V12's mathematical content was settled by sprint_016: the auxiliary z-identity `DD · h_z² + D · u_zz = 0` together with `‖h_z‖ = 1/‖D‖` collapses `‖u_zz‖` to the *single* analytic quotient `‖DD‖/‖D‖³ = ‖DD/D³‖`, which the new `h_u_zz_oracle` certifies sup-bounded by `15519/10000 ≈ 1.5519` on the V11 rectangle (vs. V11's loose triangle product `M_pp · inv_F_p_z³ = 35048/625 · 8 ≈ 449`, a 289× factor of slack). The closed-form arcsin identity `H_0''(w)/H_0'(w)³ = w` is what powers the tightening — at `p = 0` the worst-case quotient is exactly `|w|`, and the η = 1/100 correction at `p > 0` only contributes ~10%, justifying the rational ceiling `u_zz_bound_val := 2`. Sprint_017 does NOT change this math at all — `V12.lean`, `Lemma54_Paper.lean`'s `Cr_phi_uzz_direct`, `Lemma54_Paper_Pderiv_Single.lean`'s `F_inv_p_second_deriv_bound_phi_uzz_direct`, `Lemma54_Paper_Main.lean`'s `lemma_5_4_paper_on_domain_phi_uzz_direct`, `Numerical_Library/u_zz.py`'s `compute_u_zz_bound`, and the `[[oracles]]` block for `h_u_zz_oracle` in `lemma.toml` are all already in place from sprint_016 and remain byte-identical. The sprint is purely a workspace-state cleanup so the Evaluator's G3 gate (write-scope check) accepts what is already a working candidate.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_017_planner_v12_state.py` parses the log and confirms V12 has a clean `status: ok` evaluation entry (timestamp 2026-04-30T08:07:20Z) with `Cr_val = 1/32 = 0.03125`, four oracle-kind axioms (`h_M_phi_oracle` 61/2500≤239/5000, `h_M_phi_prime_oracle` 59/2000≤543/10000, `h_inv_F_p_z_oracle` 3407/2000≤2, `h_u_zz_oracle` 15519/10000≤2) all `status: pass`, no `h_M_pp_oracle` in the audited set (correctly dropped), and no `sorry`. The 32× reduction over V11's `Cr_val = 1` and the 2.6·10¹⁶× cumulative reduction from V0 (~8.2·10¹⁴) are sitting on the floor unscored only because the sprint_016 contract failed to enumerate `Numerical_Library/__init__.py` (functionally required: the `__init__.py` must `from .u_zz import compute_u_zz_bound` and re-export it for the Evaluator's `ORACLE_REGISTRY` discovery to find the function) and the Generator wrote a stray operator-tips doc outside the Lemma 5.4 ecosystem. Reverting the doc and including the `__init__.py` modification in this contract's allowlist is a one-edit cleanup that converts an already-passing candidate into a logged win.

## Concrete edits expected

- **`docs/HARNESS_OPERATOR_TIPS.md`** (REMOVE): delete this file. It was written by sprint_016's Generator outside the Lemma 5.4 ecosystem (`docs/` is for harness-wide operator notes, not Lemma-5.4-specific content), is not referenced by any Lean module or oracle, and has no functional role in V12's proof or audit. Use `git rm docs/HARNESS_OPERATOR_TIPS.md` (or equivalent) — the file's content is incidental and not load-bearing for any candidate; if any portion of the operator-tips content is genuinely useful it can be re-added later via a dedicated docs-only contribution outside the harness loop.

- **`ProofRefinement/Lemma54/Numerical_Library/__init__.py`** (KEEP AS-IS, ALLOWLIST ONLY): this file is **already** in its sprint_016 state with the new lines `from .u_zz import compute_u_zz_bound` and `compute_u_zz_bound` appended to `__all__`. These additions are functionally required for `Evaluator.ORACLE_REGISTRY` to discover `compute_u_zz_bound` — without them, G5 (oracle-backing audit) would fail to find the runner for the new `h_u_zz_oracle` axiom. Do NOT modify this file further; it is named here purely so that G3's write-scope check whitelists the existing additions rather than flagging them. If the Evaluator's G3 implementation diffs against the *contract's* `Concrete edits expected:` list (rather than against the candidate's parent state), then this entry alone — without any actual write — should suffice to allowlist the diff.

- **`ProofRefinement/Lemma54/Candidates/V12.lean`** (BYTE-IDENTICAL — DO NOT TOUCH): the existing file is the sprint_016 output and must remain unchanged. The Generator should explicitly verify (e.g., `sha256sum`) that V12's content matches the log entry's `candidate_sha256: df83f864cd150b1e9d8d3627fb9da8d7fa29dda23574421099c7ecacff8fe2b7` after any cleanup, to confirm the math has not been disturbed.

- **NO other edits** to: `Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, `Lemma54_Paper_Cauchy.lean`, `Lemma54_Paper_Identity.lean`, `Lemma54_Paper_Pderiv.lean`, `Lemma54_Paper_Taylor.lean`, `Numerical_Library/u_zz.py`, `Numerical_Library/{m_pp,m_phi,m_phi_prime,inv_F_p_z,m_bound,r_bound,_arb_helpers,_phi_loader,types}.py`, `lemma.toml` (the `[[oracles]]` block for `h_u_zz_oracle` is already present from sprint_016), `Proof/SearchConfig.lean`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, or any candidate file `V<K>.lean`. The single mutation in this sprint is the deletion of `docs/HARNESS_OPERATOR_TIPS.md`.

## Acceptance criteria

1. The file `docs/HARNESS_OPERATOR_TIPS.md` no longer exists. Mechanically: `! test -e docs/HARNESS_OPERATOR_TIPS.md` exits 0 (i.e., test for absence succeeds).

2. `lake env lean ProofRefinement/Lemma54/Candidates/V12.lean` exits 0 (compiles clean, no `sorry`) — confirms V12's math is undisturbed by the cleanup.

3. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V12.lean` exits 0 with `status: ok`, and the resulting log entry has `score.numer / score.denom == 1/32` exactly. Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; assert r["score"]["numer"]==1 and r["score"]["denom"]==32, r["score"]; axs={a["name"] for a in r["axioms_used"]}; assert "Braverman.PaperV0.h_u_zz_oracle" in axs, axs; assert "Braverman.PaperV0.h_M_pp_oracle" not in axs, axs'`.

(All three are mechanically checkable via `bash` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Modify `Candidates/V12.lean` in any way (byte-equality with the sprint_016 output is required; any diff invalidates the salvage).
- Re-run or re-engineer the V12 mathematical pipeline (the new `Cr_phi_uzz_direct` definition, the `F_inv_p_second_deriv_bound_phi_uzz_direct` core lemma, the `lemma_5_4_paper_on_domain_phi_uzz_direct` wrapper, the `compute_u_zz_bound` oracle, or the `[[oracles]]` registration in `lemma.toml`). All of those are correct and present from sprint_016; touching them risks regressing a 32× win.
- Add any new free-floating analytic axiom (non-oracle-shaped). No new axioms of any kind in this sprint — V12 already has its full audit set.
- Modify `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, any candidate file `V<K>.lean` for `K ≤ 11`, any of the seven `Lemma54_Paper*.lean` files, or any file under `Numerical_Library/` (the directory's contents are already in their final state from sprint_016).
- Add new entries to `Numerical_Library/__init__.py` beyond what sprint_016 already wrote. The `from .u_zz import compute_u_zz_bound` line and the `__all__` append are already present; a no-op confirmation (e.g., `git diff --quiet ProofRefinement/Lemma54/Numerical_Library/__init__.py HEAD~N` against the appropriate baseline, or simply leaving the file alone) is the right behavior.
- Restore `docs/HARNESS_OPERATOR_TIPS.md` content elsewhere in the repository (e.g., copying it into `ProofRefinement/Lemma54/`); the file is being deleted because its location was wrong AND because the harness loop does not need its content. If any of its operator-tips content is genuinely worth preserving, that is a separate human-driven docs task outside the refinement loop, not something to relocate in this sprint.
- Use `sorry`, `admit`, `native_decide`, or any non-kernel reducer — the candidate already does not, and this constraint is reaffirmed.

## Time budget

≤ 15 minutes runtime. The sprint is a one-file deletion plus a re-evaluation; the existing V12.lean takes ~6 seconds to compile and ~7 seconds to audit, and the four oracle calls are already cached or sub-second. The only bookkeeping is the `git rm` (or equivalent) of the docs file, then `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V12.lean`. Soft cap 75% of context (will be far under).

## Stop conditions for the Generator

- All three acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- The Evaluator re-run shows V12 no longer scores `Cr_val = 1/32` (e.g., the candidate's bytes drifted between sprint_016 and now, or one of the oracles' certified bounds regressed) → `STATUS=BLOCKED`, naming the diff and pointing at the regressed file. Do NOT attempt to "fix" V12 by re-deriving anything; report the regression and stop.
- The Evaluator's G3 still flags an out-of-scope write (e.g., a file modified between sprint_016 and now that this contract didn't enumerate) → `STATUS=BLOCKED`, naming the offending path so the Planner can extend the allowlist in sprint_018.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
