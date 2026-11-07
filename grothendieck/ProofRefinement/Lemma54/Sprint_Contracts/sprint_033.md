# Sprint 033: Re-baseline V27 onto truncation-free oracles via V11's `Cr_phi_uzz` formula; first post-K_max-patch PASS at `Cr_val = 1/3`

**Created**: 2026-05-03 04:00 by Planner
**Parent candidate**: `Candidates/V11.lean` (NOT V26 — branching from V11 because V11's `Cr_phi_uzz` formula has the lowest patched audit floor (0.3255) per `PATCH_NOTES.md` §3, and V12-V26's "joint" / "merged" formulas have STRICTLY LOOSER audit floors (V14: 0.281 *misleadingly* lower but only because it uses the joint_phi_phip_invD2 oracle alone; V15-V24: 0.4105; V25-V26: 0.3734) when re-evaluated with the post-patch truncation-free oracles. V11's pure-scalar formula is the structural sweet spot.)
**Target file**: `Candidates/V27.lean`
**Direction**: `truncation-free re-baselining` — first sprint post-K_max-patch (PATCH_NOTES.md, 2026-05-03). Wire the candidate's four scalar η-aware oracles (`M_phi`, `M_phi_prime`, `inv_F_p_z`, `M_pp`) onto the rigorous `Numerical_Library.truncfree.round3` ceilings (replacing V11's K_max-truncated values), and set `Cr_val` to a literal rational that dominates both the rationalised `Cr_phi_uzz` formula AND the round3 audit floor. This satisfies G7 (TRUNCATION_REGRESSION + AUDIT_FLOOR_VIOLATION). Direction not used in any of the prior 3 sprints (sprint_030 = formula-change merged-numerator, sprint_031 = oracle-resolution-tightening, sprint_032 = oracle-resolution+ceiling tightening, all on the K_max-invalid `merged_uderiv` axis). It also resets the trajectory off the `merged_uderiv` lever that PATCH_NOTES.md just nuked.
**Tier**: `ambitious` — non-trivial Lean and Python integration work. Requires (a) replacing four `[[oracles]]` entries' `oracle_fn` in `lemma.toml` to point at the new `compute_*_truncfree_bound` functions; (b) writing a new candidate that imports the V11-style proof body but with retargeted ceiling literals; (c) writing the PATCH_NOTES R5 audit-block header with the round3 audit JSON path and Cr_patched(V27) value; (d) verifying the resulting candidate audits correctly under G7. Several compile-edit cycles likely.

## Goal (one sentence)

Produce `Candidates/V27.lean` proving Lemma 5.4 with `Cr_val = 1/3 (≈ 0.333)` using V11's `Cr_phi_uzz` proof structure but with all four scalar η-aware oracle ceilings retargeted to the truncation-free round3 rationalised values (`M_phi = 231143/10000000`, `M_phi_prime = 905139/2500000`, `inv_F_p_z = 1424571/400000`, `M_pp = 185260647/10000000`) sourced from `Numerical_Library.truncfree.round3`, with the PATCH_NOTES R5 audit-block header naming `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` and recording `Cr_patched(V27) = 0.32551` (V11-formula audit) — establishing V27 as the first post-K_max-patch PASS and the new latest-PASS candidate.

## Mathematical insight (required, ≤ 5 sentences)

The K_max-truncation regression (PATCH_NOTES.md, 2026-05-03) means every "win" from V12 to V26 was illusory: the declared `Cr_val ∈ {1/32, …, 1/268000}` numbers were all bounded by oracles whose tail estimates were heuristic. Per the PATCH_NOTES §3 audit table, V11's `Cr_phi_uzz` formula re-evaluated with truncation-free oracles + 3 rounds of corner subdivision gives `Cr_patched = 0.3255` — the **lowest patched value across all 26 candidates** (V14's joint-only formula is 0.281 but combines a different oracle set; V15-V24 are 0.41+, V25-V26 0.37+). The mathematical content of this sprint is therefore: **(a)** recognise V11's pure-scalar `Cr_phi_uzz = M_phi·M_phi_prime·invFp² + (1/2)·M_pp·invFp³·M_phi²` as the post-patch structural optimum among the existing formula variants, and **(b)** plug in the round3 truncation-free ceilings (`M_phi ≈ 0.0231`, `M_phi_prime ≈ 0.362`, `inv_F_p_z ≈ 3.561`, `M_pp ≈ 18.526`) — all ~10× tighter than V11's K_max-era declared values (V11 had `M_phi=239/5000=0.0478`, `M_phi_prime=543/10000=0.0543`, `inv_F_p_z=2`, `M_pp=5608/100=56.08`) because the round3 subdivision pinned down the oracles' actual rigorous bounds — yielding `Cr_phi_uzz_rationalised = 0.3297` and a tight literal `Cr_val = 1/3 ≈ 0.333` with +1.10% margin against the formula and +2.4% against the audit floor. No new identity, no new contour, no new oracle — purely a re-baselining onto already-built infrastructure.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_033_planner_options.py` computes the round3 truncation-free rationalised oracle ceilings via `Numerical_Library.truncfree.round3()` and shows that V11's `Cr_phi_uzz` formula evaluated at those ceilings gives `Cr_phi_uzz_rationalised = 42201918532432123223367356344538861733/128000000000000000000000000000000000000 ≈ 0.32970` (term1 = 0.1061, term2 = 0.2236), so `Cr_val = 1/3 ≈ 0.33333` dominates the formula by `1/3 − Cr_phi_uzz ≈ 3.63·10⁻³` (margin +1.10%) AND dominates the round3 audit floor `Cr_patched(V11) = 0.32551` (PATCH_NOTES §3) by margin +2.4%. This is the **only `Cr_val < 1` PASS reachable today under R1-R5** without new structural work — V14's joint-formula audit (0.281) requires reviving 2 different oracles (joint_phi_phip_invD2 and uzz_phi_sq) which the V11 proof chain doesn't consume; V12-V26 score literals are all unreachable per PATCH_NOTES until additional subdivision rounds drop the audit floor further, which is months of work. The reduction is `1/3 vs V11's declared 1` = **3× tighter Cr_val** than V11, and crucially establishes the **first rigorously-PASS-ing post-K_max-patch candidate**, replacing the entire V12-V26 invalidated trajectory.

## Concrete edits expected

1. **`ProofRefinement/Lemma54/Scratch/sprint_033_verify_round3.py`** (NEW — Generator-side verification before structural commit):
   - Import `Numerical_Library.truncfree.round3` and obtain a `TruncFreeBundle`.
   - Call `b.as_oracle_result(name)` for each of `M_phi`, `M_phi_prime`, `inv_F_p_z`, `M_pp` at the *contract-stipulated* rationaliser settings (`safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7`) — these MUST match the literals encoded in V27.
   - Assert that the four returned `bound` Fractions exactly equal the contract values: `M_phi = 231143/10000000`, `M_phi_prime = 905139/2500000`, `inv_F_p_z = 1424571/400000`, `M_pp = 185260647/10000000`.
   - Compute `Cr_phi_uzz = M_phi*M_phi_prime*inv_F_p_z² + (1/2)*M_pp*inv_F_p_z³*M_phi²` exactly via `fractions.Fraction`, assert `Cr_phi_uzz <= Fraction(1, 3)`, and write `DECISION: viable` with the four bounds, the formula value, and the `1/3 − Cr_phi_uzz` margin into `Scratch/sprint_033_verify_round3.txt`. If any rationaliser bound differs from the contract value (e.g., due to upstream changes in the round3 cache), write `DECISION: dead` with the actual values.

2. **`ProofRefinement/Lemma54/lemma.toml`** (rewire four `[[oracles]]` entries to truncation-free):
   - Change the `oracle_fn` field of the entry with `bound_field = "M_phi_val"` from `"compute_M_phi_bound"` to `"compute_M_phi_truncfree_bound"`.
   - Same pattern for `M_phi_prime_val` → `"compute_M_phi_prime_truncfree_bound"`.
   - Same pattern for `inv_F_p_z_val` → `"compute_inv_F_p_z_truncfree_bound"`.
   - Same pattern for `M_pp_val` → `"compute_M_pp_truncfree_bound"`.
   - Leave the other five `[[oracles]]` entries (`M_val`, `u_zz_bound_val`, `joint_phi_phip_invD2_val`, `uzz_phi_sq_val`, `merged_uderiv_val`) UNCHANGED — V27 doesn't consume them, but V0..V26 still need their existing oracle_fn registrations for the grandfathered audit (G7 SKIPS them per PATCH_NOTES). Touching their wiring would gratuitously impact V0..V26 reproducibility.

3. **`ProofRefinement/Lemma54/Numerical_Library/__init__.py`** (re-export the four truncfree functions so `oracle_fn` lookup works):
   - Add to the `__all__` (or equivalent) and the import block: `compute_M_phi_truncfree_bound`, `compute_M_phi_prime_truncfree_bound`, `compute_inv_F_p_z_truncfree_bound`, `compute_M_pp_truncfree_bound`. They're already exported from `Numerical_Library.truncfree` per its `__init__.py`; the candidate's runtime audit looks up `oracle_fn` against `Numerical_Library` directly, so the names must be reachable as `Numerical_Library.<name>`. (If `__init__.py` already does `from .truncfree import *`, no edit needed — verify first.)

4. **`ProofRefinement/Lemma54/Candidates/V27.lean`** (NEW — copy `V11.lean` then patch):
   - Update header narrative: V27 is the **truncation-free re-baseline**, parent `Candidates/V11.lean`, sprint `Sprint_Contracts/sprint_033.md`. Cite `Scratch/sprint_033_verify_round3.txt` for oracle values, `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` for the audit floor, and `PATCH_NOTES.md` rules R1-R5 for the rigor regime.
   - Insert the **PATCH_NOTES R5 audit-block header** (mandatory per AGENT_BRIEF constraint #8 and PATCH_NOTES R5):
     ```lean
     /-
       AUDIT: Cr_phi_uzz(M_phi, M_phi_prime, inv_F_p_z, M_pp) ≤ Cr_val
              under PATCH_NOTES rules.
       Source chunks: Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json
       Source audit:  Cache/Backups/2026-05-03_subdivision/audit_naive_results.json
       Cr_patched(this candidate) = 0.32551055319967653
         (= V11 row of audit_naive_results.json; same Cr_phi_uzz formula)
       Cr_val = 1/3 ≈ 0.33333  (margin +2.40% over Cr_patched)
     -/
     ```
   - Update `M_phi_val`: `239 / 5000` → `231143 / 10000000`.
   - Update `M_phi_prime_val`: `543 / 10000` → `905139 / 2500000`.
   - Update `inv_F_p_z_val`: `2` → `1424571 / 400000`.
   - Update `M_pp_val`: `5608 / 100` → `185260647 / 10000000`.
   - Update `Cr_val`: `1` → `1 / 3`.
   - Update the `_pos` / `_nn` lemmas to handle the new rationals (mostly a `norm_num` rerun; the literals are all positive).
   - Update the dominance step in `lemma_5_4_search`: the `nlinarith`/`norm_num` proof that `Cr_phi_uzz r M_phi_val M_phi_prime_val inv_F_p_z_val M_pp_val ≤ Cr_val` now must verify the strict rational inequality `(231143/10000000)·(905139/2500000)·(1424571/400000)² + (1/2)·(185260647/10000000)·(1424571/400000)³·(231143/10000000)² ≤ 1/3`. The Generator should chain `unfold Cr_phi_uzz; show ...; norm_num` (Lean's `norm_num` handles arbitrary rational arithmetic exactly). If `norm_num` chokes on the polynomial expression size, fall back to introducing intermediate `have` rewrites for `term1` and `term2` separately, then summing — same pattern V11 already uses but with the new literals.
   - The five carried-over oracles (`h_M_oracle`, `h_oracle_domain_contains_image`, plus the four scalar η-aware ones with retargeted bounds) keep the same Lean `axiom` declarations and signatures; only the `def *_val` literals change, so the Lean-side `axiom` body refers to `M_phi_val` etc. as before.
   - All other definitions/theorems byte-identical to V11.

5. **`ProofRefinement/Lemma54/Bulletin.md`**: the Planner appends after the contract is queued (NOT the Generator).

6. **NO edits** to: `Proof/SearchConfig.lean`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, any `Numerical_Library/*.py` *other than* `__init__.py` (specifically: do NOT modify the deprecated `m_phi.py`, `m_phi_prime.py`, etc., — they stay deprecated for V0..V26 backwards-compat per PATCH_NOTES R4), any `Proof/Lib/Lemma54_Paper*.lean` (no new Lean theorems — V11's `lemma_5_4_paper_on_domain_phi_uzz` is reused as-is), `Proposals/proposal_*.md` (proposal_003 stays pending), any `V<K>.lean` for `K ≤ 26`, any `Sprint_Contracts/sprint_<K>.md` for `K < 033`, `_archive/`, `PATCH_NOTES.md`.

## Acceptance criteria

1. **Verification probe shows the four truncfree ceilings match the contract literals**: `test -s ProofRefinement/Lemma54/Scratch/sprint_033_verify_round3.txt && grep -E '^DECISION: viable' ProofRefinement/Lemma54/Scratch/sprint_033_verify_round3.txt` exits 0. The probe MUST assert the exact rational equality (using `Fraction.__eq__`) of all four `bound` values to the contract literals; if `as_oracle_result` returns a different rationalisation (e.g., upstream `arb_to_rational_ub` precision changed), the probe writes `DECISION: dead` and the Generator stops.

2. **V27 compiles and evaluates with `Cr_val = 1/3`**: `lake env lean ProofRefinement/Lemma54/Candidates/V27.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V27.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer == 1` AND `score.denom == 3`. Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and .score.numer == 1 and .score.denom == 3'`.

3. **All four retargeted oracles re-certify under truncation-free path AND G7 passes (no AUDIT_FLOOR_VIOLATION)**: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.axioms_used | map(select(.kind == "oracle" and (.short | test("M_phi|M_phi_prime|inv_F_p_z|M_pp")))) | length == 4 and (all(.; .status == "pass"))'` exits 0. AND the Evaluator's G7 must pass (no `TRUNCATION_REGRESSION` or `AUDIT_FLOOR_VIOLATION` in the run output) — the audit-block header in V27 must satisfy `Cr_patched_float = 0.32551055319967653 < Cr_val_float = 0.33333...`.

(All three criteria are mechanically checkable via `bash` / `grep` / `jq`.)

## Out of scope (Generator MUST NOT do)

- **Add any new axiom** (oracle-shaped or otherwise). V27 reuses V11's six axioms (3 Lean primitives are not counted; 12 trusted analytic + h_M_oracle + h_oracle_domain_contains_image + the four scalar η-aware oracles); only their numeric literals change. No `axiom` declarations are added.
- **Modify** `Proof/SearchConfig.lean` (locked at `eta = 1/100, r = 23/25`).
- **Modify** `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 26`.
- **Modify** any `Proof/Lib/Lemma54_Paper*.lean` — V11's proof structure (`lemma_5_4_paper_on_domain_phi_uzz`, `Cr_phi_uzz`, `F_inv_p_second_deriv_bound_phi_uzz`) is reused exactly. The only Lean-side changes are the five literal rational `def *_val` values in V27.lean.
- **Modify** any `Numerical_Library/*.py` other than `__init__.py` (and only if the truncfree functions aren't already re-exported there). Do NOT delete or alter the deprecated `m_phi.py`, `m_phi_prime.py`, `m_pp.py`, `inv_F_p_z.py` etc. — they stay for V0..V26 backwards-compat per PATCH_NOTES R4.
- **Modify** `Sprint_Contracts/sprint_<K>.md` for `K < 033` or `Proposals/proposal_*.md`. Proposal_003 (wider analyticity domain) is still pending — do NOT consume or reference it; this sprint is independent.
- **Use** `sorry`, `admit`, or `native_decide`. The literal rational dominance check `Cr_phi_uzz ≤ 1/3` must be discharged by `norm_num` (preferred) or a chain of `nlinarith` with explicit hypotheses, mirroring V11's pattern.
- **Branch** from any candidate other than V11. Sprint_032 was queued for V27 against V26 but is now superseded by PATCH_NOTES; V11 is the structural sweet spot per the audit table.
- **Pick a tighter `Cr_val`** than `1/3`. The next planner can iterate on `Cr_val` after V27 establishes the baseline; tightening to `Cr_val = 33/100 = 0.33` is technically safe (margin +0.09%) but leaves no rounding slack for `norm_num`. Stick with `1/3` for this sprint.
- **Skip** the audit-block header (R5 requirement). The Evaluator's G7 will fail without it.
- **Skip** the verify probe (criterion #1). The Lean-side literals must be byte-faithful to the truncfree round3 rationalised values; the probe is what guarantees that.
- **Switch oracle source** away from `round3`. The `production` cache gives `Cr_patched(V11) = 4.22` — far above `1/3` — so V27 would fail G7. Round3 is the only viable source.
- **File a fourth proposal**. Budget remains 1/3 pending (proposal_003).

## Time budget

≤ 180 minutes runtime total (ambitious tier). Breakdown:
- ~5 min: run the verify probe (`Numerical_Library.truncfree.round3()` is JSON-load fast, sub-second).
- ~5 min: `lemma.toml` four-line edit + smoke-test that the Evaluator can resolve the new `oracle_fn` names.
- ~5 min: `Numerical_Library/__init__.py` re-export edit (if needed; check first).
- ~30 min: clone V11 → V27, update five literal rationals, update `_pos`/`_nn` lemmas, update header, insert audit-block header.
- ~45 min: re-prove the dominance step `Cr_phi_uzz ... ≤ 1/3` — the literals are large (denominators up to ~10⁷), so `norm_num` may need staging via intermediate `have` lemmas for each term. Allow several compile-edit cycles for the `nlinarith` margin.
- ~10 min: smoke-test V27 with `lake env lean` and `Evaluator.py --skip-oracle --no-log`.
- ~15 min: full `Evaluator.py` run (oracle re-certification + G7 audit; round3 cache is JSON-load fast, ~2s).
- ~65 min slack for compile-edit cycles, especially on the `norm_num` arithmetic (this is the riskiest step).

Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (verify probe `viable`; V27 compiles + evaluates with `Cr_val = 1/3`; four oracles re-certify with `status: pass`; G7 passes with `Cr_patched = 0.32551 < 1/3`) → `STATUS=READY_FOR_EVALUATION`.

- Verify probe at `safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7` returns oracle bounds that DIFFER from the contract literals (e.g., due to upstream changes in `arb_to_rational_ub` or the round3 chunks JSON) → write `DECISION: dead` in the probe output naming the actual values, → `STATUS=BLOCKED`. The next Planner reads the probe output and re-issues the contract with the corrected literals.

- The dominance step `Cr_phi_uzz_at_round3_rationals ≤ 1/3` cannot be discharged by `norm_num` within reasonable compile time (>5 min for one `norm_num` call) → fall back to a staged proof: introduce `have h_term1 : M_phi_val * M_phi_prime_val * inv_F_p_z_val^2 ≤ 11/100 := by norm_num` and `have h_term2 : (1/2) * M_pp_val * inv_F_p_z_val^3 * M_phi_val^2 ≤ 23/100 := by norm_num` (the bounds 11/100 and 23/100 come from the planner script: term1 ≈ 0.106 < 0.11, term2 ≈ 0.224 < 0.23, sum 0.34 still > 1/3 — REJECT, retry with tighter intermediate bounds e.g. term1 ≤ 107/1000 = 0.107 and term2 ≤ 224/1000 = 0.224, sum 0.331 < 1/3 ✓). The Generator should iterate on the intermediate bounds until both `norm_num`s close and the sum ≤ 1/3.

- Lemma.toml `oracle_fn` rewiring causes `Numerical_Library` to fail importing the truncfree functions (e.g., circular import) → fall back to leaving lemma.toml's `oracle_fn` strings UNCHANGED but adding new entries pointing at the truncfree variants AND deleting the four old entries — but this requires more invasive lemma.toml restructuring and would touch V0..V26's audit. If this fallback is needed, → `STATUS=BLOCKED` with the import error recorded; the next Planner repairs the import path.

- Acceptance criteria require a non-oracle axiom or a wider analyticity domain (proposal_003 pending) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — this sprint is purely an oracle-ceiling re-baselining + literal rational tightening on existing infrastructure.

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
