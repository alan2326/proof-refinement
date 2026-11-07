# Sprint 023: Bump joint oracle scan resolution n_per_edge from 2048 to 4096; tighten joint_phi_phip_invD2_val to 63/1000000 and uzz_phi_sq_val to 11/250000; drop Cr_val from 1/3500 to 1/11700 (3.34× reduction)

**Created**: 2026-04-30 12:30 by Planner
**Parent candidate**: `Candidates/V17.lean` (linear chain — V17 is the latest-PASS at `Cr_val = 1/3500`; sprint_022's research findings explicitly recommend the L1-RUN action that this sprint executes, so the natural parent is V17, not V0).
**Target file**: `Candidates/V18.lean`
**Direction**: oracle-resolution-tightening (bump `n_per_edge` 2048 → 4096 in the two production-consumed joint oracles; sister of sprint_018/sprint_021 ceiling-tightening, but the lever is *cell-width* not *rationalisation-tolerance*; not used in any prior sprint with this specific lever, and distinct from sprint_021's safety_abs/max_denom move). Direction-history check: sprint_020 = inline-oracle, sprint_021 = oracle-ceiling-tightening (rationalisation), sprint_022 = research; the wildcard rule (≤3 same-axis in a row) is satisfied. Wildcard cadence: last wildcard was sprint_022, so the next wildcard isn't due until sprint_026 — this sprint can be a normal linear-chain advance.
**Tier**: cheap — three surgical edits: bump two `n_per_edge: int = 2048` defaults to `= 4096` in `Numerical_Library/{joint_phi_phip_invD2,uzz_phi_sq}.py`, retarget two `def *_val : ℝ` literals in the candidate file, and bump one `Cr_val` literal. The new oracle outputs are already cached (`compute_joint_phi_phip_invD2_bound(n_per_edge=4096)` and `compute_uzz_phi_sq_bound(n_per_edge=4096)` were both run and cached during sprint_022's research script — see `Scratch/sprint_022_research.py` and `Scratch/sprint_022_research_findings.md`), so the Evaluator's oracle reverification will hit the cache and complete near-instantly. The `norm_num`-driven Cr_val arithmetic at the new literals is pure rational; no proof-engineering is required. Soft cap 75% of context — should use ≤25% since the structural body of the candidate is byte-identical to V17.

## Goal (one sentence)

Drop `Cr_val` from `1/3500` (V17) to `1/11700` (V18) by bumping the two production-consumed joint oracles' `n_per_edge` default from 2048 to 4096, retargeting `joint_phi_phip_invD2_val` from `1/5000` to `63/1000000` and `uzz_phi_sq_val` from `153/1000000` to `11/250000` to match the certified arb supreme rationals at the higher resolution, achieving a `3.34×` win over V17 and a cumulative `9.59·10¹⁸×` reduction over V0.

## Mathematical insight (required, ≤ 5 sentences)

The two oracles `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` produce **certified upper bounds on continuous functions** by partitioning the boundary `∂Ω(δ_val, B_val) × [0, p_max]` into cells and summing per-cell interval-arithmetic upper bounds; cell width is `O(1/n_per_edge)`, and as cells shrink the per-cell looseness (driven by `f(x_cell_max) - f(x_cell_min)` and by the divisor's `|D|_lb` slack on the `1/|D|^k` quotient terms) shrinks roughly linearly in cell width. Sprint_022 measured this at production parameters: doubling `n_per_edge` from 2048 to 4096 reduced the joint sup from `1.989·10⁻⁴` to `6.250·10⁻⁵` (a `−68.6%` change) and the uzz_phi_sq sup from `1.525·10⁻⁴` to `4.288·10⁻⁵` (a `−71.9%` change). Both reductions are well above the value-precision floor (the certified arb intervals have ±5e-25 / ±3e-25 radii, so the bound *is* genuinely interval-width-dominated rather than true-value-dominated, meaning further halvings would continue to shrink — but this sprint exhausts the immediately-actionable single-doubling lever, deferring `n_per_edge=8192` to sprint_024 if the wall-time budget allows). The new triangle bound `joint_n4096 + uzz_n4096/2 = 63/1000000 + (1/2)·11/250000 = 17/200000 = 8.5·10⁻⁵` is dominated by `Cr_val = 1/11700 ≈ 8.547·10⁻⁵` with a 0.55% safety margin (computed in `Scratch/sprint_023_planner_cr_val_optimum.py`); `norm_num` closes the rational comparison cleanly. The structural form of `Cr_phi_uzz_direct_joint2 joint uzz = joint + (1/2)·uzz` (Proof/Lib/Lemma54_Paper.lean:567) is unchanged — this sprint is a pure parameter retargeting in oracle resolution, not a formula or identity change.

## Why (≤ 3 sentences, must include numerical evidence)

[`Scratch/sprint_022_research_findings.md`](../Scratch/sprint_022_research_findings.md) (the deliverable of sprint_022's wildcard research run) committed to the L1-RUN recommendation: at `n_per_edge=4096`, `joint_phi_phip_invD2` drops from `1.989·10⁻⁴` to `6.250·10⁻⁵` (rationalised to `63/1000000`) and `uzz_phi_sq` drops from `1.525·10⁻⁴` to `4.289·10⁻⁵` (rationalised to `11/250000`), giving a new triangle bound of `17/200000 = 8.5·10⁻⁵` versus V17's `5.50·10⁻⁴`. [`Scratch/sprint_023_planner_cr_val_optimum.py`](../Scratch/sprint_023_planner_cr_val_optimum.py) computes the optimal new `Cr_val := 1/11700`: the tightest integer-denominator dominator is `1/11764` (margin `0.006%`, knife-edge), but `1/11700` (margin `0.55%`) is preferred for arithmetic headroom, and yields a `3.34×` win on Cr_val over V17's `1/3500`. The new high-resolution oracle outputs are **already cached** in `Numerical_Library/.cache/` from sprint_022's `Scratch/sprint_022_research.py` invocations, so the Evaluator's G5 oracle reverification will hit the cache and run in ≈10 seconds, not the 30–120 seconds a fresh scan would cost.

## Concrete edits expected

- **`ProofRefinement/Lemma54/Numerical_Library/joint_phi_phip_invD2.py`** (default-tweak, lines 149–162):
  - Change `n_per_edge: int = 2048,` to `n_per_edge: int = 4096,` in the `compute_joint_phi_phip_invD2_bound` signature (around line 155). The cache key already includes `n_per_edge`, so this just selects a different (already-populated) cache entry; no upstream caller passes `n_per_edge` explicitly (the Evaluator calls `fn()` with no kwargs at `Evaluator.py:331`).
  - Update the docstring's "Performance" line (≈ line 177) from "scans 4·n_per_edge·n_p_subdiv ≈ 32k cells at n_per_edge=2048, prec=200" to "scans 4·n_per_edge·n_p_subdiv ≈ 64k cells at n_per_edge=4096, prec=200; sprint_022 cache populated, so cached call is near-instant".
  - Update the "Note `safety_abs = 1e-7` ..." paragraph (≈ lines 170–175) to reflect the new typical bound `≈ 6.25·10⁻⁵` and the new rationalised ceiling `63/1000000` (the existing `safety_abs = 1e-7, max_denom = 1000000` are already correct for the new value; do not change them).
  - Optional: append a one-line comment near the signature noting "n_per_edge=4096 from sprint_023; was 2048 in sprint_021".

- **`ProofRefinement/Lemma54/Numerical_Library/uzz_phi_sq.py`** (default-tweak, mirrored):
  - Change `n_per_edge: int = 2048,` to `n_per_edge: int = 4096,` in the `compute_uzz_phi_sq_bound` signature (around line 171).
  - Update the docstring's "Performance" line analogously.
  - Optional: append a one-line comment noting "n_per_edge=4096 from sprint_023; was 2048 in sprint_020".

- **`ProofRefinement/Lemma54/Candidates/V18.lean`** (NEW FILE, copy-with-tweaks of V17):
  - Header comment block: identify V18 as the L1-RUN sprint's output; drop the V17 wildcard explanation paragraph; update `-- @parent Candidates/V17.lean` and `-- @sprint Sprint_Contracts/sprint_023.md`.
  - Update the `def joint_phi_phip_invD2_val : ℝ := 1 / 5000` (line 103) to `def joint_phi_phip_invD2_val : ℝ := 63 / 1000000`. Update its docstring to state the new arb sup `≈ 6.25·10⁻⁵` and the new ceiling.
  - Update the `def uzz_phi_sq_val : ℝ := 153 / 1000000` (line 112) to `def uzz_phi_sq_val : ℝ := 11 / 250000`. Update its docstring analogously.
  - Update `def Cr_val : ℝ := 1 / 3500` (line 153) to `def Cr_val : ℝ := 1 / 11700`. Update its docstring (lines 146–152) to show:
    - LHS = `(63/1000000) + (1/2)·(11/250000) = 17/200000`
    - Margin to `Cr_val = 1/11700` is `≈ 4.7·10⁻⁷` (`≈ 0.55%` of RHS), comfortably handled by `norm_num`.
  - Body of `lemma_5_4_search` (the sink theorem): byte-identical to V17 — the proof structure (`Cr_phi_uzz_direct_joint2_nonneg`, `unfold ... ; norm_num`, `mul_le_mul_of_nonneg_right`) does not depend on the specific literals; `norm_num` handles the pure-rational arithmetic at the new values.
  - All `theorem *_pos` and `*_nn` lemmas: byte-identical to V17 (the rationals at the new values are still trivially positive; `norm_num` closes them).
  - All other oracle declarations and `def`s: byte-identical to V17.

- **NO edits** to: `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper*.lean` (the `Cr_phi_uzz_direct_joint2` formula and the underlying `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` theorem are unchanged), `ProofRefinement/Lemma54/Proof/SearchConfig.lean`, `ProofRefinement/Lemma54/lemma.toml` (the `[[oracles]]` entries are unchanged — only the oracle's *internal* default `n_per_edge` shifts, and the cache key already encodes the new value), `LeanProof/`, `ProofGraph/`, `Evaluator.py`, any `V<K>.lean` for `K ≤ 17`, `Bulletin.md` (the Planner appends after the contract is written), or any other `Numerical_Library/` Python file (`m_phi.py`, `m_phi_prime.py`, `u_zz.py`, `m_pp.py`, `inv_F_p_z.py`, `m_bound.py`, `r_bound.py`, `_phi_loader.py`, `_arb_helpers.py`, `types.py`, `__init__.py`).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V18.lean` exits 0 (compiles clean, no `sorry`, no `admit`). Mechanically: `cd /home/rsaha/projects/grothendieck && lake env lean ProofRefinement/Lemma54/Candidates/V18.lean; echo "exit=$?"` should print `exit=0`.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V18.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer == 1 AND score.denom == 11700` (i.e., `Cr_val = 1/11700`, exactly 3.34× tighter than V17's `1/3500`). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; assert r["score"]["numer"] == 1 and r["score"]["denom"] == 11700, r["score"]; print(f"V18 Cr_val = {r[chr(34)+chr(115)+chr(99)+chr(111)+chr(114)+chr(101)+chr(34)]}; oracle ceilings: joint={r[chr(34)+chr(100)+chr(101)+chr(102)+chr(95)+chr(118)+chr(97)+chr(108)+chr(115)+chr(34)][chr(34)+chr(106)+chr(111)+chr(105)+chr(110)+chr(116)+chr(95)+chr(112)+chr(104)+chr(105)+chr(95)+chr(112)+chr(104)+chr(105)+chr(112)+chr(95)+chr(105)+chr(110)+chr(118)+chr(68)+chr(50)+chr(95)+chr(118)+chr(97)+chr(108)+chr(34)]}, uzz_phi_sq={r[chr(34)+chr(100)+chr(101)+chr(102)+chr(95)+chr(118)+chr(97)+chr(108)+chr(115)+chr(34)][chr(34)+chr(117)+chr(122)+chr(122)+chr(95)+chr(112)+chr(104)+chr(105)+chr(95)+chr(115)+chr(113)+chr(95)+chr(118)+chr(97)+chr(108)+chr(34)]}")'`. (Equivalent simpler form: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and .score.numer == 1 and .score.denom == 11700 and .def_vals.joint_phi_phip_invD2_val == "63/1000000" and .def_vals.uzz_phi_sq_val == "11/250000"'`.)

3. Both oracle reverifications pass (G5): the V18 log entry's `axioms_used` array includes records for `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` and `Braverman.PaperV0.h_uzz_phi_sq_oracle`, each with `"status":"pass"` and `"oracle_bound"` matching the declared `*_val` (i.e., the certified oracle output is `≤` declared at the new resolution). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '[.axioms_used[] | select(.short == "h_joint_phi_phip_invD2_oracle" or .short == "h_uzz_phi_sq_oracle") | select(.status == "pass")] | length == 2'`.

(All three are mechanically checkable via `bash` / `jq` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration, any new `[[oracles]]` entry in `lemma.toml`, or any new free-floating analytic axiom. The oracle axioms `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` already exist; this sprint changes only their *internal default* `n_per_edge` and the candidate-side `*_val` literals.
- Modify any other Numerical_Library Python file beyond the two named (`joint_phi_phip_invD2.py`, `uzz_phi_sq.py`). Specifically: do NOT touch `_arb_helpers.py` (the `cached_run` infra), `_phi_loader.py`, `m_phi.py`, `m_phi_prime.py`, `u_zz.py`, `m_pp.py`, `inv_F_p_z.py`, `m_bound.py`, `r_bound.py`, `types.py`, `__init__.py`, or any cell-scan internals.
- Modify `Proof/Lib/Lemma54_Paper*.lean`, `Proof/SearchConfig.lean`, `lemma.toml`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any candidate file `V<K>.lean` for `K ≤ 17`.
- Use `sorry`, `admit`, or `native_decide` in `V18.lean` (V17 has none; preserve that).
- Run `compute_joint_phi_phip_invD2_bound(n_per_edge=8192)` or `compute_uzz_phi_sq_bound(n_per_edge=8192)` — that is sprint_024's lever if Cr_val plateaus before exhausting the resolution axis; doing it here doubles the wall-time budget unnecessarily.
- Edit the `safety_abs`, `max_denom`, `safety_rel`, `prec`, `K_max`, `n_p_subdiv`, `delta`, `B`, `eta`, or `p_max` defaults in either oracle. The only default that changes is `n_per_edge`.
- Re-rationalise the oracle outputs at different `safety_abs` / `max_denom` (sprint_021's lever). The current values (`safety_abs = 1e-7`, `max_denom = 1000000`) already give clean rationals (`63/1000000` and `11/250000`) at the new resolution; no need to retune.
- File a proposal in `Proposals/`. This sprint is a pure resolution-tightening that consumes only existing oracle infrastructure.
- Create files outside `Candidates/V18.lean` and the two oracle Python files. No new Scratch files needed (the planner script `Scratch/sprint_023_planner_cr_val_optimum.py` is sufficient context). No docs, no READMEs, no test files.

## Time budget

≤ 30 minutes runtime total. Breakdown: ~5 min for the two `Numerical_Library/*.py` default tweaks (single-line edits + docstring updates); ~10 min for `Candidates/V18.lean` (cp from V17, three literal swaps, three docstring rewrites); ~5 min for `lake env lean V18.lean` to re-elaborate (cache-hit on Mathlib imports); ~5 min for `Evaluator.py V18.lean` to compile + audit + reverify oracles (oracle calls hit the sprint_022 cache, ~10s each instead of 60–120s for fresh scans); ~5 min slack for `norm_num` debugging if the new literals expose any unexpected arithmetic edge case (unlikely — the formula is `joint + uzz/2 = 17/200000 ≤ 1/11700` is pure rational comparison `17·11700 ≤ 200000`, i.e., `198900 ≤ 200000`, easily handled). Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (V18 compiles, evaluator passes with `score.denom == 11700`, both oracle axioms reverify pass) → `STATUS=READY_FOR_EVALUATION`.

- `lake env lean V18.lean` fails with a `norm_num` error in the `Cr_le_Cr_val` step, despite the literals being pure rational → record the goal state, attempt `decide`, `omega`, or `linarith` as fallbacks (the underlying inequality `17·11700 ≤ 200000` is mechanically trivial); if none close it, → `STATUS=BLOCKED`, naming the failed step and the goal state. Should not happen; preserved as a defensive stop only.

- The Evaluator's oracle reverification at the new resolution unexpectedly returns a *higher* certified bound than `63/1000000` (joint) or `11/250000` (uzz_phi_sq) — this would mean the sprint_022 cache is invalid or the rationalisation is non-deterministic. Inspect the cache file (`Numerical_Library/.cache/*.json`) and the `arb_to_rational_ub` output; if cache is stale, delete the relevant entry and let the Evaluator recompute (cache-miss cost ~60–120s per oracle, well within the time budget); if rationalisation is non-deterministic, → `STATUS=BLOCKED`, naming the failure mode for sprint_024 to investigate.

- Cannot satisfy criteria without violating "Out of scope" (e.g., the sprint reveals an edge case that requires touching `Proof/Lib/Lemma54_Paper.lean` — not expected since `Cr_phi_uzz_direct_joint2` is generic over its two arguments) → `STATUS=BLOCKED`, one-paragraph reason.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — the sprint reuses existing axioms.

- Soft context cap exceeded (very unlikely) → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
