# Sprint 024: Bump joint oracle scan resolution n_per_edge from 4096 to 8192; tighten joint_phi_phip_invD2_val to 3/125000 and uzz_phi_sq_val to 3/200000; drop Cr_val from 1/11700 to 1/31500 (2.69× reduction)

**Created**: 2026-04-30 13:00 by Planner
**Parent candidate**: `Candidates/V18.lean` (linear chain — V18 is the latest-PASS at `Cr_val = 1/11700`; sprint_024 executes the next step on the same resolution-tightening axis that sprint_023 just opened, with already-cached n=8192 oracle outputs).
**Target file**: `Candidates/V19.lean`
**Direction**: oracle-resolution-tightening (bump `n_per_edge` 4096 → 8192 in the two production-consumed joint oracles; same lever as sprint_023, second consecutive sprint on this axis). Direction-history check: sprint_021 = oracle-ceiling-tightening (rationalisation), sprint_022 = research, sprint_023 = oracle-resolution-tightening (n=2048→4096); this sprint is the *2nd* consecutive oracle-resolution sprint, well within the ≤3 same-axis cap. Wildcard cadence: last wildcard was sprint_022, so the next mandatory wildcard is sprint_026; sprint_024 can be a normal linear advance.
**Tier**: cheap — three surgical edits: bump two `n_per_edge: int = 4096` defaults to `= 8192` in `Numerical_Library/{joint_phi_phip_invD2,uzz_phi_sq}.py`, retarget two `def *_val : ℝ` literals in the candidate file, and bump one `Cr_val` literal. The new oracle outputs are **already cached** (`compute_joint_phi_phip_invD2_bound(n_per_edge=8192) = 3/125000` and `compute_uzz_phi_sq_bound(n_per_edge=8192) = 3/200000` were both run and cached during planner exploration in `Scratch/sprint_024_planner_n8192.py`), so the Evaluator's oracle reverification at G5 will hit the cache and complete in seconds. The `norm_num`-driven Cr_val arithmetic at the new literals is pure rational; no proof-engineering required. Soft cap 75% of context — should use ≤25% since the structural body of the candidate is byte-identical to V18.

## Goal (one sentence)

Drop `Cr_val` from `1/11700` (V18) to `1/31500` (V19) by bumping the two production-consumed joint oracles' `n_per_edge` default from 4096 to 8192, retargeting `joint_phi_phip_invD2_val` from `63/1000000` to `3/125000` and `uzz_phi_sq_val` from `11/250000` to `3/200000` to match the certified arb supremum rationals at the higher resolution, achieving a `2.692×` win over V18 and a cumulative `~2.58·10¹⁹×` reduction over V0.

## Mathematical insight (required, ≤ 5 sentences)

The two oracles `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` produce certified upper bounds on continuous functions by partitioning the boundary `∂Ω(δ_val, B_val) × [0, p_max]` into cells and taking interval-arithmetic upper bounds per cell; cell width is `O(1/n_per_edge)`, and the per-cell looseness shrinks roughly linearly in cell width while the bound is interval-width-dominated rather than true-value-dominated. Sprint_023 measured a -68.6% / -71.9% drop on the 2048→4096 doubling; this sprint's planner script (`Scratch/sprint_024_planner_n8192.py`, run end-to-end with both oracles cached after run) measures the *next* doubling 4096→8192: joint drops from `6.25·10⁻⁵` (rationalised `63/1000000`) to `2.40·10⁻⁵` (rationalised `3/125000`), a -61.9% reduction; uzz_phi_sq drops from `4.29·10⁻⁵` (rationalised `11/250000`) to `1.50·10⁻⁵` (rationalised `3/200000`), a -65.9% reduction. The reductions are slightly sub-linear in cell width (a halving in cell width gives ~63%/66% reduction, not 50%), confirming we are still in the cell-width-dominated regime and a further doubling (8192→16384, sprint_025 candidate) would likely give another ~2-2.5× win — but that's deferred to a future sprint. The new triangle bound `joint_n8192 + uzz_n8192/2 = 3/125000 + (1/2)·3/200000 = 63/2000000 = 3.15·10⁻⁵` is dominated by `Cr_val = 1/31500 ≈ 3.175·10⁻⁵` with a 0.78% margin (computed in `Scratch/sprint_024_planner_n8192.py`); `norm_num` closes the rational comparison cleanly. The structural form of `Cr_phi_uzz_direct_joint2 joint uzz = joint + (1/2)·uzz` (`Proof/Lib/Lemma54_Paper.lean`) is unchanged — this sprint is a pure parameter retargeting in oracle resolution, not a formula or identity change.

## Why (≤ 3 sentences, must include numerical evidence)

[`Scratch/sprint_024_planner_n8192.py`](../Scratch/sprint_024_planner_n8192.py) ran both oracles at `n_per_edge=8192` end-to-end and recorded: `compute_joint_phi_phip_invD2_bound(n_per_edge=8192).bound = 3/125000` (certified arb sup ≈ 2.40·10⁻⁵, vs V18's 63/1000000 ≈ 6.25·10⁻⁵, a -62% reduction), and `compute_uzz_phi_sq_bound(n_per_edge=8192).bound = 3/200000` (certified arb sup ≈ 1.50·10⁻⁵, vs V18's 11/250000 ≈ 4.40·10⁻⁵, a -66% reduction). The new triangle bound `joint + uzz/2 = 3/125000 + (1/2)·3/200000 = 63/2000000 = 3.15·10⁻⁵` is well below the next viable rational ceiling `1/31500 ≈ 3.175·10⁻⁵` (margin `+2.46·10⁻⁷`, +0.78% of LHS — comfortable headroom for `norm_num`); `1/31700` is even tighter (margin +0.15%) but `31500 = 2²·3²·5³·7` factors more cleanly than `31700 = 2²·5²·317` and was chosen for `norm_num` ease at minimal Cr_val cost. The new high-resolution oracle outputs are **already cached** in `Numerical_Library/.cache/` from the planner script's runs (cache verified with a zero-time second invocation in the Bash log), so the Evaluator's G5 oracle reverification hits the cache and runs in ≈10 seconds, not the 30–120 seconds a fresh scan would cost.

## Concrete edits expected

- **`ProofRefinement/Lemma54/Numerical_Library/joint_phi_phip_invD2.py`** (default-tweak, line 155):
  - Change `n_per_edge: int = 4096,` to `n_per_edge: int = 8192,` in the `compute_joint_phi_phip_invD2_bound` signature. The cache key already includes `n_per_edge`, so this just selects a different (already-populated) cache entry.
  - Update the trailing comment on the same line from `# n_per_edge=4096 from sprint_023; was 2048 in sprint_021` to `# n_per_edge=8192 from sprint_024; was 4096 in sprint_023, 2048 in sprint_021`.
  - Update the docstring's "Performance" line (≈ line 176) and the "Note safety_abs = 1e-7…" paragraph (≈ line 170) to reflect the new typical bound `≈ 2.40·10⁻⁵` and the new rationalised ceiling `3/125000` at n=8192.

- **`ProofRefinement/Lemma54/Numerical_Library/uzz_phi_sq.py`** (default-tweak, line 171):
  - Change `n_per_edge: int = 4096,` to `n_per_edge: int = 8192,` in the `compute_uzz_phi_sq_bound` signature.
  - Update the trailing comment from `# n_per_edge=4096 from sprint_023; was 2048 in sprint_020` to `# n_per_edge=8192 from sprint_024; was 4096 in sprint_023, 2048 in sprint_020`.
  - Update the docstring's "Note max_denom" paragraph (≈ lines 186–189) and "Performance" line (≈ line 191) analogously, reflecting the new bound `≈ 1.50·10⁻⁵` and rationalised ceiling `3/200000` at n=8192.

- **`ProofRefinement/Lemma54/Candidates/V19.lean`** (NEW FILE, copy-with-tweaks of V18):
  - Header comment block: identify V19 as the n=4096→8192 sprint's output; update `-- @parent Candidates/V18.lean` and `-- @sprint Sprint_Contracts/sprint_024.md`. Update the narrative paragraphs to cite the new bounds and Cr_val.
  - Update the `def joint_phi_phip_invD2_val : ℝ := 63 / 1000000` to `def joint_phi_phip_invD2_val : ℝ := 3 / 125000`. Update its docstring to state the new arb sup `≈ 2.40·10⁻⁵` and the new ceiling.
  - Update the `def uzz_phi_sq_val : ℝ := 11 / 250000` to `def uzz_phi_sq_val : ℝ := 3 / 200000`. Update its docstring analogously.
  - Update `def Cr_val : ℝ := 1 / 11700` to `def Cr_val : ℝ := 1 / 31500`. Update its docstring to show:
    - LHS = `(3/125000) + (1/2)·(3/200000) = 63/2000000`
    - Margin to `Cr_val = 1/31500` is `≈ 2.46·10⁻⁷` (`≈ 0.78%` of RHS), comfortably handled by `norm_num`.
    - Cumulative win `~2.58·10¹⁹×` over V0.
  - Body of `lemma_5_4_search` (the sink theorem): byte-identical to V18 — the proof structure (`Cr_phi_uzz_direct_joint2_nonneg`, `unfold ... ; norm_num`, `mul_le_mul_of_nonneg_right`) does not depend on the specific literals; `norm_num` handles the pure-rational arithmetic at the new values (the comparison `63/2000000 ≤ 1/31500` reduces to `63·31500 ≤ 2000000`, i.e., `1984500 ≤ 2000000`, trivially true).
  - All `theorem *_pos` and `*_nn` lemmas: byte-identical to V18 (the rationals at the new values are still trivially positive; `norm_num` closes them).
  - All other oracle declarations and `def`s: byte-identical to V18.

- **NO edits** to: `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper*.lean` (the `Cr_phi_uzz_direct_joint2` formula and the underlying `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` theorem are unchanged), `ProofRefinement/Lemma54/Proof/SearchConfig.lean`, `ProofRefinement/Lemma54/lemma.toml` (the `[[oracles]]` entries are unchanged — only the oracle's *internal* default `n_per_edge` shifts, and the cache key already encodes the new value), `LeanProof/`, `ProofGraph/`, `Evaluator.py`, any `V<K>.lean` for `K ≤ 18`, `Bulletin.md` (the Planner appends after the contract is written), or any other `Numerical_Library/` Python file (`m_phi.py`, `m_phi_prime.py`, `u_zz.py`, `m_pp.py`, `inv_F_p_z.py`, `m_bound.py`, `r_bound.py`, `_phi_loader.py`, `_arb_helpers.py`, `types.py`, `__init__.py`).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V19.lean` exits 0 (compiles clean, no `sorry`, no `admit`). Mechanically: `cd /home/rsaha/projects/grothendieck && lake env lean ProofRefinement/Lemma54/Candidates/V19.lean; echo "exit=$?"` should print `exit=0`.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V19.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer == 1 AND score.denom == 31500` (i.e., `Cr_val = 1/31500`, exactly 2.692× tighter than V18's `1/11700`). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and .score.numer == 1 and .score.denom == 31500 and .def_vals.joint_phi_phip_invD2_val == "3/125000" and .def_vals.uzz_phi_sq_val == "3/200000"'`.

3. Both oracle reverifications pass (G5): the V19 log entry's `axioms_used` array includes records for `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` and `Braverman.PaperV0.h_uzz_phi_sq_oracle`, each with `"status":"pass"` and `"oracle_bound"` matching the declared `*_val` (i.e., the certified oracle output is `≤` declared at the new resolution). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '[.axioms_used[] | select(.short == "h_joint_phi_phip_invD2_oracle" or .short == "h_uzz_phi_sq_oracle") | select(.status == "pass")] | length == 2'`.

(All three are mechanically checkable via `bash` / `jq`.)

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration, any new `[[oracles]]` entry in `lemma.toml`, or any new free-floating analytic axiom. The oracle axioms `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` already exist; this sprint changes only their *internal default* `n_per_edge` and the candidate-side `*_val` literals.
- Modify any other Numerical_Library Python file beyond the two named (`joint_phi_phip_invD2.py`, `uzz_phi_sq.py`). Specifically: do NOT touch `_arb_helpers.py` (the `cached_run` infra), `_phi_loader.py`, `m_phi.py`, `m_phi_prime.py`, `u_zz.py`, `m_pp.py`, `inv_F_p_z.py`, `m_bound.py`, `r_bound.py`, `types.py`, `__init__.py`, or any cell-scan internals.
- Modify `Proof/Lib/Lemma54_Paper*.lean`, `Proof/SearchConfig.lean`, `lemma.toml`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any candidate file `V<K>.lean` for `K ≤ 18`.
- Use `sorry`, `admit`, or `native_decide` in `V19.lean` (V18 has none; preserve that).
- Run `compute_joint_phi_phip_invD2_bound(n_per_edge=16384)` or `compute_uzz_phi_sq_bound(n_per_edge=16384)` — that is sprint_025's potential lever (or a different axis entirely if Cr plateaus); doing it here doubles the wall-time budget unnecessarily and pollutes the cache for a future sprint.
- Edit the `safety_abs`, `max_denom`, `safety_rel`, `prec`, `K_max`, `n_p_subdiv`, `delta`, `B`, `eta`, or `p_max` defaults in either oracle. The only default that changes is `n_per_edge`.
- Re-rationalise the oracle outputs at different `safety_abs` / `max_denom` (sprint_021's lever). The current values (`safety_abs = 1e-7`, `max_denom = 1000000`) already give clean rationals (`3/125000` and `3/200000`) at the new resolution; no need to retune.
- File a proposal in `Proposals/`. This sprint is a pure resolution-tightening that consumes only existing oracle infrastructure.
- Create files outside `Candidates/V19.lean` and the two oracle Python files. No new Scratch files needed (the planner script `Scratch/sprint_024_planner_n8192.py` is sufficient context). No docs, no READMEs, no test files.

## Time budget

≤ 30 minutes runtime total. Breakdown: ~5 min for the two `Numerical_Library/*.py` default tweaks (single-line edits + docstring updates); ~10 min for `Candidates/V19.lean` (cp from V18, three literal swaps, three docstring rewrites); ~5 min for `lake env lean V19.lean` to re-elaborate (cache-hit on Mathlib imports); ~5 min for `Evaluator.py V19.lean` to compile + audit + reverify oracles (oracle calls hit the planner-populated cache, ~10s each instead of 30–120s for fresh scans); ~5 min slack for `norm_num` debugging if the new literals expose any unexpected arithmetic edge case (unlikely — the underlying inequality `63/2000000 ≤ 1/31500` is `1984500 ≤ 2000000`, trivially mechanical). Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (V19 compiles, evaluator passes with `score.denom == 31500`, both oracle axioms reverify pass) → `STATUS=READY_FOR_EVALUATION`.

- `lake env lean V19.lean` fails with a `norm_num` error in the `Cr_le_Cr_val` step, despite the literals being pure rational → record the goal state, attempt `decide`, `omega`, or `linarith` as fallbacks (the underlying inequality `63·31500 ≤ 2000000`, i.e., `1984500 ≤ 2000000`, is mechanically trivial); if none close it, → `STATUS=BLOCKED`, naming the failed step and the goal state. Should not happen; preserved as a defensive stop only.

- The Evaluator's oracle reverification at the new resolution unexpectedly returns a *higher* certified bound than `3/125000` (joint) or `3/200000` (uzz_phi_sq) — this would mean the planner cache is invalid or the rationalisation is non-deterministic. Inspect the cache file (`Numerical_Library/.cache/*.json`) and the `arb_to_rational_ub` output; if cache is stale, delete the relevant entry and let the Evaluator recompute (cache-miss cost ~30–120s per oracle, well within the time budget); if rationalisation is non-deterministic, → `STATUS=BLOCKED`, naming the failure mode for sprint_025 to investigate.

- Cannot satisfy criteria without violating "Out of scope" (e.g., the sprint reveals an edge case that requires touching `Proof/Lib/Lemma54_Paper.lean` — not expected since `Cr_phi_uzz_direct_joint2` is generic over its two arguments) → `STATUS=BLOCKED`, one-paragraph reason.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — the sprint reuses existing axioms.

- Soft context cap exceeded (very unlikely) → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
