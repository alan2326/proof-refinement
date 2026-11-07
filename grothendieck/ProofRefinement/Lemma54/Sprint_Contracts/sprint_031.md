# Sprint 031: Bump merged_uderiv oracle resolution `n_per_edge` from 262144 to 524288; tighten `merged_uderiv_val` and drop `Cr_val` from `1/240000` to ≤ `1/280000`

**Created**: 2026-04-30 13:15 by Planner
**Parent candidate**: `Candidates/V25.lean` (linear chain — V25 is the latest-PASS, sprint_030's merged-numerator structural pivot at `Cr_val = 1/240000`).
**Target file**: `Candidates/V26.lean`
**Direction**: `oracle-resolution-tightening` on the new merged_uderiv oracle (last used in sprint_028 on the legacy joint+uzz oracles; the merged oracle is the V25-active path's sole consumed bound, so this axis is fresh on the new oracle and the no-3-in-a-row rule is satisfied — sprints 028/029/030 used three different axes [oracle-resolution-tightening, research+proposal-filing, formula-change/merged-numerator]).
**Tier**: `cheap` — surgical: bump one default kwarg in `Numerical_Library/merged_uderiv.py`, re-run the oracle once at the new resolution, rationalise, and clone V25 with two updated rationals (`merged_uderiv_val`, `Cr_val`). No new Lean theorems, no new oracles, no new axioms; the oracle's *axiom statement* and *signature* are unchanged — only its *numerical* declared value tightens.

## Goal (one sentence)

Re-run `compute_merged_uderiv_bound` at `n_per_edge=524288` (one resolution doubling above V25's 262144), rationalise the new ball value at the existing `safety_abs=1e-8, max_denom=10⁷` settings, and produce `Candidates/V26.lean` with `merged_uderiv_val` updated to the new rational and `Cr_val` set to a literal `1/<DENOM>` that strictly dominates `(1/2) · merged_uderiv_val_new` and is strictly less than `1/240000` (target `1/280000` or tighter, projected `~1/295000`).

## Mathematical insight (required, ≤ 5 sentences)

V25's merged-numerator oracle bounds `sup_{p,w} ‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³` (the *exact* `|u''|` quotient by the form-A identity), and its arb-certified `ball_value` shrinks monotonically with the boundary discretisation `n_per_edge` because the per-cell `acb` interval slack on the merged numerator's destructive-interference cancellation tightens linearly in cell-width. The active inequality in `lemma_5_4_paper_on_domain_phi_uzz_merged` is `‖u''‖ ≤ merged_uderiv_val`, so any tighter rationalised certificate on the same analytic quantity directly tightens `Cr_phi_uzz_merged = (1/2)·merged_uderiv_val` and hence `Cr_val`. The mathematical content is not new: this sprint reuses the *same* form-A identity and the *same* oracle signature shipped in V25; the gain comes purely from a finer boundary partition resolving more of the integrand's actual variability rather than its interval-arithmetic over-estimate. Per-doubling history of `merged_sup` (`Scratch/sprint_030_verify_n262144.txt` plus `Scratch/sprint_030_merged_n131072.txt`) shows a constant ~17% absolute drop per `n_per_edge` doubling: `n=131072: 9.7548·10⁻⁶ → n=262144: 8.0865·10⁻⁶`. Projecting one more doubling gives `n=524288: ≈ 6.7-7.0·10⁻⁶`, halved to `≈ 3.35-3.55·10⁻⁶`, comfortably below V25's `Cr_val = 1/240000 ≈ 4.167·10⁻⁶`.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_031_planner_projection.txt` documents the per-doubling trajectory `n=131072→262144` (absolute drop 17.1%, ratio 1.0344→0.871) and the conservative projection: at `n=524288` we expect `merged_sup ≈ 6.7-7.0·10⁻⁶` (15-17% drop from the V25 ball), giving rationalised `~71/10000000` (1.4% slack) or tighter, halved to `~3.55·10⁻⁶`, which dominates `Cr_val := 1/280000 ≈ 3.571·10⁻⁶` with margin ≥ 0.5%. The wall-time cost is one ~1030s oracle run (twice the V25 cost; `n=262144` measured at 515s), and the result is *cached* in `Numerical_Library/cache/merged_uderiv_*.json`, so subsequent Evaluator runs (G5 audit) re-use the cache in milliseconds. The win is conservative-case `1.17×` (`1/240000 → 1/280000`) and projected `1.23×` (`→ 1/295000`) on `Cr_val`, on top of V25's `1.42×` win over V23 — cumulative `~1.66×` over the V23 baseline.

## Concrete edits expected

1. **`ProofRefinement/Lemma54/Scratch/sprint_031_verify_n524288.txt`** (NEW — Generator-side verification before structural commit):
   - Run `compute_merged_uderiv_bound(n_per_edge=524288, safety_abs=1e-8, max_denom=10000000)` (all other params at the existing defaults: `eta=0.01, delta="1635/10000", B="1115/1000", p_max="1", n_p_subdiv=4, prec=200, K_max=80`).
   - Record: wall-time, `merged_uderiv_str`, `merged_uderiv_upper_float`, the rationalised `bound`, and the `ball_value` field.
   - Decision rule: write `DECISION: viable` if the rationalised bound `B_new` satisfies `B_new < 2/280000 = 1/140000` (so halved gives `Cr_val ≤ 1/280000` is feasible) AND `(B_new / 2) < 1/240000` strict (so V26 can dominate V25's Cr_val); otherwise `DECISION: marginal` with the actual numbers and a recommendation on whether to commit V26 with a smaller win or `STATUS=BLOCKED` for sprint_031.

2. **`ProofRefinement/Lemma54/Numerical_Library/merged_uderiv.py`** (one-line default-kwarg bump): change `n_per_edge: int = 262144` to `n_per_edge: int = 524288` in `compute_merged_uderiv_bound`'s signature. Update the docstring's "Default `n_per_edge=262144`" line and the "Performance: scans 4·n_per_edge·n_p_subdiv ≈ 4194k cells at n_per_edge=262144" line to reflect the new defaults (~8.4M cells, ~1030s). No other changes to the Python file. The cache file naming is keyed on `n_per_edge` so the V25-era cache for n=262144 is not invalidated.

3. **`ProofRefinement/Lemma54/Candidates/V26.lean`** (NEW — copy `V25.lean` verbatim, then patch):
   - Update header narrative: V26 is the merged_uderiv resolution doubling, parent `Candidates/V25.lean` (linear chain), sprint `Sprint_Contracts/sprint_031.md`. Cite `Scratch/sprint_031_verify_n524288.txt` for the new oracle output.
   - Update `merged_uderiv_val` from `41 / 5000000` to the new rationalised value `<NEW_NUMER> / <NEW_DENOM>` returned by the verify probe. Keep all positivity lemmas; their proofs are `unfold X; norm_num` and continue to work for the new literal.
   - Update `Cr_val` from `1 / 240000` to `1 / <NEW_CR_DENOM>` (target `1/280000`, projected `1/295000`, exact value chosen by the Generator from the verify-probe output to maximise the win while leaving a ≥ 0.5% rational margin against `(1/2)·merged_uderiv_val`).
   - Update the dominance step inside `lemma_5_4_search`: the rational check `Cr_phi_uzz_merged merged_uderiv_val ≤ Cr_val` is purely a `norm_num` / `decide` on the literal rational inequality `<NEW_NUMER>/(2·<NEW_DENOM>) ≤ 1/<NEW_CR_DENOM>`. The Generator updates the proof body if needed (it should be a one-liner identical to V25's pattern).
   - All other definitions, axioms, and theorems are byte-identical to V25 (carried-over oracle declarations stay; sink delegation pattern unchanged; the only consumed oracle is `h_merged_uderiv_oracle`).

4. **`ProofRefinement/Lemma54/lemma.toml`**: NO changes — the existing `h_merged_uderiv_oracle` `[[oracles]]` entry is unchanged (oracle_fn name and bound_field name both unchanged); the runtime oracle re-runs at the new default n_per_edge automatically because the Lean-side declared value `merged_uderiv_val` is what the runner compares against `oracle_bound`.

5. **`ProofRefinement/Lemma54/Bulletin.md`**: the Planner appends after the contract is queued (NOT the Generator).

6. **NO edits** to: `Proof/SearchConfig.lean`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, `Numerical_Library/__init__.py`, any `Numerical_Library/*.py` other than `merged_uderiv.py`, any `Proof/Lib/Lemma54_Paper*.lean` (no new Lean theorems), `Proposals/proposal_*.md`, any `V<K>.lean` for `K ≤ 25`, any `Sprint_Contracts/sprint_<K>.md` for `K < 031`, `_archive/`.

## Acceptance criteria

1. **Verification probe shows resolution doubling is viable**: `test -s ProofRefinement/Lemma54/Scratch/sprint_031_verify_n524288.txt && grep -E '^DECISION: viable' ProofRefinement/Lemma54/Scratch/sprint_031_verify_n524288.txt` exits 0. (If `DECISION: marginal` or worse, the Generator stops with `STATUS=BLOCKED` per the stop conditions; the Lean-side V26 is not written.)

2. **V26 compiles and evaluates with strictly smaller Cr_val**: `lake env lean ProofRefinement/Lemma54/Candidates/V26.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V26.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer * 240000 < score.denom * 1`. Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and (.score.numer * 240000) < .score.denom'`.

3. **Audit set unchanged in shape**: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.axioms_used | map(select(.name == "Braverman.PaperV0.h_merged_uderiv_oracle")) | length == 1'` exits 0, AND that axiom's entry has `kind == "oracle"`, `status == "pass"`, AND its `oracle_bound` equals the new rationalised value (i.e., the runtime arb pipeline re-verifies the oracle at `n_per_edge=524288` and certifies `oracle_bound ≤ declared`). The trust delta is exactly zero — same set of seed/oracle axioms, same runner re-verification path; only the certified-rational value tightens.

(All three criteria are mechanically checkable via `bash` / `grep` / `jq`.)

## Out of scope (Generator MUST NOT do)

- **Add any new axiom** (oracle-shaped or otherwise). The oracle-shape axiom `h_merged_uderiv_oracle` already exists in V25; this sprint changes only its bound field's literal value, not its name, signature, or count. Any *new* `axiom` declaration is forbidden.
- **Modify** `Proof/SearchConfig.lean` (locked at `eta = 1/100, r = 23/25`).
- **Modify** `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 25`.
- **Modify** any `Numerical_Library/*.py` other than `merged_uderiv.py`. The legacy `joint_phi_phip_invD2.py`, `uzz_phi_sq.py`, `m_phi.py`, etc., stay byte-identical — they are still declared in V26 (carried-over from V25) but not consumed by the active sink.
- **Modify** `Sprint_Contracts/sprint_<K>.md` for `K < 031` or `Proposals/proposal_*.md`. Proposal_003 (wider analyticity domain) is still pending — do NOT consume or reference it; this sprint is independent.
- **Use** `sorry`, `admit`, or `native_decide` introduced for the new rational check. (V25 already uses `norm_num`/`decide` patterns for the dominance step; mirror those exactly.)
- **Branch** from any candidate other than V25.
- **Write a new Lean theorem** — V26 reuses `lemma_5_4_paper_on_domain_phi_uzz_merged` from V25's shared infrastructure exactly. The only Lean changes are the two literal rationals (`merged_uderiv_val`, `Cr_val`) and any `norm_num` margin update.
- **Skip** the n=524288 verification probe (criterion #1). The structural change is conditional on it.
- **Lower** the verify probe's resolution to save runtime. The whole point is the absolute drop at the next doubling; using `n=393216` (between the two) is not on the per-doubling trajectory and gives no comparable projection.
- **File a fourth proposal**. Budget remains 1/3 pending (proposal_003).

## Time budget

≤ 60 minutes runtime total (cheap tier). Breakdown:
- ~17 min: run the verify probe at `n_per_edge=524288` (one `compute_merged_uderiv_bound` call; ~1030s wall)
- ~3 min: parse output, decide rationalisation, choose `Cr_val` denominator
- ~5 min: edit `Numerical_Library/merged_uderiv.py` default kwarg + docstring
- ~10 min: clone `V25.lean` → `V26.lean`, update two rationals + dominance proof
- ~5 min: smoke-test V26 with `lake env lean` and `Evaluator.py --skip-oracle --no-log`
- ~10 min: full `Evaluator.py` (oracle is cached after probe run; full audit ~10s)
- ~10 min slack for compile-edit cycles

Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (verify probe `viable`; V26 compiles + evaluates with `Cr_val < 1/240000`; merged oracle re-certified at new value with `status: pass`) → `STATUS=READY_FOR_EVALUATION`.

- Verify probe at `n=524288` returns `merged_sup` such that `(merged_sup / 2) ≥ 1/240000` (i.e., halved doesn't strictly beat V25 — possible if the per-doubling decrement collapses earlier than projected) → write `DECISION: dead` in the probe output, revert any partially-written changes (the git auto-checkpoint hook makes this `git checkout HEAD` of the touched files), → `STATUS=BLOCKED` with the actual `merged_sup` recorded. The next Planner reads the probe output and knows the per-doubling trend has plateaued; future sprints in this axis are likely dead and a structural pivot is needed.

- Verify probe `viable` but the rationalisation slack is too large to clear `Cr_val < 1/240000` strictly (e.g., `safety_abs=1e-8` over-pads the rational) → first try `safety_abs=1e-9, max_denom=100000000` (one decade tighter on each); if that still doesn't clear, → `STATUS=BLOCKED` with the rational and ball values both recorded. Do NOT silently weaken the `Cr_val < 1/240000` requirement.

- Acceptance criteria require a non-oracle axiom (e.g., a wider analyticity domain) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — this sprint is purely a parameter-bump on an existing oracle.

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
