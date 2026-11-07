# Sprint 032: Bump merged_uderiv oracle `n_per_edge` 524288→1048576 and tighten rationaliser (`safety_abs` 1e-8→1e-9, `max_denom` 1e7→1e8); drop `Cr_val` from `1/268000` to `≤1/290000`

**Created**: 2026-04-30 14:00 by Planner
**Parent candidate**: `Candidates/V26.lean` (linear chain — V26 is the latest-PASS at `Cr_val = 1/268000`, sprint_031's resolution doubling on the merged_uderiv oracle).
**Target file**: `Candidates/V27.lean`
**Direction**: `oracle-resolution-tightening + oracle-ceiling-tightening` — a combined move on the merged_uderiv oracle: one resolution doubling (`n_per_edge` 524288→1048576) AND a finer rationaliser (`safety_abs` 1e-8→1e-9, `max_denom` 1e7→1e8). The combined tightening was explicitly identified as Option C in `Scratch/sprint_032_planner_options.py`. This is NOT 3-in-a-row on either component axis: the prior 3 sprints' directions were 029=research, 030=formula-change, 031=oracle-resolution-tightening (just the resolution component, no rationaliser change); oracle-ceiling-tightening (the rationaliser component) was last used in sprint_026, five sprints ago. Mandatory wildcard cadence: sprint_026 wildcard, sprint_030 wildcard, next at sprint_034 — sprint_032 is a regular linear-chain sprint.
**Tier**: `cheap` — surgical: bump one default kwarg in `Numerical_Library/merged_uderiv.py`, change two rationaliser kwargs in the same file, re-run the oracle once at the new resolution-and-rationaliser combo, and clone V26 with two updated rationals (`merged_uderiv_val`, `Cr_val`). No new Lean theorems, no new oracles, no new axioms; the oracle's *axiom statement* and *signature* are unchanged — only its *numerical* declared value tightens and its rationaliser settings tighten.

## Goal (one sentence)

Re-run `compute_merged_uderiv_bound` at `n_per_edge=1048576, safety_abs=1e-9, max_denom=10⁸` (one resolution doubling and one rationaliser-decade tightening over V26's locked settings), rationalise the new ball value at the finer settings, and produce `Candidates/V27.lean` with `merged_uderiv_val` updated to the new (tighter) rational and `Cr_val` set to a literal `1/<DENOM>` strictly dominating `(1/2) · merged_uderiv_val_new` AND strictly less than `1/268000` (target `1/290000` conservative-case, projected `1/295000-1/300000` mid-case per `Scratch/sprint_032_planner_options.py`).

## Mathematical insight (required, ≤ 5 sentences)

V26's merged-numerator oracle bounds `sup_{p,w} ‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³` (the *exact* `|u''|` quotient by the form-A identity), and its arb-certified `ball_value` shrinks monotonically with the boundary discretisation `n_per_edge` because the per-cell `acb` interval slack on the merged numerator's destructive-interference cancellation tightens with cell-width; orthogonally, the rationaliser slack between the certified `ball_value` and the rationalised declared `merged_uderiv_val` is governed by `(safety_abs, max_denom)`, with finer settings reducing the slack from ~1.24% (at 1e-8/1e7) to ~0.14% (at 1e-9/1e8) per the verify-probe in `Scratch/sprint_031_verify_n524288.txt`. The active inequality in `lemma_5_4_paper_on_domain_phi_uzz_merged` is `‖u''‖ ≤ merged_uderiv_val`, so two independent slack reductions compose multiplicatively into a tighter `Cr_phi_uzz_merged = (1/2)·merged_uderiv_val` and hence a tighter `Cr_val`. The mathematical content is unchanged from V26: this sprint reuses the *same* form-A identity, the *same* oracle signature, and the *same* axiom statement — gains come purely from the numerical certification pipeline at the new (n, safety, max_denom) settings. Per-doubling history of `merged_sup` (`Scratch/sprint_031_verify_n524288.txt`) shows decelerating drops (17.1% at 131072→262144, 9.6% at 262144→524288); a conservative 7-9% drop projection at 524288→1048576 gives `merged_sup ≈ 6.6-6.8·10⁻⁶`, halved to `≈ 3.3-3.4·10⁻⁶`, sitting strictly below V26's `1/268000 ≈ 3.731·10⁻⁶` even in the conservative case.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_032_planner_options.py` documents Options A-I and selects Option C (combined doubling + rationaliser tightening): the conservative-case projection at `n=1048576, safety_abs=1e-9, max_denom=1e8` is `merged_sup ≈ 6.80·10⁻⁶ → Cr_phi ≈ 3.40·10⁻⁶`, dominating `Cr_val = 1/290000 ≈ 3.45·10⁻⁶` with margin +1.45% (1.082× win, conservative); the mid-case projection is `merged_sup ≈ 6.65·10⁻⁶ → Cr_phi ≈ 3.33·10⁻⁶`, dominating `Cr_val = 1/295000 ≈ 3.39·10⁻⁶` with margin +1.7% (1.10× win, mid). The combined move is preferred over either lever alone because Option A (doubling only at locked rationaliser) gives ~1.108× and Option B (rationaliser only at fixed n=524288) gives only ~1.019× — composing both takes ~33 min of wall time for a single oracle re-run instead of two separate sprints. The wall-time cost is one ~2050s oracle run (~2× the V26 cost; n=524288 measured at 989s, n=1048576 projected ~2050s); the result is *cached* in `Numerical_Library/cache/merged_uderiv_*.json`, so subsequent Evaluator runs (G5 audit) re-use the cache in milliseconds.

## Concrete edits expected

1. **`ProofRefinement/Lemma54/Scratch/sprint_032_verify_n1048576.txt`** (NEW — Generator-side verification before structural commit):
   - Run `compute_merged_uderiv_bound(n_per_edge=1048576, safety_abs=1e-9, max_denom=100000000)` (all other params at the existing defaults: `eta=0.01, delta="1635/10000", B="1115/1000", p_max="1", n_p_subdiv=4, prec=200, K_max=80`).
   - Record: wall-time, `merged_uderiv_str`, `merged_uderiv_upper_float`, the rationalised `bound`, and the `ball_value` field.
   - Decision rule: write `DECISION: viable` if the rationalised bound `B_new` satisfies `(B_new / 2) < 1/268000` strictly (so V27 can dominate V26's Cr_val) AND `(B_new / 2) ≤ 1/290000` (so the conservative-case `Cr_val=1/290000` is reachable); otherwise write `DECISION: marginal` with the actual numbers and the largest `Cr_val=1/<N>` denominator achievable that strictly beats `1/268000`. Write `DECISION: dead` only if `(B_new / 2) ≥ 1/268000` (would fail to beat V26 entirely — extremely unlikely given the projection but the stop-condition is preserved).

2. **`ProofRefinement/Lemma54/Numerical_Library/merged_uderiv.py`** (three default-kwarg bumps in `compute_merged_uderiv_bound`'s signature):
   - Change `n_per_edge: int = 524288` to `n_per_edge: int = 1048576`.
   - Change `safety_abs: float = 1e-8` to `safety_abs: float = 1e-9`.
   - Change `max_denom: int = 10000000` to `max_denom: int = 100000000`.
   - Update the docstring's "Default `n_per_edge=524288`" / "safety_abs = 1e-8" / "max_denom = 10000000" lines to reflect the new defaults.
   - Update the "Performance: scans 4·n_per_edge·n_p_subdiv ≈ 8389k cells at n_per_edge=524288, prec=200; sprint_031 verify-probe measured ~989s wall" performance line to the new numbers (~16.8M cells at n=1048576, projected ~2050s).
   - No other changes to the Python file. The cache file naming is keyed on `(n_per_edge, safety_abs, max_denom)` so the V25/V26-era caches are not invalidated.

3. **`ProofRefinement/Lemma54/Candidates/V27.lean`** (NEW — copy `V26.lean` verbatim, then patch):
   - Update header narrative: V27 is the merged_uderiv combined-tightening (resolution doubling + rationaliser tightening), parent `Candidates/V26.lean` (linear chain), sprint `Sprint_Contracts/sprint_032.md`. Cite `Scratch/sprint_032_verify_n1048576.txt` for the new oracle output.
   - Update `merged_uderiv_val` from `37 / 5000000` to the new rationalised value `<NEW_NUMER> / <NEW_DENOM>` returned by the verify probe (expected ~`67/10000000` to ~`679/100000000` range depending on actual ball value).
   - Update `Cr_val` from `1 / 268000` to `1 / <NEW_CR_DENOM>` (target `1/290000` conservative-case, projected `1/295000-1/300000` mid-case; exact value chosen by the Generator from the verify-probe output to maximise the win while leaving a ≥ 0.5% rational margin against `(1/2)·merged_uderiv_val`).
   - Update the dominance step inside `lemma_5_4_search`: the rational check `Cr_phi_uzz_merged merged_uderiv_val ≤ Cr_val` is purely a `norm_num` / `decide` on the literal rational inequality `<NEW_NUMER>/(2·<NEW_DENOM>) ≤ 1/<NEW_CR_DENOM>`. The Generator updates the proof body if needed (it should be a one-liner identical to V26's pattern).
   - All other definitions, axioms, and theorems are byte-identical to V26 (carried-over oracle declarations stay; sink delegation pattern unchanged; the only consumed oracle is `h_merged_uderiv_oracle`).
   - Update the header docstring's `merged_uderiv_val` value reference (line 6 in V26 mentions "the locked rationaliser settings"; should now say "tightened to safety_abs=1e-9, max_denom=1e8") and lines 43-44's `Cr_val` arithmetic check description.

4. **`ProofRefinement/Lemma54/lemma.toml`**: NO changes — the existing `h_merged_uderiv_oracle` `[[oracles]]` entry is unchanged (oracle_fn name and bound_field name both unchanged); the runtime oracle re-runs at the new default `(n_per_edge, safety_abs, max_denom)` automatically because the Lean-side declared value `merged_uderiv_val` is what the runner compares against `oracle_bound`.

5. **`ProofRefinement/Lemma54/Bulletin.md`**: the Planner appends after the contract is queued (NOT the Generator).

6. **NO edits** to: `Proof/SearchConfig.lean`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, `Numerical_Library/__init__.py`, any `Numerical_Library/*.py` other than `merged_uderiv.py`, any `Proof/Lib/Lemma54_Paper*.lean` (no new Lean theorems), `Proposals/proposal_*.md` (proposal_003 stays pending, do not consume), any `V<K>.lean` for `K ≤ 26`, any `Sprint_Contracts/sprint_<K>.md` for `K < 032`, `_archive/`.

## Acceptance criteria

1. **Verification probe shows the combined tightening is viable**: `test -s ProofRefinement/Lemma54/Scratch/sprint_032_verify_n1048576.txt && grep -E '^DECISION: (viable|marginal)' ProofRefinement/Lemma54/Scratch/sprint_032_verify_n1048576.txt` exits 0. (If `DECISION: dead`, the Generator stops with `STATUS=BLOCKED` per the stop conditions; the Lean-side V27 is not written. `DECISION: marginal` is acceptable provided the actual achievable `Cr_val` strictly beats `1/268000`.)

2. **V27 compiles and evaluates with strictly smaller Cr_val**: `lake env lean ProofRefinement/Lemma54/Candidates/V27.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V27.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer * 268000 < score.denom * 1`. Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and (.score.numer * 268000) < .score.denom'`.

3. **Audit set unchanged in shape**: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.axioms_used | map(select(.name == "Braverman.PaperV0.h_merged_uderiv_oracle")) | length == 1'` exits 0, AND that axiom's entry has `kind == "oracle"`, `status == "pass"`, AND its `oracle_bound` equals the new rationalised value (i.e., the runtime arb pipeline re-verifies the oracle at `n_per_edge=1048576, safety_abs=1e-9, max_denom=1e8` and certifies `oracle_bound ≤ declared`). The trust delta is exactly zero — same set of seed/oracle axioms, same runner re-verification path; only the certified-rational value tightens.

(All three criteria are mechanically checkable via `bash` / `grep` / `jq`.)

## Out of scope (Generator MUST NOT do)

- **Add any new axiom** (oracle-shaped or otherwise). The oracle-shape axiom `h_merged_uderiv_oracle` already exists in V26; this sprint changes only its bound field's literal value, not its name, signature, or count. Any *new* `axiom` declaration is forbidden.
- **Modify** `Proof/SearchConfig.lean` (locked at `eta = 1/100, r = 23/25`).
- **Modify** `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 26`.
- **Modify** any `Numerical_Library/*.py` other than `merged_uderiv.py`. The legacy `joint_phi_phip_invD2.py`, `uzz_phi_sq.py`, `m_phi.py`, etc., stay byte-identical — they are still declared in V27 (carried-over from V26) but not consumed by the active sink.
- **Modify** `Sprint_Contracts/sprint_<K>.md` for `K < 032` or `Proposals/proposal_*.md`. Proposal_003 (wider analyticity domain) is still pending — do NOT consume or reference it; this sprint is independent.
- **Use** `sorry`, `admit`, or `native_decide` introduced for the new rational check. (V26 already uses `norm_num`/`decide` patterns for the dominance step; mirror those exactly.)
- **Branch** from any candidate other than V26.
- **Write a new Lean theorem** — V27 reuses `lemma_5_4_paper_on_domain_phi_uzz_merged` from V25's shared infrastructure exactly. The only Lean changes are the two literal rationals (`merged_uderiv_val`, `Cr_val`) and any `norm_num` margin update, plus the header docstring rationaliser note.
- **Skip** the n=1048576 verification probe (criterion #1). The structural change is conditional on it.
- **Lower** the verify probe's resolution to save runtime. The whole point is the absolute drop at the next doubling; using `n=786432` (between the two) is not on the per-doubling trajectory and gives no comparable projection.
- **Tighten only one of the two settings** (e.g., bump `n_per_edge` but leave `safety_abs=1e-8`). The combined Option C analysis in `Scratch/sprint_032_planner_options.py` rejected single-axis moves as too marginal; if the verify probe shows the combined move is unworkable, fall back to BLOCKED and let the next planner choose between A or B alone.
- **File a fourth proposal**. Budget remains 1/3 pending (proposal_003).

## Time budget

≤ 75 minutes runtime total (cheap tier). Breakdown:
- ~35 min: run the verify probe at `n_per_edge=1048576, safety_abs=1e-9, max_denom=1e8` (one `compute_merged_uderiv_bound` call; ~2050s wall projected)
- ~3 min: parse output, decide rationalisation, choose `Cr_val` denominator
- ~5 min: edit `Numerical_Library/merged_uderiv.py` three default kwargs + docstring/performance lines
- ~10 min: clone `V26.lean` → `V27.lean`, update two rationals + dominance proof + header rationaliser note
- ~5 min: smoke-test V27 with `lake env lean` and `Evaluator.py --skip-oracle --no-log`
- ~5 min: full `Evaluator.py` (oracle is cached after probe run; full audit ~10s)
- ~12 min slack for compile-edit cycles or in case the verify probe needs a re-run at marginally different rationaliser settings

Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (verify probe `viable` or `marginal`; V27 compiles + evaluates with `Cr_val < 1/268000`; merged oracle re-certified at new value with `status: pass`) → `STATUS=READY_FOR_EVALUATION`.

- Verify probe at `n=1048576` returns `merged_sup` such that `(merged_sup / 2) ≥ 1/268000` (i.e., halved doesn't strictly beat V26 — possible if the per-doubling decrement collapses earlier than projected, e.g., if the destructive-interference saturation point is reached at this resolution) → write `DECISION: dead` in the probe output, revert any partially-written changes (the git auto-checkpoint hook makes this `git checkout HEAD` of the touched files), → `STATUS=BLOCKED` with the actual `merged_sup` recorded. The next Planner reads the probe output and knows the per-doubling trend has saturated; future sprints in this axis are likely dead and a structural pivot is needed.

- Verify probe `viable` but the combined-rationaliser slack is too large to clear `Cr_val < 1/268000` strictly (extremely unlikely given the verify-probe analysis already quoted in `Scratch/sprint_031_verify_n524288.txt` showed `safety_abs=1e-9, max_denom=1e8` would give 0.14% slack at the V26 ball value) → first try `safety_abs=1e-10, max_denom=1e9` (one decade tighter on each); if that still doesn't clear, → `STATUS=BLOCKED` with the rational and ball values both recorded. Do NOT silently weaken the `Cr_val < 1/268000` requirement.

- Acceptance criteria require a non-oracle axiom (e.g., a wider analyticity domain — proposal_003 pending) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — this sprint is purely a parameter-bump on an existing oracle.

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
