# Sprint 029: Wildcard research sprint — probe structural pivot levers (3-way decomposition, merged numerator at n=65536, per-edge sup dominance) and file proposal_003 (wider analyticity domain) async; V24 byte-identical to V23 (Cr_val 1/169000 unchanged)

**Created**: 2026-04-30 11:48 by Planner
**Parent candidate**: `Candidates/V23.lean` (linear chain — V23 is the latest-PASS at `Cr_val = 1/169000`. Sprint_028's contract explicitly directed: "sprint_029 onward must consider structural pivots". The same-axis history is sprints 026 (oracle-ceiling-tightening) → 027 (oracle-resolution-tightening) → 028 (oracle-resolution-tightening); the no-same-axis-3-in-a-row rule allows sprint_029 to be a different axis. Last wildcard-parent was sprint_026 (V18); next mandatory wildcard is sprint_030, so sprint_029 can be a linear-parent research sprint.)
**Target file**: `Candidates/V24.lean`
**Direction**: `research+proposal-filing` — V24 is byte-identical to V23 (`Cr_val` unchanged at `1/169000`); the deliverable is numerical characterisation of the three structural pivot levers identified in `Scratch/sprint_026_research_summary.md` (3-way decomposition; merged numerator at high resolution; per-edge sup dominance) and an async non-oracle proposal (proposal_003) requesting a wider analyticity domain to revive the sprint_013-blocked contour-change axis. The sprint exists to keep the loop running per `Bulletin.md` "Keeping the loop running" guidance, while gathering data for sprint_030's mandatory wildcard pivot.
**Tier**: `cheap` — three Python research scripts (each ≤30 min runtime, the merged-numerator probe at n=65536 is the longest at ~10 min); one new candidate file `V24.lean` byte-identical to V23 except for a header narrative update; one new proposal file `Proposals/proposal_003_wider_analyticity_domain.md` (already drafted by the Planner in this invocation).

## Goal (one sentence)

Run three structural-pivot research probes (3-way decomposition viability, merged-numerator at n_per_edge=65536, per-edge sup-dominance on `∂Ω(δ_val, B_val)`), synthesize findings in `Scratch/sprint_029_research_summary.md` to inform sprint_030's mandatory wildcard, file `Proposals/proposal_003_wider_analyticity_domain.md` async for human review, and produce `V24.lean` byte-identical to V23 with header narrative updated to record the research direction — `Cr_val` stays at `1/169000` and the score doesn't move this sprint.

## Mathematical insight (required, ≤ 5 sentences)

The V23 active chain consumes joint oracles whose ball-values `joint = 4.62·10⁻⁶` and `uzz = 2.37·10⁻⁶` together dominate `Cr_val = 1/169000`; per-doubling-resolution reductions have decayed monotonically (28%/21% at n=32768→65536, projecting <2× total remaining headroom on this axis). Three structural levers remain numerically untested at the V23 baseline: (i) **3-way decomposition** of term-2's `|DD·Φ²/D³| = |DD/D|·|Φ/D|²` into separate sup-norms, which is *looser* in principle (sup of products ≤ product of sups) but may have *less interval slack* in arb arithmetic at high resolution because each factor has lower-degree denominators than the joint cubic; (ii) the **merged numerator** `|2·Φ·Φ'·D − DD·Φ²|/|D|³` (= the *exact* `|u''|`) which sprint_026 declared dead at n=8192 (ratio 1.78× worse) but whose ratio-vs-triangle-bound was monotonically decreasing with resolution (1.99 at n=1024 → 1.78 at n=8192) — at the much-higher V23 resolution n=65536 the destructive interference may finally beat the triangle bound; (iii) **per-edge sup dominance** on `∂Ω(δ_val, B_val)` — if a single edge (top, bottom, left, right) accounts for ≥80% of the joint sup, a sub-region oracle scanning only that edge could yield a tighter bound (currently each edge contributes equally to the scan). The fourth lever — **wider analyticity domain** to revive sprint_013's contour-change axis — requires a new free-floating analytic axiom and is filed as `Proposals/proposal_003_wider_analyticity_domain.md` in this sprint's same invocation. None of (i)-(iii) require new axioms or oracle entries — only Python research scripts that read existing oracle infrastructure. The candidate-side Lean proof is unchanged from V23.

## Why (≤ 3 sentences, must include numerical evidence)

Sprint_028's contract (final paragraph) explicitly directed: "sprint_029 onward must consider structural pivots"; sprint_026's research summary's "Future leverage" section (lever #2) flagged the 3-way decomposition as *promising but untested*, and (lever #3) flagged the wider-analyticity-domain proposal as the trust-expanding direction with the highest reachable win — neither has been numerically probed at the V23 baseline. The diminishing-returns trajectory on the resolution axis (per-doubling reduction now 28%/21% per `Scratch/sprint_028_planner_run_n65536.py` output and shrinking) means any further `n_per_edge` doubling yields ≤1.2× win, while a successful structural pivot could yield ≥2× win — so spending one sprint on numerical characterisation has ~5-10× expected information value (per the Planner's "Keeping the loop running" rule that prefers research/cleanup over BLOCKED). The proposal-filing component is justified independently: sprint_026 research summary line 113 said "File a non-oracle proposal for a wider analyticity domain (sprint_013-blocked direction). Allows lifting the Cauchy contour radius" — this is the right invocation to file it, with budget 0/3 currently consumed (`grep -c 'Status: pending' Proposals/proposal_*.md` returns 0).

## Concrete edits expected

- **`ProofRefinement/Lemma54/Scratch/sprint_029_planner_three_way_decomp.py`** (NEW — Python research script):
  - Imports `Numerical_Library.uzz_phi_sq.compute_uzz_phi_sq_bound` for the joint baseline.
  - Implements two new sup-norm scans on `∂Ω(δ_val, B_val)`:
    - `compute_DD_invD_sup` — sup of `|DD(p,w)/D(p,w)|` over `p ∈ [0, 1], w ∈ ∂Ω`.
    - `compute_phi_invD_sup` — sup of `|Φ(w)/D(p,w)|` over the same domain.
  - At `n_per_edge=4096` (cheap, ~10s each), reports both sup values and computes the triangle-product upper bound `sup(|DD/D|) · sup(|Φ/D|)²`.
  - Compares to the joint sup `2.37·10⁻⁶` (V23 ball value): if the triangle product is ≤ joint, the 3-way decomposition is a viable structural lever and sprint_030 should mint two new inline oracles (`compute_DD_invD_bound`, `compute_phi_invD_bound`); if it's >> joint, the lever is dead.
  - Writes `Scratch/sprint_029_three_way_decomp.txt` with the numerical conclusion.

- **`ProofRefinement/Lemma54/Scratch/sprint_029_planner_merged_n65536.py`** (NEW — Python research script):
  - Reuses `Scratch.sprint_022_planner_full_merge.compute_full_merged_uderiv_bound` from sprint_022/026 (the merged-numerator probe).
  - Runs at `n_per_edge ∈ {16384, 32768, 65536}` to confirm or refute sprint_026's "merged dead" verdict at high resolution.
  - Reports `merged_sup / (2·joint_sup + uzz_sup)` ratio at each resolution.
  - Decision rule: if ratio drops below 1.0 at any tested resolution, merged is alive and sprint_030 should mint a `compute_merged_uderiv_bound` inline oracle; if ratio stays above 1.5, merged is permanently dead and sprint_030 should not pursue this axis.
  - Writes `Scratch/sprint_029_merged_n65536.txt` with the numerical conclusion.

- **`ProofRefinement/Lemma54/Scratch/sprint_029_planner_per_edge_sup.py`** (NEW — Python research script):
  - Implements a custom rectangle-boundary scan that records the per-edge maximum of the joint and uzz quotients separately (Left edge `Re=−B`, Right edge `Re=+B`, Top edge `Im=+δ`, Bottom edge `Im=−δ`, each scanned at `n_per_edge=4096`).
  - Reports each edge's max and the global sup as a sanity check against the existing oracles' `4.62e-6 / 2.37e-6` ball values.
  - Decision rule: if a single edge dominates by ≥4× over the next-largest, a sub-region oracle scanning only that edge is viable; if all edges are within 2× of each other, sub-region pivot is dead.
  - Writes `Scratch/sprint_029_per_edge_sup.txt` with the numerical conclusion.

- **`ProofRefinement/Lemma54/Scratch/sprint_029_research_summary.md`** (NEW — markdown synthesis):
  - One-page summary of the three probes' findings.
  - Names the highest-value direction for sprint_030 (mandatory wildcard).
  - Cross-references `Proposals/proposal_003_wider_analyticity_domain.md` and notes its async status.

- **`ProofRefinement/Lemma54/Proposals/proposal_003_wider_analyticity_domain.md`** (ALREADY WRITTEN by the Planner before delegating to the Generator — the Generator does NOT re-write it, but should verify it exists and is unchanged):
  - The Planner has authored this proposal in the same invocation as queueing this sprint contract.
  - Status: `pending`. Type: `new-axiom`. Asks for one new free-floating analytic axiom `F_inv_paper_analytic_wider` over `disk((3+r)/4)` (vs the existing `disk((1+r)/2)`).
  - Win: revives sprint_013-blocked contour-change axis; estimated direct V23-chain win 1.0×-1.5×, with the larger value being structural unblocking.
  - Generator's only job: verify the file exists at the path above with `Status: pending` and Type: `new-axiom`. Do NOT modify the proposal — it's the Planner's responsibility.

- **`ProofRefinement/Lemma54/Candidates/V24.lean`** (NEW — byte-identical to V23 modulo header):
  - Copy `Candidates/V23.lean` verbatim.
  - Update the header comment block (lines 1-79) to identify V24 as the linear successor to V23 along the `research+proposal-filing` axis: state the sprint's research deliverables, the filed proposal_003, and the unchanged Cr_val (1/169000).
  - Update `-- @parent Candidates/V23.lean` and `-- @sprint Sprint_Contracts/sprint_029.md`.
  - All numeric `def`s (`M_val`, `delta_val`, `B_val`, `M_phi_val`, `M_phi_prime_val`, `inv_F_p_z_val`, `u_zz_bound_val`, `joint_phi_phip_invD2_val`, `uzz_phi_sq_val`, `Cr_val`) are byte-identical to V23.
  - All oracle declarations and supporting lemmas are byte-identical to V23.
  - The body of `lemma_5_4_search` is byte-identical to V23.

- **`ProofRefinement/Lemma54/Bulletin.md`** (the Planner appends after the contract is written, NOT the Generator).

- **NO edits** to: `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper*.lean`, `ProofRefinement/Lemma54/Proof/SearchConfig.lean`, `ProofRefinement/Lemma54/lemma.toml`, `ProofRefinement/Lemma54/Numerical_Library/*.py` (except possibly importing existing functions in the new Scratch scripts), `LeanProof/`, `ProofGraph/`, `Evaluator.py`, any `V<K>.lean` for `K ≤ 23`, or any file outside the named edit list.

## Acceptance criteria

1. **Compile and evaluate V24 cleanly with Cr_val unchanged**: `lake env lean ProofRefinement/Lemma54/Candidates/V24.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V24.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer == 1 AND score.denom == 169000` (i.e., V24's Cr_val is byte-identical to V23's). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and .score.numer == 1 and .score.denom == 169000'`.

2. **Three research scripts present and runnable**: `ls ProofRefinement/Lemma54/Scratch/sprint_029_planner_three_way_decomp.py ProofRefinement/Lemma54/Scratch/sprint_029_planner_merged_n65536.py ProofRefinement/Lemma54/Scratch/sprint_029_planner_per_edge_sup.py` exits 0 with all three files non-empty (≥ 50 lines each). Each script must successfully run end-to-end (the Generator runs them with `cd /home/rsaha/projects/grothendieck && PYTHONPATH=. uv run python ProofRefinement/Lemma54/Scratch/sprint_029_planner_<topic>.py 2>&1 | tee ProofRefinement/Lemma54/Scratch/sprint_029_<topic>.txt`). The `.txt` files must each include a numerical decision line of the form `DECISION: <viable|dead|inconclusive>` near the end.

3. **Research summary and proposal_003 present**: `test -s ProofRefinement/Lemma54/Scratch/sprint_029_research_summary.md && test -s ProofRefinement/Lemma54/Proposals/proposal_003_wider_analyticity_domain.md && grep -c 'Status: pending' ProofRefinement/Lemma54/Proposals/proposal_003_wider_analyticity_domain.md` exits 0 with the grep count ≥ 1. The research summary must name a recommended direction for sprint_030 (a string matching one of `3-way-decomposition`, `merged-numerator-revive`, `sub-region-oracle`, `wider-analyticity-domain-pending`, `oracle-ceiling-tightening-d1e8`, or `oracle-resolution-tightening-n131072`).

(All three are mechanically checkable via `bash`/`jq`/`grep`.)

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration (the proposal_003 axiom is filed for human approval — the Generator does NOT add it to Lean in this sprint).
- Add any new `[[oracles]]` entry to `lemma.toml`. The three research scripts are pure-Python explorations; they do not become oracles in this sprint regardless of their numerical conclusions. (sprint_030 may mint inline oracles if the research warrants it.)
- Modify `Proof/Lib/Lemma54_Paper*.lean`, `Proof/SearchConfig.lean`, `lemma.toml`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 23`.
- Modify `Numerical_Library/*.py` files. The research scripts may *import* from them (specifically `_arb_helpers`, `_phi_loader`, `joint_phi_phip_invD2`, `uzz_phi_sq`) but do NOT edit them.
- Modify `Proposals/proposal_003_wider_analyticity_domain.md` — it's the Planner's deliverable, written before this contract was queued. Generator should `cat` it to verify presence and `Status: pending`, but not edit.
- Use `sorry`, `admit`, or `native_decide` in `V24.lean` (V23 has none; preserve that).
- Pick a different `Cr_val` than V23's `1/169000`. V24 is byte-identical to V23 modulo the header; the score must not move.
- Branch from any candidate other than V23. Linear chain V23→V24 is correct. (sprint_030 will be the next mandatory wildcard, branching from an earlier V<K>.)
- Run the research scripts at higher resolutions than specified (`n_per_edge=4096` for three-way and per-edge probes; `n ∈ {16384, 32768, 65536}` for merged-numerator). Higher resolutions blow the time budget; the cheap probes are sufficient for the decision rules.
- File a fourth proposal beyond proposal_003. The budget is 1/3 pending after this sprint; further proposals are sprint_030+ business.

## Time budget

≤ 60 minutes runtime total. Breakdown: ~10 min for the 3-way decomp probe (two custom sup-scans at n=4096, ~5s each + minor analysis); ~15 min for the merged-numerator probe (re-uses sprint_022 infra at n=16384 ~10s, n=32768 ~40s, n=65536 ~120s); ~5 min for the per-edge sup probe (one custom edge-labelled scan at n=4096, ~10s); ~5 min for `Scratch/sprint_029_research_summary.md` (synthesis writeup); ~5 min for `Candidates/V24.lean` (`cp V23.lean V24.lean` + header rewrite); ~10 min for `lake env lean V24.lean` to re-elaborate (cache hits since proofs are byte-identical); ~5 min for `Evaluator.py V24.lean` to compile + audit + reverify oracles (oracle calls hit cache). ~5 min slack. Soft cap 75% of context. The Generator should NOT block on the proposal_003 file — that's already drafted by the Planner.

## Stop conditions for the Generator

- All three acceptance criteria met (V24 compiles with Cr_val unchanged; three research scripts run end-to-end and produce DECISION lines; research summary and proposal_003 present) → `STATUS=READY_FOR_EVALUATION`.

- A research script fails to run (e.g., `compute_full_merged_uderiv_bound` API has changed since sprint_026, or `_iter_rect_boundary` signature differs from what the per-edge probe expects) → record the failure in the script's `.txt` output as `DECISION: inconclusive (<failure mode>)`, continue with the other two scripts, and note in the research summary which lever could not be probed. The acceptance criteria still pass if the script produces *some* DECISION line, even `inconclusive`. → `STATUS=READY_FOR_EVALUATION` with the inconclusive note.

- `lake env lean V24.lean` fails despite V24 being byte-identical to V23 modulo header (very unlikely — header comments don't affect elaboration) → revert the candidate to byte-identical V23 with only `-- @parent` and `-- @sprint` lines updated, retry compile. If still fails → `STATUS=BLOCKED` with the goal state.

- Cannot satisfy criteria without violating "Out of scope" (e.g., a research script reveals a serious bug in an existing oracle that requires editing `Numerical_Library/`) → record the bug in `Scratch/sprint_029_<topic>.txt` and `Scratch/sprint_029_research_summary.md` for human review, then → `STATUS=BLOCKED` naming the bug; do NOT edit the oracle.

- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — research scripts and a header-only candidate require no new axioms.

- Soft context cap exceeded (very unlikely for a research-only sprint) → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
