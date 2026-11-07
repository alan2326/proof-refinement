# Sprint 022: Wildcard research sprint — characterize the achievable floor of the current `(2·joint + uzz_phi_sq)` decomposition by running joint oracles at higher arb-scan resolutions and probing one alternative factored bound; produce no V17 score change but a Scratch findings file that pins down sprint_023's next direction

**Created**: 2026-04-30 11:30 by Planner
**Parent candidate**: `Candidates/V0.lean` (wildcard — the recent linear chain V14 → V15 → V16 has the parent moving each sprint along a single accumulating `[[oracles]]` axis, and the every-4-sprints wildcard rule is binding: the last wildcard was sprint_017, and sprints 018, 019, 020, 021 form the four-sprint window since. V17 is a *byte-identical copy* of V16's literals/structure — the candidate-file deliverable is procedural, not where the sprint's value lives. The real deliverable is a Scratch/ research artifact that branches the search out of the local optimum at `Cr_val = 1/3500` ≈ `2.857·10⁻⁴`. We use V0 in the `Parent candidate` field because the wildcard rule explicitly says "the parent MUST be V0.lean (or another non-immediate ancestor)"; the actual byte content of V17 is copied from V16 since the score's been monotonically tightening and there is no V0 property that V16 lacks worth reviving.)
**Target file**: `Candidates/V17.lean` (byte-identical copy of V16) **plus** primary deliverable `Scratch/sprint_022_research_findings.md` (a free-form Markdown file written by the Generator summarizing the numerical results below, ≤ 200 lines).
**Direction**: research: achievable-floor-and-alternative-factored-bound-probe. This direction has not been used in any prior sprint. Direction-history check: sprint_019 = inline-oracle, sprint_020 = inline-oracle, sprint_021 = oracle-ceiling-tightening; the wildcard rule requires the new direction to differ from all three, which "research" does. The sprint also satisfies the wildcard *parent* rule (V0 ≠ V16). After this sprint the next Planner has concrete numerical data to pick sprint_023's structural lever; without it sprint_023 is likely to mis-estimate the floor and queue a sprint that fails to clear V16 (we already know full-merge fails — see `Scratch/sprint_022_planner_full_merge.py`).
**Tier**: cheap — surgical: the only Lean change is `cp Candidates/V16.lean Candidates/V17.lean` plus updating the file header to identify the wildcard role. The numerical work is one Python script with two cached arb runs (high-resolution joint oracles) and one new arb scan (the alternative factored bound), runtime ~5–15 minutes total for the runs themselves (cache hits will be near-instant for params already explored). Soft cap 75% of context.

## Goal (one sentence)

Produce numerical evidence in `Scratch/sprint_022_research_findings.md` characterizing (a) the achievable floor of `joint_phi_phip_invD2` and `uzz_phi_sq` at scan resolutions `n_per_edge ∈ {2048, 4096, 8192}` (production is currently 2048), and (b) the achievable bound of one alternative factored expression `‖Φ‖ · ‖2·Φ'·D - DD·Φ‖ / ‖D‖³` over `(p, w) ∈ [0, 1] × Ω(δ_val, B_val)` to determine whether a single-oracle factored bound could replace the current sum decomposition; ship V17 byte-identical to V16 so `Cr_val = 1/3500` is preserved as the latest-PASS floor.

## Mathematical insight (required, ≤ 5 sentences)

The current sink (V16) bounds `‖u''‖ ≤ 2·‖Φ·Φ'‖/‖D‖² + ‖DD·Φ²‖/‖D‖³ ≤ 2·joint + uzz_phi_sq` with `joint ≈ 1.989·10⁻⁴` and `uzz_phi_sq ≈ 1.525·10⁻⁴`. Two structural levers exist for tightening: **(L1)** the joint-sup bounds themselves can be tightened by finer arb cell width — at `n_per_edge=512` the joint sup reads `5.14·10⁻³` (cache files), at `n_per_edge=2048` it drops to `1.989·10⁻⁴` (26× tighter), so further halvings of cell width may continue to shrink the bound until value-precision dominates over interval-width slack. **(L2)** Using `u' = -Φ/D` and the form-A identity `D·u'' = -(2·Φ'·u' + DD·u'·u')`, we have `u'' = (2·Φ·Φ'·D - DD·Φ²) / D³`, but a triangle on the *signed* numerator is what produces the `2·joint + uzz_phi_sq` decomposition; **interval-arithmetic on the merged complex numerator was numerically tested and fails (`Scratch/sprint_022_planner_full_merge.py` shows ~2× *worse* than naive sum at smoke resolution)**, so the next plausible structural lever is the *factored* bound `‖u''‖ ≤ ‖Φ‖/‖D‖² · ‖2·Φ' - DD·Φ/D‖`, which moves one factor `‖Φ‖` outside the inner cancellation envelope. This sprint *quantifies* both L1 and L2 — we need to know whether the joint oracle's true floor is ~1·10⁻⁴ (1.5–2× win possible) or already at ~1.99·10⁻⁴ (no L1 win), and whether the factored bound's sup is below `2·joint + uzz_phi_sq ≈ 5.5·10⁻⁴` (L2 win) or above it (L2 dead). Without these data, sprint_023 would have to guess.

## Why (≤ 3 sentences, must include numerical evidence)

[`Scratch/sprint_022_planner_full_merge.py`](../Scratch/sprint_022_planner_full_merge.py) ran a 1024-resolution smoke test of the fully-merged numerator `‖2·Φ·Φ'·D - DD·Φ²‖ / ‖D‖³` and found `merged_sup ≈ 6.93·10⁻³` versus naive sum (`2·term1 + term2`) of `3.48·10⁻³` (i.e., merged is **1.99× worse than naive** even at smoke resolution — interval-arithmetic looseness on the complex difference inflates the upper bound far more than destructive interference reduces the value). This rules out the obvious "fully-merge ‖u''‖ into one oracle" direction without further analysis; the *factored* form `‖Φ‖·‖2·Φ' - DD·Φ/D‖/‖D‖²` is the next candidate but has not been tested. The cache files (`Numerical_Library/.cache/58b21a1*.json` etc.) show `joint_phi_phip_invD2` at `n_per_edge=512` is `5.14·10⁻³`, versus production-resolution `1.989·10⁻⁴` (df0152055009c35a.json), i.e., one halving of cell width tightened by 26×; whether another halving (n_per_edge=4096) yields another order-of-magnitude or settles on a constant is an empirical question this sprint resolves.

## Concrete edits expected

- **`ProofRefinement/Lemma54/Candidates/V17.lean`** (NEW FILE, byte-identical to V16 except for the header comment block):
  - Header: identify V17 as a wildcard byte-identical copy of V16 (same `Cr_val = 1/3500`, same six oracle declarations, same sink delegation), procedural for the wildcard cadence rule (cite sprint_022 contract).
  - Update `-- @parent` line: `Candidates/V0.lean` per wildcard rule (even though V17's *content* is V16's, the wildcard rule's parent field is what the sprint contract names; the byte content is V16's because there is no V0-specific property to revive).
  - Update `-- @sprint` line: `Sprint_Contracts/sprint_022.md`.
  - All `def`s, `theorem`s, `axiom`s, the `lemma_5_4_search` body — all byte-for-byte from V16. Score = 1/3500 unchanged.

- **`ProofRefinement/Lemma54/Scratch/sprint_022_research.py`** (NEW FILE, ≤ 250 lines):
  - Imports the existing `Numerical_Library.joint_phi_phip_invD2.compute_joint_phi_phip_invD2_bound` and `Numerical_Library.uzz_phi_sq.compute_uzz_phi_sq_bound` functions.
  - Runs `compute_joint_phi_phip_invD2_bound(n_per_edge=4096, n_p_subdiv=4, prec=200, K_max=80)` and prints the certified arb sup. (Cache miss expected; ~60–120s.)
  - Runs `compute_uzz_phi_sq_bound(n_per_edge=4096, n_p_subdiv=4, prec=200, K_max=80)` and prints the certified arb sup. (Cache miss expected; ~60–120s.)
  - Optionally runs both at `n_per_edge=8192` if the 4096 results suggest meaningful improvement (skip if 4096 gives < 5% reduction over 2048).
  - Implements `compute_factored_uderiv_bound(...)` mirroring the structure of `_compute_uzz_phi_sq_for_params` (same imports — `_iter_rect_boundary`, `eval_H_eta_at_acb`, `eval_H_eta_deriv_at_acb`, `_eval_H_eta_p_pp_at_acb`, `_H0_at_acb`, `_H0_prime_at_acb`, `_H0_pp_at_acb`) and computing per-cell `(abs_ub(Phi) · abs_ub(2·Phi'·D - DD·Phi)) / abs_lb(D)^3`. Run at `n_per_edge=2048, n_p_subdiv=4, prec=200`.
  - Compare `factored_sup` against V16's bound `2·joint + uzz_phi_sq ≈ 5.5·10⁻⁴` and the merged `≈ 6.93·10⁻³` from `sprint_022_planner_full_merge.py`. Print the comparison.
  - Print all numbers in a single summary block to stdout AND tee them to `Scratch/sprint_022_research_findings.md`.
  - Do NOT cache anything outside `Numerical_Library/.cache/` (the existing `cached_run` plumbing is reused via the imported functions).

- **`ProofRefinement/Lemma54/Scratch/sprint_022_research_findings.md`** (NEW FILE, ≤ 200 lines):
  - Markdown summary of the numerical findings. Sections: "Setup", "L1: Resolution sensitivity (joint, uzz_phi_sq at n_per_edge ∈ {2048, 4096, 8192})", "L2: Factored bound at production resolution", "Recommendation for sprint_023".
  - The "Recommendation" section is the key output — one paragraph that says either:
    - "L1-RUN: at n_per_edge=4096, joint drops from `1.989·10⁻⁴` to `X·10⁻⁴` and uzz_phi_sq drops to `Y·10⁻⁴`, suggesting sprint_023 should be an oracle-precision-tightening sprint targeting Cr_val = 1/Z." (with concrete X, Y, Z), OR
    - "L1-DEAD: at n_per_edge=4096, joint is unchanged within 5%, indicating value-precision dominates and L1 is exhausted. Sprint_023 should pivot to L2/L3."
    - "L2-WIN: factored sup ≈ V (V < 2·joint + uzz_phi_sq), suggesting a factored-oracle replacement direction."
    - "L2-DEAD: factored sup ≈ V (V > 2·joint + uzz_phi_sq), confirming the factored direction is also intervalarithmetic-loose; sprint_023 should pivot to a non-decomposition direction (Lagrange-3 remainder, identity-(75)-refine, or a non-oracle proposal for an enlarged-domain Cauchy axiom)."
  - The Generator MUST commit to *one* of these recommendations based on the actual numbers, not hedge.

- **NO edits** to: any file in `Numerical_Library/` (joint_phi_phip_invD2.py, uzz_phi_sq.py, etc. — the script imports them as-is), `Proof/Lib/Lemma54_Paper*.lean`, `Proof/SearchConfig.lean`, `lemma.toml`, any `V<K>.lean` for `K ≤ 16`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Bulletin.md` (Bulletin update is the Planner's job after the contract is written), or `Experience.md` (the Generator may append an Experience.md entry per existing convention but it is NOT a hard requirement for this sprint).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V17.lean` exits 0 (compiles clean, no `sorry`). Mechanically: `cd /home/rsaha/projects/grothendieck && lake env lean ProofRefinement/Lemma54/Candidates/V17.lean; echo "exit=$?"` should print `exit=0`.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V17.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer == 1 AND score.denom == 3500` (i.e., V17 byte-identical to V16's score, no regression). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; assert r["score"]["numer"] == 1 and r["score"]["denom"] == 3500, r["score"]; print("V17 Cr_val unchanged at 1/3500 -- wildcard procedural pass")'`.

3. `Scratch/sprint_022_research_findings.md` exists, is ≥ 30 lines, and contains a "Recommendation for sprint_023" header followed by exactly ONE of the four pre-specified labels: `L1-RUN`, `L1-DEAD`, `L2-WIN`, or `L2-DEAD`. Mechanically: `test -f ProofRefinement/Lemma54/Scratch/sprint_022_research_findings.md && wc -l ProofRefinement/Lemma54/Scratch/sprint_022_research_findings.md | awk '{ if ($1 < 30) exit 1 }' && grep -E '^\*?\*?(L1-RUN|L1-DEAD|L2-WIN|L2-DEAD)' ProofRefinement/Lemma54/Scratch/sprint_022_research_findings.md | head -1`.

(All three are mechanically checkable via `bash` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration, any new `[[oracles]]` entry, or any new free-floating analytic axiom. This is a research sprint — the only Lean delivered is V17 = V16 byte-identical, no axiom changes.
- Modify any of the Numerical_Library Python files (`joint_phi_phip_invD2.py`, `uzz_phi_sq.py`, `u_zz.py`, `m_phi.py`, `m_phi_prime.py`, `m_pp.py`, `inv_F_p_z.py`, `m_bound.py`, `r_bound.py`, `_phi_loader.py`, `_arb_helpers.py`, `types.py`, `__init__.py`). The research script in `Scratch/` imports these modules but must not alter them; in particular, it must not change `safety_abs`, `max_denom`, `n_per_edge`, or `prec` defaults. Pass parameters explicitly when calling.
- Modify `Proof/`, `Proof/Lib/Lemma54_Paper*.lean`, `Proof/SearchConfig.lean`, `lemma.toml`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any candidate file `V<K>.lean` for `K ≤ 16`. Note: the score is *intentionally* unchanged at `1/3500` — V17 is procedural for the wildcard cadence, not a refinement.
- Use `sorry`, `admit`, or `native_decide` in `V17.lean` (it's a copy of V16 which has no such tactics; preserve that property).
- File a proposal in `Proposals/`. This sprint produces internal research output, not a trust-base expansion request.
- Create new files OUTSIDE the named locations. Allowed new files: `Candidates/V17.lean`, `Scratch/sprint_022_research.py`, `Scratch/sprint_022_research_findings.md`. Optional: an `Experience.md` append (existing convention, not a hard requirement). NO docs, NO READMEs, NO test files outside `Scratch/`, NO new `Numerical_Library/` files.
- Run the high-resolution scans without first checking the cache (`Numerical_Library/.cache/`) for existing entries at the requested parameters; if such an entry exists, the script's `cached_run` reuse will hit it and avoid the recompute. The script must call the `compute_*_bound` functions (which themselves use `cached_run`) rather than reimplementing the cell scan from scratch.
- Spend more than 30 minutes on the high-resolution arb scans. If `n_per_edge=4096` takes > 10 minutes for a single oracle (estimated ~60–120s based on linear scaling from `n_per_edge=2048`'s 30–60s), abort and skip the `n_per_edge=8192` run; record the timing in the findings file. The factored-bound scan at `n_per_edge=2048` is the highest-priority output and must complete.
- Iterate on the recommendation label after the numbers are computed. Pick exactly ONE label, commit to it. The next Planner reads the label first; an "ambiguous" or "all four" recommendation is worse than any single committed one.

## Time budget

≤ 60 minutes runtime total. Breakdown: ~5 min for V17 = V16 copy + header update; ~30 min for the joint oracle reruns at `n_per_edge=4096` (two oracles, ~60–120s each, plus cache write); ~15 min for the factored-bound scan at production resolution (similar timing to existing oracles); ~10 min for writing `sprint_022_research_findings.md` and committing to a recommendation label. Soft cap 75% of context — should be well under since most of the work is plumbing the existing `Numerical_Library` functions rather than novel Lean.

## Stop conditions for the Generator

- All three acceptance criteria met (V17 compiles, evaluator passes at unchanged 1/3500, research findings file exists and contains a committed recommendation label) → `STATUS=READY_FOR_EVALUATION`.

- Cannot satisfy criteria without violating "Out of scope" (e.g., the joint oracle's high-resolution rerun unexpectedly *increases* the certified bound, suggesting a numerical bug in the oracle code) → `STATUS=BLOCKED`, naming the unexpected behavior, and the next Planner can investigate. Should not happen — `cached_run` is deterministic given the same parameters.

- The factored-bound scan diverges or returns `inf` (e.g., `D` corner certify_positive fails in some cell) → record the diagnostic in the findings file, mark the recommendation as `L2-DEAD` (interval-arithmetic on the inner difference is too loose), and proceed.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. (Should not happen — research sprints touch zero Lean axioms.)

- Soft context cap exceeded (very unlikely for this sprint) → `STATUS=BLOCKED`, "context cap exceeded; please re-scope". The recovery is for the next Planner to split the research script into two sprints (one per oracle resolution probe).
