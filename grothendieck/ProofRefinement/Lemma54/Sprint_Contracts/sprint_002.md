# Sprint 002: Switch to tight Rouché-certified rectangle Ω(163/1000, 1115/1000), drop M_val to 432

**Created**: 2026-04-30 02:35 by Planner
**Parent candidate**: `Candidates/V0.lean`
**Target file**: `Candidates/V1.lean`
**Direction**: rectangle-tighten (replace production rectangle with the tighter Rouché-certified rectangle Ω(163/1000, 1115/1000); recompute M_val on the smaller rectangle)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V1.lean` with `delta_val := 163/1000`, `B_val := 1115/1000`, and `M_val := 432`, and retarget the M-oracle in `lemma.toml` from `compute_M_bound_production` to `compute_M_bound_tight`, taking `Cr_val` from V0's `≈ 8.19·10¹⁴` to `≈ 9.55·10¹²` in a single coordinated structural move (≈ 98.8% reduction).

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_rouche_tight.py` (run today at prec=200) directly verifies that the tight rectangle Ω(δ=163/1000, B=1115/1000) passes all four Step-1 / Rouché checks at `r_outer = (1+r)/2 = 24/25`: containment of `sin(r_outer·D)`, positive Rouché margin `m ≈ 2.63·10⁻⁴`, and a feasible `p_candidate ≈ 9.5·10⁻⁶` with `p·M_d < m` certified — so `h_oracle_domain_contains_image` remains a structurally sound seed axiom on this smaller rectangle (the existential `pr_paper` witness in the sink theorem can be chosen ≤ p_candidate). `Scratch/planner_M_tight_floor.py` then prints `compute_M_bound_tight = 4318113/10000 ≈ 431.81`, whose integer ceiling is **432** — the unique smallest integer M_val that the per-candidate Evaluator's oracle gate accepts on this rectangle. `Scratch/planner_axes.py` cross-checks the score in arb (256-bit): `Cr_paper(r=23/25, M=432, R=sinh(49/50))` evaluates to `≈ 9.5505·10¹²`, an 86× drop from V0's `≈ 8.19·10¹⁴` (vs only ≈ 0.81× achievable from M-only tightening on the production rectangle); this dwarfs any same-rectangle M tightening we could do and is a structurally distinct lever (rectangle change, not just M_val numeric edit).

## Concrete edits expected

- `ProofRefinement/Lemma54/Candidates/V1.lean`: created as a copy of `Candidates/V0.lean` with the following changes only:
  1. Header comment block updated to reference V1 / sprint_003 and to declare `-- @parent Candidates/V0.lean`. The header should explain that V1 switches to the tight Rouché-certified rectangle Ω(163/1000, 1115/1000) and tightens M_val to its integer floor 432 over `compute_M_bound_tight ≈ 431.81`.
  2. `def M_val : ℝ := 4000` → `def M_val : ℝ := 432`.
  3. `def delta_val : ℝ := 57 / 1000` → `def delta_val : ℝ := 163 / 1000`.
  4. `def B_val : ℝ := 293 / 250` → `def B_val : ℝ := 1115 / 1000`.
  5. The docstrings on `M_val`, `delta_val`, `B_val`, and `oracle_domain` updated to reflect the tight rectangle (no other prose changes).
  6. **No** changes to the sink theorem `lemma_5_4_search`, to the axiom signatures of `h_oracle_domain_contains_image` or `h_M_oracle`, or to any imports. The sink-theorem body still delegates to `Braverman.Paper.lemma_5_4_paper_on_domain` with the new `M_val` and the new `oracle_domain`.
- `ProofRefinement/Lemma54/lemma.toml`: in the `[[oracles]]` table for `axiom = "h_M_oracle"`, change `oracle_fn = "compute_M_bound_production"` to `oracle_fn = "compute_M_bound_tight"`. No other edits.
- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_003` summarising the rectangle switch and the resulting Cr_val reduction (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V1.lean` returns 0; `git status --porcelain` shows `Candidates/V1.lean` (new), `lemma.toml` (modified), and optional appends to `Experience.md` / `Bulletin.md`. No other paths appear.
2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V1.lean` exits 0 and the appended JSON line in `Refinement_Log/log.jsonl` has `"status":"ok"` with `"def_vals"` containing `"M_val":"432/1"`, `"delta_val":"163/1000"`, `"B_val":"1115/1000"`, and an audit message of the form `pass Braverman.PaperV0.h_M_oracle: declared M_val=432 ≥ oracle 4318113/10000`.
3. The new entry's `score.approx` is strictly less than `1.0e13` (concretely expected ≈ `9.55e12`); equivalently, `score.approx` < V0's `8.196e14` by a factor of at least 50×. The `axioms_used` list contains exactly the same 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives that V0's audit reports — no new axiom, no `sorryAx`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration. The structural axiom `h_oracle_domain_contains_image` retains the same signature and remains a seed axiom (its Rouché justification is now witnessed on the tight rectangle by `Scratch/planner_rouche_tight.py`; the production runner's wider rectangle remains valid and is unchanged).
- Modify `Candidates/V0.lean`, `Sprint_Contracts/sprint_001.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `Proof/`, `LeanProof/`, `ProofGraph/`, `Numerical_Library/`, `Evaluator.py`, or any helper script. (`compute_M_bound_tight` already exists in `Numerical_Library/m_bound.py`; no edit needed.)
- Refactor or rewrite anything beyond the four numeric defs (`M_val`, `delta_val`, `B_val`, header/docstring), the single `oracle_fn` retarget in `lemma.toml`, and the `Experience.md` append.
- Change `SearchConfig.eta`, `SearchConfig.r`, the `Cr_paper` formula, or any analytic axiom. (`Cr_val` re-evaluates automatically because it consumes `M_val` and `R_val_paper SearchConfig.r`; the latter is unchanged.)

## Time budget

≤ 20 minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
