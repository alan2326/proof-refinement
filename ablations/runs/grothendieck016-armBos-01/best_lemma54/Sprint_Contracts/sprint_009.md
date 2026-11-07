# Sprint 009: Push delta to its Rouché-margin floor (`163/1000 → 1635/10000`); drop M_val from `431` to `428`, dropping `Cr_val` from `1148240000` to `1132310000`

**Created**: 2026-04-30 04:30 by Planner
**Parent candidate**: `Candidates/V6.lean`
**Target file**: `Candidates/V7.lean`
**Direction**: rectangle-delta-tighten (sprint 003 originally chose `δ = 163/1000` heuristically, then sprint 008 tightened only the oracle's *internal* precision while keeping the rectangle fixed. A finer Rouché-margin sweep at fixed `B = 1115/1000` reveals that `δ` can rise from `163/1000 = 0.163` to `1635/10000 = 0.1635` while still certifying the Rouché margin — but `δ ≥ 1636/10000` collapses the margin. Pushing `δ` to its Rouché-margin floor shrinks the M-ball from ≈ 430.18 → 427.71, a ~0.6% drop, allowing `M_val = 428` (vs V6's `431`). This is a *different sub-axis* than sprint 008's pure precision retarget — sprint 009 changes the underlying rectangle, which forces the precision retarget *and* the integer `M_val` drop *and* the rectangle's literal `delta_val` to all move together. Direction history: 005/006/007 (R-axis), 008 (M-precision); rectangle-delta is the natural next move and respects the no-same-axis-3-in-a-row rule.)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V7.lean` (parent: V6) that switches `delta_val` from `163/1000` to `1635/10000` (the largest rational ≤ 0.1640 keeping the Rouché margin certified positive at `B_val = 1115/1000`), retargets `compute_M_bound_tight`'s defaults to `(delta="1635/10000", B="1115/1000", n_per_edge=8192, prec=600, safety_rel=1e-5, max_denom=10000)` (oracle rational bound `855827/2000 ≈ 427.9135 < 428`), redefines `M_val := 428`, redefines `Cr_val := 1132310000` (= `⌈16 · 428² · (23/20) · (43/20) · (625/4)/10000⌉ · 10000` with comfortable nlinarith margin `624/25 = 24.96`), and updates the Cr-monotonicity literals in `lemma_5_4_search` accordingly — taking `score.approx` from `1.148240·10⁹` to `1.132310·10⁹`, a `1.0141×` reduction (≈ 1.387 % off the V6 baseline) by tightening the rectangle's `δ` to the Rouché floor.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_009_rect_tight.py` runs the production-side certified pipeline (`certify_sin_r_disk_in_omega`, `compute_rouche_margin_omega`, `compute_perturbation_bound_omega`, `choose_p`) on a fine `δ`-sweep at `B = 1115/1000` and finds that `δ = 1635/10000 = 0.1635` is the largest rational ≤ 0.164 keeping all four certifications passing (`im` & `re` containment, Rouché margin `m ≈ 1.10·10⁻⁴ > 0`, `p·M_d < m`); `δ = 1636/10000` already collapses to `Rouché margin ≤ 0`. At this floor rectangle `compute_M_rigorous(r=23/25, δ=1635/10000, B=1115/1000, n_per_edge=8192, prec=600)` returns the arb ball `[427.711 +/- 0.198]` (upper ≈ 427.909), and `compute_M_bound_tight` at `(n_per_edge=8192, prec=600, safety_rel=1e-5, max_denom=10000)` rationalizes to `855827/2000 = 427.9135`, well below the integer ceiling `428`; the resulting `Cr_min = 16·428²·(23/20)·(43/20)·(625/4) = 1132306100`, so `Cr_val = 1132310000` is the next clean multiple of `10⁴` above with nlinarith margin `Cr_val·(2/25)² − 16·428²·(23/20)·(43/20) = 7246784 − 7246759.04 = 624/25 = 24.96` (verified exactly via `Fraction`, matching V6's comfortable margin shape). The audited axiom set is unchanged (3 Lean primitives + 12 trusted analytic + `h_M_oracle` + `h_oracle_domain_contains_image`); only the rectangle literal `delta_val`, the oracle's internal params, the `M_val` integer, and the Cr-monotonicity literals move. Direction discipline: 005/006/007 were R-axis, 008 was M-precision (oracle internals only); 009 is rectangle-delta (the `δ` literal moves on the candidate side, *and* the oracle is retargeted to the new rectangle), respecting the no-same-axis-3-in-a-row rule and breaking decisively from V6 by changing the underlying domain Ω rather than just the precision.

## Concrete edits expected

- `ProofRefinement/Lemma54/Numerical_Library/m_bound.py`: in `compute_M_bound_tight`'s `params` dict (currently lines 164–169 of V6), retarget the defaults in-place:
  - `delta`: `"163/1000"` → `"1635/10000"`
  - `B`: `"1115/1000"` (unchanged)
  - `n_per_edge`: `4096` → `8192`
  - `prec`: `400` → `600`
  - `safety_rel`: `1e-4` → `1e-5`
  - `max_denom`: `10000` (unchanged)
  - `r`, `eta`: unchanged (`"23/25"`, `0.01`).

  Also update the docstring (lines 149–163) to reflect the new rectangle floor and the resulting `M ≈ 427.9135` certified bound. The docstring should note: *"sprint 009 sweeps `δ` at fixed `B = 1115/1000` and finds `δ = 1635/10000` is the Rouché-margin floor (`δ ≥ 1636/10000` fails). The certified arb ball is `[427.71 +/- 0.20]`; the rationalized bound at the bumped precision is `855827/2000 ≈ 427.9135 < 428`."* Function signature unchanged; this is a retarget of the rectangle defaults plus internal precision, not a new oracle. The first call after the edit takes ~3–5 minutes (cache miss at the new rectangle); thereafter cached.

- `ProofRefinement/Lemma54/Candidates/V7.lean`: created as a copy of `Candidates/V6.lean` with the following minimal, surgical changes (no structural rewrites):

  1. Header comment block updated: declare `-- @parent Candidates/V6.lean`, `-- @sprint Sprint_Contracts/sprint_009.md`, and explain that V7 pushes the rectangle's `δ` to its Rouché-margin floor (`163/1000 → 1635/10000`), retargets the oracle precision (`n_per_edge=8192, prec=600, safety_rel=1e-5`), and tightens `M_val` from `431` to `428`, dropping `Cr_val` from `1148240000` to `1132310000` (a 1.387 % reduction). Note that R remains at `23/20` (V5's bound) — the R-axis and M-precision-axis are deliberately *not* touched in this sprint.

  2. Replace `def delta_val : ℝ := 163 / 1000` with `def delta_val : ℝ := 1635 / 10000`. Update its docstring to reflect the new rectangle: *"Real-width parameter for the tight Rouché-certified oracle rectangle, pushed to its Rouché-margin floor at fixed `B_val = 1115/1000`. Sprint 009 found that `δ = 1635/10000 = 0.1635` is the largest rational ≤ 0.164 keeping the Rouché margin certified positive (≈ 1.10·10⁻⁴ at the chosen precision); `δ ≥ 1636/10000` collapses the margin."* The existing `delta_val_pos` proof (`unfold delta_val; norm_num`) works unchanged.

  3. Replace `def M_val : ℝ := 431` with `def M_val : ℝ := 428`. Update its docstring: the precision-bumped oracle at the new rectangle returns `compute_M_bound_tight ≈ 855827/2000 ≈ 427.9135`, well below `428`. `M_val_pos`, `M_val_nn` proofs (`unfold M_val; norm_num`) work unchanged.

  4. Replace `def Cr_val : ℝ := 1148240000` with `def Cr_val : ℝ := 1132310000`. Update the docstring to state the new arithmetic identity:
     `1132310000 ≥ 16 · 428² · (23/20) · (43/20) / (2/25)² = 16·183184·989/400·625/4 = 1132306100`,
     with the closing margin `1132310000 · (2/25)² − 16·428²·(23/20)·(43/20) = 7246784 − 181168976/25 = 624/25 = 24.96 > 0`. `Cr_val_nn` works unchanged (`norm_num` closes `0 ≤ 1132310000`).

  5. **Do not modify** `R_val_paper_le_twentythree_twentieths` (the helper from V5). It stays exactly as-is — R is not the axis this sprint.

  6. **Do not modify** `B_val`, `oracle_domain`, `h_M_oracle`'s signature, or `h_oracle_domain_contains_image`. The type-level rectangle is now `Ω(1635/10000, 1115/1000)` (smaller in the real direction) but the `axiom` declarations refer to it via `delta_val`/`B_val` parametrically, so their statements update automatically.

  7. In `theorem lemma_5_4_search`, update the closing `nlinarith` step's literals: V6's `Cr_val = 1148240000` becomes V7's `Cr_val = 1132310000`. The polynomial identity to be closed is `16 · 428² · R · (R+1) ≤ 1132310000 · (2/25)²` given `0 ≤ R ≤ 23/20`; numerically `LHS_max = 16·428²·(23/20)·(43/20) = 7246759.04` and `RHS = 1132310000·4/625 = 7246784`, margin `624/25 = 24.96` (≈ 80% of V6's margin `30.84`, still comfortable). The `nlinarith` hints `sq_nonneg (R - 23/20)`, `sq_nonneg R`, `mul_nonneg hR_nn' hR_nn'` from V6 should still close the polynomial unchanged.

  8. **Do not** edit `Proof/Lib/Lemma54_Paper*.lean`, `lemma.toml`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, or any historical candidate (`V0.lean` … `V6.lean`).

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_009` summarising the rectangle-floor retarget (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V7.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V7.lean` (new), modifications to `Numerical_Library/m_bound.py`, plus optional appends to `Experience.md` / `Bulletin.md`. **No edits** to `Proof/Lib/Lemma54_Paper*.lean`, `Candidates/V0.lean` … `V6.lean`, `lemma.toml`, `Evaluator.py`, `LeanProof/`, or `ProofGraph/`.

2. `lake env lean ProofRefinement/Lemma54/Candidates/V7.lean` exits 0 (the file compiles cleanly, no `sorry` survives), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V7.lean` exits 0 with `"status":"ok"` in the appended JSON line; the oracle gate passes (i.e., `compute_M_bound_tight().bound ≤ M_val`, with `oracle_bound ≈ 855827/2000 = 427.9135 ≤ 428 = M_val`).

3. The new entry's `score.approx` is finite and equals `1132310000.0` exactly (i.e. `score.numer/score.denom == 1132310000/1`); the `axioms_used` list contains exactly the 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives (no new axiom, no `sorryAx`). The score is strictly less than V6's `1148240000`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Add a new `[[oracles]]` entry in `lemma.toml`. The `compute_M_bound_tight` retarget is a precision + rectangle-defaults change of the existing oracle, not a new oracle.
- Modify `Proof/Lib/Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, or any other file in `Proof/Lib/`. The `Cr_tight` chain stays untouched.
- Modify `Candidates/V0.lean` through `V6.lean`, `Sprint_Contracts/sprint_001.md` through `sprint_008.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `lemma.toml`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script.
- Modify `Numerical_Library/r_bound.py`, `Numerical_Library/types.py`, `Numerical_Library/_arb_helpers.py`, `Numerical_Library/__init__.py`, or any cache files in `Numerical_Library/.cache/`. Only `m_bound.py`'s `compute_M_bound_tight` defaults change.
- Pick a different `delta_val` than `1635/10000`. Looser (`164/1000` and above) fails Rouché margin; tighter (`163/1000`) is V6's value (no improvement). The Rouché-margin floor `1635/10000` is the chosen optimum for `B = 1115/1000`.
- Pick a different `B_val` than `1115/1000`. Smaller `B` (e.g. `1114/1000`) fails containment (`sinh(r_outer) ≈ 1.11440 > 1.114`); larger `B` (e.g. `112/100 = 1120/1000`) increases M (≈ 430.0 vs 427.7 at the new floor). `1115/1000` stays optimal.
- Pick a different `M_val` than `428`. Tighter (e.g. `4280/10`) fails the oracle gate at the chosen precision (oracle bound is `855827/2000 = 427.9135` so `4280/10 = 428.0 ≥ 427.9135` *is* admissible, but the integer `428` is cleaner; using `4280/10` would offer no Cr improvement since `Cr_min` is already capped at the integer-`M` round-up). Looser (e.g. `M_val = 429`) sacrifices score.
- Pick a different `Cr_val` than `1132310000`. Smaller (e.g. `1132306200`) shrinks margin to ~3 (brittle); larger (e.g. `1132400000`) sacrifices score. `1132310000 = ⌈Cr_min/10000⌉ · 10000` is the chosen optimum: multiple-of-`10⁴`, generous nlinarith margin `624/25 ≈ 24.96`.
- Change the precision params other than as specified (`n_per_edge=8192, prec=600, safety_rel=1e-5`). Lower precision (e.g. `n_per_edge=4096, prec=400, safety_rel=1e-4`) gives oracle bound `≈ 4280841/10000 = 428.0841 > 428`, failing the gate. Higher precision (e.g. `n_per_edge=16384, prec=800`) wastes compile time without further reducing the bound below `428`.
- Switch axes (e.g. additionally tighten R or attempt to prove an axiom). One sprint, one direction.

## Time budget

≤ 30 minutes runtime; soft cap 75 % of context. Most of the budget is the first oracle call after the rectangle change (cache miss at the new rectangle + bumped precision: ~3–5 minutes) plus the standard Lean compile/audit cycle (~10–15 s). The Lean edits are mechanical literal substitutions.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
