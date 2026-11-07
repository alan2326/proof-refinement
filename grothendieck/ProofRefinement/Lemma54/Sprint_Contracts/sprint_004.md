# Sprint 004: Drop the loose `(2R+1)(1-r)³ ≤ 16R` algebraic step; switch to `Cr_tight = 16 M² R (R+1) / (1-r)²`

**Created**: 2026-04-30 02:50 by Planner
**Parent candidate**: `Candidates/V1.lean`
**Target file**: `Candidates/V2.lean`
**Direction**: Cr-formula-tighten (use the constant the proof already establishes for `‖∂²_p F_inv‖`, instead of weakening it via the loose `(2R+1)(1-r)³ ≤ 16R` algebraic step)
**Tier**: checkpoint

## Goal (one sentence)

Add a parallel proof chain `Cr_tight` / `F_inv_p_second_deriv_bound_tight` / `lemma_5_4_paper_on_domain_tight` in `Proof/Lib/Lemma54_Paper*.lean` that bounds `‖∂²_p F_inv‖ ≤ 32 M² R (R+1) / (1-r)²` directly (skipping the algebraic step that bloats the constant by ~8340×), and create `Candidates/V2.lean` whose sink theorem delegates to `lemma_5_4_paper_on_domain_tight` with `Cr_val := 16 * M_val² * R_val * (R_val + 1) / (1 - r)²` (where `R_val = R_val_paper r`), taking `Cr_val` from V1's `≈ 9.55·10¹²` to `≈ 1.145·10⁹` (an ≈ 8340× reduction).

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_Cr_tight_v2.py` (mpmath at 50 dps) computes that at `(r=23/25, M=432, R=sinh(24/25))` the existing proof of `F_inv_p_second_deriv_bound_paper` (in `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`, lines 663–683) actually establishes `‖u''‖ ≤ 32 M² R (R+1) / (1-r)² ≈ 2.290·10⁹`, but then weakens this to `2 · Cr_paper r M R ≈ 1.910·10¹³` via `alg_step_paper`'s `(2R+1)(1-r)³ ≤ 16R` — and at our parameters `(2R+1)(1-r)³ ≈ 1.68·10⁻³` while `16R ≈ 1.83·10¹`, so the algebraic step is loose by a factor of ≈ 10870×, propagating to an 8340× loss on `Cr_paper / Cr_tight`. The Lagrange Taylor step `taylor_remainder_p` (in `Lemma54_Paper_Taylor.lean`, line 109) takes `Cr` as a parameter, so substituting `Cr_tight = 16 M² R (R+1) / (1-r)²` in place of `Cr_paper r M R` requires no new analysis — only that we cut the proof of `F_inv_p_second_deriv_bound_paper` short at line 683 (after the existing `h_arith` simplification gives the LHS literally `32 M² R (R+1) / (1-r)²`). No new axioms are introduced; the 12 trusted IFT axioms and 2 oracle axioms remain unchanged, audit count stays at 17 (3 lean primitives + 12 IFT + 2 oracle), and the score numerically drops by ≈ 8340× from `≈ 9.55·10¹²` to `≈ 1.145·10⁹`.

## Concrete edits expected

- `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`: add (alongside the existing `Cr_paper`/`Cr_refined` block in Section 5)
  1. `def Cr_tight (r M R : ℝ) : ℝ := 16 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2` with a brief docstring noting that this is the constant the paper proof's Step 5 derivation actually establishes (before the loose algebraic step).
  2. `theorem Cr_tight_nonneg {r M R : ℝ} (hr1 : r < 1) (hM : 0 ≤ M) (hR : 0 ≤ R) : 0 ≤ Cr_tight r M R` — single-line `unfold Cr_tight; positivity` or `nlinarith` proof.

- `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`: add (after the existing `F_inv_p_second_deriv_bound_paper`, with the same hypothesis bundle)
  1. `theorem F_inv_p_second_deriv_bound_tight` with conclusion `≤ 2 * Cr_tight r M (R_val_paper r)` — i.e. `≤ 32 M² R (R+1) / (1-r)²`. The proof body is a copy of `F_inv_p_second_deriv_bound_paper` truncated at the `rw [h_arith] at h_bound_RM` line (line 683), so it stops with `h_bound_RM` already in the form `‖u''‖ ≤ 32 * M ^ 2 * R * (R + 1) / (1 - r) ^ 2`, then closes with a one-line `2 * Cr_tight r M R = 32 * M^2 * R * (R + 1) / (1 - r)^2` rewrite (provable by `unfold Cr_tight; ring` modulo `(1 - r) ^ 2 ≠ 0`). The Generator may keep both theorems by sharing common lemmas or copy-pasting the body — either is acceptable.

- `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean`: add (after the existing `lemma_5_4_paper_on_domain`)
  1. `theorem lemma_5_4_paper_on_domain_tight` with the same hypotheses as `lemma_5_4_paper_on_domain` but conclusion `≤ Cr_tight r M (R_val_paper r) * p ^ 2`. The proof body is a copy of `lemma_5_4_paper_on_domain` (lines 109–231) with two changes:
     - Replace `set Cr := Cr_paper r M (R_val_paper r) with hCr_def` by `set Cr := Cr_tight r M (R_val_paper r) with hCr_def` and `Cr_paper_nonneg` by `Cr_tight_nonneg`.
     - Replace the call to `F_inv_p_second_deriv_bound_paper` by `F_inv_p_second_deriv_bound_tight`.
     The remainder of the proof (the `iteratedDerivWithin`-vs-`iteratedDeriv` glue, the `taylor_remainder_p` invocation) is unchanged because `taylor_remainder_p` is `Cr`-polymorphic.

- `ProofRefinement/Lemma54/Candidates/V2.lean`: created as a copy of `Candidates/V1.lean` with
  1. Header comment block updated: declare `-- @parent Candidates/V1.lean`, `-- @sprint Sprint_Contracts/sprint_004.md`, and explain that V2 switches `Cr_val`'s formula from `Cr_paper` to `Cr_tight`, eliminating the `(2R+1)(1-r)³ ≤ 16R` algebraic-step slack.
  2. `def Cr_val : ℝ := Braverman.Paper.Cr_paper …` → `def Cr_val : ℝ := Braverman.Paper.Cr_tight Braverman.SearchConfig.r M_val (Braverman.Paper.R_val_paper Braverman.SearchConfig.r)`.
  3. `theorem Cr_val_nn` updated to call `Braverman.Paper.Cr_tight_nonneg` instead of `Cr_paper_nonneg` (same argument list).
  4. The sink theorem `lemma_5_4_search` body changed from `Braverman.Paper.lemma_5_4_paper_on_domain …` to `Braverman.Paper.lemma_5_4_paper_on_domain_tight …` (identical argument list).
  5. Numerical witnesses (`M_val`, `delta_val`, `B_val`) and oracle axioms remain literally unchanged from V1.

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_004` summarising the Cr-formula switch (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V2.lean && test -f ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean && test -f ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Single.lean && test -f ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V2.lean` and the four files listed above (plus optional appends to `Experience.md`/`Bulletin.md`). No other paths appear; in particular `Candidates/V0.lean`, `Candidates/V1.lean`, `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, and `ProofGraph/` are untouched.
2. `lake env lean ProofRefinement/Lemma54/Candidates/V2.lean` exits 0 (the file compiles cleanly), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V2.lean` exits 0 with `"status":"ok"` in the appended JSON line and no `sorryAx` in `axioms_used`.
3. The new entry's `score.approx` is strictly less than `2.0e9` (concretely expected ≈ `1.145e9`); equivalently, `score.approx` is at most V1's `9.560e12 / 5000 ≈ 1.91e9`. The `axioms_used` list contains exactly the same 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives that V1's audit reports — no new axiom (in particular no new analytic axiom in `Lemma54_Paper.lean`).

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere — the new `Cr_tight` / `F_inv_p_second_deriv_bound_tight` / `lemma_5_4_paper_on_domain_tight` declarations must all be `def` / `theorem`, fully proved from the existing axioms.
- Modify, delete, or replace the existing `Cr_paper`, `Cr_refined`, `F_inv_p_second_deriv_bound_paper`, `lemma_5_4_paper_on_domain`, or `lemma_5_4_paper` declarations. The new declarations live alongside the existing ones; downstream `LeanProof/`, `ProofGraph/`, and `Candidates/V0.lean`/`V1.lean` continue to use the old chain.
- Modify `Candidates/V0.lean`, `Candidates/V1.lean`, `Sprint_Contracts/sprint_001.md`, `Sprint_Contracts/sprint_002.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `lemma.toml`, `Numerical_Library/`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script. The numeric witnesses (`M_val = 432`, `delta_val = 163/1000`, `B_val = 1115/1000`) and oracles are unchanged from V1.
- Refactor or rewrite anything beyond the additions listed in "Concrete edits expected". In particular, do not factor out shared lemmas between `F_inv_p_second_deriv_bound_paper` and `F_inv_p_second_deriv_bound_tight` if it requires touching the original theorem's proof body.
- Change `SearchConfig.eta`, `SearchConfig.r`, the `R_val_paper` definition (`sinh((3+r)/4)`), or the rectangle parameters.

## Time budget

≤ 60 minutes runtime; soft cap 75% of context.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
