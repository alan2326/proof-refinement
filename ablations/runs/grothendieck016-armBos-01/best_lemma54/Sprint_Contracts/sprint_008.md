# Sprint 008: Tighten the M-bound oracle precision and drop `M_val` from `432` to `431`, dropping `Cr_val` from `1153569600` to `1148240000`

**Created**: 2026-04-30 04:00 by Planner
**Parent candidate**: `Candidates/V5.lean`
**Target file**: `Candidates/V6.lean`
**Direction**: M-precision-tighten (sprints 005, 006, 007 were all R-axis: Cr-formula structure, R-as-rational, direct sinh bound. The R lever is now nearly at its analytic floor (`sinh(49/50) ≈ 1.1446` vs current `R_rat = 23/20 = 1.15`, leaving only ~0.5% room). Time to switch axes. Sprint 003 last visited the M lever, dropping M from 4000 to 432 via a Rouché-tightened rectangle. The current `compute_M_bound_tight` at `(δ=163/1000, B=1115/1000)` returns `bound = 4318113/10000 = 431.81` at the default low-precision settings (`n_per_edge=1024, prec=200, safety_rel=1e-3`), but the underlying arb ball is `[429.78 +/- 1.60]` (true M ≈ 430.18). Bumping the oracle's internal precision to `n_per_edge=4096, prec=400, safety_rel=1e-4` gives `bound = 215309/500 = 430.62`, well below the integer 431. This sprint retargets the oracle's precision parameters and drops `M_val` from `432` to `431`. The `compute_M_bound_tight` signature stays unchanged — only its internal numerical params tighten. NO new oracle, NO new axiom.)
**Tier**: cheap

## Goal (one sentence)

Create `Candidates/V6.lean` (parent: V5) that retargets `Numerical_Library/m_bound.py:compute_M_bound_tight` to use the higher-precision arb settings `n_per_edge=4096, prec=400, max_denom=10000, safety_rel=1e-4` (yielding oracle bound `≈ 430.62 < 431`), redefines `M_val := 431`, redefines `Cr_val := 1148240000` (= `16 · 431² · (23/20) · (43/20) / (2/25)²` rounded up to a clean multiple of `10000` with comfortable nlinarith margin `≈ 30.84`), and updates the Cr-monotonicity literals in `lemma_5_4_search` accordingly — taking `score.approx` from `1.153570·10⁹` to `1.148240·10⁹`, a `1.00465×` reduction (≈ 0.462% off the V5 baseline) by switching axes from R to M.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_008_M_tight.py` (importing `Numerical_Library.compute_M_bound`) shows that bumping `compute_M_bound_tight`'s precision from `(n_per_edge=1024, prec=200, safety_rel=1e-3, max_denom=10000)` to `(n_per_edge=4096, prec=400, safety_rel=1e-4, max_denom=10000)` shrinks the certified rational bound from `4318113/10000 = 431.811` to `215309/500 = 430.618`, a 0.276% drop in M giving `(431/432)² = 0.99537`, a 0.462% drop in `M²` and hence in `Cr_tight`; with `M_val = 431` and `R_rat = 23/20`, `Cr_min = 16·431²·(23/20)·(43/20)·(625/4) = 4592940725/4 = 1148235181.25`, so the next clean multiple-of-10⁴ is `1148240000` with `nlinarith` margin `1148240000·(2/25)² − 16·431²·(23/20)·(43/20) = 30.84` (verified numerically), comfortably above the V5-style `< 0.05` brittle margins. The R lever has been the focus of sprints 005, 006, 007 (Cr-formula → R-as-rational → direct sinh) and is approaching its floor (`sinh(49/50) ≈ 1.1446`, current bound `23/20 = 1.15`, only `0.5%` headroom); the M lever — last visited in sprint 003 when M dropped 4000 → 432 — still has room because the rectangle `(163/1000, 1115/1000)` Rouché-certifies M ≈ 430.18 but the low-precision oracle reports 431.81. No new axiom, no new oracle: the audited set stays at 3 Lean primitives + 12 trusted analytic + `h_M_oracle` + `h_oracle_domain_contains_image`, identical to V5; only `compute_M_bound_tight`'s internal params change (a permitted "retarget" per `AGENT_BRIEF.md`).

## Concrete edits expected

- `ProofRefinement/Lemma54/Numerical_Library/m_bound.py`: in `compute_M_bound_tight`'s `params` dict (currently lines 156–161), change the oracle's internal precision parameters in-place:
  - `n_per_edge`: `1024` → `4096`
  - `prec`: `200` → `400`
  - `safety_rel`: `1e-3` → `1e-4`
  - `max_denom`: `10000` (unchanged)
  - `delta`, `B`, `r`, `eta`: unchanged.

  Also update the docstring (lines 150–155) to reflect the new precision and the resulting `M ≈ 430.62` bound. Function signature stays unchanged; this is a retarget of internal precision, not a new oracle. The first call after the edit takes ~1–2 minutes (then is cached in `Numerical_Library/.cache/`).

- `ProofRefinement/Lemma54/Candidates/V6.lean`: created as a copy of `Candidates/V5.lean` with the following minimal, surgical changes (no structural rewrites):

  1. Header comment block updated: declare `-- @parent Candidates/V5.lean`, `-- @sprint Sprint_Contracts/sprint_008.md`, and explain that V6 retargets the oracle precision (`n_per_edge=4096, prec=400, safety_rel=1e-4`) and tightens `M_val` from `432` to `431`, dropping `Cr_val` from `1153569600` to `1148240000` (a 0.462% reduction). Note that R remains at `23/20` (V5's bound) — this sprint's axis is M, not R.

  2. Replace `def M_val : ℝ := 432` with `def M_val : ℝ := 431`. The accompanying docstring should clarify that the oracle's higher-precision arb ball is `[430.18 +/- 0.5]`-ish (depending on the precision choice), rationalized to `215309/500 ≈ 430.62`, well below the integer ceiling `431`. `M_val_pos`, `M_val_nn` proofs (`unfold M_val; norm_num`) work unchanged with `431` instead of `432`.

  3. Replace `def Cr_val : ℝ := 1153569600` with `def Cr_val : ℝ := 1148240000`. Update the docstring to state the new arithmetic identity:
     `1148240000 ≥ 16 · 431² · (23/20) · (43/20) / (2/25)² = 16·185761·989/400·625/4 = 4592940725/4 = 1148235181.25`,
     with the closing margin `1148240000 · (2/25)² − 16·431²·(23/20)·(43/20) = 30.84 > 0`. `Cr_val_nn` works unchanged (`norm_num` closes `0 ≤ 1148240000`).

  4. **Do not modify** `R_val_paper_le_twentythree_twentieths` (the helper from V5). It stays exactly as-is — R is not the axis this sprint.

  5. **Do not modify** `delta_val`, `B_val`, `oracle_domain`, `h_M_oracle`'s signature, or `h_oracle_domain_contains_image`. The rectangle `Ω(163/1000, 1115/1000)` stays; only the oracle's internal precision tightens.

  6. In `theorem lemma_5_4_search`, update the closing `nlinarith` step's literals: V5's `Cr_val * (2/25)² = 1153569600 · 4/625 = 7382845.44` becomes V6's `1148240000 · 4/625 = 7348509.44`. The polynomial identity to be closed is `16 · 431² · R · (R+1) ≤ 1148240000 · (2/25)²` given `0 ≤ R ≤ 23/20`; numerically `LHS_max = 16·431²·(23/20)·(43/20) = 7348705.16` and `RHS = 7348509.44`. Wait — that would make the inequality **fail**. Let me re-verify: `LHS = 16·185761·989/400 = 16·185761·2.4725 ≈ 7349... `

     **Correction**: After re-checking, `Cr_val · (2/25)² = 1148240000 · 4/625 = 7348736.0`. And `LHS_max = 16·431²·(23/20)·(43/20) = 16·185761·989/400 = 16·459116/400 = ...`. Let `Scratch/planner_008_M_tight.py` be authoritative — it computes `LHS = 7348705.16`, `Cr_val·(1-r)² = 7348736.00`, margin `= 30.84 > 0`. So the inequality holds: `1148240000·4/625 ≥ 16·431²·(23/20)·(43/20)`. The `nlinarith` hints `sq_nonneg (R - 23/20)`, `sq_nonneg R`, `mul_nonneg hR_nn' hR_nn'` from V5 should still close the polynomial; if not, add `mul_self_nonneg (R - 23/20)` or make the literals explicit.

  7. **Do not** edit `Proof/Lib/Lemma54_Paper*.lean`, `lemma.toml`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, or any historical candidate (`V0.lean` … `V5.lean`).

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_008` summarising the M-precision retarget (no claims about pass/fail).

## Acceptance criteria

1. `test -f ProofRefinement/Lemma54/Candidates/V6.lean` returns 0; `git status --porcelain` shows additions only to `Candidates/V6.lean` (new), modifications to `Numerical_Library/m_bound.py`, plus optional appends to `Experience.md` / `Bulletin.md`. **No edits** to `Proof/Lib/Lemma54_Paper*.lean`, `Candidates/V0.lean` … `V5.lean`, `lemma.toml`, `Evaluator.py`, `LeanProof/`, or `ProofGraph/`.

2. `lake env lean ProofRefinement/Lemma54/Candidates/V6.lean` exits 0 (the file compiles cleanly, no `sorry` survives), and `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V6.lean` exits 0 with `"status":"ok"` in the appended JSON line; the oracle gate passes (i.e., `compute_M_bound_tight().bound ≤ M_val`, with `oracle_bound ≈ 215309/500 = 430.62 ≤ 431 = M_val`).

3. The new entry's `score.approx` is finite and equals `1148240000.0` exactly (i.e. `score.numer/score.denom == 1148240000/1`); the `axioms_used` list contains exactly the 12 trusted analytic axioms + `h_M_oracle` + `h_oracle_domain_contains_image` + 3 Lean primitives (no new axiom, no `sorryAx`). The score is strictly less than V5's `1153569600`.

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere.
- Add a new `[[oracles]]` entry in `lemma.toml`. The `compute_M_bound_tight` retarget is a precision change of the existing oracle, not a new oracle.
- Modify `Proof/Lib/Lemma54_Paper.lean`, `Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv_Single.lean`, or any other file in `Proof/Lib/`. The `Cr_tight` chain stays untouched.
- Modify `Candidates/V0.lean` through `V5.lean`, `Sprint_Contracts/sprint_001.md` through `sprint_007.md`, the `Refinement_Log/log.jsonl` entries, or any historical record.
- Modify `lemma.toml`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, or any helper script.
- Modify `Numerical_Library/r_bound.py`, `Numerical_Library/types.py`, `Numerical_Library/_arb_helpers.py`, `Numerical_Library/__init__.py`, or any cache files in `Numerical_Library/.cache/`. Only `m_bound.py`'s `compute_M_bound_tight` defaults change.
- Pick a different `M_val` than `431`. Tighter (e.g. `M_val = 4307/10`) shrinks the `nlinarith` margin to `≈ 0.005`, which is brittle; looser (e.g. `M_val = 4315/10`) sacrifices score. `431` is the chosen optimum: clean integer, `0.46%` reduction, generous `≈ 30.84` margin.
- Change `delta_val`, `B_val`, or the underlying rectangle. The Rouché certification of `Ω(163/1000, 1115/1000)` is what `h_oracle_domain_contains_image` axiomatizes; changing the rectangle would require a separate sprint.
- Pick a different `Cr_val` than `1148240000`. `1148240000 = ⌈Cr_min/10000⌉ · 10000` where `Cr_min = 16·431²·(23/20)·(43/20)·(625/4) = 1148235181.25`. Smaller (e.g. `1148236000`) shrinks the margin to ~5; larger (e.g. `1148300000`) sacrifices score. `1148240000` is the chosen optimum: multiple-of-`10⁴`, `0.46%` reduction, generous `≈ 30.84` `nlinarith` margin.
- Change the precision params other than as specified (`n_per_edge=4096, prec=400, safety_rel=1e-4`). Higher precision (e.g. `n_per_edge=8192`) wastes compile time without further reducing the bound below `431`; lower precision (e.g. `prec=300`) may fail to certify `bound ≤ 431`.

## Time budget

≤ 25 minutes runtime; soft cap 75% of context. Most of the budget is the first oracle call after the precision bump (cache miss, ~60–90s) plus the standard Lean compile/audit cycle (~10–15s). The Lean edits are mechanical literal substitutions.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
