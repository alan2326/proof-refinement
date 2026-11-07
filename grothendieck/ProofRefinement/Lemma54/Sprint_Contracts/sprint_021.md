# Sprint 021: Tighten `compute_joint_phi_phip_invD2_bound` rationalization (`safety_abs` 1e-4 → 1e-7) to retire the 33% oracle-ceiling slack on V15's term-1; drop `Cr_val` from `1/2600` to `1/3500` (1.35× win)

**Created**: 2026-04-30 10:30 by Planner
**Parent candidate**: `Candidates/V15.lean` (linear chain — V15 is the latest-PASS, `Cr_val = 1/2600 ≈ 3.846·10⁻⁴`, sprint_020's term-2-joint-oracle verdict). No reason to branch from an earlier candidate: V15's audit set (3 Lean primitives + 11 `F_inv_paper` seeds + `h_oracle_domain_contains_image` + 6 oracles, of which the new sink consumes only `h_joint_phi_phip_invD2_oracle`, `h_uzz_phi_sq_oracle`, plus `h_oracle_domain_contains_image`) is the right foundation. V16 only updates the rational ceiling exposed by `compute_joint_phi_phip_invD2_bound` and the matching `joint_phi_phip_invD2_val` literal; no new oracle, no new axiom, no new theorem statement.
**Target file**: `ProofRefinement/Lemma54/Candidates/V16.lean` (with one parameter change in `Numerical_Library/joint_phi_phip_invD2.py`).
**Direction**: oracle-ceiling-tightening (`safety_abs` parameter on the `compute_joint_phi_phip_invD2_bound` oracle, currently `1e-4`, is far too coarse for a value of order `2·10⁻⁴` — it inflates the certified arb sup by 50%; tighten to `1e-7` to match the sister oracle `compute_uzz_phi_sq_bound` and let `joint_phi_phip_invD2_val` drop from `3/10000` to `1/5000`). Direction-history check: 014=inline-oracle (inv_F_p_z), 015=formula-change (M_pp), 016=formula-change+inline-oracle (u_zz), 017=salvage, 018=oracle-ceiling-tightening, 019=inline-oracle (joint term-1), 020=inline-oracle (joint term-2). The "oracle-ceiling-tightening" axis was last used 3 sprints ago (018), with two inline-oracle sprints in between; no same-axis-3-times violation. Wildcard cadence: last wildcard was sprint_017 (branched from V11). Sprints 018, 019, 020, 021 = the 4th is sprint_021; this Planner explicitly defers the wildcard to sprint_022 because sprint_021 is a one-shot computable fix (≤30 min, no compounding risk) to retire 33% slack on the most recent infrastructure that would otherwise sit on the table indefinitely. Sprint_022 should be the wildcard.
**Tier**: cheap — surgical: one-line edit to `joint_phi_phip_invD2.py` defaults, copy V15 to V16, update one literal (`joint_phi_phip_invD2_val`) and one literal (`Cr_val`), update header comment. Estimated ~30 min runtime; soft cap 75% of context.

## Goal (one sentence)

Tighten `compute_joint_phi_phip_invD2_bound`'s default `safety_abs` from `1e-4` to `1e-7` (and `max_denom` from `10000` to `1000000`, consistent with `compute_uzz_phi_sq_bound`), update V15's `joint_phi_phip_invD2_val` from `3/10000` to `1/5000` to match the new oracle return, set V16's `Cr_val := 1/3500`, and verify the closing `norm_num` step proves `Cr_phi_uzz_direct_joint2 (1/5000) (153/1000000) ≤ 1/3500` (i.e., `553/2000000 ≤ 1/3500`).

## Mathematical insight (required, ≤ 5 sentences)

The arb oracle `compute_joint_phi_phip_invD2_bound` certifies `sup_{(p, w) ∈ [0, p_max] × Ω} ‖Phi · Phi' / D²‖ ≤ [0.00019886579287456120667 ± 5.46·10⁻²⁵]` (recovered from the cache file `Numerical_Library/.cache/<hash>.json`; see [`Scratch/sprint_021_planner_joint_safety_abs.py`](../Scratch/sprint_021_planner_joint_safety_abs.py)) — a value of order `1.989·10⁻⁴`. But the oracle's `arb_to_rational_ub` step then *inflates* this by `max(safety_rel · value, safety_abs) = max(1e-3 · 1.99e-4, 1e-4) = 1.0·10⁻⁴` and rounds up to `3/10000`, throwing away **33% absolute slack** with no improvement in trust (the certified arb interval is already exact to 25 digits). The `safety_abs = 1e-4` default was inherited from sprint_019's first draft when the value's order of magnitude wasn't yet known; sister oracle `compute_uzz_phi_sq_bound` (sprint_020) correctly uses `safety_abs = 1e-7` for its similar-order-of-magnitude (`1.525·10⁻⁴`) value, retiring all but 0.3% of its rationalization slack. Tightening `safety_abs` to `1e-7` produces the cleanly-rounded `1/5000 = 2·10⁻⁴`, a 33% term-1 reduction with **zero** change to the underlying arb scan, **zero** new axioms, **zero** new theorems. This is the simplest possible Cr_val win still on the table: a parameter cleanup of the most recent oracle, identical in spirit to sprint_018's V13 oracle-ceiling-tightening sweep.

## Why (≤ 3 sentences, must include numerical evidence)

[`Scratch/sprint_021_planner_joint_safety_abs.py`](../Scratch/sprint_021_planner_joint_safety_abs.py) loaded the cached arb result from `Numerical_Library/.cache/679a03db08c57d7b.json` (parameters `eta=0.01, delta=1635/10000, B=1115/1000, p_max=1, n_per_edge=2048, n_p_subdiv=4, prec=200, K_max=80`): `joint_phi_phip_invD2_str = "[0.00019886579287456120667 +/- 5.46e-25]"`. With tightened settings (`safety_rel=1e-3, safety_abs=1e-7, max_denom=1000000`), the planner verified via direct invocation of `arb_to_rational_ub` that the rounded ceiling becomes `1/5000 ≈ 2.0·10⁻⁴` — a 33% absolute reduction from `3/10000 = 3·10⁻⁴`. With `joint_phi_phip_invD2_val := 1/5000` and `uzz_phi_sq_val` unchanged at `153/1000000`, the new `Cr_phi_uzz_direct_joint2 = (1/5000) + (1/2)·(153/1000000) = 553/2000000 ≈ 2.765·10⁻⁴`; setting `Cr_val := 1/3500 = 2.857·10⁻⁴` leaves a 3.3% margin (very safe for `norm_num` rational arithmetic), and gives a `(1/2600)/(1/3500) = 1.346×` win over V15 (cumulative `2.87·10¹⁸×` over V0).

## Concrete edits expected

- **`ProofRefinement/Lemma54/Numerical_Library/joint_phi_phip_invD2.py`** (one-line parameter changes in the `compute_joint_phi_phip_invD2_bound` function signature):
  - Change `safety_abs: float = 1e-4` to `safety_abs: float = 1e-7`.
  - Change `max_denom: int = 10000` to `max_denom: int = 1000000`.
  - Update the function's docstring to mention the new defaults briefly (one line, like the existing one-line note in `uzz_phi_sq.py`).
  - Do NOT modify the cell-scanning algorithm, the per-cell arithmetic, the `_compute_joint_phi_phip_invD2_for_params` helper, the `_iter_rect_boundary` consumer, the `_H0_at_acb` / `_H0_prime_at_acb` helpers, or the `cached_run` key (the cache key intentionally excludes safety/max_denom parameters, so the new safety params hit the existing cache instantly with no recomputation).
  - Keep `safety_rel = 1e-3` (unchanged).

- **`ProofRefinement/Lemma54/Candidates/V16.lean`** (NEW FILE, copy of `V15.lean` with these specific changes):
  - Header comment: identify V16 as the term-1-rationalization-tightened variant of V15 (mention parent `V15.lean`, sprint `021`, target `Cr_val := 1/3500`, the unchanged oracle scan but tightened ceiling, and the expected ≥ 1.346× win factor).
  - Update the `def joint_phi_phip_invD2_val : ℝ := 3 / 10000` line to `def joint_phi_phip_invD2_val : ℝ := 1 / 5000`. (The V15 docstring remark "Set to `3/10000`" should be updated to `1/5000` and the docstring's "(from the certified arb sup of `1.989·10⁻⁴`)" wording should be added if not already present, but this is purely cosmetic and not part of the acceptance criteria.)
  - Update `def Cr_val : ℝ := 1 / 2600` to `def Cr_val : ℝ := 1 / 3500`.
  - Re-run/repair the closing `norm_num` step in `lemma_5_4_search` proving `Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val ≤ Cr_val`. At V16 values the inequality is `(1/5000) + (1/2)·(153/1000000) = 553/2000000 ≤ 1/3500 = 2000000/7000000000`. `norm_num` should close this directly; if not, fallback to `nlinarith` with no hints. Mathematically: `553/2000000 = 1.9355·10⁻⁵·(143)≈ 2.765·10⁻⁴` vs `1/3500 ≈ 2.857·10⁻⁴`, margin `~3.3%`.
  - Keep `M_val`, `delta_val`, `B_val`, `M_phi_val`, `M_phi_prime_val`, `inv_F_p_z_val`, `u_zz_bound_val`, `uzz_phi_sq_val` byte-identical to V15.
  - Keep all six oracle declarations (`h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle`, `h_joint_phi_phip_invD2_oracle`, `h_uzz_phi_sq_oracle`) byte-identical except the `joint_phi_phip_invD2_val` literal occurrence inside `h_joint_phi_phip_invD2_oracle`'s statement (which references `joint_phi_phip_invD2_val` by name, so the axiom statement itself doesn't need editing — only the `def` does).
  - Keep `h_oracle_domain_contains_image` byte-identical.
  - Keep all theorem-name references and the `lemma_5_4_search` body byte-identical except the closing `norm_num` step.

- **NO edits** to: `Proof/SearchConfig.lean`, `Proof/Lib/Lemma54_Paper.lean`, `Proof/Lib/Lemma54_Paper_Cauchy.lean`, `Proof/Lib/Lemma54_Paper_Identity.lean`, `Proof/Lib/Lemma54_Paper_Pderiv.lean`, `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`, `Proof/Lib/Lemma54_Paper_Taylor.lean`, `Proof/Lib/Lemma54_Paper_Main.lean`, `lemma.toml`, `Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py, m_bound.py, r_bound.py, uzz_phi_sq.py, _phi_loader.py, _arb_helpers.py, types.py, __init__.py}`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, or any candidate file `V<K>.lean` for `K ≤ 15`. The only Python file touched is `joint_phi_phip_invD2.py`; the only Lean file touched is the new `Candidates/V16.lean`.

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V16.lean` exits 0 (compiles clean, no `sorry`). Mechanically: `cd /home/rsaha/projects/grothendieck && lake env lean ProofRefinement/Lemma54/Candidates/V16.lean; echo "exit=$?"` should print `exit=0`.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V16.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer * 2600 < score.denom` (i.e., `Cr_val < 1/2600`, strictly tighter than V15). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; n,d = r["score"]["numer"], r["score"]["denom"]; assert n*2600 < d, (n,d); print("V16 Cr_val =", n, "/", d, "≈", n/d)'`.

3. The audited axiom set for V16 contains the existing oracle entry `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` with `kind: "oracle"`, `oracle_fn: "compute_joint_phi_phip_invD2_bound"`, `bound_field: "joint_phi_phip_invD2_val"`, `declared: "1/5000"`, `oracle_bound: "1/5000"`, `status: "pass"`. No NEW axioms appear (V16's axiom names are a subset of V15's). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); axs={a["name"]:a for a in r["axioms_used"]}; o = axs.get("Braverman.PaperV0.h_joint_phi_phip_invD2_oracle"); assert o is not None, axs.keys(); assert o.get("declared")=="1/5000", o; assert o.get("oracle_bound")=="1/5000", o; assert o.get("status")=="pass", o'`.

(All three are mechanically checkable via `bash` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Add any new free-floating analytic axiom OR any new oracle-shaped axiom OR any new `[[oracles]]` entry. This sprint is purely a parameter tightening of an *existing* oracle; the axiom name `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` and its statement are unchanged (only the literal `joint_phi_phip_invD2_val` referenced inside it changes from `3/10000` to `1/5000`). Adding any other axiom is forbidden.

- Modify any of the OTHER oracles' Python implementations (`Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py, uzz_phi_sq.py, m_bound.py, r_bound.py, _phi_loader.py, _arb_helpers.py, types.py}`) or their default precision/n_per_edge/safety parameters. Touch ONLY `joint_phi_phip_invD2.py`'s `safety_abs` (1e-4 → 1e-7) and `max_denom` (10000 → 1000000) defaults; NOTHING ELSE in that file or any other Python file.

- Modify `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, any of the eight `Proof/Lib/Lemma54_Paper*.lean` files, `lemma.toml`, or any candidate `V<K>.lean` for `K ≤ 15`. The shared infrastructure is byte-identical — V16 just consumes the existing wrapper `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` (added in sprint_020) at the new tighter literal `joint_phi_phip_invD2_val`.

- Use `sorry`, `admit`, `native_decide`, or any non-kernel reducer. The closing arithmetic `(1/5000) + (1/2)·(153/1000000) ≤ 1/3500` is pure rational; `norm_num` should close it. If `norm_num` fails (very unlikely with 3.3% margin), fallback to `nlinarith` with no hints.

- Set `Cr_val` to a value `≥ 1/2600` (no improvement) or `< 1/3580` (over-aggressive — 1/3580 has only 1% margin, risks `norm_num` brittleness; 1/3590 cuts to 0.74%; below that the Generator should raise the floor not lower it). Realistic targets: `D ∈ {3500, 3550, 3580}`. Pick `1/3500` for safety; only push to `1/3550` or `1/3580` if `norm_num` closes immediately. Do NOT iterate past `1/3580`.

- Re-run the actual arb scan (would take ~30s, but is unnecessary because the cache key for `compute_joint_phi_phip_invD2_bound` excludes safety/max_denom; the existing cache hit is sufficient and the rationalization is a pure post-processing step). The Generator MAY invoke the oracle once to verify the new return value is `1/5000` before encoding it in V16, but the cache should make this near-instant.

- File a proposal in `Proposals/`. This sprint is a parameter tightening of an existing self-serve oracle; no human-approval-gated trust expansion is needed.

- Create new files OUTSIDE the named locations. Only `Candidates/V16.lean` is a new file; everything else is an in-place edit to `Numerical_Library/joint_phi_phip_invD2.py`. NO docs, NO READMEs, NO test files. Scratch helpers under `Scratch/sprint_021_*` are auto-allowed if needed for debugging but not required.

## Time budget

≤ 30 minutes runtime. Breakdown: ~5 min for the `joint_phi_phip_invD2.py` parameter change and docstring update, ~5 min for the cache-hit oracle invocation to verify the new return value, ~10 min for the V16 candidate file (mostly a copy of V15 with three literal updates and the closing `norm_num` re-run), ~10 min buffer for `norm_num` debugging or fallback to `nlinarith`. Soft cap 75% of context — should be well under that since most of the candidate is byte-identical to V15.

## Stop conditions for the Generator

- All three acceptance criteria met (V16 compiles, evaluator passes, oracle audit shows the new `1/5000` declared/oracle bound) → `STATUS=READY_FOR_EVALUATION`.

- The tightened oracle `compute_joint_phi_phip_invD2_bound` returns a rational ≥ `3/10000` (i.e., NO improvement over V15's ceiling) → `STATUS=BLOCKED`, naming the returned value. Should not happen — the planner verified via `arb_to_rational_ub` directly that the rationalization with `safety_abs=1e-7, max_denom=1000000` returns `1/5000`. If it returns something else, the cause is most likely a stale cache entry (run `rm Numerical_Library/.cache/679a03db08c57d7b.json` and re-invoke).

- The closing `norm_num` step in V16 fails to close `Cr_phi_uzz_direct_joint2 (1/5000) (153/1000000) ≤ 1/3500` → fallback to `nlinarith [Cr_phi_uzz_direct_joint2_nonneg ...]` and try again. If that ALSO fails, lower the target to `Cr_val := 1/3580`, then `1/3550`, then `1/3500`, in that order. If even `1/2700` fails to close, → `STATUS=BLOCKED`, naming the residual goal-state and the failed tactic chain.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. (Should not happen — this is a pure parameter tightening, no axioms involved.)

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope". The sprint should fit comfortably under the 30-minute / 75%-context cap; if it exceeds, the Generator is likely overthinking the `norm_num` proof — fallback to `nlinarith` and ship.
