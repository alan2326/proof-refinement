# Sprint 019: Mint a new inline arb-certified joint oracle on `‖Phi · Phi' / D²‖` over `[0, pr_paper] × Ω`, replacing the triangle product `M_phi · M_phi_prime · inv_F_p_z²` in term-1 of `Cr_phi_uzz_direct`

**Created**: 2026-04-30 09:10 by Planner
**Parent candidate**: `Candidates/V13.lean` (linear chain — V13 is the latest-PASS, `Cr_val = 1/300 ≈ 0.00333`, sprint_018's literal-tightening verdict). No reason to branch from an earlier candidate: V13's audit set (3 Lean primitives + 9 `F_inv_paper` seeds + `h_oracle_domain_contains_image` + 4 oracles `h_M_phi/h_M_phi_prime/h_inv_F_p_z/h_u_zz`) plus its `Cr_phi_uzz_direct` chain in `Lemma54_Paper.lean` and `Lemma54_Paper_Pderiv_Single.lean` are exactly the foundation V14 needs — V14 *adds* a new fifth oracle (`h_joint_phi_phip_invD2_oracle`) and a new Lean theorem `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` that consumes it; the four existing oracles and the `Cr_phi_uzz_direct` decomposition stay byte-identical to V13.
**Target file**: `ProofRefinement/Lemma54/Candidates/V14.lean` (with shared-infrastructure additions in `Proof/Lib/Lemma54_Paper.lean`, `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`, `Proof/Lib/Lemma54_Paper_Main.lean`, `lemma.toml`, and `Numerical_Library/joint_phi_phip_invD2.py`).
**Direction**: inline-oracle: joint analytic-correlation tightening — replace term-1 of `Cr_phi_uzz_direct` (`M_phi · M_phi_prime · inv_F_p_z²`, currently using three independently-supremized oracles producing the loose product `0.00209`) with a single direct arb-certified oracle on the joint analytic quotient `‖Phi(w) · Phi'(w) / D(p,w)²‖` over `(p, w) ∈ [0, pr_paper] × Ω(δ_val, B_val)`. Term-2 (the `(1/2) · u_zz_bound · M_phi²` chunk, currently 0.000462) stays unchanged — V14 keeps `h_M_phi_oracle` and `h_u_zz_oracle` for term-2, drops only the *first* uses of `h_M_phi_prime_oracle` and `h_inv_F_p_z_oracle` from the term-1 chain. Direction-history check: 014=inline-oracle (`inv_F_p_z`), 015=formula-change (`M_pp` via approved-proposal), 016=formula-change+inline-oracle (`u_zz`), 017=salvage, 018=oracle-ceiling-tightening. None is "joint-analytic-correlation oracle"; this is a genuinely new direction (no-same-axis-3-times-in-a-row trivially satisfied — the prior inline-oracle sprints minted oracles on *single* analytic quantities `1/D` and `DD/D³`, while V14's oracle covers the *joint quotient* `Phi · Phi' / D²` whose binding-corner alignment is provably less degenerate than the product of separate sups).
**Tier**: ambitious — substantial new Lean writing required: a new arb pipeline in `Numerical_Library/joint_phi_phip_invD2.py` (~150 lines mirroring `u_zz.py`), a new `[[oracles]]` entry in `lemma.toml`, a new `def Cr_phi_uzz_direct_joint` and `theorem Cr_phi_uzz_direct_joint_nonneg` in `Lemma54_Paper.lean`, a new `theorem F_inv_p_second_deriv_bound_phi_uzz_direct_joint` in `Lemma54_Paper_Pderiv_Single.lean` (~80 lines, near-copy of `_phi_uzz_direct` with the term-1 lemma chain rewritten), a new `theorem lemma_5_4_paper_on_domain_phi_uzz_direct_joint` in `Lemma54_Paper_Main.lean` (~30 lines), and V14 itself (~310 lines, near-copy of V13 with the new fifth oracle declared and consumed). Estimated 200-400 lines total of new Lean code; expect ~1-3 hours of Generator iteration to land all parts compiling clean. Time budget ≤ 3 hours; soft cap 75% of context.

## Goal (one sentence)

Mint a new inline arb-certified `[[oracles]]` entry `h_joint_phi_phip_invD2_oracle` returning a certified rational upper bound on `sup_{(p, w) ∈ [0, pr_paper] × Ω} ‖Phi(w) · Phi'(w) / D(p,w)²‖`, factor it through new shared-infrastructure theorems `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` and `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`, and consume it in a new candidate `V14.lean` that drops `Cr_val` from V13's `1/300` to a value strictly below `1/350` (≈ 17% reduction or better), realizing the corresponding tightening of term-1 from `0.00209` (V13 triangle product) to whatever the joint oracle returns (estimated `≤ 0.00185`, at least 10% smaller).

## Mathematical insight (required, ≤ 5 sentences)

V13's term-1 decomposition `M_phi · M_phi_prime · inv_F_p_z² = (61/2500) · (59/2000) · (3407/2000)² = 0.0020888` is a *triangle product*: the four oracles `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle` each take their sup *independently* over `(p, w) ∈ [0, pr_paper] × Ω`, but the actual analytic quantity bounded by term-1 is the *joint* `‖Phi(w) · Phi'(w) / D(p,w)²‖` evaluated at a *single* `(p, w)`. The triangle product is sharp only if all three suprema bind at the same `(p, w)`; per `Scratch/sprint_019_planner_uzz_corner_check.py`, at `p = 0` the corner `(re=0.8365, im=1.115)` gives `1/|D| = 1.5560` (vs certified `inv_F_p_z = 1.7035`, a 9% slack at p=0) and `|H_0''| = 0.3700` — so the certified `inv_F_p_z = 1.7035` binds at some `p > 0` where `|D|` dips, while term-1's `Phi · Phi' / D²` tracks a *different* `(p, w)`-dependent expression whose joint sup is bounded by interval arb on each cell of a `(w-cell, p-interval)` partition of `∂Ω × [0, pr_paper]`. By the same token, `M_phi = 0.0244` and `M_phi_prime = 0.0295` bind at the *top* corners (where η-perturbation is largest) but `Phi(w) · Phi'(w)` may evaluate to a value whose magnitude is smaller than the product `0.0244 × 0.0295 = 7.20·10⁻⁴` because `Phi(w)` and `Phi'(w)` are correlated complex-valued and may have phase opposition. Replacing the term-1 triangle with a single-cell arb scan of the joint quotient is *exactly* the step that turned `M_pp · inv_F_p_z³ ≈ 449` (V11's product) into the `u_zz_bound = 1.5519` direct bound (V12's joint oracle, 290× win); the same technique applied to term-1 should yield a similar (10-30%) tightening. See [`Scratch/sprint_019_planner_joint_phi_phip_invD2.py`](../Scratch/sprint_019_planner_joint_phi_phip_invD2.py) and [`Scratch/sprint_019_planner_uzz_corner_check.py`](../Scratch/sprint_019_planner_uzz_corner_check.py) for the full corner alignment analysis and per-corner u_zz/inv_D evidence.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_019_planner_uzz_corner_check.py` confirms (`mpmath` at `prec=200`): at the binding corner `(re=0.8365, im=1.115)` with `p=0`, `1/|D| = 1.5560` and `|DD| = 0.3700`, so the *non-η* joint analytic quotient `|H_0''(corner) · 1/H_0'(corner)³| = 1.394` lies meaningfully below the V13 certified `u_zz_bound = 1.5519` (8% slack at the binding corner from p>0 contribution) — and analogously the `Phi · Phi' / D²` quotient at p=0 gives `0.0244 · 0.0295 · 1.556² = 0.001745`, a 17% reduction from V13's triangle product `0.00209` even at the worst single corner; over the joint scan the certified arb sup is expected to land in the `0.00170-0.00185` range. With term-1 dropped to `0.00180` (conservative), `Cr_phi_uzz_direct_joint = 0.00180 + 0.000462 = 0.002262`, allowing `Cr_val := 1/425 ≈ 0.002353` (margin `9.1·10⁻⁵`, 4% of RHS) or more comfortably `Cr_val := 1/400 ≈ 0.002500` (margin `2.4·10⁻⁴`, 9.5% of RHS). At the conservative `Cr_val := 1/400` target this is a `1/300 ÷ 1/400 = 4/3 = 1.333×` win over V13; cumulative win over V0 (`Cr_val ≈ 8.196·10¹⁴`) becomes `~3.28·10¹⁷×`. The arb scan cost is comparable to the existing `u_zz` oracle (~30-60s first call, cached thereafter) since it scans the same `∂Ω × [0, p_max]` cells using the same `phi_series` infrastructure.

## Concrete edits expected

- **`ProofRefinement/Lemma54/Numerical_Library/joint_phi_phip_invD2.py`** (NEW FILE, ~150 lines, modeled tightly on `u_zz.py`):
  - Module docstring describing the certified sup `sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖Phi(w) · Phi'(w) / D(p,w)²‖` and the Lean axiom it backs (`h_joint_phi_phip_invD2_oracle`, see V14 below).
  - Reuse the `_eval_H_eta_p_pp_at_acb` helper from `u_zz.py` (or replicate the simpler `_eval_H_eta_and_deriv_at_acb` pattern from `m_phi_prime.py` if only first derivatives are needed). For this oracle we need `H_eta(w)` and `H_eta'(w)` (NOT `H_eta''`), so the import of `_eval_phi_and_deriv_at_acb` (already used by `m_phi_prime.py`) is sufficient.
  - Compute `Phi_iv = H_eta_iv - H_0_iv = H_eta_iv - asin(w_acb)`, `Phi_p_iv = H_eta_p_iv - H_0_p_iv` where `H_0_p_iv = (1 - w²)^{-1/2}`.
  - For each `w_acb` on `_iter_rect_boundary(delta, B, n_per_edge)` and each `p_iv` of `n_p_subdiv` subdivisions of `[0, p_max]`:
    - Compute `D_iv = H_0_p_val + acb(p_iv) * (H_eta_p_val - H_0_p_val)`.
    - Verify `certified_positive(abs_lb(D_iv))`; abort with diagnostic if it fails.
    - Compute `numer_ub = abs_ub(Phi_iv) * abs_ub(Phi_p_iv)` (Phi and Phi' are p-independent — they're η-perturbations of H_0 and H_0', not p-dependent — so the per-cell upper bound on `|Phi · Phi'|` is *constant* in p; only the divisor `|D|^2` varies in p).
    - Compute `denom_lb = abs_lb(D_iv) ** 2`.
    - Per-cell ratio `numer_ub / denom_lb` upper-bounds `|Phi · Phi' / D²|` on the cell.
    - Track `max_g = arb.max(max_g, ratio)`.
  - Return `OracleResult(bound=arb_to_rational_ub(max_g, ...), ...)`.
  - Top-level `compute_joint_phi_phip_invD2_bound(eta=0.01, delta="1635/10000", B="1115/1000", p_max="1", n_per_edge=2048, n_p_subdiv=4, prec=200, K_max=80, max_denom=10000, safety_rel=1e-3, safety_abs=1e-4)` mirroring `compute_u_zz_bound`.
  - Cache key registered via `cached_run` so the second invocation is instant.

- **`ProofRefinement/Lemma54/lemma.toml`** (APPEND a new `[[oracles]]` entry):
  ```toml
  [[oracles]]
  name = "Braverman.PaperV0.h_joint_phi_phip_invD2_oracle"
  short = "h_joint_phi_phip_invD2_oracle"
  bound_field = "joint_phi_phip_invD2_val"
  oracle_fn = "compute_joint_phi_phip_invD2_bound"
  ```
  (The TOML schema for `[[oracles]]` is the same as the four existing entries `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle` — copy one and adjust the four fields.)

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`** (APPEND new `Cr_phi_uzz_direct_joint` def and `_nonneg` lemma after the existing `Cr_phi_uzz_direct` block at line 537):
  ```lean
  /-! ### `Cr_phi_uzz_direct_joint` — η-aware Cr formula taking a joint
      Phi·Phi'/D² bound as a single oracle, plus a direct ‖u_zz‖ bound

  Same shape as `Cr_phi_uzz_direct`, but the term-1 triangle product
  `M_phi · M_phi_prime · inv_F_p_z²` is replaced by a single direct
  bound `joint_phi_phip_invD2` on the analytic quotient
  `‖Phi(w) · Phi'(w) / D(p,w)²‖`. By the joint sup binding at a *single*
  (p, w) rather than separate suprema (each binding at potentially
  different (p, w)), this is fundamentally tighter than the product. -/
  def Cr_phi_uzz_direct_joint
      (r M_phi joint_phi_phip_invD2 u_zz_bound : ℝ) : ℝ :=
    joint_phi_phip_invD2 + (1 / 2) * u_zz_bound * M_phi ^ 2

  theorem Cr_phi_uzz_direct_joint_nonneg
      {r M_phi joint_phi_phip_invD2 u_zz_bound : ℝ}
      (hMphi : 0 ≤ M_phi) (hjoint : 0 ≤ joint_phi_phip_invD2)
      (huzz : 0 ≤ u_zz_bound) :
      0 ≤ Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound := by
    unfold Cr_phi_uzz_direct_joint
    positivity
  ```
  Note the `r` argument is retained for API parity with `Cr_phi_uzz_direct` even though the formula does not consume it; this preserves the wrapper's signature stability across candidate versions.

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`** (APPEND a new theorem `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` AFTER the existing `_phi_uzz_direct` theorem at line 2614, near-copy with the term-1 chain replaced):
  - Same hypotheses as `F_inv_p_second_deriv_bound_phi_uzz_direct` EXCEPT replace
    - `(M_phi_prime : ℝ) (hM_phi_prime_nn : 0 ≤ M_phi_prime)` and
    - `(inv_F_p_z : ℝ) (h_inv_F_p_z_nn : 0 ≤ inv_F_p_z)` and
    - `(h_M_phi_prime_bound : ∀ p ∈ ..., ∀ z ∈ disk r, ‖deriv (H_eta η) ... - deriv H0 ...‖ ≤ M_phi_prime)` and
    - `(h_invD_bound : ∀ p ∈ ..., ∀ z ∈ disk r, 1 ≤ ‖deriv (F_p η p) ...‖ * inv_F_p_z)`
    with the *single* combined hypothesis
    - `(joint_phi_phip_invD2 : ℝ) (h_joint_nn : 0 ≤ joint_phi_phip_invD2)` and
    - `(h_joint_bound : ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r, ‖(H_eta η (F_inv p z) - H0 (F_inv p z)) * (deriv (H_eta η) (F_inv p z) - deriv H0 (F_inv p z))‖ ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 2 * joint_phi_phip_invD2)`.
  - Conclusion: `‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖ ≤ 2 * Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound`.
  - Proof body: copy `_phi_uzz_direct`'s proof verbatim through the part where `term-1` is bounded as `2 * M_phi · M_phi_prime · invFp²`; replace that step with a single application of `h_joint_bound` (which directly bounds `‖Phi · Phi'‖ * invFp²` ≤ `joint_phi_phip_invD2`). The term-2 chain (using `h_M_phi_bound` and `h_u_zz_bound`) is byte-identical.
  - The proof should be ~10-20 lines shorter than `_phi_uzz_direct` because we skip the multiplicative-monotonicity chain on `‖Phi‖ · ‖Phi'‖ · invFp²`.

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean`** (APPEND a new wrapper `lemma_5_4_paper_on_domain_phi_uzz_direct_joint` AFTER the existing `_phi_uzz_direct` wrapper at line 844, near-copy):
  - Same shape as `lemma_5_4_paper_on_domain_phi_uzz_direct`: takes `(η, r, hr0, hr1, M_phi, M_phi_nn, joint_phi_phip_invD2, h_joint_nn, u_zz_bound, h_u_zz_nn, oracle_domain, h_oracle_domain_contains_image, h_M_phi_oracle, h_joint_oracle, h_u_zz_oracle)` (note: NO `M_phi_prime`, NO `inv_F_p_z`).
  - Body: delegate to `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` and chain through Taylor-in-p as in the existing wrapper.

- **`ProofRefinement/Lemma54/Candidates/V14.lean`** (NEW FILE, copy of `V13.lean` with these specific changes):
  - Header: identify V14 as the joint-oracle variant of V13 (mention parent `V13.lean`, sprint `019`, target `Cr_val := 1/400` (or whichever value `norm_num` certifies given the actual oracle return), the new fifth oracle, and the expected ≥ 1.33× win factor).
  - Drop `def M_phi_prime_val` and `def inv_F_p_z_val` (no longer used by the sink) BUT keep `axiom h_M_phi_prime_oracle` and `axiom h_inv_F_p_z_oracle` as carried-over parity declarations (NOT consumed by `lemma_5_4_search`, but kept in the file so the audit set is the *strict superset* of V13's — adding one new oracle without removing any). Actually — re-read the regime: minor-axis tightening within the same oracle infrastructure is fine. **REVISED**: keep `M_phi_prime_val`, `inv_F_p_z_val`, and their corresponding oracles byte-identical to V13. The new oracle is *additive*; the new term-1 bound uses only the new oracle, and the V13 oracles remain declared but unused by the new sink. This way V14's audit set is V13's plus one new entry.
  - Add a new `def joint_phi_phip_invD2_val : ℝ := <CERTIFIED_RATIONAL>` where `<CERTIFIED_RATIONAL>` is the rational upper bound returned by `compute_joint_phi_phip_invD2_bound` at the V14 default precision (estimated 17/10000 ≈ 0.0017 to 19/10000 ≈ 0.0019; the Generator MUST run the oracle once via `uv run python -c 'from ProofRefinement.Lemma54.Numerical_Library.joint_phi_phip_invD2 import compute_joint_phi_phip_invD2_bound; r = compute_joint_phi_phip_invD2_bound(); print(r.bound)'` and use the returned rational).
  - Add `theorem joint_phi_phip_invD2_val_pos` and `_nn` lemmas (both via `unfold; norm_num`).
  - Add the new `axiom h_joint_phi_phip_invD2_oracle` declaration:
    ```lean
    axiom h_joint_phi_phip_invD2_oracle :
        ∀ p ∈ Set.Ioo (0 : ℝ)
            (Braverman.Paper.pr_paper
              Braverman.SearchConfig.eta Braverman.SearchConfig.r
              Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
          ∀ w ∈ oracle_domain,
            ‖(Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
                * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                    - deriv Braverman.H0 w)‖
              ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 2
                  * joint_phi_phip_invD2_val
    ```
  - Replace `lemma_5_4_search`'s body to delegate to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint` (the new wrapper) instead of `_phi_uzz_direct`, threading the new oracle bundle.
  - Update the closing `norm_num` step to prove `Cr_phi_uzz_direct_joint r_val M_phi joint_phi_phip_invD2 u_zz_bound ≤ Cr_val` at the new literal values; the inequality is `joint_phi_phip_invD2_val + (1/2) · u_zz_bound_val · M_phi_val² ≤ Cr_val`, with `u_zz_bound_val = 15519/10000`, `M_phi_val = 61/2500`, `joint_phi_phip_invD2_val = <oracle_returned_rational>`. At target `Cr_val = 1/400`: needs `joint_phi_phip_invD2_val + 0.0004620 ≤ 0.0025` ⟹ `joint_phi_phip_invD2_val ≤ 0.002038`. If oracle returns ≤ 0.002, set `Cr_val := 1/400`. If oracle returns 0.0021, set `Cr_val := 1/350`. Pick the *largest denominator* `D` such that `joint_phi_phip_invD2_val + 0.0004620 + safety_margin ≤ 1/D` and `norm_num` closes. The Generator MUST iterate this empirically.
  - The four V13 oracles `h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle` remain declared with their V13 declared bounds. The new sink uses only `h_M_phi_oracle`, `h_u_zz_oracle`, `h_joint_phi_phip_invD2_oracle`, and `h_oracle_domain_contains_image`; the others are carried for parity (the V14 audit set should equal V13's plus the new joint oracle, with the prime/inv_F_p_z oracles' status unchanged from "declared but not consumed by the sink" — note V13 itself does consume them, V14 does not, so the transitive axiom set may shrink by 2 if these become orphaned; that's fine and improves trust).

- **NO edits** to: `Proof/SearchConfig.lean`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, any candidate file `V<K>.lean` for `K ≤ 13`, `Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py, m_bound.py, r_bound.py}` (all existing oracle implementations stay byte-identical), `Numerical_Library/_phi_loader.py`, `Numerical_Library/_arb_helpers.py`, `Numerical_Library/types.py`, or any of the other `Proof/Lib/Lemma54_Paper_*.lean` files (`Cauchy`, `Identity`, `Pderiv`, `Taylor`).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V14.lean` exits 0 (compiles clean, no `sorry`). All upstream-touched files (`Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, `Lemma54_Paper_Main.lean`) also compile clean — verifiable by `lake build LeanProof` exiting 0.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V14.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer * 300 < score.denom` (i.e., `Cr_val < 1/300`, strictly tighter than V13). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; n,d = r["score"]["numer"], r["score"]["denom"]; assert n*300 < d, (n,d); print("V14 Cr_val =", n, "/", d, "≈", n/d)'`.

3. The audited axiom set for V14 contains a NEW oracle entry `Braverman.PaperV0.h_joint_phi_phip_invD2_oracle` with `kind: "oracle"`, `oracle_fn: "compute_joint_phi_phip_invD2_bound"`, `status: "pass"`, AND every existing oracle from V13 (`h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle`) is either still present with status `"pass"` (carried-for-parity) or absent (orphaned by the new sink — also acceptable). No NEW non-oracle axioms appear (no `kind: "seed"` additions beyond V13's set). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); axs={a["name"]:a for a in r["axioms_used"]}; new_oracle = "Braverman.PaperV0.h_joint_phi_phip_invD2_oracle"; assert new_oracle in axs, axs.keys(); assert axs[new_oracle]["kind"]=="oracle", axs[new_oracle]; assert axs[new_oracle]["oracle_fn"]=="compute_joint_phi_phip_invD2_bound", axs[new_oracle]; assert axs[new_oracle]["status"]=="pass", axs[new_oracle]'`.

(All three are mechanically checkable via `bash` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Add any NEW free-floating analytic axiom (non-oracle). The new `h_joint_phi_phip_invD2_oracle` is an oracle-shaped axiom (universal-quantifier over `(p, w) ∈ Ioo × oracle_domain`, conclusion `‖<analytic_expression>‖ ≤ <bound_field>_val * <D-factor>`) and is allowed under the inline-oracle self-serve rule (Bulletin "Inline oracle creation" item 4). Adding any *other* axiom (free-floating analytic, statement reformulation, weakening of the Lemma 5.4 conclusion) is forbidden.

- Modify any of the existing five oracles' Python implementations (`Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py}`) or their default precision/n_per_edge parameters. The certified outputs from V13 (`M_phi=61/2500`, `M_phi_prime=59/2000`, `inv_F_p_z=3407/2000`, `u_zz=15519/10000`) must remain byte-identical at the V14 oracle calls.

- Modify `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, `Proof/Lib/Lemma54_Paper_{Cauchy,Identity,Pderiv,Taylor}.lean`, or any candidate `V<K>.lean` for `K ≤ 13`. The shared infrastructure is allowed to be EXTENDED (new defs/theorems appended) in `Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, and `Lemma54_Paper_Main.lean`, but the V13-and-prior content of those three files must remain byte-identical (only APPEND new declarations after the existing ones).

- Use `sorry`, `admit`, `native_decide`, or any non-kernel reducer in any of the new theorems or in the V14 closing arithmetic. `norm_num` should close the closing inequality `joint_phi_phip_invD2_val + (1/2) · u_zz_bound_val · M_phi_val² ≤ Cr_val`; if it doesn't, fallback to `nlinarith` with no hints. The new term-1 chain in `_phi_uzz_direct_joint` should follow the same kernel-checked tactics (`linarith`, `mul_le_mul`, `pow_le_pow_left`, `positivity`) as the existing `_phi_uzz_direct`.

- Set `Cr_val` to a value `≥ 1/300` (no improvement) or `< 1/600` (over-aggressive — the certified joint bound at safety margin won't support it). Aim for the *largest denominator* `D` such that `1/D > <oracle_returned_rational> + (1/2) · 15519/10000 · (61/2500)² + 0.0001` and `norm_num` closes. Realistic targets: `D ∈ {350, 380, 400, 425}`.

- File a proposal in `Proposals/`. This sprint is fully self-serve (inline oracle creation + shared-infrastructure additions); no human-approval-gated trust expansion is needed.

- Create new files OUTSIDE the named locations. The five files explicitly named in `Concrete edits expected:` (`joint_phi_phip_invD2.py`, `lemma.toml`, `Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, `Lemma54_Paper_Main.lean`, `V14.lean`) plus `Numerical_Library/__init__.py` (allowlisted for inline-oracle sprints per the sprint_017 salvage policy) are the only files the Generator may write to. NO docs, NO READMEs, NO test files, NO additional Scratch/ files (unless they're scratch helpers genuinely needed during debugging — those are auto-allowed under `Scratch/`).

## Time budget

≤ 3 hours runtime. Breakdown: ~30 min for `joint_phi_phip_invD2.py` (modeled tightly on `u_zz.py`), ~15 min for the `lemma.toml` entry, ~30-60 min for `Cr_phi_uzz_direct_joint` def + `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` theorem (the proof body is a near-copy of `_phi_uzz_direct` minus the term-1 multiplicative chain — should be straightforward but Lean tactic adjustments to bridge "bound on `‖Phi · Phi'‖ * invFp²`" to "joint_phi_phip_invD2 directly" may take debugging), ~30 min for `lemma_5_4_paper_on_domain_phi_uzz_direct_joint` wrapper, ~20 min for V14 candidate, ~20 min for first oracle invocation (cold cache; subsequent runs hit the cache). Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (V14 compiles, evaluator passes, new oracle in audit set with `Cr_val < 1/300`) → `STATUS=READY_FOR_EVALUATION`.

- The new oracle `compute_joint_phi_phip_invD2_bound` returns a rational ≥ `2090/1000000 = 0.00209` (i.e., NO improvement over the V13 triangle product `M_phi · M_phi_prime · inv_F_p_z² = 0.00209`) → `STATUS=BLOCKED`, naming the returned value and including in the `BLOCKED` reason "joint sup did not beat triangle; Phi·Phi'/D² binds at the same corner as the product of separate sups; sprint hypothesis falsified". Do NOT attempt to push `Cr_val` below `1/300` by literal-tightening alone — that's a separate (and questionable) sprint.

- The new theorem `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` does not compile after 60 minutes of Generator iteration on the proof body → `STATUS=BLOCKED`, naming the residual goal-state and the failed tactic chain. Do NOT introduce auxiliary axioms or `sorry` to close gaps; report the blocker.

- The closing `norm_num` step in V14 does not close at any `Cr_val ∈ {1/350, 1/400, 1/425, 1/450, 1/475}` → `STATUS=BLOCKED`, naming the certified joint oracle value, the resulting `Cr_phi_uzz_direct_joint` value, and the `Cr_val` ranges tried.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. (Should not happen — the joint oracle is oracle-shaped and self-serve.)

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope". The sprint should fit comfortably under the 75% cap (~200-400 lines of new Lean across three files plus a 150-line Python file is moderate).
