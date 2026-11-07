# Sprint 020: Mint a new inline arb-certified joint oracle on `‖DD · Phi² / D³‖` over `[0, pr_paper] × Ω`, replacing the term-2 triangle product `u_zz_bound · M_phi²` in `Cr_phi_uzz_direct_joint`

**Created**: 2026-04-30 09:30 by Planner
**Parent candidate**: `Candidates/V14.lean` (linear chain — V14 is the latest-PASS, `Cr_val = 1/1300 ≈ 7.692·10⁻⁴`, sprint_019's term-1 joint-oracle verdict). No reason to branch from an earlier candidate: V14's audit set (3 Lean primitives + 9 `F_inv_paper` seeds + `h_oracle_domain_contains_image` + 5 oracles `h_M_oracle/h_M_phi/h_M_phi_prime/h_inv_F_p_z/h_u_zz/h_joint_phi_phip_invD2`, with `h_M_phi_prime/h_inv_F_p_z/h_M_oracle` orphaned) is the right foundation. V15 *adds* a new sixth oracle (`h_uzz_phi_sq_oracle`) for term-2 of `Cr_phi_uzz_direct_joint`, mirroring sprint_019's term-1 mechanism.
**Target file**: `ProofRefinement/Lemma54/Candidates/V15.lean` (with shared-infrastructure additions in `Proof/Lib/Lemma54_Paper.lean`, `Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`, `Proof/Lib/Lemma54_Paper_Main.lean`, `lemma.toml`, and `Numerical_Library/uzz_phi_sq.py`).
**Direction**: inline-oracle: joint analytic-correlation tightening on **term-2** of `Cr_phi_uzz_direct_joint` (the `(1/2) · u_zz_bound · M_phi²` chunk, currently `4.62·10⁻⁴`) — replace the triangle product `u_zz_bound · M_phi²` with a single direct arb-certified oracle on the joint analytic quotient `‖DD(p,w) · Phi(w)² / D(p,w)³‖` over `(p, w) ∈ [0, pr_paper] × Ω(δ_val, B_val)`. Term-1 (`joint_phi_phip_invD2 = 3/10000`, contributing `6·10⁻⁴` to `2·Cr`) stays unchanged at V14's value. Direction-history check: 014=inline-oracle (`inv_F_p_z`), 015=formula-change (`M_pp`), 016=formula-change+inline-oracle (`u_zz`), 017=salvage, 018=oracle-ceiling-tightening, 019=inline-oracle: joint analytic-correlation (term-1). The same-axis-3-times rule is satisfied: only sprint_019 used "joint-analytic-correlation"; sprint_020 is a *natural successor* applying the proven mechanism to the now-dominant term-2.
**Tier**: ambitious — substantial new Lean writing required: a new arb pipeline `Numerical_Library/uzz_phi_sq.py` (~180 lines, mirroring `joint_phi_phip_invD2.py` but with the H_eta'' evaluation from `u_zz.py`), a new `[[oracles]]` entry in `lemma.toml`, a new `def Cr_phi_uzz_direct_joint2` and `_nonneg` lemma in `Lemma54_Paper.lean`, a new `theorem F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` in `Lemma54_Paper_Pderiv_Single.lean` (~200-250 lines, near-copy of `_phi_uzz_direct_joint` with the term-2 chain rewritten — replaces the V14 lines 3530-3541 `h_step_d`/`h_bound_RM` block with a single application of the new oracle hypothesis), a new `theorem lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` in `Lemma54_Paper_Main.lean` (~70 lines, near-copy of `_phi_uzz_direct_joint`), and V15 itself (~310 lines, near-copy of V14 with the new sixth oracle declared and consumed). Estimated 400-600 lines total of new Lean code; expect ~2-3 hours of Generator iteration. Time budget ≤ 3 hours; soft cap 75% of context.

## Goal (one sentence)

Mint a new inline arb-certified `[[oracles]]` entry `h_uzz_phi_sq_oracle` returning a certified rational upper bound on `sup_{(p, w) ∈ [0, pr_paper] × Ω} ‖DD(p,w) · Phi(w)² / D(p,w)³‖`, factor it through new shared-infrastructure theorems `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` and `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2`, and consume it in a new candidate `V15.lean` that drops `Cr_val` from V14's `1/1300` to `1/2400` or smaller (≥ 1.85× win factor), realizing the 6× term-2 tightening (from `9.24·10⁻⁴` to ≈ `1.55·10⁻⁴`) the planner's smoke test confirmed.

## Mathematical insight (required, ≤ 5 sentences)

V14's term-2 chunk `u_zz_bound · M_phi² = (15519/10000) · (61/2500)² ≈ 9.24·10⁻⁴` is a *triangle product*: the oracles `h_u_zz_oracle` (bounding `‖DD/D³‖`) and `h_M_phi_oracle` (bounding `‖Phi‖`) take their suprema *independently* over `(p, w) ∈ [0, pr_paper] × Ω`, but the actual analytic quantity bounded by term-2 (via the aux-z identity `‖DD‖·‖u'‖² = ‖D‖·‖u_zz‖·‖Φ‖²` followed by `‖u'‖ = ‖Φ‖/‖D‖`) is `‖u_zz‖·‖Phi‖² = ‖DD · Phi² / D³‖` evaluated at a *single* `(p, w)`. Per [`Scratch/sprint_020_planner_term2_joint.py`](../Scratch/sprint_020_planner_term2_joint.py) (executed inline; recipe captured for archival), the certified arb sup of this joint quotient at production parameters (`n_per_edge=2048`, `n_p_subdiv=4`, `prec=200`) is `[0.00015286... +/- 1.4e-24]` — *6.04× smaller* than the triangle product `9.24·10⁻⁴`. The miss is that `‖u_zz‖` binds at the high-`|w|` corners with `p>0` inflation, while `‖Phi‖²` binds at *the same corners but with magnitude `~9·10⁻⁴`* (not the ceiling `M_phi = 0.0244` which represents the rationalized upper bound, not the actual value at the binding point) — so the joint scan of `‖DD · Phi² / D³‖` captures the genuine analytic worst case. This is *exactly* the same "triangle vs joint" pattern that sprint_019 used for term-1 (which won 7×); applying it to term-2 (now the dominant piece of `Cr_phi_uzz_direct_joint`) yields a 6× tightening on a `~9·10⁻⁴` chunk, dropping the total from `7.62·10⁻⁴` to `~3.77·10⁻⁴` — enabling `Cr_val ∈ {1/2400, 1/2500, 1/2639}`.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_020_planner_term2_joint.py` confirms via direct arb scan (using `_iter_rect_boundary` from `grothendieck.proof.certified.certify_invertibility` at `n_per_edge=2048`, `n_p_subdiv=4`, `prec=200`, evaluating `H_eta` via the existing `compute_cr_v2.eval_H_eta_at_acb` and `H_eta''` via `Numerical_Library/u_zz.py`'s `_eval_H_eta_p_pp_at_acb`): the certified sup of `‖DD · Phi² / D³‖` is `[0.00015286 ± 1.4e-24]`, attained near `w ≈ (0.8365, 1.115)` with the largest `p`-subinterval. Setting `uzz_phi_sq_val := 154/1000000 ≈ 1.540·10⁻⁴` (the rational ceiling at `1/1000000` resolution with `0.1%` safety) gives a margin ≈ `0.7%` over the certified arb upper bound. With term-1 unchanged (`2 · joint_phi_phip_invD2 = 6·10⁻⁴`), the new total `2 · Cr_phi_uzz_direct_joint2 = 6·10⁻⁴ + 1.54·10⁻⁴ = 7.54·10⁻⁴`, so `Cr_phi_uzz_direct_joint2 ≈ 3.77·10⁻⁴`. The largest `1/D` ≥ this with `0.5%` margin is `1/2639` (or more conservatively `1/2400`), a `1300/2400 ≈ 1.85×` (resp. `1300/2639 ≈ 2.03×`) win factor over V14; cumulative win over V0 (`Cr_val ≈ 8.196·10¹⁴`) becomes `~2.16·10¹⁸×`.

## Concrete edits expected

- **`ProofRefinement/Lemma54/Numerical_Library/uzz_phi_sq.py`** (NEW FILE, ~180 lines, modeled tightly on `joint_phi_phip_invD2.py` plus `u_zz.py`'s H_eta'' evaluator):
  - Module docstring describing the certified sup `sup_{(p, w) ∈ [0, p_max] × Ω(δ, B)} ‖DD(p, w) · Phi(w)² / D(p, w)³‖` and the Lean axiom it backs (`h_uzz_phi_sq_oracle`).
  - Reuse `_eval_H_eta_p_pp_at_acb` from `u_zz.py` (or import it directly via `from .u_zz import _eval_H_eta_p_pp_at_acb`) — this evaluator already returns `(H_eta'(w), H_eta''(w))` simultaneously, exactly what we need.
  - Reuse `eval_H_eta_at_acb` from `grothendieck.proof.certified.compute_cr_v2` for `H_eta(w)` (matches the pattern used by `joint_phi_phip_invD2.py`).
  - Define `_H0_at_acb`, `_H0_prime_at_acb`, `_H0_pp_at_acb` (the last is `w * (1 - w²)^{-3/2}` via `(acb(1) - w*w).rsqrt() ** 3 * w` or equivalent).
  - For each `w_acb` on `_iter_rect_boundary(delta, B, n_per_edge)`:
    - Compute `Phi_iv = H_eta(w) - H_0(w)` (p-independent).
    - Compute `phi_sq_ub = abs_ub(Phi_iv) ** 2` (p-independent).
    - Compute `H_0'(w)`, `H_eta'(w)`, `H_0''(w)`, `H_eta''(w)`.
    - For each `p_iv` of `n_p_subdiv` subdivisions of `[0, p_max]`:
      - `D_iv = H_0' + p_iv · (H_eta' - H_0')`.
      - `DD_iv = H_0'' + p_iv · (H_eta'' - H_0'')`.
      - Verify `certified_positive(abs_lb(D_iv))`; abort with diagnostic if it fails.
      - `numer_ub = abs_ub(DD_iv) * phi_sq_ub`.
      - `denom_lb = abs_lb(D_iv) ** 3`.
      - Per-cell ratio `numer_ub / denom_lb` upper-bounds `|DD · Phi² / D³|` on the cell.
      - Track `max_g = arb.max(max_g, ratio)`.
  - Return `OracleResult(bound=arb_to_rational_ub(max_g, ...), ...)`.
  - Top-level `compute_uzz_phi_sq_bound(eta=0.01, delta="1635/10000", B="1115/1000", p_max="1", n_per_edge=2048, n_p_subdiv=4, prec=200, K_max=80, max_denom=1000000, safety_rel=1e-3, safety_abs=1e-7)` mirroring `compute_joint_phi_phip_invD2_bound`. Note `max_denom=1000000` (vs `joint_phi_phip_invD2`'s `10000`) — the certified value `1.53·10⁻⁴` is too small for a `10000`-denominator rational ceiling (would round up to `2/10000 = 2·10⁻⁴`, losing 30% slack); a `1000000`-denominator gives `154/1000000` with only `0.7%` slack.
  - Cache key registered via `cached_run`.

- **`ProofRefinement/Lemma54/lemma.toml`** (APPEND a new `[[oracles]]` entry):
  ```toml
  [[oracles]]
  name = "Braverman.PaperV0.h_uzz_phi_sq_oracle"
  short = "h_uzz_phi_sq_oracle"
  bound_field = "uzz_phi_sq_val"
  oracle_fn = "compute_uzz_phi_sq_bound"
  ```
  (Schema identical to the existing five `[[oracles]]` entries.)

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`** (APPEND new `Cr_phi_uzz_direct_joint2` def and `_nonneg` lemma AFTER the existing `Cr_phi_uzz_direct_joint` block at line 546; do NOT modify `Cr_phi_uzz_direct_joint`):
  ```lean
  /-! ### `Cr_phi_uzz_direct_joint2` — η-aware Cr formula taking BOTH a
      joint Phi·Phi'/D² bound (term-1) AND a joint DD·Phi²/D³ bound (term-2)

  Same shape as `Cr_phi_uzz_direct_joint`, but the term-2 triangle
  product `(1/2) · u_zz_bound · M_phi²` is replaced by a single direct
  bound `(1/2) · uzz_phi_sq` on the analytic quotient
  `‖DD · Phi² / D³‖` (which equals `‖u_zz · Phi²‖` via the aux-z
  identity). By the joint sup binding at a single (p, w) rather than
  separate suprema, this is fundamentally tighter than the product. -/
  def Cr_phi_uzz_direct_joint2
      (joint_phi_phip_invD2 uzz_phi_sq : ℝ) : ℝ :=
    joint_phi_phip_invD2 + (1 / 2) * uzz_phi_sq

  theorem Cr_phi_uzz_direct_joint2_nonneg
      {joint_phi_phip_invD2 uzz_phi_sq : ℝ}
      (hjoint : 0 ≤ joint_phi_phip_invD2)
      (huzz_phi_sq : 0 ≤ uzz_phi_sq) :
      0 ≤ Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq := by
    unfold Cr_phi_uzz_direct_joint2
    positivity
  ```
  Note: `Cr_phi_uzz_direct_joint2` no longer takes `r`, `M_phi`, or `u_zz_bound` arguments — it's parameterized by the two joint bounds only. Keep `Cr_phi_uzz_direct_joint` byte-identical (still consumed by V14 and earlier).

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`** (APPEND a new theorem `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` AFTER the existing `_phi_uzz_direct_joint` theorem at line 3552, near-copy with the term-2 chain replaced):
  - Same hypotheses as `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` (lines 3112-3140) EXCEPT:
    - REMOVE `(M_phi : ℝ) (hM_phi_nn : 0 ≤ M_phi)` and `(h_M_phi_bound : ...)`.
    - REMOVE `(u_zz_bound : ℝ) (h_u_zz_nn : 0 ≤ u_zz_bound)` and `(h_u_zz_bound : ...)`.
    - ADD `(uzz_phi_sq : ℝ) (h_uzz_phi_sq_nn : 0 ≤ uzz_phi_sq)`.
    - ADD `(h_uzz_phi_sq_bound : ∀ p ∈ Set.Ioo (0 : ℝ) pr, ∀ z ∈ disk r, ‖iteratedDeriv 2 (F_p η p) (F_inv p z) * (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖ ≤ ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * uzz_phi_sq)`. (Equivalently: `‖DD · Phi²‖ ≤ ‖D‖³ · uzz_phi_sq`, which is `‖DD · Phi² / D³‖ ≤ uzz_phi_sq` after dividing — but the multiplicative form avoids carrying a `‖D‖ > 0` hypothesis through the axiom statement.)
  - Conclusion: `‖iteratedDeriv 2 (fun q : ℝ => F_inv q z) p‖ ≤ 2 * Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq`.
  - Proof body: copy `_phi_uzz_direct_joint`'s proof verbatim through `h_form_AB_joint` (line 3497) — the term-1 chain (using `h_joint_oracle`) is byte-identical. Then REPLACE lines 3530-3541 (the `h_step_d` / `h_bound_RM` block bounding `‖u_zz‖ * ‖Φ‖²`) with the chain:
    ```
    -- Bound term-2 directly via the joint oracle:
    -- ‖DD · Phi² / D³‖ ≤ uzz_phi_sq, equivalently ‖DD · Phi²‖ ≤ ‖D‖³ · uzz_phi_sq.
    -- Rewrite the LHS ‖u_zz‖ · ‖Phi‖² in the form ‖DD · Phi² / D³‖.
    have h_term2_eq_quot : ‖u_zz‖ * ‖Φ‖ ^ 2 = ‖DD * Φ ^ 2‖ / ‖D‖ ^ 3 := by
      rw [h_uzz_eq_quot, norm_mul, norm_pow]
      ring
    have h_term2_le : ‖u_zz‖ * ‖Φ‖ ^ 2 ≤ uzz_phi_sq := by
      rw [h_term2_eq_quot]
      have hD_cube_pos : 0 < ‖D‖ ^ 3 := by positivity
      rw [div_le_iff₀ hD_cube_pos]
      have h_oracle_apply : ‖DD * Φ ^ 2‖ ≤ ‖D‖ ^ 3 * uzz_phi_sq := by
        show ‖iteratedDeriv 2 (F_p η p) (F_inv p z) *
              (H_eta η (F_inv p z) - H0 (F_inv p z)) ^ 2‖ ≤
            ‖deriv (F_p η p) (F_inv p z)‖ ^ 3 * uzz_phi_sq
        exact h_uzz_phi_sq_bound p hp z hz
      linarith [h_oracle_apply]
    have h_bound_RM :
        ‖u''‖ ≤ 2 * joint_phi_phip_invD2 + uzz_phi_sq := by
      linarith [h_bound_divD, h_term1_joint_bound, h_term2_le]
    ```
    (Note: `h_uzz_eq_quot` from line 3269 — reused from the V14 proof body, gives `‖u_zz‖ = ‖DD‖/‖D‖³`. The new chain converts `‖u_zz‖·‖Φ‖²` to `‖DD·Φ²‖/‖D‖³` and applies the oracle.)
  - Update `h_target_eq` to use `Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq` instead of `Cr_phi_uzz_direct_joint r M_phi joint_phi_phip_invD2 u_zz_bound`. The unfold and `ring` close as before.

- **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean`** (APPEND a new wrapper `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` AFTER the existing `_phi_uzz_direct_joint` wrapper at line ~1100, near-copy):
  - Same shape as `lemma_5_4_paper_on_domain_phi_uzz_direct_joint` (line 994), but:
    - REMOVE `M_phi`, `hM_phi_nn`, `h_M_phi_bound_dom`.
    - REMOVE `u_zz_bound`, `h_u_zz_nn`, `h_u_zz_oracle_dom`.
    - ADD `uzz_phi_sq`, `h_uzz_phi_sq_nn`, `h_uzz_phi_sq_oracle_dom : ∀ q ∈ Set.Ioo (0 : ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E, ‖iteratedDeriv 2 (F_p η q) w * (H_eta η w - H0 w) ^ 2‖ ≤ ‖deriv (F_p η q) w‖ ^ 3 * uzz_phi_sq`.
  - Conclusion: same Lemma 5.4 statement but with `Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2 uzz_phi_sq` as the constant.
  - Body: lift `h_uzz_phi_sq_oracle_dom` to `h_uzz_phi_sq_at` via `h_image_domain` exactly like `h_M_phi_at` and `h_u_zz_at`; delegate to `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2`; chain through Taylor-in-p as in the existing wrapper.

- **`ProofRefinement/Lemma54/Candidates/V15.lean`** (NEW FILE, copy of `V14.lean` with these specific changes):
  - Header: identify V15 as the term-2-joint-oracle variant of V14 (mention parent `V14.lean`, sprint `020`, target `Cr_val := 1/2400` (or whichever value `norm_num` certifies given the actual oracle return, in the range `[1/2400, 1/2639]`), the new sixth oracle, and the expected ≥ 1.85× win factor).
  - Keep `M_val`, `delta_val`, `B_val`, `M_phi_val`, `M_phi_prime_val`, `inv_F_p_z_val`, `u_zz_bound_val`, `joint_phi_phip_invD2_val` byte-identical to V14 (V15's audit set is V14's *plus* one new oracle, with `M_phi`, `u_zz`, `M_phi_prime`, `inv_F_p_z`, `M_oracle` all becoming orphaned in the new sink — this is fine, the audit should reflect the strict improvement).
  - Add `def uzz_phi_sq_val : ℝ := <CERTIFIED_RATIONAL>` where `<CERTIFIED_RATIONAL>` is the rational upper bound returned by `compute_uzz_phi_sq_bound` at the V15 default precision. The Generator MUST run the oracle once via `uv run python -c 'from ProofRefinement.Lemma54.Numerical_Library.uzz_phi_sq import compute_uzz_phi_sq_bound; r = compute_uzz_phi_sq_bound(); print(r.bound)'` and use the returned rational. Expected: `154/1000000 ≈ 1.54·10⁻⁴` to `2/10000 = 2·10⁻⁴` depending on `max_denom`.
  - Add `theorem uzz_phi_sq_val_pos` and `_nn` lemmas (both via `unfold; norm_num`).
  - Add the new `axiom h_uzz_phi_sq_oracle` declaration:
    ```lean
    axiom h_uzz_phi_sq_oracle :
        ∀ p ∈ Set.Ioo (0 : ℝ)
            (Braverman.Paper.pr_paper
              Braverman.SearchConfig.eta Braverman.SearchConfig.r
              Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
          ∀ w ∈ oracle_domain,
            ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta p) w
                * (Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w) ^ 2‖
              ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta p) w‖ ^ 3
                  * uzz_phi_sq_val
    ```
  - Replace `lemma_5_4_search`'s body to delegate to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` (the new wrapper) instead of `_phi_uzz_direct_joint`, threading the new oracle bundle (no `M_phi`, no `u_zz_bound`, but include `joint_phi_phip_invD2` and the new `uzz_phi_sq`).
  - Update the closing `norm_num` step to prove `Cr_phi_uzz_direct_joint2 joint_phi_phip_invD2_val uzz_phi_sq_val ≤ Cr_val` at the new literal values; the inequality is `joint_phi_phip_invD2_val + (1/2) · uzz_phi_sq_val ≤ Cr_val`, with `joint_phi_phip_invD2_val = 3/10000` and `uzz_phi_sq_val = 154/1000000` (or whatever the oracle returns). At target `Cr_val = 1/2400`: needs `3/10000 + (1/2)·154/1000000 = 0.0003 + 0.000077 = 3.77·10⁻⁴ ≤ 1/2400 = 4.167·10⁻⁴`, margin ~10%. If oracle returns lower, push `Cr_val` to `1/2500` or `1/2600`. Pick the *largest denominator* `D` such that `(joint + uzz_phi_sq/2) · 1.005 ≤ 1/D` and `norm_num` closes. The Generator MUST iterate this empirically.
  - V14's five oracle declarations (`h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle`) and the V14 `joint_phi_phip_invD2_val`/`h_joint_phi_phip_invD2_oracle` declarations remain byte-identical. The new sink uses only `h_joint_phi_phip_invD2_oracle`, `h_uzz_phi_sq_oracle`, and `h_oracle_domain_contains_image`; the others become orphaned (V15 audit set may shrink relative to V14 by 4 — `h_M_oracle`, `h_M_phi_oracle`, `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_u_zz_oracle`); orphaning is acceptable and improves trust.

- **NO edits** to: `Proof/SearchConfig.lean`, `Evaluator.py`, `LeanProof/`, `ProofGraph/`, any candidate file `V<K>.lean` for `K ≤ 14`, `Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py, m_bound.py, r_bound.py, joint_phi_phip_invD2.py}` (all existing oracle implementations stay byte-identical), `Numerical_Library/_phi_loader.py`, `Numerical_Library/_arb_helpers.py`, `Numerical_Library/types.py`, `Cr_phi`, `Cr_phi_invD`, `Cr_phi_uzz`, `Cr_phi_uzz_direct`, `Cr_phi_uzz_direct_joint` (none of them touched — V15 only ADDS `Cr_phi_uzz_direct_joint2`), or any of the other `Proof/Lib/Lemma54_Paper_*.lean` files (`Cauchy`, `Identity`, `Pderiv`, `Taylor`).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Candidates/V15.lean` exits 0 (compiles clean, no `sorry`). All upstream-touched files (`Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, `Lemma54_Paper_Main.lean`) also compile clean — verifiable by `lake build LeanProof` exiting 0.

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V15.lean` exits 0 with `status: ok`, AND the resulting log entry has `score.numer * 1300 < score.denom` (i.e., `Cr_val < 1/1300`, strictly tighter than V14). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); assert r["status"]=="ok", r; n,d = r["score"]["numer"], r["score"]["denom"]; assert n*1300 < d, (n,d); print("V15 Cr_val =", n, "/", d, "≈", n/d)'`.

3. The audited axiom set for V15 contains a NEW oracle entry `Braverman.PaperV0.h_uzz_phi_sq_oracle` with `kind: "oracle"`, `oracle_fn: "compute_uzz_phi_sq_bound"`, `status: "pass"`. No NEW non-oracle axioms appear (no `kind: "seed"` additions beyond V14's set). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | python -c 'import json,sys; r=json.loads(sys.stdin.read()); axs={a["name"]:a for a in r["axioms_used"]}; new_oracle = "Braverman.PaperV0.h_uzz_phi_sq_oracle"; assert new_oracle in axs, axs.keys(); assert axs[new_oracle]["kind"]=="oracle", axs[new_oracle]; assert axs[new_oracle]["oracle_fn"]=="compute_uzz_phi_sq_bound", axs[new_oracle]; assert axs[new_oracle]["status"]=="pass", axs[new_oracle]'`.

(All three are mechanically checkable via `bash` / `python -c`.)

## Out of scope (Generator MUST NOT do)

- Add any NEW free-floating analytic axiom (non-oracle). The new `h_uzz_phi_sq_oracle` is an oracle-shaped axiom (universal-quantifier over `(p, w) ∈ Ioo × oracle_domain`, conclusion `‖<analytic_expression>‖ ≤ <bound_field>_val * <D-factor>`) and is allowed under the inline-oracle self-serve rule (Bulletin "Inline oracle creation" item 4). Adding any *other* axiom (free-floating analytic, statement reformulation, weakening of the Lemma 5.4 conclusion) is forbidden.

- Modify any of the existing six oracles' Python implementations (`Numerical_Library/{m_phi.py, m_phi_prime.py, m_pp.py, u_zz.py, inv_F_p_z.py, joint_phi_phip_invD2.py}`) or their default precision/n_per_edge parameters. The certified outputs from V14 (`M_phi=61/2500`, `M_phi_prime=59/2000`, `inv_F_p_z=3407/2000`, `u_zz=15519/10000`, `joint_phi_phip_invD2=3/10000`) must remain byte-identical at the V15 oracle calls.

- Modify `Evaluator.py`, `LeanProof/`, `ProofGraph/`, `Proof/SearchConfig.lean`, `Proof/Lib/Lemma54_Paper_{Cauchy,Identity,Pderiv,Taylor}.lean`, or any candidate `V<K>.lean` for `K ≤ 14`. The shared infrastructure may be EXTENDED (new defs/theorems appended) in `Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, and `Lemma54_Paper_Main.lean`, but the V14-and-prior content of those three files must remain byte-identical (only APPEND new declarations after the existing ones; do NOT modify `Cr_phi_uzz_direct_joint`, `F_inv_p_second_deriv_bound_phi_uzz_direct_joint`, `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`).

- Use `sorry`, `admit`, `native_decide`, or any non-kernel reducer in any of the new theorems or in the V15 closing arithmetic. `norm_num` should close the closing inequality `joint_phi_phip_invD2_val + (1/2) · uzz_phi_sq_val ≤ Cr_val`; if it doesn't, fallback to `nlinarith` with no hints. The new term-2 chain in `_phi_uzz_direct_joint2` should follow the same kernel-checked tactics (`linarith`, `mul_le_mul`, `pow_le_pow_left`, `positivity`, `div_le_iff₀`, `field_simp`, `ring`) as the existing `_phi_uzz_direct_joint`.

- Set `Cr_val` to a value `≥ 1/1300` (no improvement) or `< 1/3000` (over-aggressive — the certified joint bound at safety margin won't support it). Aim for the *largest denominator* `D` such that `1/D > joint_phi_phip_invD2_val + (1/2) · uzz_phi_sq_val + 0.0001` and `norm_num` closes. Realistic targets: `D ∈ {2400, 2500, 2600, 2639}`.

- File a proposal in `Proposals/`. This sprint is fully self-serve (inline oracle creation + shared-infrastructure additions); no human-approval-gated trust expansion is needed.

- Create new files OUTSIDE the named locations. The five files explicitly named in `Concrete edits expected:` (`uzz_phi_sq.py`, `lemma.toml`, `Lemma54_Paper.lean`, `Lemma54_Paper_Pderiv_Single.lean`, `Lemma54_Paper_Main.lean`, `V15.lean`) plus `Numerical_Library/__init__.py` (allowlisted for inline-oracle sprints per the sprint_017 salvage policy) are the only files the Generator may write to. NO docs, NO READMEs, NO test files. Scratch helpers under `Scratch/sprint_020_*` are auto-allowed if needed for debugging but not required.

## Time budget

≤ 3 hours runtime. Breakdown: ~30 min for `uzz_phi_sq.py` (modeled tightly on `joint_phi_phip_invD2.py` plus `u_zz.py`'s helper), ~15 min for the `lemma.toml` entry, ~30-60 min for `Cr_phi_uzz_direct_joint2` def + `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` theorem (the proof body is a near-copy of `_phi_uzz_direct_joint` minus the term-2 multiplicative chain plus the new `h_term2_eq_quot` rewrite — should be straightforward but Lean tactic adjustments to bridge `‖u_zz‖·‖Φ‖² = ‖DD·Φ²‖/‖D‖³` may take debugging), ~30 min for `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` wrapper, ~20 min for V15 candidate, ~30 min for first oracle invocation (cold cache; subsequent runs hit the cache; the new oracle has the same cell budget as V14's joint oracle so ~30-60s expected). Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (V15 compiles, evaluator passes, new oracle in audit set with `Cr_val < 1/1300`) → `STATUS=READY_FOR_EVALUATION`.

- The new oracle `compute_uzz_phi_sq_bound` returns a rational ≥ `9·10⁻⁴` (i.e., NO improvement over the V14 triangle product `u_zz_bound · M_phi² ≈ 9.24·10⁻⁴`) → `STATUS=BLOCKED`, naming the returned value and including in the `BLOCKED` reason "joint sup did not beat triangle; sprint hypothesis falsified". The planner's smoke test predicts `1.53·10⁻⁴`; a returned value above `5·10⁻⁴` would indicate the smoke test was wrong (e.g., a numerical bug or a different binding corner under tighter resolution).

- The new theorem `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2` does not compile after 60 minutes of Generator iteration on the proof body → `STATUS=BLOCKED`, naming the residual goal-state and the failed tactic chain. Specifically, if the `‖u_zz‖·‖Φ‖² = ‖DD·Φ²‖/‖D‖³` rewrite via `h_uzz_eq_quot` doesn't compose cleanly with the oracle's multiplicative form, report the exact `linarith`/`field_simp` failure. Do NOT introduce auxiliary axioms or `sorry` to close gaps.

- The closing `norm_num` step in V15 does not close at any `Cr_val ∈ {1/2400, 1/2500, 1/2600, 1/2700}` → `STATUS=BLOCKED`, naming the certified `uzz_phi_sq_val`, the resulting `Cr_phi_uzz_direct_joint2` value, and the `Cr_val` ranges tried.

- Acceptance criteria require a new (non-oracle) axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. (Should not happen — the joint oracle is oracle-shaped and self-serve.)

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope". The sprint should fit comfortably under the 75% cap (~400-600 lines of new Lean across three files plus a 180-line Python file is moderate-to-heavy; the proof body is mostly a copy of an existing 470-line theorem with a localized change).
