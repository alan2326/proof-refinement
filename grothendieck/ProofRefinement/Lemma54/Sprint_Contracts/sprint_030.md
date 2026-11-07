# Sprint 030: Wildcard structural pivot — replace V23's joint+uzz triangle product with a merged-numerator inline oracle on `‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³`, capturing destructive interference; mint `compute_merged_uderiv_bound` at `n_per_edge=262144`

**Created**: 2026-04-30 12:30 by Planner
**Parent candidate**: `Candidates/V23.lean`. V24 is byte-identical to V23 (sprint_029 was a research-only sprint with no score change at `Cr_val=1/169000`), so V23 is the latest-content predecessor. Sprint_030 is the mandatory wildcard per the 4-sprint cadence (sprint_026 was the previous wildcard at V18 → V21). The direction (`structural-formula-change: merged-numerator inline oracle`) is fresh — it has not been used in sprints 026 (oracle-ceiling-tightening), 027 (oracle-resolution-tightening), 028 (oracle-resolution-tightening), or 029 (research+proposal-filing). Branching from V23 (rather than from V0 or V18) is intentional: the merged-numerator pivot must consume the existing oracle ceilings' structural skeleton (rectangle constants `delta_val=327/2000`, `B_val=223/200`, `M_phi_val=61/2500`, `M_phi_prime_val=59/2000`, `inv_F_p_z_val=3407/2000`) which V23 already carries; reverting to V18 would force re-deriving these and lose the `1/71900 → 1/169000` ceiling work for no structural benefit.
**Target file**: `Candidates/V25.lean`
**Direction**: `formula-change: merged-numerator inline oracle (collapses V23's `2·joint + uzz_phi_sq` triangle product into a single oracle on the exact analytic quotient `‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³ = ‖u''‖` per the form-A identity, capturing destructive-interference savings the triangle bound discards). Mints a new `compute_merged_uderiv_bound` Python oracle in `Numerical_Library/merged_uderiv.py` and a corresponding `[[oracles]]` entry; introduces `Cr_phi_uzz_merged` in `Lemma54_Paper.lean` and `lemma_5_4_paper_on_domain_phi_uzz_merged` in `Lemma54_Paper_Main.lean`; `V25.lean` consumes the new oracle and routes `lemma_5_4_search` through the merged theorem.`
**Tier**: `ambitious` — substantial new Lean writing (one new theorem in `Lemma54_Paper_Main.lean` mirroring `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` with a single-oracle hypothesis; one new upstream `F_inv_p_second_deriv_bound_phi_uzz_merged` in `Lemma54_Paper_Pderiv*.lean` proving `‖u''‖ ≤ ‖D‖³ · merged · invFp³` directly from the form-A identity without the triangle split; new `Cr_phi_uzz_merged` definition + nonneg lemma in `Lemma54_Paper.lean`); one new arb-certified Python oracle `Numerical_Library/merged_uderiv.py` (modeled on `joint_phi_phip_invD2.py` and `uzz_phi_sq.py`); `lemma.toml` `[[oracles]]` append; new `V25.lean` declaring `merged_uderiv_val`, the new oracle axiom, and rewiring `lemma_5_4_search` through the new theorem. Time budget ≤180 min; the Generator should iterate compile-edit cycles aggressively rather than terminate early.

## Goal (one sentence)

Mint a single inline arb-certified oracle `compute_merged_uderiv_bound(n_per_edge=262144)` returning a rational upper bound on `sup_{p∈[0,1], w∈∂Ω} ‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³` (the *exact* `|u''|` quotient via the form-A identity `D·u'' = −(2Φ'·u' + DD·u'²)` with `u' = −Φ/D`), prove the corresponding `lemma_5_4_paper_on_domain_phi_uzz_merged` analog of V23's `_phi_uzz_direct_joint2` route, and rewire `V25.lean`'s `lemma_5_4_search` through it — dropping `Cr_val` from `1/169000` (V23) to a target `≤ 1/200000` (~1.18× win, conservative; merged ratio at n=131072 is `1.0344` and projects to `≈ 0.86` at n=262144, giving a ~1.4× win on the `(2·joint + uzz_phi_sq)` factor and thus ~1.2-1.4× on `Cr_val`).

## Mathematical insight (required, ≤ 5 sentences)

V23's active chain bounds `‖u''‖` via the *triangle-inequality decomposition* `‖u''‖ = ‖2·Φ·Φ'·D − DD·Φ²‖/‖D‖³ ≤ (2·‖Φ·Φ'/D²‖ + ‖DD·Φ²/D³‖) = 2·joint + uzz_phi_sq`, splitting the merged numerator's two terms `2·Φ·Φ'·D` and `−DD·Φ²` into separate suprema; the triangle bound is *strictly looser* than the merged bound because the two terms have *opposite signs* (the form-A identity gives `D·u'' = −2Φ'·u' − DD·u'·u' = +2·Φ·Φ'/D − DD·Φ²/D²` after substituting `u' = −Φ/D`, so the merged numerator is `2·Φ·Φ'·D − DD·Φ²` — a *difference*, not a sum), and at our `(η, r) = (1/100, 23/25)` the destructive interference is numerically substantial. Sprint_022 first computed this merged sup at `n_per_edge=8192` and found it 1.78× *worse* than the triangle (acb-interval slack on the difference exceeded the destructive-interference savings); sprint_029 re-ran at `n ∈ {16384, 32768, 65536}` and found ratios 1.61 → 1.40 → 1.20 monotonically converging; this sprint's planner-side probe at n=131072 gave ratio `1.0344` (`Scratch/sprint_030_merged_n131072.txt`), with the per-doubling decrement constant at ~0.18-0.21 implying ratio ~0.86 at n=262144. The mathematical content is the *form-A identity* in `Lemma54_Paper_Pderiv_Single.lean:546-557`: `D·u'' + 2Φ'·u' + DD·u'² = 0` with `u' = −Φ/D`, hence `u'' = (−2Φ'·(-Φ/D) − DD·Φ²/D²)/D = (2·Φ·Φ'·D − DD·Φ²)/D³` exactly. The new theorem `lemma_5_4_paper_on_domain_phi_uzz_merged` takes a single oracle hypothesis `‖2·Φ·Φ'·D − DD·Φ²‖ ≤ ‖D‖³ · merged_uderiv` and proves `Cr_phi_uzz_merged merged_uderiv := (1/2) · merged_uderiv` — replacing V23's `Cr_phi_uzz_direct_joint2 joint uzz_phi_sq := joint + (1/2)·uzz_phi_sq = (1/2)·(2·joint + uzz_phi_sq)` with a tighter `(1/2) · ‖merged‖`, structurally collapsing two oracles into one and yielding a real Cr_val win that captures all the destructive-interference savings that triangle splitting discarded.

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_030_planner_merged_n131072.py` ran the merged-numerator probe at `n_per_edge=131072` and got `merged_sup=9.7548·10⁻⁶, naive_sum=9.4307·10⁻⁶, ratio=1.0344` (full output in `Scratch/sprint_030_merged_n131072.txt`); the per-doubling ratio history (n=8192:1.78, n=16384:1.61, n=32768:1.40, n=65536:1.20, n=131072:1.0344) shows constant decrement of ~0.18-0.21 per doubling, projecting ratio ~0.86 at n=262144 — i.e., merged_sup will be ~14% below naive_sum, giving a ~1.16× direct win on `2·joint + uzz_phi_sq` and thus on `Cr_phi_uzz_direct_joint2`. Sprint_029's research summary (`Scratch/sprint_029_research_summary.md`) explicitly named `merged-numerator-revive` as the top sprint_030 candidate (above oracle-resolution-tightening-n131072 which is forbidden by the no-3-in-a-row axis rule, and above wider-analyticity-domain-pending which is gated by proposal_003's pending review). Even in the conservative case where n=262144 gives ratio 0.95 (rather than the projected 0.86), `Cr_val` would still drop from `1/169000` to ~`1/178000`, a meaningful structural improvement that simultaneously simplifies the trust base (one merged oracle instead of two coupled oracles).

## Concrete edits expected

1. **`ProofRefinement/Lemma54/Scratch/sprint_030_planner_verify_n262144.py`** (NEW — Generator-side verification before committing to the structural work):
   - Reuses `Scratch.sprint_022_planner_full_merge.compute_full_merged_uderiv_bound`.
   - Runs at `n_per_edge=262144` (single resolution; ~500s wall time on the planner host).
   - Reports `merged_sup`, `naive_sum`, `ratio = merged_sup / naive_sum`.
   - Decision rule: if `ratio < 1.0`, write `DECISION: viable` and proceed to structural work. If `ratio ≥ 1.0`, write `DECISION: dead` and abort with `STATUS=BLOCKED`, recording the actual ratio for the next planner. (This guards against the extrapolation being wrong; the structural Lean work is wasted if the oracle is looser than the V23 triangle.)
   - Writes `Scratch/sprint_030_verify_n262144.txt` with the numerical conclusion.

2. **`ProofRefinement/Lemma54/Numerical_Library/merged_uderiv.py`** (NEW — single new arb-certified Python oracle):
   - Modeled byte-for-byte on `Numerical_Library/uzz_phi_sq.py` (~250 lines), with the inner per-cell quotient computed as `abs_ub(2·Phi·Phi_prime·D − DD·Phi²) / abs_lb(D)³` using interval-arb arithmetic on the merged complex numerator (so destructive interference is captured per-cell).
   - Default `n_per_edge=262144`, `n_p_subdiv=4`, `prec=200`, `safety_abs=1e-8`, `max_denom=10000000` (matches V23 oracle rationaliser settings).
   - Returns `OracleResult(bound=<rational ≥ ball_value>, ball_value=<float>, n_per_edge=262144, …)`.
   - Cache file under `Numerical_Library/cache/merged_uderiv_*.json` per the existing pattern.
   - Imports follow the same pattern as `uzz_phi_sq.py` (`from ._phi_loader import …`, etc.); also reuses `_eval_H_eta_p_pp_at_acb` from `u_zz.py`.

3. **`ProofRefinement/Lemma54/Numerical_Library/__init__.py`**: append `from .merged_uderiv import compute_merged_uderiv_bound` to the public re-export list (consistent with V12+ inline-oracle pattern; allowlisted by sprint_017+).

4. **`ProofRefinement/Lemma54/lemma.toml`**: append a single new `[[oracles]]` entry with `name = "h_merged_uderiv_oracle"`, `oracle_fn = "compute_merged_uderiv_bound"`, `bound_field = "merged_uderiv_val"`, `kind = "oracle"` (matches the existing `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` entries' shape).

5. **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`** (append, do not modify existing definitions): add a new definition

   ```lean
   def Cr_phi_uzz_merged (merged_uderiv : ℝ) : ℝ :=
     (1 / 2) * merged_uderiv

   theorem Cr_phi_uzz_merged_nonneg {merged_uderiv : ℝ}
       (h_merged_nn : 0 ≤ merged_uderiv) :
       0 ≤ Cr_phi_uzz_merged merged_uderiv := by
     unfold Cr_phi_uzz_merged; positivity
   ```

   placed after the existing `Cr_phi_uzz_direct_joint2` block.

6. **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Pderiv_Single.lean`** (or whichever upstream file currently houses `F_inv_p_second_deriv_bound_phi_uzz_direct_joint2`): add a new theorem `F_inv_p_second_deriv_bound_phi_uzz_merged` proving from the form-A identity `D·u'' + 2Φ'·u' + DD·u'·u' = 0` (currently at `Pderiv_Single.lean:546-557`) and the substitution `u' = −Φ/D` (from the existing `u'_eq_neg_Phi_invD` lemma if present, or derived inline) that for any merged_uderiv ≥ 0 with the oracle hypothesis `∀ q w ∈ E, ‖2·Φ·Φ'·D − DD·Φ²‖ ≤ ‖D‖³ · merged_uderiv` (where `D = deriv (F_p η q) w`, `Φ = H_eta η w − H0 w`, etc.), one has `‖u''‖ ≤ merged_uderiv` pointwise. (No invFp factor — the merged numerator's exact identity bypasses the separate ‖D‖³ bound used in the joint+uzz triangle path. The expected proof is ~80-120 lines: discharge the form-A solve to `D·u'' = −2Φ'·u' − DD·u'·u'`, substitute `u' = -Φ/D`, multiply both sides by `D²` to get `D³·u'' = −(2·Φ·Φ'·D − DD·Φ²)` *up to sign*, take norms, divide by `‖D‖³`, then apply the merged oracle hypothesis directly. The Generator may need to introduce a helper lemma `u_pp_eq_merged_div_D_cubed` separately if the algebra is too long for one theorem body.)

7. **`ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean`** (append after `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2`): add a new theorem

   ```lean
   theorem lemma_5_4_paper_on_domain_phi_uzz_merged
       (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
       (merged_uderiv : ℝ) (h_merged_nn : 0 ≤ merged_uderiv)
       (E : Set ℂ)
       (h_image_domain : ∀ q ∈ Set.Ioo (0:ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ disk r,
           F_inv_paper η r hr0 hr1 q w ∈ E)
       (h_merged_oracle_dom : ∀ q ∈ Set.Ioo (0:ℝ) (pr_paper η r hr0 hr1), ∀ w ∈ E,
           ‖2 * (H_eta η w - H0 w) * (deriv (H_eta η) w - deriv H0 w) * deriv (F_p η q) w
             - iteratedDeriv 2 (F_p η q) w * (H_eta η w - H0 w) ^ 2‖
             ≤ ‖deriv (F_p η q) w‖ ^ 3 * merged_uderiv) :
       ∃ pr_paper, 0 < pr_paper ∧ ∀ p, 0 < p → p < pr_paper → ∀ z ∈ disk r,
         ∃ F_inv : ℂ → ℂ, F_p η p (F_inv z) = z ∧ F_inv z ∈ S ∧
         ‖F_inv z - Complex.sin z - p · ((z - H_eta η (Complex.sin z)) * Complex.cos z)‖
           ≤ Cr_phi_uzz_merged merged_uderiv * p ^ 2
   ```

   proved by mirroring `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2`'s structure (lines 1132-1226) with `h_step5` calling the new `F_inv_p_second_deriv_bound_phi_uzz_merged` (single-oracle hypothesis) instead of the two-oracle joint2 version, and `Cr := Cr_phi_uzz_merged merged_uderiv` (single-arg) instead of the joint2 form.

8. **`ProofRefinement/Lemma54/Candidates/V25.lean`** (NEW — copy `V23.lean` verbatim then patch):
   - Update the header narrative: V25 is the merged-numerator structural pivot, parent `Candidates/V23.lean` (linear-content; V24 was research byte-identical), sprint `Sprint_Contracts/sprint_030.md`.
   - **Keep** all existing oracle definitions and ceilings for `M_val`, `delta_val`, `B_val`, `M_phi_val`, `M_phi_prime_val`, `inv_F_p_z_val`, `u_zz_bound_val`, `joint_phi_phip_invD2_val`, `uzz_phi_sq_val` (the joint and uzz oracles remain available; V25's `lemma_5_4_search` *replaces* their use in the active path with the single merged oracle, but their axioms are kept declared since other downstream consumers might exist — actually if no downstream consumer remains, `axioms_used` will not list them and they become inert, which is fine).
   - **Add** `def merged_uderiv_val : ℝ := <RATIONALISED>/<DENOM>` with the rationalised value from `compute_merged_uderiv_bound(n_per_edge=262144)` (e.g., if oracle returns ball ~0.84·9.43e-6 ≈ 7.93e-6, rationalised at safety_abs=1e-8/max_denom=10⁷ might be `81/10000000` ≈ 8.1e-6 — exact value to be determined by the Generator after running the oracle).
   - **Add** the merged oracle axiom declaration:
     ```lean
     axiom h_merged_uderiv_oracle :
       ∀ p ∈ Set.Ioo (0:ℝ) Braverman.Paper.pr_paper, ∀ w ∈ oracle_domain,
         ‖2 * (H_eta SearchConfig.eta w - H0 w) * (deriv (H_eta SearchConfig.eta) w - deriv H0 w)
             * deriv (F_p SearchConfig.eta p) w
           - iteratedDeriv 2 (F_p SearchConfig.eta p) w * (H_eta SearchConfig.eta w - H0 w) ^ 2‖
           ≤ ‖deriv (F_p SearchConfig.eta p) w‖ ^ 3 * merged_uderiv_val
     ```
     placed alongside the existing `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` declarations.
   - **Replace** `def Cr_val : ℝ := 1 / 169000` with `def Cr_val : ℝ := <NEW_RATIONAL>` where `<NEW_RATIONAL>` dominates `Cr_phi_uzz_merged merged_uderiv_val = (1/2) * merged_uderiv_val` (e.g., `1/200000` if merged ~ 8.1e-6 / 2 ≈ 4.05e-6 < 5e-6 = 1/200000; exact rational determined by the Generator from the verified oracle output, with the strict requirement `Cr_val < 1/169000`).
   - **Rewire** `lemma_5_4_search`'s body: the existing call to `lemma_5_4_paper_on_domain_phi_uzz_direct_joint2` (or its V23 wrapper) is replaced by a call to `lemma_5_4_paper_on_domain_phi_uzz_merged` consuming `h_merged_uderiv_oracle` and `h_oracle_domain_contains_image`. The dominance proof for `Cr_phi_uzz_merged merged_uderiv_val ≤ Cr_val` is a `norm_num` or `decide` on the rational inequality.
   - All other Lean lemmas (oracle positivity proofs, etc.) updated only as needed for the new oracle.

9. **`ProofRefinement/Lemma54/Bulletin.md`**: the Planner appends after the contract is queued (NOT the Generator).

10. **NO edits** to: `Proof/SearchConfig.lean`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, `Proposals/proposal_003_wider_analyticity_domain.md` (it stays pending), any `V<K>.lean` for `K ≤ 24`, `Sprint_Contracts/sprint_<K>.md` for `K < 030`, `_archive/`, anything not on the explicit edit list.

## Acceptance criteria

1. **Verification probe shows merged is viable**: `test -s ProofRefinement/Lemma54/Scratch/sprint_030_verify_n262144.txt && grep -E '^DECISION: viable' ProofRefinement/Lemma54/Scratch/sprint_030_verify_n262144.txt` exits 0. (If `DECISION: dead`, the Generator stops with `STATUS=BLOCKED` per the stop conditions below; the structural Lean work is not wasted because the merged oracle's empirical floor is now documented for the next planner.)

2. **V25 compiles and evaluates with strictly smaller Cr_val**: `lake env lean ProofRefinement/Lemma54/Candidates/V25.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V25.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer * 169000 < score.denom * 1` (i.e., V25's Cr_val is strictly less than V23's `1/169000`). Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and (.score.numer * 169000) < .score.denom'`.

3. **Audit set contains the new merged oracle**: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.axioms_used | map(select(.name == "Braverman.PaperV0.h_merged_uderiv_oracle")) | length == 1'` exits 0, AND that axiom's entry has `kind == "oracle"` and `status == "pass"` (i.e., the runtime arb pipeline re-verifies the merged oracle and `oracle_bound ≤ declared` per the existing G5 logic). The two old oracles `h_joint_phi_phip_invD2_oracle` and `h_uzz_phi_sq_oracle` may either remain (declared but inert if not transitively used) or be removed; the only mechanical requirement is the merged oracle is present and certified.

(All three criteria are mechanically checkable via `bash`/`grep`/`jq`.)

## Out of scope (Generator MUST NOT do)

- **Add any non-oracle-shaped axiom.** The merged oracle is permitted (it has the `∀ q w, ‖<expr>‖ ≤ <bound>` shape and is registered in `lemma.toml`); any *other* axiom (including a "wider analyticity" axiom from proposal_003, which is still pending) is forbidden — return `STATUS=BLOCKED_NEEDS_HUMAN` if proof-of-concept reveals the merged oracle alone isn't enough.
- **Modify** `Proof/SearchConfig.lean` (locked at `eta = 1/100, r = 23/25`).
- **Modify** `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 24`.
- **Modify** existing `Numerical_Library/joint_phi_phip_invD2.py` or `Numerical_Library/uzz_phi_sq.py` (their resolution defaults stay at `n_per_edge=65536`; `merged_uderiv.py` is a new file).
- **Modify** `Sprint_Contracts/sprint_<K>.md` for `K < 030` or `Proposals/proposal_*.md`.
- **Use** `sorry`, `admit`, or `native_decide` in `V25.lean` or any of the new shared-infrastructure lemmas. (`native_decide` is allowed in the existing V23 chain only at compile-precomputed rational dominance steps; if used at all in V25, it must mirror an existing V23 pattern verbatim.)
- **Branch** from any candidate other than V23. V24 is byte-identical and equivalent; reverting to V18 or earlier is incorrect.
- **Skip** the n=262144 verification probe (criterion #1). The structural work is conditional on it passing.
- **Lower** the n=262144 oracle resolution to save runtime. The whole point is that destructive interference only beats the triangle bound at this resolution; using `n_per_edge=131072` (where ratio=1.0344) produces a *worse* bound than V23's joint+uzz triangle.
- **File a fourth proposal**. The budget is currently 1/3 pending (proposal_003); proposal_001 approved, proposal_002 superseded. No new proposals from this sprint.

## Time budget

≤ 180 minutes runtime total (ambitious tier). Breakdown:
- ~10 min: read existing `joint_phi_phip_invD2.py`, `uzz_phi_sq.py`, `_iter_rect_boundary` for the new oracle's structure
- ~15 min: write `Numerical_Library/merged_uderiv.py` (mostly cloned from `uzz_phi_sq.py` with the merged numerator computation)
- ~10 min: smoke-test the new oracle at low resolution (`n_per_edge=4096`) and verify output shape matches `OracleResult`
- ~15 min: run the verify probe at n=262144 (~500s wall but most of it is one Python script call; the agent waits)
- ~10 min: append `[[oracles]]` to `lemma.toml`, update `Numerical_Library/__init__.py`
- ~30 min: write `Cr_phi_uzz_merged` + nonneg in `Lemma54_Paper.lean`; write `F_inv_p_second_deriv_bound_phi_uzz_merged` in `Lemma54_Paper_Pderiv_Single.lean` from the form-A identity (~100 lines of Lean proof)
- ~30 min: write `lemma_5_4_paper_on_domain_phi_uzz_merged` in `Lemma54_Paper_Main.lean` (mirroring the existing `_phi_uzz_direct_joint2` proof's ~100 lines)
- ~15 min: write `V25.lean` (clone V23, add `merged_uderiv_val`, axiom declaration, rewire `lemma_5_4_search`, prove `Cr_phi_uzz_merged ≤ Cr_val` dominance)
- ~30 min: compile-edit cycles for any signature mismatches, missing imports, or proof-skeleton drift
- ~15 min: run `Evaluator.py` at the end (oracle scan at n=262144 ~500s but cached after first run; full audit ~10s)
- ~5 min slack

Soft cap 75% of context. **Ambitious tier reminder**: premature termination on hitting a small obstacle is *not* a graceful exit — iterate the compile-edit cycle aggressively. Fall back to `STATUS=BLOCKED` only if a real impasse appears (e.g., the form-A identity doesn't quite give the merged numerator with the expected sign — in which case write `STATUS=BLOCKED` with the algebraic obstruction recorded).

## Stop conditions for the Generator

- All three acceptance criteria met (verification probe `viable`; V25 compiles + evaluates with `Cr_val < 1/169000`; merged oracle in audit set with `status: pass`) → `STATUS=READY_FOR_EVALUATION`.

- Verification probe at n=262144 returns `DECISION: dead` (ratio ≥ 1.0) → record the actual ratio in `Scratch/sprint_030_verify_n262144.txt` and in a one-paragraph note appended to `Scratch/sprint_030_planner_merged_n131072.txt` (so the next planner can read both probes' outputs in one place), revert any partially-written `Numerical_Library/merged_uderiv.py` and Lean changes (the git auto-checkpoint hook makes this a `git checkout HEAD` of the touched files), and → `STATUS=BLOCKED` with the recorded ratio. The Lean structural work is not committed in this case.

- Verification probe `viable` but the new oracle's rationalised `merged_uderiv_val` × `(1/2)` does NOT dominate strictly below `1/169000` (e.g., the slack from rationalisation eats the destructive-interference savings) → record the calculation in a Scratch note and → `STATUS=BLOCKED` ("merged oracle ratio < 1.0 but rationalisation slack consumed the savings; needs tighter `safety_abs` or higher `max_denom`"). Do NOT silently relax the `Cr_val < 1/169000` requirement.

- New shared-infrastructure Lean theorem `lemma_5_4_paper_on_domain_phi_uzz_merged` cannot be proved within the time budget (e.g., the form-A identity's algebraic manipulation is more involved than the planner estimated, or there's a subtle sign error in the merged numerator's derivation) → record the impasse with a goal-state dump in a Scratch note and → `STATUS=BLOCKED`. Do NOT introduce a `sorry` or `admit` to ship a partial proof.

- Acceptance criteria require a non-oracle axiom (e.g., a wider analyticity domain) → `STATUS=BLOCKED_NEEDS_HUMAN` with a one-paragraph reason. Should not happen for this sprint — the merged-numerator approach uses only the existing analyticity axioms and the new merged oracle.

- Soft context cap exceeded (likely on this ambitious sprint if the Lean proofs go deep) → save partial progress to a Scratch note with the current goal state and `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
