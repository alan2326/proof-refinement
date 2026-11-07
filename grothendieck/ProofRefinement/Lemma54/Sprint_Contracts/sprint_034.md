# Sprint 034: Re-baseline V28 onto V14's `Cr_phi_uzz_direct_joint` formula via truncation-free `joint_phi_phip_invD2` + `u_zz_bound`; drop `Cr_val` from `1/3` to `2/7` (~16.7% reduction)

**Created**: 2026-05-04 04:30 by Planner
**Parent candidate**: `Candidates/V11.lean` (NOT V27 — V27 is the literal-tightened V11 baseline. V28 must change the *formula*, not just the literal. Branching from V11 gives the cleanest diff: V27 already showed how to retarget the four V11 scalar oracles, but the V14 formula consumes a different constellation (`M_phi`, `joint_phi_phip_invD2`, `u_zz_bound`) and uses a different `Cr_phi_uzz_direct_joint` wrapper from `Lemma54_Paper.lean`. V14 itself is the "natural" parent in the formula sense, but its K_max-era literals (`M_phi=61/2500`, `joint=3/10000`, `u_zz_bound=15519/10000`) are all wrong for the truncation-free pipeline (the truncfree `u_zz_bound` is `~834`, not `~1.55` — see `Scratch/sprint_034_planner_v14_baseline.txt`), so even V14 needs a near-total literal swap. Branching from V11 makes the formula change explicit; the diff to V11 is "swap `Cr_phi_uzz` for `Cr_phi_uzz_direct_joint`, swap the four-scalar oracle pack for the three-oracle pack, retarget all literals to round3 truncfree".)
**Target file**: `Candidates/V28.lean`
**Direction**: `formula-change: re-baseline onto V14's `Cr_phi_uzz_direct_joint` formula with truncation-free oracles` — a structural pivot off V27's `Cr_phi_uzz` formula, not a parameter tweak. Per PATCH_NOTES §3a (line 247), V14's formula has the *smallest* `Cr_patched = 0.2810` of any V0..V26 candidate at round-3 chunks (vs V11's `0.3255`); switching formula is "the only obvious immediate win" the table identifies and is one-shot computable. Direction is *not* "oracle-resolution-tightening" / "oracle-ceiling-tightening" / "salvage" / "truncation-free re-baselining" (V27's direction) — it's a genuine `Cr_phi_*` formula swap. Last 3 sprints: sprint_031 = oracle-resolution-tightening, sprint_032 = (queued, then K_max patch invalidated), sprint_033 = truncation-free re-baselining (literal-only). No same-axis-three-times conflict.
**Tier**: `ambitious` — non-trivial Lean and lemma.toml integration. Requires (a) rewiring two `[[oracles]]` `oracle_fn` entries (`u_zz_bound`, `joint_phi_phip_invD2`) from deprecated K_max-truncated to truncation-free; (b) writing a new candidate that swaps the `lemma_5_4_paper_on_domain_phi_uzz` delegation for `lemma_5_4_paper_on_domain_phi_uzz_direct_joint` (a different theorem with a different oracle hypothesis signature); (c) declaring three oracle axioms instead of four (drop `M_phi_prime`, `inv_F_p_z`, `M_pp`; add `joint_phi_phip_invD2`, `u_zz_bound`); (d) discharging the literal rational dominance `joint + (1/2)*uzz*M_phi^2 ≤ 2/7` where `uzz ≈ 834` makes the polynomial expression numerically wide; (e) verifying the resulting candidate audits correctly under G7 (`Cr_patched(V14) = 0.28103 < 2/7 = 0.2857`). Several compile-edit cycles likely on the dominance step.

## Goal (one sentence)

Produce `Candidates/V28.lean` proving Lemma 5.4 with `Cr_val = 2/7 (≈ 0.2857)` by switching from V27's `Cr_phi_uzz` formula to V14's `Cr_phi_uzz_direct_joint` formula and consuming the truncation-free `round3` rationalised values for `M_phi = 231143/10000000`, `joint_phi_phip_invD2 = 609061/10000000`, `u_zz_bound = 8342848479/10000000`, with the PATCH_NOTES R5 audit-block header naming `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` and recording `Cr_patched(V28) = 0.28103` (V14 row) — a ~16.7% reduction over V27's `Cr_val = 1/3` and the first post-patch sprint that actually moves the audit floor (by changing the structural formula, not just the literal).

## Mathematical insight (required, ≤ 5 sentences)

The post-K_max-patch audit table (PATCH_NOTES §3) ranks every candidate's `Cr_phi_*` formula by its rigorously-evaluated patched value `Cr_patched`. V11/V27's `Cr_phi_uzz = M_phi · M_phi_prime · invFp² + (1/2) · M_pp · invFp³ · M_phi²` (a pure-scalar product of four worst-case oracles) gives `Cr_patched = 0.3255`; V14's `Cr_phi_uzz_direct_joint = joint_phi_phip_invD2 + (1/2) · u_zz_bound · M_phi²` (which replaces `M_phi · M_phi_prime · invFp²` with the joint sup `‖Phi · Phi' / D²‖`) gives `Cr_patched = 0.28103` — a structural ~14% tightening because the joint sup binds `Phi`, `Phi'`, `1/D²` at a **single** `(p, w)` rather than at three potentially-different worst-case points. Note this is despite the truncation-free `u_zz_bound ≈ 834` being ~540× larger than the K_max-era `15519/10000 ≈ 1.55` that V14 originally declared — the joint formula still wins because its term-1 (`joint ≈ 0.061`) is much smaller than V27's `M_phi · M_phi_prime · invFp² = 0.106`, and the term-2 `(1/2)·uzz·M_phi² ≈ 0.223` ends up only marginally larger than V27's term-2 (`0.223` exactly because both formulas apply the `(1/2)` factor to a `M_pp·invFp³·M_phi²` or `u_zz_bound·M_phi²` quantity that aux-z identity makes equal at the joint sup; see `Lemma54_Paper.lean` line 596: `‖u''‖ = ‖DD/D³‖ = ‖u_zz‖`). The math content of this sprint is therefore: **(a)** recognise that `Cr_phi_uzz_direct_joint`'s "joint" decomposition exposes destructive interference / co-binding between `Phi` and `Phi'` that the four-scalar product `M_phi · M_phi_prime · invFp²` cannot capture, and **(b)** observe that PATCH_NOTES §3a (line 247) tabulates this as a "free ~17% win without any new analytic input, just by switching formula" — which is exactly the action V28 takes. No new oracle is created; the truncfree `compute_joint_phi_phip_invD2_truncfree_bound` and `compute_u_zz_bound_truncfree_bound` already exist in `Numerical_Library/truncfree/`, only the lemma.toml `oracle_fn` strings need to be rewired (the same R4 pattern sprint_033 used for `M_phi`, `M_phi_prime`, `inv_F_p_z`, `M_pp`).

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/sprint_034_planner_v14_baseline.py` queries `Numerical_Library.truncfree.round3()` at the contract-stipulated rationaliser settings (`safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7`) and reports `M_phi = 231143/10000000 ≈ 0.02311`, `joint_phi_phip_invD2 = 609061/10000000 ≈ 0.06091`, `u_zz_bound = 8342848479/10000000 ≈ 834.28`, evaluates the V14 formula `Cr_phi_uzz_direct_joint = joint + (1/2) * uzz * M_phi^2 = 567546286918441161071/2000000000000000000000 ≈ 0.28377`, and confirms margin against `Cr_val = 2/7 ≈ 0.28571` is `27175991570911872503/14000000000000000000000 ≈ 1.94·10⁻³` (+0.68%) — tight but `norm_num`-tractable since the literals are exact rationals. This dominates the audit floor `Cr_patched(V14) = 0.28103` (read from `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` candidates row `V14`) by margin `2/7 − 0.28103 = 0.00468` (+1.66%), so G7.b passes. The reduction over V27 is `Cr_val(V27)/Cr_val(V28) = (1/3)/(2/7) = 7/6 ≈ 1.167×` (16.7% tighter), and crucially this is the **first post-patch sprint that lowers the audit floor** (V27 only tightened the literal against V11's audit floor of 0.3255; V28 swaps to V14's audit floor of 0.28103) — establishing the formula-swap pattern as the next-tier lever when literal-tightening is exhausted at a given formula.

## Concrete edits expected

1. **`ProofRefinement/Lemma54/Scratch/sprint_034_verify_v14.py`** (NEW — Generator-side verification before structural commit):
   - Import `Numerical_Library.truncfree.round3` and obtain a `TruncFreeBundle`.
   - Call `b.as_oracle_result(name)` for each of `M_phi`, `joint_phi_phip_invD2`, `u_zz_bound` at the contract-stipulated rationaliser settings (`safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7`).
   - Assert via `Fraction.__eq__` that the three returned `bound` Fractions exactly equal the contract values: `M_phi = Fraction(231143, 10000000)`, `joint_phi_phip_invD2 = Fraction(609061, 10000000)`, `u_zz_bound = Fraction(8342848479, 10000000)`.
   - Compute `Cr_phi_uzz_direct_joint = joint + (1/2) * u_zz_bound * M_phi**2` exactly via `fractions.Fraction`, assert `Cr <= Fraction(2, 7)`, and write `DECISION: viable` with the three bounds, the formula value, and the `2/7 − Cr` margin into `Scratch/sprint_034_verify_v14.txt`. If any rationaliser bound differs from the contract value (e.g., due to upstream changes in the round3 cache), write `DECISION: dead` with the actual values and stop.
   - Also load `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` and verify the V14 row has `Cr_patched_float ≈ 0.28103` (within 1e-4) — this is the value that goes into the V28 audit-block header.

2. **`ProofRefinement/Lemma54/lemma.toml`** (rewire two `[[oracles]]` entries to truncation-free):
   - Change the `oracle_fn` field of the entry with `bound_field = "joint_phi_phip_invD2_val"` from `"compute_joint_phi_phip_invD2_bound"` to `"compute_joint_phi_phip_invD2_truncfree_bound"`.
   - Change the `oracle_fn` field of the entry with `bound_field = "u_zz_bound_val"` from `"compute_u_zz_bound"` to `"compute_u_zz_bound_truncfree_bound"`.
   - Leave the other seven `[[oracles]]` entries UNCHANGED (`M_val` stays on `compute_M_bound_tight`; the four scalar η-aware entries already on truncfree per sprint_033; `uzz_phi_sq_val` and `merged_uderiv_val` stay on the deprecated K_max-era `oracle_fn`s — V28 doesn't consume them, but V0..V26 still need them registered for the grandfathered audit per PATCH_NOTES R4 / G7 SKIP).

3. **`ProofRefinement/Lemma54/Numerical_Library/__init__.py`** (re-export the two truncfree functions if not already):
   - Verify (`grep`) that `compute_u_zz_bound_truncfree_bound` and `compute_joint_phi_phip_invD2_truncfree_bound` are reachable as `Numerical_Library.<name>` (per sprint_033's pattern). If `__init__.py` already does `from .truncfree import *` or explicit re-imports, confirm both names appear; otherwise add them. The Evaluator's `oracle_fn` lookup goes through `Numerical_Library`, so the names must resolve at the top level.

4. **`ProofRefinement/Lemma54/Candidates/V28.lean`** (NEW — copy `V27.lean` as the structural starting point, since V27 is the most recent PASS and shares the `oracle_domain` / `M_val` / V11-axiom-shape boilerplate, then patch heavily):
   - Update header narrative: V28 is the **V14-formula re-baseline**, parent `Candidates/V11.lean` (formula source) but cloned from `V27.lean` (most recent PASS scaffolding), sprint `Sprint_Contracts/sprint_034.md`. Cite `Scratch/sprint_034_verify_v14.txt` for oracle values, `Cache/Backups/2026-05-03_subdivision/audit_naive_results.json` (V14 row) for the audit floor, and PATCH_NOTES §3a for the formula-swap rationale.
   - Insert the **PATCH_NOTES R5 audit-block header** (mandatory per AGENT_BRIEF constraint #8 and PATCH_NOTES R5):
     ```lean
     /-
       AUDIT: Cr_phi_uzz_direct_joint(M_phi, joint_phi_phip_invD2, u_zz_bound)
              ≤ Cr_val under PATCH_NOTES rules.
       Source chunks: Cache/Backups/2026-05-03_subdivision/round3_v26_corner_split_v3.json
       Source audit:  Cache/Backups/2026-05-03_subdivision/audit_naive_results.json
       Cr_patched(this candidate) = 0.28102580431097141
         (= V14 row of audit_naive_results.json; same Cr_phi_uzz_direct_joint formula)
       Cr_val = 2/7 ≈ 0.28571  (margin +1.66% over Cr_patched)
     -/
     ```
   - **Drop** the V27 definitions `M_phi_prime_val`, `inv_F_p_z_val`, `M_pp_val` (and their `_pos`/`_nn` lemmas) — V14 formula doesn't consume them.
   - **Add** new definitions (and `_pos`/`_nn` lemmas):
     ```lean
     def joint_phi_phip_invD2_val : ℝ := 609061 / 10000000
     def u_zz_bound_val : ℝ := 8342848479 / 10000000
     ```
   - **Keep** `M_phi_val := 231143 / 10000000` byte-identical to V27 (same oracle, same value).
   - **Update** `Cr_val`: `1 / 3` → `2 / 7`.
   - **Drop** the V27 axioms `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, `h_M_pp_oracle`; **keep** `h_oracle_domain_contains_image`, `h_M_oracle` (for parity), `h_M_phi_oracle` (consumed by V14 formula).
   - **Add** two new axioms:
     ```lean
     axiom h_joint_phi_phip_invD2_oracle :
         ∀ q ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper
                Braverman.SearchConfig.eta Braverman.SearchConfig.r
                Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
           ∀ w ∈ oracle_domain,
             ‖(Braverman.H_eta Braverman.SearchConfig.eta w - Braverman.H0 w)
                * (deriv (Braverman.H_eta Braverman.SearchConfig.eta) w
                   - deriv Braverman.H0 w)‖
               ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta q) w‖ ^ 2
                 * joint_phi_phip_invD2_val

     axiom h_u_zz_oracle :
         ∀ q ∈ Set.Ioo (0 : ℝ) (Braverman.Paper.pr_paper
                Braverman.SearchConfig.eta Braverman.SearchConfig.r
                Braverman.SearchConfig.r_pos Braverman.SearchConfig.r_lt_one),
           ∀ w ∈ oracle_domain,
             ‖iteratedDeriv 2 (Braverman.F_p Braverman.SearchConfig.eta q) w‖
               ≤ ‖deriv (Braverman.F_p Braverman.SearchConfig.eta q) w‖ ^ 3
                 * u_zz_bound_val
     ```
     (Both signatures match `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`'s `h_joint_oracle_dom` and `h_u_zz_oracle_dom` hypotheses verbatim — see `Proof/Lib/Lemma54_Paper_Main.lean:1005-1012`. These are not new free-floating axioms in the proposal sense; they are inline oracle-shaped axioms that V14 also declared, registered in the existing `lemma.toml` `[[oracles]]` table — sprint_034's edit (2) just rewires their `oracle_fn` strings to the truncfree variants.)
   - **Replace** the `lemma_5_4_search` proof body. The delegation target changes from `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz` to `Braverman.Paper.lemma_5_4_paper_on_domain_phi_uzz_direct_joint`, and the call's argument list changes from `(M_phi, M_phi_prime, M_phi_nn, M_phi_prime_nn, inv_F_p_z, inv_F_p_z_nn, M_pp, M_pp_nn, oracle_domain, h_image, h_M_phi, h_M_phi_prime, h_inv_F_p_z, h_M_pp)` to `(M_phi, M_phi_nn, joint_phi_phip_invD2, joint_nn, u_zz_bound, u_zz_nn, oracle_domain, h_image, h_M_phi, h_joint, h_u_zz)`. (See `Proof/Lib/Lemma54_Paper_Main.lean:994-1020` for the exact theorem signature.)
   - **Update** the dominance step `h_Cr_le`. The new chain:
     ```lean
     have h_Cr_le :
         Braverman.Paper.Cr_phi_uzz_direct_joint Braverman.SearchConfig.r
             M_phi_val joint_phi_phip_invD2_val u_zz_bound_val
           ≤ Cr_val := by
       unfold Braverman.Paper.Cr_phi_uzz_direct_joint Cr_val
              M_phi_val joint_phi_phip_invD2_val u_zz_bound_val
       -- LHS = joint + (1/2)*uzz*M_phi^2
       --     = 609061/10000000 + (1/2)*(8342848479/10000000)*(231143/10000000)^2
       --     ≈ 0.06091 + 0.22287 ≈ 0.28377
       -- RHS = 2/7 ≈ 0.28571
       -- margin ≈ 0.00194 (+0.68%)
       show 609061 / 10000000
              + 1 / 2 * (8342848479 / 10000000)
                * ((231143 : ℝ) / 10000000) ^ 2 ≤ 2 / 7
       norm_num
     ```
   - All other definitions (the `R_val_paper_le_twentythree_twentieths` helper, `oracle_domain`, `M_val`/`δ_val`/`B_val`, the `h_M_oracle` and `h_oracle_domain_contains_image` axioms) byte-identical to V27.

5. **`ProofRefinement/Lemma54/Bulletin.md`**: the Planner appends after the contract is queued (NOT the Generator).

6. **NO edits** to: `Proof/SearchConfig.lean`, `LeanProof/`, `ProofGraph/`, `Evaluator.py`, any `Numerical_Library/*.py` *other than* `__init__.py` (and only if a re-export is missing — verify first), any `Proof/Lib/Lemma54_Paper*.lean` (no new theorems — `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`, `Cr_phi_uzz_direct_joint`, and the supporting `F_inv_p_second_deriv_bound_phi_uzz_direct_joint` are reused as-is), `Proposals/proposal_*.md` (proposal_003 stays pending), any `V<K>.lean` for `K ≤ 27`, any `Sprint_Contracts/sprint_<K>.md` for `K < 034`, `_archive/`, `PATCH_NOTES.md`.

## Acceptance criteria

1. **Verification probe shows the three truncfree ceilings match the contract literals AND `Cr_phi_uzz_direct_joint ≤ 2/7`**: `test -s ProofRefinement/Lemma54/Scratch/sprint_034_verify_v14.txt && grep -E '^DECISION: viable' ProofRefinement/Lemma54/Scratch/sprint_034_verify_v14.txt` exits 0. The probe MUST assert exact rational equality (using `Fraction.__eq__`) of all three `bound` values to the contract literals; if `as_oracle_result` returns a different rationalisation (e.g., upstream `arb_to_rational_ub` precision changed), the probe writes `DECISION: dead` and the Generator stops.

2. **V28 compiles and evaluates with `Cr_val = 2/7`**: `lake env lean ProofRefinement/Lemma54/Candidates/V28.lean` exits 0 AND `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V28.lean` exits 0 with `status: ok` AND the resulting log entry has `score.numer == 2` AND `score.denom == 7`. Mechanically: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.status == "ok" and .score.numer == 2 and .score.denom == 7'`.

3. **The three consumed oracles re-certify under truncation-free path AND G7 passes (no AUDIT_FLOOR_VIOLATION)**: `tail -n 1 ProofRefinement/Lemma54/Refinement_Log/log.jsonl | jq -e '.axioms_used | map(select(.kind == "oracle" and (.short | test("M_phi_oracle$|joint_phi_phip_invD2|u_zz")))) | length == 3 and (all(.; .status == "pass"))'` exits 0. AND the Evaluator's G7 must pass (no `TRUNCATION_REGRESSION` or `AUDIT_FLOOR_VIOLATION` in the run output) — the audit-block header in V28 must satisfy `Cr_patched_float = 0.28102580431097141 < Cr_val_float = 0.28571428...`. (The transitive axiom set should NOT contain `h_M_phi_prime_oracle`, `h_inv_F_p_z_oracle`, or `h_M_pp_oracle` — the V14-formula sink doesn't consume them, so they must be dropped from V28.lean per edit (4) above.)

(All three criteria are mechanically checkable via `bash` / `grep` / `jq`.)

## Out of scope (Generator MUST NOT do)

- **Add any new free-floating analytic axiom**. The two new oracle-shaped axioms `h_joint_phi_phip_invD2_oracle` and `h_u_zz_oracle` are not "new" in the proposal sense — they have the standard oracle shape `∀ p w, ‖<expr>‖ ≤ <bound>_val`, are registered in lemma.toml's existing `[[oracles]]` entries (rewired to truncfree per edit (2)), and were already declared in V14.lean. No `axiom` declarations are added to the trust base in the Proposals sense.
- **Modify** `Proof/SearchConfig.lean` (locked at `eta = 1/100, r = 23/25`).
- **Modify** `LeanProof/`, `ProofGraph/`, `Evaluator.py`, or any `V<K>.lean` for `K ≤ 27`.
- **Modify** any `Proof/Lib/Lemma54_Paper*.lean` — V14's proof structure (`lemma_5_4_paper_on_domain_phi_uzz_direct_joint`, `Cr_phi_uzz_direct_joint`, `F_inv_p_second_deriv_bound_phi_uzz_direct_joint`) is reused exactly. The only Lean-side changes are V28.lean.
- **Modify** any `Numerical_Library/*.py` other than `__init__.py` (and only if the truncfree functions aren't already re-exported there, which sprint_033 should have already handled). Do NOT delete or alter the deprecated `m_phi.py`, `m_phi_prime.py`, `u_zz.py`, `joint_phi_phip_invD2.py`, etc. — they stay for V0..V26 backwards-compat per PATCH_NOTES R4.
- **Modify** `Sprint_Contracts/sprint_<K>.md` for `K < 034` or `Proposals/proposal_*.md`. Proposal_003 (wider analyticity domain) is still pending — do NOT consume or reference it; this sprint is independent.
- **Use** `sorry`, `admit`, or `native_decide`. The literal rational dominance check `Cr_phi_uzz_direct_joint ≤ 2/7` must be discharged by `norm_num` (preferred) or a chain of `nlinarith` with explicit `have h_term1 : ... ≤ ...` / `have h_term2 : ... ≤ ...` rewrites if `norm_num` chokes on the polynomial size.
- **Branch** from any candidate other than V11 (for formula source) / V27 (for clone scaffolding). The PATCH_NOTES §3a recommendation explicitly names the V14-formula re-baseline as the "free ~17% win without any new analytic input"; deviating chooses a worse formula.
- **Pick a tighter `Cr_val`** than `2/7`. The Cr_phi_uzz_direct_joint value at the round3 ceilings is `≈ 0.28377`; a tighter literal like `283/1000 = 0.283` fails the dominance step (margin -0.27% per `Scratch/sprint_034_planner_v14_baseline.txt`). `Cr_val = 2/7 ≈ 0.28571` gives +0.68% margin against the formula and +1.66% against the audit floor — a reasonable safety buffer for `norm_num`. Future sprints may push tighter via subdivision rounds (round-4) or alternative-formula choices.
- **Skip** the audit-block header (R5 requirement). The Evaluator's G7 will fail without it.
- **Skip** the verify probe (criterion #1). The Lean-side literals must be byte-faithful to the truncfree round3 rationalised values; the probe is what guarantees that.
- **Switch oracle source** away from `round3`. The `production` cache gives `Cr_patched(V14) = 5.20` — far above `2/7` — so V28 would fail G7. Round3 is the only viable source.
- **File a fourth proposal**. Budget remains 1/3 pending (proposal_003).
- **Re-introduce** `M_phi_prime_val`, `inv_F_p_z_val`, `M_pp_val` definitions or their oracles into V28. The V14-formula sink does not consume them; declaring them would fail acceptance criterion (3)'s axiom-set check (would require length ≥ 5, not 3).

## Time budget

≤ 180 minutes runtime total (ambitious tier). Breakdown:
- ~5 min: run the verify probe (`Numerical_Library.truncfree.round3()` is JSON-load fast, sub-second; the audit JSON load + V14-row extract is also sub-second).
- ~3 min: `lemma.toml` two-line edit + smoke-test that the Evaluator can resolve the new `oracle_fn` names (`compute_joint_phi_phip_invD2_truncfree_bound`, `compute_u_zz_bound_truncfree_bound`).
- ~2 min: `Numerical_Library/__init__.py` re-export verify (likely no edit needed — sprint_033 already wired the pattern).
- ~30 min: clone V27 → V28, drop three axioms + three `_val` defs, add two axioms + two `_val` defs, swap the sink delegation target, swap the `h_Cr_le` formula.
- ~60 min: re-prove the dominance step `joint + (1/2)*uzz*M_phi^2 ≤ 2/7`. The literals are large (`uzz` denominator is 10⁷, `M_phi` denominator 10⁷, with a square in the term, so the polynomial expression is wide). `norm_num` may need staging via intermediate `have h_term1 : 609061 / 10000000 ≤ 7/100 := by norm_num` and `have h_term2 : (1/2) * (8342848479 / 10000000) * (231143/10000000)^2 ≤ 224/1000 := by norm_num` lemmas, then summing `7/100 + 224/1000 = 70/1000 + 224/1000 = 294/1000 < 2/7` — but check `294/1000 = 0.294` vs `2/7 ≈ 0.2857`, FAIL — retry tighter intermediates: `term1 ≤ 61/1000` and `term2 ≤ 223/1000` give `61/1000 + 223/1000 = 284/1000 = 0.284 < 0.2857` ✓. Allow several compile-edit cycles for the `nlinarith` margin.
- ~10 min: smoke-test V28 with `lake env lean` and `Evaluator.py --skip-oracle --no-log`.
- ~15 min: full `Evaluator.py` run (oracle re-certification + G7 audit; round3 cache is JSON-load fast).
- ~55 min slack for compile-edit cycles, especially on the `norm_num` dominance step (the riskiest step due to tight margin and wide literals).

Soft cap 75% of context.

## Stop conditions for the Generator

- All three acceptance criteria met (verify probe `viable`; V28 compiles + evaluates with `Cr_val = 2/7`; three oracles re-certify with `status: pass`; G7 passes with `Cr_patched = 0.28103 < 2/7`) → `STATUS=READY_FOR_EVALUATION`.

- Verify probe at `safety_rel=1e-3, safety_abs=1e-4, max_denom=1e7` returns oracle bounds that DIFFER from the contract literals (e.g., due to upstream changes in `arb_to_rational_ub` or the round3 chunks JSON) → write `DECISION: dead` in the probe output naming the actual values, → `STATUS=BLOCKED`. The next Planner reads the probe output and re-issues the contract with the corrected literals.

- The dominance step `joint + (1/2)*uzz*M_phi^2 ≤ 2/7` cannot be discharged by direct `norm_num` within reasonable compile time (>5 min for one `norm_num` call) → fall back to a staged proof: introduce
  ```lean
  have h_term1 : (609061 / 10000000 : ℝ) ≤ 61/1000 := by norm_num
  have h_term2 : (1/2) * (8342848479 / 10000000) * (231143 / 10000000)^2 ≤ 223/1000 := by norm_num
  -- 61/1000 + 223/1000 = 284/1000 = 71/250 < 2/7 ⇔ 71*7 = 497 < 250*2 = 500 ✓
  ```
  then `linarith` (or `nlinarith`) the sum. If the intermediate `norm_num` calls are too slow, tighten them further (e.g., `term1 ≤ 6091/100000`, `term2 ≤ 22287/100000` — sum `28378/100000 = 14189/50000 < 2/7 ⇔ 14189*7 = 99323 < 50000*2 = 100000` ✓ with margin 677/100000). The Generator should iterate until the margin is reproducible at compile-clean.

- Lemma.toml `oracle_fn` rewiring causes `Numerical_Library` to fail importing the truncfree functions (e.g., circular import or missing re-export in `__init__.py`) → first attempt to fix by adding the explicit re-export in `__init__.py`; if that fails, → `STATUS=BLOCKED` with the import error recorded; the next Planner repairs the import path.

- The new axioms `h_joint_phi_phip_invD2_oracle` and `h_u_zz_oracle` have signature mismatches with `lemma_5_4_paper_on_domain_phi_uzz_direct_joint`'s hypotheses (e.g., the oracle returns a `≤` in the form expected by the theorem, but the candidate's axiom shape uses `disk r` instead of `oracle_domain` or has a different binder structure) → check `Proof/Lib/Lemma54_Paper_Main.lean:1005-1012` for the exact hypothesis shape and align the V28 axiom signatures. Reference V14.lean for the axiom-shape pattern that worked at the K_max-era. If the alignment cannot be made compatible without modifying `Lemma54_Paper_Main.lean` (which is out of scope), → `STATUS=BLOCKED`.

- Acceptance criteria require a non-oracle axiom or a wider analyticity domain (proposal_003 pending) → `STATUS=BLOCKED_NEEDS_HUMAN`. Should not happen — this sprint is purely a formula-swap on existing infrastructure that V14 already validated structurally at the K_max-era.

- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
