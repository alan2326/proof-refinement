# Sprint 010: Promote `F_inv_paper_zero` from axiom to Lean theorem (axiom-prove)

**Created**: 2026-04-30 05:10 by Planner
**Parent candidate**: `Candidates/V7.lean` (V7 is the most recent PASS; this sprint changes the shared `Proof/Lib/Lemma54_Paper.lean` infrastructure rather than the candidate's literals, so the same `Cr_val = 1132310000` will hold; we still produce `Candidates/V8.lean` to expose the audit-count change as a fresh log entry).
**Target file**: `Candidates/V8.lean` (literals identical to V7) plus `Proof/Lib/Lemma54_Paper.lean` (replace `axiom F_inv_paper_zero` with `theorem F_inv_paper_zero` whose proof body uses `Braverman.H0_injective`, `Braverman.H0_sin_eq`, and `F_inv_paper_eq` + `F_inv_paper_mem_S`).
**Direction**: axiom-prove (Bulletin's "Current priority", direction 1: convert one of the 12 trusted analytic axioms into a Lean theorem). The previous 3 sprints (007 sinh-direct-tighten, 008 M-precision-tighten, 009 rectangle-delta-tighten) were all parameter-tweak axes; the 2026-04-30 REGIME SHIFT note in the Bulletin forbids further parameter-tweak sprints and demands a structural/axiom-prove move. Sprint 010 takes the most tractable axiom-prove move: `F_inv_paper_zero` is the unique axiom in the 12-axiom IFT package that follows directly from the *non-axiomatic* infrastructure already present (`Braverman.H0_injective`, `Braverman.H0_sin_eq`) plus two existing axioms (`F_inv_paper_eq`, `F_inv_paper_mem_S`).
**Tier**: ambitious (per Bulletin: "Default `Tier:` is now `ambitious`"; this is a multi-step Lean proof on shared infrastructure with several side-condition lemmas, expected to need ~1.5-2.5 hours of Generator iteration).

## Goal (one sentence)

Replace the `axiom F_inv_paper_zero` in `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean` (lines 243-245) with a `theorem F_inv_paper_zero` of the same statement and signature, whose proof uses `Braverman.H0_injective` (from `LeanProof/Lemma52.lean:159`), `Braverman.H0_sin_eq` (from the same file, exported via `LeanProof/.context/API.md`), the two existing axioms `F_inv_paper_eq` and `F_inv_paper_mem_S`, and the algebraic fact `F_p η 0 = H0` (proved in two lines via `funext w; unfold F_p; simp`); then create `Candidates/V8.lean` (parent V7) byte-identical to V7 except for the header comment, so that the per-candidate audit reports the new axiom set with `F_inv_paper_zero` *no longer* appearing in `axioms_used` (one fewer trusted analytic axiom: 11 instead of 12).

## Mathematical insight (required, ≤ 5 sentences)

`F_inv_paper_zero` (line 244 of `Lemma54_Paper.lean`) asserts `F_inv_paper η r hr0 hr1 0 z = Complex.sin z` for `z ∈ disk r₁`. The paper's docstring at line 243 already gives the math: at `p = 0`, the family is `sin` since `F_p η 0 = H_0 = arcsin`. The Lean derivation is:
1. `F_inv_paper_eq` at `p = 0` gives `F_p η 0 (F_inv_paper 0 z) = z`.
2. `F_p η 0 w = (1 - 0) · H0 w + 0 · H_eta η w = H0 w` (algebraic).
3. So `H0 (F_inv_paper 0 z) = z`. By `Braverman.H0_sin_eq` (which says `H0 (sin z) = z` for `z` with `|z.re| < π/2` and `sin z ∈ S`), and noting `z ∈ disk r₁ ⊆ disk 1 ⊆ {|Re z| < π/2}` plus `sin (disk r₁) ⊆ S` (already established in `LeanProof/Lemma54.lean:56` and re-used in line 1021), we get `H0 (sin z) = z` as well.
4. `F_inv_paper_mem_S` puts `F_inv_paper 0 z ∈ S`. With both `F_inv_paper 0 z` and `sin z` in `S` mapped to the same value `z` by `H0`, `Braverman.H0_injective : InjOn H0 S` (proved as a non-axiomatic theorem in `LeanProof/Lemma52.lean:159`) concludes `F_inv_paper 0 z = sin z`.

The mathematical content is the same as the IFT delivery: the joint right-inverse at `p = 0` IS sin (because `H0` IS arcsin on its domain, and arcsin is the unique right-inverse of sin). What's new is that the Lean version no longer needs to *axiomatize* this branch identification — `Braverman.H0_injective` (from Lemma 5.2) carries the global injectivity information at the candidate side, so the IFT's branch-pinning is redundant for `p = 0`. The other 11 axioms remain (the `p > 0` joint-regularity axioms cannot be eliminated without re-deriving the analytic IFT, which is multi-week work).

## Why (≤ 3 sentences, must include numerical evidence)

`Scratch/planner_010_explore.py` enumerates the four allowed theoretical directions and finds: (a) `Cr_refined` (η²-scaled) would shrink `Cr_val` from `1.132·10⁹` to ≈ `9.2·10⁷` (12.2× reduction) but requires NEW oracles for `M_diff/M_diffp/M_pp`, FORBIDDEN by the harness's "no new axioms" rule; (b) tightening `R_val_paper` from `sinh r₂` to `sinh r₁` would save 4% on `Cr_val` but requires a new analytic axiom for the tighter image bound, FORBIDDEN; (c) Cauchy-on-disk for `‖u_zz‖` is sharp (no improvement available without new contour analysis); (d) **axiom-prove on `F_inv_paper_zero` is uniquely tractable** because the candidate's import chain already provides `Braverman.H0_injective` (Lemma 5.2 result, `InjOn H0 S`, fully proved at `LeanProof/Lemma52.lean:159`) and `Braverman.H0_sin_eq` (proved in same file, listed in `LeanProof/.context/API.md:198`), making the axiom-prove derivable from existing non-axiomatic infrastructure. The win is `Cr_val` *unchanged* at `1132310000` (per Bulletin's "How you'll know you're winning" criterion, axiom-count reduction is a valid victory) but the **trusted analytic axiom count drops from 12 to 11** (specifically, `F_inv_paper_zero` will no longer appear in `axioms_used` because it'll be a `theorem`, not an `axiom`, so its derived axioms are listed instead — verifiably 11 if the proof closes without `sorry`).

## Concrete edits expected

- `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean`: remove the `axiom F_inv_paper_zero` declaration (lines 243-245) and replace it with a `theorem F_inv_paper_zero` of the *exact same signature*:
  ```
  theorem F_inv_paper_zero (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      ∀ z ∈ disk (r1 r), F_inv_paper η r hr0 hr1 0 z = Complex.sin z := by
    intro z hz
    -- (proof body, see "proof skeleton" below)
  ```
  The signature must remain *byte-identical* (same param names, same statement) so that all downstream call sites continue to compile without modification. Place the new `theorem` immediately after `axiom F_inv_paper_eq` (lines 239-241) so the file's logical structure (axioms → first derived theorem) is preserved. Update the docstring at line 243 to reflect that this is now a *derived theorem*: change `"At `p = 0`, the family is `sin` (since `F_p η 0 = H_0 = arcsin`)."` to `"At `p = 0`, the family is `sin` (since `F_p η 0 = H0 = arcsin`). **Proved** from `F_inv_paper_eq` + `Braverman.H0_injective` (Lemma 5.2) + `Braverman.H0_sin_eq` + `F_inv_paper_mem_S`."`. Do *not* add any new `axiom` declaration, anywhere; do not remove the other 11 axioms; do not modify `pr_paper`, `pr_paper_pos`, `pr_paper_le_one`, `F_inv_paper`, `F_inv_paper_eq`, `F_inv_paper_mem_S`, `F_inv_paper_R_bound`, `F_inv_paper_analytic`, `F_inv_paper_contdiff`, `F_inv_paper_at_origin`, `F_inv_paper_first_deriv_zero`, or any other declaration in the file.

  Proof skeleton (the Generator must fill in side-condition lemmas; allow Mathlib search and `lean_multi_attempt` to discover exact names):
  ```
    intro z hz
    -- Step 1: F_p η 0 (F_inv_paper 0 z) = z (from axiom F_inv_paper_eq at p = 0)
    have h0_in_Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (pr_paper η r hr0 hr1) :=
      Set.mem_Ico.mpr ⟨le_refl 0, pr_paper_pos η r hr0 hr1⟩
    have h_eq : F_p η 0 (F_inv_paper η r hr0 hr1 0 z) = z :=
      F_inv_paper_eq η r hr0 hr1 0 h0_in_Ico z hz
    -- Step 2: F_p η 0 = H0 (algebraic, from F_p definition)
    have h_F_p_0 : ∀ w, F_p η 0 w = Braverman.H0 w := by
      intro w; unfold F_p; simp
    rw [h_F_p_0] at h_eq
    -- Now h_eq : H0 (F_inv_paper 0 z) = z
    -- Step 3: |z.re| < π/2 (since |z| < r1 r ≤ 1 < π/2)
    have h_z_norm : ‖z‖ < r1 r := hz   -- mem_disk
    have h_re_bound : |z.re| < Real.pi / 2 := by
      have hr1_le_one : r1 r ≤ 1 := by unfold r1; linarith
      have h_pi : (1 : ℝ) < Real.pi / 2 := by
        have h_pi_gt : Real.pi > 2 := Real.pi_gt_two
        linarith
      have hzre_le_norm : |z.re| ≤ ‖z‖ := Complex.abs_re_le_abs z
      linarith
    -- Step 4: sin z ∈ S (use existing infrastructure; see e.g. Lemma54.lean:56)
    have h_sin_z_S : Complex.sin z ∈ Braverman.S := by
      -- One natural approach: |sin z| ≤ sinh ‖z‖ < sinh 1 < something small,
      -- and the real part of sin z is bounded by ‖sin z‖ < 1, so sin z ∈ S.
      -- Generator should grep for similar patterns in LeanProof/Lemma54.lean.
      sorry  -- Generator: replace with actual proof. Probably already exists as a helper.
    -- Step 5: H0 (sin z) = z (apply Braverman.H0_sin_eq from Lemma52.lean)
    have h_H0_sin : Braverman.H0 (Complex.sin z) = z :=
      Braverman.H0_sin_eq z h_re_bound h_sin_z_S
    -- Step 6: F_inv_paper 0 z ∈ S (axiom F_inv_paper_mem_S)
    have h_F_inv_S : F_inv_paper η r hr0 hr1 0 z ∈ Braverman.S :=
      F_inv_paper_mem_S η r hr0 hr1 0 h0_in_Ico z hz
    -- Step 7: H0_injective concludes (both points in S map to same z)
    exact Braverman.H0_injective h_F_inv_S h_sin_z_S (h_eq.trans h_H0_sin.symm)
  ```

  The `sorry` at Step 4 must be replaced — it's likely a one-liner using existing infrastructure in `LeanProof/Lemma54.lean` (around line 56, `hK_sin_sub_S : Complex.sin '' closedBall 0 r ⊆ S`); the Generator should `lean_local_search` for "sin_mem_S" or equivalents before re-deriving from scratch. If a one-line invocation isn't available, the Generator may construct it from `Complex.abs_re_sin_le` + `mem_S_iff` + algebra — pure Mathlib + `Strip.lean` infrastructure, no axioms needed.

- `ProofRefinement/Lemma54/Candidates/V8.lean`: created as a copy of `Candidates/V7.lean` with these minimal changes:
  1. Header comment block updated: declare `-- @parent Candidates/V7.lean`, `-- @sprint Sprint_Contracts/sprint_010.md`, and explain that V8 is byte-identical to V7 except for the comment, **the only change is in shared infrastructure** (`Proof/Lib/Lemma54_Paper.lean` axiom→theorem promotion). The score `Cr_val = 1132310000` is unchanged from V7; the win is the audited axiom count dropping from 12 trusted analytic + 2 oracle = 14 to 11 trusted analytic + 2 oracle = 13.
  2. **Do not** modify `M_val`, `delta_val`, `B_val`, `Cr_val`, `R_val_paper_le_twentythree_twentieths`, `oracle_domain`, `h_M_oracle`, `h_oracle_domain_contains_image`, the `lemma_5_4_search` proof body, or any literal — V8's literals are identical to V7's. The score remains `1132310000`.
  3. The candidate's audit (when V8 is run through `Evaluator.py`) should show the `axioms_used` list now lacks `Braverman.Paper.F_inv_paper_zero` (since it's now a derived theorem). The 11 remaining trusted analytic axioms must still appear (`F_inv_paper`, `F_inv_paper_R_bound`, `F_inv_paper_analytic`, `F_inv_paper_contdiff`, `F_inv_paper_eq`, `F_inv_paper_first_deriv_zero`, `F_inv_paper_mem_S`, `pr_paper`, `pr_paper_pos`, plus the 3 Lean primitives + `h_M_oracle` + `h_oracle_domain_contains_image`).

- `ProofRefinement/Lemma54/lemma.toml`: the `seed_axioms.allowed` list will likely still contain `"Braverman.Paper.F_inv_paper_zero"` even though it's no longer used (no harm: it's an *allow*-list, not a *require*-list). **Do not edit `lemma.toml`** unless the Evaluator complains; the harness's audit runs on transitively-used axioms only, and a now-unused entry in the allow-list is benign. (If the Generator finds the Evaluator complains about the now-missing axiom, the fix is to leave it in the allow-list; do *not* remove it from `lemma.toml`.)

- `ProofRefinement/Lemma54/Experience.md`: append one paragraph dated `### 2026-04-30 sprint_010` summarising the axiom-prove (no claims about pass/fail).

## Acceptance criteria

1. `lake env lean ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean` exits 0 (the file compiles cleanly with `F_inv_paper_zero` now a `theorem`, no `sorry` survives, no new `axiom` declarations were introduced). Verifiable via `! grep -E '^\s*axiom\s+F_inv_paper_zero' ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean` (i.e., the literal `axiom F_inv_paper_zero` declaration is gone) AND `grep -E '^\s*theorem\s+F_inv_paper_zero' ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper.lean` (i.e., a `theorem F_inv_paper_zero` now exists in the file).

2. `uv run ProofRefinement/Lemma54/Evaluator.py --file ProofRefinement/Lemma54/Candidates/V8.lean` exits 0 with `"status":"ok"` in the appended JSON line; `score.numer/score.denom == 1132310000/1` (i.e., `Cr_val` unchanged from V7); the appended `axioms_used` list contains exactly 13 entries (3 Lean primitives + 9 `F_inv_paper`-family seeds + `pr_paper` + `pr_paper_pos` + `h_M_oracle` + `h_oracle_domain_contains_image`) — note `F_inv_paper_zero` is **NOT** in the list (since it's now a theorem, only its derived axioms appear, which are already in the allowed set).

3. `grep -c "F_inv_paper_zero" ProofRefinement/Lemma54/Refinement_Log/log.jsonl | tail -1` for the V8 entry shows the `axioms_used` array length is **strictly less** than the V7 entry's (13 vs 14). Equivalently: a `jq`-style check on the V8 log entry's `axioms_used` array length (`length == 13`) and the absence of `F_inv_paper_zero` from that array (verifiable as `! jq '.axioms_used[] | select(.name=="Braverman.Paper.F_inv_paper_zero")' <V8-log-entry>`).

## Out of scope (Generator MUST NOT do)

- Add any new `axiom` declaration anywhere (in `Lemma54_Paper.lean`, in `Candidates/V8.lean`, in `lemma.toml`, anywhere). The whole point of the sprint is removing one axiom; introducing one is a hard fail.
- Modify the **statement** of `F_inv_paper_zero` (the new `theorem` must have the same signature `∀ z ∈ disk (r1 r), F_inv_paper η r hr0 hr1 0 z = Complex.sin z`). Weakening the conclusion is forbidden.
- Modify any of the other 11 axioms (`pr_paper`, `pr_paper_pos`, `pr_paper_le_one`, `F_inv_paper`, `F_inv_paper_eq`, `F_inv_paper_mem_S`, `F_inv_paper_R_bound`, `F_inv_paper_analytic`, `F_inv_paper_contdiff`, `F_inv_paper_at_origin`, `F_inv_paper_first_deriv_zero`).
- Modify `Numerical_Library/`, `Evaluator.py`, `LeanProof/` (only *consult* `LeanProof/Lemma52.lean` for `H0_injective`, `H0_sin_eq` declarations; do NOT edit), `ProofGraph/`, or any historical record (`Sprint_Contracts/sprint_001..009.md`, `Refinement_Log/log.jsonl` past entries, `Candidates/V0..V7.lean`).
- Modify the literals `M_val = 428`, `delta_val = 1635/10000`, `B_val = 1115/1000`, or `Cr_val = 1132310000` — V8 is byte-identical to V7 for these. Tightening any of these in the same sprint is a different axis (parameter-tweak, currently forbidden) and is out of scope.
- Modify `Proof/Lib/Lemma54_Paper_Main.lean`, `Lemma54_Paper_Pderiv*.lean`, `Lemma54_Paper_Cauchy.lean`, `Lemma54_Paper_Identity.lean`, or `Lemma54_Paper_Taylor.lean`. The proof of `F_inv_paper_zero` is local to `Lemma54_Paper.lean`; the rest of the chain is unaffected.
- Use `sorry` in the final committed proof. The proof skeleton above contains a placeholder `sorry` at Step 4 (sin z ∈ S); this *must* be replaced with a closed proof before the contract's acceptance criteria are met. If `sin z ∈ S` cannot be proved without new axioms (it should be — it's a pure Mathlib + `LeanProof/Defs/Strip.lean` fact), the Generator should report `STATUS=BLOCKED_NEEDS_HUMAN`.
- Refactor unrelated code, rename declarations, change file structure, or "clean up" surrounding declarations.

## Time budget

≤ 150 minutes runtime; soft cap 75 % of context. Most of the budget is spent on (a) finding the right name for `sin z ∈ S` in existing infrastructure (10-30 min via `lean_local_search` + `Grep`), (b) writing the 7-step proof body in `Lemma54_Paper.lean` and getting it to compile (45-90 min), (c) handling potential namespace issues (`Braverman.H0_injective` vs `H0_injective`, `Complex.abs_re_le_abs`'s exact name, etc.) (15-30 min). The Lean compile + Evaluator audit is ~10-20s. V8's literal substitutions are mechanical and take <5 min.

## Stop conditions for the Generator

- Acceptance criteria met → `STATUS=READY_FOR_EVALUATION`.
- Cannot satisfy criteria without violating "Out of scope" → `STATUS=BLOCKED`, one-paragraph reason. In particular, if `sin z ∈ S` requires a new axiom (it shouldn't — the strip `S = {|Re z| < π/2}` containment of `sin (disk 1)` is pure Mathlib calculus + `mem_S_iff` from `Strip.lean`), report `STATUS=BLOCKED`.
- Acceptance criteria require a new axiom (forbidden) → `STATUS=BLOCKED_NEEDS_HUMAN`. If on detailed inspection some Mathlib lemma needed (e.g., a strict version of `Complex.abs_re_sin_lt`) doesn't exist, the Generator may need to ADD it as a Lean theorem (allowed — it's a Mathlib-style fact, not an axiom) but should NOT introduce an `axiom` to short-circuit.
- Soft context cap exceeded → `STATUS=BLOCKED`, "context cap exceeded; please re-scope".
