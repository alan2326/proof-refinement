# Sprint 098: Hoist `Summability` from `Candidates/V63/` to `Proof/` — completes the V63 derived-theorem trio (after sprints 096 + 097)

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`; sprint 096 hoisted `DiskInnerSeriesBridge.lean` and sprint 097 hoisted `Integrability.lean` with V68's score and `axioms_used` set preserved byte-for-byte both times)
**Target file**: `ProofRefinement/Korenblum/Proof/Summability.lean` (new shared module; ships V64–V68 candidate updates pointing at it; V63's `Candidates/V63/Summability.lean` reduced to a thin re-export shim mirroring sprints 096/097)
**Direction**: section2-proof (structural — score-neutral hoist of the third and largest paper-axiom-free derived-theorem module from per-candidate scope to shared `Proof/` scope, completing the V63 trio established by sprints 096/097 and restoring AGENT_BRIEF compliance for the most-imported per-candidate file in the workspace)

## Goal

Move the paper-axiom-free derived-theorem module
`ProofRefinement.Korenblum.Candidates.V63.Summability`
(currently at `Candidates/V63/Summability.lean`, **498 lines**, **seven
top-level `theorem`s** — `summable_plus_disk_weight`,
`summable_plus_sigma_at_c`, `summable_minus_disk_weight`,
`summable_minus_sigma_at_c`, `summable_minus_kernel_weight`,
`summable_minus_sigma_uniform_on_open`, `six_summability_shapes_from_h2`
— plus **nine helper `lemma`s** — `abs_coeffPlusGap_le_envelope`,
`abs_coeffMinusGap_le_envelope`, `abs_plusSeq_le_envelope`,
`abs_minusSeq_le_envelope`, `summable_h2_envelope`,
`pow_two_n_le_one`, `pow_two_n_plus_two_le_one`, `disk_weight_le_one`,
`weight_le_one`, `weight_nonneg`, no `axiom`s, no `sorry`s) to a
shared location at `Proof/Summability.lean` under the namespace
`ProofRefinement.Korenblum.Proof.Summability`, update the five
direct downstream consumers (V64, V65, V66, V67, V68) to import the
hoisted module, and re-evaluate V68 to confirm the score remains
`c = 71313/200000 = 356565/1000000`. The file's mathematical content
is preserved byte-for-byte modulo namespace and import-line rewrites.

The move uses neither equation `(15)` nor any new oracle. It is a
structural cleanup that completes the V63 derived-theorem trio
(`DiskInnerSeriesBridge` hoisted in sprint 096, `Integrability`
hoisted in sprint 097, `Summability` hoisted now), restoring full
AGENT_BRIEF compliance for the per-candidate-scope rule on the V63
output cone.

## Why

The AGENT_BRIEF (lines 175-195) pins the per-candidate-scope rule:
"the file is imported only by `Candidates/V<N>.lean` (or by other
files under `Candidates/V<N>/`), never by `KorenblumPaper/`,
`Proof/`, or other candidates." `Candidates/V63/Summability.lean`
is currently imported by **five** other candidates beyond V63
itself (V64, V65, V66, V67, V68) — every multi-window c-push from
V64 onward — with **dense usage**: 6–7 invocations of
`six_summability_shapes_from_h2` per consumer (one per τ-window
endpoint plus a `hkit := …` pattern at the witness-construction
site). This is the most-imported per-candidate file in the
workspace — strictly more dense than the two files already hoisted
in sprints 096/097.

Sprint 096's verdict explicitly noted: "The other two V63
derived-theorem files (`Integrability.lean`, `Summability.lean`)
are also widely imported across V64–V68 and would benefit from the
same hoist treatment — queued as candidates for follow-up sprints."
Sprint 097 picked up `Integrability.lean`. Sprint 098 picks up
`Summability.lean`, the third and final V63 file. After this
sprint, `Candidates/V63/` will contain only thin re-export shims
for backward compatibility with V63's own imports; all
mathematical content of the V63 trio will live under `Proof/`.

The seven theorems in `Summability.lean` carry the H²→summability
transfer kit that bridges Wang's Section 2 H² boundary-norm
hypothesis (`hH2_v6×`) to the six concrete `Summable` shapes
required by `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`'s
`h_witness` predicate (`Proof/Reduction.lean:7787-7803`). Every
multi-window c-push from V64 onward consumes
`six_summability_shapes_from_h2` once per τ-window plus once at
the witness step:

  - V64 (j=2 + j=1): 6 explicit invocations + 1 `hkit` (line 262–272 + 300).
  - V65 (j=2 + j=1): 6 invocations + 1 `hkit` (line 235–245 + 277).
  - V66 (j=4..1, four-window):  7 invocations + 1 `hkit` (line 238–248 + 287).
  - V67 (j=7..1, seven-window): 7 invocations + 1 `hkit` (line 246–256 + 296).
  - V68 (j=10..1, eleven-window): 7 invocations + 1 `hkit` (line 249–259 + 302).

Hoisting once now is bounded; deferring as the candidate stream
lengthens compounds the per-candidate-scope rule violation on the
densest call site in the workspace.

The hoist is preferred over the four other candidate sprint shapes
considered:

  (a) **Hoist `Candidates/V66/Branch1Integrability.lean` to
      `Proof/Branch1Integrability.lean`**. Smaller scope (113 lines,
      2 theorems) and only **two** direct consumers (V67, V68). But
      this file is window-architecture-specific (concerns the
      mode-1 "branch one" residual integrand for the V66/V67/V68
      family), and sprint 097's "Out of scope" explicitly demoted
      it for that reason: "These are window-architecture specific
      (one set of endpoints per architecture) and are not reused
      as broadly as the V63 trio." Following sprint 097's
      guidance, Branch1Integrability hoist should wait until a
      future architecture demonstrates the cross-architecture
      demand. **Demoted**: weaker per-candidate-scope case than
      Summability (2 vs. 5 consumers); the V63 trio is the natural
      first-pass hoist set; Branch1 hoist is a follow-up after
      the trio is complete.

  (b) **Wang Lemma 2 / Fourier orthogonality derived theorem in
      `Proof/`**. Long-standing brief target. No current consumer
      — would build infrastructure that nothing immediately uses,
      risking speculative work. Sprints 096 and 097 both
      explicitly demoted this for the same reason; the same
      demotion applies here. **Best queued *after* a sprint that
      establishes the consuming Lean derivation chain** (e.g. a
      structural Slack-2 successor that needs the boundary-L²
      expansion as a load-bearing step). **Demoted**: speculative
      infrastructure absent a consumer.

  (c) **Trust-surface compaction: discharge `hH2_v6×` from
      `Section2Assumptions` as a Lean theorem**. Bulletin §B(4)
      explicitly names this as a score-neutral but structurally
      valuable target. **But** `Candidates/V63/Summability.lean`
      lines 26-38 explicitly document the structural blocker: *"The
      bundled `Section2Assumptions` structure does NOT carry
      coefficient-level summability data … The V64+ c-push will
      need to either carry `(hH2_a, hH2_b)` as candidate-side
      hypotheses (free axiom, expanding the seed envelope by two
      axioms) or file proposal_004 to add H² fields to
      `Section2Assumptions`."* Adding fields to
      `Section2Assumptions` requires editing `KorenblumPaper/`,
      which the AGENT_BRIEF (lines 188-190) explicitly forbids the
      generator from doing. The discharge would have to come via a
      `Numerical_Library` oracle (Wang's H² hypothesis is a
      high-precision computational claim about the canonical
      extremals, not a derivation-from-Mathlib claim). **Demoted**:
      not runnable as a sprint without a prior trust-base expansion
      proposal; per the planner role's proposal-filing checklist,
      the math is not pinned tightly enough yet to justify a
      proposal_004 entry.

  (d) **New analytical attempt at Slack 2 (per-k cross-coupling
      lift) in Lean**. Sprint 077's data at `c = 0.35645` reports
      kernel margin uniformly `≈ −0.86 to −0.99` across all
      α-families and all canonical extremals E1–E5 in the
      contraction regime `|α(k)| < 1`. Pushing to V68's c
      (+1.15e-4 in the c-axis) is mathematically unlikely to
      reverse a uniform −90% margin. Same chain the seed uses
      under a marginally different parameter — **demoted as not
      novel per the planner role's "ultrathink" rule**, mirroring
      sprints 096 and 097.

  (e) **Migrate one oracle wrapper to interval arithmetic
      (Bulletin §C 5)**. Score-neutral credibility advance. But
      requires significant `Numerical_Library/` work plus
      `[[oracles]]` re-registration plus careful pre-verification
      under `mpmath.iv` or `arb` — a larger scope than a one-file
      hoist and not bounded to one generator session. **Demoted**:
      bigger scope; queue after the V63-trio hoist sequence is
      complete (i.e. after this sprint).

The strongest objection to the chosen direction (hoist
Summability) is "is it really worth a generator session for the
*third* pure cleanup in a row?" The answer is yes for three
reasons:

  1. **Densest call site in the workspace.** Summability is
     invoked 6–7 times per consumer across five consumers — at
     least 30 direct call sites total. The per-candidate-scope
     rule violation here is the largest in the workspace.
  2. **Completes the V63 trio.** After this sprint, the entire
     V63 derived-theorem cone moves from per-candidate scope to
     shared `Proof/` scope under a single coherent organization.
     The V63 candidate file itself is unchanged (it imports the
     per-candidate namespaces via re-export shims, exactly as
     sprints 096/097 left things). All five downstream consumers
     are updated to import directly from `Proof/`.
  3. **Template is twice-validated.** Sprints 096 and 097 both
     completed cleanly with V68's score and `axioms_used` set
     preserved byte-for-byte. The third application of an
     identical template is bounded to one generator session even
     at Summability's larger size (498 lines vs. 303 / 129).

After this sprint, **the per-candidate-scope-violation queue is
empty for V63's output cone**, and the next sprint can pivot to
a non-hoist direction (interval-arithmetic oracle migration,
Branch1Integrability hoist if a third consumer ever appears, or
a structural Slack-2/Slack-4 attack with renewed mathematical
preparation).

## Concrete edits expected

- **Create** `ProofRefinement/Korenblum/Proof/Summability.lean`:
  copy the entire content of
  `ProofRefinement/Korenblum/Candidates/V63/Summability.lean`,
  changing only:
  - the namespace declaration from
    `namespace ProofRefinement.Korenblum.Candidates.V63.Summability`
    to
    `namespace ProofRefinement.Korenblum.Proof.Summability`,
  - the file header docstring's location reference (replace
    "Sprint 081, Phase A: per-candidate derived-theorem file …"
    with a header reflecting "Sprint 098: hoisted from
    `Candidates/V63/Summability.lean` for shared reuse across
    V63–V68 and future candidates; completes the V63 derived-theorem
    trio after sprint 096 (`DiskInnerSeriesBridge`) and sprint 097
    (`Integrability`)"),
  - the corresponding closing `end` namespace statement.
  All seven top-level `theorem`s and all nine helper `lemma`s are
  preserved verbatim. No `axiom`s, no `sorry`s, no edits to
  mathematical content. The imports
  (`Mathlib`, `KorenblumPaper.PaperAxioms`,
  `KorenblumPaper.OneModePaperBridge`) are preserved byte-for-byte;
  all are already pinned in `lemma.toml:[workspace_import_policy]`.

- **Update** `ProofRefinement/Korenblum/Candidates/V63/Summability.lean`:
  reduce to a thin re-export shim that imports
  `ProofRefinement.Korenblum.Proof.Summability` and re-exports the
  seven top-level theorems under the original per-candidate
  namespace `ProofRefinement.Korenblum.Candidates.V63.Summability`,
  via trivial `theorem` aliases of the form
  `theorem foo := ProofRefinement.Korenblum.Proof.Summability.foo`.
  This preserves backward compatibility for V63 itself (which
  imports the per-candidate namespace by its original name) so
  V63 does not need to be edited at the candidate level. Mirror
  the shape of sprint 096's
  `Candidates/V63/DiskInnerSeriesBridge.lean` shim and sprint
  097's `Candidates/V63/Integrability.lean` shim. **OR** — if the
  generator finds it cleaner — directly edit V63 to import the
  hoisted module and update its qualified references. Either
  path is acceptable; whichever produces a smaller diff is
  preferred. Document the choice in the candidate header
  comment.

  Note on helper lemmas: the nine helper `lemma`s
  (`abs_coeffPlusGap_le_envelope`, `abs_coeffMinusGap_le_envelope`,
  `abs_plusSeq_le_envelope`, `abs_minusSeq_le_envelope`,
  `summable_h2_envelope`, `pow_two_n_le_one`,
  `pow_two_n_plus_two_le_one`, `disk_weight_le_one`,
  `weight_le_one`, `weight_nonneg`) are referenced only inside
  the file's own theorem-proof bodies (not from outside the file
  by qualified name — verify by `grep -rn
  "Candidates.V63.Summability.abs_coeffPlusGap_le_envelope"
  Candidates/*.lean` for each helper; sprint 097's experience on
  Integrability suggests the helper-set is internal-only). If
  any helper lemma is referenced from outside the file, include
  a corresponding alias in the shim. Aliasing only the seven
  top-level theorems is expected to be sufficient.

- **Update imports** in each of the five direct downstream consumers,
  by replacing the line
    `import ProofRefinement.Korenblum.Candidates.V63.Summability`
  with
    `import ProofRefinement.Korenblum.Proof.Summability`
  and updating any qualified references from
  `ProofRefinement.Korenblum.Candidates.V63.Summability.*`
  to
  `ProofRefinement.Korenblum.Proof.Summability.*`
  in the affected files:
  - `ProofRefinement/Korenblum/Candidates/V64.lean`
    (~7 references to `six_summability_shapes_from_h2`)
  - `ProofRefinement/Korenblum/Candidates/V65.lean`
    (~7 references)
  - `ProofRefinement/Korenblum/Candidates/V66.lean`
    (~8 references)
  - `ProofRefinement/Korenblum/Candidates/V67.lean`
    (~8 references)
  - `ProofRefinement/Korenblum/Candidates/V68.lean`
    (~8 references)

  Use `grep -n "Candidates.V63.Summability" Candidates/V<n>.lean`
  to enumerate every qualified reference per consumer before
  editing; the dominant pattern is `(ProofRefinement.Korenblum.
  Candidates.V63.Summability.six_summability_shapes_from_h2 …)`
  inside `· exact (…` blocks at lines 235–272 (varying by
  consumer) plus one `have hkit := …` near the witness-construction
  step. Each rewrite is a one-line replacement. **Verify zero
  residuals** with `grep -n "Candidates.V63.Summability"
  Candidates/V<n>.lean` after the rewrite — the result should be
  empty for V64–V68 (V63 itself retains the old namespace via
  the shim).

  Each candidate's evaluator-relevant content
  (`def c_value`, `def *_window_mass_lower`, `axiom hH2_v6×`,
  `axiom hCircleGapInt_v6×`, `theorem v6×_witness`,
  `theorem korenblum_constant_search`) is preserved verbatim.
  Only the import line and qualified reference changes.

- **Update** `ProofRefinement/Korenblum/lemma.toml`:
  - The candidate-side `[import_policy].allowed_exact` row
    `"ProofRefinement.Korenblum.Candidates.V63.Summability"` is
    **kept as-is** (V63 still imports the per-candidate
    namespace via the shim, or has been updated; either way V63
    itself is unchanged from the user's perspective). The newly
    required path `"ProofRefinement.Korenblum.Proof.Summability"`
    is **already covered** by the existing `allowed_prefixes`
    entry `"ProofRefinement.Korenblum.Proof"`, so no
    `[import_policy]` entry add is needed.
  - The `[workspace_import_policy]` is unchanged: the new module
    lives under the existing `ProofRefinement.Korenblum.*`
    prefix.
  - **Document** the hoist in a comment block above the
    `Candidates.V63.Summability` row, mirroring sprint 097's
    annotation pattern: "Sprint 098: hoisted to
    `ProofRefinement.Korenblum.Proof.Summability`; the
    per-candidate row is retained for V63's local consumption
    via a thin re-export shim. Completes the V63 derived-theorem
    trio (with sprints 096 + 097)."

- **Re-evaluate V68** by running the candidate evaluator on
  `Candidates/V68.lean` and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds;
  - `Evaluator.py --file Candidates/V68.lean` succeeds with
    `pass: true` and `score: "71313/200000"` (unchanged from the
    pre-hoist evaluator run);
  - V68's `axioms_used` set is unchanged conjunct-for-conjunct
    relative to the pre-hoist log entry (set-theoretically): the
    six entries
    `propext`, `Classical.choice`, `Quot.sound`,
    `ProofRefinement.Korenblum.h_eleven_window_mass_certified_at_356565_modeJ10`,
    `ProofRefinement.Korenblum.Candidates.V68.hH2_v68`,
    `ProofRefinement.Korenblum.Candidates.V68.hCircleGapInt_v68`.

- **Verify all five direct downstream consumers compile** after the
  import update, by running
  `lake build ProofRefinement.Korenblum.Candidates.V64`,
  `… V65`, `… V66`, `… V67`, `… V68` in turn. If any fails, the
  import update has a typo or a qualified reference was missed.
  Also `lake build ProofRefinement.Korenblum.Candidates.V63`
  to confirm the shim still works for V63's own consumption.

- **Optionally re-evaluate V64, V65, V66, V67** to confirm none
  of them regress. As in sprints 096/097, this is bounded extra
  work but is an important falsifier — if any of these
  candidates' `pass` status flips or `score` changes, the hoist
  has introduced an unintended trust-surface change. The hoist
  is a pure namespace rewrite, so the only failure mode is a
  typo or missed reference.

- `Experience.md`: append a "Sprint 098 — Summability hoist
  (V63 trio complete)" subsection summarizing the move, the
  consumer list, the V68 re-evaluation result (score unchanged
  at `71313/200000`, audit envelope unchanged), and the forward
  implication: future candidates can import `Proof.Summability`
  directly instead of from the per-candidate path; the V63
  derived-theorem cone is now fully relocated to `Proof/` with
  V63's per-candidate files reduced to thin re-export shims for
  backward compatibility.

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_098 PASS|FAIL: …`).

No edits to:
- `KorenblumPaper/` (read-only).
- `Numerical_Library/` (no oracle changes).
- `Proposals/` (no proposal filed; not needed — the hoist is a
  pure relocation of paper-axiom-free theorems within the
  workspace, not a trust-base expansion).
- The mathematical content of any theorem or lemma in
  `Summability.lean` (preserved verbatim).
- `Candidates/V63/Integrability.lean` (sprint 097's shim — kept
  as-is) or `Candidates/V63/DiskInnerSeriesBridge.lean`
  (sprint 096's shim — kept as-is).
- V68's `c_value`, `eleven_window_mass_lower`, `hH2_v68`,
  `hCircleGapInt_v68`, or oracle axiom (preserved verbatim).
- `Proof/CandidateContract.lean`, `Proof/Main.lean`,
  `Proof/Reduction.lean`, `Proof/ProblemAxioms.lean`,
  `Proof/DiskInnerSeriesBridge.lean` (sprint 096's hoisted file),
  `Proof/Integrability.lean` (sprint 097's hoisted file).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Summability`
   succeeds (the new shared module compiles in isolation).

2. `lake build ProofRefinement.Korenblum.Candidates.V63` succeeds
   (V63 either imports the hoisted module via the shim or has
   been updated to import directly; either way V63 still
   compiles).

3. `lake build ProofRefinement.Korenblum.Candidates.V64` succeeds.

4. `lake build ProofRefinement.Korenblum.Candidates.V65` succeeds.

5. `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds.

6. `lake build ProofRefinement.Korenblum.Candidates.V67` succeeds.

7. `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds.

8. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (= `356565/1000000`,
   unchanged from V68's pre-hoist score).

9. The post-hoist V68 evaluator log entry's `axioms_used` set is
   **identical** (set-theoretically, comparing the `name` field
   of each entry) to the pre-hoist log entry's `axioms_used`
   set: exactly the six entries listed above. No new axioms
   introduced. No old axioms removed.

10. The new file `Proof/Summability.lean` contains the same
    seven top-level theorems
    (`summable_plus_disk_weight`,
    `summable_plus_sigma_at_c`,
    `summable_minus_disk_weight`,
    `summable_minus_sigma_at_c`,
    `summable_minus_kernel_weight`,
    `summable_minus_sigma_uniform_on_open`,
    `six_summability_shapes_from_h2`)
    matching the original file's theorems by signature, plus the
    same nine helper `lemma`s, no `axiom`s, no `sorry`s. The
    theorem names are preserved (or trivially aliased via the
    shim) so that direct imports in V64–V68 type-check without
    requiring further proof updates.

11. The post-hoist V68 evaluator log entry's `imports` field
    contains `ProofRefinement.Korenblum.Proof.Summability`
    (and **does not** contain
    `ProofRefinement.Korenblum.Candidates.V63.Summability`,
    unless V63 itself is in the transitive import set — which
    it currently is not for V64–V68; V64–V68 import only the V63
    derived files, not the V63 candidate itself).

12. `Experience.md` and `Bulletin.md` each gain one row per the
    standard pattern.

The sprint is **PASS** if all 12 criteria are met. The sprint is
**FAIL** if any of V63–V68 fails to compile after the import
update, or if V68's evaluator score changes from `71313/200000`,
or if V68's `axioms_used` set gains or loses any entry.

## Out of scope

- Edit the mathematical content of any of the seven theorems or
  nine helper lemmas in `Summability.lean`. The hoist is a pure
  relocation; the proofs are byte-preserved (modulo namespace
  rewrites).

- Hoist `Candidates/V66/Branch1Integrability.lean` to
  `Proof/Branch1Integrability.lean`. This is the natural next
  candidate if a third consumer of branch-1 integrability ever
  appears, but currently only V67 and V68 import it (two
  consumers, both using the same eight/eleven-window architecture
  family) — sprint 097 explicitly demoted Branch1Integrability
  hoist as architecture-specific. Queue for a future sprint
  after a cross-architecture demand surfaces.

- Hoist V64's `TauWindowEndpoints.lean`, V66's
  `SevenWindowEndpoints.lean`, V67's `EightWindowEndpoints.lean`,
  or V68's `ElevenWindowEndpoints.lean`. These are
  window-architecture specific (one set of endpoints per
  architecture) and are not reused as broadly as the V63 trio.

- Add or remove free axioms. The hoist preserves the trust
  surface conjunct-for-conjunct.

- Add or modify oracles. No oracle interaction.

- File a `Proposals/` entry. The hoist is a pure relocation of
  paper-axiom-free theorems; no trust-base expansion is involved.

- Change the final theorem statement of any candidate.

- Edit `KorenblumPaper/`, `Numerical_Library/`, or
  `lemma.toml:[seed_axioms]`/`[[oracles]]`. Only the
  `[import_policy]` documentation comment may be added to note
  the hoist; no policy entries are added or removed.

- Discharge `hH2_v6×` or `hCircleGapInt_v6×` from
  `Section2Assumptions` (Slack 4 / Bulletin §B(4)). This
  requires a `KorenblumPaper/` edit (forbidden by AGENT_BRIEF
  lines 188-190) or a trust-base expansion proposal whose math
  is not pinned tightly enough yet; out of scope for a hoist
  sprint.

- Push past V68's `c = 71313/200000`. The score-push surface at
  the existing trust surface is exhausted (Slacks 1, 3, 5
  falsified by sprints 093, 094, 095; Slack 2 effectively
  settled by sprint 077; Slack 4 needs a trust expansion).
  After this sprint, the live frontier remains V68 at
  `71313/200000`.

- Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`. No
  current consumer; queueing it speculatively before
  establishing a Lean derivation chain that needs it would risk
  infrastructure-speculation work. Best queued *after* a sprint
  that explicitly needs the boundary-L² expansion as a
  load-bearing step.

- Migrate any oracle wrapper to interval arithmetic
  (Bulletin §C 5). Score-neutral credibility advance, but
  larger scope than a one-file hoist; queue after the V63 trio
  hoist sequence is complete (i.e. after this sprint).

- Run any Phase 0 numerical falsifier sweep. This sprint is
  structural cleanup only.

## Time budget

≤ 30 minutes runtime (six `lake build` invocations of ~10–60
seconds each plus one `Evaluator.py` invocation of ~3 minutes
plus optional re-evaluation of V64/V65/V66/V67 of ~3 minutes
each; in line with the wall-clock profile of sprints 096 and
097).

≤ 1 generator session (~1.5–2.5 hours including the file move,
five import-line rewrites with ~30+ qualified-reference
replacements per consumer pair, lemma.toml documentation
comment, V68 re-evaluation, optional V63–V67 re-evaluations,
witness update to `Experience.md`, and Bulletin append).

## Stop conditions

- All 12 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- Any of V63–V68 fails to compile after the import update:
  `STATUS=BLOCKED` with the exact compile error and the
  offending qualified reference. Most likely cause: a missed
  qualified reference to
  `ProofRefinement.Korenblum.Candidates.V63.Summability.foo`
  inside one of the consumer files, beyond the import line
  itself. With ~30+ call sites across V64–V68, careful
  per-consumer `grep` verification before and after rewriting
  is critical.

- V68's evaluator score changes from `71313/200000` after the
  hoist: `STATUS=BLOCKED` with the diff in `axioms_used` and
  the new score. Most likely cause: an accidental edit to V68's
  body during the qualified-reference rewrite (a careful
  generator should prevent this; the hoist is a pure
  namespace-rename edit per consumer).

- The `axioms_used` set diverges from V68's pre-hoist set:
  `STATUS=BLOCKED` with the set-difference. The hoist must be
  audit-envelope-preserving by construction; if it is not,
  something has gone wrong (e.g. the new `Proof/`-namespace
  module pulls in an unexpected dependency through Mathlib).

- The hoisted module fails to compile under the new namespace:
  `STATUS=BLOCKED` with the typecheck error. Most likely cause:
  a residual self-reference inside the file using the old
  namespace path that was missed in the namespace rewrite, or a
  helper lemma referenced by a top-level theorem proof that
  needs an explicit alias.

- A helper `lemma` turns out to be referenced from outside the
  file (i.e. by qualified name from V64–V68): `STATUS=BLOCKED`
  with the helper-name diff. Resolution: add an alias for that
  helper in the shim or directly in the consumer's qualified
  reference rewrite. Sprint 097 found no such cases for
  Integrability; sprint 098 should `grep` for each of the nine
  helpers' fully-qualified names across V64–V68 before
  finalizing the shim shape.

- Trust expansion needed (the hoisted module unexpectedly
  requires a paper-axiom field not in the existing
  `Section2Assumptions` carrier or a Mathlib lemma not currently
  imported by the workspace): `STATUS=BLOCKED_NEEDS_HUMAN`.
  Note: this should not occur — the original
  `Candidates/V63/Summability.lean` is paper-axiom-free by
  inspection (its imports are `Mathlib`,
  `KorenblumPaper.PaperAxioms`,
  `KorenblumPaper.OneModePaperBridge`, all pinned in
  `[workspace_import_policy]`); the namespace rewrite cannot
  introduce a trust dependency.
