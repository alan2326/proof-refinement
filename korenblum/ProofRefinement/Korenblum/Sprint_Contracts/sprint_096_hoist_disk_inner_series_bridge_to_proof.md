# Sprint 096: Hoist `DiskInnerSeriesBridge` from `Candidates/V63/` to `Proof/` for shared reuse across V62/V64–V68 (and any future candidate)

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`)
**Target file**: `ProofRefinement/Korenblum/Proof/DiskInnerSeriesBridge.lean` (new shared module; ships V62 and V64–V68 candidate updates pointing at it)
**Direction**: section2-proof (structural — score-neutral hoist of a paper-axiom-free derived-theorem module from per-candidate scope to shared `Proof/` scope, restoring compliance with the AGENT_BRIEF rule that per-candidate files are imported only by their own candidate plus its sibling files)

## Goal

Move the paper-axiom-free derived-theorem module
`ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`
(currently at `Candidates/V63/DiskInnerSeriesBridge.lean`) to a
shared location at `Proof/DiskInnerSeriesBridge.lean` under the
namespace `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`,
update the six downstream consumers (V62, V64, V65, V66, V67, V68)
to import the hoisted module, and re-evaluate V68 to confirm the
score remains `c = 71313/200000 = 356565/1000000`. The file's
mathematical content (five `theorem`s, no `axiom`s) is preserved
byte-for-byte modulo namespace and import-line rewrites.

The move uses neither equation `(15)` nor any new oracle. It is a
structural cleanup that restores compliance with the AGENT_BRIEF's
per-candidate-scope rule and unblocks future candidates from
having to either re-prove these theorems or import them from a
sibling candidate's directory.

## Why

The AGENT_BRIEF (lines 175-195) pins the per-candidate-scope rule:
"the file is imported only by `Candidates/V<N>.lean` (or by other
files under `Candidates/V<N>/`), never by `KorenblumPaper/`,
`Proof/`, or other candidates." The current state violates this
rule — `Candidates/V63/DiskInnerSeriesBridge.lean` is imported by
**six** other candidates (V62, V64, V65, V66, V67, V68), all the
multi-window c-pushes from V62 onward.

The AGENT_BRIEF also specifies the remediation: "If a derived
theorem is genuinely useful across multiple future candidates,
propose hoisting it to a shared location in a sprint contract."
Six consumers across the entire post-V52 candidate stream
satisfies "genuinely useful across multiple future candidates"
to a degree that no other per-candidate file in the workspace
matches.

The hoist is preferred over Wang Lemma 2 / Fourier orthogonality
(also a long-standing brief target — see Bulletin Section B and
the user prompt) because:

1. **Concrete consumer list, byte-exact signature.** Six
   candidate files import this module today. Each import line is
   a one-line rewrite. The bridge's five theorem signatures are
   load-bearing for the multi-window reducer's `h_witness`
   construction; any consumer mismatch is immediately visible at
   typecheck time. Wang Lemma 2 has no current consumer; queueing
   it now would build infrastructure speculatively.

2. **Bounded scope, immediately runnable.** The hoist is a single
   file move + namespace rename + six import-line rewrites + one
   `lemma.toml` edit. No new mathematical content is added. No
   trust-base expansion. No proposal needed (the module already
   contains only paper-axiom-free theorems; relocating them does
   not change the trust class).

3. **Unblocks future candidates without re-proving.** Any sprint
   beyond V68 that builds a multi-window c-push needs the
   `diskExcess = innerSeriesExcess` bridge. Today such a sprint
   either re-imports from `Candidates.V63.*` (compounding the
   per-candidate-scope violation) or duplicates the proof. After
   this sprint, future candidates simply
   `import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`
   and consume the bridge directly.

4. **Score-neutral, structurally positive.** Per the user prompt:
   "Score-neutral structural advances are explicitly allowed and
   useful." The hoist does not change V68's `c_value` (which
   remains `71313/200000`), nor does it change the trust surface
   (the module is paper-axiom-free both before and after the
   move). The audit envelope of every downstream candidate is
   unchanged conjunct-for-conjunct.

5. **Smallest meaningful structural cleanup.** The other two V63
   derived-theorem files (`Integrability.lean`, `Summability.lean`)
   are also imported by V64–V68 and would benefit from the same
   treatment, but they are larger and more architecture-coupled.
   Restricting this sprint to `DiskInnerSeriesBridge.lean` only
   keeps the cleanup bounded to one generator session and
   establishes the pattern; a follow-up sprint can hoist the
   other two if the sprint 096 pattern is clean.

The four candidate sprint shapes considered before settling on
this one:

  (a) **Wang Lemma 2 / Fourier orthogonality** (long-standing
      brief target). Highest analytical novelty per session,
      but no current consumer — would build infrastructure
      that nothing immediately uses, risking speculative work.
      Best queued *after* a sprint that establishes the
      consuming Lean derivation chain (e.g. a Slack 5
      successor that needs the boundary-L² expansion as a
      load-bearing step). Demoted: a useful derived-theorem
      file with no immediate consumer is precisely the
      "speculative analytical content" the AGENT_BRIEF cautions
      against by requiring the file to be "imported only by
      [its candidate]".

  (b) **Hoist `DiskInnerSeriesBridge.lean` to `Proof/`**
      (this sprint). Bounded, falsifiable, immediate consumer
      list, fixes a real per-candidate-scope rule violation,
      unblocks future candidates. Selected.

  (c) **New analytical attempt at Slack 2** (per-k cross-coupling
      lift, sprint 077's chain re-run at V68's c). Sprint 077's
      data at c = 0.35645 reports kernel margin uniformly `≈ −0.86
      to −0.99` across all α-families and all canonical extremals
      E1–E5 in the contraction regime |α(k)| < 1. Pushing to
      V68's c (+1.15e-4 in the c-axis) is mathematically unlikely
      to reverse a uniform −90% margin — same chain the seed uses
      under a marginally different parameter. Demoted as not
      novel.

  (d) **Phase 0 c-grid sweep at finer granularity**. The
      score-push surface at the existing trust surface is
      exhausted (sprints 093, 094, 095 falsified Slacks 1, 3, 5;
      sprint 077 effectively settled Slack 2). A finer grid is
      pure cleanup with no expected upside. Demoted as redundant.

The strongest objection to (b) is "is it really worth a generator
session for a pure cleanup?" The answer is yes: the
per-candidate-scope rule violation has six instances, and the
violation compounds as the candidate stream lengthens. Fixing it
once now is bounded; deferring it until a future sprint that needs
to use the bridge from yet another candidate compounds the
problem.

## Concrete edits expected

- **Create** `ProofRefinement/Korenblum/Proof/DiskInnerSeriesBridge.lean`:
  copy the entire content of
  `ProofRefinement/Korenblum/Candidates/V63/DiskInnerSeriesBridge.lean`,
  changing only:
  - the namespace declaration from
    `namespace ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`
    to
    `namespace ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`,
  - the file header docstring's location reference (replace
    "Sprint 082, Phase A: per-candidate derived-theorem file" with
    a header reflecting "Sprint 096: hoisted from
    `Candidates/V63/DiskInnerSeriesBridge.lean` for shared reuse
    across V62, V64–V68, and future candidates"),
  - the corresponding closing `end` namespace statement.
  All five theorems and their proofs are preserved verbatim. No
  `axiom`s, no `sorry`s, no edits to mathematical content.

- **Update** `ProofRefinement/Korenblum/Candidates/V63/DiskInnerSeriesBridge.lean`:
  reduce to a thin re-export shim that imports
  `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge` and
  re-exports each of the five theorems under the original
  per-candidate namespace
  `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`,
  via `export` declarations or trivial `theorem` aliases of the
  form `theorem foo := ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.foo`.
  This preserves backward compatibility for V63 itself (which
  imports the per-candidate namespace by its original name), so
  V63 does not need to be edited. **OR** — if simpler — directly
  edit V63 to import the hoisted module and update its references.
  The generator may pick whichever path produces a cleaner diff,
  documenting the choice in the candidate header.

- **Update imports** in each of the six downstream consumers, by
  replacing the line
    `import ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge`
  with
    `import ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`
  and updating any qualified references from
  `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.*`
  to
  `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge.*`
  in the affected files:
  - `ProofRefinement/Korenblum/Candidates/V62.lean`
  - `ProofRefinement/Korenblum/Candidates/V64.lean`
  - `ProofRefinement/Korenblum/Candidates/V65.lean`
  - `ProofRefinement/Korenblum/Candidates/V66.lean`
  - `ProofRefinement/Korenblum/Candidates/V67.lean`
  - `ProofRefinement/Korenblum/Candidates/V68.lean`

  Each candidate's evaluator-relevant content
  (`def c_value`, `def eight_window_mass_lower` /
  `def eleven_window_mass_lower`, `axiom hH2_v6×`,
  `axiom hCircleGapInt_v6×`, `theorem v6×_witness`,
  `theorem korenblum_constant_search`) is preserved verbatim. Only
  the import line and qualified reference changes.

- **Update** `ProofRefinement/Korenblum/lemma.toml`:
  - The candidate-side `[import_policy].allowed_exact` row
    `"ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge"`
    is **kept as-is** (V63 still imports the per-candidate
    namespace via the shim, or has been updated; either way V63
    itself is unchanged from the user's perspective). The newly
    required path
    `"ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge"` is
    **already covered** by the existing `allowed_prefixes` entry
    `"ProofRefinement.Korenblum.Proof"` (line 55-56), so no
    `[import_policy]` edit is needed.
  - The `[workspace_import_policy]` is unchanged: the new module
    lives under the existing `ProofRefinement.Korenblum.*` prefix
    (line 66-67).
  - **Document** the hoist in a comment block near the
    `Candidates.V63.DiskInnerSeriesBridge` row, e.g.
    "Sprint 096: hoisted to
    `ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`; the
    per-candidate row is retained for V63's local consumption".

- **Re-evaluate V68** by running the candidate evaluator on
  `Candidates/V68.lean` and confirming:
  - `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds;
  - `Evaluator.py --file Candidates/V68.lean` succeeds with
    `pass: true` and `score: "71313/200000"` (unchanged from the
    pre-hoist evaluator run);
  - V68's `axioms_used` set is unchanged conjunct-for-conjunct
    relative to the pre-hoist log entry: same six entries
    (`propext`, `Classical.choice`, `Quot.sound`,
    `h_eight_window_mass_certified_at_356565_modeJ10` (the
    sprint-092 oracle axiom — the actual name from the V68 log
    entry should be preserved verbatim; it may include "eleven"
    or "eight" depending on naming conventions in the codebase),
    `hH2_v68`, `hCircleGapInt_v68`).

- **Verify all six downstream consumers compile** after the
  import update, by running
  `lake build ProofRefinement.Korenblum.Candidates.V62`,
  `… V64`, `… V65`, `… V66`, `… V67`, `… V68` in turn. If any
  fails, the import update has a typo or a qualified reference
  was missed.

- **Optionally re-evaluate V62, V64, V65, V66, V67** to confirm
  none of them regress. This is bounded extra work but is an
  important falsifier — if any of these candidates' `pass`
  status flips or `score` changes, the hoist has introduced an
  unintended trust-surface change. Given the hoist is a pure
  namespace rewrite, the only failure mode is a typo or missed
  reference; the evaluator runs are cheap (~30s each) and
  catching a regression is worth the time.

- `Experience.md`: append a "Sprint 096 — DiskInnerSeriesBridge
  hoist" subsection summarizing the move, the consumer list, the
  V68 re-evaluation result (score unchanged at `71313/200000`,
  audit envelope unchanged), and the forward implication
  (future candidates can import
  `Proof.DiskInnerSeriesBridge` directly instead of from a
  per-candidate path; the other two V63 derived files
  (`Integrability.lean`, `Summability.lean`) are queued for a
  follow-up hoist if this sprint's pattern is clean).

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_096 PASS|FAIL: …`).

No edits to:
- `KorenblumPaper/` (read-only).
- `Numerical_Library/` (no oracle changes).
- `Proposals/` (no proposal filed; not needed — the hoist is a
  pure relocation of paper-axiom-free theorems within the
  workspace, not a trust-base expansion).
- The mathematical content of any theorem in
  `DiskInnerSeriesBridge.lean` (preserved verbatim).
- V68's `c_value`, `eleven_window_mass_lower`, `hH2_v68`,
  `hCircleGapInt_v68`, or oracle axiom (preserved verbatim).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.DiskInnerSeriesBridge`
   succeeds (the new shared module compiles).

2. `lake build ProofRefinement.Korenblum.Candidates.V62` succeeds.

3. `lake build ProofRefinement.Korenblum.Candidates.V63` succeeds
   (V63 either imports the hoisted module via the shim or has
   been updated to import directly; either way V63 still
   compiles).

4. `lake build ProofRefinement.Korenblum.Candidates.V64` succeeds.

5. `lake build ProofRefinement.Korenblum.Candidates.V65` succeeds.

6. `lake build ProofRefinement.Korenblum.Candidates.V66` succeeds.

7. `lake build ProofRefinement.Korenblum.Candidates.V67` succeeds.

8. `lake build ProofRefinement.Korenblum.Candidates.V68` succeeds.

9. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V68.lean` succeeds with
   `pass: true` and `score: "71313/200000"` (= `356565/1000000`,
   unchanged from V68's pre-hoist score).

10. The post-hoist V68 evaluator log entry's `axioms_used` set is
    **identical** (set-theoretically, comparing the `name` field
    of each entry) to the pre-hoist log entry's `axioms_used` set.
    No new axioms introduced. No old axioms removed.

11. The new file `Proof/DiskInnerSeriesBridge.lean` contains
    exactly five theorems (matching the original file's five
    theorems by signature), no `axiom`s, no `sorry`s. The five
    theorem names are preserved (or trivially aliased) so that
    the V63 shim or direct imports in V62/V64–V68 type-check
    without requiring further proof updates.

12. `Experience.md` and `Bulletin.md` each gain one row per the
    standard pattern.

The sprint is **PASS** if all 12 criteria are met. The sprint is
**FAIL** if any candidate V62–V68 fails to compile after the
import update, or if V68's evaluator score changes from
`71313/200000`, or if V68's `axioms_used` set gains or loses any
entry.

## Out of scope

- Edit the mathematical content of any of the five theorems in
  `DiskInnerSeriesBridge.lean`. The hoist is a pure relocation;
  the proofs are byte-preserved (modulo namespace rewrites).

- Hoist the other two V63 derived-theorem files
  (`Integrability.lean`, `Summability.lean`). These are also
  imported across V64–V68 and would benefit from the same
  treatment, but they are larger and more architecture-coupled;
  hoisting all three in one sprint would exceed the
  one-generator-session bound. They are queued for a follow-up
  sprint if this sprint's pattern is clean.

- Hoist V64's `TauWindowEndpoints.lean`, V66's
  `Branch1Integrability.lean` and `SevenWindowEndpoints.lean`,
  V67's `EightWindowEndpoints.lean`, or V68's
  `ElevenWindowEndpoints.lean`. These are window-architecture
  specific (one set of endpoints per architecture); they are not
  reused as broadly as the V63 trio and are not currently
  candidates for hoisting.

- Add or remove free axioms. The hoist preserves the trust
  surface conjunct-for-conjunct.

- Add or modify oracles. No oracle interaction.

- File a `Proposals/` entry. The hoist is a pure relocation of
  paper-axiom-free theorems; no trust-base expansion is involved.
  Per the user prompt's guidance, proposals are deferred.

- Change the final theorem statement of any candidate.

- Edit `KorenblumPaper/`, `Numerical_Library/`, or
  `lemma.toml:[seed_axioms]`/`[[oracles]]`. Only the
  `[import_policy]` documentation comment may be updated to note
  the hoist; no policy entries are added or removed.

- Run the Phase 0 numerical falsifier sweeps (Slacks 1/3/5
  already settled by sprints 093/094/095; Slack 2 settled by
  sprint 077). This sprint is structural cleanup, not score-push.

- Push past V68's `c = 71313/200000`. The score-push surface at
  the existing trust surface is exhausted. After this sprint,
  the live frontier remains V68 at `71313/200000`.

- Attack Wang Lemma 2 / Fourier orthogonality. This is a
  long-standing brief target, but it has no current consumer;
  queueing it speculatively before establishing a Lean derivation
  chain that needs it would risk infrastructure-speculation work.
  Best queued *after* a sprint that explicitly needs the
  boundary-L² expansion as a load-bearing step.

## Time budget

≤ 30 minutes runtime (six `lake build` invocations of ~10–60
seconds each plus one `Evaluator.py` invocation of ~10 seconds
plus optional re-evaluation of V62/V64/V65/V66/V67 of ~30s each;
in line with the wall-clock profiles of past structural sprints).

≤ 1 generator session (~1.5–2.5 hours including the file move,
six import-line rewrites, lemma.toml documentation comment, V68
re-evaluation, optional V62/V64–V67 re-evaluations, witness
update to `Experience.md`, and Bulletin append).

## Stop conditions

- All 12 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- Any of V62–V68 fails to compile after the import update:
  `STATUS=BLOCKED` with the exact compile error and the offending
  qualified reference. Most likely cause: a missed qualified
  reference to
  `ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge.foo`
  inside one of the consumer files, beyond the import line itself.

- V68's evaluator score changes from `71313/200000` after the
  hoist: `STATUS=BLOCKED` with the diff in `axioms_used` and the
  new score. Most likely cause: an accidental edit to V68's
  body during the import-line rewrite (a careful generator should
  prevent this; the hoist is a one-line edit per candidate).

- The `axioms_used` set diverges from V68's pre-hoist set:
  `STATUS=BLOCKED` with the set-difference. The hoist must be
  audit-envelope-preserving by construction; if it is not,
  something has gone wrong (e.g. the new Proof-namespace module
  pulls in an unexpected dependency through Mathlib).

- The hoisted module fails to compile under the new namespace:
  `STATUS=BLOCKED` with the typecheck error. Most likely cause:
  a residual self-reference inside the file using the old
  namespace path that was missed in the namespace rewrite.

- Trust expansion needed (the hoisted module unexpectedly
  requires a paper-axiom field not in the existing
  `Section2Assumptions` carrier): `STATUS=BLOCKED_NEEDS_HUMAN`.
  Note: this should not occur — the original
  `Candidates/V63/DiskInnerSeriesBridge.lean` is paper-axiom-free
  by inspection (its imports are `Mathlib`, `KorenblumPaper.PaperAxioms`,
  `KorenblumPaper.OneModePaperBridge`, and
  `ProofRefinement.Korenblum.Proof.Reduction`, all of which are
  pinned in `[workspace_import_policy]`); the namespace rewrite
  cannot introduce a trust dependency.
