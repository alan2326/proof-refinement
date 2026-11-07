# Sprint 097: Hoist `Integrability` from `Candidates/V63/` to `Proof/` for shared reuse across V64–V68 (and any future candidate)

**Created**: 2026-05-05 by Planner
**Parent candidate**: `Candidates/V68.lean` (live frontier, evaluator-confirmed at `c = 71313/200000 = 356565/1000000`; last sprint 096 confirmed V68 score-and-axioms preserved through the `DiskInnerSeriesBridge` hoist)
**Target file**: `ProofRefinement/Korenblum/Proof/Integrability.lean` (new shared module; ships V64–V68 candidate updates pointing at it)
**Direction**: section2-proof (structural — score-neutral hoist of a paper-axiom-free derived-theorem module from per-candidate scope to shared `Proof/` scope, restoring AGENT_BRIEF compliance for the second of three V63 derived files; follows sprint 096's clean template)

## Goal

Move the paper-axiom-free derived-theorem module
`ProofRefinement.Korenblum.Candidates.V63.Integrability`
(currently at `Candidates/V63/Integrability.lean`, 315 lines, two
`theorem`s + several private `lemma`s, no `axiom`s, no `sorry`s) to
a shared location at `Proof/Integrability.lean` under the namespace
`ProofRefinement.Korenblum.Proof.Integrability`, update the five
downstream consumers (V64, V65, V66, V67, V68) to import the
hoisted module, and re-evaluate V68 to confirm the score remains
`c = 71313/200000 = 356565/1000000`. The file's mathematical
content is preserved byte-for-byte modulo namespace and import-line
rewrites.

The move uses neither equation `(15)` nor any new oracle. It is a
structural cleanup that restores compliance with the AGENT_BRIEF's
per-candidate-scope rule, exactly mirroring sprint 096's
`DiskInnerSeriesBridge` hoist on a different file.

## Why

The AGENT_BRIEF (lines 175-195) pins the per-candidate-scope rule:
"the file is imported only by `Candidates/V<N>.lean` (or by other
files under `Candidates/V<N>/`), never by `KorenblumPaper/`,
`Proof/`, or other candidates." `Candidates/V63/Integrability.lean`
is currently imported by **five** other candidates beyond V63 itself
(V64, V65, V66, V67, V68) — every multi-window c-push from V64
onward. Sprint 096's verdict explicitly noted: "The other two V63
derived-theorem files (`Integrability.lean`, `Summability.lean`)
are also widely imported across V64–V68 and would benefit from the
same hoist treatment — queued as candidates for follow-up sprints."
Sprint 097 picks up that queue.

The two theorems in the file —
`modeScalarIntegrand_intervalIntegrable` (the general-`j`
parametric `IntervalIntegrable` of `ModeBridge.scalarIntegrand`)
and `mode_two_and_one_scalarIntegrand_intervalIntegrable` (its
two-window consolidation at `(j_1, j_2) = (2, 1)`) — are
load-bearing for every multi-window c-push: V64 (j=2 + j=1),
V65 (j=2 + j=1), V66 (j=4..1, four invocations of the parametric
form), V67 (j=7..1, seven invocations), V68 (j=10..1, ten
invocations). Hoisting once now is bounded; deferring as the
candidate stream lengthens compounds the per-candidate-scope rule
violation.

The hoist is preferred over the four other candidate sprint shapes
considered:

  (a) **Hoist `Summability.lean`** instead. Summability is the
      third V63 file with the same per-candidate-scope rule
      violation, but it is larger (498 lines, seven `theorem`s
      plus nine helper `lemma`s vs. Integrability's 315 lines /
      two `theorem`s + smaller helper set). Sprint 096's verdict
      noted both Integrability and Summability are queued; doing
      the smaller one first preserves the one-generator-session
      bound while replicating sprint 096's pattern. **Demoted**:
      preferred ordering is Integrability now, Summability in
      sprint 098 if this sprint's pattern is clean (mirror of
      sprint 096's "hoist DiskInnerSeriesBridge first, then
      Integrability/Summability" sequencing).

  (b) **Wang Lemma 2 / Fourier orthogonality derived theorem in
      `Proof/`**. Long-standing brief target. No current consumer
      — would build infrastructure that nothing immediately uses,
      risking speculative work. Sprint 096 explicitly demoted this
      for the same reason; the same demotion applies here. Best
      queued *after* a sprint that establishes the consuming Lean
      derivation chain.

  (c) **New analytical attempt at Slack 2 (per-k cross-coupling
      lift)**. Sprint 077's data at c = 0.35645 reports kernel
      margin uniformly `≈ −0.86 to −0.99` across all α-families
      and all canonical extremals E1–E5 in the contraction
      regime. Pushing to V68's c (+1.15e-4 above sprint 077's c
      in the c-axis) is mathematically unlikely to reverse a
      uniform −90% margin. Same chain the seed uses under a
      marginally different parameter — **demoted as not novel**.

  (d) **Slack 4: discharge `hH2_v6×` from `Section2Assumptions`**.
      Bulletin §B(4) and Slack 4 explicitly name this. **But**
      `Candidates/V63/Summability.lean` lines 26-38 document the
      structural blocker: *"The bundled `Section2Assumptions`
      structure does NOT carry coefficient-level summability data
      … The V64+ c-push will need to either carry `(hH2_a, hH2_b)`
      as candidate-side hypotheses (free axiom, expanding the seed
      envelope by two axioms) or file proposal_004 to add H²
      fields to `Section2Assumptions`."* Adding fields to
      `Section2Assumptions` requires editing `KorenblumPaper/`,
      which the AGENT_BRIEF (lines 188-190) explicitly forbids the
      generator from doing. **Demoted**: not runnable as a sprint
      without a prior trust-base expansion proposal.

  (e) **Interval-arithmetic re-discharge of one oracle**
      (Bulletin §C 5). Score-neutral credibility advance. But it
      requires significant `Numerical_Library/` work plus
      `[[oracles]]` re-registration plus careful pre-verification
      under `mpmath.iv` or `arb` — a larger scope than a one-file
      hoist. **Demoted**: bigger scope per session; queue after
      the V63-trio hoist sequence is complete.

The strongest objection to the chosen direction (hoist
Integrability) is "is it really worth a generator session for a
pure cleanup?" The answer is the same as sprint 096's: yes, the
per-candidate-scope rule violation has five direct instances (plus
V62's transitive dependency through V63's other files), and the
violation compounds as the candidate stream lengthens. Sprint 096
established the hoist template is clean (V68's score and audit
envelope preserved byte-for-byte); sprint 097 applies the template
to the next file in the queue.

## Concrete edits expected

- **Create** `ProofRefinement/Korenblum/Proof/Integrability.lean`:
  copy the entire content of
  `ProofRefinement/Korenblum/Candidates/V63/Integrability.lean`,
  changing only:
  - the namespace declaration from
    `namespace ProofRefinement.Korenblum.Candidates.V63.Integrability`
    to
    `namespace ProofRefinement.Korenblum.Proof.Integrability`,
  - the file header docstring's location reference (replace
    "Sprint 080, Phase A: per-candidate derived-theorem file …"
    with a header reflecting "Sprint 097: hoisted from
    `Candidates/V63/Integrability.lean` for shared reuse across
    V63–V68 and future candidates"),
  - the corresponding closing `end` namespace statement.
  All theorems and helper lemmas (`modeScalarIntegrand_intervalIntegrable`,
  `mode_two_and_one_scalarIntegrand_intervalIntegrable`, plus any
  `private`/section-local helpers used by their proofs) are
  preserved verbatim. No `axiom`s, no `sorry`s, no edits to
  mathematical content. The imports
  (`Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`,
  `KorenblumPaper.PaperAxioms`, `KorenblumPaper.OneModePaperBridge`)
  are preserved byte-for-byte; all are already pinned in
  `lemma.toml:[workspace_import_policy]`.

- **Update** `ProofRefinement/Korenblum/Candidates/V63/Integrability.lean`:
  reduce to a thin re-export shim that imports
  `ProofRefinement.Korenblum.Proof.Integrability` and
  re-exports the two top-level theorems under the original
  per-candidate namespace
  `ProofRefinement.Korenblum.Candidates.V63.Integrability`,
  via trivial `theorem` aliases of the form
  `theorem foo := ProofRefinement.Korenblum.Proof.Integrability.foo`.
  This preserves backward compatibility for V63 itself (which
  imports the per-candidate namespace by its original name) so
  V63 does not need to be edited at the candidate level. Mirror
  the shape of sprint 096's
  `Candidates/V63/DiskInnerSeriesBridge.lean` shim. **OR** — if
  the generator finds it cleaner — directly edit V63 to import
  the hoisted module and update its qualified references. Either
  path is acceptable; whichever produces a smaller diff is
  preferred. Document the choice in the candidate header
  comment.

  Note on private/section-local lemmas: if any helper lemma in
  the original file is referenced by name from outside the file
  (unlikely — Integrability's only outside-callers use the two
  top-level `theorem` names), include corresponding aliases in
  the shim. Sprint 096's experience suggests aliasing only the
  top-level theorems is sufficient; helper lemmas private to the
  proof bodies do not need re-export.

- **Update imports** in each of the five downstream consumers, by
  replacing the line
    `import ProofRefinement.Korenblum.Candidates.V63.Integrability`
  with
    `import ProofRefinement.Korenblum.Proof.Integrability`
  and updating any qualified references from
  `ProofRefinement.Korenblum.Candidates.V63.Integrability.*`
  to
  `ProofRefinement.Korenblum.Proof.Integrability.*`
  in the affected files:
  - `ProofRefinement/Korenblum/Candidates/V64.lean`
  - `ProofRefinement/Korenblum/Candidates/V65.lean`
  - `ProofRefinement/Korenblum/Candidates/V66.lean`
  - `ProofRefinement/Korenblum/Candidates/V67.lean`
  - `ProofRefinement/Korenblum/Candidates/V68.lean`

  (V62 also imports `Candidates.V63.Integrability` per the
  workspace-imports list; verify by `grep` and update the import
  line there too if present. Sprint 096's contract overcounted
  V62 by one for `DiskInnerSeriesBridge` because V62 only
  transitively imported it via V63's other files; for
  `Integrability`, V62's actual imports must be checked
  empirically and the candidate updated only if the import line
  is direct. The generator should `grep -l
  "Candidates.V63.Integrability" Candidates/*.lean` first to
  produce the exact consumer list and use that as the
  authoritative reference.)

  Each candidate's evaluator-relevant content (`def c_value`,
  `def *_window_mass_lower`, `axiom hH2_v6×`,
  `axiom hCircleGapInt_v6×`, `theorem v6×_witness`,
  `theorem korenblum_constant_search`) is preserved verbatim.
  Only the import line and qualified reference changes.

- **Update** `ProofRefinement/Korenblum/lemma.toml`:
  - The candidate-side `[import_policy].allowed_exact` row
    `"ProofRefinement.Korenblum.Candidates.V63.Integrability"`
    is **kept as-is** (V63 still imports the per-candidate
    namespace via the shim, or has been updated; either way V63
    itself is unchanged from the user's perspective). The newly
    required path
    `"ProofRefinement.Korenblum.Proof.Integrability"` is
    **already covered** by the existing `allowed_prefixes` entry
    `"ProofRefinement.Korenblum.Proof"` (line 63), so no
    `[import_policy]` add is needed.
  - The `[workspace_import_policy]` is unchanged: the new module
    lives under the existing `ProofRefinement.Korenblum.*`
    prefix (line 74).
  - **Document** the hoist in a comment block above the
    `Candidates.V63.Integrability` row, mirroring sprint 096's
    annotation pattern: "Sprint 097: hoisted to
    `ProofRefinement.Korenblum.Proof.Integrability`; the
    per-candidate row is retained for V63's local consumption
    via a thin re-export shim."

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

- **Verify all five downstream consumers compile** after the
  import update, by running
  `lake build ProofRefinement.Korenblum.Candidates.V64`,
  `… V65`, `… V66`, `… V67`, `… V68` in turn. If any fails, the
  import update has a typo or a qualified reference was missed.

- **Optionally re-evaluate V64, V65, V66, V67** to confirm none
  of them regress. As in sprint 096, this is bounded extra work
  but is an important falsifier — if any of these candidates'
  `pass` status flips or `score` changes, the hoist has
  introduced an unintended trust-surface change. The hoist is a
  pure namespace rewrite, so the only failure mode is a typo or
  missed reference; the evaluator runs are cheap (~30s each) and
  catching a regression is worth the time.

- `Experience.md`: append a "Sprint 097 — Integrability hoist"
  subsection summarizing the move, the consumer list, the V68
  re-evaluation result (score unchanged at `71313/200000`, audit
  envelope unchanged), and the forward implication (future
  candidates can import `Proof.Integrability` directly instead of
  from the per-candidate path; `Summability.lean` remains queued
  for sprint 098 if this sprint's pattern is clean).

- `Bulletin.md`: append one row per the standard pattern
  (`sprint_097 PASS|FAIL: …`).

No edits to:
- `KorenblumPaper/` (read-only).
- `Numerical_Library/` (no oracle changes).
- `Proposals/` (no proposal filed; not needed — the hoist is a
  pure relocation of paper-axiom-free theorems within the
  workspace, not a trust-base expansion).
- The mathematical content of any theorem in `Integrability.lean`
  (preserved verbatim).
- `Candidates/V63/Summability.lean` or
  `Candidates/V63/DiskInnerSeriesBridge.lean` (the shim from
  sprint 096) — Summability is queued for sprint 098;
  DiskInnerSeriesBridge already hoisted.
- V68's `c_value`, `eleven_window_mass_lower`, `hH2_v68`,
  `hCircleGapInt_v68`, or oracle axiom (preserved verbatim).
- `Proof/CandidateContract.lean`, `Proof/Main.lean`,
  `Proof/Reduction.lean`, `Proof/ProblemAxioms.lean`,
  `Proof/DiskInnerSeriesBridge.lean` (sprint 096's hoisted file).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Integrability`
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

10. The new file `Proof/Integrability.lean` contains the same
    top-level theorems (`modeScalarIntegrand_intervalIntegrable`
    and `mode_two_and_one_scalarIntegrand_intervalIntegrable`)
    matching the original file's theorems by signature, no
    `axiom`s, no `sorry`s. The two theorem names are preserved
    (or trivially aliased via the shim) so that direct imports
    in V64–V68 type-check without requiring further proof
    updates.

11. The post-hoist V68 evaluator log entry's `imports` field
    contains `ProofRefinement.Korenblum.Proof.Integrability`
    (and **does not** contain
    `ProofRefinement.Korenblum.Candidates.V63.Integrability`,
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

- Edit the mathematical content of either of the two theorems in
  `Integrability.lean`. The hoist is a pure relocation; the
  proofs are byte-preserved (modulo namespace rewrites).

- Hoist the third V63 derived-theorem file
  (`Summability.lean`). Summability is also widely imported
  across V63–V68 and would benefit from the same treatment, but
  it is larger (498 lines vs. 315) and has more helper lemmas
  (nine vs. a small private set). Hoisting both Integrability
  and Summability in one sprint risks exceeding the
  one-generator-session bound. Summability is queued for sprint
  098 if this sprint's pattern is clean. Sprint 096 used the
  same "hoist one file at a time" sequencing.

- Hoist V64's `TauWindowEndpoints.lean`, V66's
  `Branch1Integrability.lean` and `SevenWindowEndpoints.lean`,
  V67's `EightWindowEndpoints.lean`, or V68's
  `ElevenWindowEndpoints.lean`. These are window-architecture
  specific (one set of endpoints per architecture) and are not
  reused as broadly as the V63 trio.

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
  lines 188-190) or a trust-base expansion proposal; out of
  scope for a hoist sprint.

- Push past V68's `c = 71313/200000`. The score-push surface at
  the existing trust surface is exhausted. After this sprint,
  the live frontier remains V68 at `71313/200000`.

- Attack Wang Lemma 2 / Fourier orthogonality in `Proof/`. No
  current consumer; queueing it speculatively before
  establishing a Lean derivation chain that needs it would risk
  infrastructure-speculation work. Best queued *after* a sprint
  that explicitly needs the boundary-L² expansion as a
  load-bearing step.

- Run any Phase 0 numerical falsifier sweep. This sprint is
  structural cleanup only.

## Time budget

≤ 30 minutes runtime (six `lake build` invocations of ~10–60
seconds each plus one `Evaluator.py` invocation of ~3 minutes
plus optional re-evaluation of V64/V65/V66/V67 of ~3 minutes
each; in line with the wall-clock profile of sprint 096's
hoist).

≤ 1 generator session (~1.5–2.5 hours including the file move,
five (or six counting V62 if it is a direct consumer)
import-line rewrites, lemma.toml documentation comment, V68
re-evaluation, optional V64–V67 re-evaluations, witness update
to `Experience.md`, and Bulletin append).

## Stop conditions

- All 12 acceptance criteria met:
  `STATUS=READY_FOR_EVALUATION`.

- Any of V63–V68 fails to compile after the import update:
  `STATUS=BLOCKED` with the exact compile error and the
  offending qualified reference. Most likely cause: a missed
  qualified reference to
  `ProofRefinement.Korenblum.Candidates.V63.Integrability.foo`
  inside one of the consumer files, beyond the import line
  itself.

- V68's evaluator score changes from `71313/200000` after the
  hoist: `STATUS=BLOCKED` with the diff in `axioms_used` and
  the new score. Most likely cause: an accidental edit to V68's
  body during the import-line rewrite (a careful generator
  should prevent this; the hoist is a one-line edit per
  candidate).

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

- Trust expansion needed (the hoisted module unexpectedly
  requires a paper-axiom field not in the existing
  `Section2Assumptions` carrier or a Mathlib lemma not currently
  imported by the workspace): `STATUS=BLOCKED_NEEDS_HUMAN`.
  Note: this should not occur — the original
  `Candidates/V63/Integrability.lean` is paper-axiom-free by
  inspection (its imports are
  `Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable`,
  `KorenblumPaper.PaperAxioms`, `KorenblumPaper.OneModePaperBridge`,
  all pinned in `[workspace_import_policy]`); the namespace
  rewrite cannot introduce a trust dependency.
