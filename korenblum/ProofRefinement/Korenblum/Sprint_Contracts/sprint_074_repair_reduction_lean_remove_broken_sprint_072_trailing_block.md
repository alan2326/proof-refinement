# Sprint 074: repair `Proof/Reduction.lean` by removing the broken sprint_072 trailing block

**Created**: 2026-05-04 12:45 by Planner
**Parent candidate**: `Candidates/V57.lean` (sprint_073's deliverable, currently
non-buildable in-tree because of the broken `Reduction.lean`)
**Target file**: no new candidate file; repairs an existing trusted-surface
file. After repair, `Candidates/V57.lean` is re-evaluated as-is.
**Direction**: other (harness repair — restore `lake build` so future analytic
sprints can be evaluated).

## Goal

Surgically remove the half-completed sprint_072 multi-window τ-partition
reducer that an interrupted generator left at the tail of
`ProofRefinement/Korenblum/Proof/Reduction.lean`, restore `lake build` of
`Proof/Reduction.lean`, then confirm the previously-shipped V56 candidate and
sprint_073's V57 candidate both build and that V57 evaluates at the unchanged
score `7129/20000`.

This sprint is intentionally NOT a proof-search advance. No new
`c_value`, no new theorems, no new derived-theorem files, no new oracle, no
new axiom, no edits to `KorenblumPaper/`, `Numerical_Library/`, or
`lemma.toml`. The only objective is to undo the in-tree breakage so that the
harness can resume passing `lake build` for candidates.

## Why

The driver-level note in the planner invocation is explicit. The current
working tree of `Proof/Reduction.lean` is 8268 lines, of which only the first
102 lines come from `HEAD`; the remaining 8166 lines are uncommitted
prior-sprint work that built clean through sprint_071. The trailing block
beginning at line 7690 is sprint_072's interrupted multi-window τ-partition
reducer (the docstring `/-- Sprint 072 — first multi-window per-mode τ-partition
closing reducer ... -/` immediately followed by the half-finished theorem
`valid_of_perMode_multiWindow_tau_partition_eq8_eq9`); it produces:

- a type-mismatch error around line 8064;
- a `rewrite` motive-not-type-correct error around line 8191
  with the `hcEqStart0 : c = start 0` / `hSplit_c_start0` /
  `hSplit_start0` goal recorded in the planner brief.

The downstream consequence is that `lake build
ProofRefinement.Korenblum.Proof.Reduction` fails, and therefore every
`ProofRefinement.Korenblum.Candidates.V<N>.lean` that imports
`Proof.Main` (which transitively imports `Proof.Reduction`) also fails to
build. Sprint_073 PASSED in the structural sense — `Candidates/V57/DiskExcessLiftIntegrated.lean`
builds clean in isolation and is the workspace's first Λ-free disk-side
bound — but `Candidates/V57.lean` cannot even be evaluated until
`Reduction.lean` builds again.

Until repair lands, every subsequent generator session is locked out of
acceptance criterion 1 of the standard sprint template (`lake build
... .Candidates.V<N>` succeeds). The repair is the highest-priority option
because it is the unique unblocker for the entire harness; analytic
sprint shapes (V58 derived-theorem files, sprint_072 reattempts, novel
closing reducers) all depend on a working `Reduction.lean`. Without
repair, the harness can only ship isolated-build derived-theorem files
that never evaluate, which the planner brief explicitly warns about.

The repair is bounded, falsifiable, and small — the broken block has a
clean upper boundary in the file (a blank line at 7689 closes the last
working theorem `valid_of_perMode_tau_window_eq8_eq9`'s `calc` chain;
sprint_072's docstring opens at 7690), so the deletion is mechanical.

## Concrete edits expected

- `ProofRefinement/Korenblum/Proof/Reduction.lean`: delete every line from
  line 7690 through line 8267 inclusive (the entire sprint_072
  docstring `/-- Sprint 072 — first multi-window per-mode τ-partition
  closing reducer ... -/` plus the entire half-completed
  `theorem valid_of_perMode_multiWindow_tau_partition_eq8_eq9 ... `
  body up to but NOT including the existing closing
  `end ProofRefinement.Korenblum`). The repaired file should end with
  the last good theorem `valid_of_perMode_tau_window_eq8_eq9`'s final
  `calc` line followed by a blank line and then
  `end ProofRefinement.Korenblum`. Use the `Read` tool first to confirm
  exact line ranges before editing — the number of lines to delete is
  large and the boundary line numbers are sensitive to any prior edits.

  Concrete shape after repair:

      ...
      _ ≤ AnnulusIntegralReduction.annulusSlice paper.circleGap c 1 := hSliceLE
      _ = PaperAxioms.annulusExcess (PaperAxioms.circleGap a b) c := hAnnulusEq

      end ProofRefinement.Korenblum

  After the edit, the file should be approximately 7691 lines (the
  exact number is not important; what matters is acceptance criterion 1
  below).

  Do NOT touch any other content in `Reduction.lean`. The 16 sprints
  worth of theorems above line 7690 (through `valid_of_perMode_tau_window_eq8_eq9`
  ending around line 7689) are sprint_071's deliverable and earlier;
  they all built clean through sprint_071 and are part of the trusted
  in-tree surface for V56 and the existing tests. They MUST be
  preserved byte-for-byte.

- No edits to `Candidates/V57.lean`, `Candidates/V57/DiskExcessLiftIntegrated.lean`,
  `Candidates/V56.lean`, `Candidates/V56/`, any other candidate file,
  `KorenblumPaper/`, `Numerical_Library/`, `lemma.toml`, or any other
  file. The single-file scope is intentional.

- `Bulletin.md`: append a single status line and a single sprint-summary
  paragraph in the standard pattern (one row at the end of the priority
  block recording `harness 2026-05-04: sprint_074 driver run complete —
  ...`, plus a `sprint_074 PASS: ...` summary). The summary should record
  (i) the deletion range, (ii) the post-repair `lake build` PASS for
  `Reduction.lean`, V56, V57, and (iii) V57's evaluator outcome.

- `Experience.md`: append a single short paragraph in the existing
  format documenting that sprint_072's multi-window reducer attempt was
  rolled back at sprint_074 with the broken-block boundary precisely
  identified, so a future planner that wants to reattempt the
  multi-window τ-partition reducer knows where the prior attempt got
  stuck (the `hcEqStart0 : c = start 0` `rewrite` motive-not-type-correct
  obstruction at the original line 8191).

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Proof.Reduction` succeeds.

2. `lake build ProofRefinement.Korenblum.Candidates.V56` succeeds.

3. `lake build ProofRefinement.Korenblum.Candidates.V57` succeeds.

4. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V57.lean` succeeds with
   `pass: true` and `score = 7129/20000`. The axiom envelope MUST be
   byte-for-byte identical to V56's last successful evaluator run (per
   `Refinement_Log/log.jsonl`):
   `axioms_used = {propext, Classical.choice, Quot.sound,
   hEq15_oracle_certified_hp_35645}` plus whatever V57-namespaced
   wrappers are already shipped in `Candidates/V57.lean`.
   No new axioms, no missing axioms, no oracle-audit drift.

5. The repaired `Reduction.lean` retains every theorem from
   `valid_of_perMode_tau_window_eq8_eq9` (sprint_071's deliverable) and
   earlier. Confirm by `grep -c "^theorem " Proof/Reduction.lean`
   matching the count of theorems present at the head of the broken
   block (count theorems in the current 8268-line file with line
   numbers strictly less than 7690 before deleting; the post-repair
   count must equal that pre-repair count).

6. The repaired file's last non-blank lines before `end ProofRefinement.Korenblum`
   come from `valid_of_perMode_tau_window_eq8_eq9`'s closing `calc`
   chain, NOT from any sprint_072 content. After repair, `grep -n
   "valid_of_perMode_multiWindow_tau_partition_eq8_eq9"
   Proof/Reduction.lean` returns no matches; `grep -n "Sprint 072"
   Proof/Reduction.lean` returns no matches.

## Out of scope

- Edit older candidates (V0–V57) or any per-candidate derived-theorem
  file under `Candidates/V<N>/`.
- Change the final theorem statement, the candidate contract, or any
  proof in `Reduction.lean` other than removing the broken sprint_072
  trailing block.
- Reattempt or partially complete the sprint_072 multi-window
  τ-partition reducer. That belongs in a separate future sprint.
- Add a free-floating new axiom, a new oracle row in `lemma.toml`, a
  new entry in `[workspace_import_policy]`, or a new entry in
  `[import_policy]`. The repair is read-only with respect to all
  trust-surface files except `Reduction.lean`.
- Edit `KorenblumPaper/`, `Numerical_Library/`, `Proof/CandidateContract.lean`,
  `Proof/Main.lean`, or any other `Proof/*.lean` file.
- Run any Scratch numerical script. The repair is purely textual.
- Increase `c_value`, refine eq(15) bounds, or otherwise advance the
  proof search. The score MUST remain at the V52/V56 high-water mark
  `7129/20000`.

## Time budget

≤ 25 minutes runtime (mostly `lake build` time for V56, V57, and
Reduction.lean — the textual deletion itself is seconds).

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
- Edit applied but `lake build` of `Reduction.lean` still fails (e.g.
  the broken-block boundary was wrong, a stray fragment remains, or
  the repair revealed a deeper breakage above line 7690): `STATUS=BLOCKED`,
  with an obstruction note recording the exact failing build error and
  the surviving boundary line numbers — the planner will then queue a
  follow-up sprint with a tightened repair scope.
- A `lake build` failure unrelated to the deletion (e.g. an environment-
  level toolchain issue, missing Mathlib dep, OOM) surfaces:
  `STATUS=BLOCKED_NEEDS_HUMAN`, with the exact error captured. Do NOT
  attempt to "fix" upstream Mathlib / toolchain issues; that is a
  driver-level concern.
- The deletion succeeds and `Reduction.lean` builds, but V57's
  evaluator returns `pass: false` or a score other than `7129/20000`
  or an axiom envelope drift: `STATUS=BLOCKED`, with a verdict
  recording the evaluator output verbatim. The planner will then
  decide whether the V57 candidate itself needs touching (out of scope
  for this sprint) or whether a prior derived-theorem file changed.
