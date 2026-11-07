# Sprint 054: Pin `mpmath` + `python-flint` in a repo-root `pyproject.toml` so the canonical `uv run` evaluator can invoke the sprint 053 oracle, and re-run V48 to PASS

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V48.lean` (unchanged from sprint 053)
**Target file**: `Candidates/V48.lean` (no Lean change; the candidate already
exists at the seed and was verified gate-1/gate-2 PASS by sprint 053)
**Direction**: oracle-support — repair sprint 053's gate-3 failure by pinning
the Python dependency surface that `Numerical_Library/rigorous_scalar.py`
already requires; the substantive Lean and oracle-channel work was completed
in sprint 053, only the canonical evaluator environment is missing the runtime
dependencies.

## Goal

Make sprint 053's `[[oracles]]` channel actually executable in the canonical
`uv run` evaluator environment by adding a repo-root `pyproject.toml` that
pins `mpmath` and `python-flint` as runtime dependencies, then re-run the
Evaluator on the existing `Candidates/V48.lean` to convert sprint 053's
gate-3 FAIL into a PASS row in `Refinement_Log/log.jsonl`.

The fixed final theorem statement
`theorem korenblum_constant_search : ValidKorenblumBound c_value` is
unchanged. `c_value` remains `1777/5000 = 3554/10000` (V48 ties V0/V47).

## Why

### Sprint 053's failure was purely a Python-dependency issue, not a Lean issue

Per `Refinement_Log/verdict_sprint_053.md` (lines 18–43):

- Gate 1 (`lake build ProofRefinement.Korenblum.Candidates.V48`): PASS.
- Gate 2 (`grep -n 'sorry' Candidates/V48.lean`): PASS.
- Gate 3 (canonical evaluator): FAIL with
  `oracle function rigorous_scalar.certify_eq15_at_seed not found:
  No module named 'mpmath'`.

Per the Experience.md sprint_053 entry (lines 670–767), the wrapper itself
behaves correctly when `mpmath` and `flint` are available:

- `certify_eq15(3554, 10000, dps=50, n_trunc=200)` → `True`
  (certified `total ≈ 1.02225` against the strict `1 + 10^(-30)` margin).
- `certify_eq15(3565, 10000, dps=50, n_trunc=200)` → `False`
  (certified `total ≈ 0.99649`, matching sprint 050's `gap = -3.598e-04`
  beyond Wang's `(15)` crossover, the load-bearing falsifiability check
  from sprint 050's pinpoint).

The Lean side (`Candidates/V48.lean`), the `lemma.toml` `[[oracles]]`
registration, the `[seed_axioms].allowed` extension, and the
`certify_eq15_at_seed` shim are all correct and unchanged. The only fix
needed is to add `mpmath` and `python-flint` to the canonical evaluator
environment so `import mpmath` (line 7 of `rigorous_scalar.py`) and
`from flint import arb, ctx, fmpq` (line 8) succeed.

### Why route (1) is the correct fix, not route (2)

The verdict's "Notes" block names two candidate routes:

1. Add `mpmath` (and `python-flint` for the verified-interval `arb`
   machinery) to the project's `pyproject.toml` or `uv.lock` so the
   canonical evaluator environment has them.
2. Refactor `rigorous_scalar.py` to defer the `import mpmath` inside
   `certify_eq15_at_seed` (and similar functions).

Route (2) is rejected because:

- The deferred-import pattern only delays the same `ModuleNotFoundError`
  to call time. When the Evaluator's `run_oracle_checks` (line 421 of
  `Evaluator.py`) invokes `certify_eq15_at_seed()`, the function body
  immediately calls `certify_eq15(3554, 10000, dps=50, n_trunc=200)`,
  whose body uses `mp.mp.dps`, `mp.mpf`, `mp.quad`, etc. (per
  `rigorous_scalar.py`). Deferring the top-level `import mpmath` would
  push the failure from gate-3-import-time to gate-3-call-time without
  fixing it. The same applies to `flint.arb` / `flint.ctx` / `flint.fmpq`
  used by `_arb_exact`, `_arb_box`, `_arb_floor_to_int`, and the
  `lambda_upper_on_interval` / `_inv_lambda_lower_from_k_upper_fraction`
  pipeline that `certify_eq15` composes.
- The user's framing in the harness directive ("The right fix is probably
  (1) — adding the dependencies cleanly — because (2) just defers the same
  failure to call time. But if the canonical environment is `uv run` with
  no project deps file, decide accordingly.") confirms route (1) is the
  intent.
- Route (2) would also produce a misleading import surface: every future
  `Numerical_Library` consumer would have to remember to defer imports of
  any heavy dependency, instead of declaring those dependencies once at
  the project boundary. Route (1) is the standard Python-project pattern.

### Why a repo-root `pyproject.toml` rather than PEP-723 inline metadata or wrapper-script `--with` flags

There is currently **no Python dependency-management file anywhere** in
the repo. `find korenblum -maxdepth 5 -name pyproject.toml -o
-name uv.lock -o -name 'requirements*.txt'` returns empty. The
`korenblum_eval_candidate.sh` wrapper invokes `uv run "$WORKSPACE_DIR/Evaluator.py"`
with the working directory set to `REPO_ROOT` (line 19 of the wrapper),
which means a `pyproject.toml` at `REPO_ROOT` is exactly where `uv run`
will look for the project's declared dependencies. Three alternatives
were considered and rejected:

- **PEP-723 inline metadata in `Evaluator.py`** (a `# /// script` block at
  the top declaring `dependencies = ["mpmath", "python-flint"]`). This
  works for the canonical `uv run Evaluator.py …` invocation, but it
  buries the project's runtime dependency surface inside an executable
  script and makes it invisible to standard tooling (`pip install -e .`,
  `uv pip compile`, IDE auto-completion, dependency scanners). Future
  oracle wrappers (e.g. `wang_k_kernel.py` from `proposal_002`'s
  oracle-approval branch) would need parallel inline-metadata blocks if
  consumed independently. The repo-root `pyproject.toml` is the
  standard-tooling target.
- **`--with mpmath --with python-flint` flags in
  `korenblum_eval_candidate.sh`.** The TEMPLATE.md gate-2 acceptance line
  literally says
  `env UV_CACHE_DIR=… uv run ProofRefinement/Korenblum/Evaluator.py
  --file …` — bypassing the wrapper entirely. Pinning deps only in the
  wrapper would leave the canonical TEMPLATE invocation broken. The
  `pyproject.toml` route fixes both the wrapper and the canonical bare
  invocation in one edit.
- **A `requirements.txt` instead of `pyproject.toml`.** `uv` honors
  `pyproject.toml`'s `[project].dependencies` natively without an extra
  install step; `requirements.txt` requires `uv pip install -r` first.
  Pyproject is the lower-friction choice.

### This sprint does not change `c_value`, but it is the prerequisite for the c-push cascade the bulletin prescribes

V48 will tie V47 at `1777/5000 = 0.3554`, so by the bulletin's first
2026-05-02 directive ("tying V0 is no longer a win") this is not a
score-improving sprint. However:

- Sprint 053's contract was explicitly authorised by the bulletin's
  second 2026-05-02 directive (lines 263–272) as a no-c-push
  trust-surface-reshaping sprint, with the explicit clarification (line
  295) that "A sprint that pushes `c` from `0.3556` to `0.3558` with a
  comfortable margin and an axiom-set that does not grow is *a successful
  sprint*". Sprint 053 was that prescribed sprint; sprint 054 is its
  *completion*. Without sprint 054, sprint 053 cannot land its trust-surface
  change in the canonical evaluator environment, and the per-sprint c-push
  cascade (`3554 → 3558 → 3560 → 3562`) the bulletin prescribes for sprints
  055+ cannot start.
- Per the bulletin's incrementalism principle (lines 288–298), the
  closest verified step from the current state is *not* a c-push: it is
  the dependency-pinning fix that converts sprint 053's gate-1/gate-2
  PASS + gate-3 FAIL into a clean four-gate PASS in the canonical
  environment. Sprint 055 (next) re-points the oracle's shim at
  `c = 1779/5000` and ships V49 for the first c-push above the seed.

### Three candidate sprint shapes considered (planner ultrathink)

**C1 (chosen) — Add a repo-root `pyproject.toml` declaring `mpmath` and
`python-flint` as project dependencies; re-run the Evaluator on the
existing `Candidates/V48.lean`.**

- *Strongest objection*: this is a pure dependency-management edit — no
  Lean theorem, no analytical novelty, just a `pyproject.toml` two
  directories above the workspace. The bulletin's first directive
  ("structural novelty is now valued only insofar as it advances a
  `c_value > 0.3554`") would seem to forbid such sprints. *Resolution*:
  the bulletin's second directive (lines 219–313) explicitly authorises
  the oracle-channel sprint family, and sprint 053's `BLOCKED_NEEDS_HUMAN`
  diagnosis explicitly names the two candidate fix routes — both of
  which are pure plumbing. Sprint 053's substantive intent (oracle
  channel works in the canonical environment) is not realised until
  sprint 054 lands. The bulletin's "incrementalism is the point of this
  harness, not a fallback" (line 288) directly applies: this is the
  closest verified step from the current state.
- *Why this is novel*: it is the workspace's first declared Python
  dependency surface; the first repo-level `pyproject.toml`; and the
  precondition for *every* future `[[oracles]]` registration that
  consumes `mpmath`/`flint` (which is essentially all of them — the
  existing `wang_box_math.py`, `wang_k_kernel.py`, `numerical_audit.py`
  also depend on `mpmath`). Without sprint 054, the `[[oracles]]`
  channel is documentary infrastructure that nothing can actually
  invoke; with it, the channel is fully wired and the c-push cascade
  is one shim-add per sprint.

**C2 — Combine the dependency fix with the first c-push (target
`c = 1779/5000` directly).**

- *Strongest objection*: stacks two structural changes (repo-level
  `pyproject.toml` AND a candidate at a new `c`) into one Generator
  session. If the dependency-pin has any wiring issue (`uv run` finds
  the project file but can't resolve `python-flint` on the Python
  3.14 wheel surface, or the `[tool.uv] package = false` flag is
  misformulated, or `uv` 0.9.10 has a parsing quirk), the c-pushing
  candidate fails for the wrong reason and the post-mortem cannot
  cleanly separate "the canonical evaluator environment can now invoke
  the oracle" from "the inequality holds at `c = 0.3558`". The bulletin
  (line 298) explicitly says "aim for the closest verified step, not
  the limit"; here the closest verified step from the current state
  (sprint 053 gate-3 FAIL) is the dependency fix, not a c-push. Demoted.

**C3 — File a third proposal (e.g. `proposal_003`) requesting human
sign-off on adding a Python dependency manifest to the repo.**

- *Strongest objection*: the agent brief's §"Numerical tooling" makes
  the oracle path explicitly **pre-approved without proposals** as long
  as the contract names the wrapper function (already done in sprint
  053), the `lemma.toml` entry (already shipped in sprint 053), and
  the Lean axiom (already declared in V48). Adding the project's
  Python runtime dependencies — `mpmath` and `python-flint` — is the
  *implementation* of that pre-approved channel, not a trust-base
  expansion. The Lean cone is unchanged; the seed axioms set is
  unchanged; the workspace import policy is unchanged; only the runtime
  Python interpreter's available imports change. A `Proposals/` filing
  here is exactly the failure mode of sprints 048–052 the bulletin's
  second directive criticises. Demoted.

**Verdict.** C1 is the literal completion of sprint 053's
substantive intent; the only edit is one new `pyproject.toml` at
the repo root. Zero Lean edits. Zero `lemma.toml` edits. Zero
`Numerical_Library/` edits. Zero `Candidates/` edits. The
re-run of V48 with `mpmath` and `python-flint` available
converts sprint 053's gate-3 FAIL into a PASS row in
`Refinement_Log/log.jsonl` with the substantive trust-surface
change (`hEq15_oracle_certified_3554` instead of
`hEq15_seed_3554`) finally landing.

## Concrete edits expected

1. **`korenblum/pyproject.toml`** (NEW FILE): create a
   minimal "non-package" project pinning the Python deps:

   ```toml
   [project]
   name = "korenblum-eval"
   version = "0.0.0"
   description = "Runtime Python deps for the Korenblum Evaluator and Numerical_Library oracles"
   requires-python = ">=3.11"
   dependencies = [
       "mpmath>=1.4",
       "python-flint>=0.8",
   ]

   [tool.uv]
   package = false
   ```

   Notes:
   - `name = "korenblum-eval"` is arbitrary; `uv` does not publish or
     install this project, only its dependencies, because of
     `[tool.uv] package = false`.
   - `requires-python = ">=3.11"` matches the `cpython-3.14.0` interpreter
     `uv` selected in the existing `.uv-cache/interpreter-v4` (verified
     by `env UV_CACHE_DIR=korenblum/.uv-cache uv run python3
     -c 'import sys; print(sys.version)'` in the planner's pre-sprint
     reconnaissance).
   - `mpmath>=1.4` matches the `1.4.1` resolved by
     `uv run --with mpmath --with python-flint` in the planner's
     pre-sprint check.
   - `python-flint>=0.8` matches the `0.8.0` resolved similarly. The
     PyPI package name is `python-flint`; the import name is `flint`
     (per `rigorous_scalar.py:8`).
   - **No `[build-system]` block.** Without one, and combined with
     `[tool.uv] package = false`, `uv run` treats the project as a
     dependency-only manifest and does *not* attempt to build or
     install `korenblum-eval` itself.

2. **`korenblum/.gitignore`**: append two lines if not
   already present:

   ```
   .venv/
   uv.lock
   ```

   The first because `uv run` with a `pyproject.toml` will create a
   `.venv` at the workspace root (or wherever `UV_PROJECT_ENVIRONMENT`
   resolves to). The second because `uv.lock` is a transient lock file
   `uv` may create at the repo root if it decides to lock the
   resolution; we do not want it tracked unless the workspace adopts a
   `uv.lock`-pinned policy in a future sprint.

   Diff against the current `.gitignore`:

   ```
   .lake/
   build/
   __pycache__/
   *.olean
   *.ilean
   *.hash
   *.trace
   .DS_Store
   +.venv/
   +uv.lock
   ```

3. **NO edits to any other file.** Specifically:
   - `Candidates/V48.lean` is NOT edited (sprint 053 already landed it).
   - `Numerical_Library/rigorous_scalar.py` is NOT edited (the
     unconditional `import mpmath as mp` and `from flint import …`
     stay; route (2) is rejected).
   - `lemma.toml` is NOT edited (sprint 053's `[[oracles]]` block and
     `[seed_axioms].allowed` entry are correct).
   - `Evaluator.py` is NOT edited.
   - `scripts/korenblum_eval_candidate.sh` is NOT edited.
   - `Proof/`, `KorenblumPaper/`, all earlier `Candidates/V<n>.lean`,
     and `lakefile.toml` are NOT edited.
   - No new `Proposals/` file.
   - No new `Scratch/` file.

4. **`ProofRefinement/Korenblum/Bulletin.md`**: append exactly one line
   to the `## Recent events` block:

   ```text
   sprint_054 PASS: pinned mpmath + python-flint in repo-root pyproject.toml — V48 re-evaluated to PASS in canonical `uv run` environment with axioms_used switched from {seed} ∪ {hEq15_seed_3554} to {seed} ∪ {hEq15_oracle_certified_3554} and oracle_checks recording successful invocation of `rigorous_scalar.certify_eq15_at_seed` (oracle_bound=1, declared=1); first repo-level Python dependency manifest, completes sprint 053's oracle-channel substantive intent in the canonical evaluator environment; sprint 055 ships V49 at c=1779/5000 by adding a `certify_eq15_at_3558` shim and a sibling `[[oracles]]` row, no further Lean infrastructure change needed
   ```

   on success, or the matching `BLOCKED` line on failure. Do not reflow.

5. **`ProofRefinement/Korenblum/Experience.md`**: append a new dated
   entry `### 2026-05-02 sprint_054` summarising:
   - what sprint 053 left undone (gate-3 FAIL on `ModuleNotFoundError:
     mpmath` in the canonical `uv run` environment, with verdict at
     `Refinement_Log/verdict_sprint_053.md`);
   - which fix route was chosen and why (route (1) — repo-root
     `pyproject.toml` — over route (2) deferred-imports, and over
     PEP-723 inline metadata / wrapper `--with` flags);
   - the exact `pyproject.toml` shape shipped (non-package,
     `[tool.uv] package = false`, two pinned deps);
   - the explicit `axioms_used` change for V48 in the re-run vs sprint
     053's failed run (axiom set is identical to the design — what
     changed is the gate-3 result going from FAIL to PASS);
   - the next-sprint plan (sprint 055 → V49 at `c = 1779/5000` by
     adding a sibling `certify_eq15_at_3558` shim to
     `rigorous_scalar.py` plus a sibling `[[oracles]]` row in
     `lemma.toml`; the Lean infrastructure (V49 ≈ V48 with axiom
     name + `c_value` swapped) is essentially identical);
   - that this sprint does NOT touch `proposal_001` or `proposal_002`
     (their `Status:` fields remain `pending`); the dependency-pin is
     structurally orthogonal to both proposals.

## Acceptance criteria

1. The new `korenblum/pyproject.toml` exists and is well
   formed (`uv` 0.9.10 parses it without error). Verify:
   ```bash
   env UV_CACHE_DIR=korenblum/.uv-cache \
     uv tree --project korenblum 2>&1 | head -20
   ```
   should list `mpmath` and `python-flint` (with their resolved
   versions) under the `korenblum-eval` root, and exit with code 0.

2. The canonical bare `uv run` invocation succeeds at importing both
   deps:
   ```bash
   cd korenblum && \
   env UV_CACHE_DIR=korenblum/.uv-cache \
     uv run python3 -c "import mpmath, flint; print('mpmath', mpmath.__version__, '/ flint', flint.__version__)"
   ```
   prints e.g. `mpmath 1.4.1 / flint 0.8.0` and exits with code 0.

3. `lake build ProofRefinement.Korenblum.Candidates.V48` succeeds
   (already passes per sprint 053's gate-1; this re-confirms no
   Lean regression from the new `pyproject.toml`).

4. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V48.lean` succeeds (exit code
   0). The terminal output must include the lines:
   - `oracle audit:  PASS`
   - `  PASS  hEq15_oracle_certified_3554: oracle=1 declared=1`

5. The newest `Refinement_Log/log.jsonl` row records all of:
   - `pass: true`
   - `score: "1777/5000"` (V48 ties V47/V0 at the seed; the trust-surface
     change is the deliverable, not the score)
   - `axioms_used` array contains an entry whose `name` is
     `ProofRefinement.Korenblum.Candidates.V48.hEq15_oracle_certified_3554`
     and whose `kind` is `seed` (per sprint 053's Experience entry, the
     axiom shows up as `kind: seed` because it is listed in
     `[seed_axioms].allowed`; the oracle invocation is recorded
     separately in `oracle_checks`)
   - `axioms_used` does NOT contain any entry whose `name` ends in
     `hEq15_seed_3554`
   - `oracle_checks` is a non-empty array with exactly one element
     whose `axiom: "hEq15_oracle_certified_3554"`,
     `bound_field: "eq15_lower_bound"`,
     `oracle_bound: "1"`,
     `declared: "1"`,
     `ok: true`

   Greppable check:
   ```bash
   tail -1 korenblum/ProofRefinement/Korenblum/Refinement_Log/log.jsonl \
     | python3 -c "
   import json, sys
   r = json.loads(sys.stdin.read())
   assert r['pass'] is True
   assert r['score'] == '1777/5000'
   names = [a['name'] for a in r['axioms_used']]
   assert any(n.endswith('hEq15_oracle_certified_3554') for n in names), names
   assert not any(n.endswith('hEq15_seed_3554') for n in names), names
   assert r['oracle_checks'] and r['oracle_checks'][0]['ok'] is True, r['oracle_checks']
   print('OK')
   "
   ```
   prints `OK`.

6. Falsifiability sanity check (must still hold after the dep pin):
   ```bash
   cd korenblum && \
   env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 -c "
   from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import certify_eq15
   assert certify_eq15(3554, 10000, dps=50, n_trunc=200) is True
   assert certify_eq15(3565, 10000, dps=50, n_trunc=200) is False
   print('OK')
   "
   ```
   prints `OK` and exits 0. This re-confirms sprint 053's
   wrapper-correctness check (`Experience.md` lines 745–767) now
   succeeds in the canonical environment, not just in a hand-pulled
   `pip install mpmath python-flint` shell.

7. `git diff --stat` shows changes only to:
   - `pyproject.toml` (new file at repo root, ≤ 15 lines),
   - `.gitignore` (≤ 2 appended lines),
   - `ProofRefinement/Korenblum/Bulletin.md` (one appended line),
   - `ProofRefinement/Korenblum/Experience.md` (one appended entry),
   - `ProofRefinement/Korenblum/Refinement_Log/log.jsonl` (one
     appended row from the Evaluator run),
   - `ProofRefinement/Korenblum/Refinement_Log/verdict_sprint_054.md`
     (new file from the Evaluator agent).

   Greppable check:
   ```bash
   git -C korenblum status --short \
     | awk '{print $2}' \
     | sort > /tmp/sprint_054_changed.txt
   diff /tmp/sprint_054_changed.txt - <<'EOF'
   .gitignore
   ProofRefinement/Korenblum/Bulletin.md
   ProofRefinement/Korenblum/Experience.md
   ProofRefinement/Korenblum/Refinement_Log/log.jsonl
   ProofRefinement/Korenblum/Refinement_Log/verdict_sprint_054.md
   pyproject.toml
   EOF
   ```
   exits 0 (modulo any `.uv-cache/` or `.venv/` paths, which are
   gitignored after edit 2).

   No edits to `Numerical_Library/`, `Candidates/`, `Proof/`,
   `KorenblumPaper/`, `lemma.toml`, `lakefile.toml`, `Evaluator.py`,
   any prior `Sprint_Contracts/sprint_<NNN>.md`, or any prior
   `Proposals/proposal_<NNN>.md`.

## Out of scope

- Push `c_value` above `1777/5000`. That is sprint 055's job. This
  sprint deliberately ties V48 to verify the oracle channel's
  canonical-environment plumbing in isolation. Sprint 055 will add
  `certify_eq15_at_3558` shim + sibling `[[oracles]]` row + V49 in
  a separate Generator session; the work cleanly separates.
- Modify `proposal_001` or `proposal_002`'s `Status:` fields. Both
  remain `pending`. The dependency-pin is structurally orthogonal
  to both proposals (it is plumbing for the pre-approved oracle
  channel, not a trust-base expansion).
- Add any new Lean theorem to `Reduction.lean`, `Main.lean`, or
  any module under `KorenblumPaper/`. Zero Lean edits.
- Refactor `rigorous_scalar.py` to defer imports (route 2 is
  explicitly rejected; do not touch the file). Future
  `Numerical_Library/` modules (e.g. `wang_k_kernel.py`'s
  oracle-approval branch from `proposal_002`) should rely on the
  same project-level dependency declaration; do not introduce
  per-module deferred-import patterns.
- Add `[build-system]` block to `pyproject.toml` or otherwise make
  `korenblum-eval` an installable package. The `[tool.uv] package
  = false` flag is the load-bearing piece that keeps this a
  dependency-only manifest.
- Pin `mpmath` / `python-flint` to specific patch versions in the
  initial sprint. Use `>=` lower-bound constraints matching the
  resolutions verified by the planner's pre-sprint
  `uv run --with` check (`mpmath>=1.4`, `python-flint>=0.8`); a
  future sprint can introduce a `uv.lock` if reproducibility
  becomes a concern.
- Generate a `uv.lock` file. Add `uv.lock` to `.gitignore` and
  let `uv run` resolve at invocation time; the resolution surface
  for two well-known packages on a stable Python is small enough
  that lock-file overhead is not yet warranted.
- File a third proposal. We are at 2/3 pending and the
  `[[oracles]]` channel is pre-approved per `AGENT_BRIEF.md`
  §"Numerical tooling".

## Time budget

≤ 25 minutes runtime. Breakdown:

- ~5 min: write the `pyproject.toml` file (≤ 15 lines) and append
  the two `.gitignore` lines.
- ~5 min: smoke-test that `uv run python3 -c "import mpmath,
  flint; …"` succeeds from `REPO_ROOT` (acceptance criterion 2).
- ~5 min: re-run `lake build ProofRefinement.Korenblum.Candidates.V48`
  (acceptance criterion 3) and the canonical Evaluator
  (acceptance criterion 4). The Evaluator's wall-clock at the
  seed is ~38–45s per the sprint 053 Experience entry (line 760);
  the actual run is dominated by the `certify_eq15` wrapper.
- ~5 min: append the `Bulletin.md` line and the `Experience.md`
  entry; verify `git diff --stat` matches acceptance criterion 7.
- ~5 min: buffer for an unexpected resolution issue (e.g.
  `python-flint` wheel unavailable on the resolved Python; in
  that case, fall back to relaxing `python-flint>=0.8` to
  `python-flint>=0.7` or pinning to the known-good `0.8.0`, then
  re-verify acceptance criterion 2). The planner's pre-sprint
  reconnaissance confirmed `mpmath==1.4.1` and `python-flint==0.8.0`
  resolve cleanly via `uv run --with` on the existing
  `.uv-cache/interpreter-v4` (cpython 3.14.0), so this buffer is
  unlikely to be needed.

## Stop conditions

- Acceptance criteria 1–7 all met: `STATUS=READY_FOR_EVALUATION`.
- `uv run python3 -c "import mpmath, flint; …"` still fails
  after `pyproject.toml` is in place (criterion 2 fails):
  `STATUS=BLOCKED` with note "uv 0.9.10 not picking up
  `[project].dependencies` from repo-root `pyproject.toml`;
  investigate `tool.uv.package`, `tool.uv.workspace`, or whether
  the `cd REPO_ROOT` step in the wrapper is being bypassed".
  Do **not** ship the change with a non-functional dep pin —
  that would leave V48 in the same gate-3-FAIL state and waste
  a Generator session.
- The canonical Evaluator invocation now succeeds at the import
  layer but the oracle invocation itself fails for a *different*
  reason (e.g. `flint` ABI mismatch with the installed FLINT C
  library, or `mpmath` precision-context interaction with the
  global `mp.mp.pretty = False` setting in `rigorous_scalar.py`):
  `STATUS=BLOCKED` with diagnostic and recommended next move
  (typically: pin `python-flint` to a specific version known to
  match the system FLINT, or switch the canonical environment to
  a `uv` Python that ships with a bundled FLINT). This is a
  low-probability failure mode given the planner's pre-sprint
  smoke-test of the exact wrapper signature already passing in
  a `uv run --with` shell.
- The wrapper's falsifiability check fails (`certify_eq15(3565,
  10000, …)` returns True after the dep pin, criterion 6 fails):
  `STATUS=BLOCKED` — this is a critical rigour failure indicating
  the new resolved `python-flint` version has changed `arb`
  semantics in a way that breaks sprint 053's verified-interval
  bounds. Pin `python-flint` to the exact `0.8.0` the planner
  verified with `uv run --with python-flint==0.8.0` in
  pre-sprint reconnaissance and re-test.
- A repo-level `pyproject.toml` interferes with the existing
  Lake / Lean toolchain (e.g. `lake build` now fails because
  some Lake helper script picks up `pyproject.toml` and assumes
  this is a Python project): `STATUS=BLOCKED_NEEDS_HUMAN` with
  diagnostic. Lake reads `lakefile.toml`, not `pyproject.toml`,
  so this is highly unlikely; flagged as a known but extremely
  low-probability failure mode.

## Notes for the Generator

- **The fix is `pyproject.toml`, not `requirements.txt`, not PEP-723,
  not deferred imports.** The contract's "Why" section enumerates the
  alternatives and rejects them. If you find yourself reaching for any
  of those, re-read the rationale.

- **Do not edit `rigorous_scalar.py`.** The unconditional
  `import mpmath as mp` and `from flint import arb, ctx, fmpq` at
  module top are correct — they declare the module's actual
  dependencies. Route (2) (defer imports) is rejected because it just
  pushes the same `ModuleNotFoundError` from import time to call time.

- **`[tool.uv] package = false` is load-bearing.** Without it, `uv
  run` will try to install the local project (`korenblum-eval`) into
  the venv before resolving deps. Since there is no `[build-system]`
  block, the install would fail and the `uv run` invocation would
  error out. The `package = false` flag tells `uv` to treat the
  manifest as deps-only.

- **`requires-python = ">=3.11"` matches the resolved interpreter.**
  The existing `.uv-cache/interpreter-v4/cpython-3.14.0` was chosen by
  `uv` previously; any constraint `>=3.11` will accept it. Do not
  pin to `==3.14` — that would over-constrain and break if
  `.uv-cache/` is later regenerated against a different bundled
  interpreter.

- **`python-flint` is the PyPI package; `flint` is the import name.**
  This is a common gotcha. The `dependencies` array in
  `pyproject.toml` uses `python-flint`; `rigorous_scalar.py:8`
  imports `from flint import arb, ctx, fmpq`. If you write
  `dependencies = ["flint"]` you will get a different (unrelated)
  package and the import will fail.

- **The Evaluator re-runs the oracle on every candidate compile.**
  Per `Evaluator.py:run_oracle_checks` (line 393), the oracle audit
  iterates `used_axioms` against `config.oracles` and invokes the
  registered function fresh each time. There is no caching at the
  Evaluator layer. So acceptance criterion 4's ~38–45s wall-clock is
  the actual cost; budget accordingly.

- **The `axioms_used` entry will be reported as `kind: seed`, not
  `kind: oracle`.** Per the sprint 053 Experience entry (lines
  680–700) and the schema-deviation note (lines 720–740), the
  axiom is listed in BOTH `[seed_axioms].allowed` AND `[[oracles]]`.
  The Evaluator's audit reports it as `kind: seed` (because it
  matches `seed_axioms` first in the audit pass at line 350) but
  STILL invokes the oracle from `run_oracle_checks` (line 393)
  independently. Acceptance criterion 5 asks for the axiom to
  appear in `axioms_used` (with whatever `kind` the audit assigns)
  AND for `oracle_checks` to record a successful invocation. Both
  must hold.

- **No `Scratch/` script needed.** This sprint is pure
  dependency-management plumbing; the analytical kernel is
  unchanged from sprint 053 and was numerically verified there.
  Skipping `Scratch/` for this sprint does not violate the
  bulletin's "use Scratch — it has been empty for 46 sprints"
  directive (line 92) because that directive is about *sprints
  proposing numerical headroom for a c-push*; sprint 054 proposes
  no numerical headroom.

- **Sprint 055 will be the first c-push.** Per the Experience.md
  sprint_053 entry (lines 700–725), sprint 055's plan is
  essentially:
  1. Add `certify_eq15_at_3558()` shim to `rigorous_scalar.py`
     calling `certify_eq15(1779, 5000, dps=50, n_trunc=200)`.
  2. Add a sibling `[[oracles]]` row in `lemma.toml` with
     `axiom = "hEq15_oracle_certified_3558"`,
     `bound_field = "eq15_lower_bound"`,
     `oracle_fn = "rigorous_scalar.certify_eq15_at_3558"`.
  3. Add `"hEq15_oracle_certified_3558"` to
     `[seed_axioms].allowed`.
  4. Ship `Candidates/V49.lean` at `c_value := 1779 / 5000` with
     the new axiom name.
  None of that is in scope for sprint 054. Stay focused.
