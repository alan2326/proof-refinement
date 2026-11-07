# Proof Refinement: Design and Implementation Plan

## 0. What this document is

A design for the `ProofRefinement/` workspace that lets an LLM agent
iteratively improve formal proofs of named lemmas (5.4 today; 5.3, 4.3, …
later) with as little structural overhead as possible. The mental model
comes from
[assets/pdf_text/proof_refinement_graphs.tex](../assets/pdf_text/proof_refinement_graphs.tex)
— a proof is a certified DAG, a refinement is a graph edit, the score is the
certificate at the sink. We adopt the *flavor* of that formalism, not the
letter.

Companion to (and supersedes) the lemma-specific
[PROOF_REFINEMENT_PLAN.md](PROOF_REFINEMENT_PLAN.md), which covers a one-off
seed migration; this document covers the framework.

## 1. Goals

1. **Thin.** The implementation should be a small layer of glue around
   `lake` + Python oracles. Adding a new lemma is a directory copy plus a
   short config file.
2. **Faithful in flavor.** The vocabulary "node / certificate / sink / value
   / refinement / propagation / log" is preserved and visible to the agent
   in tool output.
3. **Maximum agent freedom.** The agent edits Lean files. Nothing else.
   It declares no schemas, no node types, no edit types, no transfer
   maps, no monotonicity assertions. The framework infers what it needs
   from the file.
4. **Multi-lemma scalable.** One generic evaluator, per-lemma config,
   shared numerical-library and infrastructure code.
5. **Reproducible audit trail.** Every successful evaluation appends a
   structured record so a reviewer can answer (after the fact) the three
   questions the TeX section 7 asks: what idea changed, which formal nodes
   were affected, and how did the certificate change.

## 2. Non-goals (i.e., things we deliberately do not formalize)

These come straight from the TeX, in the order it introduces them. Each
one is tempting to encode and would add cost without commensurate value.

| Concept in TeX                                | Status here                          |
|---|---|
| Theorem family $\mathcal S_v:\Theta_v\to\Prop$  | Not represented as data. Lives in the Lean type of the axiom/theorem. |
| Strength preorder $\preceq_v$                 | Implicit. Score expression is `ℝ`, smaller is better. |
| Certificate $\theta_v$                        | Just a `def *_val : ℝ := <rat>`. Type is always `ℝ` for now. |
| Local proof term $\pi_v$                      | Whatever Lean accepts in the file. Not extracted. |
| Transfer map $F_v$                            | Whatever the Lean expression at the dependent node says. We never extract it as a function symbol. |
| Monotonicity of $F_v$                         | Not checked or asserted anywhere. The framework does not need it; recompilation discharges everything. |
| Forward cone $\Up_G(A)$                       | We do not compute it. Lean rebuilds whatever it must. |
| Interface refinement, $\rho:I\to V(G')$, adapters | Replaced by: each lemma directory pins one *sink theorem signature* in `lemma.toml`. That is the entire interface. |
| Primitive edit catalog (strengthen/generalize/insert/delete/rewire/split/merge/reparameterize) | Not enforced. The agent writes whatever Lean it wants. The catalog stays in the paper as exposition. |
| Refinement trajectory $G_0\to\ldots\to G_N$ as a typed object | Approximated by an append-only log of evaluation records. |

The single hard constraint we keep from the formalism is **local
checkability**: every node in the new graph has a Lean-checked proof from
its predecessors. This is exactly what `lake env lean` plus the axiom audit
already enforce.

## 3. Mental model: how the paper maps to this codebase

| Paper concept                       | Implementation                                         |
|---|---|
| Node $v$                            | A Lean declaration: `def`, `theorem`, or `axiom` in the candidate file (and its transitive imports). |
| Edge $u\to v$                       | A use of `u` in the proof term of `v`. Recovered for axioms via `#print axioms <sink>`; for everything else, implicit in `lake build`. |
| Certificate $\theta_v$              | The rational on the RHS of `def *_val : ℝ := <rat>`. |
| Statement family $\mathcal S_v$     | The Lean type of the declaration (a `Prop`). Parameter symbols inside the type, e.g. `M_val`, are the certificate. |
| Local proof $\pi_v$                 | The proof script following `:=` (or the axiom declaration if unproven). |
| Sink $t$                            | A named theorem in the candidate file (one per lemma directory; pinned in `lemma.toml`). |
| Sink's certificate $\theta_t$       | The score expression evaluated over the candidate's `*_val` defs (e.g. `Cr_val`). |
| Refinement $\mathcal E$             | The act of producing a new candidate file. No structure imposed on the act. |
| Improving refinement                | Score went down. Detected post hoc by comparing log records. |
| Refinement log entry $\mathfrak r$  | One JSON record appended to `Refinement_Log/log.jsonl`. |
| Affected cone $\Up_G(A)$            | Implicit: whatever `lake` recompiles, plus whatever `#print axioms` newly reports. We don't compute it; we observe it. |
| Soundness proposition (Prop. 1)     | Discharged by `lake env lean`. |
| Monotone propagation (Prop. 2)      | Not asserted. The score computation is symbolic over the candidate's own `*_val`s, so improving an input rational mechanically improves a monotone output (e.g. `Cr_val`); if the agent wires a non-monotone expression, that is its choice. |

The compact restatement: **a candidate file is one proof graph; running the
evaluator on it checks soundness and reports the sink certificate; the
log preserves the trajectory.**

## 4. Architecture

### 4.1 Directory layout

```
ProofRefinement/
├── README.md                          # one-page overview pointing here
├── proof_refinement/                  # the framework (Python package)
│   ├── __init__.py
│   ├── evaluator.py                   # generic; replaces per-lemma Evaluator.py
│   ├── lemma_config.py                # loads lemma.toml
│   ├── parser.py                      # extracts def *_val, axioms, sink
│   ├── compile.py                     # lake env lean wrapper
│   ├── axiom_audit.py                 # #print axioms + categorize
│   ├── oracle.py                      # OracleResult, registry merging
│   ├── score.py                       # symbolic Fraction eval
│   └── log.py                         # append-only JSONL writer
├── Lemma54/
│   ├── lemma.toml                     # per-lemma config (NEW; see §4.2)
│   ├── README.md                      # lemma-specific notes for the agent
│   ├── Experience.md                  # agent's running notebook
│   ├── Candidates/
│   │   ├── V0.lean                    # seed
│   │   ├── V1.lean                    # …
│   │   └── ...
│   ├── Proof/                         # non-evolved Lean infrastructure
│   │   ├── SearchConfig.lean          # locked parameters
│   │   └── Lib/                       # shared lemmas across candidates
│   ├── Numerical_Library/             # Python oracles for THIS lemma
│   │   ├── __init__.py                # registry: name → callable
│   │   └── *.py
│   ├── Refinement_Log/
│   │   └── log.jsonl                  # one JSON record per evaluation
│   └── Scratch/                       # agent's ad-hoc files (untracked or .gitignored)
├── Lemma53/                           # same shape (added later)
├── Lemma43/                           # same shape (added later)
└── docs/                              # cross-cutting notes (move PROOF_REFINEMENT_PLAN.md here?)
```

What changes from today: a generic `proof_refinement/` package replaces
the in-place `Lemma54/Evaluator.py`; `lemma.toml` makes per-lemma config
explicit; `Refinement_Log/` is new. Everything inside `Candidates/`,
`Proof/`, `Numerical_Library/`, `Experience.md`, `Scratch/` keeps the
shape it has today.

### 4.2 `lemma.toml`

The single piece of metadata that the framework needs about a lemma.
Everything else is inferred from the candidate file or from the
`Numerical_Library/` package.

```toml
# ProofRefinement/Lemma54/lemma.toml

# Display + lookup.
name        = "Lemma 5.4"
slug        = "lemma_5_4"
paper_ref   = "Braverman et al. (2011), §5"

# The sink theorem the candidate must declare. The evaluator searches the
# candidate file for `theorem <sink_theorem>` (and confirms it appears).
# It also runs `#print axioms <sink_namespace>.<sink_theorem>`.
sink_theorem  = "lemma_5_4_search"
# Optional: a regex the sink's Lean type must match, to detect drift.
# Empty = no signature check.
sink_signature_regex = ""

# Score expression: a Python arithmetic expression over the candidate's
# `def *_val` rationals (and any constants from search_constants below).
# Evaluated as Fractions. Smaller is better.
score      = "Cr_val"
direction  = "min"

# Constants the candidate may reference but the framework can resolve to
# rationals (e.g. SearchConfig.r is locked at 23/25).
[search_constants]
"SearchConfig.r"   = "23/25"
"SearchConfig.eta" = "1/100"

# Seed axioms — present in V0, allowed in derived candidates without
# oracle backing. Each is a fully-qualified Lean name. Listing them here
# (instead of hardcoding in Evaluator.py) makes adding a new lemma a
# config-only change.
[seed_axioms]
allowed = [
  "Braverman.PaperV0.h_M_bound",
  "Braverman.PaperV0.h_R_bound",
  "Braverman.PaperV0.paper_taylor_argument",
  # Standard Lean.
  "propext",
  "Classical.choice",
  "Quot.sound",
]

# Oracle axioms — short Lean name → spec. The oracle function is resolved
# from this lemma's Numerical_Library (loaded as a Python module).
[[oracles]]
axiom = "h_M_bound"               # short name, namespace-stripped
bound_field = "M_val"             # the def the bound corresponds to
oracle_fn = "compute_M_bound"     # resolved as Numerical_Library.compute_M_bound
expected_pattern = '''closedBall.*R_val.*S.*‖H0.*≤ M_val'''  # regex on Lean type

[[oracles]]
axiom = "h_R_bound"
bound_field = "R_val"
oracle_fn = "compute_R_bound"
expected_pattern = '''disk.*1 \+ SearchConfig\.r.*F_inv.*‖F_inv.*‖ ≤ R_val'''
```

Why TOML and not Python: agents (and humans) edit it without risk of
arbitrary-code execution; it's diff-friendly; `tomllib` is in the stdlib.

What is *not* in `lemma.toml`: the dependency graph between nodes, the
strength order, transfer maps, monotonicity flags, edit catalog
restrictions. We do not need them.

### 4.3 The candidate file: convention over configuration

A candidate is a single Lean file. The agent has full freedom inside it,
subject to two conventions:

1. It declares a theorem with the `sink_theorem` name from `lemma.toml`.
2. It declares `def *_val : ℝ := <rat>` for any rational referenced in
   `score` or in an oracle's `bound_field`.

Beyond that: import whatever, restructure proofs however, split or merge
declarations, add or remove axioms (subject to audit), use any Mathlib
tactic, define helper lemmas inline, change the namespace, add comments
or remove them. The only thing the framework will reject is something
that fails one of the audit gates in §4.4.

The agent need not (and should not be expected to) declare what kind of
edit it just performed. There is no "this is a strengthen/insert/rewire"
metadata. The post-hoc log captures everything we care about.

### 4.4 Evaluator pipeline (unchanged in shape from today's Evaluator.py)

```
PARSE      ← reads candidate.lean, extracts def *_val rationals + axiom decls + namespace
COMPILE    ← lake env lean candidate.lean
AXIOM      ← #print axioms <namespace>.<sink_theorem>; categorize each:
                seed   → in lemma.toml seed_axioms.allowed
                oracle → registered in lemma.toml [[oracles]]
                else   → FAIL (especially sorryAx)
ORACLE     ← for each oracle axiom:
              run Numerical_Library.<oracle_fn>(...) → OracleResult.bound (Fraction)
              check candidate.<bound_field> ≥ that bound
              also: re-check expected_pattern matches the Lean axiom type
SCORE      ← evaluate `score` expression symbolically over def *_val rationals
LOG        ← append a record to Refinement_Log/log.jsonl
```

If any of {COMPILE, AXIOM, ORACLE} fails, the evaluation status is `fail`
and the score record carries a reason. Failed evaluations *are* logged —
that is part of the audit trail.

### 4.5 Refinement log format

`Refinement_Log/log.jsonl` is one JSON record per line. Append-only,
never rewritten in place. A record has roughly:

```json
{
  "timestamp": "2026-04-27T14:32:11Z",
  "candidate": "Candidates/V3.lean",
  "candidate_sha256": "abc123...",
  "parent": "Candidates/V2.lean",
  "parent_sha256": "def456...",
  "status": "ok",
  "score": {"numer": 14, "denom": 1, "approx": 14.0},
  "score_field": "Cr_val",
  "axioms_used": [
    {"name": "Braverman.PaperV0.h_M_bound", "kind": "oracle", "bound_field": "M_val", "declared": "5", "oracle_bound": "5"},
    {"name": "Braverman.PaperV0.h_R_bound", "kind": "oracle", "bound_field": "R_val", "declared": "6/5", "oracle_bound": "6/5"},
    {"name": "Braverman.PaperV0.paper_taylor_argument", "kind": "seed"}
  ],
  "def_vals": {"M_val": "5", "R_val": "6/5", "Cr_val": "...", "eps_val": "..."},
  "wall_seconds": {"compile": 42.1, "axiom_audit": 8.0, "oracle": 1.3}
}
```

Concretely useful fields and *why*:

* `parent`: the agent's edit basis. Determined by either (a) a `-- @parent
  Candidates/Vk.lean` comment line in the new file (one line of opt-in
  metadata) or (b) the immediate predecessor in modification time within
  `Candidates/`. If absent, `null`. This is the bare-minimum analogue of
  the paper's "edit applied to which graph".
* `score`: as Fraction (numer/denom) plus float for human reading. Lets
  later tooling sort, plot, and compute the `val(G_N) ≤ val(G_0)` check
  trivially.
* `axioms_used`: this is the readable approximation of `\Up_G(A)`'s most
  interesting subset — every axiom node still load-bearing in the proof.
  Shrinking `seed` count over runs is a visible measure of progress, even
  when the score is unchanged.
* `def_vals`: rational snapshots so later analysis can attribute score
  changes to specific certificates.

Things deliberately *not* in the log: a list of edit operations performed
("insert", "rewire", …). The agent is not asked to know.

### 4.6 What the agent sees

The agent operates against a small CLI:

```bash
# Evaluate a candidate.
uv run -m proof_refinement.evaluator --lemma Lemma54 --file Candidates/V3.lean

# Helpful supporting commands.
uv run -m proof_refinement.evaluator --lemma Lemma54 --list           # list candidates + scores
uv run -m proof_refinement.evaluator --lemma Lemma54 --best           # print best candidate path + score
uv run -m proof_refinement.evaluator --lemma Lemma54 --history        # tail of log.jsonl, formatted
```

`README.md` and `Experience.md` are the natural-language interface to the
agent — they tell it what the lemma is, what's been tried, and what
oracles exist. This is no different from today; we're not asking the agent
to learn a framework.

## 5. How the formalism shows through (without forcing the agent to think about it)

The agent does not author DAGs, certificates, transfer maps, or interface
maps. But the abstraction is still visible in the artifacts the framework
produces:

* The candidate file *is* a proof graph: its `def *_val`s are
  certificates, its `axiom`s and proven declarations are nodes, the
  sink theorem is the sink.
* The evaluator's output explicitly names "node / certificate / oracle /
  sink / score" in human-readable lines. `Cr_val: 14.0` is the value of
  the proof graph.
* The log is the refinement trajectory. Diffing two candidate files plus
  reading the two log entries gives the reviewer the same content as a
  paper-style refinement step record.
* When the agent splits an axiom into provable parts, the seed-axiom
  count in the log goes down. When it tightens an oracle bound, the
  bound_field rational in the log goes down. Both are observable in
  the trajectory.
* When the score drops, that is exactly an "improving refinement" in
  the paper's sense.

So the formalism is the *interpretation* of the artifacts, not a layer
the agent has to navigate.

## 6. What changes vs. today

The table below is exhaustive at the file level. Minimal new code, no
breaking changes to the V0 candidate.

| Path | Today | Action |
|---|---|---|
| `ProofRefinement/Lemma54/Evaluator.py` | per-lemma evaluator, hard-codes seed axioms + oracle registry | Delete after migration. |
| `ProofRefinement/proof_refinement/` | does not exist | **NEW.** Generic evaluator package per §4.1. |
| `ProofRefinement/Lemma54/lemma.toml` | does not exist | **NEW.** Inlines the constants currently hardcoded in Evaluator.py. |
| `ProofRefinement/Lemma54/Refinement_Log/log.jsonl` | does not exist | **NEW.** Created on first run. |
| `ProofRefinement/Lemma54/Candidates/V0.lean` | exists, three custom axioms | Unchanged. |
| `ProofRefinement/Lemma54/Numerical_Library/{m_bound,r_bound}.py` | stubs raising NotImplementedError | Unchanged. (Implementing them is downstream work; orthogonal to this plan.) |
| `ProofRefinement/Lemma54/Proof/` | locked SearchConfig + Lib | Unchanged. |
| `ProofRefinement/Lemma54/{README,Experience}.md` | exist | README gets a paragraph pointing at the new CLI. |
| `ProofRefinement/README.md` | does not exist | **NEW.** One page: how to add a new lemma, how to run the evaluator, where to read the design. |
| `docs/PROOF_REFINEMENT_PLAN.md` | exists, lemma-54 specific migration | Keep; reference from this doc. |
| `docs/PROOF_REFINEMENT_DESIGN.md` | this document | **NEW.** |

## 7. Implementation plan

Three small, independently mergeable steps.

### Step 1 — Extract the evaluator into a package, behavior-preserving

1. Create `ProofRefinement/proof_refinement/` with the modules from §4.1.
2. Move all logic from `Lemma54/Evaluator.py` into the package. Replace
   the hard-coded `SEED_AXIOMS` / `ORACLE_REGISTRY` with reads from
   `lemma.toml`. The generic CLI is `python -m proof_refinement.evaluator
   --lemma Lemma54 --file Candidates/V0.lean`.
3. Write `ProofRefinement/Lemma54/lemma.toml` matching the current
   hardcoded values exactly (so V0.lean evaluates identically before and
   after). Today's `ORACLE_REGISTRY` is empty in the active set, so this
   is a one-liner table pointing the (still-stub) M and R oracles by name.
4. Replace `Lemma54/Evaluator.py` with a thin `__main__` shim that calls
   the package, *or* delete it and update `Lemma54/README.md` to use the
   new CLI. Recommendation: delete it.
5. Sanity check: rerun the V0 evaluation, confirm `PASS` and identical
   score. (Today the active oracle set is empty so this is mostly a
   parser/compile/seed-audit smoke test.)

Acceptance: the V0 evaluation produces the same human-readable output
modulo the new "lemma: Lemma 5.4" header and the new log line.

### Step 2 — Add the refinement log

1. Create `proof_refinement/log.py` with an `append(record: dict, path:
   Path)` function that writes one JSON line, fsync'd.
2. Have `evaluator.py` build the record (§4.5) and append on every run,
   regardless of pass/fail. On fail, include a `failure` field with the
   short reason and the last 2 KB of compile/audit output.
3. Add `--list`, `--best`, `--history` subcommands that read
   `Refinement_Log/log.jsonl` (and fall back to scanning `Candidates/` if
   the log is empty or missing — robust to fresh checkouts).
4. Recognize an optional `-- @parent Candidates/Vk.lean` comment line in
   the candidate header. Use it for the `parent` field in the log; if
   missing, default to the most recent prior candidate by mtime, or
   `null` if there is none.

Acceptance: running the evaluator twice on V0 produces two log lines;
`--history` formats them readably; `--best` returns V0's score.

### Step 3 — Generalize: ship a second lemma directory

Once the first new lemma is on the agenda (likely Lemma 5.3 or 4.3):

1. Add `ProofRefinement/Lemma53/` with `lemma.toml`, an empty
   `Numerical_Library/`, an initial `Candidates/V0.lean`, a `Proof/Lib/`
   (sharing across lemmas via standard `LeanProof.*` imports), an empty
   `Refinement_Log/`, an `Experience.md`.
2. Confirm the generic evaluator runs unchanged (`--lemma Lemma53`).
3. Move any cross-lemma utility code into `proof_refinement/` (e.g. the
   `Fraction` symbolic eval, oracle-result type, log writer).

If shared Lean infrastructure (e.g. helpers used by both Lemma 5.3 and
5.4) needs a home, put it under `ProofRefinement/Shared/Lib/` rather
than promoting to `LeanProof/`. That keeps refinement-side refactors out
of the proven-good `LeanProof/` tree.

Acceptance: a new lemma directory is a copy + edit of `Lemma54/`'s
config and a new V0 candidate, with no Python changes.

### Step 4 (optional, deferred) — Cross-lemma dependency tracking

If Lemma 5.4 begins importing a node from Lemma 5.3's candidates (rather
than from `LeanProof/`), the framework needs to know which version of
the dependency was used. The minimal extension: `lemma.toml` gains an
optional `[[dependencies]]` table:

```toml
[[dependencies]]
lemma = "Lemma53"
candidate = "Candidates/V7.lean"   # pinned, or "best" to resolve dynamically
```

The evaluator records the pinned version in the log. We do not need this
yet; explicitly defer.

## 8. Worked example: what a refinement step looks like

Before:

```
Candidates/V0.lean
  def M_val : ℝ := 5
  def R_val : ℝ := 6/5
  axiom h_M_bound       : ...
  axiom h_R_bound       : ...
  axiom paper_taylor_argument : ...
  theorem lemma_5_4_search := paper_taylor_argument M_val R_val ...
  -- score: Cr_val = 8·25·1.2/(0.08)² · (1 + 16·1.2/0.08³) ≈ 1.4 × 10⁹
```

The agent edits, producing `Candidates/V1.lean`. It tightens `M_val` to
`9/2` (using a sharper Arb run) and splits `paper_taylor_argument` into
`cauchy_F_inv_first_deriv` (now proven from `Proof/Lib/Lemma54_Cauchy`)
plus a smaller residual axiom `paper_taylor_remainder_argument`.

After running the evaluator:

```
[1/5] PARSE       V1.lean
        namespace:    Braverman.PaperV0
        def *_val:    {M_val, R_val, eps_val, Cr_val}   # 4
        axioms:       {h_M_bound, h_R_bound, paper_taylor_remainder_argument}   # 3, was 3
        sink:         lemma_5_4_search                  # found
[2/5] COMPILE     ok in 41.9s
[3/5] AXIOM AUDIT lemma_5_4_search depends on:
        seed   Braverman.PaperV0.h_M_bound
        seed   Braverman.PaperV0.h_R_bound
        seed   Braverman.PaperV0.paper_taylor_remainder_argument   # NEW seed name; agent declared it
        ...    standard Lean axioms
        UNREG  paper_taylor_remainder_argument is not in seed_axioms.allowed
        FAIL: unregistered axiom (the agent must list it in lemma.toml or
              break it down further).
```

The framework politely fails because the agent introduced a new axiom
without registering it. The agent then either (i) extends `lemma.toml`'s
seed list with `paper_taylor_remainder_argument` (small, paper-cited;
listed alongside the others), or (ii) eliminates that axiom by writing
a Lean proof. Either way, the next run logs the new shape:

```json
{
  "candidate": "Candidates/V1.lean",
  "parent":    "Candidates/V0.lean",
  "status":    "ok",
  "score":     {"approx": 1.07e9, "numer": ..., "denom": ...},
  "axioms_used": [
    {"name": "...h_M_bound",                       "kind": "oracle", "bound_field": "M_val", "declared": "9/2", "oracle_bound": "9/2"},
    {"name": "...h_R_bound",                       "kind": "oracle"},
    {"name": "...paper_taylor_remainder_argument", "kind": "seed"}
  ],
  "def_vals": {"M_val": "9/2", "R_val": "6/5", "Cr_val": "..."}
}
```

Reading the two log entries plus diffing V0 ↔ V1 gives the reviewer:
the local idea (sharper M, partial Cauchy proof), the formal scope
(M_val tightened, one axiom split), and the certificate change
(`Cr_val` 1.4 × 10⁹ → 1.07 × 10⁹). That is the §7 audit log of the
TeX, produced automatically.

## 9. What the agent is told

A single short paragraph in each lemma's `README.md`:

> Edit any file in `Candidates/`. Run `uv run -m proof_refinement.evaluator
> --lemma Lemma54 --file Candidates/<your_name>.lean`. The evaluator
> compiles your file, audits its axioms, runs the registered numerical
> oracles, and computes `Cr_val`. Smaller `Cr_val` is better. Three
> failure modes: compile error, unregistered axiom, oracle bound below
> declared. To register a new numerical axiom, add a function in
> `Numerical_Library/`, then add an `[[oracles]]` entry to `lemma.toml`.
> To carry over a paper-cited axiom from V0 without an oracle, add its
> fully-qualified name to `lemma.toml`'s `seed_axioms.allowed`. Anything
> else is your call.

That is the entire framework footprint as far as the agent is concerned.

## 10. Risks and judgment calls

1. **`lemma.toml` regex strictness for axiom-type matching.** The
   current `expected_pattern` regexes are tight (and the existing
   plan-doc flags this in its §7.4). Mitigation: log the *full* Lean
   axiom type alongside the regex match result, so when a regex
   mis-matches the agent can see why and adjust either the candidate
   axiom statement or, if necessary, the regex in `lemma.toml`. We
   should accept that `lemma.toml` is a config the agent may edit too.

2. **Score expression expressivity.** Today `Cr_val` is a closed-form
   rational expression. Future lemmas may want `max`, `min`, or
   piecewise scores. The Fraction-based evaluator already supports
   arithmetic; add `max`/`min` if and when needed. Don't pre-build.

3. **Parent-tracking is best-effort.** mtime ordering is fragile under
   git-clone. The opt-in `-- @parent` comment is the reliable form;
   make it the recommendation in the README, treat mtime as a fallback
   only.

4. **What if the agent introduces a non-rational `def *_val`?** E.g.
   `def M_val : ℝ := Real.sqrt 2`. The Fraction evaluator will fail to
   parse it; the score becomes "unevaluable". Treat that as a soft
   warning, not a hard fail — the candidate still compiled and its
   axioms audited; we just can't put a number on it. Log the score as
   `null` and include the raw expression. This preserves agent freedom
   while flagging that the agent has stepped outside the rational regime.

5. **Mathlib drift / nightly bumps.** Out of scope here, but the
   `lake-manifest.json` pin at the project root is what governs
   reproducibility. Note in `proof_refinement/README.md` that the log
   records `wall_seconds` not toolchain hash; if reproducibility across
   toolchain bumps matters, add a `lean_toolchain` field then.

6. **"Unlimited freedom" vs. footguns.** The agent could `import` a file
   that sneaks `sorry` past the audit (e.g. by axiomatizing a wrapper).
   Mitigation: the axiom audit walks transitive dependencies via
   `#print axioms`, which is the correct kernel-checked enumeration.
   `sorryAx` is always a hard fail. We trust the kernel; we do not
   trust agent-written audits.

## 11. Out of scope, but worth naming

* **Automatic forward-cone computation.** Could add `lake graph` parsing
  to compute affected nodes. Useful only if we want to prune
  recompilation or visualize. Not needed for soundness.
* **Multiple sinks.** A lemma could have two terminal theorems with two
  scores. `lemma.toml` could grow `[[scores]]`. Skip until needed.
* **Trajectory visualization.** A small static-site renderer over
  `log.jsonl` (score over time, axiom-count over time) is a one-day
  follow-up; don't build it now.
* **Cross-lemma propagation.** The §7.4 deferred extension. Add when
  the second lemma actually depends on the first.
* **Refinement type catalog (strengthen/insert/…) as enforced metadata.**
  The TeX presents these as exposition-level vocabulary. Do not encode
  them as required fields in the log; the diff between two candidate
  files already exposes the edit kind to a reviewer who cares.

## 12. One-paragraph summary

A `ProofRefinement/<Lemma>/Candidates/Vk.lean` file is a proof graph; a
new `Vk+1.lean` is a refinement. A lightweight Python evaluator
(`proof_refinement/`) compiles the file, audits its axioms against a
per-lemma `lemma.toml`, runs registered numerical oracles, computes the
sink certificate, and appends a JSON record to the lemma's refinement
log. The agent edits Lean freely; the framework is invisible except as
output. The DAG-edit formalism in
[proof_refinement_graphs.tex](../assets/pdf_text/proof_refinement_graphs.tex)
is the interpretation of the artifacts the framework produces — not a
schema the agent has to follow.
