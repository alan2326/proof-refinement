"""
Build the task system message for the ShinkaEvolve run.

We assemble it from:

* Wang's paper text (`Wang2025.txt`) — the original mathematical source.
* The exact Lean contract (`Proof/CandidateContract.lean`) and problem
  axioms (`Proof/ProblemAxioms.lean`).
* A *sanitised* view of `lemma.toml` (per QUESTIONS.md §5 Option B): we
  emit only the V0-era seed axioms (`hEq15_seed_3554` plus the standard
  Lean axioms) and zero registered oracles, so the LLM cannot ladder
  onto prior search progress by reading axiom names. The real
  `lemma.toml` on disk (which the evaluator gates against) is unchanged.
* A module index of every file under `Proof/` and `KorenblumPaper/`,
  showing only filenames + leading docstring (the LLM cannot search the
  trust surface interactively because tool-use is disabled).
* The full source of `Numerical_Library/*.py` (per user direction).
  Note: this is a related leak channel — function names like
  `certify_eq15_at_hp_35645` mirror oracle-axiom names registered in
  the real `lemma.toml`. The LLM can guess the axiom name from the
  function name. Documented in QUESTIONS.md.

We deliberately exclude all prior search artefacts — `Candidates/V1+`,
`Bulletin.md`, `Experience.md`, `AGENT_BRIEF.md`, `Refinement_Log/`,
`Sprint_Contracts/`, `Proposals/`, `Scratch/`, the agent harness wiring,
and any per-candidate derived theorem subdirectories.
"""

from __future__ import annotations

import re
from pathlib import Path

KORENBLUM_LEAN_ROOT = Path(__file__).resolve().parents[1]
KORENBLUM_WORKSPACE = KORENBLUM_LEAN_ROOT / "ProofRefinement" / "Korenblum"

PAPER_TEXT_PATH = KORENBLUM_WORKSPACE / "Wang2025.txt"
CONTRACT_PATH = KORENBLUM_WORKSPACE / "Proof" / "CandidateContract.lean"
AXIOMS_PATH = KORENBLUM_WORKSPACE / "Proof" / "ProblemAxioms.lean"
LEMMA_TOML_PATH = KORENBLUM_WORKSPACE / "lemma.toml"
PROOF_DIR = KORENBLUM_WORKSPACE / "Proof"
PAPER_DIR = KORENBLUM_LEAN_ROOT / "KorenblumPaper"
NUMLIB_DIR = KORENBLUM_WORKSPACE / "Numerical_Library"


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _module_index(directory: Path, header: str) -> str:
    """One line per Lean file: filename + first nonblank docstring sentence."""
    lines = [f"### {header}", ""]
    for f in sorted(directory.glob("*.lean")):
        text = _read(f)
        # Pull out the first /-! ... -/ or /-- ... -/ comment.
        m = re.search(r"/-[!-]\s*([^\n]+(?:\n[^\n]+){0,5})\s*-/", text)
        gist = m.group(1).strip().splitlines()[0] if m else "(no docstring)"
        lines.append(f"- `{f.name}` — {gist}")
    lines.append("")
    return "\n".join(lines)


_V0_ERA_SEED_AXIOMS = (
    "Classical.choice",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
    "Quot.sound",
    "propext",
    "hEq15_seed_3554",
)


def _sanitised_lemma_toml() -> str:
    """Return a hand-built V0-era view of `lemma.toml` for the prompt.

    The real file on disk (which `Evaluator.py` actually reads) is
    UNCHANGED: it still contains 13 post-V0 seed axioms, 10 registered
    oracles, and a per-candidate `allowed_exact` import list. We construct
    a minimal V0-era TOML view here so the LLM cannot ladder onto prior
    progress by reading the file. Concretely we drop:

    * every `[[oracles]]` table entry,
    * every post-V0 seed axiom (oracle-certified-at-c values, window-mass
      certifications, and per-V_n hCircleGapInt / hH2 axioms),
    * every per-candidate `Candidates.V<N>` module name in the
      `[import_policy]` `allowed_exact` list,
    * every sprint-commentary block and inline comment that referenced
      prior search progress.

    What stays is exactly what V0 needed: the contract spec, the import
    prefixes for `Mathlib` and `ProofRefinement.Korenblum.Proof`, the
    workspace-side allowance for the three `KorenblumPaper.*` modules
    that V0 transitively imports, and the V0 seed axiom plus the
    standard Lean axioms.
    """
    seed_axioms_lit = ",\n  ".join(f'"{a}"' for a in _V0_ERA_SEED_AXIOMS)
    return f"""\
name = "Korenblum Constant"
slug = "korenblum"
paper_ref = "Wang (2025), Section 2 / equation (15)"

sink_theorem = "korenblum_constant_search"
constant_def = "c_value"
score = "c_value"
score_direction = "maximize"

[search_constants]

[import_policy]
# Candidate-side imports the evaluator allows in your `.lean` file.
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Korenblum.Proof",
  "Mathlib",
]

[workspace_import_policy]
# Imports the evaluator allows in the rest of the workspace.
allowed_exact = [
  "KorenblumPaper.PaperAxioms",
  "KorenblumPaper.PaperEq15",
  "KorenblumPaper.OneModePaperBridge",
]
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[seed_axioms]
# Standard Lean axioms plus the single paper-faithful seed input
# (Wang's equation (15) at c = 0.3554). Any axiom you introduce in your
# candidate must be in this list, otherwise the evaluator rejects the
# candidate at the axiom-audit stage.
allowed = [
  {seed_axioms_lit},
]
"""


# Whitelist of `Numerical_Library` files safe to inline in the prompt.
#
# The agent search produced post-V0 strategy artefacts (box certificates,
# weighted-mass linear bounds, n-window decompositions, certify_eq15_at_*
# function lineups). Those leak the routes the agent search has already
# tried — including ones that succeeded — and pre-bias the LLM's
# diff/full edits towards the same routes. We only inline files that
# contain paper-level arithmetic and no strategy/route or specific
# c-value reference.
#
# Audit (2026-05-07):
#
# * `__init__.py`              — imports strategy fns; STRIP
# * `types.py`                 — BoxCertificate dataclasses; STRIP
# * `wang_box_math.py`         — `mass_from_constant_box`; STRIP
# * `wang_k_kernel.py`         — paper-level Wang K-kernel arithmetic; KEEP
# * `numerical_audit.py`       — parses `branch{N}_box_NNNN` candidates; STRIP
# * `independent_verify.py`    — `_weighted_linear_mass_lower`; STRIP
# * `generate_candidate.py`    — emits versioned `V{n}` namespaces; STRIP
# * `generate_wang_candidate.py` — references `branch2_box_0369`; STRIP
# * `rigorous_scalar.py`       — every `certify_*` function and sprint
#   commentary; STRIP (per QUESTIONS.md §5 Option 2)
NUMLIB_WHITELIST: tuple[str, ...] = (
    "wang_k_kernel.py",
)


def _python_dump(directory: Path, header: str) -> str:
    """Inline whitelisted `.py` files only."""
    out = [f"### {header}", ""]
    for name in NUMLIB_WHITELIST:
        f = directory / name
        if not f.is_file():
            continue
        out.append(f"#### `Numerical_Library/{f.name}`")
        out.append("")
        out.append("```python")
        out.append(_read(f).rstrip())
        out.append("```")
        out.append("")
    return "\n".join(out)


def build_task_sys_msg() -> str:
    paper = _read(PAPER_TEXT_PATH)
    contract = _read(CONTRACT_PATH)
    axioms = _read(AXIOMS_PATH)
    # Sanitised — see `_sanitised_lemma_toml` and QUESTIONS.md §5.
    lemma_toml = _sanitised_lemma_toml()
    proof_index = _module_index(PROOF_DIR, "`ProofRefinement.Korenblum.Proof.*` (workspace trust surface)")
    paper_index = _module_index(PAPER_DIR, "`KorenblumPaper.*` (paper-faithful trust surface)")
    numlib_dump = _python_dump(NUMLIB_DIR, "`Numerical_Library/` — registered oracle code (Python; called by the evaluator only when an oracle axiom is referenced)")

    return f"""You are an expert in complex analysis, Bergman spaces, and Lean 4 formalization. You are participating in a search for a larger lower bound on the Korenblum constant. The current best, due to Wang (2025), is c ≥ 0.3554. Your goal is to push that bound up.

# Task

Improve the candidate Lean file. The improvement objective is to **maximize** `c_value`, defined as:

```lean
def c_value : ℝ := <a closed-form rational>
```

The candidate must close the theorem

```lean
theorem korenblum_constant_search : ProofRefinement.Korenblum.ValidKorenblumBound c_value
```

A candidate is *correct* iff:

1. The Lean file compiles via `lake build`.
2. `korenblum_constant_search` has the exact contract type
   `ValidKorenblumBound c_value`.
3. Every axiom transitively used by the proof is either a standard Lean axiom (`Classical.choice`, `propext`, `Quot.sound`, etc.), a seed axiom listed in `lemma.toml`, or a registered oracle axiom listed in `lemma.toml`.
4. `sorryAx` is a hard fail.
5. All imports are allowed by `lemma.toml`'s `[import_policy]` and `[workspace_import_policy]`.

The score is exactly the rational value of `c_value` (parsed by the evaluator as a `Fraction`). Larger is better.

# Search space

The full search space is **any Lean proof of `ValidKorenblumBound c_value`**, for any rational `c_value` in (0, 1). The published seed route uses Wang's equation (15) at c = 0.3554; that is one path among many. Strengthening the (15)-style scalar inequality, replacing it with a direct disk-vs-annulus argument, or proving the bound via a new analytic strategy are all in scope.

Tool use is disabled — you cannot interactively look up Mathlib lemmas or inspect proof states. You may only modify the candidate file. The system message below contains the trust surface you can rely on; everything else must be derived in Lean from these inputs and Mathlib.

# Wang's paper (verbatim)

```
{paper}
```

# Contract (read-only, defines the theorem you must prove)

```lean
{contract}
```

# Problem axioms (read-only, defines `Section2Assumptions`, `Eq15ScalarBound`, `diskExcess`, `annulusExcess`)

```lean
{axioms}
```

# `lemma.toml` (workspace policy — read carefully; any axiom you introduce must be registered here)

```toml
{lemma_toml}
```

# Module index — workspace trust surface (read-only)

The workspace pre-proves a set of intermediate theorems for you. You can `import` any of these modules (subject to `lemma.toml:[import_policy]`) and use any public theorem they expose. The full source is not in this prompt; rely on the docstring summaries below.

{proof_index}

{paper_index}

# Numerical_Library (oracle support code)

The workspace exposes registered Python oracles in `Numerical_Library/`. The evaluator calls these only when a candidate's proof depends on an oracle axiom registered in `lemma.toml:[[oracles]]`. You may study the source to understand what numerical bounds can be certified; you may also propose a new oracle (but the human registers it via `lemma.toml`, you cannot).

{numlib_dump}

# Hard constraint — no local axiom declarations

The candidate file MUST NOT declare any new `axiom`. The evaluator's
parse-time gate rejects any candidate whose source contains a line
matching `^\\s*axiom\\s+`. Reason: the agent harness's V0 candidate
declared `hEq15_seed_3554` locally, scoped to a re-bindable `c_value`.
That made it possible to "prove" the bound at any `c < 1` simply by
overriding `c_value` and keeping the axiom name. We close that loophole
here.

The only registered external input is

```lean
ProofRefinement.Korenblum.Proof.ShinkaTrustedSeed.hEq15_seed_3554
    : ∀ (K : ℝ → ℝ → ℝ), Eq15ScalarBound K ((3554 : ℝ) / 10000)
```

Note that the type pins `c` to the literal `3554 / 10000`. Even if your
candidate sets `c_value` to a different rational, this axiom still only
gives Wang's `(15)` at `c = 0.3554`.

Therefore, to push `c_value` above `0.3554`, your candidate must:

* prove `Eq15ScalarBound K c_value` at the larger `c_value` from
  Mathlib + `KorenblumPaper.*` + `ProofRefinement.Korenblum.Proof.*`
  (no new axioms), or
* prove `ValidKorenblumBound c_value` directly via a different
  reduction (e.g. via `valid_of_eq2_eq3_eq4_annulus_budget`,
  `valid_of_eq10_subinterval_branch1`, or any other `valid_of_*`
  lemma in `Proof/Reduction.lean`).

If you can prove neither, the highest passing `c_value` you can ship
is `3554 / 10000`. That is fine — many generations will reasonably
re-derive the seed; an honest `0.3554` candidate still scores.

# Strategy notes

- The seed pulls Wang (15) in scalar form via `hEq15_seed_3554`. To increase `c_value` past 0.3554 you must either (a) prove (15) at a larger c using paper-pinned ingredients in `KorenblumPaper.*`, (b) replace the (15)-route with a direct argument bridging `diskExcess` and `annulusExcess`, or (c) introduce a new oracle axiom — but only if you can register it in `lemma.toml` (you cannot; the registration must come from the human). In practice (a) and (b) are the open avenues.

- Every axiom you add MUST already be in `seed_axioms.allowed` or `[[oracles]]`. Adding a new axiom that is not registered is a hard fail. The seed axiom `hEq15_seed_3554` is allowed; you can replace it with a stronger fully-proved theorem at a different c, but you cannot just rename it to `hEq15_seed_<bigger>` and assert without proof — that would be unregistered.

- Mathlib (4.28.0) is available throughout. Use `nlinarith`, `polyrith`, `linear_combination`, `field_simp`, `ring`, `norm_num`, and friends.

- Do not edit the placeholder namespace `ProofRefinement.Korenblum.Candidates.SHINKA_PLACEHOLDER`. The evaluator rewrites it at staging time; if you change the name your file will still compile because the rewrite is regex-based.

# Output discipline

Make targeted improvements that compile end-to-end. A failed compile gets `combined_score = 0`. Prefer small, verified increments over speculative large rewrites.
"""
