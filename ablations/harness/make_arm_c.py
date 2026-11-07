#!/usr/bin/env python3
"""Build the Arm C workspace: agentic system KEPT, partial formalization ABLATED.

Start from S0 (so the harness mechanics, Evaluator, scripts, MCP config and the
Wang paper are identical to Arm A), then replace the Lean surface with:

  * `Proof/CandidateContract.lean` -- the function-level Bergman A^2 statement
    of the Korenblum maximum principle, against Mathlib only.
  * `Candidates/V0.lean` -- a single axiom asserting the ANCHOR PARENT bound
    `ValidKorenblumBound (35646/100000)`, i.e. exactly the c Arm A starts from.

and delete every intermediate: KorenblumPaper/*, Proof/Reduction.lean, the
Section2Assumptions bundle, Numerical_Library/, every V1+ candidate, and the
whole sprint history.

Kept deliberately (steelmanning, see design sect. 3.3): the full planner /
generator / evaluator agent system, all tools including MCP, AND Wang (2025)
plus web search.  Ablating only the Lean scaffold -- not the literature -- keeps
this a one-factor experiment.
"""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]  # the ablations/ directory of the release
S0 = ROOT / "workspaces" / "S0_korenblum"
NOPF = ROOT / "korenblum_no_partial_formalization"
DST = ROOT / "workspaces" / "armC"
C_PARENT = "35646 / 100000"          # the anchor parent, == Arm A's start
C_PARENT_FLAT = "35646/100000"

K = DST / "ProofRefinement" / "Korenblum"


def main():
    print(f"[armC] cloning S0 -> {DST}")
    subprocess.run([str(ROOT / "harness" / "make_arm_ws.sh"), "armC"], check=True)

    # ---------------------------------------------------------- 1. contract
    print("[armC] installing Bergman A^2 candidate contract")
    shutil.copy2(NOPF / "ProofRefinement/Korenblum/Proof/CandidateContract.lean",
                 K / "Proof" / "CandidateContract.lean")

    # ------------------------------------------------------------- 2. seed
    print(f"[armC] seeding V0 at the anchor parent c = {C_PARENT_FLAT}")
    (K / "Candidates" / "V0.lean").write_text(f'''-- @parent seed
import ProofRefinement.Korenblum.Proof.CandidateContract

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V0

open ProofRefinement.Korenblum

/-- The previous best certified radius this arm must improve on. -/
def c_value : ℝ := {C_PARENT}

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Seed external input: the previous state of the art for the Korenblum
maximum principle, asserted at the Bergman A² level as a single axiom.

This is the ONLY mathematical input in this arm. There is no Wang Section 2
hypothesis bundle, no equation chain, no coefficient-level intermediate and
no numerical oracle: the trust leaf is the entire conclusion at
`c = {C_PARENT_FLAT}`.

The task is to certify `ValidKorenblumBound c` for some rational
`c > {C_PARENT_FLAT}`.
-/
axiom hKorenblum_prev : ValidKorenblumBound (({C_PARENT} : ℝ))

/-- Seed candidate: the previous best radius is a valid Korenblum bound. -/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  change ValidKorenblumBound (({C_PARENT} : ℝ))
  exact hKorenblum_prev

end ProofRefinement.Korenblum.Candidates.V0
''')

    # --------------------------------------------------- 3. delete the PF
    print("[armC] deleting the partial formalization")
    for rel in ("KorenblumPaper", "KorenblumPaper.lean"):
        p = DST / rel
        if p.exists():
            shutil.rmtree(p) if p.is_dir() else p.unlink()
            print(f"   rm {rel}")
    for rel in ("Proof/Reduction.lean", "Proof/Main.lean", "Proof/ProblemAxioms.lean",
                "Proof/ShinkaTrustedSeed.lean", "Numerical_Library"):
        p = K / rel
        if p.exists():
            shutil.rmtree(p) if p.is_dir() else p.unlink()
            print(f"   rm ProofRefinement/Korenblum/{rel}")
    for p in sorted((K / "Candidates").iterdir()):
        if p.name != "V0.lean":
            shutil.rmtree(p) if p.is_dir() else p.unlink()
    print("   rm all candidates except V0.lean")

    # ---------------------------------------------------- 4. reset history
    print("[armC] resetting sprint history and workspace memory")
    for d, keep in ((K / "Sprint_Contracts", {"TEMPLATE.md"}),
                    (K / "Refinement_Log", set()),
                    (K / "Scratch", {".gitkeep"}),
                    (K / "Proposals", {"README.md", "TEMPLATE.md"})):
        if d.exists():
            for p in sorted(d.iterdir()):
                if p.name not in keep:
                    shutil.rmtree(p) if p.is_dir() else p.unlink()
    (K / "Refinement_Log" / "log.jsonl").write_text("")
    (K / "Bulletin.md").write_text(f"""# Bulletin — Korenblum refinement loop (Arm C: no partial formalization)

Volatile signaling between sprints. The historical record is
`Refinement_Log/log.jsonl`.

Format:

```text
sprint_<NNN> queued: <title> [direction: <axis>]
sprint_<NNN> PASS: <title>
sprint_<NNN> FAIL: <title> [gate: G<id>]
note: <human note>
```

## Current priority

Certify `ValidKorenblumBound c` for some rational `c > {C_PARENT_FLAT}`.

The workspace contains only the Bergman A² definition of the constant
(`Proof/CandidateContract.lean`) and the previous best bound as a single
axiom (`Candidates/V0.lean`). There is no reduction chain, no paper-side
hypothesis bundle and no numerical oracle. Wang (2025) is available at
`ProofRefinement/Korenblum/Wang2025.pdf` (and `.txt`), and web search is
enabled, so the literature is available — only the Lean scaffolding is absent.

Building whatever Lean apparatus the task needs is in scope and expected.
""")
    (K / "Experience.md").write_text(
        "# Experience log — Arm C (no partial formalization)\n\n"
        "_initial state; no entries yet_\n")

    # --------------------------------------------------- 5. build plumbing
    print("[armC] rewiring lakefile / root module / lemma.toml")
    lf = (DST / "lakefile.toml").read_text()
    lf = lf.replace('defaultTargets = ["KorenblumPaper", "ProofRefinement"]',
                    'defaultTargets = ["ProofRefinement"]')
    lf = lf.replace('[[lean_lib]]\nname = "KorenblumPaper"\nroots = ["KorenblumPaper"]\n\n', "")
    (DST / "lakefile.toml").write_text(lf)
    assert "KorenblumPaper" not in lf, "lakefile still references KorenblumPaper"

    (DST / "ProofRefinement.lean").write_text(
        "import ProofRefinement.Korenblum.Candidates.V0\n"
        "import ProofRefinement.Korenblum.Proof.CandidateContract\n")

    (K / "lemma.toml").write_text(f'''name = "Korenblum Constant (Arm C — no partial formalization)"
slug = "korenblum_armC_noPF"
paper_ref = "Korenblum max principle, Bergman A² level; previous best c = {C_PARENT_FLAT}"

sink_theorem = "korenblum_constant_search"
constant_def = "c_value"
score = "c_value"
score_direction = "maximize"

[search_constants]

[import_policy]
# Candidate-side surface. No KorenblumPaper.* — the partial formalization is
# the ablated factor in this arm. New derived-theorem modules the agent builds
# under ProofRefinement.Korenblum.* are admitted via allowed_prefixes.
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[workspace_import_policy]
allowed_exact = []
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[seed_axioms]
allowed = [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
  "Lean.trustCompiler",

  # The previous state of the art, axiomatized at the Bergman A² level.
  # This is the single paper-side leaf in this arm: it asserts the FULL
  # conclusion at c = {C_PARENT_FLAT}, not a sub-claim.
  "hKorenblum_prev",
]

# No oracles at seed. If the agent builds its own numerical sub-claim it must
# register the wrapper here, exactly as the with-PF arm does.
''')

    # ------------------------------------------------------- 6. agent brief
    print("[armC] writing AGENT_BRIEF for the ablated surface")
    (K / "AGENT_BRIEF.md").write_text(f"""# Agent brief — Korenblum, Arm C (partial formalization ablated)

## The contract

`Proof/CandidateContract.lean` defines, against Mathlib only:

* `UnitDisk : Set ℂ` — the open unit disk;
* `bergmanNormSq f = ∫_𝔻 ‖f z‖² dA` — the squared Bergman A² seminorm;
* `ValidKorenblumBound c` — the function-level Korenblum maximum principle:
  for all analytic, A²-integrable `f, g` on `𝔻`, if `‖f z‖ ≤ ‖g z‖` whenever
  `c < ‖z‖ < 1`, then `bergmanNormSq f ≤ bergmanNormSq g`.

There is **no** coefficient-level intermediate, **no** Wang Section 2
hypothesis bundle, **no** equation chain and **no** numerical oracle.

## The task

`Candidates/V0.lean` asserts the previous state of the art as one axiom:

```lean
axiom hKorenblum_prev : ValidKorenblumBound (({C_PARENT} : ℝ))
```

Ship a candidate `Candidates/V<N>.lean` whose `korenblum_constant_search`
proves `ValidKorenblumBound c_value` for some rational
`c_value > {C_PARENT_FLAT}`, and which the evaluator accepts.

## What you have

* Mathlib, in full.
* Wang (2025), at `Wang2025.pdf` and `Wang2025.txt` in this directory.
* Web search and web fetch.
* The Lean LSP and Lean search MCP tools.
* The standard harness: sprint contracts, `Refinement_Log/`, `Bulletin.md`,
  `Experience.md`, `Evaluator.py`, `scripts/`.

Building whatever Lean apparatus you need — including a partial formalization
of your own design — is **in scope and expected**.

## What counts as progress

The evaluator gate is unchanged. A candidate passes only if it compiles,
type-checks, its audited axiom set is a subset of `[seed_axioms].allowed`
(plus registered oracles), there is no `sorryAx`, and `c_value` strictly
improves on the parent.

**A direct-conclusion axiom at a larger `c` is not progress.** Adding, say,

```lean
axiom h : ValidKorenblumBound (36 / 100)
```

and registering it in `[seed_axioms].allowed` would satisfy the letter of the
gate while asserting exactly the thing to be proved. Do not do this. If you
introduce a new axiom it must be a genuine sub-claim — strictly weaker than
the conclusion — and you must say in the sprint contract why it is weaker.

If you introduce a numerical sub-claim, register it as an `[[oracles]]` row
with a wrapper the evaluator can recompute, exactly as the with-PF workspace
does.

## Halting

If you judge the task infeasible within the sprint budget, say so explicitly
in the sprint contract and in `Bulletin.md`, with the specific obstruction.
A precise, well-evidenced negative result is a legitimate outcome and is more
useful than a shortcut.
""")

    for name in ("README.md", "START_HERE.md"):
        p = K / name
        if p.exists():
            p.write_text(f"# Korenblum — Arm C (partial formalization ablated)\n\n"
                         f"See `AGENT_BRIEF.md`. Target: certify\n"
                         f"`ValidKorenblumBound c` for some rational "
                         f"`c > {C_PARENT_FLAT}`.\n")

    # ------------------------------------------- 7. agent defs: strip PF refs
    print("[armC] re-pointing agent definitions at this workspace")
    for p in sorted((DST / ".claude" / "agents").glob("*.md")):
        s = p.read_text()
        s = s.replace((str(ROOT.parent / "korenblum") + "/"), str(DST) + "/")
        p.write_text(s)
    sk = DST / ".claude" / "skills" / "run-next-korenblum-sprint" / "SKILL.md"
    if sk.exists():
        sk.write_text(sk.read_text().replace((str(ROOT.parent / "korenblum") + "/"), str(DST) + "/"))

    print("[armC] done. Now build + gate.")


if __name__ == "__main__":
    sys.exit(main())
