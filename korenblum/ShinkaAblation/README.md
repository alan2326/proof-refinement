# Korenblum × ShinkaEvolve Ablation

Black-box evolutionary baseline against the agent-driven proof search at
`ProofRefinement/Korenblum/`.

## What this is

The agent harness (in `ProofRefinement/Korenblum/`) runs a planner /
generator / evaluator loop with a Lean MCP and bespoke logic. This folder
runs the **same task** through ShinkaEvolve — a vanilla evolutionary code
search — with no tools, no MCP, no harness. The purpose is to ablate the
agent machinery: how much of the score progress comes from the search
algorithm, vs. the proving infrastructure?

To make the comparison clean:

- The trust surface is byte-identical: we invoke
  `korenblum/ProofRefinement/Korenblum/Evaluator.py`
  directly. That means same `lemma.toml`, same compile gate, same axiom
  audit, same oracle audit, same scoring.
- The candidate shape is identical: same sink theorem
  (`korenblum_constant_search`), same constant (`c_value`), same score
  direction (maximize).
- The search space is "any Lean 4 proof of `ValidKorenblumBound c_value`",
  which is the same space the agent harness explores.
- The seed is the published paper-faithful V0 at c = 0.3554.

What's deliberately different:

- **Tool use is disabled** (`enable_tool_use=False`).
- **No leakage from prior runs:** the LLM does not see V1..V68, the
  Bulletin, Experience, Refinement_Log, Sprint_Contracts, Proposals,
  Scratch, the agent harness wiring, or any per-candidate derived
  theorems. It sees the paper, the contract, `lemma.toml`, and the seed.
  See `QUESTIONS.md` for the exact boundary.
- **Latest Opus only:** `claude-opus-4-7`, registered via
  `shinka_lean_patch.py`.

## Layout

```
ShinkaAblation/
├── README.md
├── QUESTIONS.md           # uncertainties — please review and confirm
├── run_evo.py             # ShinkaEvolve config and entrypoint
├── build_task_prompt.py   # builds task_sys_msg from paper + contract + lemma.toml + module index
├── shinka_lean_patch.py   # registers claude-opus-4-7 with shinka's pricing/reasoning tables
├── initial.lean           # V0 seed wrapped in EVOLVE-BLOCK markers
├── evaluate.py            # per-generation: stage candidate → run Evaluator.py → emit metrics.json
└── results/               # populated at runtime; one subdir per generation
```

## Usage

Prereqs:

- `ANTHROPIC_API_KEY` set in the environment.
- The Korenblum Lean project at `korenblum/` builds with
  `lake build`.
- `uv` available on `PATH`.
- ShinkaEvolve installed in the grothendieck venv at
  `grothendieck/.venv/` (it is, as of 2026-05-06).

The Python environments used:

- **`run_evo.py`** runs in the grothendieck venv (it needs
  `shinka`, `anthropic`, `instructor`, etc.).
- **`evaluate.py`** invokes `Evaluator.py` via `uv run` from the
  Korenblum project root, which uses the Korenblum venv (`mpmath`,
  `python-flint`).

Run it:

```bash
cd korenblum/ShinkaAblation
bash launch.sh                # fresh run; clears prior results/, evolution_db.sqlite, evo.log
bash launch.sh --resume       # keep prior state, resume from where it left off
```

The script writes the python PID to `evo.pid`. Tail with:

```bash
tail -f korenblum/ShinkaAblation/evo.log
```

Stop with:

```bash
kill $(cat korenblum/ShinkaAblation/evo.pid)
```

## Inspecting results

- `results/gen_<N>/main.cpp` — the LLM's Lean code for that generation
  (the `.cpp` extension is a ShinkaEvolve quirk; contents are Lean).
- `results/gen_<N>/metrics.json` — `combined_score` (= `c_value` if pass,
  0 if fail), per-stage PASS/FAIL flags, fail reason.
- `results/gen_<N>/evaluator_stdout.txt` — the full
  `Evaluator.py` output for that candidate.
- `evolution_db.sqlite` — ShinkaEvolve's program archive.

## Hyperparameters

Set in `run_evo.py`:

- 200 generations
- 16 parallel jobs (made safe via uuid-suffixed temp wrappers; see
  `evaluate.py`)
- single-model LLM lineup: `claude-opus-4-7` with adaptive thinking
  routed through the SDK's `extra_body` escape hatch (anthropic 0.73
  doesn't recognise `output_config` natively; see `shinka_lean_patch.py`)
- 4 islands, weighted parent selection, λ=10
- patch types: diff/full/cross at 0.6/0.3/0.1
- temperature ∈ {0.5, 1.0} (forced to 1.0 by shinka for reasoning Claude),
  reasoning_efforts=high

Cost: smoke run (6 generations) was $22.63. Linear extrapolation to
200 generations: ~$754, but Option B may push it higher because
candidates can no longer one-shot a registered oracle and the LLM has
to reason longer per turn.

## Open questions

See `QUESTIONS.md` — there are eight items I am not 100% sure about and
would like you to confirm or override before relying on results.
