#!/usr/bin/env python3
"""
ShinkaEvolve ablation of the Korenblum agent-driven proof search.

Same trust surface as `ProofRefinement/Korenblum/`: the actual evaluator
(`ProofRefinement/Korenblum/Evaluator.py`) is invoked unchanged for every
candidate, against the same `lemma.toml`. The only thing that differs from
the agent harness is the *search strategy* — instead of planner /
generator / evaluator agents writing one sprint at a time, ShinkaEvolve
runs an evolutionary loop with diff/full LLM patches over a population.

Run:
    cd korenblum/ShinkaAblation
    uv run python run_evo.py

(`uv` is the same environment the Korenblum agent harness uses; ensure
`ANTHROPIC_API_KEY` is set.)
"""

# IMPORTANT: the patch must run BEFORE any other shinka import so that
# CLAUDE_MODELS contains claude-opus-4-7 by the time client.py reads it.
import shinka_lean_patch  # noqa: F401

from pathlib import Path

from shinka.core import EvolutionRunner, EvolutionConfig
from shinka.database import DatabaseConfig
from shinka.launch import LocalJobConfig

from build_task_prompt import build_task_sys_msg


HERE = Path(__file__).resolve().parent

# ---------------------------------------------------------------------------
# Job configuration: per-generation evaluation runs `evaluate.py`, which
# stages the LLM-produced Lean text into the Korenblum project, invokes
# `Evaluator.py`, and returns metrics.json / correct.json.
# ---------------------------------------------------------------------------
job_config = LocalJobConfig(
    eval_program_path=str(HERE / "evaluate.py"),
)

# ---------------------------------------------------------------------------
# Database: weighted parent selection, two islands, modest archive.
# Defaults the user can fiddle with later.
# ---------------------------------------------------------------------------
db_config = DatabaseConfig(
    db_path=str(HERE / "evolution_db.sqlite"),
    num_islands=4,
    archive_size=30,
    elite_selection_ratio=0.3,
    num_archive_inspirations=2,
    num_top_k_inspirations=2,
    migration_interval=10,
    migration_rate=0.1,
    island_elitism=True,
    parent_selection_strategy="weighted",
    parent_selection_lambda=10.0,
)

# ---------------------------------------------------------------------------
# Evolution config.
#
# `language="cpp"` is a deliberate workaround: ShinkaEvolve does not know
# about Lean as a first-class language, but the only side-effects are
# (a) markdown fence labels in prompts (`task_sys_msg` overrides this in
# practice — the LLM is told the language is Lean 4) and (b) the internal
# staging filename being `gen_<N>/main.cpp`. `evaluate.py` reads the file
# as text and re-stages it with a `.lean` suffix.
#
# `enable_tool_use=False` per spec.
# ---------------------------------------------------------------------------
evo_config = EvolutionConfig(
    task_sys_msg=build_task_sys_msg(),
    language="cpp",  # see comment above; do not change without reading shinka_lean_patch.py
    init_program_path=str(HERE / "initial.lean"),
    results_dir=str(HERE / "results"),

    # diff = SEARCH/REPLACE edits on one parent.
    # full = rewrite the entire EVOLVE-BLOCK from one parent.
    # cross = crossover that combines two parents into a child. Cross can
    # produce non-type-checking children when fragments from two distinct
    # Lean proofs are spliced together, but failed children just score 0,
    # and crossover provides useful diversity for escaping local optima.
    patch_types=["diff", "full", "cross"],
    patch_type_probs=[0.6, 0.3, 0.1],

    num_generations=100,
    # Parallel evaluation is safe: `evaluate.py` patches `Evaluator.py` so
    # that its temp wrapper paths are uuid-suffixed, and staged candidate
    # filenames carry a uuid suffix already. Lake itself locks `.lake/build/`
    # internally on shared deps.
    max_parallel_jobs=16,
    max_patch_resamples=3,
    max_patch_attempts=3,

    job_type="local",

    # The latest Opus, exclusively.
    llm_models=["claude-opus-4-7"],
    llm_kwargs=dict(
        temperatures=[0.5, 1.0],
        reasoning_efforts=["medium"],
        max_tokens=32768,
    ),

    # Tool use is disabled, per spec.
    enable_tool_use=False,

    # Meta-recommendation and novelty plumbing — keep cheap.
    meta_rec_interval=10,
    meta_llm_models=["gpt-5-nano"],
    meta_llm_kwargs=dict(temperatures=[0.0], max_tokens=16384),
    embedding_model="text-embedding-3-small",
    code_embed_sim_threshold=0.995,
    novelty_llm_models=["gpt-5-nano"],
    novelty_llm_kwargs=dict(temperatures=[0.0], max_tokens=16384),
    max_novelty_attempts=3,

    # Use claude-opus-4-7 unconditionally (single-model lineup); UCB
    # selection is a no-op here but harmless.
    llm_dynamic_selection="ucb1",
    llm_dynamic_selection_kwargs=dict(exploration_coef=1.0),
)


def main():
    runner = EvolutionRunner(
        evo_config=evo_config,
        job_config=job_config,
        db_config=db_config,
        verbose=True,
    )
    runner.run()


if __name__ == "__main__":
    main()
