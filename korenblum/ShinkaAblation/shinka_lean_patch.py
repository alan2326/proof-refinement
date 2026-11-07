"""
Tiny runtime patch over ShinkaEvolve.

Two changes are required for this ablation:

1. Register `claude-opus-4-7` so `get_client_llm` finds a client. Without
   this entry the call raises `ValueError: Model claude-opus-4-7 not
   supported`. Same per-Mtok prices as `claude-opus-4-6`.

2. Mark `claude-opus-4-7` as a reasoning Claude so extended-thinking
   plumbing in `shinka.llm.query` engages the same way it does for
   earlier reasoners.

That is the entire patch. Everything else about Lean is handled by:

* using `language="cpp"` in `EvolutionConfig` — the only consequences are
  (a) Markdown fences in prompts say ` ```cpp ` and (b) the internal
  staging file lives at `gen_<N>/main.cpp`. The `task_sys_msg` makes the
  Lean-4 context unambiguous, and the evaluator copies the file content
  to a `.lean` path before running `lake build`.

* writing the seed `initial.lean` with `-- EVOLVE-BLOCK-START` markers.
  Shinka's marker regex `(?:#|//|)?\\s*EVOLVE-BLOCK-START` matches the
  trailing portion of `-- EVOLVE-BLOCK-START` (the `(?:...)?` is allowed
  to consume zero characters and the regex is unanchored), so the
  mutable-region detector still finds the block.

Import this module at the very top of `run_evo.py`, before any other
shinka import.
"""

from __future__ import annotations

from shinka.llm.models import pricing as _pricing

_OPUS_4_7 = "claude-opus-4-7"

if _OPUS_4_7 not in _pricing.CLAUDE_MODELS:
    _pricing.CLAUDE_MODELS[_OPUS_4_7] = {
        "input_price": 15.0 / 1_000_000,
        "output_price": 75.0 / 1_000_000,
    }

if _OPUS_4_7 not in _pricing.REASONING_CLAUDE_MODELS:
    _pricing.REASONING_CLAUDE_MODELS.append(_OPUS_4_7)


# ---------------------------------------------------------------------------
# Patch shinka.llm.query.sample_model_kwargs to use the new adaptive-thinking
# API for claude-opus-4-7. The current code (query.py:165-168) builds:
#     kwargs["thinking"] = {"type": "enabled", "budget_tokens": N}
# which Opus 4.7 rejects with `400 invalid_request_error:
# "thinking.type.enabled" is not supported for this model. Use
# "thinking.type.adaptive" and "output_config.effort" to control thinking
# behavior.` We translate to the new shape after the original function
# returns. The budget→effort mapping mirrors shinka's THINKING_TOKENS table.
# ---------------------------------------------------------------------------
import shinka.llm.query as _shinka_query

_orig_sample_model_kwargs = _shinka_query.sample_model_kwargs


def _budget_to_effort(budget_tokens: int) -> str:
    if budget_tokens <= 2048:
        return "low"
    if budget_tokens <= 4096:
        return "medium"
    return "high"


def _patched_sample_model_kwargs(*args, **kwargs):
    kw = _orig_sample_model_kwargs(*args, **kwargs)
    if kw.get("model_name") == _OPUS_4_7 and isinstance(kw.get("thinking"), dict):
        thinking = kw["thinking"]
        if thinking.get("type") == "enabled":
            effort = _budget_to_effort(int(thinking.get("budget_tokens", 4096)))
            # Both `thinking={type: adaptive}` and `output_config={effort: ...}`
            # are too new for anthropic-python 0.73.0's SDK validator. Route
            # them via `extra_body`, the SDK escape hatch for unrecognized
            # request-body fields.
            kw.pop("thinking", None)
            existing_extra = kw.get("extra_body") or {}
            if not isinstance(existing_extra, dict):
                existing_extra = {}
            existing_extra.setdefault("thinking", {"type": "adaptive"})
            existing_extra.setdefault("output_config", {"effort": effort})
            kw["extra_body"] = existing_extra
    return kw


_shinka_query.sample_model_kwargs = _patched_sample_model_kwargs

# `shinka.llm.llm` does `from .query import sample_model_kwargs` at module
# load time, so it captures a stale reference to the original function
# when it is first imported. Patching `_shinka_query.sample_model_kwargs`
# alone is not enough — we have to overwrite the imported name in
# `shinka.llm.llm` as well. (We avoid importing `shinka.llm.llm` here
# until after `_shinka_query.sample_model_kwargs` has been replaced, so
# any further `from .query import sample_model_kwargs` would also pick
# up the patched version, but that's defense-in-depth.)
import shinka.llm.llm as _shinka_llm
_shinka_llm.sample_model_kwargs = _patched_sample_model_kwargs
