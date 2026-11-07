# Polygon-π run telemetry

Generated 2026-07-27T06:08:43.937691+00:00.


## Hardware and toolchain

| | |
|---|---|
| CPU | Intel(R) Xeon(R) Platinum 8352Y CPU @ 2.20GHz |
| Logical CPUs | 128 (2 thread/core, 2 socket) |
| CPU max MHz | 3400.0000 |
| Memory | 503Gi |
| Kernel | `Linux neptune 5.15.0-185-generic #195-Ubuntu SMP Fri Jun 19 17:11:50 UTC 2026 x86_64 x86_64 x86_64 GNU/Linux` |
| Lean | Lean (version 4.28.0, x86_64-unknown-linux-gnu, commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b, Release) |
| Lake | Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0) |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Python / uv | Python 3.13.9 / uv 0.9.10 |

## Per-sprint

| sprint | wall clock | LLM calls | main | subagent | output tok | cache read tok | cost USD | outcome |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| sprint_001 | 19.4 min | 132 | 12 | 120 | 90,585 | 11,933,673 | $10.76 | PASS |
| sprint_002 | 19.9 min | 129 | 8 | 121 | 87,079 | 10,669,819 | $10.19 | PASS |
| sprint_003 | 20.2 min | 132 | 8 | 124 | 88,823 | 11,034,491 | $10.70 | PASS |
| sprint_004 | 25.4 min | 115 | 11 | 104 | 109,037 | 12,585,341 | $13.41 | PASS |
| sprint_005 | 38.6 min | 194 | 7 | 187 | 136,812 | 21,170,478 | $18.96 | PASS |

## Run totals (sprint windows only)

| metric | value |
|---|---:|
| sprints | 5 |
| LLM calls | 702 |
| — main loop | 46 |
| — subagents | 656 |
| input tokens | 17,820 |
| output tokens | 512,336 |
| cache-write tokens (1h) | 100,129 |
| cache-write tokens (5m) | 3,167,935 |
| cache-read tokens | 67,393,802 |
| total tokens | 71,192,022 |
| **cost** | **$64.01** |

By model:

| model | calls | output tok | cost USD |
|---|---:|---:|---:|
| `claude-opus-5` | 527 | 475,237 | $58.94 |
| `claude-sonnet-5` | 175 | 37,099 | $5.07 |

## Lean compute

| candidate | pass | score | compile s | user CPU s | sys CPU s | max RSS MB |
|---|---|---|---:|---:|---:|---:|
| `V0` | True | 1 | 2.626 | 2.71 | 1.04 | 815 |
| `V1` | True | 71/100 | 2.6 | 2.71 | 1.05 | 815 |
| `V2` | True | 329947/10000000 | 2.483 | 2.58 | 1.05 | 809 |
| `V3` | True | 98297/10000000 | 2.613 | 2.64 | 1.07 | 812 |
| `V4` | True | 9816589/1000000000 | 2.634 | 2.77 | 1.08 | 812 |
| `V5` | True | 9816533/1000000000 | 2.6 | 2.68 | 1.02 | 815 |

Total Lean compile wall clock 15.6 s; CPU 22.4 s.

## Session totals, including the harness build-out

1188 LLM calls, 1,543,177 output tokens, **$168.79** total. This covers everything in the project's transcripts — designing and building the harness as well as running sprints — so it is the number to quote for total project cost, not per-sprint cost.

## Method and caveats

- Token counts and models are read from Claude Code's own per-turn transcripts, so LLM call counts and token totals are exact rather than estimated.
- Dollar figures are computed from published per-MTok list prices and are therefore an accurate reconstruction of list cost, not a billing record. Any negotiated rate, subscription bundling, or free-tier allowance is not reflected.
- Cache writes are priced by TTL (2x input at 1h, 1.25x at 5m) using the split the transcript reports; cache reads at 0.1x input.
- Sprint attribution is by wall-clock window from `results/sprint_markers.jsonl`. Anything running concurrently in the same project would land in the same window.
- Lean compile CPU and RSS come from `/usr/bin/time -v` around `lake build`, recorded per evaluation in `log.jsonl`.
