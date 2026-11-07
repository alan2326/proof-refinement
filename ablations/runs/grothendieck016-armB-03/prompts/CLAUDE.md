# Grothendieck Project

Lean 4 formalization of the Grothendieck inequality.

## Agent Worktree Setup

Before spawning agents with `isolation: "worktree"`:
1. Push `main` to remote: `git push origin main` — worktrees branch from `origin/main`.
2. Ensure `.claude/settings.local.json` has all needed permissions (see `docs/AGENT_TEST_PLAN.md`).
3. First Lean LSP call in a new worktree may fail (cold-start) — agents should retry once.

## Build

```bash
lake build LeanProof
```

Lean 4 v4.28.0 with Mathlib v4.28.0.

## Blueprint

```bash
./blueprint/build.sh          # build HTML
./blueprint/build.sh serve    # build + serve at http://0.0.0.0:8000
./blueprint/build.sh check    # verify \lean{} declarations (after lake build)
```

Source: `blueprint/src/content.tex`. See `LeanProof/.context/BLUEPRINT_GUIDE.md` for details.
