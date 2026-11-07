# Refining Lemma 5.4 — agent brief

You are refining a formal Lean 4 proof of Lemma 5.4 of Braverman et al.
(2011). Your job is to produce a sequence of candidate files that prove
the same theorem with a *smaller* error constant `Cr_val`. Smaller score
wins. That's the entire game.

> **2026-05-03 PATCH — read [PATCH_NOTES.md](PATCH_NOTES.md) before
> doing anything that touches `H_η`, `Φ`, the joint oracles, or any
> `Cr_phi_*` formula.** Every existing oracle in
> [`Numerical_Library/`](Numerical_Library/) (V9–V26's backing) is
> non-rigorous because it imports the K_max-truncated
> `eval_H_eta_at_acb`. The rigorous truncation-free oracles + cached
> outputs + per-candidate audit table live in `PATCH_NOTES.md`.
> The Evaluator now enforces this with **G7** (`TRUNCATION_REGRESSION`
> + `AUDIT_FLOOR_VIOLATION`) — write candidates that respect the
> patched audit floor or G7 will fail them. The lowest rigorously
> achievable `Cr_val` today is **V11 ≈ 0.33**, not V26's `1/268000`.

## Current state of the world (read this first)

Since the original brief was written, the production proof has moved
substantially. Two facts you must know:

1. **Lemma 5.4 is fully proved**, modulo a small named family of trusted
   analytic axioms. The proof lives in
   `Proof/Lib/Lemma54_Paper_Main.lean:lemma_5_4_paper` and is built from
   12 IFT-supplied axioms about the implicit-function-theorem family
   `F_inv_paper` (declared in `Proof/Lib/Lemma54_Paper.lean`). The Cauchy
   estimates, identity (75), `∂²ₚ F_inv` bound, and Taylor-in-p step are
   all proved in the `Lemma54_Paper_{Cauchy,Identity,Pderiv,Pderiv_Single,
   Taylor,Main}.lean` chain.

2. **The production effective companion lives at the proof graph layer**:
   `ProofGraph/Effective/Lemma54Effective.lean` instantiates
   `lemma_5_4_paper_on_domain` at the concrete tuple
   `(eta_val=1/100, r_val=23/25, M_val=4000)` over the explicit Step-1/
   Step-2 rectangle `Ω(δ_val=57/1000, B_val=293/250)`. Its sink theorem
   `Braverman.Effective.lemma_5_4_effective` has axiom set: 3 lean
   primitives + 12 trusted analytic + `h_M_oracle` +
   `h_oracle_domain_contains_image`. This is what the audit certifies.

The candidate-iteration workspace here (`ProofRefinement/Lemma54/`)
mirrors the production proof in `Candidates/V0.lean` and exists for
the agent to **explore departures from production** — different
formulations, tighter bounds, axiom eliminations.

## The loop (unchanged)

```bash
# Read the seed.
cat ProofRefinement/Lemma54/Candidates/V0.lean

# Write a new candidate.
cp ProofRefinement/Lemma54/Candidates/V0.lean \
   ProofRefinement/Lemma54/Candidates/V1.lean
# ... edit V1.lean ...

# Evaluate it.
uv run ProofRefinement/Lemma54/Evaluator.py \
  --file ProofRefinement/Lemma54/Candidates/V1.lean
```

The evaluator: parses, compiles (`lake env lean`), audits axioms
(`#print axioms`), runs registered numerical oracles, computes `Cr_val`,
and appends a JSON record to `Refinement_Log/log.jsonl`. Pass = compile
clean + every axiom either seed or oracle + every oracle bound certified
≥ declared. Fail prints the reason and still logs.

Useful flags: `--skip-compile` (parse + score only, ~instant),
`--skip-oracle` (compile + audit, no Python oracles), `--no-log`
(don't pollute the log during throwaway experiments).

## What V0 looks like

V0 is now a **production-faithful mirror** of
`ProofGraph/Effective/Lemma54Effective.lean`. Same constants
(`M_val = 4000`, `delta_val = 57/1000`, `B_val = 293/250`,
`SearchConfig.eta = 1/100`, `SearchConfig.r = 23/25`), same oracle
rectangle `Ω(δ_val, B_val)`, same `Cr_paper` formula. The sink
theorem `Braverman.PaperV0.lemma_5_4_search` is proved by direct
delegation to `Braverman.Paper.lemma_5_4_paper_on_domain` at the
production tuple.

- **Score:** `Cr_val ≈ 8.196·10¹⁴` — the rational upper bound on
  `Cr_paper r_val M_val (R_val_paper r_val)`, matching the
  production-side `certificate.json`.
- **Two custom axioms** (matching production):
  - `h_M_oracle` — runner-witnessed by `compute_M_bound_production`,
    which returns ≈ 3600.44 on the production rectangle.
  - `h_oracle_domain_contains_image` — structural / Rouché-based;
    inherited from production as a seed axiom.
- **12 trusted analytic axioms** about `F_inv_paper` (same set
  production transitively uses).

Read [Candidates/V0.lean](Candidates/V0.lean) before doing anything.

## What the production path looks like (for orientation)

The production trust base for the **sink**
`Braverman.Effective.KG_lt_Krivine_effective` is **24 axioms**:

- 3 Lean primitives (`propext`, `Classical.choice`, `Quot.sound`).
- 12 trusted analytic axioms about `F_inv_paper` (in
  `Proof/Lib/Lemma54_Paper.lean`).
- `Braverman.Effective.h_M_oracle` (single-`M` sup bound on
  `Ω(δ_val, B_val)`; `M_val = 4000` dominates the certified
  `compute_M_rigorous ≈ 3531`).
- `Braverman.Effective.h_oracle_domain_contains_image`
  (`F_inv_paper(disk r) ⊆ Ω(δ_val, B_val)`; certified by Step 1's
  Rouché).
- `Braverman.Effective.h_eta_strict_improvement_oracle`
  (`(H_η(I)/I).re > log(1+√2)` at `η = eta_val`; arb-certified).
- `Braverman.Effective.h_gamma_explicit_sandwich` (rational sandwich
  on the IVT-chosen γ at `(eta_val, p_explicit_rat = 1/10³⁰)`).
- 4 threshold axioms at `p_explicit_rat = 1/10³⁰`
  (`h_p_explicit_lt_pr_paper`, `h_F_p_deriv_at_p_explicit`,
  `h_gap_ratio_at_p_explicit_with_B_phi`,
  `h_summability_at_p_explicit`).
- `sorryAx` (from `LeanProof/Rounding.lean`'s two non-quantitative
  sorries).

The certified-arb runner emits a [certificate.json] with 17/17
cross-validations passing and 9/9 oracle assumptions certified per
`--run-all`. See `ProofGraph/STATUS_AND_PLAN.md` for the full
trust-boundary narrative.

## Constraints (unchanged)

1. **`Proof/SearchConfig.lean` is locked.** `eta = 1/100` and
   `r = 23/25`. Don't edit it.
2. **`sorryAx` is a hard fail.** No `sorry`. Anywhere.
3. **No unregistered axioms.** Every axiom your candidate transitively
   uses must be either in [`lemma.toml`](lemma.toml)'s
   `seed_axioms.allowed` or have an `[[oracles]]` entry. To carry over
   a paper-cited axiom, append it to `seed_axioms.allowed`. To wire
   numerical backing, add an `[[oracles]]` entry and a
   `compute_*_bound` function in `Numerical_Library/`.
4. **Sink theorem name is `lemma_5_4_search`.** In whatever namespace
   you like, but the name is fixed. Its statement signature is in V0;
   matching it exactly is what makes a candidate comparable.
5. **You may not weaken the theorem.** The signature pins `eps_val * p`
   ball radius and `Cr_val * p^2` error. Tightening the constants is
   the whole game; relaxing the statement is cheating.
6. **Do not edit `ProofGraph/`** as part of a refinement candidate. The
   proof-graph layer is the production target; refinement candidates
   live in `Candidates/`. (You may *consult* the proof graph for
   guidance; just don't write to it from here.)
7. **No truncation. Ever.** Never import `eval_H_eta_at_acb`,
   `eval_phi_at_acb`, `eval_H_eta_deriv_at_acb`, or
   `eval_phi_and_deriv_at_acb`. They are K_max-truncated with no
   rigorous tail bound (their docstring admits it). Use the
   truncation-free machinery in [`Scratch/`](Scratch/) — see
   [PATCH_NOTES.md](PATCH_NOTES.md) §2a — or the cached chunk JSONs
   in [`Cache/Backups/2026-05-03_*`](Cache/Backups/). The
   Evaluator's G7 fails any candidate whose oracle path reaches a
   forbidden symbol.
8. **`Cr_val` must dominate `Cr_patched`.** Every candidate file
   must include the audit-block header from PATCH_NOTES R5 naming
   the source chunks JSON, the source audit JSON, and the
   `Cr_patched(this candidate)` it's claiming. The Evaluator
   reads the audit JSON and fails the candidate if its
   `Cr_patched_float` exceeds the candidate's `Cr_val_float`.
   Lowering the rational literal without lowering the audit is no
   longer a win — that was the K_max-era trick.

Beyond that: edit anything. Restructure, split, merge, prove from
scratch, change the namespace, add helper lemmas, import more Mathlib,
rewrite proofs, delete dead code.

## Where to start (priorities)

V0 is a production mirror, so the framework's purpose is to find
candidate-side **departures** from production that win on the score
(`Cr_val`) or on the audited axiom count.

The intent is for the agent to **derive its own refinement
directions** by reading `Proof/Lib/Lemma54_Paper*.lean`, identifying
loose bounds or factorizations, and proposing tightenings.
Documentation here intentionally avoids enumerating specific
candidate directions or alternative formulations — that's the
agent's job to discover. Some abstract levers worth thinking
about:

- The numerical inputs flowing into `Cr_paper` (e.g. `M_val`).
  Their certified values come from `Numerical_Library`'s production
  oracle; any tightening that respects the certified floor lowers
  `Cr_val`.
- The shape of the bound itself in `Lemma54_Paper.lean` and the
  step-by-step derivation in `Lemma54_Paper_*.lean`. Each step
  introduces a factorization or a constant; some of them may be
  loose for the actual analytic quantities involved at the
  configured `(η, r)`.
- The trusted axioms in `lemma.toml`'s `seed_axioms.allowed` list.
  Each one represents a fact the proof currently takes on faith;
  proving any of them in Lean removes one from the audit set.

**Do not look in `_archive/` for guidance.** Old candidates and
archived alternatives are out-of-bounds — the harness's purpose is
for you to come up with the refinement ideas yourself, not to copy
from prior work.

## Conventions (unchanged)

- **One candidate per file**: `Candidates/V1.lean`, `V2.lean`, etc.
  Don't overwrite V0.
- **Declare the parent**: put `-- @parent Candidates/V0.lean` near the
  top of your candidate. The log records it; review later becomes
  painless.
- **Use `Experience.md` as your notebook**: write down what you tried,
  what worked, what didn't, what's worth retrying. It persists across
  sessions and is the only thing besides the log that does.
- **Use `Scratch/` for ad-hoc experiments** (Python sketches, isolated
  Lean files, oracle prototypes). Nothing in `Scratch/` is audited or
  scored. **Scratch/ is persistent across sprints** — name new files
  `Scratch/sprint_<NNN>_<topic>.py` so future agents can trace which
  sprint produced what. Reading prior `Scratch/sprint_<K>_*` files is
  encouraged: they're the harness's institutional memory of past
  numerical findings.
- **Do not edit `Proof/`** unless you have a specific reason. It's
  shared infrastructure (now feeding the production proof too); per-
  candidate work goes in `Candidates/`.

## Reading list (in priority order)

0. [PATCH_NOTES.md](PATCH_NOTES.md) — **mandatory.** The 2026-05-03
   K_max-truncation discovery, the truncation-free oracle suite, the
   cached-output canon, the per-candidate audit (Cr_patched), and the
   binding rules R1–R5 enforced by G7. Read **before** V0.lean if your
   sprint touches numerics.
1. [Candidates/V0.lean](Candidates/V0.lean) — the seed, fully commented.
2. [README.md](README.md) — layout + workflow.
3. [`Proof/Lib/Lemma54_Paper.lean`](Proof/Lib/Lemma54_Paper.lean) and
   [`Proof/Lib/Lemma54_Paper_Main.lean`](Proof/Lib/Lemma54_Paper_Main.lean)
   — the production paper-faithful proof (12 trusted axioms +
   derivations). Read this to understand what's already proved.
4. [lemma.toml](lemma.toml) — config you'll likely edit when registering
   new axioms.
5. [`../../ProofGraph/STATUS_AND_PLAN.md`](../../ProofGraph/STATUS_AND_PLAN.md)
   — production-side trust boundary, what's done, what's open.
6. [`assets/pdf/braverman.pdf`](../../assets/pdf/braverman.pdf), §5
   (Lemma 5.3, 5.4, eq. 75–76) — the paper. Page 21 onward.

## If you are running inside the harness

If this brief is being read by an agent invoked as a sub-agent
(`refinement-planner`, `refinement-generator`, or
`refinement-evaluator` — see `.claude/agents/`), the rules of the
[harness](../../docs/PROOF_REFINEMENT_HARNESS.md) apply on top of the
above. Most importantly:

- **The Generator MUST NOT add new axioms.** Removing an axiom (by
  proving it as a Lean theorem) or retargeting an existing oracle
  (e.g. tightening `M_val`) is fine. Introducing a new `axiom`
  declaration is forbidden. If a sprint appears to require one,
  return `STATUS=BLOCKED_NEEDS_HUMAN`.
- **The Generator may edit shared Lemma 5.4 infrastructure**
  (`Proof/Lib/Lemma54_Paper*.lean`, `Numerical_Library/`,
  `ProofGraph/Effective/Lemma54*.lean`, `LeanProof/Lemma54.lean`,
  `LeanProof/Defs/Strip.lean`) — but only files named in the
  contract's `Concrete edits expected:` list. Out-of-list edits
  trip the Evaluator's G3 (`WRITE_SCOPE_VIOLATION`). Loss prevention
  is handled by the project's git auto-checkpoint hook (every
  Edit/Write commits), so any modification is recoverable from
  history.
- **History is sacrosanct.** Older `Candidates/V<K<N>.lean`,
  Sprint Contracts, `Evaluator.py`, runner code under
  `ProofGraph/proof_graph/`, TOML node configs, and helper scripts
  are always forbidden, regardless of what the contract says.
- **The Generator does not run the production audit or `--run-all`.**
  Those are post-port verifications, not in-loop gates.

The candidate-iteration framework on this brief above (the
`Candidates/V<N>.lean` workflow) is unchanged — but in harness mode it
is *driven by Sprint Contracts* (`Sprint_Contracts/sprint_<NNN>.md`)
rather than by the agent's own initiative, and may co-edit shared
infrastructure when a sprint's direction (e.g., a structural
formula change to `Cr_paper`/`Cr_tight`) requires it.

## How you'll know you're winning

- **`Cr_val` in successive log entries decreases.** This is the
  primary metric. In the current regime (see
  `Bulletin.md` "Current priority"), wins come from structural
  formula changes, identity refinements, contour-change moves, or
  consuming a freshly-approved proposal's new infrastructure
  (e.g., the η-aware oracles that unlock `Cr_refined`).
- **A pending proposal becomes approved.** The proposal mechanism
  amortizes high-value-but-trust-expanding moves through human
  review; an approval = a future `Cr_val` win is now reachable.
- Reducing the audited axiom count by converting a seed axiom into
  a Lean theorem is **not** considered a win in the current
  regime — the engineering hours are better spent on `Cr_val`-
  reducing structural moves. (Sprint_010 was the last
  axiom-prove run; the policy has since shifted.)

That's it. Edit Lean, run the evaluator, log the result. The framework
gets out of your way.
