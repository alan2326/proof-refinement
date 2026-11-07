# Agent brief — Polygon-π proof refinement

## The scored contract

Fixed, and no sprint may weaken it. From `Proof/CandidateContract.lean`:

```lean
def ValidPolygonBound (lam kap : ℝ) : Prop :=
  0 ≤ lam ∧ 0 < kap ∧
    ∀ n : ℕ,
      polygonLower n + lam / 4 ^ n < Real.pi ∧
      Real.pi < polygonLower n + kap / 4 ^ n
```

A candidate is one file, `Candidates/V<N>.lean`, containing:

```lean
-- @parent V<N-1>
import ProofRefinement.PolygonPi.Proof.Main
...
def lambda : ℝ := <rational literal>
def kappa  : ℝ := <rational literal>
theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa := ...
```

**Score = `kappa - lambda`, minimized.** You improve by lowering `kappa`, raising
`lambda`, or both.

`lambda` and `kappa` must each be a **single-line** `def … : ℝ := <rational>`.
The evaluator parses them textually and scores them as exact `Fraction`s; a
multi-line definition will not parse and the candidate will be rejected. Both
are capped at 30 digits in numerator and denominator.

## What the trusted surface gives you

Everything reachable from `Proof/Main.lean`, and nothing else:

| declaration | what it is |
|---|---|
| `PolygonCore.polygonLower n` | `2 ^ (n+1) * √(2 - sqrtTwoAddSeries 0 n)` |
| `PolygonCore.polygonLower_eq_mul_sin` | `polygonLower n = 2 ^ (n+2) * sin (π / 2 ^ (n+2))` |
| `PolygonCore.polygonLower_pos` | `0 < polygonLower n` |
| `PolygonCore.polygonLower_lt_pi` | `polygonLower n < π`, uniform in `n` |
| `PolygonCore.benchmarkDepth` | `10` — the reported depth. `benchmarkSides = 4096` |
| `ValidPolygonBound`, `ValidPolygonBoundAt` | the contracts |
| `certified_polygon_interval` | the trusted depth-10 corollary the artifact reports |

That is the whole trusted surface. It contains **no estimate of any kind** — no
bound on `x - sin x`, no bound on `π`. Anything quantitative is yours to prove,
and nothing quantitative will be added to the trusted surface on request.

`n` is the **doubling depth**, not the side count: depth `n` is a `2^(n+2)`-gon,
so `benchmarkDepth = 10` is a 4096-gon.

## Rules

**You may:**

- replace `kappa` and `lambda` with any rational literals
- replace the proof entirely
- add helper lemmas in your own candidate file
- add per-candidate derived-theorem files under `Candidates/V<N>/` (see below)
- import additional `Mathlib.*` modules, subject to the import policy
- optionally also declare `kappaDepth10` / `lambdaDepth10` and prove
  `polygon_pi_depth10_search : ValidPolygonBoundAt 10 lambdaDepth10 kappaDepth10`.
  This is logged as a second frontier. It is never a substitute for the main
  contract, and a candidate that only has the depth-10 version does not count.

**You may not:**

- change the contract, or the name/type of `polygon_pi_constant_search`
- edit `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`, `scripts/`,
  sprint contracts, or any older candidate
- introduce `axiom`, `opaque`, `unsafe`, `native_decide`, `run_tac`, or any
  metaprogramming
- import a blocked module, directly **or transitively**

### Import policy

Allowed prefixes: `Mathlib`, `ProofRefinement.PolygonPi`, `PolygonCore`.

Blocked: bare `import Mathlib` (the mega-import), and anything under
`Mathlib.Analysis.Real.Pi`. Those modules have also been physically removed from
this checkout, so the import would fail to resolve even if policy allowed it.

The block is **transitive**. Some innocuous-looking Mathlib modules reach the
blocked namespace — `Mathlib.Analysis.SpecialFunctions.Stirling` imports
`Pi.Wallis`, for instance. Check before you rely on a new import:

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  <module> --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi
```

Also forbidden by static text scan, because they are the finished machinery this
exercise exists to rebuild: `pi_lt_sqrtTwoAddSeries`, `pi_gt_sqrtTwoAddSeries`,
`sqrtTwoAddSeries_step_up`/`_down`, `pi_lower_bound_start`, `pi_upper_bound_start`,
`pi_gt_three`, `pi_gt_3141592`, `pi_lt_3141593`.

### Axiom rule — this is the strict one

Your candidate's axiom closure must be **exactly a subset of**

    {propext, Classical.choice, Quot.sound}

Zero project axioms. Zero oracles. No `native_decide` (it adds
`Lean.ofReduceBool` and `Lean.trustCompiler`). This workspace makes a stronger
claim than a typical proof-search run: the artifact is fully formally verified,
with a small read-only human surface fixing only the problem statement. Do not
weaken that. Check with:

```lean
#print axioms ProofRefinement.PolygonPi.Candidates.V<N>.polygon_pi_constant_search
```

### Creating derived-theorem files

If a candidate needs a substantial intermediate result, put it in
`Candidates/V<N>/<Name>.lean`, imported only by `Candidates/V<N>.lean` or its
siblings. These files contain `theorem`s and `lemma`s only — never `axiom`s.
Register the module path in `lemma.toml`'s `[workspace_import_policy]` only if
the contract explicitly tells you to.

## What the evaluator checks

Twelve stages, fail-closed, in this order. Read `Evaluator.py` if you want the
detail; the ones that surprise people are 3, 4 and 9.

1. workspace import audit  2. candidate imports  3. **transitive closure**
4. **static pattern + size scan** (≤2000 lines, ≤100 KB per file)
5. declarations present, `0 < kappa`, `0 ≤ lambda`, `lambda < kappa`
6. `lake build`  7. exact contract type check **and** that
`certified_polygon_interval` applies  8. optional secondary contract
9. **axiom closure**  10. oracle table empty  11. score + incumbent
12. log append

Run it yourself before declaring done:

```bash
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V<N>.lean --no-log
```

A valid but non-improving candidate is a legitimate logged outcome, not a
failure — but the *sprint contract* may require a strict improvement, and the
evaluator agent will enforce whatever the contract declared.

## Capability note — what you are expected to be able to do

The obstacles in this workspace are ordinary real-analysis formalization, and
you are competent at all of it. Concretely, this task's toolkit:

- **Monotonicity arguments.** `strictMonoOn_of_deriv_pos` over `Set.Ici 0` or
  `Set.Ico`, with `HasDerivAt` built from `Real.hasDerivAt_sin`,
  `Real.hasDerivAt_cos`, `hasDerivAt_pow`, `.div_const`, `.add`, `.sub`, then
  `(h).deriv` to rewrite. `Real.lt_tan` in Mathlib is a worked example of exactly
  this shape — read it.
- **Square-root bounds.** `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`,
  `Real.sqrt_nonneg`, and `nlinarith` with `Real.sq_sqrt` as a hint. This is how
  you turn `√2` or a nested radical into a certified rational interval.
- **The nested radical.** `Real.sqrtTwoAddSeries 0 n` unfolds by `simp
  [Real.sqrtTwoAddSeries]`; `Real.sqrtTwoAddSeries_succ`,
  `_monotone_left`, `_lt_two`, `_nonneg` are all available, as are
  `Real.cos_pi_over_two_pow` and `Real.sin_pi_over_two_pow_succ`.
- **Arithmetic chains.** `field_simp`, `ring`, `gcongr`, `positivity`,
  `nlinarith`, `norm_num` on exact rationals with 20+ digit numerators.
- **Induction on the depth parameter**, when a uniform-in-`n` claim needs it.

Search Mathlib aggressively — `lean_local_search`, `lean_loogle`,
`lean_leansearch`, `lean_state_search`, `lean_hammer_premise` — and use more than
one of them before concluding a lemma does not exist. Note that lemma names drift
between versions: `div_le_div_iff` and `mul_lt_mul_left` do **not** resolve the
way you may remember in this Mathlib, while `pow_le_pow_left₀`,
`mul_lt_mul_of_pos_left`, and `le_div_iff₀` do. When a name fails, grep the
Mathlib tree for the real one rather than guessing twice.

Long proofs are normal here. Do not exit because a tactic block got long, or
because you have been working a while. Exit when you have genuinely exhausted
your ideas — and "genuinely exhausted" means you stated the goal with
`lean_goal` rather than from memory, searched with at least two tools and can
name what you searched for, tried *tactically distinct* approaches rather than
three flavours of `simp`, and considered whether the obstruction is really at a
different level than where you are attacking it.
