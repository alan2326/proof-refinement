# The Polygon-π proof-refinement harness

Design document. Describes what the loop is, what it may touch, and how a
candidate is judged. For the day-to-day rules see
[`../AGENT_BRIEF.md`](../AGENT_BRIEF.md).

---

## 1. The problem

Inscribe a regular polygon with `N = 2^(n+2)` sides in the unit circle. Half its
perimeter is `N sin(π/N)`, which Mathlib writes without trigonometry using the
nested radical `sqrtTwoAddSeries`:

```lean
noncomputable def polygonLower (n : ℕ) : ℝ :=
  2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n)
```

`n` is the **doubling depth**, not the side count. Depth `n` is a `2^(n+2)`-gon,
so `benchmarkDepth = 10` means the inscribed regular **4096-gon**.

A candidate declares two rational constants and proves

```lean
def ValidPolygonBound (lam kap : ℝ) : Prop :=
  0 ≤ lam ∧ 0 < kap ∧
    ∀ n : ℕ,
      polygonLower n + lam / 4 ^ n < Real.pi ∧
      Real.pi < polygonLower n + kap / 4 ^ n
```

**Score = `kappa - lambda`, minimized.** Both endpoints sit on the *same*
inscribed polygon, so the score is a pure width coefficient and candidates are
directly comparable.

The obligation is quantified over all `n`. The benchmark depth appears only in the
trusted corollary the artifact reports:

```lean
theorem certified_polygon_interval {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    polygonLower benchmarkDepth + lam / 4 ^ benchmarkDepth < Real.pi ∧
    Real.pi < polygonLower benchmarkDepth + kap / 4 ^ benchmarkDepth
```

Freezing the depth means no score improvement can come from simply adding sides.
Quantifying over `n` means no candidate can win by brute-force numerics at a
single point.

## 2. The loop

```
preflight → planner → generator → evaluator → bulletin line → summary
```

- **planner** (`opus`) reads `Bulletin.md`, `Experience.md`, and the tail of
  `log.jsonl`, then writes exactly one bounded sprint contract. It writes no Lean.
- **generator** (`opus`) executes that contract into `Candidates/V<N>.lean`,
  within a declared write scope, and stops with a `STATUS` line.
- **evaluator** (`sonnet`) runs the gates literally and writes
  `Refinement_Log/verdict_<sprint>.md`. It never edits Lean and never fixes a
  failure.

Persistent state is only: `Bulletin.md` (frontier + human priorities),
`Experience.md` (append-only notebook), `log.jsonl` (one record per evaluation),
the verdict notes, and the candidates themselves.

Autonomous mode is **self-paced** — `/loop /run-next-polygonpi-sprint` with no
interval, so the next sprint starts when the previous one returns. Throttling is
by preflight halt, not by a timer: a stuck loop should stop, not be rate-limited
into looking healthy.

### Preflight halt conditions

1. uncommitted changes to the trusted surface or the harness;
2. a reference candidate or its build artifacts present in the workspace;
3. a blocked module reachable from any workspace module, transitively;
4. the last 3 evaluations all failed;
5. **saturation** — the last 5 passing candidates each improved the score by less
   than a relative `1e-3`;
6. the incumbent no longer builds.

Condition 5 is the important one. The score has a dense rational approach to its
analytic floor, so there is an unbounded supply of technically-valid
"improvements" with no analytic content. The countermeasures are this halt, the
required `Rung type` field on every contract, and the standing Bulletin directive
to prefer architectural rungs — the same mechanism a human would use to steer the
loop, made explicit.

## 3. Trust surface

**Zero project axioms. Zero numerical oracles.** Every candidate's axiom closure
must be a subset of `{propext, Classical.choice, Quot.sound}`. This automatically
bans `native_decide`, whose closure contains `Lean.ofReduceBool` and
`Lean.trustCompiler`, and it means every numeric fact is a proof rather than a
computation the kernel is asked to trust.

"Partial formalization" here refers only to the division of labour: a small
read-only human-provided Lean surface fixes the problem statement, and the agent
supplies every line of the refinement on top of it. The read-only surface is:

```
PolygonCore/Polygon.lean       polygonLower, benchmarkDepth, the perimeter identity
PolygonCore/LowerBound.lean    polygonLower_pos, polygonLower_lt_pi
Proof/Surface.lean             re-export
Proof/CandidateContract.lean   ValidPolygonBound, ValidPolygonBoundAt
Proof/FixedDepth.lean          certified_polygon_interval + its width
Proof/Main.lean                the one module candidates import
```

That surface contains **no estimate of any kind** — no bound on `x - sin x`, no
bound on `π`, and no reduction bridge factoring the coefficient into reusable
pieces. This is deliberate. The baseline `Candidates/V0.lean` contains one worked
instance of the whole chain inline, so a candidate can read an example and must
generalize it itself. Nothing quantitative will be added to the trusted surface
on request; if a candidate wants a lemma, the candidate proves it.

## 4. Isolation

Mathlib ships a finished version of this result — `Real.pi_gt_3141592`,
`Real.pi_lt_3141593`, and the `pi_lower_bound`/`pi_upper_bound` machinery built on
`sqrtTwoAddSeries_step_up`/`_down`. Rebuilding the quantitative part is the
exercise, so that machinery is unavailable three ways.

**Policy.** `lemma.toml` allows the prefixes `Mathlib`,
`ProofRefinement.PolygonPi`, `PolygonCore`, and blocks bare `import Mathlib`
(the mega-import) plus everything under `Mathlib.Analysis.Real.Pi`. Both the
candidate file and every `.lean` in the workspace are audited.

**Transitively.** Blocking direct imports is not enough: several innocuous
modules reach the blocked namespace — `Mathlib.Analysis.SpecialFunctions.Stirling`
imports `Pi.Wallis`, and `NumberTheory/NumberField/Discriminant/Basic` imports
`Pi.Bounds`. `scripts/polygonpi_import_closure.py` resolves the full closure
across the project and the vendored packages and rejects any blocked module in it.

Two parsing details that a naive implementation gets wrong, both of which would
silently disable the audit:

- This Mathlib is the Lean 4.28 **module-system** tree. It writes
  `public import M` 23818 times against bare `import M` only 319 times, so a
  parser anchored on `^import` sees almost nothing — and a candidate could have
  evaded the audit by writing `module` + `public import <blocked>`. The parser
  accepts any sequence of `public` / `private` / `meta` modifiers.
- Several Mathlib docstrings contain a literal `import Mathlib` inside a code
  fence. Comments are stripped before parsing, or the closure false-positives on
  the mega-import.

**Static text scan.** The finished lemma names are forbidden by name, against
comment-stripped source, so that a token appearing only in prose is not a
violation while an actual use is.

**Physical.** All five modules under `Mathlib/Analysis/Real/Pi/` are deleted from
this checkout, together with their build artifacts and the root `Mathlib.olean`.
Both the mega-import and any direct `Pi.*` import now fail to resolve rather than
merely being disallowed. Pre-deletion hashes are recorded in
`environment/stripped_modules.txt`. The only modules this breaks are
`Counterexamples/NowhereDifferentiable`, the root `Mathlib.lean`,
`NumberTheory/NumberField/Discriminant/Basic`, and
`Analysis/SpecialFunctions/Stirling` — none of which is in any closure we build.

**Answer key.** There is a human-only directory of experiment records, and a
human-only reporting directory. Both are denied in
`.claude/settings.local.json` and off-limits to every agent in the loop; the
first is also gitignored. Their contents are deliberately not described anywhere
an agent can read, and everything derived from them is computed human-side, so
nothing inside the workspace reveals how good a bound is achievable. If you are
an agent reading this: the existence of those directories is not an invitation,
and reading either invalidates the run.

**Honest disclosure.** The agent runs inside Claude Code with filesystem read
access, so isolation is enforced by policy plus module deletion rather than by a
sealed container. The classical Archimedes argument is famous and certainly
present in model weights. This is therefore a **transfer and formal-certificate
recovery** task, not a held-out discovery benchmark, and the artifact must say so.

## 5. The evaluator

Twelve stages, fail-closed; the first failure stops the run and is logged with a
reason.

| # | stage | notes |
|---|---|---|
| 1 | workspace import audit | every `.lean` under the workspace |
| 2 | candidate direct imports | against `[import_policy]` |
| 3 | **transitive import closure** | §4; also flags blocked modules whose source is deleted, since those appear as unresolved |
| 4 | **static pattern + size scan** | forbidden tokens on comment-stripped source; ≤2000 lines, ≤100 KB per file |
| 5 | declarations + sanity | sink theorem present; `kappa`, `lambda` parse as rationals; `0 < kappa`, `0 ≤ lambda`, `lambda < kappa`; ≤30 digits |
| 6 | compile | `lake build`, 600 s, wall/CPU/RSS via `/usr/bin/time -v` |
| 7 | **exact type check** | the sink theorem has exactly the contract type at the declared constants, **and** `certified_polygon_interval` applies to it |
| 8 | secondary contract | optional depth-10 frontier; absent ⇒ skipped, not failed |
| 9 | **axiom closure** | must be a subset of the three standard axioms |
| 10 | oracle table | hard error if `lemma.toml` declares any oracle |
| 11 | score + incumbent | exact `Fraction`; records `incumbent` and `strict_improvement` |
| 12 | log append | one JSON record to `log.jsonl` |

Two deliberate design points:

- **Stage 7 checks the corollary, not just the theorem.** A candidate could in
  principle prove something of the right shape that the reported interval does not
  actually follow from. Type-checking `certified_polygon_interval` applied to the
  candidate closes that gap.
- **Stage 11 does not hard-fail a non-improving candidate.** A valid but
  non-improving result is a legitimate logged outcome. It is the *evaluator
  agent's* job to enforce whatever inequality the sprint contract declared.

`kappa` and `lambda` must be **single-line** `def … : ℝ := <rational>`. The
parser captures to end-of-line rather than scanning forward for the next
declaration, because the scan-forward form silently runs away when the following
declaration carries a modifier such as `private lemma`.

## 6. Reporting

`results/summarize.py` is human-side and never agent-written. It reads
`log.jsonl`, the verdict notes, and the human-only records, and emits
`frontier.csv` (with `rung_type` and `side` columns, so a one-sided or
precision-dominated run is visible at a glance), `summary.md`, and a
`human_effort.csv` skeleton.

`scripts/verify_all.sh` is the one-command replay: it re-checks the isolation
properties, rebuilds the trusted surface, re-evaluates every candidate with
`--no-log`, and prints the axiom closure of the best one.

Known limitation, stated plainly: per-model-call token and dollar accounting is
not obtainable from inside this harness, so cost reporting is wall-clock and
Lean-compile CPU only.
