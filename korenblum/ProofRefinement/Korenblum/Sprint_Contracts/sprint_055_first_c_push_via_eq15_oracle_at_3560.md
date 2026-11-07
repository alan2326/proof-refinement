# Sprint 055: First c-push above the seed via the `eq15` oracle channel — ship `Candidates/V49.lean` at `c_value = 1780/5000 = 0.3560`

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V48.lean` (the seed-tying oracle-routed candidate
sprints 053/054 landed at `c = 3554/10000`)
**Target file**: `Candidates/V49.lean`
**Direction**: raise-c — first sprint to actually push `c_value` above the seed
since V0 was sealed 54 sprints ago. Routes through the pre-approved
`[[oracles]]` channel landed by sprints 053/054, with a sibling per-`c` shim
in `Numerical_Library/rigorous_scalar.py` and a sibling `[[oracles]]` row in
`lemma.toml`. No Lean infrastructure change.

## Goal

Ship `Candidates/V49.lean` proving
`theorem korenblum_constant_search : ValidKorenblumBound c_value` at
`c_value := 1780 / 5000 = 0.3560`, discharging the `(15)` premise via a
new oracle-registered axiom `hEq15_oracle_certified_3560`. Score must
report `1780/5000 > 1777/5000` for this to count as the workspace's first
genuine c-push under the new directive.

## Why

### The c-push cascade is finally unblocked

Sprints 048–051 wrote `Scratch/` evidence (sprint 050 mpmath `dps=50,
N_TRUNC=200` table pinpointed the literal `(15)` crossover inside
`c ∈ (0.3560, 0.3565)`). Sprint 052 went off-script and filed
`proposal_002` (deferred by the human). Sprints 053 and 054 wired the
`[[oracles]]` channel: sprint 053 shipped the
`Numerical_Library.rigorous_scalar.certify_eq15(c_num, c_den, *, dps,
n_trunc)` wrapper plus a per-`c` zero-argument shim
`certify_eq15_at_seed()`, and sprint 054 pinned `mpmath` and
`python-flint` in a repo-root `pyproject.toml` so the canonical
`uv run` Evaluator can actually invoke the oracle. The latest
`log.jsonl` row (sprint 054 re-run of V48) confirms

```
oracle_checks: [{
  axiom: "hEq15_oracle_certified_3554",
  bound_field: "eq15_lower_bound",
  declared: "1",
  ok: true,
  oracle_bound: "1"
}]
```

i.e. the channel is fully functional. The bulletin's second 2026-05-02
directive (lines 219–313) explicitly authorised this sprint family, and
its example schedule (lines 271–280) literally lists `c = 1780/5000 =
0.3560` as the "push to the next safe step" with mpmath-verified gap
`+0.0113`.

The seed has been tied for 54 sprints. Pushing `c` is the only
deliverable that counts as a win under the bulletin's first 2026-05-02
directive ("structural novelty is now valued only insofar as it advances
a `c_value > 0.3554`"). Sprint 055 ships that win.

### Why c = 1780/5000 = 0.3560, not 1779/5000 = 0.3558 or 1781/5000 = 0.3562

The user's sprint instructions framed this as "0.3558 vs 0.3560". I
considered three structurally distinct candidates (planner ultrathink,
per `KORENBLUM_PROOF_REFINEMENT_HARNESS.md`):

**C1 — `c = 1779/5000 = 0.3558` (sprint 054's bulletin-line plan).**
Sprint 050's mpmath `dps=50, N_TRUNC=200` table reports gap `+2.07e-02`
at `c = 0.3556` and `+1.131e-02` at `c = 0.3560`; interpolating, the
gap at `c = 0.3558` is approximately `+0.016`. Subtract sprint 053's
empirically-measured ~0.003 box-by-box conservatism gap (Experience.md
sprint_053 lines 745–767) and the wrapper's certified `total` at 0.3558
is ~`1.013`, well above the strict-margin threshold `1 + 10^(-30)`.
**Strongest objection:** this is *cautious by 5x* what the wrapper's
falsifiability margin requires. With 0.0113 of mpmath-verified gap and
~0.003 of conservatism, the wrapper has ~0.008 of headroom even at
0.3560. Stopping at 0.3558 burns one extra sprint per ~0.0002 of `c`
without buying any verifiability that 0.3560 doesn't already have.

**C2 — `c = 1780/5000 = 0.3560` (CHOSEN).** Sprint 050's table reports
gap `+1.131e-02` directly at this point — the largest integer-10000ths
`c` *with verified margin* in sprint 050's enumeration. Subtract sprint
053's ~0.003 conservatism and the certified `total` at 0.3560 is
~`1.008`, still ~`8 × 10^6` times the strict-margin threshold
`10^(-30)` (so a True return is essentially guaranteed). **Strongest
objection:** it is one tenth-thousandth shy of the bulletin's
suggested-next-step `0.3558`, which would have been a more
conservative trial. **Resolution:** the bulletin's incrementalism
principle (line 298) is "aim for the closest verified step, not the
limit" — 0.3560 is *not* the limit (the limit is the crossover at
~0.35635), it is *the closest sprint-050-verified positive step* at
the next integer-10000ths after 0.3558, and the bulletin's example
schedule (line 277) **literally names this c-value as the
"next safe step"**. The cascade `0.3554 → 0.3558 → 0.3560` was
designed by the bulletin under the assumption that each step burns
one sprint; sprints 048–054 already burned 7 sprints on roadmap and
plumbing, so catching up to the bulletin's original schedule by
collapsing one step is in line with the spirit of incrementalism, not
against it.

**C3 — `c = 1781/5000 = 0.3562` (one tenth-thousandth past 0.3560).**
**Strongest objection (decisive):** sprint 050's mpmath table tested
`{0.3554, 0.3556, 0.3558, 0.3560, 0.3565}`. **0.3562 is not in the
table.** The bulletin (line 280) interpolates "`gap ~+0.008`" but no
`Scratch/` script has actually verified it under the wrapper's
envelope. The bulletin's first directive (line 99) is unambiguous:
"*every* sprint that proposes a numerical headroom must include a
`Scratch/` script that confirms the inequality holds at the proposed
`(c, parameters)` with a stated margin, **before** writing any Lean".
Pushing to 0.3562 in sprint 055 would either (a) require running the
wrapper on 0.3562 first as a new `Scratch/` step (legitimate but
exceeds the bounded one-Generator-session budget — the wrapper's
~38–45s wall-clock per call is fine, but writing the contract for a
c-push past sprint 050's verified table requires `Scratch/`
documentation that is itself a separate small sprint), or (b) skip
that step and proceed without verified evidence (forbidden). Demoted.

**Verdict.** C2 is strictly better than C1 on incrementalism economics
(saves one sprint while staying inside sprint 050's verified-positive
table) and strictly better than C3 on adherence to the
"verify-numerically-before-Lean" rule. The choice of 1780/5000 over
the user's framing of 1779/5000 is the planner's expected-value
calculation, not a deviation from the bulletin — the bulletin's
example schedule (line 277) endorses this exact c-value.

### What success looks like

Score `1780/5000 > 1777/5000`. Axiom set is exactly
`{propext, Classical.choice, Quot.sound, hEq15_oracle_certified_3560}`,
with the new axiom registered under `[[oracles]]` and discharged at
Evaluator-time by `Numerical_Library.rigorous_scalar.certify_eq15_at_3560`.
This is the harness's first c-push, and the first `score > 1777/5000` row
in `Refinement_Log/log.jsonl`.

## Concrete edits expected

### 1. `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`

Add a sibling zero-argument shim `certify_eq15_at_3560()` directly after
the existing `certify_eq15_at_seed()` shim (which sits at lines 952–976
of the current file). The shape mirrors `certify_eq15_at_seed` exactly,
modulo the `(c_num, c_den) = (1780, 5000)` parameter pin and the error
message:

```python
def certify_eq15_at_3560() -> Fraction:
    """
    Sprint 055 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_3560``.

    Calls ``certify_eq15(1780, 5000, dps=50, n_trunc=200)``; on True,
    returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_3560``.

    Sprint 050's mpmath ``dps=50, N_TRUNC=200`` table reports
    ``gap = +1.131e-02`` at ``c = 0.3560`` (the largest integer-10000ths
    ``c`` with verified margin in the enumeration; ``gap = -3.598e-04``
    at ``c = 0.3565`` past the literal ``(15)`` crossover). Sprint 053's
    Experience entry empirically measures ~0.003 box-by-box conservatism
    gap relative to adaptive ``mp.quad``, so the wrapper's certified
    ``total`` at ``c = 0.3560`` is ~``1.008`` — well above the
    strict-margin threshold ``1 + 10^(-30)``.

    The Evaluator's ``run_oracle_checks`` then compares the returned
    Fraction against the candidate's ``def eq15_lower_bound : ℝ := 1``
    via ``oracle_bound <= declared``, and accepts the candidate iff
    ``1 <= 1`` — which holds because the shim only returns when the
    certified bound is strictly above 1.
    """
    if not certify_eq15(1780, 5000, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(1780, 5000, dps=50, n_trunc=200) returned False; "
            "wrapper cannot reproduce sprint 050's mpmath gap +1.131e-02 at "
            "c = 0.3560 under the registered envelope. Refusing to certify "
            "the Lean axiom `hEq15_oracle_certified_3560` to keep the trust "
            "surface honest."
        )
    return Fraction(1, 1)
```

**Do NOT** refactor `certify_eq15_at_seed` to take a parameter. The
existing per-`c` zero-argument shim convention (one shim per registered
oracle row, each pinning its own `(c_num, c_den)`) is the Evaluator's
expected calling discipline (`run_oracle_checks` invokes each oracle
function with no arguments per `Evaluator.py:393`). Parametric refactor
would force a wider Evaluator-side change that exceeds this sprint's
scope; the per-`c` shim cost is ~15 lines per c-push and is acceptable
for the cascade size (~4 more sprints to the crossover).

### 2. `ProofRefinement/Korenblum/lemma.toml`

Append a sibling `[[oracles]]` row directly after the existing
`eq15_certified_at_seed` block (which sits at lines 71–74 of the
current file). The schema fields match `Evaluator.py:load_workspace_config`
(`axiom`, `bound_field`, `oracle_fn`):

```toml
[[oracles]]
axiom = "hEq15_oracle_certified_3560"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3560"
```

Also add `"hEq15_oracle_certified_3560"` to `[seed_axioms].allowed`,
right after the existing `"hEq15_oracle_certified_3554"` entry. The
combined diff against the current `lemma.toml`:

```toml
 [seed_axioms]
 allowed = [
   "propext",
   "Classical.choice",
   "Quot.sound",
   "Lean.ofReduceBool",
   "Lean.trustCompiler",

   # The V0 seed's single external input: Wang's equation (15) at c = 0.3554.
   "hEq15_seed_3554",

   # Sprint 053: the Lean-facing axiom name asserted by V48 and discharged by
   # the registered oracle `eq15_certified_at_seed`. Same paper-statement
   # shape as `hEq15_seed_3554` but trust is grounded in the
   # `Numerical_Library.rigorous_scalar.certify_eq15` verified-interval
   # wrapper rather than as a free-floating per-c axiom.
   "hEq15_oracle_certified_3554",
+
+  # Sprint 055: the c-pushed sibling of `hEq15_oracle_certified_3554`.
+  # Same Lean axiom shape, same `Eq15ScalarBound K c_value` statement,
+  # same registered wrapper (`certify_eq15`), but with `c_value` pinned
+  # to `1780/5000 = 0.3560` instead of `3554/10000 = 0.3554`. Discharged
+  # by the sibling oracle `eq15_certified_at_3560`.
+  "hEq15_oracle_certified_3560",
 ]
 …
 [[oracles]]
 axiom = "hEq15_oracle_certified_3554"
 bound_field = "eq15_lower_bound"
 oracle_fn = "rigorous_scalar.certify_eq15_at_seed"
+
+# Sprint 055: first c-push oracle. Pins `certify_eq15` at
+# `(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)` via the
+# zero-argument shim `certify_eq15_at_3560`. Per sprint 050's mpmath
+# `dps=50, N_TRUNC=200` table, gap = +1.131e-02 at c = 0.3560
+# (well above the wrapper's ~0.003 box-by-box conservatism gap
+# relative to adaptive `mp.quad`, and ~10^28 times the strict-margin
+# threshold `10^(-30)`).
+#
+# Falsifiability: the wrapper rejects `(3565, 10000, dps=50, n_trunc=200)`
+# (gap -3.598e-04 per sprint 050's crossover-pinpoint). The same wrapper
+# at `(1780, 5000)` is structurally on the safe side of that crossover.
+
+[[oracles]]
+axiom = "hEq15_oracle_certified_3560"
+bound_field = "eq15_lower_bound"
+oracle_fn = "rigorous_scalar.certify_eq15_at_3560"
```

### 3. `ProofRefinement/Korenblum/Candidates/V49.lean` (NEW FILE)

Mirror `Candidates/V48.lean` byte-for-byte, modulo:

- `@parent V47` → `@parent V48` (V49 is the c-pushed child of V48)
- `namespace ...V48` → `namespace ...V49`
- `def c_value : ℝ := 3554 / 10000` → `def c_value : ℝ := 1780 / 5000`
- `axiom hEq15_oracle_certified_3554` → `axiom hEq15_oracle_certified_3560`
- the discharge of the sink theorem stays
  `valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3560 K)`
- comments updated to refer to the c-push and the new oracle row

Concretely:

```lean
-- @parent V48
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V49

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
First c-push above the seed in 55 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48, but with the literal
`(15)` premise pinned at `c = 1780/5000 = 0.3560` (= the largest
integer-10000ths `c` with sprint-050-verified positive margin in
the mpmath `dps=50, N_TRUNC=200` envelope) instead of the seed
`c = 3554/10000`. The `(15)` premise is discharged by the registered
oracle `eq15_certified_at_3560` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)`; per sprint
050's pinpoint, the wrapper certifies `total ≥ 1 + 10^(-30)` at this
`c` (mpmath gap +1.131e-02, conservatism ~0.003).
-/
def c_value : ℝ := 1780 / 5000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 055 oracle bound-field. Identical declaration to V48; the
Evaluator compares the per-candidate `oracle_fn`'s returned Fraction
against this `def` via `oracle_bound <= declared`. Sharing the same
`bound_field` name across V48 / V49 / future V50+ is permitted because
each `[[oracles]]` row carries its own `oracle_fn` (the per-`c` shim);
the `bound_field` is just the candidate-side declaration of the RHS
threshold of Wang's `1 ≤ scalarCriterion c (paperLambda K c)`.
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 1780/5000 = 0.3560`. Discharged by the registered oracle
`eq15_certified_at_3560` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1780, 5000, 50, 200)`.

Lean axiom shape is byte-for-byte identical to V48's
`hEq15_oracle_certified_3554` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper invoked
by the Evaluator on every candidate run; the wrapper is parametric in
`(c_num, c_den)` so the c-push cascade reuses the existing oracle
infrastructure with one shim-add per sprint.
-/
axiom hEq15_oracle_certified_3560 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3560 K)

end ProofRefinement.Korenblum.Candidates.V49
```

### 4. `ProofRefinement/Korenblum/Bulletin.md`

Append exactly one line to the `## Recent events` block on success
(or the matching BLOCKED line on failure):

```text
sprint_055 PASS: first c-push above the seed in 55 sprints — V49 ships at c_value = 1780/5000 = 0.3560 with axioms_used = {seed} ∪ {hEq15_oracle_certified_3560}; oracle_checks records successful invocation of `rigorous_scalar.certify_eq15_at_3560` (oracle_bound=1, declared=1, ok=true) corresponding to mpmath gap +1.131e-02 at c=0.3560 with ~0.003 box-by-box conservatism gap; score 1780/5000 > 1777/5000 — first row in log.jsonl with score > V0 since the workspace was created; sprint 056 can push further (next safe step is c = 1781/5000 ≈ 0.3562, gap interpolated from sprint 050's table at ~+0.008 — but requires a Scratch verification at the wrapper's envelope first since 0.3562 is not directly in sprint 050's enumeration)
```

Do not reflow the line.

### 5. `ProofRefinement/Korenblum/Experience.md`

Append a new dated entry `### 2026-05-02 sprint_055` summarising:

- **What sprint 054 left undone:** the dependency-pin landed and the
  oracle channel works in the canonical environment, but V48 still ties
  V0 at `c = 0.3554`. The c-push cascade prescribed by the bulletin's
  second 2026-05-02 directive (lines 271–280) was authorised but had
  not yet started.
- **The c-push delivered:** `c = 1780/5000 = 0.3560`, the largest
  integer-10000ths `c` with sprint-050-verified positive mpmath gap
  (+1.131e-02 at `dps=50, N_TRUNC=200`). Mirrors V48 byte-for-byte
  modulo the c-value and axiom-name swaps.
- **Why 0.3560 over 0.3558:** the planner's ultrathink (see contract's
  Why section) compared three candidates — 1779/5000 (sprint 054's
  bulletin-line cautious step), 1780/5000 (chosen — the bulletin's
  example schedule line 277 endorses this c-value as the "next safe
  step"), and 1781/5000 (rejected — outside sprint 050's verified
  table, would require a fresh `Scratch/` verification at the wrapper's
  envelope). 0.3560 is sprint-050-verified, ~5x the wrapper's
  conservatism gap above the strict-margin threshold, and saves one
  sprint of the cascade vs the cautious step.
- **Wrapper behaviour at 0.3560:** the box-by-box certified `total`
  predicted at ~`1.008` from sprint 050's adaptive `mp.quad` gap of
  +1.131e-02 minus sprint 053's empirically-measured ~0.003
  conservatism gap. Strict-margin threshold is `1 + 10^(-30)`, so
  the headroom is ~`8 × 10^25` × the threshold; True return is
  essentially guaranteed (the only failure mode would be a
  K-monotonicity certificate failure on multiple boxes, which the
  wrapper handles by `_split_spec` retry plus drop-on-second-failure).
- **Explicit `axioms_used` change for V49 vs V48:** the Lean axiom set
  shape is identical (4 elements: `propext`, `Classical.choice`,
  `Quot.sound`, plus one per-`c` oracle axiom) but the per-`c` axiom
  swaps from `…V48.hEq15_oracle_certified_3554` to
  `…V49.hEq15_oracle_certified_3560`. `oracle_checks` swaps from
  invoking `certify_eq15_at_seed` to invoking `certify_eq15_at_3560`.
- **Next-sprint plan (sprint 056):** target `c = 1781/5000 = 0.3562`
  (next integer-10000ths past 0.3560). **Sprint 056 must first run a
  `Scratch/` script** invoking `certify_eq15(1781, 5000, dps=50,
  n_trunc=200)` and recording the wrapper's True/False result plus
  certified `total`. If True with margin, sprint 056 ships V50 with a
  sibling shim and `[[oracles]]` row. If False, the cascade has hit
  the wrapper's effective ceiling at 0.3560 and sprint 056 instead
  re-runs the wrapper at `(dps=100, n_trunc=500)` (per the bulletin's
  closing note line 300–304: "explicit headroom for a sixth sprint
  that *re-verifies* `c ∈ {0.3563, 0.3564, 0.3565}` at `mpmath
  dps=100, N=500`"). The cascade's hard ceiling is the literal `(15)`
  crossover at `~0.35635` (sprint 050); past that, the only routes
  are `proposal_001` (rejected) or a fresh proposal addressing
  proposal_001's five "Required to resubmit" points.
- **proposal_001 / proposal_002 status untouched.** Sprint 055 does
  NOT touch either proposal. The c-push routes through the
  pre-approved `[[oracles]]` channel; trust-base expansions remain
  out-of-scope for this sprint family.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V49` succeeds.
   Verify:
   ```bash
   bash korenblum/scripts/korenblum_lake_build.sh \
     Candidates/V49.lean
   ```
   exit code 0.

2. `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V49.lean`
   returns no matches.

3. The new shim `certify_eq15_at_3560` exists and behaves correctly in
   the canonical `uv run` environment:
   ```bash
   cd korenblum && \
   env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 -c "
   from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import (
       certify_eq15_at_3560, certify_eq15
   )
   from fractions import Fraction
   assert certify_eq15_at_3560() == Fraction(1, 1), 'shim must return Fraction(1)'
   assert certify_eq15(1780, 5000, dps=50, n_trunc=200) is True, 'wrapper must accept c=0.3560'
   assert certify_eq15(3565, 10000, dps=50, n_trunc=200) is False, 'falsifiability sanity check'
   print('OK')
   "
   ```
   prints `OK` and exits 0. The first assertion verifies the shim is
   wired correctly; the second re-confirms the wrapper accepts at the
   c-push target; the third re-confirms (regression check) that the
   wrapper still rejects past the literal `(15)` crossover, ensuring
   sprint 053's falsifiability sanity check still holds.

4. The canonical Evaluator invocation succeeds:
   ```bash
   env UV_CACHE_DIR=korenblum/.uv-cache \
     uv run ProofRefinement/Korenblum/Evaluator.py \
     --file ProofRefinement/Korenblum/Candidates/V49.lean
   ```
   exit code 0. Terminal output must include:
   - `oracle audit:  PASS`
   - `  PASS  hEq15_oracle_certified_3560: oracle=1 declared=1`
   - `score: 1780/5000` (or equivalent display showing
     `score > 1777/5000`)

5. The newest `Refinement_Log/log.jsonl` row records:
   - `pass: true`
   - `score: "1780/5000"` (this is **strictly greater than `1777/5000`**;
     verify both as a string match and as a Fraction comparison)
   - `axioms_used` array contains an entry whose `name` is
     `ProofRefinement.Korenblum.Candidates.V49.hEq15_oracle_certified_3560`
   - `axioms_used` does NOT contain any entry whose `name` ends in
     `hEq15_oracle_certified_3554` or `hEq15_seed_3554` (V49 must not
     transitively depend on the seed's per-`c` axiom)
   - `oracle_checks` is a non-empty array with exactly one element:
     `{axiom: "hEq15_oracle_certified_3560", bound_field:
     "eq15_lower_bound", declared: "1", oracle_bound: "1", ok: true}`

   Greppable check:
   ```bash
   tail -1 korenblum/ProofRefinement/Korenblum/Refinement_Log/log.jsonl \
     | python3 -c "
   import json, sys
   from fractions import Fraction
   r = json.loads(sys.stdin.read())
   assert r['pass'] is True, r
   assert r['candidate'] == 'Candidates/V49.lean', r['candidate']
   assert Fraction(r['score']) > Fraction('1777/5000'), r['score']
   names = [a['name'] for a in r['axioms_used']]
   assert any(n.endswith('hEq15_oracle_certified_3560') for n in names), names
   assert not any(n.endswith('hEq15_oracle_certified_3554') for n in names), names
   assert not any(n.endswith('hEq15_seed_3554') for n in names), names
   assert len(r['oracle_checks']) == 1, r['oracle_checks']
   oc = r['oracle_checks'][0]
   assert oc['axiom'] == 'hEq15_oracle_certified_3560', oc
   assert oc['ok'] is True, oc
   print('OK')
   "
   ```
   prints `OK`.

6. **Workspace import policy unchanged.** `lemma.toml`'s
   `[workspace_import_policy]` and `[import_policy]` blocks are
   byte-for-byte identical to their pre-sprint state. The only
   `lemma.toml` edits are (a) one new entry in
   `[seed_axioms].allowed`, and (b) one new `[[oracles]]` block
   appended after the existing one. Greppable check:
   ```bash
   git -C korenblum diff \
     ProofRefinement/Korenblum/lemma.toml \
     | grep -E '^[+-][^+-]' \
     | grep -vE 'hEq15_oracle_certified_3560|certify_eq15_at_3560|^[+]\s*$|^[+]\s*#' \
     | wc -l
   ```
   should be small (only the two block-additions and their boilerplate;
   no edits to `[import_policy]` or `[workspace_import_policy]`).

7. `git diff --stat` shows changes to exactly:
   - `ProofRefinement/Korenblum/Candidates/V49.lean` (NEW FILE),
   - `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
     (one new function `certify_eq15_at_3560` appended; no edits to
     existing `certify_eq15` or `certify_eq15_at_seed`),
   - `ProofRefinement/Korenblum/lemma.toml` (one new entry in
     `[seed_axioms].allowed`, one new `[[oracles]]` block),
   - `ProofRefinement/Korenblum/Bulletin.md` (one appended line),
   - `ProofRefinement/Korenblum/Experience.md` (one appended entry),
   - `ProofRefinement/Korenblum/Refinement_Log/log.jsonl` (one
     appended row from the Evaluator run),
   - `ProofRefinement/Korenblum/Refinement_Log/verdict_sprint_055.md`
     (NEW FILE from the Evaluator agent).

   No edits to `Proof/`, `KorenblumPaper/`, any prior
   `Candidates/V<n>.lean`, `lakefile.toml`, `pyproject.toml`,
   `Evaluator.py`, any prior `Sprint_Contracts/sprint_<NNN>.md`,
   or any `Proposals/proposal_<NNN>.md` (`Status:` fields
   untouched).

## Out of scope

- Push `c_value` past `1780/5000`. That is sprint 056's job. Aiming at
  `1781/5000 = 0.3562` requires a fresh `Scratch/` verification at the
  wrapper's envelope first because sprint 050's enumeration only
  covered integer-10000ths `{0.3554, 0.3556, 0.3558, 0.3560, 0.3565}`;
  0.3562 is interpolated by the bulletin but not directly verified. A
  combined verification + c-push would exceed the bounded-Generator-
  session budget and conflate two failure modes.
- Refactor `certify_eq15_at_seed` to be parametric. The per-`c`
  zero-argument shim convention is the Evaluator's expected calling
  discipline (`run_oracle_checks` invokes each oracle function with no
  arguments per `Evaluator.py:393`). A parametric refactor would force
  a wider Evaluator-side change. Per-`c` shims at ~15 lines each are
  acceptable boilerplate for the cascade size.
- Modify `proposal_001` or `proposal_002`'s `Status:` fields. Both
  remain at their current state (rejected and pending respectively;
  the human's note in `Bulletin.md` line 376 explicitly forbids
  autonomous `Status:` edits on these).
- Add any new Lean theorem to `Reduction.lean`, `Main.lean`, or any
  module under `KorenblumPaper/`. Zero edits to `Proof/` and
  `KorenblumPaper/`.
- File a third proposal. We are at 2/3 pending (proposal_001 rejected,
  proposal_002 deferred-pending) and the `[[oracles]]` channel
  consumed here is pre-approved per `AGENT_BRIEF.md` §"Numerical
  tooling".
- Update `pyproject.toml` or `.gitignore`. Sprint 054 landed both
  correctly for the wrapper's runtime dependencies.
- Edit `KorenblumPaper.PaperEq15` or `KorenblumPaper.OneModePaperBridge`.
  The `Eq15ScalarBound`-asserting axiom in V49 has the same Lean type
  shape as V48's; no paper-side change is required.

## Time budget

≤ 25 minutes runtime. Breakdown:

- ~5 min: append the new shim `certify_eq15_at_3560` to
  `rigorous_scalar.py` (~15 lines). Smoke-test the shim in `uv run`
  per acceptance criterion 3.
- ~5 min: append the `[[oracles]]` block and the
  `[seed_axioms].allowed` entry to `lemma.toml`.
- ~5 min: write `Candidates/V49.lean` (mirror V48 with the four
  one-line swaps). Run `lake build` per acceptance criterion 1.
- ~5 min: run the canonical Evaluator per acceptance criterion 4. The
  wrapper's wall-clock at `c = 0.3560` with `dps=50, n_trunc=200`
  should be ~38–45s per sprint 053's measurement at the seed (the box
  count and per-box cost are essentially independent of `c` within
  this small range).
- ~5 min: append the `Bulletin.md` line and the `Experience.md`
  entry; verify `git diff --stat` matches acceptance criterion 7.

## Stop conditions

- Acceptance criteria 1–7 all met:
  `STATUS=READY_FOR_EVALUATION`.

- Acceptance criterion 3 fails because
  `certify_eq15(1780, 5000, dps=50, n_trunc=200)` returns False (i.e.
  the wrapper's box-by-box conservatism gap is larger than the ~0.003
  sprint 053 measured, and exceeds the +0.0113 mpmath gap at this `c`):
  `STATUS=BLOCKED` with diagnostic. The next planner should either
  (a) re-target at the more conservative `c = 1779/5000` (sprint
  054's bulletin-line plan), or (b) increase the wrapper's precision
  envelope to `(dps=100, n_trunc=500)` and re-verify (per the
  bulletin's closing-note headroom, line 300–304). Do **not** ship
  V49 with a non-functional oracle — that would record a
  `oracle_checks: ok=false` row and leave V49's
  `hEq15_oracle_certified_3560` axiom uncertified.

- Acceptance criterion 3 fails because the wrapper rejects
  `(3565, 10000)` (i.e. the falsifiability sanity check fails):
  `STATUS=BLOCKED` — this is a critical rigour regression indicating
  the wrapper has been broken since sprint 053's verification. Do
  not proceed; the entire oracle channel needs re-verification.

- Acceptance criterion 5 fails because `axioms_used` contains an
  unexpected entry (e.g. some transitive consumer of
  `KorenblumPaper.PaperEq15` has injected a new `hEq15_*` axiom):
  `STATUS=BLOCKED` with diagnostic naming the unexpected axiom.

- The Evaluator reports `pass: true` but
  `score: "1779/5000"` (i.e. somehow the c-value was misread or the
  candidate-side `def c_value` lost a digit):
  `STATUS=BLOCKED` — re-check `Candidates/V49.lean` for the literal
  `1780 / 5000`, not `1779 / 5000`. (This is a copy-paste guard.)

- `lake build` succeeds but the Evaluator's `oracle_checks` reports
  `result: "missing-oracle-fn"` (mirroring sprint 053's gate-3
  failure): `STATUS=BLOCKED_NEEDS_HUMAN` — sprint 054's
  `pyproject.toml` has somehow regressed; do not paper over with a
  per-sprint shim, fix the canonical environment.

## Notes for the Generator

- **Mirror V48 exactly modulo four one-line swaps.** The Lean
  infrastructure is identical: same `valid_of_eq15` discharge body,
  same `Eq15ScalarBound K c_value` axiom shape, same
  `eq15_lower_bound : ℝ := 1` declaration. The only differences are
  the namespace, the `c_value`, the axiom name, and the `@parent`
  comment.

- **Per-`c` shim, not parametric refactor.** The existing
  `certify_eq15_at_seed` shim convention is what the Evaluator
  expects (`Evaluator.py:393` invokes oracles with no arguments).
  Adding `certify_eq15_at_3560` as a sibling — calling
  `certify_eq15(1780, 5000, dps=50, n_trunc=200)` directly with the
  same `RuntimeError`-on-False discipline — is the right move.
  Refactoring `certify_eq15_at_seed` to take a parameter would
  require Evaluator-side changes that exceed this sprint's scope.

- **Sprint 050's table is the authoritative numerical witness.**
  `Scratch/sprint_050_eq15_crossover_pinpoint.txt` reports gap
  `+1.131e-02` at `c = 0.3560`, mpmath `dps=50, N_TRUNC=200`. Sprint
  053's Experience entry empirically measures the box-by-box
  wrapper's conservatism gap at ~0.003 below adaptive `mp.quad` at
  the seed; the gap should be similar at 0.3560 since the box count
  and per-box cost are essentially independent of `c` within this
  small range.

- **Falsifiability re-check is non-negotiable.** Acceptance
  criterion 3's third assertion (`certify_eq15(3565, 10000, dps=50,
  n_trunc=200) is False`) is the load-bearing falsifiability check
  for the entire `[[oracles]]` channel. If it ever returns True, the
  wrapper has lost its rigour and the oracle channel is no longer
  trustworthy. Do not skip this check; do not weaken it.

- **The Evaluator reuses `eq15_lower_bound`-named declarations
  per-candidate.** V48 declares `def eq15_lower_bound : ℝ := 1` and
  V49 will declare the same. There is no namespace collision because
  each candidate lives in its own namespace
  (`...Candidates.V48` vs `...Candidates.V49`); the Evaluator's
  `bound_field` lookup is per-candidate-module per
  `Evaluator.py:load_workspace_config`. So you can reuse the same
  `bound_field = "eq15_lower_bound"` name in the new `[[oracles]]`
  block without colliding with the existing one.

- **Score must be `1780/5000`, not `0.3560` decimal.** The Evaluator
  evaluates `score_expr = "c_value"` against the candidate-side
  `def c_value : ℝ := 1780 / 5000` and reports the ratio as a
  Fraction. `1780/5000` reduces to `89/250` in lowest terms, but the
  log row may keep it as `1780/5000`; either form satisfies
  `Fraction(score) > Fraction("1777/5000")`. Acceptance criterion 5
  uses the Fraction comparison, not a string match.

- **Bulletin row format.** Match the existing `## Recent events`
  block style: a single line beginning with `sprint_055 PASS:` (or
  `BLOCKED`) and ending with the score. Do not reflow.

- **No Scratch script needed for this sprint.** Sprint 050 already
  verified `c = 0.3560` is in the positive-margin region with
  mpmath `dps=50, N_TRUNC=200`. The wrapper at the same envelope
  is what the oracle channel actually invokes; the wrapper's
  conservatism gap was measured by sprint 053. No new numerical
  exploration is required for the c-push to 0.3560 specifically.
  *Sprint 056* will need a Scratch script for `c = 0.3562` because
  that point is not in sprint 050's enumeration.
