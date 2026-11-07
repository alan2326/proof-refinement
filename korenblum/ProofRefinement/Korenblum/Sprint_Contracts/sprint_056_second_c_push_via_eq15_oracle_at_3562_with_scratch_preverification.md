# Sprint 056: Second c-push above the seed via the `eq15` oracle channel — ship `Candidates/V50.lean` at `c_value = 1781/5000 = 0.3562` after a `Scratch/` pre-verification of the wrapper at the new c

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V49.lean` (the first c-pushed candidate sprint
055 landed at `c = 1780/5000 = 0.3560`)
**Target file**: `Candidates/V50.lean`
**Direction**: raise-c — second sprint to actually push `c_value` above the
seed. Routes through the same pre-approved `[[oracles]]` channel as sprint 055
but with one critical addition the bulletin's "verify before Lean" rule
(Bulletin.md lines 95–104) requires: a `Scratch/` script that actually invokes
`certify_eq15(1781, 5000, dps=50, n_trunc=200)` and records the wrapper's
True/False return plus certified `total` BEFORE any Lean file is written. If
the Scratch step shows the wrapper rejects at this `c`, the contract's stop
conditions name the explicit fallback (finer denominator at
`c = 0.35610 = 35610/100000`, halfway between verified 0.3560 and proposed
0.3562) so the sprint can still ship a c-push without conflating two failure
modes in one Generator session.

## Goal

Ship `Candidates/V50.lean` proving
`theorem korenblum_constant_search : ValidKorenblumBound c_value` at
`c_value := 1781 / 5000 = 0.3562` (or the fallback `35610/100000 = 0.35610` if
the Scratch sub-step rejects), discharging the `(15)` premise via a new
oracle-registered axiom `hEq15_oracle_certified_3562` (resp.
`hEq15_oracle_certified_35610`). Score must report a value strictly greater
than `1780/5000` (i.e. V49's score) for this to count as the workspace's
second genuine c-push.

## Why

### The cascade is live, and the next safe step is +0.0002

Sprint 055 landed the workspace's first c-push above the seed in 55 sprints
(V49 at `c = 1780/5000 = 0.3560`, score `89/250 > 1777/5000`,
`oracle_checks: ok=true` per the latest `log.jsonl` row). The
`[[oracles]]` channel works end-to-end in the canonical `uv run`
environment; the per-`c` shim convention scales by ~15 lines per sprint;
trust expansion is one new entry in `[seed_axioms].allowed` plus one new
`[[oracles]]` block per c-push. **The plumbing is settled.** What remains
is execution: each sprint pushes `c` by the smallest verifiable
increment, the bulletin gains one row, and the harness converges on the
literal `(15)` crossover at `c ≈ 0.35635` (sprint 050's pinpoint).

The bulletin's second 2026-05-02 directive (lines 271–280) explicitly
prescribes the cascade `0.3554 → 0.3558 → 0.3560 → 0.3562 → 0.3564?`
with margins from sprint 050's mpmath `dps=50, N_TRUNC=200` table. Sprint
055 shipped the second step (collapsing 0.3558 and 0.3560 into one
sprint per the planner's expected-value calculation). Sprint 056's job is
the third step: `c = 1781/5000 = 0.3562`, the next integer-10000ths past
sprint 055's `c = 0.3560`.

### Why c = 1781/5000 = 0.3562 (cautious route, with Scratch pre-verification), not other candidates

The user's sprint instructions framed this as "cautious vs aggressive at
0.3562" plus "different denominator". I considered three structurally
distinct candidate sprint shapes (planner ultrathink, per
`KORENBLUM_PROOF_REFINEMENT_HARNESS.md`):

**C1 — `c = 1781/5000 = 0.3562`, AGGRESSIVE (no Scratch pre-verification).**
Just write the Lean candidate, the shim, the `[[oracles]]` row, and rely
on the wrapper to either certify or reject. **Strongest objection
(decisive):** this route directly violates Bulletin.md line 99: *"every
sprint that proposes a numerical headroom must include a `Scratch/`
script that confirms the inequality holds at the proposed
`(c, parameters)` with a stated margin, **before** writing any Lean"*.
The bulletin's working practice is non-negotiable. Sprint 050's mpmath
table verified the `(15)` gap at `{0.3554, 0.3556, 0.3558, 0.3560,
0.3565}`; **0.3562 is not in the table**. The bulletin (line 280)
interpolates "`gap ~+0.008`", and a planner can extrapolate further
(linear interpolation between sprint 050's gap +1.131e-02 at 0.3560 and
−3.598e-04 at 0.3565 puts the gap at 0.3562 at roughly
+1.131e-02 + (2/5) × (−3.598e-04 − 1.131e-02) ≈ +6.6e-03; subtract
sprint 053's ~0.003 box-by-box conservatism, certified ~+3.6e-03).
That's predicted-positive but it has not been verified. Demoted.

**C2 — `c = 1781/5000 = 0.3562`, CAUTIOUS (with Scratch pre-verification)
(CHOSEN).** Same target c as C1, but adds an explicit `Scratch/`
pre-step that runs `certify_eq15(1781, 5000, dps=50, n_trunc=200)` and
records True/False plus certified `total` BEFORE writing the Lean file
or modifying `lemma.toml`. **Strongest objection:** the Scratch step
takes one extra ~38–45s wrapper invocation in the Generator session.
**Resolution:** that's exactly the cost the bulletin's "verify before
Lean" rule is asking the harness to absorb. A 40-second Scratch
verification that catches a wrapper rejection BEFORE writing 60+ lines
of Lean / TOML / Experience text is far cheaper than a `BLOCKED` sprint
that has to undo all those edits. The Scratch script also doubles as
the documentation row sprint 057+ will reuse when targeting 0.3563 (the
script can be parameterised). Adopting the cautious route this sprint
sets the precedent for every c-push past sprint 050's verified table.

**C3 — `c = 35610/100000 = 0.35610`, finer-denominator fallback (DEMOTED
to fallback role).** This is a +0.0001 step instead of +0.0002, halfway
between sprint 055's verified-positive 0.3560 and the proposed 0.3562.
Linear interpolation puts mpmath gap at ~+8.85e-03 (between 1.131e-02
at 0.3560 and ~+6.6e-03 at 0.3562), certified ~+5.85e-03 after
conservatism — comfortably positive. **Strongest objection:** burns one
sprint per +0.0001 of `c` instead of +0.0002, doubling the cascade
length to the crossover. **Resolution:** this is the right *fallback*
if C2's Scratch step rejects 0.3562, but it should not be the *primary*
target — sprint 055 demonstrated that +0.0002 steps work, and the
bulletin's example schedule line 279 explicitly names 0.3562 as the
next step. Adopt as the contract's named fallback, not the primary
target.

**C4 — Pure Scratch sweep across `{0.3561, 0.3562, 0.3563, 0.3564}` with
no Lean candidate (DEMOTED).** Pure exploration, no c-push deliverable.
**Strongest objection (decisive):** sprints 048–051 produced four
roadmap-only sprints in a row that the bulletin explicitly criticised
(lines 219–229: *"sprints 048–051 are now four roadmap-only sprints in
a row that produced `Scratch/` evidence and one pending `Proposals/`
entry but **zero changes to `lemma.toml` and zero new candidates**"*).
A second Scratch-only sprint while the cascade is live would re-commit
that mistake. The Scratch verification needs to be *part of* a c-push
sprint, not a standalone sprint. Demoted.

**Verdict.** C2 is strictly better than C1 on bulletin compliance
("verify before Lean" rule), strictly better than C3 on cascade
economics (+0.0002 per sprint vs +0.0001), and strictly better than C4
on incrementalism (ships a candidate, not just `Scratch/` files). C3 is
adopted as the named fallback in the contract's stop conditions so a
wrapper rejection at 0.3562 can still ship a smaller c-push without a
second sprint.

### What success looks like

Score `1781/5000 > 1780/5000` (or fallback `35610/100000 > 1780/5000`).
Axiom set is exactly `{propext, Classical.choice, Quot.sound,
hEq15_oracle_certified_3562}` (resp. `…_35610`), with the new axiom
registered under `[[oracles]]` and discharged at Evaluator-time by
`Numerical_Library.rigorous_scalar.certify_eq15_at_3562` (resp.
`…_at_35610`). This is the harness's second c-push, and the
*continuation* of the cascade — i.e. the bulletin's "incrementalism is
the point of this harness, not a fallback" (line 288) is now a
demonstrated working practice rather than a directive.

## Concrete edits expected

The sprint splits into **two phases**: (A) Scratch pre-verification, and
(B) Lean/TOML/Experience materialisation. Phase B's edits are conditional
on phase A's wrapper return.

### Phase A — Scratch pre-verification (run BEFORE phase B)

#### A.1 `ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py` (NEW FILE)

Mirror the structure of `Scratch/sprint_050_eq15_crossover_pinpoint.py`
but invoke the **registered wrapper** `certify_eq15` rather than
recomputing the gap from scratch with mpmath directly. The point is to
verify that the wrapper — which is what the Evaluator actually invokes —
accepts at `(1781, 5000, dps=50, n_trunc=200)`, not just that mpmath's
adaptive `mp.quad` produces a positive gap. (Sprint 053 measured ~0.003
box-by-box conservatism between the wrapper and `mp.quad`; we need to
verify the certified `total` after that conservatism is still positive.)

The script body:

```python
"""
Sprint 056 wrapper pre-verification at c = 1781/5000 = 0.3562.

Bulletin.md line 99: every c-push sprint must include a Scratch/ script
that confirms the wrapper accepts at the proposed (c, parameters) with
a stated margin BEFORE any Lean file is written. Sprint 050's mpmath
dps=50, N_TRUNC=200 table verified gap >0 at c in {0.3554, 0.3556,
0.3558, 0.3560} and gap <0 at c = 0.3565. The point c = 0.3562 is NOT
in that table; this script fills the gap.

The script invokes the registered wrapper certify_eq15 directly (the
same call sequence the Evaluator's certify_eq15_at_3562 shim will use
in phase B), records True/False, and also runs build_adaptive_certificate
to extract the certified `total_mass_lower` so the conservatism gap can
be reported. Falsifiability cross-checks at c = 0.3565 (must be False)
and c = 0.3560 (must be True, regression check on sprint 055's win).

Run: `cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py`

Output is appended to sprint_056_eq15_wrapper_pre_verification.txt for
the Generator's `STATUS=...` decision.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

# Ensure ProofRefinement is on the path when invoked from the repo root.
sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import (
    certify_eq15,
    build_adaptive_certificate,
)


def report(c_num: int, c_den: int, dps: int, n_trunc: int) -> dict:
    """Run wrapper and certificate; return a dict of metrics for the txt log."""
    print(f"\n=== c = {c_num}/{c_den} = {c_num/c_den:.6f}, dps={dps}, n_trunc={n_trunc} ===")
    sys.stdout.flush()
    accepted = certify_eq15(c_num, c_den, dps=dps, n_trunc=n_trunc)
    print(f"  certify_eq15(...) returned: {accepted}")
    sys.stdout.flush()
    cert = build_adaptive_certificate(Fraction(c_num, c_den), dps=dps, n_trunc=n_trunc)
    total = cert.total_mass_lower.to_fraction()
    print(f"  certified total_mass_lower = {float(total):.12f}")
    print(f"  boxes used = {len(cert.boxes)}")
    margin = float(total) - 1.0
    print(f"  margin (total - 1) = {margin:+.6e}")
    sys.stdout.flush()
    return {
        "c_num": c_num,
        "c_den": c_den,
        "c_decimal": c_num / c_den,
        "dps": dps,
        "n_trunc": n_trunc,
        "accepted": accepted,
        "total_lower": float(total),
        "margin": margin,
        "boxes": len(cert.boxes),
    }


def main() -> int:
    print("Sprint 056 — wrapper pre-verification (cautious route per Bulletin line 99)")
    print("Targets: 1781/5000 (primary), 35610/100000 (fallback) per sprint contract")
    print("Regressions: 1780/5000 (must accept, sprint 055), 3565/10000 (must reject, sprint 053)")

    # Primary target first so its result anchors the Generator's decision.
    primary = report(1781, 5000, dps=50, n_trunc=200)
    fallback = report(35610, 100000, dps=50, n_trunc=200)
    regression_pos = report(1780, 5000, dps=50, n_trunc=200)
    regression_neg = report(3565, 10000, dps=50, n_trunc=200)

    print("\n=== Summary ===")
    print(f"primary    (c=0.3562):  accepted={primary['accepted']}, "
          f"margin={primary['margin']:+.4e}")
    print(f"fallback   (c=0.35610): accepted={fallback['accepted']}, "
          f"margin={fallback['margin']:+.4e}")
    print(f"regr+ (c=0.3560, sp055): accepted={regression_pos['accepted']}, "
          f"margin={regression_pos['margin']:+.4e}")
    print(f"regr- (c=0.3565, sp053): accepted={regression_neg['accepted']}, "
          f"margin={regression_neg['margin']:+.4e}")

    # Hard guardrail: regression checks must hold or the wrapper has lost rigour.
    if not regression_pos['accepted']:
        print("\nFATAL: regression check at c=0.3560 failed. The wrapper has regressed since sprint 055; do not proceed.")
        return 2
    if regression_neg['accepted']:
        print("\nFATAL: regression check at c=0.3565 unexpectedly succeeded. The wrapper's falsifiability has been broken.")
        return 2

    # Decision tree per the sprint contract's stop conditions.
    if primary['accepted']:
        print("\nDECISION: ship Lean candidate at c=1781/5000=0.3562 (primary target).")
        return 0
    if fallback['accepted']:
        print("\nDECISION: ship Lean candidate at c=35610/100000=0.35610 (fallback target — primary rejected).")
        return 1
    print("\nDECISION: BLOCKED — both primary and fallback rejected. Cascade has hit wrapper ceiling at sprint 055's c=0.3560.")
    return 3


if __name__ == "__main__":
    raise SystemExit(main())
```

#### A.2 `ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.txt` (NEW FILE)

Run the Scratch script via the canonical `uv run` invocation and tee
stdout to this file. The exit code drives the Generator's phase-B branch.
Suggested invocation:

```bash
cd korenblum && \
env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 \
  ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py \
  2>&1 | tee ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.txt
```

The file's last line must be one of:
- `DECISION: ship Lean candidate at c=1781/5000=0.3562 (primary target).` → phase B uses 1781/5000 / `_3562`
- `DECISION: ship Lean candidate at c=35610/100000=0.35610 (fallback target — primary rejected).` → phase B uses 35610/100000 / `_35610`
- `DECISION: BLOCKED — both primary and fallback rejected. Cascade has hit wrapper ceiling at sprint 055's c=0.3560.` → `STATUS=BLOCKED_NEEDS_HUMAN`, no phase B
- `FATAL: …` → `STATUS=BLOCKED`, no phase B (rigour regression on the wrapper)

### Phase B — Lean/TOML/Experience materialisation (only if phase A returns 0 or 1)

Phase B mirrors sprint 055's edits exactly, modulo the `(c_num, c_den)`
swap dictated by phase A's exit code. The four edits below use `<C>` as
a placeholder for the chosen c-suffix (`3562` for primary,
`35610` for fallback) and `<C_NUM>/<C_DEN>` for the numeric pin
(`1781/5000` or `35610/100000`).

#### B.1 `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`

Append a sibling zero-argument shim `certify_eq15_at_<C>()` directly
after the existing `certify_eq15_at_3560()` shim (currently lines
979–1013). Mirror that shim byte-for-byte modulo the `(c_num, c_den)`
parameter pin and the error message:

```python
def certify_eq15_at_<C>() -> Fraction:
    """
    Sprint 056 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_<C>``.

    Calls ``certify_eq15(<C_NUM>, <C_DEN>, dps=50, n_trunc=200)``; on
    True, returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_<C>``.

    Pre-verified by ``Scratch/sprint_056_eq15_wrapper_pre_verification.py``
    at this c with the same envelope. Sprint 050's mpmath table verified
    the (15) gap at adjacent points {0.3560 (+1.131e-02), 0.3565
    (-3.598e-04)}; the wrapper at this c sits inside that interval per
    the Scratch pre-verification's recorded margin.
    """
    if not certify_eq15(<C_NUM>, <C_DEN>, dps=50, n_trunc=200):
        raise RuntimeError(
            "certify_eq15(<C_NUM>, <C_DEN>, dps=50, n_trunc=200) returned False; "
            "wrapper cannot reproduce the Scratch pre-verification's positive "
            "margin at c = <C_NUM>/<C_DEN> under the registered envelope. Refusing "
            "to certify the Lean axiom `hEq15_oracle_certified_<C>` to keep the "
            "trust surface honest."
        )
    return Fraction(1, 1)
```

**Do NOT** refactor the existing per-`c` shims to be parametric. The
per-`c` zero-argument shim convention remains the Evaluator's expected
calling discipline (`run_oracle_checks` invokes each oracle function
with no arguments). Per-`c` shims at ~15 lines each are acceptable
boilerplate for the cascade size.

#### B.2 `ProofRefinement/Korenblum/lemma.toml`

Append a sibling `[[oracles]]` row directly after the existing
`eq15_certified_at_3560` block (currently ending at line 98). Add
`"hEq15_oracle_certified_<C>"` to `[seed_axioms].allowed`, right after
the existing `"hEq15_oracle_certified_3560"` entry. The combined diff:

```toml
 [seed_axioms]
 allowed = [
   …
   "hEq15_oracle_certified_3554",
   "hEq15_oracle_certified_3560",
+
+  # Sprint 056: the second c-push sibling, pinning c = <C_NUM>/<C_DEN>.
+  # Same Lean axiom shape and same registered wrapper as the 3554/3560
+  # siblings; the Scratch pre-verification at
+  # `Scratch/sprint_056_eq15_wrapper_pre_verification.txt` records the
+  # wrapper's True return and certified margin at this c.
+  "hEq15_oracle_certified_<C>",
 ]
 …
 [[oracles]]
 axiom = "hEq15_oracle_certified_3560"
 bound_field = "eq15_lower_bound"
 oracle_fn = "rigorous_scalar.certify_eq15_at_3560"
+
+# Sprint 056: second c-push oracle. Pins `certify_eq15` at
+# `(c_num, c_den, dps, n_trunc) = (<C_NUM>, <C_DEN>, 50, 200)` via the
+# zero-argument shim `certify_eq15_at_<C>`. The wrapper's positive return
+# at this `(c_num, c_den)` is pre-verified by
+# `Scratch/sprint_056_eq15_wrapper_pre_verification.py`.
+
+[[oracles]]
+axiom = "hEq15_oracle_certified_<C>"
+bound_field = "eq15_lower_bound"
+oracle_fn = "rigorous_scalar.certify_eq15_at_<C>"
```

#### B.3 `ProofRefinement/Korenblum/Candidates/V50.lean` (NEW FILE)

Mirror `Candidates/V49.lean` byte-for-byte modulo:

- `@parent V48` → `@parent V49`
- `namespace ...V49` → `namespace ...V50`
- `def c_value : ℝ := 1780 / 5000` → `def c_value : ℝ := <C_NUM> / <C_DEN>`
- `axiom hEq15_oracle_certified_3560` → `axiom hEq15_oracle_certified_<C>`
- the discharge body's reference to the axiom name updates correspondingly
- comments updated to refer to the second c-push and the Scratch
  pre-verification

Concretely (showing the primary `c = 1781/5000` shape; fallback shape is
identical with the four substitutions):

```lean
-- @parent V49
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V50

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
Second c-push above the seed in 56 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48 / V49, but with the literal
`(15)` premise pinned at `c = 1781/5000 = 0.3562` (= one
integer-10000ths past sprint 055's c = 0.3560, the next safe step in
the bulletin's directive lines 271–280) instead of sprint 055's
`c = 1780/5000`. The `(15)` premise is discharged by the registered
oracle `eq15_certified_at_3562` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1781, 5000, 50, 200)`; the wrapper's
positive return at this c was pre-verified by
`Scratch/sprint_056_eq15_wrapper_pre_verification.{py,txt}` (a step
sprint 055 did not need because sprint 050's mpmath table already
covered c = 0.3560 directly; sprint 056 needs it because c = 0.3562 is
not in sprint 050's enumeration).
-/
def c_value : ℝ := 1781 / 5000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/--
Sprint 056 oracle bound-field. Identical declaration to V48 / V49; the
Evaluator compares the per-candidate `oracle_fn`'s returned Fraction
against this `def` via `oracle_bound <= declared`. Sharing the same
`bound_field` name across V48 / V49 / V50 is permitted because each
`[[oracles]]` row carries its own `oracle_fn` (the per-`c` shim).
-/
def eq15_lower_bound : ℝ := 1

/--
Oracle-backed external input: Wang's equation `(15)` at
`c = 1781/5000 = 0.3562`. Discharged by the registered oracle
`eq15_certified_at_3562` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (1781, 5000, 50, 200)`.

Lean axiom shape is byte-for-byte identical to V49's
`hEq15_oracle_certified_3560` modulo the `c_value` swap. Trust is
grounded in the same `certify_eq15` verified-interval wrapper, plus
the Scratch pre-verification recorded at
`Scratch/sprint_056_eq15_wrapper_pre_verification.txt`.
-/
axiom hEq15_oracle_certified_3562 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_3562 K)

end ProofRefinement.Korenblum.Candidates.V50
```

#### B.4 `ProofRefinement/Korenblum/Bulletin.md`

Append exactly one line to the `## Recent events` block on success:

```text
sprint_056 PASS: second c-push above the seed — V50 ships at c_value = <C_NUM>/<C_DEN> with axioms_used = {seed} ∪ {hEq15_oracle_certified_<C>}; oracle_checks records successful invocation of `rigorous_scalar.certify_eq15_at_<C>` (oracle_bound=1, declared=1, ok=true); wrapper acceptance pre-verified by `Scratch/sprint_056_eq15_wrapper_pre_verification.{py,txt}` BEFORE writing Lean (per Bulletin.md line 99); score <C_NUM>/<C_DEN> > 1780/5000 — second consecutive c-push row in log.jsonl, demonstrating the cascade is sustainable on the +0.0002 (or +0.0001 fallback) increment; sprint 057 can either continue the cascade (target c = 1782/5000 = 0.3564 if 0.3562 landed; or 1781/5000 = 0.3562 if fallback landed) with a Scratch pre-verification, or — if approaching the literal (15) crossover at ~0.35635 per sprint 050 — prepare the dps=100, n_trunc=500 precision-envelope upgrade per Bulletin.md line 300–304
```

Do not reflow.

#### B.5 `ProofRefinement/Korenblum/Experience.md`

Append a new dated entry `### 2026-05-02 sprint_056` summarising:

- **What sprint 055 left undone:** sprint 055 demonstrated the cascade
  works at +0.0002 increments (V49 at c = 0.3560 from V48 at c = 0.3554)
  but did NOT need a `Scratch/` pre-verification because sprint 050's
  mpmath table already covered c = 0.3560 directly. The next step
  (c = 0.3562) is *not* in sprint 050's enumeration, so sprint 056 is
  the first c-push that *requires* Scratch pre-verification per
  Bulletin.md line 99.
- **The c-push delivered:** `c = <C_NUM>/<C_DEN>` (primary or fallback,
  depending on phase A's wrapper return). Mirrors V49 byte-for-byte
  modulo the c-value and axiom-name swaps.
- **Why cautious-with-Scratch over aggressive:** the planner's
  ultrathink (see contract's Why section) compared four candidates —
  C1 (aggressive 0.3562 no Scratch, demoted as Bulletin line 99
  violation), C2 (cautious 0.3562 with Scratch, CHOSEN), C3 (finer
  denominator 0.35610, demoted to fallback role), C4 (Scratch-only
  no candidate, demoted as repeating sprints 048–051's mistake).
  C2's +40s Scratch step is the cheapest insurance against a wrapper
  rejection that would otherwise force a `BLOCKED` sprint after Lean
  is already written.
- **Phase A (Scratch) results:** record the four wrapper invocations'
  True/False returns and their certified margins. The two regression
  checks (c = 0.3560 must accept, c = 0.3565 must reject) are the
  rigour guardrails — if either fails, the entire `[[oracles]]`
  channel needs re-verification.
- **Phase B (Lean) results:** record the standard sprint-055-shaped
  evidence (axioms_used, oracle_checks, score, log.jsonl row).
  Highlight that the `axioms_used` set shape is identical to sprint
  055 modulo the per-`c` axiom name swap.
- **Next-sprint plan (sprint 057):** depends on which c sprint 056
  landed.
  - **If 056 landed at primary 0.3562**, target c = 1782/5000 = 0.3564
    (next +0.0002). Sprint 050's table puts gap +1.131e-02 at 0.3560
    and -3.598e-04 at 0.3565; linear interpolation puts gap at 0.3564
    at roughly +1.131e-02 + (4/5) × (-1.167e-02) ≈ +1.93e-03 — much
    tighter than 0.3562's predicted ~+6.6e-03. Sprint 057 *must* run a
    Scratch pre-verification with dps=50,N=200 first; if certified
    `total - 1` is below ~3e-3, sprint 057 should also try
    dps=100,n_trunc=500 (per Bulletin line 300–304's headroom note)
    before shipping.
  - **If 056 landed at fallback 0.35610**, target c = 1781/5000 =
    0.3562 (the missed primary). Sprint 056's Scratch script already
    proved that's a wrapper rejection at dps=50,n_trunc=200, so
    sprint 057 must FIRST upgrade the envelope to dps=100,n_trunc=500
    and re-verify. If still rejected, the cascade has hit the
    box-by-box conservatism ceiling and sprint 057 must instead
    target an even finer denominator like c = 35615/100000 = 0.35615
    or shift to addressing proposal_001's "Required to resubmit"
    points.
- **proposal_001 / proposal_002 status untouched.** Sprint 056 does
  NOT touch either proposal. The c-push routes through the
  pre-approved `[[oracles]]` channel; trust-base expansions remain
  out-of-scope for this sprint family.

## Acceptance criteria

### Phase A — Scratch pre-verification

A1. `ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py`
    exists and executes successfully via the canonical `uv run`
    invocation:

    ```bash
    cd korenblum && \
    env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 \
      ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py \
      2>&1 | tee ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.txt
    ```

    exit code is 0 (primary accepted), 1 (fallback accepted), 2 (FATAL
    regression), or 3 (cascade ceiling). Record the exit code and the
    final `DECISION: …` line in the Generator's `STATUS=…` summary.

A2. The two regression checks pass:
    - `certify_eq15(1780, 5000, dps=50, n_trunc=200) is True` (sprint
      055's win, must still hold)
    - `certify_eq15(3565, 10000, dps=50, n_trunc=200) is False` (sprint
      053's falsifiability check, must still hold)

    These are *load-bearing*: a regression on either means the wrapper
    has lost rigour and phase B must NOT proceed.

A3. The `Scratch/sprint_056_eq15_wrapper_pre_verification.txt` file
    contains the four `=== c = … ===` blocks (primary, fallback, two
    regressions) with `accepted`, `total_lower`, `margin`, `boxes`
    fields recorded for each.

### Phase B — Lean / TOML / Experience materialisation
### (skip if phase A returned exit codes 2 or 3)

B1. `lake build ProofRefinement.Korenblum.Candidates.V50` succeeds:
    ```bash
    bash korenblum/scripts/korenblum_lake_build.sh \
      Candidates/V50.lean
    ```
    exit code 0.

B2. `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V50.lean`
    returns no matches.

B3. The new shim `certify_eq15_at_<C>` exists and behaves correctly in
    the canonical `uv run` environment:
    ```bash
    cd korenblum && \
    env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 -c "
    from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import (
        certify_eq15_at_<C>, certify_eq15
    )
    from fractions import Fraction
    assert certify_eq15_at_<C>() == Fraction(1, 1), 'shim must return Fraction(1)'
    assert certify_eq15(<C_NUM>, <C_DEN>, dps=50, n_trunc=200) is True, 'wrapper must accept c=<C_DEC>'
    assert certify_eq15(3565, 10000, dps=50, n_trunc=200) is False, 'falsifiability sanity check'
    print('OK')
    "
    ```
    prints `OK` and exits 0.

B4. The canonical Evaluator invocation succeeds:
    ```bash
    env UV_CACHE_DIR=korenblum/.uv-cache \
      uv run ProofRefinement/Korenblum/Evaluator.py \
      --file ProofRefinement/Korenblum/Candidates/V50.lean
    ```
    exit code 0. Terminal output must include:
    - `oracle audit:  PASS`
    - `  PASS  hEq15_oracle_certified_<C>: oracle=1 declared=1`
    - `score: <C_NUM>/<C_DEN>` (or equivalent display showing
      `score > 1780/5000`)

B5. The newest `Refinement_Log/log.jsonl` row records:
    - `pass: true`
    - `score`: a Fraction strictly greater than `1780/5000`
    - `axioms_used` array contains an entry whose `name` is
      `ProofRefinement.Korenblum.Candidates.V50.hEq15_oracle_certified_<C>`
    - `axioms_used` does NOT contain any entry whose `name` ends in
      `hEq15_oracle_certified_3560`, `hEq15_oracle_certified_3554`, or
      `hEq15_seed_3554` (V50 must not transitively depend on prior
      per-`c` axioms)
    - `oracle_checks` is a non-empty array with exactly one element:
      `{axiom: "hEq15_oracle_certified_<C>", bound_field:
      "eq15_lower_bound", declared: "1", oracle_bound: "1", ok: true}`

    Greppable check:
    ```bash
    tail -1 korenblum/ProofRefinement/Korenblum/Refinement_Log/log.jsonl \
      | python3 -c "
    import json, sys
    from fractions import Fraction
    r = json.loads(sys.stdin.read())
    assert r['pass'] is True, r
    assert r['candidate'] == 'Candidates/V50.lean', r['candidate']
    assert Fraction(r['score']) > Fraction('1780/5000'), r['score']
    names = [a['name'] for a in r['axioms_used']]
    assert any('hEq15_oracle_certified_' in n for n in names), names
    for stale in ('hEq15_oracle_certified_3560', 'hEq15_oracle_certified_3554', 'hEq15_seed_3554'):
        assert not any(n.endswith(stale) for n in names), (stale, names)
    assert len(r['oracle_checks']) == 1, r['oracle_checks']
    assert r['oracle_checks'][0]['ok'] is True, r['oracle_checks'][0]
    print('OK')
    "
    ```

B6. **Workspace import policy unchanged.** `lemma.toml`'s
    `[workspace_import_policy]` and `[import_policy]` blocks are
    byte-for-byte identical to their pre-sprint state. The only
    `lemma.toml` edits are (a) one new entry in
    `[seed_axioms].allowed`, and (b) one new `[[oracles]]` block
    appended after the existing one.

B7. `git diff --stat` shows changes to exactly:
    - `ProofRefinement/Korenblum/Candidates/V50.lean` (NEW FILE),
    - `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
      (one new shim function appended; no edits to existing
      `certify_eq15`, `certify_eq15_at_seed`, or `certify_eq15_at_3560`),
    - `ProofRefinement/Korenblum/lemma.toml` (one new entry in
      `[seed_axioms].allowed`, one new `[[oracles]]` block),
    - `ProofRefinement/Korenblum/Bulletin.md` (one appended line),
    - `ProofRefinement/Korenblum/Experience.md` (one appended entry),
    - `ProofRefinement/Korenblum/Refinement_Log/log.jsonl` (one
      appended row from the Evaluator run),
    - `ProofRefinement/Korenblum/Refinement_Log/verdict_sprint_056.md`
      (NEW FILE from the Evaluator agent),
    - `ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.py`
      (NEW FILE),
    - `ProofRefinement/Korenblum/Scratch/sprint_056_eq15_wrapper_pre_verification.txt`
      (NEW FILE).

    No edits to `Proof/`, `KorenblumPaper/`, any prior
    `Candidates/V<n>.lean`, `lakefile.toml`, `pyproject.toml`,
    `Evaluator.py`, any prior `Sprint_Contracts/sprint_<NNN>.md`, or
    any `Proposals/proposal_<NNN>.md` (`Status:` fields untouched).

## Out of scope

- Push `c_value` past `1781/5000` in this sprint. The next +0.0002
  step (c = 1782/5000 = 0.3564) approaches the literal (15) crossover
  at ~0.35635; per sprint 050's pinpoint, the gap at 0.3564 is
  predicted at ~+1.93e-03 raw mpmath, which after sprint 053's ~0.003
  conservatism would be NEGATIVE under the wrapper's envelope. That
  case requires the dps=100,n_trunc=500 precision upgrade (Bulletin
  line 300–304) and is sprint 057's job.
- Refactor any of the existing per-`c` shims to be parametric. Per-`c`
  shims at ~15 lines each are acceptable boilerplate.
- Modify `proposal_001` or `proposal_002`'s `Status:` fields. Both
  remain at their current state (rejected and pending respectively).
- Add any new Lean theorem to `Reduction.lean`, `Main.lean`, or any
  module under `KorenblumPaper/`. Zero edits to `Proof/` and
  `KorenblumPaper/`.
- File a new proposal. The c-push routes through the pre-approved
  `[[oracles]]` channel.
- Update `pyproject.toml` or `.gitignore`. Sprint 054 landed both
  correctly.
- Edit `KorenblumPaper.PaperEq15` or `KorenblumPaper.OneModePaperBridge`.

## Time budget

≤ 30 minutes runtime. Breakdown:

- ~5 min: write `Scratch/sprint_056_eq15_wrapper_pre_verification.py`
  (~80 lines, mirrors sprint 050's structure but invokes the wrapper
  directly).
- ~5 min: run the Scratch pre-verification (4 wrapper invocations × ~40s
  each = ~160s wall-clock). Read the final `DECISION:` line; record exit
  code; decide primary vs fallback vs BLOCKED.
- ~5 min: append the new shim `certify_eq15_at_<C>` to
  `rigorous_scalar.py` (~15 lines). Smoke-test in `uv run`.
- ~5 min: append the `[[oracles]]` block and the
  `[seed_axioms].allowed` entry to `lemma.toml`.
- ~5 min: write `Candidates/V50.lean` (mirror V49 with four one-line
  swaps). Run `lake build`.
- ~5 min: run the canonical Evaluator. Append the `Bulletin.md` line and
  the `Experience.md` entry; verify `git diff --stat` matches B7.

## Stop conditions

- Phase A returns 0 (primary accepted) and phase B's acceptance
  criteria B1–B7 all met: `STATUS=READY_FOR_EVALUATION` with
  `c_value = 1781/5000`.

- Phase A returns 1 (fallback accepted) and phase B's acceptance
  criteria B1–B7 all met (with `<C>` = `35610` and
  `<C_NUM>/<C_DEN>` = `35610/100000`):
  `STATUS=READY_FOR_EVALUATION` with `c_value = 35610/100000`. Note
  in the `STATUS` summary that the primary target was rejected and
  the fallback was used.

- Phase A returns 3 (both primary and fallback rejected, no FATAL):
  `STATUS=BLOCKED_NEEDS_HUMAN`. Diagnostic: the wrapper's box-by-box
  conservatism ceiling has been hit at sprint 055's c = 0.3560
  earlier than sprint 050's mpmath table predicted. Next sprint
  should either (a) upgrade the wrapper envelope to dps=100,
  n_trunc=500 and re-verify both primary and fallback, or (b) shift
  to addressing `proposal_001`'s "Required to resubmit" points
  (paper-side cross-coupling enrichment to break the c=0.35635
  crossover).

- Phase A returns 2 (FATAL regression): `STATUS=BLOCKED`. Diagnostic:
  the wrapper has lost rigour since sprint 055 — the regression check
  at c = 0.3560 failed (must accept) or at c = 0.3565 succeeded (must
  reject). Do NOT ship V50; the entire `[[oracles]]` channel needs
  re-verification. File a `Proposals/proposal_003_oracle_channel_rigour_regression.md`
  describing the failure mode.

- Phase A succeeds but phase B's `lake build` fails (B1):
  `STATUS=BLOCKED` with the Lean compilation error. Most likely a
  copy-paste typo in the `c_value` literal; verify the `def
  c_value : ℝ := <C_NUM> / <C_DEN>` line matches the chosen target.

- Phase B's Evaluator reports `pass: true` but score is unchanged
  (e.g. `score = 1780/5000`): `STATUS=BLOCKED`. Re-check
  `Candidates/V50.lean` for the literal `<C_NUM> / <C_DEN>`, not a
  copy of V49's `1780 / 5000`.

- Phase B's `lake build` succeeds but the Evaluator's `oracle_checks`
  reports `result: "missing-oracle-fn"`: `STATUS=BLOCKED_NEEDS_HUMAN`
  — sprint 054's `pyproject.toml` has somehow regressed.

## Notes for the Generator

- **Phase A is non-skippable.** The Scratch pre-verification is the
  bulletin's "verify before Lean" rule (line 99) made concrete. Do not
  skip it even if you are confident the wrapper will accept; the
  ~160s wall-clock cost is the cheapest insurance against a `BLOCKED`
  sprint that has to undo Lean / TOML / Experience edits.

- **Mirror V49 exactly modulo four one-line swaps.** The Lean
  infrastructure is identical: same `valid_of_eq15` discharge body,
  same `Eq15ScalarBound K c_value` axiom shape, same
  `eq15_lower_bound : ℝ := 1` declaration. Only the namespace,
  c_value, axiom name, and `@parent` comment change.

- **Per-`c` shim, not parametric refactor.** The existing
  `certify_eq15_at_seed` and `certify_eq15_at_3560` shims are the
  Evaluator's expected calling discipline (`Evaluator.py:393` invokes
  oracles with no arguments). Adding `certify_eq15_at_<C>` as a
  sibling is the right move; refactoring would exceed scope.

- **Falsifiability re-check is non-negotiable.** Phase A's regression
  check at c = 0.3565 (must reject) is the load-bearing falsifiability
  check for the entire `[[oracles]]` channel. If it ever returns True,
  the wrapper has lost its rigour and the oracle channel is no longer
  trustworthy. Do not skip; do not weaken.

- **Bulletin row format.** Match the existing `## Recent events` block
  style: a single line beginning with `sprint_056 PASS:` (or
  `BLOCKED`/`BLOCKED_NEEDS_HUMAN`) and ending with the score. Do not
  reflow.

- **The Scratch script doubles as sprint 057's template.** Sprint 057
  will likely target c = 1782/5000 = 0.3564 (or fallback 0.3562 if
  sprint 056 landed at 35610/100000), which is also not in sprint
  050's enumeration. Sprint 057's Scratch script can be sprint 056's
  with three substitutions (primary c, fallback c, regression c). Keep
  the script's structure clean enough to copy.

- **Wrapper wall-clock at this c.** Sprint 053's measurement reports
  ~38–45s per `certify_eq15` invocation for `(c, dps=50, n_trunc=200)`
  with the box count and per-box cost approximately independent of c
  in the 0.3554–0.3565 range. Phase A's four invocations should
  total ~160s wall-clock; phase B's Evaluator invocation adds one
  more ~40s call. Total Generator session wall-clock: ~3.5 minutes
  for the wrapper alone, plus the ~10 min of file edits.

- **The fallback c = 35610/100000.** Note the denominator is 100000,
  not 5000 — it's the finer-grained mid-point between sprint 055's
  verified 0.3560 and the proposed 0.3562. The shim function name is
  `certify_eq15_at_35610` (the "35610" suffix matches the numerator-
  in-the-100000-denominator convention; the canonical decimal form is
  `0.35610`). Phase B's edits all use the longer suffix in this case.

- **Score arithmetic.** `1781/5000` reduces to `1781/5000` (1781 is
  prime — actually 1781 = 13 × 137, but 5000 = 2³ × 5⁴ shares no
  factors, so the fraction is already in lowest terms). `35610/100000`
  reduces to `3561/10000` (gcd 10). Either way, the comparison
  `Fraction(score) > Fraction("1780/5000")` is the load-bearing
  acceptance check, not a string match.
