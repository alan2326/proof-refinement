# Sprint 057: Third c-push above the seed via the `eq15` oracle channel with **tiered-envelope** Scratch pre-verification — try `c = 1782/5000 = 0.3564` at the standard `(dps=50, n_trunc=200)` envelope first, and if the wrapper rejects (predicted by Experience.md sprint_056 lines 1122–1138 and the slope `−2.34e-3 per +0.0001` measured across V49/V50/sprint_056 fallback), upgrade to `(dps=100, n_trunc=500)` per Bulletin.md lines 300–304 and ship at the largest accepting `c` in `{0.3564, 0.3566, 0.3568}`. Either path produces `c_value > 1781/5000` and ships `Candidates/V51.lean`.

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V50.lean` (the second c-pushed candidate sprint
056 landed at `c = 1781/5000 = 0.3562` with margin +3.96e-03)
**Target file**: `Candidates/V51.lean`
**Direction**: raise-c — third sprint to push `c_value` above the seed. Routes
through the same pre-approved `[[oracles]]` channel as sprints 055/056, with
the structural addition (first time in the cascade) that the `[[oracles]]`
row's per-`c` shim may pin a **stricter precision envelope** than the previous
shims if Phase A1 shows the standard envelope rejects at the chosen `c`. This
absorbs the precision upgrade Bulletin.md lines 300–304 envisioned as part of
a c-pushing sprint, not a c-tying sprint. The shape mirrors sprint 056's
two-phase Scratch+Lean structure, generalised to a *two-tiered* phase A
(standard envelope first, upgraded envelope as fallback).

## Goal

Ship `Candidates/V51.lean` proving
`theorem korenblum_constant_search : ValidKorenblumBound c_value` at a
`c_value` strictly greater than `1781/5000` (V50's score), discharging the
`(15)` premise via a new oracle-registered axiom whose name and pinned
envelope depend on phase A's outcome:

- **Path STD-3564**: standard envelope `(dps=50, n_trunc=200)` accepts at
  `c = 1782/5000 = 0.3564`. Ship at `c = 1782/5000` with axiom
  `hEq15_oracle_certified_3564` and shim `certify_eq15_at_3564()` calling
  `certify_eq15(1782, 5000, dps=50, n_trunc=200)`.
- **Path HP-3564**: standard envelope rejects at `0.3564` but the upgraded
  envelope `(dps=100, n_trunc=500)` accepts at `c = 1782/5000`. Ship at
  `c = 1782/5000` with axiom `hEq15_oracle_certified_hp_3564` and shim
  `certify_eq15_at_hp_3564()` calling
  `certify_eq15(1782, 5000, dps=100, n_trunc=500)`.
- **Path HP-3566**: HP also accepts at `c = 1783/5000 = 0.3566`. Ship at
  `c = 1783/5000` with axiom `hEq15_oracle_certified_hp_3566` and shim
  `certify_eq15_at_hp_3566()`.
- **Path HP-3568**: HP also accepts at `c = 1784/5000 = 0.3568`. Ship at
  `c = 1784/5000` with axiom `hEq15_oracle_certified_hp_3568` and shim
  `certify_eq15_at_hp_3568()`.

The Generator must select the **largest accepting c** observed in phase A
(highest score). Score must report a value strictly greater than `1781/5000`
for this to count as the workspace's third genuine c-push.

## Why

### The cascade is approaching the wrapper's standard-envelope ceiling — exactly as Experience.md sprint_056 forecast

Sprint 055 landed at `c = 0.3560` with margin **+8.63e-03**. Sprint 056
landed at `c = 0.3562` with margin **+3.96e-03**. The empirically-measured
slope across V49/V50 plus sprint 056's fallback probe at
`c = 35610/100000 = 0.35610` (margin +6.29e-03) is **−2.34e-03 per +0.0001
of `c`** — strikingly steeper than the planner's prior linear interpolation
across sprint 050's broad mpmath table predicted (the cascade is in the
"smooth shoulder" right before the literal (15) crossover at `c ≈ 0.35635`,
where the gap function transitions from convex-decreasing to nearly-vertical).

**Extrapolating that measured slope** puts the standard-envelope wrapper's
margin at:

- `c = 0.3563`: predicted margin **+1.6e-03** — positive but already below
  the wrapper's measured ~3e-3 box-by-box conservatism amplitude.
- `c = 0.3564`: predicted margin **−0.7e-03** — **wrapper expected to
  REJECT** at the standard envelope.
- `c = 0.3565`: known to reject (sprint 056 phase A regression check, margin
  −3.01e-03).

This matches Experience.md sprint_056 lines 1122–1138 verbatim: *"sprint 057
*must* run the Scratch pre-verification at `dps=50, n_trunc=200` first; if
the wrapper rejects (as this prediction suggests), sprint 057 should
immediately upgrade the envelope to `dps=100, n_trunc=500` per Bulletin line
300–304 before either re-trying 0.3564 or shipping a finer-denominator step
like 35630/100000 = 0.35630."* That guidance is an explicit roadmap from the
previous sprint to this one.

### Why a tiered c-push, not a precision-only tying sprint

The user's framing offered two routes: (A) continue the cascade at
`c = 0.3564` with a Scratch pre-verification and graceful fallback (the
sprint 056 shape replayed), or (B) precision-envelope upgrade with score
unchanged at `c = 1781/5000` (V50's c) as a structural prerequisite for
future sprints. I considered four structurally distinct candidate sprint
shapes (planner ultrathink, per `KORENBLUM_PROOF_REFINEMENT_HARNESS.md`):

**C1 — `c = 1782/5000 = 0.3564`, standard envelope only (sprint 056 shape
verbatim).** The cascade's third step at the same envelope as 055/056.
**Strongest objection (decisive):** the empirical slope `−2.34e-3 per
+0.0001` measured across V49/V50/sprint_056-fallback predicts margin
**−0.7e-3 at c=0.3564** under the standard envelope — i.e. the wrapper is
expected to REJECT. Sprint 056's contract did not anticipate this slope
(its predicted margin at 0.3562 was +6.6e-03 raw, becoming ~+3.6e-03
certified — close to the actual +3.96e-03; but its forward predictions for
0.3564 used linear interpolation against sprint 050's *broad* table, not
the *local* slope between 0.3560/0.3561/0.3562). Without an envelope
upgrade, sprint 057 has very low expected probability of shipping a c-push.
Demoted to "primary attempt within a tiered structure"; if it succeeds,
ship; if it fails, the upgrade tier (C3-derivative below) takes over.

**C2 — Precision-envelope upgrade with score unchanged at c = 1781/5000
(user's option B).** A pure precision-upgrade sprint that re-runs the
oracle at V50's c with a stricter `(dps=100, n_trunc=500)` envelope but
ships score = 1781/5000, identical to V50. **Strongest objection
(decisive):** the bulletin's first 2026-05-02 directive (lines 28–31) is
unambiguous: *"sprints that tie V0's `c` — no matter how structurally
novel — are no longer wins; they are at best preparatory and must
explicitly justify why they cannot be folded into a single c-pushing
sprint."* Reading that against V50 (the latest c-push baseline), a sprint
that ties V50's `c = 1781/5000` is a non-win unless it cannot be folded
into a c-push. **A precision upgrade at `c = 0.3564` (or higher) is exactly
that fold:** the upgraded envelope's purpose IS to enable a c-push past the
standard-envelope ceiling, so applying it to V50's already-shipped c-value
is wasted infrastructure work. Bulletin lines 300–304 literally say *"the
five-sprint plan above leaves explicit headroom for a sixth sprint that
*re-verifies* `c ∈ {0.3563, 0.3564, 0.3565}` at `mpmath dps=100, N=500` and
either certifies one of them (next increment) or confirms the cliff"* —
the bulletin envisions the precision upgrade as a c-pushing sprint, not a
tying sprint. Demoted.

**C3 — Tiered c-push: standard envelope at `c=0.3564` first, upgraded
envelope at `c ∈ {0.3564, 0.3566, 0.3568}` as escalation, ship at largest
accepting c (CHOSEN).** Phase A runs Scratch pre-verifications in two tiers.
Tier A1 (standard `dps=50, n_trunc=200`) probes `c=0.3564`. If accepted,
short-circuit to phase B with axiom `hEq15_oracle_certified_3564`. If
rejected, tier A2 (upgraded `dps=100, n_trunc=500`) probes
`{0.3564, 0.3566, 0.3568}` to discover the new ceiling, and phase B ships
at the largest accepting c with axiom name and shim suffix
`hEq15_oracle_certified_hp_<C>`. **Strongest objection:** tier A2 has
non-trivial wall-clock cost (precision upgrade roughly 10× per box, 650
boxes ≈ 5 minutes per call, three calls ≈ 15 minutes wall-clock for the HP
probe alone, plus the standard-envelope tier A1 + regression checks ≈ 3
minutes). Total Generator session wall-clock: ~25–30 minutes, near the time
budget limit. **Resolution:** the tier A1 short-circuit eliminates tier A2
entirely if the standard envelope unexpectedly accepts at 0.3564 (predicted
unlikely but possible if the slope flattens), so the worst-case
wall-clock is bounded by the HP-tier scenario, which is still within 30
minutes per the budget. The c-push delivered (either +0.0002 standard or
+0.0002/+0.0004/+0.0006 HP) is the workspace's first c-push beyond
sprint 050's verified-positive enumeration, AND the first sprint to
register an `[[oracles]]` row with a non-default precision envelope —
both genuine novelty per the harness directive. The two-tiered structure
also doubles as the documentation row sprint 058+ will reuse when probing
even further (the Scratch script is a parameterised template).

**C4 — Finer-denominator step `c = 35630/100000 = 0.35630` standard
envelope only (Experience.md sprint_056's named alternative).** A
+0.00010 step instead of +0.00020. Linear interpolation from sprint 056's
measured data puts the standard-envelope margin at ~+1.6e-3 — positive
but very small. **Strongest objection:** burns one sprint per +0.00010
of c instead of +0.00020 (or +0.00040/+0.00060 with HP), and the
*next* sprint at this denominator (c=0.35640) would face the same
conservatism wall but worse. C4 is a strictly weaker version of C3 if
C3's tier A2 succeeds, and only marginally better than C3 if both C3
tiers fail. The tiered c-push C3 strictly dominates: if standard works
at 0.3564, C3 ships +0.0002; if standard fails at 0.3564, C3's HP tier
ships either at 0.3564 (+0.0002), 0.3566 (+0.0004), or 0.3568 (+0.0006).
C4 only "wins" against C3 in the scenario where (a) standard fails at
0.3564, (b) HP fails at 0.3564, (c) standard succeeds at 0.35630 — and
that scenario is internally inconsistent (HP at 0.3564 should be at
least as accepting as standard at 0.35630, since HP has strictly tighter
envelope at strictly larger c only if the ground-truth gap at 0.3564
is positive enough to overcome the envelope improvement). Demoted as
C4 ⊂ C3.

**Verdict.** C3 strictly dominates C1 (C1 is a sub-path of C3's tier A1),
strictly dominates C2 (C2 ties; C3 pushes), and strictly dominates C4
(C4 is a worse sub-case). The contract executes phase A's two tiers
sequentially and ships at the largest accepting c.

### What success looks like

Score strictly greater than `1781/5000`. Specific values per path:

- Path STD-3564: score `1782/5000` (= `891/2500`). Axiom set `{seed,
  hEq15_oracle_certified_3564}`. Standard envelope shim.
- Path HP-3564: score `1782/5000`. Axiom set `{seed,
  hEq15_oracle_certified_hp_3564}`. Upgraded envelope shim — first
  workspace use of `(dps=100, n_trunc=500)` in the oracle channel.
- Path HP-3566: score `1783/5000`. Axiom set `{seed,
  hEq15_oracle_certified_hp_3566}`.
- Path HP-3568: score `1784/5000`. Axiom set `{seed,
  hEq15_oracle_certified_hp_3568}`.

Either way, `oracle_checks` records exactly one entry with `ok: true`,
the canonical Evaluator output displays `score > 1781/5000`, and
`log.jsonl` has the third c-pushed row in the workspace's history. The
HP paths additionally demonstrate that the oracle channel scales to
stricter precision envelopes — eliminating the "is precision actually a
knob" question for sprint 058+.

## Concrete edits expected

The sprint splits into **two phases**: (A) tiered Scratch pre-verification
with short-circuit between tiers, and (B) Lean/TOML/Experience
materialisation. Phase B's edits and naming are conditional on phase A's
chosen path (STD-3564, HP-3564, HP-3566, or HP-3568).

### Phase A — tiered Scratch pre-verification (run BEFORE phase B)

#### A.1 `ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py` (NEW FILE)

Mirror the structure of `Scratch/sprint_056_eq15_wrapper_pre_verification.py`
with the following modifications:

1. **Replace `build_adaptive_certificate` with the inline-replay pattern
   Experience.md sprint_056 documented at lines 1086–1100**: the contract
   for sprint 056 had an operational issue where `build_adaptive_certificate`
   stalled at `(dps=50, n_terms=200)`; the fix is to inline-replicate
   `certify_eq15`'s body (single split-pass, no iterative refinement) so
   the reported `total_mass_lower` is exactly the value the wrapper
   certifies against. **Read sprint 056's actual script
   (`Scratch/sprint_056_eq15_wrapper_pre_verification.py`) to copy its
   inline-replay helper verbatim.**
2. **Two-tiered probe structure**:
   - **Tier A1 (standard envelope `dps=50, n_trunc=200`)**: probe
     `c = 1782/5000 = 0.3564` only. If `certify_eq15` returns True,
     write `DECISION: ship Lean candidate at c=1782/5000=0.3564 (path
     STD-3564, standard envelope).` and exit 0; **skip tier A2 entirely**.
   - **Tier A2 (upgraded envelope `dps=100, n_trunc=500`, only if A1
     rejects)**: probe `{1782/5000, 1783/5000, 1784/5000}` in ascending
     order. Find the largest c with `certify_eq15` returning True. Write
     `DECISION: ship Lean candidate at c=<C_NUM>/<C_DEN>=<C_DEC> (path
     HP-<C>, upgraded envelope dps=100,n_trunc=500).` with the matching
     numerics, exit 0. If all three reject, write `DECISION: BLOCKED —
     both standard and upgraded envelopes reject at c≥0.3564. The
     wrapper has hit a true ceiling near sprint 050's literal (15)
     crossover c≈0.35635.` and exit 3.
3. **Regression checks** (run regardless of which tier fires; these are
   load-bearing falsifiability guardrails):
   - Standard envelope at `c = 1781/5000 = 0.3562` must accept (V50's
     win, must still hold). If False, exit 2 (FATAL regression).
   - Standard envelope at `c = 3565/10000 = 0.3565` must reject
     (sprint 053/056 falsifiability). If True, exit 2 (FATAL
     regression).
   - **HP envelope at `c = 3565/10000 = 0.3565`** must reject (the HP
     envelope must NOT have crossed the literal (15) crossover at
     ~0.35635). If True, exit 2 (FATAL — the upgrade has somehow
     introduced over-acceptance, which would invalidate the entire HP
     tier's trust grounding).

The script body (skeleton; fill in the inline-replay helper from
sprint 056's actual script):

```python
"""
Sprint 057 - tiered wrapper pre-verification at c = 1782/5000 = 0.3564 (and
upgraded-envelope escalation at c in {1782, 1783, 1784}/5000 if standard
rejects).

Bulletin.md line 99: every c-push sprint must include a Scratch/ script
that confirms the wrapper accepts at the proposed (c, parameters) with a
stated margin BEFORE any Lean file is written.

Sprint 056's measured slope across V49 (margin +8.63e-3 at c=0.3560), the
fallback probe (margin +6.29e-3 at c=0.35610), and V50 (margin +3.96e-3
at c=0.3562) is -2.34e-3 per +0.0001 of c. Extrapolating to c=0.3564
predicts margin -0.7e-3 at the standard envelope — wrapper expected to
REJECT. This script tests that prediction (tier A1) and, if confirmed,
escalates to the upgraded envelope (tier A2) per Bulletin.md lines 300-304.

Run: cd korenblum && env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py
Output is appended to sprint_057_eq15_wrapper_tiered_preverification.txt.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from ProofRefinement.Korenblum.Numerical_Library.rigorous_scalar import certify_eq15

# IMPORTANT: copy sprint 056's inline-replay helper here verbatim. Do NOT
# call build_adaptive_certificate — Experience.md sprint_056 lines 1086-1100
# documents that build_adaptive_certificate stalls at (dps=50, n_terms=200).
# The helper should reuse certify_eq15's own box partition so the reported
# total_mass_lower matches the wrapper's certified value byte-for-byte.

def report(label: str, c_num: int, c_den: int, dps: int, n_trunc: int) -> dict:
    """Run wrapper and inline-replay; return a dict for the txt log."""
    print(f"\n=== {label}: c = {c_num}/{c_den} = {c_num/c_den:.6f}, dps={dps}, n_trunc={n_trunc} ===")
    sys.stdout.flush()
    accepted = certify_eq15(c_num, c_den, dps=dps, n_trunc=n_trunc)
    print(f"  certify_eq15(...) returned: {accepted}")
    sys.stdout.flush()
    # ... inline-replay helper here, computing total_lower and margin ...
    margin = ...  # placeholder; fill in from sprint 056's helper
    total_lower = ...
    return {
        "label": label, "c_num": c_num, "c_den": c_den,
        "c_decimal": c_num / c_den, "dps": dps, "n_trunc": n_trunc,
        "accepted": accepted, "total_lower": total_lower, "margin": margin,
    }


def main() -> int:
    print("Sprint 057 - tiered wrapper pre-verification")
    print("Tier A1: standard envelope (dps=50, n_trunc=200) at c=0.3564")
    print("Tier A2: upgraded envelope (dps=100, n_trunc=500) at c in {0.3564, 0.3566, 0.3568}")

    # Tier A1 - the cheap attempt
    a1 = report("A1-std-3564", 1782, 5000, dps=50, n_trunc=200)

    # Regression checks - must hold or we cannot trust any path
    regr_pos_std = report("regr+std-3562", 1781, 5000, dps=50, n_trunc=200)
    regr_neg_std = report("regr-std-3565", 3565, 10000, dps=50, n_trunc=200)

    if not regr_pos_std['accepted']:
        print("\nFATAL: standard envelope regression at c=0.3562 failed.")
        return 2
    if regr_neg_std['accepted']:
        print("\nFATAL: standard envelope falsifiability at c=0.3565 broken.")
        return 2

    if a1['accepted']:
        print("\nDECISION: ship Lean candidate at c=1782/5000=0.3564 (path STD-3564, standard envelope).")
        return 0  # short-circuit; tier A2 unnecessary

    # Tier A2 - the expensive escalation. Precision dps=100 is ~4x slower per
    # mpmath op; n_trunc=500 is ~2.5x more series terms; total ~10x slower per
    # box, 650 boxes ~5 min wall-clock per call.
    print("\nTier A1 rejected. Escalating to tier A2 (HP envelope dps=100, n_trunc=500).")
    a2_3564 = report("A2-hp-3564", 1782, 5000, dps=100, n_trunc=500)
    a2_3566 = report("A2-hp-3566", 1783, 5000, dps=100, n_trunc=500)
    a2_3568 = report("A2-hp-3568", 1784, 5000, dps=100, n_trunc=500)

    # HP-tier falsifiability check at c=0.3565 (must still reject; the HP
    # envelope must NOT cross the literal (15) crossover at ~0.35635).
    regr_neg_hp = report("regr-hp-3565", 3565, 10000, dps=100, n_trunc=500)
    if regr_neg_hp['accepted']:
        print("\nFATAL: HP envelope falsifiability at c=0.3565 broken — HP has crossed the literal (15) crossover.")
        return 2

    # Pick the largest accepting c at HP
    if a2_3568['accepted']:
        print("\nDECISION: ship Lean candidate at c=1784/5000=0.3568 (path HP-3568, upgraded envelope dps=100,n_trunc=500).")
        return 0
    if a2_3566['accepted']:
        print("\nDECISION: ship Lean candidate at c=1783/5000=0.3566 (path HP-3566, upgraded envelope dps=100,n_trunc=500).")
        return 0
    if a2_3564['accepted']:
        print("\nDECISION: ship Lean candidate at c=1782/5000=0.3564 (path HP-3564, upgraded envelope dps=100,n_trunc=500).")
        return 0

    print("\nDECISION: BLOCKED - both standard and upgraded envelopes reject at c>=0.3564. Wrapper has hit ceiling near literal (15) crossover c~0.35635.")
    return 3


if __name__ == "__main__":
    raise SystemExit(main())
```

#### A.2 `ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt` (NEW FILE)

Run the script via the canonical `uv run` invocation and tee stdout to
this file:

```bash
cd korenblum && \
env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 \
  ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py \
  2>&1 | tee ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt
```

The file's last `DECISION: …` line dictates phase B's path:

- `DECISION: ship Lean candidate at c=1782/5000=0.3564 (path STD-3564, standard envelope).` → phase B uses path STD-3564 (axiom suffix `_3564`, envelope `dps=50, n_trunc=200`)
- `DECISION: ship Lean candidate at c=1782/5000=0.3564 (path HP-3564, upgraded envelope dps=100,n_trunc=500).` → path HP-3564 (axiom suffix `_hp_3564`, envelope `dps=100, n_trunc=500`)
- `DECISION: ship Lean candidate at c=1783/5000=0.3566 (path HP-3566, …).` → path HP-3566 (axiom suffix `_hp_3566`)
- `DECISION: ship Lean candidate at c=1784/5000=0.3568 (path HP-3568, …).` → path HP-3568 (axiom suffix `_hp_3568`)
- `DECISION: BLOCKED — both standard and upgraded envelopes reject at c≥0.3564.` → `STATUS=BLOCKED_NEEDS_HUMAN`, no phase B
- `FATAL: …` → `STATUS=BLOCKED`, no phase B (rigour regression on the wrapper or HP envelope)

### Phase B — Lean/TOML/Experience materialisation (only if phase A returned exit 0)

Phase B mirrors sprint 056's edits, generalised across paths. Below uses
`<C>` as a placeholder for the chosen suffix (`3564`, `hp_3564`,
`hp_3566`, or `hp_3568`), `<C_NUM>/<C_DEN>` for the numeric pin
(`1782/5000`, `1782/5000`, `1783/5000`, `1784/5000`), and `<DPS>`/`<N_TRUNC>`
for the envelope (`50/200` for STD, `100/500` for HP).

#### B.1 `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`

Append a sibling zero-argument shim `certify_eq15_at_<C>()` directly after
the existing `certify_eq15_at_3562()` shim (currently at lines 1016–1043).
Mirror that shim's structure modulo the `(c_num, c_den, dps, n_trunc)`
parameter pin and the docstring/error message:

```python
def certify_eq15_at_<C>() -> Fraction:
    """
    Sprint 057 zero-argument Evaluator-facing shim for the registered
    oracle ``eq15_certified_at_<C>``.

    Calls ``certify_eq15(<C_NUM>, <C_DEN>, dps=<DPS>, n_trunc=<N_TRUNC>)``;
    on True, returns the certified lower bound (which is at least
    ``1 + 10^(-30)`` by construction). On False, raises ``RuntimeError``
    so the Evaluator records an oracle-check failure rather than silently
    accepting a numerically-unverified ``hEq15_oracle_certified_<C>``.

    Pre-verified by ``Scratch/sprint_057_eq15_wrapper_tiered_preverification.py``
    at this c with this envelope.
    [STD path docstring: standard envelope dps=50, n_trunc=200; the
     ground-truth (15) gap is shrinking but the wrapper still accepts.]
    [HP path docstring: upgraded envelope dps=100, n_trunc=500; first
     oracle in the workspace to use a precision envelope stricter than
     the standard (dps=50, n_trunc=200) used by sprints 053/055/056.
     The upgraded envelope reduces the wrapper's box-by-box conservatism
     gap relative to adaptive mp.quad, allowing certification at c values
     where the standard envelope rejects despite the ground-truth gap
     being positive.]
    """
    if not certify_eq15(<C_NUM>, <C_DEN>, dps=<DPS>, n_trunc=<N_TRUNC>):
        raise RuntimeError(
            "certify_eq15(<C_NUM>, <C_DEN>, dps=<DPS>, n_trunc=<N_TRUNC>) returned False; "
            "wrapper cannot reproduce the Scratch pre-verification's positive "
            "margin at c = <C_NUM>/<C_DEN> under the registered envelope. Refusing "
            "to certify the Lean axiom `hEq15_oracle_certified_<C>` to keep the "
            "trust surface honest."
        )
    return Fraction(1, 1)
```

**Do NOT** refactor any existing shims. Per-`c`-and-envelope shims at
~15 lines each remain the Evaluator's expected calling discipline.

#### B.2 `ProofRefinement/Korenblum/lemma.toml`

Append a sibling `[[oracles]]` row directly after the existing
`eq15_certified_at_3562` block. Add `"hEq15_oracle_certified_<C>"` to
`[seed_axioms].allowed`, after the existing `"hEq15_oracle_certified_3562"`
entry. The combined diff:

```toml
 [seed_axioms]
 allowed = [
   …
   "hEq15_oracle_certified_3560",
   "hEq15_oracle_certified_3562",
+
+  # Sprint 057: the third c-push sibling, pinning c = <C_NUM>/<C_DEN>.
+  # [STD path: same envelope as 3560/3562 siblings.]
+  # [HP path: first oracle in the workspace to pin the upgraded envelope
+  #  (dps=100, n_trunc=500) per Bulletin.md lines 300-304.]
+  # The Scratch tiered pre-verification at
+  # `Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt` records
+  # the wrapper's True return and certified margin at this c-and-envelope.
+  "hEq15_oracle_certified_<C>",
 ]
 …
 [[oracles]]
 axiom = "hEq15_oracle_certified_3562"
 bound_field = "eq15_lower_bound"
 oracle_fn = "rigorous_scalar.certify_eq15_at_3562"
+
+# Sprint 057: third c-push oracle. Pins `certify_eq15` at
+# `(c_num, c_den, dps, n_trunc) = (<C_NUM>, <C_DEN>, <DPS>, <N_TRUNC>)`
+# via the zero-argument shim `certify_eq15_at_<C>`. The wrapper's positive
+# return at this `(c_num, c_den, dps, n_trunc)` is pre-verified by
+# `Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`.
+# [HP path note: first workspace oracle with non-default precision envelope.]
+
+[[oracles]]
+axiom = "hEq15_oracle_certified_<C>"
+bound_field = "eq15_lower_bound"
+oracle_fn = "rigorous_scalar.certify_eq15_at_<C>"
```

#### B.3 `ProofRefinement/Korenblum/Candidates/V51.lean` (NEW FILE)

Mirror `Candidates/V50.lean` byte-for-byte modulo:

- `@parent V49` → `@parent V50`
- `namespace ...V50` → `namespace ...V51`
- `def c_value : ℝ := 1781 / 5000` → `def c_value : ℝ := <C_NUM> / <C_DEN>`
- `axiom hEq15_oracle_certified_3562` → `axiom hEq15_oracle_certified_<C>`
- discharge body's reference to the axiom name updates correspondingly
- comments updated to refer to the third c-push and the chosen path

The Lean file's docstring should explicitly name the path (STD-3564,
HP-3564, HP-3566, or HP-3568) and the pinned envelope, so a future reader
can tell at a glance whether V51 used the standard or upgraded oracle:

```lean
-- @parent V50
import ProofRefinement.Korenblum.Proof.Main

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V51

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms

/--
Third c-push above the seed in 57 sprints. Routes through the same
`valid_of_eq15` reducer as V0 / V47 / V48 / V49 / V50, but with the
literal `(15)` premise pinned at `c = <C_NUM>/<C_DEN> = <C_DEC>` (path
<PATH>) instead of sprint 056's `c = 1781/5000`. The `(15)` premise is
discharged by the registered oracle `eq15_certified_at_<C>` whose
wrapper is `Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (<C_NUM>, <C_DEN>, <DPS>, <N_TRUNC>)`;
the wrapper's positive return at this `(c, envelope)` was pre-verified
by `Scratch/sprint_057_eq15_wrapper_tiered_preverification.{py,txt}`.

[STD path: same standard envelope dps=50,n_trunc=200 as V49/V50.]
[HP path: first candidate in the workspace to pin the upgraded envelope
 dps=100,n_trunc=500. The upgraded envelope reduces the wrapper's
 box-by-box conservatism gap, allowing certification at c values where
 the standard envelope rejects despite the ground-truth (15) gap being
 positive. Per Bulletin.md lines 300-304's anticipated structure.]
-/
def c_value : ℝ := <C_NUM> / <C_DEN>

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

def eq15_lower_bound : ℝ := 1

axiom hEq15_oracle_certified_<C> (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_<C> K)

end ProofRefinement.Korenblum.Candidates.V51
```

#### B.4 `ProofRefinement/Korenblum/Bulletin.md`

Append exactly one line to the `## Recent events` block on success:

```text
sprint_057 PASS: third c-push above the seed — V51 ships at c_value = <C_NUM>/<C_DEN> via path <PATH> with axioms_used = {seed} ∪ {hEq15_oracle_certified_<C>}; oracle_checks records successful invocation of `rigorous_scalar.certify_eq15_at_<C>` (oracle_bound=1, declared=1, ok=true); wrapper acceptance pre-verified by `Scratch/sprint_057_eq15_wrapper_tiered_preverification.{py,txt}` at envelope (dps=<DPS>, n_trunc=<N_TRUNC>) with certified margin <MARGIN> above the strict-margin threshold; standard-envelope tier A1 [accepted at c=0.3564 / rejected at c=0.3564, escalated to HP tier A2]; HP-tier falsifiability at c=0.3565 still rejects [if HP path was taken / N/A if STD path]; score <C_NUM>/<C_DEN> > 1781/5000 — third consecutive c-push row in log.jsonl, demonstrating [the cascade is sustainable on +0.0002 standard-envelope steps / the HP envelope unlocks c-push past the standard-envelope ceiling]; sprint 058 can [continue +0.0002 cascade / probe further past the HP-accepted c — see Experience.md sprint_057's next-sprint-plan]
```

The bracketed alternatives are conditional on the chosen path; the
Generator must pick the matching wording for the actual phase A outcome.
Do not reflow.

#### B.5 `ProofRefinement/Korenblum/Experience.md`

Append a new dated entry `### 2026-05-02 sprint_057` summarising:

- **What sprint 056 left undone:** sprint 056 demonstrated the cascade
  works at +0.0002 increments through c=0.3562 (margin +3.96e-03), and
  Experience.md sprint_056 lines 1122–1138 explicitly forecast that
  sprint 057 would need to upgrade the envelope to dps=100,n_trunc=500
  if the standard envelope rejected at 0.3564.
- **The c-push delivered:** `c = <C_NUM>/<C_DEN>` via path <PATH>.
  Mirrors V50 byte-for-byte modulo the c-value, axiom-name, and
  envelope-pin swaps.
- **Why tiered c-push over precision-only tying:** the planner's
  ultrathink (see contract's Why section) compared four candidates —
  C1 (standard-only at 0.3564, demoted as overwhelmingly likely to
  fail per measured slope), C2 (precision-tying at V50's c, demoted
  per bulletin "ties are no longer wins" directive), C3 (tiered c-push,
  CHOSEN), C4 (finer-denominator standard-envelope, demoted as
  strictly dominated by C3). The tiered structure is a strict
  generalisation of sprint 056's two-phase shape: phase A1 short-circuits
  if the cheap envelope works; phase A2 escalates to the expensive
  envelope only when needed.
- **Phase A (Scratch) results:** record all wrapper invocations across
  both tiers and all regression checks. Particular attention to the
  HP-tier falsifiability check at c=0.3565 (must still reject; if it
  accepts, the HP envelope has crossed the literal (15) crossover and
  the entire HP tier's trust grounding is invalidated).
- **Measured slope update:** report the actual `(c, envelope, margin)`
  tuples and update the slope estimate. If HP at c=0.3564 ships, the
  HP envelope's conservatism gap can be backed out from the difference
  between the HP margin and the standard-envelope's predicted margin
  (~−0.7e-3) — first workspace measurement of HP conservatism.
- **Phase B (Lean) results:** record the standard sprint-056-shaped
  evidence (axioms_used, oracle_checks, score, log.jsonl row).
- **Next-sprint plan (sprint 058):** depends on which path landed.
  - **If STD-3564:** unexpectedly the cascade continues at the standard
    envelope; sprint 058 targets c=0.3566 with sprint 057's tiered
    Scratch script (probably HP-tier needed).
  - **If HP-3564:** the HP envelope unlocked +0.0002 past the standard
    ceiling; sprint 058 probes c=0.3566 / 0.3568 / 0.3570 at HP and
    ships at the new HP ceiling.
  - **If HP-3566 or HP-3568:** sprint 057 already explored the HP-tier
    ceiling; sprint 058 either ships the next +0.0002 step at HP (if
    margin headroom is large), or probes finer denominators
    (e.g. 1783/5000 at HP if 1784/5000 just barely accepted).
  - **The literal (15) crossover at ~0.35635** is the absolute hard
    ceiling regardless of envelope; past that, only `proposal_001`'s
    "Required to resubmit" successor can unblock further c-push.
- **proposal_001 / proposal_002 status untouched.** Sprint 057 does NOT
  touch either proposal. The c-push routes through the pre-approved
  `[[oracles]]` channel; trust-base expansions remain out-of-scope.

## Acceptance criteria

### Phase A — tiered Scratch pre-verification

A1. `ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`
    exists and executes successfully via the canonical `uv run` invocation:

    ```bash
    cd korenblum && \
    env UV_CACHE_DIR=korenblum/.uv-cache uv run python3 \
      ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py \
      2>&1 | tee ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt
    ```

    exit code is 0 (some path accepted), 2 (FATAL regression), or 3
    (cascade ceiling — both envelopes reject at c≥0.3564).

A2. The standard-envelope regression checks pass:
    - `certify_eq15(1781, 5000, dps=50, n_trunc=200) is True` (V50's
      win, must still hold)
    - `certify_eq15(3565, 10000, dps=50, n_trunc=200) is False` (sprint
      053/056 falsifiability)

A3. **If tier A2 fired**, the HP-tier falsifiability check passes:
    `certify_eq15(3565, 10000, dps=100, n_trunc=500) is False`. If
    True, the HP envelope has crossed the literal (15) crossover and
    the entire HP tier's trust grounding is invalidated; phase B must
    NOT proceed and the contract's STATUS becomes BLOCKED.

A4. The `Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt`
    file contains `=== … ===` blocks for every wrapper invocation
    (tier A1's c=0.3564 plus the two standard-envelope regressions; if
    A2 fired, additionally the three HP probes at c∈{0.3564, 0.3566,
    0.3568} plus the HP falsifiability at c=0.3565), each with
    `accepted`, `total_lower`, `margin` fields recorded.

### Phase B — Lean / TOML / Experience materialisation
### (skip if phase A returned exit codes 2 or 3)

B1. `lake build ProofRefinement.Korenblum.Candidates.V51` succeeds:
    ```bash
    bash korenblum/scripts/korenblum_lake_build.sh \
      Candidates/V51.lean
    ```
    exit code 0.

B2. `grep -n 'sorry' korenblum/ProofRefinement/Korenblum/Candidates/V51.lean`
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
    assert certify_eq15(<C_NUM>, <C_DEN>, dps=<DPS>, n_trunc=<N_TRUNC>) is True, 'wrapper must accept c=<C_DEC> at envelope (<DPS>,<N_TRUNC>)'
    assert certify_eq15(3565, 10000, dps=<DPS>, n_trunc=<N_TRUNC>) is False, 'falsifiability sanity check at envelope (<DPS>,<N_TRUNC>)'
    print('OK')
    "
    ```
    prints `OK` and exits 0. (For STD path, the third assertion uses the
    standard envelope which is sprint 053/056's known falsifiability check.
    For HP paths, the third assertion uses the upgraded envelope and is the
    HP-tier falsifiability check from A3 above — load-bearing.)

B4. The canonical Evaluator invocation succeeds:
    ```bash
    env UV_CACHE_DIR=korenblum/.uv-cache \
      uv run ProofRefinement/Korenblum/Evaluator.py \
      --file ProofRefinement/Korenblum/Candidates/V51.lean
    ```
    exit code 0. Terminal output must include:
    - `oracle audit:  PASS`
    - `  PASS  hEq15_oracle_certified_<C>: oracle=1 declared=1`
    - `score: <C_NUM>/<C_DEN>` (or equivalent display showing
      `score > 1781/5000`)

B5. The newest `Refinement_Log/log.jsonl` row records:
    - `pass: true`
    - `score`: a Fraction strictly greater than `1781/5000`
    - `axioms_used` array contains an entry whose `name` is
      `ProofRefinement.Korenblum.Candidates.V51.hEq15_oracle_certified_<C>`
    - `axioms_used` does NOT contain any entry whose `name` ends in
      `hEq15_oracle_certified_3562`, `hEq15_oracle_certified_3560`,
      `hEq15_oracle_certified_3554`, or `hEq15_seed_3554` (V51 must not
      transitively depend on prior per-`c` axioms)
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
    assert r['candidate'] == 'Candidates/V51.lean', r['candidate']
    assert Fraction(r['score']) > Fraction('1781/5000'), r['score']
    names = [a['name'] for a in r['axioms_used']]
    assert any('hEq15_oracle_certified_' in n for n in names), names
    for stale in ('hEq15_oracle_certified_3562', 'hEq15_oracle_certified_3560', 'hEq15_oracle_certified_3554', 'hEq15_seed_3554'):
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
    - `ProofRefinement/Korenblum/Candidates/V51.lean` (NEW FILE),
    - `ProofRefinement/Korenblum/Numerical_Library/rigorous_scalar.py`
      (one new shim function appended; no edits to existing
      `certify_eq15`, `certify_eq15_at_seed`, `certify_eq15_at_3560`,
      or `certify_eq15_at_3562`),
    - `ProofRefinement/Korenblum/lemma.toml` (one new entry in
      `[seed_axioms].allowed`, one new `[[oracles]]` block),
    - `ProofRefinement/Korenblum/Bulletin.md` (one appended line),
    - `ProofRefinement/Korenblum/Experience.md` (one appended entry),
    - `ProofRefinement/Korenblum/Refinement_Log/log.jsonl` (one
      appended row from the Evaluator run),
    - `ProofRefinement/Korenblum/Refinement_Log/verdict_sprint_057.md`
      (NEW FILE from the Evaluator agent),
    - `ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`
      (NEW FILE),
    - `ProofRefinement/Korenblum/Scratch/sprint_057_eq15_wrapper_tiered_preverification.txt`
      (NEW FILE).

    No edits to `Proof/`, `KorenblumPaper/`, any prior
    `Candidates/V<n>.lean`, `lakefile.toml`, `pyproject.toml`,
    `Evaluator.py`, any prior `Sprint_Contracts/sprint_<NNN>.md`, or
    any `Proposals/proposal_<NNN>.md` (`Status:` fields untouched).

## Out of scope

- Push `c_value` past whatever phase A's largest accepting c is. The
  next +0.0002 step (or finer-denominator probe past the HP ceiling)
  is sprint 058's job.
- Refactor any of the existing per-`c` shims or per-`c` `[[oracles]]`
  rows into parametric forms. Per-`c`-and-envelope shims at ~15 lines
  each remain the Evaluator's expected calling discipline.
- Modify `proposal_001` or `proposal_002`'s `Status:` fields. Both
  remain at their current state (rejected and pending respectively).
- Add any new Lean theorem to `Reduction.lean`, `Main.lean`, or any
  module under `KorenblumPaper/`. Zero edits to `Proof/` and
  `KorenblumPaper/`.
- File a new proposal. The c-push routes through the pre-approved
  `[[oracles]]` channel, including the precision-envelope upgrade per
  Bulletin lines 300–304's pre-authorised plan.
- Update `pyproject.toml` or `.gitignore`. Sprint 054 landed both
  correctly; HP-tier mpmath operations use the same pinned `mpmath`
  package.
- Edit `KorenblumPaper.PaperEq15` or `KorenblumPaper.OneModePaperBridge`.
- Investigate the **literal (15) crossover** at `c ≈ 0.35635` itself —
  if HP-tier rejects past that crossover, that's the absolute ceiling
  and is correctly diagnosed. Past it requires a future sprint that
  files a successor to `proposal_001`.

## Time budget

≤ 35 minutes runtime (slightly higher than sprint 056's 30-minute
budget because the HP-tier wrapper invocations are ~10× slower per box
than standard envelope; if tier A1 short-circuits, total wall-clock
drops back to ~25 minutes). Breakdown:

- ~8 min: write `Scratch/sprint_057_eq15_wrapper_tiered_preverification.py`
  (~150 lines, mirrors sprint 056's structure but adds the tiered
  decision tree and copies sprint 056's inline-replay helper verbatim).
- ~3 min: tier A1 wrapper invocation at c=0.3564 (~40s) plus two
  standard-envelope regression checks (~80s) = ~120s.
- **Conditional ~12 min**: tier A2 only if tier A1 rejects. Three HP
  probes at c ∈ {0.3564, 0.3566, 0.3568} (~5 min each = 15 min) plus
  HP falsifiability at c=0.3565 (~5 min). Reduce by short-circuiting
  if c=0.3568 accepts (no need for a fourth HP probe).
- ~5 min: append the new shim `certify_eq15_at_<C>` to
  `rigorous_scalar.py` (~15 lines). Smoke-test in `uv run`.
- ~3 min: append the `[[oracles]]` block and the
  `[seed_axioms].allowed` entry to `lemma.toml`.
- ~3 min: write `Candidates/V51.lean` (mirror V50 with four one-line
  swaps). Run `lake build`.
- ~5 min: run the canonical Evaluator. Append the `Bulletin.md` line
  and the `Experience.md` entry; verify `git diff --stat` matches B7.

## Stop conditions

- Phase A returns 0 with path STD-3564 and phase B's acceptance
  criteria B1–B7 all met: `STATUS=READY_FOR_EVALUATION` with
  `c_value = 1782/5000` via standard envelope. Note in summary that
  the measured slope `−2.34e-3 per +0.0001` was wrong — flatter than
  predicted near the cliff; document for sprint 058.

- Phase A returns 0 with path HP-3564, HP-3566, or HP-3568 and phase
  B's acceptance criteria B1–B7 all met (with `<C>` and `<C_NUM>/<C_DEN>`
  per the chosen path): `STATUS=READY_FOR_EVALUATION` with the
  matching `c_value`. Note in summary that the standard envelope hit
  its ceiling and the HP envelope unlocked the c-push.

- Phase A returns 3 (BLOCKED — both envelopes reject at c≥0.3564, no
  FATAL): `STATUS=BLOCKED_NEEDS_HUMAN`. Diagnostic: the wrapper has
  hit a true ceiling near the literal (15) crossover at c≈0.35635
  even with the upgraded envelope. The cascade has hit the
  intrinsic-mathematics wall, not a numerical-precision wall. Next
  sprint should NOT continue the cascade — instead it should either
  (a) probe finer denominators in `(0.3562, 0.3564)` at the HP
  envelope to characterise where exactly the HP ceiling sits, or (b)
  shift to addressing `proposal_001`'s "Required to resubmit"
  points (paper-side cross-coupling enrichment to break the c≈0.35635
  crossover).

- Phase A returns 2 (FATAL regression): `STATUS=BLOCKED`. Diagnostic
  describes which regression failed:
  - standard regression at c=0.3562 failed: V50's win has regressed,
    entire `[[oracles]]` channel needs re-verification.
  - standard falsifiability at c=0.3565 succeeded unexpectedly:
    standard envelope has lost rigour.
  - HP falsifiability at c=0.3565 succeeded: the HP envelope has
    crossed the literal (15) crossover, invalidating its trust
    grounding (the upgraded envelope must be at least as conservative
    as the standard one — if HP accepts where standard rejects past
    the true crossover, the HP wrapper has a bug).

  Do NOT ship V51; file
  `Proposals/proposal_003_oracle_channel_envelope_regression.md`
  describing the failure mode.

- Phase A succeeds but phase B's `lake build` fails (B1):
  `STATUS=BLOCKED` with the Lean compilation error. Most likely a
  copy-paste typo in the `c_value` literal or axiom name; verify
  matches the chosen path.

- Phase B's Evaluator reports `pass: true` but score is unchanged
  (e.g. `score = 1781/5000`): `STATUS=BLOCKED`. Re-check
  `Candidates/V51.lean` for the literal `<C_NUM> / <C_DEN>`, not a
  copy of V50's `1781 / 5000`.

- Phase B's `lake build` succeeds but the Evaluator's `oracle_checks`
  reports `result: "missing-oracle-fn"`: `STATUS=BLOCKED_NEEDS_HUMAN`
  — sprint 054's `pyproject.toml` has somehow regressed.

## Notes for the Generator

- **Phase A is non-skippable, and tier A1 must be tried before tier
  A2.** The Bulletin's "verify before Lean" rule (line 99) is
  non-negotiable. The tier ordering is also load-bearing: if you
  reverse it (try HP first), you waste ~12 minutes of wall-clock on a
  path that may not be needed. The expected scenario is tier A2
  fires per Experience.md sprint_056's forecast, but the planner
  cannot rule out that the slope flattens near the cliff (in which
  case tier A1 succeeds and tier A2 is unnecessary).

- **Copy sprint 056's inline-replay helper verbatim.** Do NOT call
  `build_adaptive_certificate` — Experience.md sprint_056 lines
  1086–1100 documents that it stalls at `(dps=50, n_terms=200)`. The
  inline-replay pattern that reuses `certify_eq15`'s own box partition
  is the correct way to extract `total_mass_lower` for the margin
  display. The HP envelope `(dps=100, n_trunc=500)` may actually
  work with `build_adaptive_certificate` (since the issue may be
  truncation-loop-vs-precision, not absolute), but for safety use the
  inline-replay pattern in both tiers — it matches the wrapper
  byte-for-byte and avoids the iterative-refinement stall.

- **HP envelope wall-clock.** `dps=100` is roughly 4× slower than
  `dps=50` per mpmath operation; `n_trunc=500` is 2.5× more series
  terms than `n_trunc=200`; per-box cost ≈ 10× standard. With ~650
  boxes per certificate, expect ~5 minutes per HP `certify_eq15`
  call. Three HP probes at c ∈ {0.3564, 0.3566, 0.3568} plus the
  HP falsifiability at c=0.3565 = four calls ≈ 20 minutes
  worst-case. Short-circuit when feasible (e.g. if HP-3564 rejects,
  HP-3566 and HP-3568 will also reject, so skip them — but do still
  run the falsifiability check at c=0.3565 to confirm the HP
  envelope's regression-correctness).

- **HP envelope falsifiability is non-negotiable.** Acceptance
  criterion A3 / B3-third-assertion is load-bearing: if the HP
  envelope ever returns True at c=0.3565, it has crossed the literal
  (15) crossover and the entire HP tier's trust grounding is
  invalidated. This is a critical rigour guardrail; the HP envelope
  is supposed to be *more* conservative than the standard envelope,
  not less. If it's ever less conservative on a known-rejection
  point, there's a bug in `certify_eq15`'s precision handling that
  must be diagnosed before any HP-tier candidate ships.

- **Mirror V50 exactly modulo four one-line swaps.** The Lean
  infrastructure is identical: same `valid_of_eq15` discharge body,
  same `Eq15ScalarBound K c_value` axiom shape, same
  `eq15_lower_bound : ℝ := 1` declaration. Only the namespace,
  c_value, axiom name, and `@parent` comment change.

- **The sprint 058 plan depends on phase A's outcome.** Document
  this clearly in Experience.md sprint_057's "Next-sprint plan"
  section per the schema in B.5 above. If HP-3568 lands, the
  cascade has gained ~5 sprints worth of headroom (each future
  +0.0002 step at HP); if HP-3564 lands, only ~1 sprint of
  headroom; if STD-3564 lands, the cascade unexpectedly continues
  at the standard envelope and the planner's slope estimate was
  pessimistic.

- **The literal (15) crossover at c≈0.35635 is the absolute
  ceiling.** Past it, the (15) inequality itself is false (sprint
  050 verified the gap goes negative at c=0.3565). No oracle
  envelope upgrade can recover beyond that point — only a
  paper-side reformulation per a successor to `proposal_001` could.
  Sprint 057 is approaching that ceiling; if HP-3568 ships
  (c=0.3568, past 0.35635), that would be evidence that sprint
  050's pinpoint was off, which deserves a sanity-check Scratch
  re-verification of the raw mpmath gap at c=0.3568 before
  certifying.

- **Bulletin row format.** Match the existing `## Recent events`
  block style: a single line beginning with `sprint_057 PASS:` (or
  `BLOCKED`/`BLOCKED_NEEDS_HUMAN`) and ending with the score. Do
  not reflow.

- **Score arithmetic.**
  - `1782/5000 = 891/2500` (gcd 2)
  - `1783/5000` is in lowest terms (1783 is prime, 5000 = 2^3 × 5^4)
  - `1784/5000 = 223/625` (gcd 8)

  The comparison `Fraction(score) > Fraction("1781/5000")` is the
  load-bearing acceptance check, not a string match.
