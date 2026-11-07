# Sprint 079: register joint two-window mass oracle and ship V62 as first c-push past V52

**Created**: 2026-05-04 18:30 by Planner
**Parent candidate**: `Candidates/V61.lean`
**Target file**: `Candidates/V62.lean`
**Direction**: raise-c

## Goal

Register a new `[[oracles]]` row in `lemma.toml` whose Python wrapper
certifies the joint two-window mass

```text
1 ≤ (∫_{ρStart₁..ρStop₁} ModeBridge.scalarIntegrand c j₁ (paperLambda K c) ρ dρ)
   + (∫_{ρStart₂..ρStop₂} ModeBridge.scalarIntegrand c j₂ (paperLambda K c) ρ dρ)
```

at concrete rational endpoints/modes derived from sprint 078's Phase 0
witness (c = 35646/100000, j₁ = 2, j₂ = 1, the canonical τ-windows
`[ρ_2(c), ρ_1(c)]` and `[ρ_1(c), 1]`), then ship `Candidates/V62.lean`
at `c_value = 35646/100000 = 0.35646` discharging
`korenblum_constant_search` via the existing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` from
`Proof/Reduction.lean` (sprint 078, lines 7770–7990).

This produces the **first c-push past V52's `7129/20000 = 0.35645`
high-water mark in 18 sprints**.

## Why

- Sprint 078 shipped the structural deliverable: a new closing reducer
  whose `hMassTotal : 1 ≤ ∫₁ + ∫₂` premise is a single numerical
  inequality at fixed `(c, ρStart₁, ρStop₁, ρStart₂, ρStop₂, j₁, j₂)`.
- Sprint 078's Phase 0 sweep
  (`Scratch/sprint_078_two_window_tau_mass_sweep.{py,txt}`) established
  margin **+1.9e-3** at c = 0.35646 with j-pair (j₁, j₂) = (2, 1) on
  the canonical τ-windows. The wrapper's strict-margin floor is
  `10^(-min(dps,30))` per the existing `certify_eq15` pattern, so
  +1.9e-3 has roughly 60 orders of magnitude of headroom against
  the certification threshold at dps = 30.
- The AGENT_BRIEF (lines 78–85) explicitly designates the
  `[[oracles]]` registration channel as **pre-approved** when the
  sprint contract names the wrapper, the toml row, and the Lean axiom
  name. No proposal is required.
- The Bulletin's "current priority" directive ranks the c-push as the
  primary objective; tying V52 is no longer scored as a win. Sprint
  078 shipped Phase 0 GO + Phase A reducer but explicitly took the
  V60-tie fallback because the discharge route (oracle vs interval-
  arithmetic Lean derivation) was left to the next planner. This
  sprint makes that choice: **oracle**, because the workspace already
  has four `certify_eq15_at_*` shims following the same shape and the
  numerical content (joint two-window mass) is byte-identical to the
  Phase 0 sweep that already exists on disk.

## Concrete edits expected

### 1. New Numerical_Library wrapper

- `Numerical_Library/rigorous_scalar.py`: add a new function
  `certify_two_window_mass_at_35646() -> Fraction` (Evaluator-facing
  zero-argument shim) that reuses the same mpmath kernel as
  `Scratch/sprint_078_two_window_tau_mass_sweep.py` (the `paper_lambda`,
  `term_j`, and `mass_j_quad` helpers, copied verbatim or imported
  via a small private helper module under `Numerical_Library/`).
  The wrapper:

  - pins `(c_num, c_den) = (35646, 100000)`,
  - pins the four endpoints to **the exact rationals** chosen below
    (these must match the candidate-side `ρStart₁, ρStop₁, ρStart₂,
    ρStop₂` byte-for-byte; see "Endpoint selection" §),
  - pins `(j₁, j₂) = (2, 1)`,
  - pins `(dps, n_trunc) = (30, 200)` (matching sprint 078's Phase 0
    envelope; if the wrapper wants extra headroom it may raise dps),
  - computes the joint mass via `mp.quad` over the two windows (or
    via verified-interval arithmetic with `flint.arb` if the
    generator prefers — either is acceptable),
  - returns `Fraction(1, 1)` iff `joint_mass ≥ Fraction(1, 1) +
    Fraction(1, 10**min(dps, 30))` (matching the `certify_eq15`
    margin pattern),
  - raises `RuntimeError` on rejection, so the Evaluator records an
    oracle-check failure rather than silently accepting an
    unverified Lean axiom.

  The wrapper's docstring must cite sprint 078's Phase 0 witness file
  and reproduce the four exact endpoints + (j₁, j₂) so the trust
  surface is auditable.

### 2. New `[[oracles]]` row + `[seed_axioms].allowed` extension in `lemma.toml`

```toml
# Sprint 079: first non-eq15 oracle. Pins the joint two-window mass at
# (c_num, c_den, j₁, j₂, ρStart₁, ρStop₁, ρStart₂, ρStop₂, dps, n_trunc).
# Wrapper: `Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646`.
# Phase 0 witness: `Scratch/sprint_078_witness.txt` (margin +1.9e-3).

[[oracles]]
axiom = "h_two_window_mass_certified_at_35646"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646"
```

Add `"h_two_window_mass_certified_at_35646"` to `[seed_axioms].allowed`
so the Evaluator's axiom audit accepts it as a registered oracle
axiom.

### 3. Phase 0 re-verification at the chosen exact endpoints

- Add `Scratch/sprint_079_endpoint_pinned_witness.{py,txt}` re-running
  the joint-mass computation at the **exact rational endpoints** the
  candidate-side axiom pins (not just `c/sqrt(tau(j))` floats).
  Margin must remain ≥ 1e-3 to qualify as Phase 0 GO. If Phase 0 NO-GO
  at the chosen endpoints, the generator picks a slightly relaxed
  endpoint window and re-tries; the actual chosen endpoints + margin
  go into both the Scratch file and the `lemma.toml` row docstring.

### 4. New candidate `Candidates/V62.lean`

- `def c_value : ℝ := 35646 / 100000`
- `theorem c_value_pos`, `theorem c_value_lt_one` (`norm_num`).
- `def two_window_mass_lower : ℝ := 1` (Evaluator's bound-field def).
- `def ρStart₁ : ℝ := <chosen rational>` and similarly for `ρStop₁`,
  `ρStart₂`, `ρStop₂` (with `ρStop₁ = ρStart₂` enforced by `rfl`).
- The new candidate-side axiom

  ```lean
  axiom h_two_window_mass_certified_at_35646
      (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤
      (∫ ρ in ρStart₁..ρStop₁,
          ModeBridge.scalarIntegrand c_value 2
            (WangOuter.paperLambda K c_value) ρ) +
        (∫ ρ in ρStart₂..ρStop₂,
          ModeBridge.scalarIntegrand c_value 1
            (WangOuter.paperLambda K c_value) ρ)
  ```

  shaped to match exactly the `hMassTotal` field inside the new
  reducer's `h_witness` predicate at `(c, j₁, j₂) = (c_value, 2, 1)`.

- `theorem korenblum_constant_search : ValidKorenblumBound c_value`
  proven by invoking
  `valid_of_perMode_twoWindow_tau_partition_eq8_eq9 c_value_pos
  c_value_lt_one h_witness`, where `h_witness` is constructed to:

  - return the seven-tuple of endpoints + j-modes from the candidate's
    `def`s,
  - discharge the τ-bounds (`OneModeTail.tau 1 ≤ c² / ρStop₁²`,
    `c² / ρStart₁² ≤ OneModeTail.tau 2`, etc.) by `norm_num` over
    the chosen rational endpoints (these are pure rational
    polynomial inequalities since `tau j` is a closed-form rational
    in `j`),
  - discharge the summability/integrability hypotheses from
    `paper`-derived facts (sprint 011/012 give `sigmaZeroMinus`
    monotonicity; sprint 042/046/076 give the polar-Jacobian
    `tsum`-of-integrals identity; sprint 005 gives
    `sigmaMinus_eq_rho_sq_mul_sigmaZeroMinus`); some of these may
    need a small per-candidate derived-theorem file under
    `Candidates/V62/`,
  - discharge the `diskExcess ≤ innerSeriesExcess` field via the
    sprint 042 `diskExcess_eq_tsum_via_termwise_integration` chain
    (or directly through `OneModePaperBridge.innerSeriesExcess`'s
    paper-faithful relationship to `diskExcess`),
  - discharge the `1 ≤ ∫₁ + ∫₂` field by the new oracle axiom
    `h_two_window_mass_certified_at_35646`.

- A side lemma `v62_c_push_witness` that exhibits the new c-value
  is strictly above V52's: `(7129 : ℝ) / 20000 < c_value`, by
  `norm_num`.

### 5. Bulletin + Experience append

- Append one row to `Bulletin.md` per the standard pattern.
- Append one row to `Experience.md` per the standard pattern;
  include the certified margin, the chosen endpoints, the wrapper
  function, and the oracle row name.

## Endpoint selection (load-bearing detail)

Sprint 078's Phase 0 sweep parameterized windows by `ρ_j(c) = c /
sqrt(tau(j))`, which involves a square root. Lean cannot use those
endpoints directly; it needs **exact rationals**. Two options:

- **Option E1 (preferred)**: pick the endpoints to be the **exact
  rational solutions** of `c² / ρ² = tau(j)`. These are
  `ρ²_j(c) = c² · ((j+1)² / (j(j+2)))`. For `c = 35646/100000`,
  `j ∈ {1, 2}` gives `ρ²_1(c) = c² · 4/3` and `ρ²_2(c) = c² · 9/8`.
  These are exact rationals; `ρ_j(c)` itself is not, but the τ-bound
  hypotheses are `tau(j-1) ≤ c²/ρ²` and `c²/ρ² ≤ tau(j)`, which use
  `ρ²` not `ρ`. So pick `ρStart₁`, `ρStop₁`, `ρStart₂`, `ρStop₂` as
  rationals close to the τ-breakpoint values, with `ρStop₁ = ρStart₂`,
  and verify the τ-bound polynomial inequalities via `norm_num`.
- **Option E2 (fallback)**: pick endpoints as truncated decimals at
  ~6 digits (e.g. `ρStart₁ = 378072/1000000`, `ρStop₁ = 411593/1000000
  = ρStart₂`, `ρStop₂ = 999/1000`) and verify the τ-bounds at those
  decimals by `norm_num`. The τ-bound margins are not tight at the
  Phase 0 sweep endpoints (sprint 078 reports `tau(1) = 0.75` and
  `c²/ρStart₁² ≈ 0.75 + ε` for ε a few decimals; the inequality
  `c²/ρStart₁² ≤ tau(1)` may go the wrong way if ρStart₁ is even a
  hair too small).

The generator should pick E1 if it can (the algebra
`c² · 4/3 ≤ ρ²` etc. is `norm_num`-friendly); otherwise E2 with
careful endpoint selection that keeps each τ-bound on the correct
side. Document the choice and the verified margin in the candidate's
docstring.

The Phase 0 sweep at the chosen exact endpoints (Scratch §3) must
report margin ≥ 1e-3.

## Acceptance criteria

1. `lake build ProofRefinement.Korenblum.Candidates.V62` succeeds.
2. `env UV_CACHE_DIR=korenblum/.uv-cache uv run
   ProofRefinement/Korenblum/Evaluator.py --file
   ProofRefinement/Korenblum/Candidates/V62.lean` reports
   `pass: true`.
3. Evaluator records `score (maximize) = 35646/100000` (strictly
   greater than V52's `7129/20000 = 0.35645`).
4. Evaluator's axiom audit reports
   `axioms_used ⊆ {propext, Classical.choice, Quot.sound,
   Lean.ofReduceBool, Lean.trustCompiler,
   ProofRefinement.Korenblum.Candidates.V62.h_two_window_mass_certified_at_35646}`.
5. Evaluator's oracle audit reports `PASS` for the new oracle row,
   with `oracle_bound = 1, declared = 1, ok = true`.
6. `Scratch/sprint_079_endpoint_pinned_witness.{py,txt}` exist and
   record margin ≥ 1e-3 at the chosen exact rational endpoints.
7. `Bulletin.md` and `Experience.md` each gain one row per the
   standard pattern.

## Out of scope

- Edit older candidates (V0–V61).
- Edit `KorenblumPaper/` (read-only paper surface).
- Edit `Proof/Reduction.lean` (the new reducer is already there from
  sprint 078). If a per-candidate derived-theorem file is needed for
  summability/integrability discharges, place it under
  `Candidates/V62/` per the AGENT_BRIEF lines 154–204.
- Add new paper axioms or `Section2Assumptions` fields.
- Re-derive the new reducer; it is already the load-bearing input.
- Reattempt the seven-window m=7 envelope (Sprint C); that is a
  separate planner deliverable.
- Discharge `hMassTotal` by an interval-arithmetic Lean derivation;
  the oracle route is the contract's chosen route.

## Time budget

≤ 90 minutes runtime for the generator session (the wrapper engineering
is ~30 min reusing sprint 078's mpmath kernel; the candidate-side proof
is ~30–60 min following V52's `valid_of_eq15` discharge pattern adapted
to the new reducer's witness-style interface).

## Stop conditions

- All seven acceptance criteria met: `STATUS=READY_FOR_EVALUATION`.
- Phase 0 re-verification at the chosen exact endpoints reports
  margin < 1e-3 even after one endpoint relaxation: `STATUS=BLOCKED`
  with a precise note in `Scratch/sprint_079_obstruction.md` naming
  the τ-bound margin geometry that prevents an exact-rational
  endpoint selection from clearing 1e-3. The next planner files
  proposal_004 only if the AGENT_BRIEF's four-condition guide is
  satisfied.
- Candidate-side discharge of a non-numerical hypothesis inside
  `h_witness` (e.g. summability of `plusSeq * c^(2n+2)/(n+1)`) turns
  out non-trivial and exceeds the per-candidate-derived-theorem-file
  budget within this sprint: `STATUS=BLOCKED` with the obstruction
  documented at `Scratch/sprint_079_obstruction.md`. The new wrapper
  + lemma.toml row should still be shipped (they are independently
  useful), and V62 should be shipped as a V61-tie with the oracle
  preserved for the next sprint to pick up.
- Trust expansion required (e.g. a new module needs to be added to
  `[workspace_import_policy]`): `STATUS=BLOCKED_NEEDS_HUMAN`.
