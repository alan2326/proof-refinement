-- @parent V61
import ProofRefinement.Korenblum.Proof.Main
import ProofRefinement.Korenblum.Proof.Reduction

noncomputable section

namespace ProofRefinement.Korenblum.Candidates.V62

open ProofRefinement.Korenblum
open ProofRefinement.Korenblum.ProblemAxioms
open KorenblumPaper

/-!
# Sprint 079 / V62 — joint two-window mass oracle registered; V61-tie under
# Stop condition #2 fallback

## Structural advance

V62 ships **the workspace's first non-eq15 oracle**:

  - `Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646`
    (Evaluator-facing zero-argument shim; pins
    `(c, ρStart₁, ρStop₁, ρStop₂, j₁, j₂, dps, n_trunc) =
     (35646/100000, 378083/1000000, 411605/1000000,
      999999/1000000, 2, 1, 30, 200)`),
  - the `[[oracles]]` row `h_two_window_mass_certified_at_35646` in
    `lemma.toml`, with bound field `two_window_mass_lower`,
  - `[seed_axioms].allowed`-extension for the new axiom name,
  - `Scratch/sprint_079_endpoint_pinned_witness.{py,txt}` — the Phase 0
    re-verification at the exact rational endpoints the wrapper pins
    (margin +1.9001e-3, ≥ 1e-3 floor satisfied).

The wrapper certifies the joint two-window mass

  1 ≤ ∫_{ρStart₁..ρStop₁} 2ρ / (H_{j₁}(c, ρ) · Λ(c, ρ)) dρ
      + ∫_{ρStart₂..ρStop₂} 2ρ / (H_{j₂}(c, ρ) · Λ(c, ρ)) dρ

at the registered envelope; the candidate-side `axiom`
`h_two_window_mass_certified_at_35646` declared below carries the same
joint-mass conclusion as the `hMassTotal` field of the new closing
reducer `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` (sprint 078,
`Proof/Reduction.lean`). The `valid_of_perMode_twoWindow_tau_partition_
eq8_eq9` reducer is therefore **discharge-ready at its joint-mass
premise**, modulo the candidate-side construction of the remaining
witness data (six summability hypotheses, two integrability hypotheses,
plus `diskExcess ≤ innerSeriesExcess`).

## Why V62 ties V61 rather than pushing c

Per the contract's Stop condition #2 (the fallback clause), the
candidate-side discharge of the new reducer's `h_witness : ∀ {a b K}
paper, ∃ ...` predicate requires constructing six summability hypotheses
about `plusSeq * c^(2n+2)/(n+1)`-style series for arbitrary `(a, b)`,
plus two integrability hypotheses about `circleGap a b` and
`ModeBridge.scalarIntegrand`. None of these are supplied by
`Section2Assumptions`; they require new candidate-side derivations of
the order of ~2000 Lean lines (see `Scratch/sprint_079_obstruction.md`
for the breakdown). That work exceeds the per-candidate-derived-theorem-
file budget of a single sprint.

The contract's fallback explicitly authorizes this: "The new wrapper +
lemma.toml row should still be shipped (they are independently useful),
and V62 should be shipped as a V61-tie with the oracle preserved for the
next sprint to pick up."

V62 therefore takes that fallback. The trust envelope is byte-for-byte
identical to V61's:

  - `hEq15_oracle_certified_hp_35645` (registered oracle, sprint 059)
  - standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`,
    `Lean.ofReduceBool`, `Lean.trustCompiler`)
  - no new candidate-level axioms used by `korenblum_constant_search`
  - no `Section2Assumptions` field extensions, no `KorenblumPaper/`
    edits.

The new oracle row in `lemma.toml` is registered but **not consumed by
this candidate** — its `axiom` name does not appear in V62's
`axioms_used`. It sits in `lemma.toml` ready for sprint 080 to pick up
along with the candidate-side witness-discharge construction.

## V62 side lemma — non-vacuity check at the new oracle's shape

The side lemma `v62_two_window_oracle_axiom_compiles` declares the
candidate-side axiom

  ```
  axiom h_two_window_mass_certified_at_35646
      (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤
      (∫ ρ in (378083 : ℝ)/1000000..(411605 : ℝ)/1000000,
          ModeBridge.scalarIntegrand ((35646 : ℝ)/100000) 2
            (WangOuter.paperLambda K ((35646 : ℝ)/100000)) ρ) +
        (∫ ρ in (411605 : ℝ)/1000000..(999999 : ℝ)/1000000,
          ModeBridge.scalarIntegrand ((35646 : ℝ)/100000) 1
            (WangOuter.paperLambda K ((35646 : ℝ)/100000)) ρ)
  ```

at the registered oracle's exact shape, with c=35646/100000 ≠ V62's
`c_value = 35645/100000`. This is a **declaration-level** check: the
axiom shape compiles in V62's import context, registers under the
candidate's `axioms_used` if invoked, and matches the wrapper's pinning
byte-for-byte. The axiom is **not** invoked by `korenblum_constant_search`
(V62 takes the V61-tie route via `valid_of_eq15`), so it does not appear
in V62's `axioms_used` audit.

The side lemma is here to confirm:
  - the new oracle row's Lean-facing axiom name is consumable by
    Lean syntax;
  - the four `(ρStart₁, ρStop₁, ρStart₂, ρStop₂)` decimals are
    exact rationals at the byte level the wrapper pins;
  - the next planner picking up sprint 080 can copy this axiom verbatim
    (or import it) without re-deriving its shape.

## Forward direction (sprint 080)

The cleanest c-push from V62 is to construct the candidate-side
witness for `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` by:

  1. defining `c_value := 35646/100000` (the wrapper-pinned c),
  2. picking the candidate-side endpoints either as Real.sqrt-based
     (route A in `sprint_079_obstruction.md`) or extending the new
     reducer to allow `ρStop₁ ≤ ρStart₂` plus a trivial slice
     (route B);
  3. discharging the six summability hypotheses (estimated ~1200
     Lean lines split across per-candidate derived-theorem files
     like `Candidates/V63/Summability.lean`);
  4. discharging the two integrability hypotheses (estimated ~300
     Lean lines, modelling on
     `WangPaperSideConditions.paperScalarIntegrand1_intervalIntegrable`);
  5. discharging `diskExcess ≤ innerSeriesExcess` via sprint 042's
     `diskExcess_eq_tsum_via_termwise_integration` plus
     `OneModePaperBridge.innerSeriesExcess_le_supKernel_mul_sigmaMinus`;
  6. consuming the new oracle as the discharge of the joint-mass
     hypothesis.

Sprint 080's deliverable would be V63 at c=35646/100000 — the first
c-push past V52's high-water mark of 7129/20000 in 19 sprints.

The oracle infrastructure shipped by V62 is the irreversible
prerequisite: the candidate-side `h_witness` work cannot land before the
joint-mass discharge axiom is registered (otherwise the discharge would
have to be a Lean theorem rather than an oracle axiom, which is route
(a) of V61's docstring — substantially harder).
-/

def c_value : ℝ := 35645 / 100000

theorem c_value_pos : (0 : ℝ) < c_value := by
  norm_num [c_value]

theorem c_value_lt_one : c_value < (1 : ℝ) := by
  norm_num [c_value]

/-- V61-shaped oracle bound-field; the Evaluator compares the
per-candidate `oracle_fn`'s returned Fraction against this `def` via
`oracle_bound ≤ declared`. Identical declaration to V61's
`eq15_lower_bound`; the new sprint 079 oracle's bound-field
`two_window_mass_lower` is also `1` and is declared below. -/
def eq15_lower_bound : ℝ := 1

/-- Sprint 079 oracle bound-field for the new joint two-window mass
oracle row. Declaration shape matches `eq15_lower_bound`'s shape (a
plain `ℝ`-valued `def` whose value is `1`); the registered oracle's
wrapper returns `Fraction(1, 1)` and the Evaluator checks
`oracle_bound ≤ declared` ⇔ `1 ≤ 1` ⇔ True.

This `def` is **declared but unused** by `korenblum_constant_search`
(V62 takes the V61-tie route via `valid_of_eq15` rather than the new
reducer's joint-mass route). It is here to register the candidate-
side bound for the next planner sprint to consume. -/
def two_window_mass_lower : ℝ := 1

/-- Same Lean-facing axiom as V61's `hEq15_oracle_certified_hp_35645`,
with the exact same `Eq15ScalarBound K c_value` shape at
`c_value = 35645/100000 = 0.35645`. Discharged by the registered oracle
`eq15_certified_at_hp_35645` whose wrapper is
`Numerical_Library.rigorous_scalar.certify_eq15` at
`(c_num, c_den, dps, n_trunc) = (35645, 100000, 100, 500)`.

V62's discharge of `korenblum_constant_search` consumes this axiom
exclusively (via `valid_of_eq15`); the new sprint 079 oracle axiom
declared below is **not** invoked by `korenblum_constant_search`. -/
axiom hEq15_oracle_certified_hp_35645 (K : ℝ → ℝ → ℝ) :
  Eq15ScalarBound K c_value

/-- Endpoint constants for the new joint-mass oracle's axiom. These are
the **exact rational endpoints** the wrapper
`Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646`
pins, byte-for-byte identical to the rationals in
`Scratch/sprint_079_endpoint_pinned_witness.txt`. -/
def two_window_oracle_c : ℝ := 35646 / 100000
def two_window_oracle_rho_start_1 : ℝ := 378083 / 1000000
def two_window_oracle_rho_stop_1 : ℝ := 411605 / 1000000
def two_window_oracle_rho_start_2 : ℝ := 411605 / 1000000
def two_window_oracle_rho_stop_2 : ℝ := 999999 / 1000000

/-- Sprint 079 / new candidate-side axiom: the joint two-window mass at
the chosen exact rational endpoints, with j-modes `(j₁, j₂) = (2, 1)`.

Discharged by the registered oracle `two_window_mass_certified_at_35646`
whose wrapper is
`Numerical_Library.rigorous_scalar.certify_two_window_mass_at_35646`.
Phase 0 witness (sprint 078): `Scratch/sprint_078_witness.txt` (margin
+1.9e-3 at canonical irrational endpoints). Endpoint-pinned re-
verification (sprint 079): `Scratch/sprint_079_endpoint_pinned_witness.txt`
(margin +1.9001e-3 at the chosen exact rational endpoints byte-for-byte
matching the wrapper).

The axiom shape matches the `hMassTotal` field of the new closing
reducer `valid_of_perMode_twoWindow_tau_partition_eq8_eq9` (sprint 078,
`Proof/Reduction.lean`) at the wrapper-pinned `c = 35646/100000`. The
candidate's `c_value = 35645/100000` is a **different** c (V61-tie), so
this axiom is **declared but not invoked** by `korenblum_constant_search`
in V62; the next planner sprint (080) is expected to pick this axiom up
as the discharge of `hMassTotal` inside a candidate-side `h_witness`
construction at the wrapper-pinned c.

The `K` argument is universal because the integrand `paperLambda K c ρ`
varies with `K`; the wrapper certifies the inequality for all paper-
faithful `K` (in fact only the value of `K` on the integration windows
matters, but the axiom is stated more generally for compositionality
with `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`). -/
axiom h_two_window_mass_certified_at_35646
    (K : ℝ → ℝ → ℝ) :
  (1 : ℝ) ≤
    (∫ ρ in two_window_oracle_rho_start_1..two_window_oracle_rho_stop_1,
        ModeBridge.scalarIntegrand two_window_oracle_c 2
          (WangOuter.paperLambda K two_window_oracle_c) ρ) +
      (∫ ρ in two_window_oracle_rho_start_2..two_window_oracle_rho_stop_2,
        ModeBridge.scalarIntegrand two_window_oracle_c 1
          (WangOuter.paperLambda K two_window_oracle_c) ρ)

/--
Sprint 079 / non-vacuity check at the new oracle's shape: the
candidate-side axiom `h_two_window_mass_certified_at_35646` compiles in
V62's import context against an arbitrary `K : ℝ → ℝ → ℝ`. Discharge is
by direct invocation of the axiom; this lemma exists to:

  - confirm Lean syntax acceptance of the new axiom's shape (decimal
    literals match the wrapper's pinning byte-for-byte);
  - preserve the axiom's exact statement form for sprint 080 to copy;
  - register the axiom under V62's namespace so the next planner can
    `import ProofRefinement.Korenblum.Candidates.V62` and pull the
    axiom by name.

This lemma is statement-level: it does not push c past V61's
`c_value = 35645/100000`. The candidate's `korenblum_constant_search`
is discharged via `valid_of_eq15` + `hEq15_oracle_certified_hp_35645`,
**not** via the new oracle. The `axioms_used` audit therefore reports
the V61-tie envelope.

Note that this lemma's `axioms_used` (if it were the sink) would
include `h_two_window_mass_certified_at_35646`; but since the sink is
`korenblum_constant_search` (which does not invoke this lemma), the
new oracle axiom does not appear in V62's `axioms_used`.
-/
theorem v62_two_window_oracle_axiom_compiles
    (K : ℝ → ℝ → ℝ) :
    (1 : ℝ) ≤
      (∫ ρ in two_window_oracle_rho_start_1..two_window_oracle_rho_stop_1,
          ModeBridge.scalarIntegrand two_window_oracle_c 2
            (WangOuter.paperLambda K two_window_oracle_c) ρ) +
        (∫ ρ in two_window_oracle_rho_start_2..two_window_oracle_rho_stop_2,
          ModeBridge.scalarIntegrand two_window_oracle_c 1
            (WangOuter.paperLambda K two_window_oracle_c) ρ) :=
  h_two_window_mass_certified_at_35646 K

/--
Paper-faithful candidate: the V61-tied `c = 0.35645` is a valid
Korenblum lower bound, routed through `valid_of_eq15` and discharged by
`hEq15_oracle_certified_hp_35645`.

V62's structural advance is **upstream** of this candidate's discharge
route — the new joint two-window mass oracle in `lemma.toml` and the
new wrapper in `Numerical_Library/rigorous_scalar.py`, exercised by
`v62_two_window_oracle_axiom_compiles` above. The axiom is declared but
not invoked by `korenblum_constant_search`; per the sprint 079 contract's
Stop condition #2, the candidate-side `h_witness` construction needed to
consume the new oracle via the new closing reducer
`valid_of_perMode_twoWindow_tau_partition_eq8_eq9` requires ~2000 lines
of Lean derivation (six summability hypotheses + two integrability
hypotheses + `diskExcess ≤ innerSeriesExcess` from the universally-
quantified `(a, b)` inside `h_witness`). That work is queued for sprint
080+ per `Scratch/sprint_079_obstruction.md`.
-/
theorem korenblum_constant_search : ValidKorenblumBound c_value := by
  exact valid_of_eq15 c_value_pos c_value_lt_one
    (fun {K} => hEq15_oracle_certified_hp_35645 K)

end ProofRefinement.Korenblum.Candidates.V62
