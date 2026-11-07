The `lemma.toml` above was truncated mid-file. Here it is complete — this block supersedes the partial one; everything else already emitted stands.

```toml path=ProofRefinement/Korenblum/lemma.toml
name = "Korenblum Constant"
slug = "korenblum"
paper_ref = "Wang (2025), Section 2 / equation (15)"

sink_theorem = "korenblum_constant_search"
constant_def = "c_value"
score = "c_value"
score_direction = "maximize"

[search_constants]

[import_policy]
# Candidate-side surface enforced against every `Candidates/V<N>.lean`.
# Each per-candidate derived-theorem module under `Candidates/V<N>/` is
# registered here as candidates start importing it. Per `AGENT_BRIEF.md`
# lines 154-204 those files contain only `theorem`s derived from the
# existing trusted surface (no new axioms, no edits to `KorenblumPaper/`).
allowed_exact = [
  "ProofRefinement.Korenblum.Candidates.V53.ThetaStep",
  "ProofRefinement.Korenblum.Candidates.V54.LiftIdentity",
  "ProofRefinement.Korenblum.Candidates.V55.LiftSeriesBridge",
  "ProofRefinement.Korenblum.Candidates.V57.DiskExcessLiftIntegrated",
  "ProofRefinement.Korenblum.Candidates.V58.AnnulusExcessLiftIntegrated",
  "ProofRefinement.Korenblum.Candidates.V60.PerKAlphaVaryingLiftIdentity",
  "ProofRefinement.Korenblum.Candidates.V63.Integrability",
  "ProofRefinement.Korenblum.Candidates.V63.Summability",
  "ProofRefinement.Korenblum.Candidates.V63.DiskInnerSeriesBridge",
  "ProofRefinement.Korenblum.Candidates.V64.TauWindowEndpoints",
  "ProofRefinement.Korenblum.Candidates.V65.TauWindowEndpoints",
]
allowed_prefixes = [
  "ProofRefinement.Korenblum.Proof",
  "Mathlib",
]

[workspace_import_policy]
allowed_exact = [
  "KorenblumPaper.PaperAxioms",
  "KorenblumPaper.PaperEq15",
  "KorenblumPaper.OneModePaperBridge",
]
allowed_prefixes = [
  "ProofRefinement.Korenblum",
  "Mathlib",
]

[seed_axioms]
allowed = [
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
  "Lean.trustCompiler",

  # V0 seed: Wang's equation (15) at c = 0.3554.
  "hEq15_seed_3554",

  # Oracle-discharged eq15 siblings (sprints 053/055/056/057/059).
  # Same `Eq15ScalarBound K c_value` shape; trust grounded in the
  # `rigorous_scalar.certify_eq15` verified-interval wrapper.
  "hEq15_oracle_certified_3554",
  "hEq15_oracle_certified_3560",
  "hEq15_oracle_certified_3562",
  "hEq15_oracle_certified_hp_3564",
  "hEq15_oracle_certified_hp_35645",

  # Sprint 079: first non-eq15 oracle. Joint two-window tau-partition
  # mass at exact rational endpoints
  #   c         = 35646/100000
  #   rho_s1    = 378083/1000000
  #   rho_t1    = 411605/1000000   (= rho_s2)
  #   rho_t2    = 999999/1000000
  #   (j1, j2)  = (2, 1),  (dps, n_trunc) = (30, 200).
  "h_two_window_mass_certified_at_35646",

  # Sprint 083: sqrt-endpoint sibling of the above, pinning the
  # canonical tau-breakpoint endpoints
  #   rho_s1 = c*sqrt(9/8),  rho_t1 = rho_s2 = c*sqrt(4/3),
  #   rho_t2 = 999999/1000000,  at c = 35646/100000.
  # Discharged by a rigorous flint.arb interval-arithmetic lower bound.
  "h_two_window_mass_certified_at_35646_sqrt",

  # V65: same sqrt-pinned shape one notch higher, at c = 35647/100000.
  # Wrapper `certify_two_window_mass_at_35647_sqrt` returns only when a
  # rigorous arb LOWER bound on the joint two-window mass clears
  # 1 + 10^(-30). Headroom: sprint 078's Phase 0 sweep
  # (`Scratch/sprint_078_two_window_tau_mass_sweep.txt`) reports margin
  # >= 1e-3 at c in {0.35646, 0.35647, 0.35648} on exactly these
  # canonical endpoints, with the mass crossing below 1 only near
  # c ~ 0.35654 — the pin is strictly inside the verified band, so
  # falsifiability is preserved.
  "h_two_window_mass_certified_at_35647_sqrt",

  # Free candidate-side axioms (AGENT_BRIEF lines 62-65 permit these
  # when listed here). `hH2_*`: Wang's Hypothesis 1 of Section 2, H^2
  # boundary-norm finiteness `Summable (‖a n‖^2)`, applied to `a` for f
  # and to `b` for g. `hCircleGapInt_*`: the paper-implicit
  # `2*rho*circleGap`-density integrability on `(c_value, 1)`; Wang
  # assumes all Section 2 integrals converge, but the bundled
  # `Section2Assumptions` does not assert circleGap measurability.
  "hH2_v64",
  "hCircleGapInt_v64",
  "hH2_v65",
  "hCircleGapInt_v65",
]

# ---------------------------------------------------------------------
# Registered numerical oracles.
#
# Schema matches `Evaluator.py:load_workspace_config`
# (`axiom`, `bound_field`, `oracle_fn`). The Evaluator invokes
# `oracle_fn` with no arguments and compares the returned
# Fraction-coercible bound against the candidate's
# `def <bound_field> : ℝ := ...` via `oracle_bound <= declared`.
# ---------------------------------------------------------------------

# Seed envelope (3554, 10000, dps=50, n_trunc=200). Falsifiability:
# the wrapper rejects (3565, 10000) at the same envelope.
[[oracles]]
axiom = "hEq15_oracle_certified_3554"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_seed"

# (1780, 5000, dps=50, n_trunc=200); sprint 050 gap +1.131e-02.
[[oracles]]
axiom = "hEq15_oracle_certified_3560"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3560"

# (1781, 5000, dps=50, n_trunc=200); pre-verified margin +3.96e-03.
[[oracles]]
axiom = "hEq15_oracle_certified_3562"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_3562"

# (1782, 5000, dps=100, n_trunc=500); HP envelope, margin +1.17e-03.
# HP still rejects at c=0.3565 (-1.15e-03).
[[oracles]]
axiom = "hEq15_oracle_certified_hp_3564"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_3564"

# (35645, 100000, dps=100, n_trunc=500); HP envelope, margin +1.35e-05.
[[oracles]]
axiom = "hEq15_oracle_certified_hp_35645"
bound_field = "eq15_lower_bound"
oracle_fn = "rigorous_scalar.certify_eq15_at_hp_35645"

# Sprint 079 joint two-window mass at exact rational endpoints,
# (dps, n_trunc) = (30, 200), margin +1.9001e-3.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646"

# Sprint 083 sqrt-endpoint joint two-window mass at c = 35646/100000,
# rigorous flint.arb interval-arithmetic lower bound, (dps, n_trunc)
# = (80, 200), subdivision schedule 256 -> 16384.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35646_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35646_sqrt"

# V65 sqrt-endpoint joint two-window mass at c = 35647/100000, one
# notch above V64. Rigorous flint.arb interval-arithmetic lower bound
# on
#   int_{c*sqrt(9/8)}^{c*sqrt(4/3)}  2r / (H_2(c,r) * Lambda(c,r)) dr
# + int_{c*sqrt(4/3)}^{999999/1000000} 2r / (H_1(c,r) * Lambda(c,r)) dr
# with (dps, n_trunc) = (80, 200) and subdivision schedule
# 2048 -> 16384; returns Fraction(1,1) only when the rigorous lower
# bound clears 1 + 10^(-30). Every step under-estimates the true
# integrand (truncated Wang product over-estimates K, Lambda is
# increasing in K, H_j evaluated at its per-subinterval maximiser and
# 2r at its minimiser), so the certificate is a genuine lower bound.
[[oracles]]
axiom = "h_two_window_mass_certified_at_35647_sqrt"
bound_field = "two_window_mass_lower"
oracle_fn = "rigorous_scalar.certify_two_window_mass_at_35647_sqrt"
```

All four files are now emitted in full:

- `Candidates/V65/TauWindowEndpoints.lean` — sqrt-pinned τ endpoints, four τ-bound discharges at the exact breakpoints `tau(1)=3/4`, `tau(2)=8/9`, ordering lemmas, all `theorem`s.
- `Candidates/V65.lean` — `c_value = 35647/100000 > 17823/50000`, sink via `valid_of_perMode_twoWindow_tau_partition_eq8_eq9`, witness composed from the three V63 derived files plus two seed-listed free axioms plus the new joint-mass oracle axiom.
- `Numerical_Library/rigorous_scalar.py` — unchanged existing content plus a shared `_certify_two_window_mass_sqrt_arb` helper and the new `certify_two_window_mass_at_35647_sqrt` shim (the 35646 shim now routes through the same helper, preserving its behaviour and subdivision schedule).
- `lemma.toml` — new import-policy entry, three new seed axioms, one new `[[oracles]]` row.

Two things worth flagging honestly. First, the numerical claim rests on sprint 078's Phase 0 sweep, which reports joint-mass margin ≥ 1e-3 at exactly `c ∈ {0.35646, 0.35647, 0.35648}` on these canonical sqrt endpoints; I could not run the wrapper here, so if the rigorous arb lower bound at `c = 0.35647` fails to clear the floor within 16384 subdivisions, the oracle raises and the candidate is rejected rather than silently accepted. Second, `certify_two_window_mass_at_35646_sqrt` now delegates to the shared helper — behaviourally identical (same endpoints, `n_trunc=200`, `dps=80`, start 256, cap 16384), but it is a refactor of a file I was told to emit whole, so it is a real edit to an existing certified path.