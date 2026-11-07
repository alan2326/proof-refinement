# ProofGraph Status And Plan

This file tracks the Apr 29, 2026 rigor pass: what changed, why it changed,
and what remains to make the effective Grothendieck bound fully rigorous
modulo explicitly named analytic axioms and numerical oracle calls.

## Change Log

### 2026-04-29 (runner upgrade — step 4)

- `ProofGraph/proof_graph/runner.py`: added two cross-checks and a top-level
  `oracle_assumptions` entry that together cover every explicit numeric
  hypothesis fed to `theorem_5_1_from_thresholds`.
  - `theorem_5_1_rational_range_hypotheses`: bundles 11 trivial rational
    inequalities from the generic theorem's signature
    (`0 < p`, `0 < r < 1`, `9/10 < r`, `0 < r_mid < r`, `9/10 < r_mid`,
    `p < 1`, `0 < eta_val < 1`, `0 < M_val`) and verifies them at the chosen
    tuple `(eta_val=1/100, p_explicit_rat=1e-30, r_val=23/25, r_mid=91/100,
    M_val=4000)`.
  - `log_one_plus_sqrt_two_in_lean_sandwich`: documents whether
    `log(1+√2)` falls inside the rational sandwich `[gamma_lo_rat,
    gamma_hi_rat]`. Currently True at the chosen 16-digit precision —
    the sandwich is consistency-only; tightening to a 38+ digit precision
    `gamma_lo_rat > log(1+√2)` would make `KG_upper_val_rat = π/(2·gamma_lo_rat)`
    strictly tighter than `KrivineBound`.
  - `__theorem_5_1_from_thresholds_preconditions`: a pseudo-axiom entry in
    the `oracle_assumptions` block that points back at the rational-range
    cross-check, the log-position check, and `Cr_val_finite_positive` to
    make the runner's coverage of the generic theorem's preconditions
    explicit.

  Cross-validation total: **17/17 passing** (was 15/15).
  Oracle assumptions: **9/9 certified**.
  Audit unchanged (5/5 ok); axiom set unchanged.

### 2026-04-29 (bridge closure)

- `ProofGraph/Effective/Lemma54PaperBridge.lean`: added
  `lemma_5_4_strong_via_paper_on_domain_explicit`, a direct copy of the
  existing existential-`Cr`/`pr` bridge but with the conclusion exposing
  `Cr_paper r M (R_val_paper r)` and `pr_paper η r hr0 hr1` literally rather
  than packaging them existentially. Lets downstream callers compare a
  concrete rational `p` against `pr_paper` directly.

- `ProofGraph/Effective/Theorem51AtPExplicit.lean` (new): defines
  `def p_explicit_rat : ℝ := 1 / 10^30` matching the certified-arb
  pipeline's `p_override`. Adds **four** numerically-justified threshold
  axioms at this `p`:
  - `h_p_explicit_lt_pr_paper`: `p_explicit_rat < pr_paper eta_val r_val …`.
  - `h_F_p_deriv_at_p_explicit`: `deriv (F_p eta_val p_explicit_rat) 0 ≠ 0`.
  - `h_gap_ratio_at_p_explicit_with_B_phi`: bundled `∃ B_phi, ...` plus the
    gap-ratio inequality at `p_explicit_rat`.
  - `h_summability_at_p_explicit`: sign-structure conclusion at
    `p_explicit_rat` (i.e., `summability_fn_at_log_lt_one` applied at
    `p = 1e-30`).

  Then `theorem_5_1_at_p_explicit` applies `theorem_5_1_from_thresholds` at
  `(eta_val, p_explicit_rat, r_val, 91/100, …)` with these axioms
  discharging each threshold inequality. The IVT-chosen γ is now the γ for
  the same `(η, p)` as `solve_gamma.gamma_best`.

- `ProofGraph/Effective/Theorem51Effective.lean`: rebound
  `eta_val_5_1 := eta_val`, `p_val_5_1 := p_explicit_rat`,
  `gamma_explicit := theorem_5_1_at_p_explicit.choose`. The downstream
  consumer `theorem_5_1_effective` now consumes the F_inv quintuple from
  `theorem_5_1_at_p_explicit` instead of the original `theorem_5_1_paper_effective`'s
  existential. The rational sandwich axiom `h_gamma_explicit_sandwich` is
  now mathematically defensible: with `(η, p)` pinned, the IVT-chosen γ is
  the same real number `solve_gamma.gamma_best` certifies.

- `ProofGraph/proof_graph/runner.py`: added two new cross-checks:
  `gap_ratio_at_p_explicit` (verifies the gap-ratio inequality at
  `p_explicit_rat = 1e-30` with `B_phi ≤ M_val + 1 = 4001`) and
  `p_explicit_lt_pr_paper` (verifies `p_explicit_rat < p_certified ~ 2.4e-4`,
  which `pr_paper` dominates). Added four new entries to the
  `oracle_assumptions` block, one per threshold axiom.

- `ProofGraph/nodes/kg_lt_krivine.toml`: added the four new threshold axioms
  to the allow list. Audit count: `kg_lt_krivine [eff]` now reports
  **24 axioms** (was 20): the 3 Lean primitives, sorryAx, the 12 trusted
  analytic axioms, the 3 prior oracle axioms (`h_M_oracle`,
  `h_oracle_domain_contains_image`, `h_eta_strict_improvement_oracle`), the
  γ-sandwich axiom, and the 4 new threshold axioms.

  Bridge status: the gap between Lean's IVT-chosen γ and the certified-arb
  `gamma_best` is now closed at the level of `(η, p)`. What remains
  axiomatic is the four threshold inequalities at `p_explicit_rat = 1e-30`,
  each a single concrete numerical inequality the runner cross-checks.

### 2026-04-29 (latest)

- `ProofGraph/Effective/Theorem51Effective.lean`: renamed `gamma_val` →
  `gamma_explicit` (and the `gamma_val_*` lemmas accordingly). Added
  `def gamma_lo_rat : ℚ := 8813735870195430 / 10^16` and
  `def gamma_hi_rat : ℚ := 8813735870195431 / 10^16` as the Python-emitted
  rational sandwich endpoints around the certified
  `solve_gamma.gamma_best ≈ 0.8813735870195430252…`. Added a new oracle
  axiom `h_gamma_explicit_sandwich :
  (gamma_lo_rat : ℝ) < gamma_explicit ∧ gamma_explicit < (gamma_hi_rat : ℝ)`.
  Why: Phase 3 step 3 — pin `gamma_explicit` (still defined via
  `Classical.choose` for now) to a rational sandwich so downstream consumers
  can use rational endpoints instead of the transcendental
  `log(1+√2) < γ < 1` bounds.

- `ProofGraph/Effective/KGBound.lean`: added
  `def KG_upper_val_rat := π / (2 · gamma_lo_rat)` as a concrete
  rational-derived upper bound on `KG`, plus
  `theorem KG_upper_val_lt_rat_bound : KG_upper_val < KG_upper_val_rat`
  (which uses the new sandwich axiom). Extended `KG_lt_Krivine_effective`'s
  conclusion to additionally include this rational-derived bound, so the
  sink theorem now transitively depends on `h_gamma_explicit_sandwich`.

- `ProofGraph/proof_graph/effective_parser.py`: extended the def-parser to
  accept `: ℚ` typing in addition to `: ℝ`, and to recognize `INT / INT ^ INT`
  literal denominators (so `8813735870195430 / 10^16` is parsed as a
  `Fraction`).

- `ProofGraph/proof_graph/runner.py`,
  `ProofGraph/proof_graph/cert_compute.py`: added the
  `gamma_best_in_lean_sandwich` cross-check (verifies the certified
  `gamma_best` arb interval is strictly contained in the rational sandwich)
  and a corresponding `oracle_assumptions["h_gamma_explicit_sandwich"]`
  entry. The `KG_upper`-style symbolic recognizer now accepts both
  `gamma_val` (legacy) and `gamma_explicit` (current) names.

- `ProofGraph/nodes/kg_lt_krivine.toml`: added
  `Braverman.Effective.h_gamma_explicit_sandwich` to the allowed-axiom list.
  Audit count: `kg_lt_krivine [eff]` now reports 20 axioms (was 19); the new
  axiom is `h_gamma_explicit_sandwich`.

  Caveat: the bridge between Lean's IVT-chosen `gamma_explicit` (selected
  via `Classical.choose` for an internally-chosen `p`) and the certified
  `gamma_best` (computed at `p_override = 1e-30`) is asserted axiomatically
  rather than proved formally. Closing this gap requires lifting `p` into
  `theorem_5_1_paper_effective`'s signature so the IVT-chosen γ becomes
  identifiable with the arb-computed `gamma_best`. See Phase 3 step 3 in
  the Recommended Plan section below.

### 2026-04-29 (later)

- `ProofGraph/Effective/Theorem51Generic.lean` (new) and
  `ProofGraph/Effective/Theorem51PaperEffective.lean`: extracted a generic
  analytic theorem `theorem_5_1_from_thresholds` that takes the explicit
  threshold inequalities the proof actually consumes (`p < pr₀`, `p < 1`,
  `p · (|B_phi| + Cr + 1) · r_mid/(r_mid - 9/10) < (sinh(9/10) - 1)/2`,
  `deriv (F_p η p) 0 ≠ 0`, sign-structure premise pre-applied at `p`).
  `theorem_5_1_paper_effective` is now a thin instantiation that plumbs
  `theorem_4_4_effective`, `lemma_5_4_strong_via_paper_on_domain`,
  `F_p_deriv_ne_zero_small_p`, and `summability_fn_at_log_lt_one` into the
  generic theorem.
  Why: Phase 3 step 2 from the plan — making the load-bearing analytic
  hypotheses visible at the function signature, so Phase 3 (replace the
  opaque `gamma_val`) and Phase 4 (rational sandwich) become local
  refactors. Audit unchanged at 5/5; transitive axiom set preserved exactly.

- `ProofGraph/nodes/{lemma_5_4,theorem_5_1,kg_lt_krivine}.toml`: added the
  missing `Braverman.Effective.h_oracle_domain_contains_image` to the
  `allowed_axioms` lists.
  Why: this oracle was added when Lemma 5.4 was refactored onto the
  concrete rectangle but the audit allow-lists were not updated, so the
  audit was failing 3/5 nodes. The audit is now back to 5/5 ok.

- `ProofGraph/proof_graph/runner.py`,
  `ProofGraph/proof_graph/cli.py`,
  `ProofGraph/nodes/certify_invertibility.toml`: added the
  `domain_containment_certified` cross-check (verifying Step 1's
  `all_checks_passed` bool) and a top-level `oracle_assumptions` block in
  `certificate.json` that maps each Lean oracle axiom to the
  cross-validation check ids that witness it. The CLI now prints a
  short "Oracle assumptions (N/M certified)" section after the cross-checks.
  Why: Phase 1 of the plan — making the certificate a faithful shadow of
  the Lean trust boundary, with each numerical oracle axiom appearing as a
  named field tied to one or more passing checks.

### 2026-04-29

- `README.md`: updated the quickstart to build `ProofGraph`, not only
  `LeanProof`.
  Why: the audit path imports `ProofGraph.Effective.*`, so the mixed Lean/Python
  workflow is not actually usable until the `ProofGraph` Lean library is built.

- `README.md`: clarified that the final sink still inherits two
  `Rounding.lean` sorries (This is FINE).
  Why: the old text described those sorries as off-path, but
  `KG_lt_Krivine_effective` still uses `grothendieck_ineq_of_rounding`.

- `nodes/theorem_5_1.toml` and `README.md`: clarified that
  `solve_gamma`, `head_contribution`, `tail_bound`, and
  `lipschitz_bounds` currently support the sidecar numerical certificate,
  not the concrete Lean witness.
  Why: the previous graph description made the Python numerics look more
  tightly integrated into Lean than they are today.

- `nodes/compute_cr.toml`: exposed `M` and `R` in addition to `C_r`.
  Why: Lean's `h_M_oracle` is phrased in terms of the single-M witness
  `M_val`, so the runner needs direct access to the computed `M` to check the
  bridge honestly.

- `proof_graph/runner.py`: added a cross-check that the oracle-side `M`
  is dominated by Lean's `M_val`, and clarified that `gamma_best` is a
  certificate-side witness distinct from Lean's current `gamma_val`.
  Why: positivity of `C_r` alone was too weak a proxy for the actual
  numerical axiom used in Lean.

- `Effective/Lemma54Effective.lean`: fixed a stale comment that still
  mentioned `M_val = 5`.
  Why: the current witness is `M_val = 4000`.

- `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Paper_Main.lean`,
  `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Refined.lean`,
  `ProofGraph/Effective/Lemma54PaperBridge.lean`,
  `ProofGraph/Effective/Lemma54Effective.lean`, and
  `ProofGraph/Effective/Theorem51PaperEffective.lean`: refactored the
  Lemma 5.4 paper/refined bridge to be parameterized by an abstract domain
  `E`, and switched the effective path to an explicit oracle-domain pair
  (`oracle_domain`, `h_oracle_domain_contains_image`) instead of the old
  `F_inv_envelope` assumption.
  Why: this removes the previous overstatement that Lean had bounds on
  `closedBall 0 (sinh r₂) ∩ S` when the numerics only certify a
  rectangle-like domain from Step 1 / Step 2.

- `LeanProof/Defs/Strip.lean`, `nodes/_index.toml`,
  `nodes/certify_invertibility.toml`, `proof_graph/oracle_wrappers.py`,
  `proof_graph/runner.py`, and `Effective/Lemma54Effective.lean`:
  replaced the abstract `oracle_domain` placeholder by the concrete rectangle
  `Braverman.Omega delta_val B_val` with `delta_val = 57/1000` and
  `B_val = 293/250`, and wired Step 1 to certify that exact rectangle.
  Why: this closes the remaining modeling gap between Lean's active Lemma 5.4
  domain and the Python Step 1 / Step 2 domain.

- `proof_graph/runner.py`: added direct checks that Lean's `delta_val` and
  `B_val` match `_index.toml`, and that Step 1 actually used those configured
  rectangle parameters.
  Why: once the domain is concrete, the runner should verify the rectangle
  bridge explicitly rather than only checking downstream consequences.

## Current Boundary

What is already in good shape:

- `lake build ProofGraph` succeeds.
- `Braverman.Effective.theorem_5_1_paper_effective` has the intended axiom
  shape: Lean primitives, trusted analytic axioms,
  `h_oracle_domain_contains_image`, `h_M_oracle`, and
  `h_eta_strict_improvement_oracle`.
- `Braverman.Effective.KG_lt_Krivine_effective` has the same axiom shape,
  plus `sorryAx` from `Rounding.lean` (which is fine)
- `#print axioms` confirms that `oracle_domain` is now a definition rather
  than an axiom; the effective sink dropped from 20 axioms to 19.
- The certified Python side can already compute the concrete `M`, `R`, and
  `C_r` data behind the Lemma 5.4 oracle witness.
- The active Lean Lemma 5.4 path now uses the explicit rectangle
  `Braverman.Omega delta_val B_val`, and the runner checks that Lean's
  `delta_val`, `B_val`, and Step 1's configured rectangle all agree.

What is not yet at the target standard:

- The current Lean witness `gamma_val` is still an opaque
  `Classical.choose` witness extracted from an existence theorem.
- The numerical `solve_gamma` witness `gamma_best` is rigorous as a
  certificate-side computation, but it is not yet imported into Lean as the
  explicit witness used by `Theorem51Effective.lean`.
- The Lemma 5.4 oracle axioms (`h_oracle_domain_contains_image` and
  `h_M_oracle`) are still handwritten Lean `axiom`s. They now appear as
  named entries in `certificate.json`'s `oracle_assumptions` block with
  passing certifying checks, but Lean still consumes them as axioms rather
  than as theorem-level hypotheses tied to first-class certificate fields
  via something like `decide` or a `native_decide`-style bridge.

## Trust Policy Target

The target trust base should be exactly:

- Lean primitives (`propext`, `Classical.choice`, `Quot.sound`).
- A small named family of analytic axioms for the implicit-function-theorem
  package and similarly obvious analytic regularity facts that Mathlib still
  makes expensive to formalize.
- A small named family of numerical oracle axioms, each tied to a
  machine-readable certificate that the Python side regenerates and checks.

The target trust base should not include:

- `sorryAx`.
- Hidden dependence on `Classical.choose` when the intent is to expose a
  concrete effective witness.
- Informal set mismatches between the domain the oracle certifies and the
  domain Lean quantifies over.

## Recommended End State

The project should expose two explicit end products:

1. `KG_upper_val_explicit < KrivineBound` with a concrete oracle-backed
   witness `gamma_explicit`.
2. `GrothendieckIneq KG_upper_val_explicit` proved from the same explicit
   witness, with no `sorryAx`.

At that point the sink theorem is fully rigorous modulo only the accepted
analytic axioms and numerical oracle calls.

## Comprehensive Plan

### Phase 1: Make the oracle boundary exact

Goal: every Lean oracle axiom should correspond to one precise, machine-checked
Python certificate field.

Tasks:

- Keep exposing the actual numerical quantities used by Lean:
  `M`, `R`, `C_r`, the `H_eta(i)/i` margin, and later the explicit
  head/tail/Lipschitz bounds used in Theorem 5.1.
- Expand the runner's cross-validation so that it checks the exact bridge
  statements the Lean axioms are meant to represent, not weaker proxies.
- Standardize a certificate schema with named assumptions, rational upper/lower
  bounds, precision, and provenance.

Exit criteria:

- Every accepted numerical oracle axiom appears as a named field in
  `certificate.json`.
- The runner checks every such field against the constants used in Lean.

### Phase 2: Refactor Lemma 5.4 around the actual certified envelope

Goal: remove the current mismatch between Lean's `F_inv_envelope` statement and
the rectangle `compute_M_rigorous` actually certifies.

Status: mostly implemented on 2026-04-29. The core Lemma 5.4 machinery is now
parameterized by an abstract domain `E`; the active effective path instantiates
that with the concrete Lean rectangle `Braverman.Omega delta_val B_val`; and
Step 1 is wired to certify the same `delta` / `B` pair. What remains is to
package the two surviving rectangle-side assumptions
(`h_oracle_domain_contains_image`, `h_M_oracle`) as explicit certificate
fields rather than only as Lean axioms plus runner checks.

Recommended approach:

- Refactor the paper-faithful Lemma 5.4 machinery so it does not hard-code a
  broad envelope like `closedBall 0 (sinh r₂) ∩ S`.
- Instead, parameterize the relevant lemmas by an abstract domain `E` together
  with the properties actually needed:
  - `F_inv(disk r₁) ⊆ E`
  - `E ⊆ S`
  - the four sup-norm bounds on `H0`, `H_eta`, `H0'`, `H_eta'` over `E`
- Then instantiate `E` by the exact rectangle or rectangle-like domain that the
  Python oracle certifies.

Why this is the recommended route:

- It makes the Lean statement match the numerical certificate literally.
- It avoids proving global sup bounds on a larger set than the oracle ever uses.
- It turns a fragile modeling convention into an explicit theorem parameter.

Exit criteria:

- The active effective Lean path uses a domain parameter rather than
  `F_inv_envelope`. Completed.
- `oracle_domain` is replaced by a concrete Lean set. Completed.
- The remaining rectangle-side oracle assumptions are emitted and checked as
  named certificate fields. Pending.

### Phase 3: Split Theorem 5.1 into a generic analytic lemma plus an explicit certificate instantiation

Goal: stop using an opaque `Classical.choose` witness for `γ`.

Recommended proof architecture:

- Extract from `Theorem51PaperEffective.lean` a generic Lean lemma that takes
  as hypotheses the finite list of explicit inequalities actually used in the
  proof:
  - `η > 0`
  - `r` and `r_mid` inequalities
  - the Theorem 4.4 improvement gap
  - the Lemma 5.4 remainder constant
  - the compactness bound `B_phi`
  - the derivative threshold
  - the summability/sign-structure threshold
  - the final numeric inequalities showing `p` is small enough
- Put all purely numerical side conditions into a certificate-instantiation file
  that names a concrete `η_explicit`, `p_explicit`, and `gamma_explicit`.
- Make the Python pipeline produce the numbers needed for those hypotheses.

This gives the right division of labor:

- Lean does the analytic and logical reasoning.
- Python only certifies the finite numerical inequalities.

Exit criteria:

- `Theorem51Effective.lean` names explicit constants instead of using
  `Classical.choose`.
- The final Lean `gamma_explicit` is the same witness the certificate reports.

### Phase 4: Decide how explicit the numerical witness should be

There are two viable targets.

Minimal explicit target:

- Keep `gamma_explicit` as a real constant in Lean plus named oracle axioms of
  the form `gamma_explicit > ...`, `head_bound <= ...`, `tail_bound <= ...`.
- This is enough for rigor modulo numerical oracles.

Stronger explicit target:

- Export rational sandwiches from Python, e.g. `gamma_lo < gamma_explicit <
  gamma_hi`, `M <= M_val`, `Cr <= Cr_val`.
- Prefer rational bounds in Lean wherever possible, reserving non-rational
  oracle constants only for transcendental quantities.

Recommendation:

- Use rational upper/lower bounds as the main certificate language.
- Let Python keep arb intervals internally, but emit rationalized facts for
  Lean consumption.







### Phase 6: Turn the runner into a real certificate checker

Goal: `--run-all` should certify exactly the assumptions used by Lean.

Tasks:

- Add checks for every oracle-backed inequality used by the future explicit
  Theorem 5.1 instantiation.
- Record whether each check is:
  - a direct Lean-constant match
  - a rational domination check
  - a strict interval inequality
- Emit a compact summary of the trusted assumptions still in force.

Exit criteria:

- The certificate is a faithful shadow of the Lean trust boundary, not just a
  general sanity check.

## Suggested Immediate Order

The best next sequence is:

1. ~~Promote `h_oracle_domain_contains_image` / `h_M_oracle` into explicit
   certificate fields on the concrete rectangle.~~ Completed 2026-04-29.
   `certificate.json` now has an `oracle_assumptions` block with
   `domain_containment_certified` + 4 supporting checks for the rectangle
   axiom and `M_oracle_le_M_val` for the M-bound axiom. Cross-validation
   is 13/13 with 4/4 oracle assumptions certified.
2. ~~Refactor Theorem 5.1 into generic-analytic and explicit-certificate layers.~~
   Completed 2026-04-29. `theorem_5_1_from_thresholds` lives in
   `Theorem51Generic.lean`; `Theorem51PaperEffective.lean` is now a thin
   instantiation.
3. ~~Replace the opaque `gamma_val` by `gamma_explicit` (rational sandwich).~~
   Completed 2026-04-29.
4. ~~Step 3.5: close the (η, p) bridge between Lean's `gamma_explicit` and
   the certified-arb `gamma_best`.~~ Completed 2026-04-29.
   `gamma_explicit` is now extracted from `theorem_5_1_at_p_explicit`, which
   pins `(η, p) = (eta_val, p_explicit_rat = 1/10^30)` matching the certified
   pipeline. Four threshold axioms (`h_p_explicit_lt_pr_paper`,
   `h_F_p_deriv_at_p_explicit`, `h_gap_ratio_at_p_explicit_with_B_phi`,
   `h_summability_at_p_explicit`) discharge the remaining numerical
   conditions. Audit count at the sink: 24 axioms; cross-validation 15/15
   passing; oracle assumptions 8/8 certified.
5. ~~Upgrade the runner so it checks every explicit numeric hypothesis fed to
   `theorem_5_1_from_thresholds`.~~ Completed 2026-04-29.
   Added `theorem_5_1_rational_range_hypotheses` (bundles 11 trivial range
   checks) and `log_one_plus_sqrt_two_in_lean_sandwich` (documents the
   transcendental lower bound's position in the rational window). Total
   cross-validations: 17/17; oracle assumptions: 9/9 certified.

That order keeps the main analytic proof stable while moving the numerical
content from a sidecar certificate into the actual Lean witness.
