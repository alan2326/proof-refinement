# Proposal 002: Per-k Σ⁺_int oracle for c-push to 36/100

**Created**: 2026-05-02 by Planner (sprint 052)
**Status**: pending
**Type**: oracle

## What's needed

- **File(s):**
  - extend `ProofRefinement/Korenblum/Numerical_Library/wang_k_kernel.py`
    (the module already exists; do not create a new module) with a new
    function `verify_sigma_plus_int_kernel_at_c` whose signature is given
    below;
  - add one new entry under `[[oracles]]` in
    `ProofRefinement/Korenblum/lemma.toml` registering this function as
    `sigma_plus_int_kernel_at_36_100`, plus a corresponding entry in
    `[seed_axioms].allowed` for the Lean-facing axiom;
  - declare a new Lean-facing axiom
    `hSigmaPlusIntKernel_at_36_100` in a new file
    `ProofRefinement/Korenblum/Proof/Oracles.lean` (or, equivalently, in
    `ProofRefinement/Korenblum/Candidates/V52.lean` directly under the
    candidate's namespace, mirroring how `hEq15_seed_3554` is declared
    inline in `Candidates/V0.lean`). Generator's choice; the
    `lemma.toml` `lean_axiom` field below assumes the latter.

- **Lean surface:** an `axiom` of exactly the type below. The signature
  matches the `h_witness` parameter consumed by sprint 045's reducer
  `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
  (`Proof/Reduction.lean` lines 6927–6990) literally, with `c` pinned to
  `36/100` instead of universally quantified:

  ```lean
  axiom hSigmaPlusIntKernel_at_36_100 :
    ∀ {a b : ℕ → ℂ} {K : ℝ → ℝ → ℝ},
      Section2Assumptions a b K (36/100 : ℝ) →
        ∃ ρ₁ ρ₂ : ℝ,
          (36/100 : ℝ) < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
          Summable (fun k : ℕ =>
            |PaperAxioms.coeffPlusGap a b k| *
              (36/100 : ℝ) ^ (2 * k + 2) / (k + 1)) ∧
          Summable (fun k : ℕ =>
            if PaperAxioms.n2Pred a b k then
              PaperAxioms.coeffMinusGap a b k * ρ₂ ^ (2 * k)
            else 0) ∧
          IntervalIntegrable
            (fun ρ' => 2 * ρ' * PaperAxioms.circleGap a b ρ')
            volume (36/100 : ℝ) 1 ∧
          IntervalIntegrable
            (fun ρ' => 2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
              / WangOuter.paperLambda K (36/100 : ℝ) ρ')
            volume ρ₁ ρ₂ ∧
          (∑' k : ℕ,
            if PaperAxioms.n1Pred a b k then
              PaperAxioms.coeffPlusGap a b k *
                (36/100 : ℝ) ^ (2 * k + 2) / (k + 1)
            else 0) ≤
            ∫ ρ' in ρ₁..ρ₂,
              2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
                / WangOuter.paperLambda K (36/100 : ℝ) ρ'
  ```

  Naming convention mirrors `hEq15_seed_3554` (paper-faithful inequality
  at a specific `c`); the suffix `_at_36_100` makes the `c`-pinning
  explicit at the name level. The axiom is specifically *not* a
  parametric `(c : ℚ) → …` shape — sprint 051's NEGATIVE evidence at
  `c = 0.37` shows the kernel fails immediately above `0.36`, so a
  parametric axiom would assert a numerically false statement at
  some inputs.

- **Config changes:** add to `ProofRefinement/Korenblum/lemma.toml`:

  ```toml
  [[oracles]]
  name = "sigma_plus_int_kernel_at_36_100"
  module = "ProofRefinement.Korenblum.Numerical_Library.wang_k_kernel"
  function = "verify_sigma_plus_int_kernel_at_c"
  args = { c_num = 36, c_den = 100, rho1_num = 37, rho1_den = 100, rho2_num = 99, rho2_den = 100, n_trunc = 200, dps = 50 }
  lean_axiom = "ProofRefinement.Korenblum.Candidates.V52.hSigmaPlusIntKernel_at_36_100"
  ```

  and append `"hSigmaPlusIntKernel_at_36_100"` to
  `[seed_axioms].allowed`. (Trust footprint stays the same shape as
  `hEq15_seed_3554`: one new entry, paper-faithful inequality at a
  specific `c`, registered through the pre-approved `[[oracles]]`
  channel.)

- **`Numerical_Library` function signature:**

  ```python
  def verify_sigma_plus_int_kernel_at_c(
      c_num: int, c_den: int,
      rho1_num: int, rho1_den: int,
      rho2_num: int, rho2_den: int,
      n_trunc: int = 200,
      dps: int = 50,
  ) -> bool:
      """
      Returns True iff the per-k series kernel inequality
          Σ⁺_int(c)(a,b) ≤ ∫_{ρ₁..ρ₂} 2ρ³ · Z_ρ(b) / Λ(c, ρ) dρ
      holds for ALL (a, b) satisfying Section2Assumptions a b K c
      where c = c_num/c_den, ρ₁ = rho1_num/rho1_den, ρ₂ = rho2_num/rho2_den.

      Σ⁺_int(c)(a,b) := ∑_{k ∈ N1(a,b)} coeffPlusGap(a,b,k) · c^(2k+2) / (k+1)

      The implementation uses verified-interval arithmetic (`flint.arb`)
      to compute upper bounds on the LHS supremum over (a, b) constrained
      by Section2Assumptions's cells (L²-normalisation, circleGap ≥ 0,
      eq2, eq3, eq4) and lower bounds on the RHS infimum over the same
      constraint set, with truncation at k = n_trunc and a rigorous tail
      bound. Returns True only when (sup LHS) < (inf RHS) is certified at
      `dps` digits of precision; returns False otherwise (optionally
      raising with an explicit counter-witness `(a, b)`).
      """
      raise NotImplementedError(
          "Oracle implementation pending Alan approval of proposal_002. "
          "The function body must implement a verified-interval bound on "
          "sup_{(a,b) ∈ Section2Assumptions} Σ⁺_int(c)(a,b) / ∫ 2ρ³·Z_ρ/Λ "
          "≤ 1, OR be rejected with a counter-witness (a, b) violating it."
      )
  ```

## Mathematical content

The oracle asserts the per-`k` series kernel inequality at a single
`(c, ρ₁, ρ₂)` triple, universally over all `(a, b, K)` satisfying
`Section2Assumptions a b K c`:

> For all `(a, b : ℕ → ℂ)` and `K : ℝ → ℝ → ℝ` with
> `Section2Assumptions a b K (36/100)`,
> ```
> Σ⁺_int(36/100)(a, b)
>   := ∑'_{k ∈ N1(a,b)} coeffPlusGap(a, b, k) · (36/100)^(2k+2) / (k+1)
>   ≤ ∫_{37/100}^{99/100} 2ρ³ · Z_ρ(b) / Λ(K, 36/100, ρ) dρ.
> ```

The narrow window `(ρ₁, ρ₂) = (37/100, 99/100)` satisfies
`c = 36/100 < 37/100 = ρ₁ ≤ ρ₂ = 99/100 < 1` and is the same window shape
as sprint 014's full-window reducer (just shifted up by one
hundredth). Sprint 045's reducer accepts any window with
`c < ρ₁ ≤ ρ₂ < 1`; the precise endpoints are the oracle's choice and
should be tuned by the implementer for tightest verified-interval bound.

### Why sprint 051's NEGATIVE evidence narrows the proposal to exactly `c = 36/100`

Sprint 051's Scratch sweep
(`Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`)
established the following per-`(c, family, α²)` table for the per-`k`
series kernel under the four canonical trivial extremals E0–E3 with the
validity floor `α² ≥ 0.05` (the smallest L²-mass on `a_0` that keeps
`circleGap ≥ 0` for the candidate witnesses):

| family   | c      | α²   | gap          |
| -------- | ------ | ---- | ------------ |
| E2       | 0.3554 | 0.05 | `+1.475e-3`  |
| **E2**   | **0.36** | **0.05** | **`+8.91e-4`** (near-miss) |
| E2       | 0.37   | 0.05 | `−3.28e-4`   |
| E2       | 0.38   | 0.05 | `−1.48e-3`   |
| E3       | 0.3554 | 0.05 | `−2.02e-3`   |

So among the canonical trivial extremals tested, the kernel under E2
with the floor `α² = 0.05` has a *positive* gap at `c = 36/100` and a
*negative* gap at `c = 37/100`. The crossover sits inside
`c ∈ (0.36, 0.37)`. The break-even slider
`α²* = J(c) / (c² + J(c))` (where `J(c) := ∫_c^1 2ρ³/Λ(c, ρ) dρ`)
collapses from `≈ 0.061` at the seed to `≈ 0.05` at `c = 0.37` and
falls below the floor for all `c ≥ 0.38`.

The oracle's proposed `c_value = 36/100` is therefore the **largest
integer-100ths `c`** for which the per-`k` kernel under any tested
canonical trivial extremal still has a positive gap above the validity
floor. It is also the largest `c` at which an honest oracle has any
chance of certifying the universal-`(a, b)` claim — at
`c ≥ 37/100`, the E2-with-`α² = 0.05` extremal is itself a
counter-witness to the universal claim.

### What the oracle must contend with that sprint 051's sweep did not

Sprint 051's E0–E3 evidence is a **lower bound on the adversarial
supremum** the oracle must dominate, not an upper bound. To certify
the universal-`(a, b)` claim at `c = 36/100` the oracle must:

1. enumerate all `(a, b)` satisfying `Section2Assumptions`'s
   structural cells — not just trivial 1- to 3-mode extremals — and
   bound `Σ⁺_int(36/100)(a, b)` from above adversarially;
2. account for the cross-mode coupling implied by `Section2Assumptions`'s
   `eq2 / eq3 / eq4` constraints, which link `‖a_k‖` and `‖b_k‖` across
   modes and are *not* captured by sprint 051's "L²-mass + α² ≥ 0.05"
   parametrisation;
3. discharge the integrability cells
   (`IntervalIntegrable` for `2ρ · circleGap` on `[c, 1]` and for
   `2ρ³ · Z_ρ / Λ` on `[ρ₁, ρ₂]`) and the two `Summable` cells. For the
   universally-quantified `(a, b)` setting these reduce to standard
   lemmas given `paper.eq4`'s coefficient envelope and the polynomial
   weight `c^(2k+2)/(k+1)` decaying geometrically in `k`.

The oracle's claim at `c = 36/100` is **not** verifiable by a
closed-form scalar inequality — sprint 051 ruled out that path for the
trivial extremals tested. The oracle therefore must rely on
`Section2Assumptions`'s **paper-side hypotheses beyond L²-mass**:
specifically the eq2/eq3/eq4 cross-coupling constraints. A
`Numerical_Library/` implementation faithful to those constraints needs
verified-interval arithmetic that respects the cross-mode bounds, and
must include a tail bound
`Σ_{k > n_trunc} |coeffPlusGap_k| · (36/100)^(2k+2) / (k+1)` that
collapses below the minimum gap.

### Reviewer's natural concern, and the alternative the human may consider

This proposal essentially asks Alan to register **a numerical
certificate of Wang Section 2's main inequality at `c = 36/100`** as a
single-purpose oracle. This is non-trivial trust expansion. The
alternative for Alan to consider, if the universal-`(a, b)` claim
turns out to be infeasible to verify at the verified-interval level,
is to **reject this proposal and request `proposal_003`** (filed by
the next planner) exposing the missing analytical step in
`KorenblumPaper.PaperAxioms`. Concretely, `proposal_003` would
request a paper-side enrichment exposing the
`sup_{(a, b) ∈ Section2Assumptions} Σ⁺_int(c)(a, b) ≤ J(c)`
inequality as a `KorenblumPaper.PaperAxioms`-level lemma derived
analytically from Wang's Section 2 — i.e. the Shape A direction of
`proposal_001` adapted to the per-`k` route. This is the
research-grade-but-paper-faithful alternative to a numerical oracle.

### Hard cap on the proposal's reach

Per sprint 051's E2 row at `c = 0.37` (`gap = −3.28e-4` under
`α² = 0.05`), the per-`k` kernel as stated is **provably false** under
the same constraint set at any `c ≥ 37/100`. The oracle therefore
cannot be approved at any `c > 36/100` without **additional
paper-side coupling not used by sprint 051's test**. The proposal
states `c = 36/100` as a hard ceiling; the next sprint after approval
must not silently push the same oracle name to a higher `c`. Any
attempt to extend would have to file a separate proposal whose
acceptance criteria include re-establishing that the kernel is at
least *not falsified* at the new `c` under E0–E3 (or extended-mode)
extremals.

## Win unlocked

- Concrete numerical target: **`c_value = 36/100 = 0.36`**. This is an
  improvement of `36/100 − 1777/5000 = 23/5000 = 0.0046` over the seed
  `1777/5000 = 0.3554`, about **`+1.30%` relative gain on `c`**.
- This would be the **first workspace candidate to break `c > 0.3554`**
  in 47+ sprints. The absolute push is small, but it converts the
  workspace from "structurally rich but pinned at the seed" to
  "actively pushing `c`", and subsequent paper-side or oracle
  refinements (proposal_001 Shape A, or a future per-`k` ratio oracle
  spanning a wider `c` range) could compound on top of it.
- The Lean-facing axiom set after approval would be
  `{seed_axioms} ∪ {hSigmaPlusIntKernel_at_36_100}`, where `seed_axioms`
  retains `hEq15_seed_3554` for backward-compat with the V0–V47
  candidate cone (which all use `valid_of_eq15` at the original seed
  `c = 1777/5000`, a path orthogonal to the new sprint 045 reducer
  route).
- **The "win" is contingent on the oracle's implementation succeeding.**
  This proposal does not promise the c-push as a guaranteed outcome.
  The honest statement: *if Alan approves AND the
  verified-interval-arithmetic implementation in
  `wang_k_kernel.py::verify_sigma_plus_int_kernel_at_c` honestly
  certifies the universal-`(a, b)` claim at `c = 36/100, dps=50,
  n_trunc=200`, then the next sprint ships `Candidates/V52.lean` with
  `c_value = 36/100`, the workspace's first c-push above the seed.*

## Risk / trust cost

- **One new oracle entry** in `lemma.toml:[[oracles]]`. Trust cost is
  bounded by the rigour of the verified-interval-arithmetic
  implementation. Alan's review burden: confirm that the `flint.arb`-
  based truncation respects all of `Section2Assumptions`'s constraints,
  including the cross-mode `eq2 / eq3 / eq4` couplings — this is
  **not trivial** and is the proposal's main risk. Sprint 051's
  evidence is silent on whether such a verifier is implementable;
  the proposal asks Alan to either (i) approve in principle and let
  the next-sprint generator attempt the implementation honestly, or
  (ii) reject and route to `proposal_003`.
- **One new entry** in `[seed_axioms].allowed`. The Lean-facing axiom
  `hSigmaPlusIntKernel_at_36_100` is the same shape as
  `hEq15_seed_3554` (a paper-faithful inequality at a specific `c`)
  but discharged by a different reducer (sprint 045 instead of
  `valid_of_eq15`). No new free-floating axiom *family* — the trust
  shape is precedented inside the workspace.
- **Risk that the oracle cannot be honestly implemented as stated.**
  If `wang_k_kernel.py` cannot verify the universal-quantifier
  statement at `dps = 50, n_trunc = 200` (because
  `Section2Assumptions`'s hidden cross-mode constraints are not
  expressible at the verified-interval level, or because the tail
  bound exceeds the minimum gap), the function should return
  `False` or raise; the candidate would then fail to evaluate and
  the workspace re-blocks pending `proposal_003`. **This outcome is
  acceptable** — it converts the open question from "can we push `c`?"
  to "what analytical infrastructure is missing?" with a precise
  diagnostic. Per the bulletin's "report what is hard, not what is
  novel" directive, an honest BLOCKED with a specific diagnostic is
  more valuable than a half-working oracle.
- **Risk that the oracle's universal claim is itself false.** Sprint
  051 only sweeps E0–E3 finite-mode extremals; higher-mode finite or
  infinite-mode extremals (Hayman-style) could in principle exceed the
  E2 near-miss and falsify the universal claim even at `c = 36/100`.
  The verified-interval implementation must contend with this in the
  honest direction — if a higher-mode counter-witness exists and is
  found by a wider sweep during implementation, the function must
  return `False`.

## Follow-up sprint outline

### If approved

1. **Sprint 053 (planner)** — re-scope to "ship `Candidates/V52.lean`
   proving `ValidKorenblumBound (36/100)` using sprint 045's reducer
   `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
   with the new oracle discharging the kernel cell".
2. **Sprint 053 (generator)** — implement
   `verify_sigma_plus_int_kernel_at_c` in
   `Numerical_Library/wang_k_kernel.py` per the signature above
   (verified-interval arithmetic on the truncated series with
   rigorous tail bound; reject explicitly with a counter-witness
   `(a, b)` if the bound exceeds 1); register the `[[oracles]]`
   entry in `lemma.toml`; declare the Lean axiom
   `hSigmaPlusIntKernel_at_36_100` in `Candidates/V52.lean`; write
   ```lean
   def c_value : ℝ := 36 / 100
   theorem korenblum_constant_search : ValidKorenblumBound c_value := by
     show ValidKorenblumBound (36 / 100 : ℝ)
     refine
       valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window
         (c := (36/100 : ℝ))
         (by norm_num) (by norm_num) ?_
     intro a b K paper
     exact hSigmaPlusIntKernel_at_36_100 paper
   ```
3. **Sprint 053 (evaluator)** — confirm
   `axioms_used ⊆ {seed} ∪ {hSigmaPlusIntKernel_at_36_100}` and
   `score = 36/100 = 9/25 > 1777/5000`.

### If rejected (e.g. "the oracle's universal claim is not honestly verifiable in `flint.arb` against the cross-mode coupling")

1. **Sprint 053 (planner)** — file `proposal_003` requesting a
   paper-side enrichment of `KorenblumPaper.PaperAxioms` exposing the
   missing cross-coupling lemma (Shape A direction of `proposal_001`
   adapted to the per-`k` route). Concrete shape TBD by sprint 053's
   planner based on Alan's rejection note. Likely target: a
   paper-faithful upper bound
   `Σ⁺_int(c)(a, b) ≤ θ(c) · (∑_k a_k² + b_k²) · J(c)` for some
   paper-derivable `θ(c) < 1`, exposed as an axiom or theorem in
   `KorenblumPaper.PaperEq4` or a new `KorenblumPaper.WangPerKBound`
   module.
2. **Sprint 054+** — implement the new paper-side bound and re-derive
   sprint 045's reducer's kernel cell from it without an oracle.

### Acceptance criteria for sprint 053 in either branch

The Lean candidate must evaluate-pass with `score > 1777/5000` AND
`axioms_used` set contained in the post-approval expanded seed set
(approval branch) or stay BLOCKED_NEEDS_HUMAN with a precise
analytical-infrastructure diagnostic (rejection branch). Sprint 053
must not silently re-tie the seed; the workspace's "tie V0" path is
exhausted under the 2026-05-02 directive.

## Status log

- 2026-05-02 created by Planner (sprint 052) following sprint 051's
  pre-staged decision tree on NEGATIVE per-k Scratch sweep evidence.
  Supporting evidence:
  `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
  (sprint 051's sweep table), and the last bullet of
  `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`'s
  Status log (which records sprint 051's NEGATIVE result and notes
  Shape B's narrowing to a precise per-`k` adversarial supremum
  oracle as the open question this proposal answers). Status: pending
  — awaiting Alan approval/rejection.
- 2026-05-02 **DEFERRED by human (Alan)**. Status remains
  `pending` but is **blocked behind sprint 053's eq15 oracle
  cascade**. Do not act on this proposal until that cascade
  is complete or has provably stalled. Rationale:
  1. Sprint 053's contract
     (`Sprint_Contracts/sprint_053_register_eq15_oracle_wrapper_at_seed.md`)
     executes the bulletin's second 2026-05-02 directive
     (Bulletin.md:219–313) by registering a verified-interval
     wrapper for Wang's literal equation `(15)`. That kernel
     is a closed-form scalar inequality in `c` alone — it
     does not depend on `(a, b)` — so an interval-arithmetic
     verifier IS honestly implementable, and the
     `[[oracles]]` channel is pre-approved per
     `AGENT_BRIEF.md` (no proposal needed). Sprint 053 has
     not yet executed.
  2. The eq15 cascade (sprints 053 → 054 → 055 → 056)
     pushes `c` to roughly `0.3562` per sprint 050's
     `mpmath dps=50, N_TRUNC=200` margin table, with zero
     proposal approvals. proposal_002's claim is for
     `c = 0.36` (a `+0.0046` jump over the seed); the eq15
     cascade gives `+0.0008` over the seed. Different scale,
     different mechanism — but the cheap/airtight path
     should be exhausted before the expensive/uncertain one
     is approved.
  3. proposal_002's universal-`(a, b)` quantification
     problem is unresolved. The proposal acknowledges this
     in §"What the oracle must contend with that sprint
     051's sweep did not" (point 2: cross-mode coupling
     from `eq2 / eq3 / eq4` is not captured by sprint 051's
     parametrisation) and in §"Risk that the oracle cannot
     be honestly implemented as stated". The function body
     in `wang_k_kernel.py::verify_sigma_plus_int_kernel_at_c`
     is currently `NotImplementedError`. Per the workspace's
     no-heuristics policy, an oracle entry whose airtight
     numerical statement is uncertain at submission time
     cannot be approved.
  4. proposal_002 itself names the correct fallback:
     `proposal_003` for a paper-side enrichment of
     `KorenblumPaper.PaperAxioms` (Shape A direction
     adapted to the per-`k` route). That is the
     research-grade-but-paper-faithful alternative if the
     eq15 cascade caps and a further `c`-push is wanted.

  ### Conditions to revisit

  Reconsider this proposal **only when all** of the
  following are true:
  - sprint 053's `certify_eq15` wrapper has shipped, V48 has
    evaluated `pass: true`, and the `[[oracles]]` channel
    has demonstrably worked end-to-end;
  - the eq15 cascade has either (a) reached its provable
    cap (`c ≈ 0.3562` per sprint 050, modulo a higher-
    precision re-verify) and stalled, OR (b) been blocked
    by some other concrete obstacle that this proposal
    addresses;
  - the Generator can demonstrate (in a `Scratch/` script,
    *before* implementation) a verified-interval bound on
    `sup_{(a,b) admissible} Σ⁺_int(36/100)(a,b)` that uses
    the `eq2 / eq3 / eq4` cross-mode coupling, not just
    L²-mass + `α² ≥ 0.05` — i.e. an honest answer to
    proposal_002 §"What the oracle must contend with"
    point 2;
  - the function body in
    `Numerical_Library/wang_k_kernel.py` has a concrete
    sketch (not `NotImplementedError`) showing the
    truncation point `K`, the analytic tail bound, and the
    `flint.arb` head computation.

  If those conditions are not met when the eq15 cascade
  caps, the right move is to file `proposal_003`
  (paper-side enrichment) and supersede proposal_002 as
  `superseded`.

  ### What the next Planner should do

  - Execute sprint 053 as written. Do not queue any sprint
    that consumes proposal_002.
  - After sprint 053 ships V48 successfully, queue
    sprints 054–056 per the bulletin's second directive
    (incremental c-push to `0.3562`).
  - Do **not** file `proposal_003` or any further
    paper-side proposal until sprint 053+ has demonstrated
    the cap.
  - Do **not** edit proposal_002's `Status:` field
    autonomously; revisit with the human only when the
    above conditions are met.
