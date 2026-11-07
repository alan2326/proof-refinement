# Sprint 052: File `proposal_002` narrowing `proposal_001` Shape B to a precise per-`k` oracle signature

**Created**: 2026-05-02 by Planner
**Parent candidate**: *(none — fifth proposal/Scratch-only sprint in a row; the latest evaluator-passing candidate remains `Candidates/V47.lean`)*
**Target file**: *(none — this sprint produces no Lean candidate)*
**Direction**: trust-base-expansion (file a precise human-approval-ready proposal narrowing `proposal_001` Shape B based on sprint 051's NEGATIVE per-`k` evidence)

## Goal

The pre-staged decision tree in sprint 051's contract directs: on a NEGATIVE
result for the per-`k` series kernel under canonical trivial extremals
(E0–E3), the next planner files `proposal_002` narrowing `proposal_001`
Shape B from the vague "register `coeff_plus_gap_k_upper`" to a **precise,
human-decidable oracle signature** with a stated target `c_value` and
stated falsifiable acceptance criteria for the follow-up sprint that would
consume it.

Sprint 051's result is in: `RESULT: per-k kernel NEGATIVE for all canonical
trivial extremals at all c >= 0.3554 (max gap = 0.00775942 at family
E1(b_1=1), c = 0.36, α² = 0.0) -- no valid (α² >= 0.05) c-push witness
above seed`. The closest near-miss under the validity floor `α² ≥ 0.05`
(required for `circleGap ≥ 0`) is **family E2 (`a_0/b_1`) at c = 0.36 with
α² = 0.05, gap = +8.91e-4** — just below the 1e-3 target and clamped to a
narrow `α² ∈ [0.05, ≈0.06]` passing window. At c = 0.37 the gap under the
floor is already `−3.28e-4`, and the analytical break-even slider
`α²* = J(c)/(c² + J(c))` collapses from 0.061 at the seed to ~0.05 at
c=0.37 and below the floor for all c ≥ 0.38. **The crossover for the per-`k`
kernel under any canonical trivial extremal sits inside `c ∈ (0.36, 0.37)`.**

This sprint's deliverable is exactly one new file:
`ProofRefinement/Korenblum/Proposals/proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`,
filed per the `Proposals/TEMPLATE.md` shape, with the content sketched in
the "Concrete edits expected" section below.

**This sprint produces no Lean theorem.** It does not add a new candidate.
It does not register a new oracle inline (only files the proposal that the
human Alan can approve or reject before the *next* sprint registers it).
It does not modify `proposal_001`'s `Status:` field (still `pending`). The
workspace remains `BLOCKED_NEEDS_HUMAN` on `proposal_001` AND now also on
`proposal_002` after this sprint.

## Why

### What sprint 051 established

Sprint 051's `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
established that **every closed-form or finite-mode-extremal kernel
reachable from existing `Reduction.lean` reducers without a trust-base
expansion has been numerically tested above the seed and shown to fail**:

| Kernel | Source | Sprint that falsified | Best gap above seed |
|---|---|---|---|
| `c⁴ ≤ ∫ 2ρ³/Λ` (full window) | sprint 014 reducer | sprint 048 | already negative at seed |
| `c⁴/2 ≤ ∫ 2ρ³/Λ` (branch-2) | sprint 017 reducer | sprint 048 | `+1.72e-4` at seed, neg above |
| literal Wang `(15)` | seed `valid_of_eq15` | sprint 049/050 | `(0.3560, 0.3565)` crossover |
| per-`k` series under E0/E1/E2/E3 | sprint 045 reducer | sprint 051 | `+8.91e-4` at E2/c=0.36/α²=0.05 |

There is no fifth untested numerical kernel reachable without trust
expansion. The remaining route is:

> **Register an oracle in `lemma.toml:[[oracles]]` whose statement is
> directly consumed by sprint 045's reducer
> `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`,
> certifying the kernel inequality at a specific `c > 0.3554`.**

### What sprint 045's reducer needs

Reading
`ProofRefinement/Korenblum/Proof/Reduction.lean` lines 6927–6990,
`valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window` takes
a `h_witness` parameter that, given any `(a, b, K, paper)`, produces
`(ρ₁, ρ₂)` plus four side cells *plus* the kernel inequality

```lean
(∑' k : ℕ,
  if PaperAxioms.n1Pred a b k then
    PaperAxioms.coeffPlusGap a b k * c ^ (2 * k + 2) / (k + 1)
  else 0) ≤
  ∫ ρ' in ρ₁..ρ₂,
    2 * ρ' ^ 3 * PaperAxioms.sigmaZeroMinus a b ρ'
      / WangOuter.paperLambda K c ρ'
```

i.e. `Σ⁺_int(c)(a,b) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ(b)/Λ(c,ρ) dρ`.

A Lean-facing axiom that discharges this kernel cell *for every (a, b)
satisfying `Section2Assumptions`* is exactly the missing trust-base
expansion. Such an axiom is **paper-faithful** in the sense that Wang's
Section 2 implicitly proves it (the paper's whole construction reduces to
this inequality), but is **not currently exposed** by the trusted
`KorenblumPaper.{PaperAxioms, PaperEq15, OneModePaperBridge}` surface — only
`hEq15_seed_3554` (the literal Wang `(15)` at the seed) is exposed, which
sprint 049/050 showed is itself only true near the seed (crossover inside
`c ∈ (0.3560, 0.3565)`).

### What sprint 051's E0–E3 evidence tells us about the oracle shape

The four canonical trivial extremals provide a **lower bound on the
adversarial `(a, b)`-supremum** that any honest oracle must contend with:

- **E2 with α² = 0.05** at `c = 0.36`: kernel barely passes (`gap = +8.91e-4`,
  margin `+11.5%`). Any oracle certifying the kernel at `c = 0.36` must
  account for this near-miss.
- **E2 with α² = 0.05** at `c = 0.37`: kernel **fails** (`gap = −3.28e-4`).
  Any oracle certifying the kernel at `c ≥ 0.37` either (i) does so at the
  cost of strictly more restrictive `(a, b)` constraints than what sprint
  051 tested, or (ii) is provably false. Since sprint 051's test only used
  L²-normalisation and the `α² ≥ 0.05` floor (a proxy for `circleGap ≥ 0`),
  the additional restriction must come from `Section2Assumptions`'s `eq2`,
  `eq3`, `eq4` constraints linking `‖a_k‖` and `‖b_k‖` across modes.
- **E3 with α² = 0.05** at the seed: already fails (`gap = −2.02e-3`). Confirms
  that the per-`k` route's bound is tight even at the seed for two-mode
  extremals with the second mode at `k = 2` rather than `k = 1`.

The natural `c_value` ceiling for an oracle that consumes only sprint 051's
constraints (L²-mass + `α² ≥ 0.05` floor, no further paper-side coupling)
is therefore **`c ≤ 0.36`**. Pushing strictly above `0.36` requires either
(a) a paper-side reduction that bounds `Σ⁺_int(c)` using the *same paper
hypotheses* `eq2/eq3/eq4` already in `Section2Assumptions` (this is
proposal_001 Shape A's territory), or (b) a verified-interval-arithmetic
oracle that solves the constrained sup analytically and certifies it
strictly below the annulus integral — which is precisely the
*Hayman-extremal* research-grade subproblem sprint 050 demoted as
out-of-scope.

So `proposal_002` is concretely a request for shape (a) — a paper-side
analytical reduction — packaged as an oracle declaration in
`lemma.toml:[[oracles]]` with a precise, narrow numerical claim at a
specific `c`, that the human can either (i) verify via a small targeted
analytical argument and approve, or (ii) reject as "this needs a real
paper-derivable lemma instead". **Crucially, `proposal_002` does NOT ask
for an unbounded sup oracle**: it asks for the much weaker per-window claim
at a chosen `c` that sprint 051's evidence shows is at least *not falsified
under canonical trivial extremals*.

### Planner ultrathink — three candidate sprint shapes considered

1. **C1 — Sprint that ships a Lean candidate using sprint 045's reducer
   instantiated at the E2/`c = 0.36`/`α² = 0.05` near-miss with an inline
   sorry-free numerical discharge of the kernel cell.** Rejected: the
   "near-miss" gap of `+8.91e-4` is below the `1e-3` target margin sprint
   050 uses for "positive" verdicts; even at this margin, the only honest
   discharge path is to invoke an unproved inequality at the exact
   `(a, b)` chosen, which would be a **new free-floating axiom** — not an
   oracle, since no `Numerical_Library/` function can compute the
   inequality without verified-interval arithmetic over the truncated
   series. The result would be a Lean candidate whose `axioms_used` set
   includes a hand-rolled inequality the human has not approved. This
   directly violates the trust discipline of `lemma.toml:[seed_axioms]`
   and should not be queued.
2. **C2 — Sprint that files a broader `proposal_003` covering sprint 040's
   mixed kernel `c²·Σ⁺(c) ≤ ∫…` under E0–E3 as a sibling Scratch sweep,
   then queues `proposal_002` after that sweep.** Rejected: sprint 051's
   contract explicitly states that the next sprint files `proposal_002`,
   not a fifth Scratch sweep. Sprint 040's mixed kernel has the same
   `(a, b)`-dependent LHS shape as sprint 045's per-`k`, just lumped
   without per-`k` weights — and is dominated by sprint 045 at every `c`
   (since `1/(k+1) ≤ 1`), so its E0–E3 sweep would produce strictly
   weaker positive evidence than sprint 051. There is no learning value
   in the sibling sweep beyond confirmation; the planning bottleneck is
   `proposal_002` content, not sweep coverage.
3. **C3 (chosen) — File `proposal_002` with a precise narrow oracle
   signature targeting `c = 36/100 = 0.36` (the largest `c` where sprint
   051's E2 near-miss has `gap > 0` even at the validity floor), with the
   oracle's universally-quantified-`(a, b)` statement matching exactly
   sprint 045's reducer's kernel-cell shape.** Bounded (one Markdown file,
   no Lean, no Scratch), falsifiable (the proposal either is or is not
   approvable by Alan), and produces the precise human-decidable
   artifact that the workspace is BLOCKED on.

Strongest objection to C3: the proposal is essentially a request for the
human to "register Wang Section 2's whole content as an oracle at
`c = 0.36`". That is a non-trivial trust ask. **Resolution:** sprint
051's evidence narrows the ask to a *single c-value* with a *single
window* and a *concrete margin* (`+8.91e-4` at the E2 near-miss; the
oracle would need to certify a strict bound in the same window across
*all* `(a, b)` satisfying `Section2Assumptions`, which is strictly
stronger than the E0–E3 evidence — but the E0–E3 negative result at
c=0.37 means **no oracle exists at c > 0.36** under the same constraints,
so the ask is concretely "approve or reject the oracle at exactly
c = 0.36"). Alan can then either:

- **Approve**: the next sprint generator implements the oracle wrapper
  in `Numerical_Library/wang_k_kernel.py` (verified-interval-arithmetic
  truncation of the kernel inequality at c = 0.36), registers the
  `[[oracles]]` entry in `lemma.toml`, ships `Candidates/V52.lean` using
  sprint 045's reducer at c = 0.36 and discharging the kernel cell via
  the new oracle. Score: 36/100 = 9/25 > 1777/5000 — first c-push.
- **Reject** (e.g. "the oracle can't be verified analytically against
  Section2Assumptions's hidden constraints; need a paper-side lemma
  instead"): the next sprint files `proposal_003` requesting a paper-side
  enrichment of `KorenblumPaper.PaperAxioms` exposing the missing
  cross-coupling.

Either way, `proposal_002` is the human-decidable artifact that resolves
sprint 051's open question.

## Concrete edits expected

This sprint produces **no Lean edits, no `lemma.toml` edits, no Scratch
edits, no candidate edits**. Deliverables:

- `ProofRefinement/Korenblum/Proposals/proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`:
  new file, ~150–200 lines, following `Proposals/TEMPLATE.md` shape with
  the structure described in detail below.
- `ProofRefinement/Korenblum/Bulletin.md`: append exactly one line to the
  recent-events block, format
  `sprint_052 BLOCKED_NEEDS_HUMAN: filed proposal_002 narrowing proposal_001 Shape B per sprint 051's NEGATIVE evidence — precise oracle signature targeting c = 36/100 awaits Alan approval`.
  Do not reflow or restructure the bulletin.
- `ProofRefinement/Korenblum/Experience.md`: append a new dated entry under
  `### 2026-05-02 sprint_052` summarising:
  - what sprint 051's pre-staged decision tree directed,
  - the key narrowed numerical targets (c = 36/100, gap margin, α² floor),
  - the precise oracle signature filed in proposal_002,
  - the concrete decision the human is being asked to make,
  - the next-sprint branch tree (approve vs reject).

### Required content of `proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`

The file must contain at minimum the following sections, populated with
the indicated content (literal text shape; Generator may polish wording
but not weaken the precision):

1. **Header block** matching `Proposals/TEMPLATE.md`:
   - `# Proposal 002: Per-k Σ⁺_int oracle for c-push to 36/100`
   - `**Created**: 2026-05-02 by Planner` (sprint 052)
   - `**Status**: pending`
   - `**Type**: oracle` (this is an `[[oracles]]` registration request, not
     a free-floating axiom or library import)

2. **What's needed** section:
   - **File(s):** new oracle wrapper function in
     `ProofRefinement/Korenblum/Numerical_Library/wang_k_kernel.py` (the
     module already exists per sprint 052's listing — extend it, do not
     create a new module); new `[[oracles]]` entry in
     `ProofRefinement/Korenblum/lemma.toml`; new Lean-facing axiom
     declaration in a new file `ProofRefinement/Korenblum/Proof/Oracles.lean`
     (or in `Candidates/V52.lean` directly under the candidate's namespace,
     consistent with how `hEq15_seed_3554` is declared in `Candidates/V0.lean`).
   - **Lean surface:** an `axiom` of the precise type
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
     This is exactly the `h_witness` shape consumed by sprint 045's
     `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`.
     Naming convention mirrors `hEq15_seed_3554` (the seed analogue for
     the literal `(15)` discharge at c = 0.3554).
   - **Config changes:** add to `lemma.toml`:
     ```toml
     [[oracles]]
     name = "sigma_plus_int_kernel_at_36_100"
     module = "ProofRefinement.Korenblum.Numerical_Library.wang_k_kernel"
     function = "verify_sigma_plus_int_kernel_at_c"
     args = { c_num = 36, c_den = 100, rho1_num = 37, rho1_den = 100, rho2_num = 99, rho2_den = 100, n_trunc = 200, dps = 50 }
     lean_axiom = "ProofRefinement.Korenblum.Candidates.V52.hSigmaPlusIntKernel_at_36_100"
     ```
     and add `"hSigmaPlusIntKernel_at_36_100"` to `[seed_axioms].allowed`.
   - **Numerical_Library function** signature:
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
         The implementation uses verified-interval arithmetic (`flint.arb`) to
         compute upper/lower bounds on Λ and on the supremum of the LHS over
         (a, b) constrained by L²-normalisation, circleGap≥0, eq2, eq3, eq4.
         """
         raise NotImplementedError(
             "Oracle implementation pending Alan approval of proposal_002. "
             "The function body must implement a verified-interval bound on "
             "sup_{(a,b) ∈ Section2Assumptions} Σ⁺_int(c)(a,b) / ∫ 2ρ³·Z_ρ/Λ "
             "≤ 1, OR be rejected with a counter-witness (a, b) violating it."
         )
     ```

3. **Mathematical content** section:
   - State the precise kernel inequality being asserted at c = 36/100,
     ρ₁ = 37/100, ρ₂ = 99/100 (or other paper-derivable narrow window).
   - Cite sprint 051's `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
     showing E2/c=0.36/α²=0.05 has gap = +8.91e-4 (positive but narrow).
   - State explicitly that the oracle's numerical content at c = 36/100 is
     **not** verifiable by a closed-form scalar inequality (sprint 051 ruled
     that out for the trivial extremals). The oracle therefore must rely on
     **paper-side hypotheses** beyond L²-mass: specifically the eq2/eq3/eq4
     cross-coupling constraints that link `‖a_k‖` and `‖b_k‖` across modes.
   - Acknowledge the reviewer's natural concern: "this oracle is essentially
     a numerical certificate of Wang Section 2's main inequality at c = 0.36,
     which is half the paper's content". State the alternative for Alan to
     consider: instead of a numerical oracle, file a paper-side proposal
     `proposal_003` exposing the missing analytical step in
     `KorenblumPaper.PaperAxioms` (this would be the Shape A direction
     adapted to the per-`k` route).
   - Cap the c-value ceiling: per sprint 051's table, the kernel under E2
     fails at c = 0.37 with α² = 0.05 (gap = -3.28e-4), so the oracle as
     stated cannot be approved at any c > 0.36 without additional
     paper-side coupling. State this as a hard limit on the proposal's
     reach.

4. **Win unlocked** section:
   - Concrete numerical target: **`c_value = 36/100 = 0.36`**, an
     improvement of **`16/5000 = 0.0046`** over the seed `1777/5000 = 0.3554`
     (about `+1.30%` relative gain on `c`).
   - Note this is a small absolute push but is the **first workspace
     candidate to break c > 0.3554**; subsequent paper-side or oracle
     refinements (proposal_001 Shape A, or a future per-`k` ratio oracle
     spanning a wider c range) could compound on top of it.
   - The Lean-facing axiom set after approval: `{seed} ∪ {hSigmaPlusIntKernel_at_36_100}`
     (the existing `hEq15_seed_3554` becomes unused at the new c-value but
     is retained as a seed for backward-compat with V0–V47).

5. **Risk / trust cost** section:
   - **One new oracle entry** in `lemma.toml:[[oracles]]`. Trust cost is
     bounded by the rigour of the verified-interval-arithmetic implementation
     in `wang_k_kernel.py`. Alan's review burden: confirm that the
     `flint.arb`-based truncation respects all of `Section2Assumptions`'s
     constraints, including the cross-mode `eq2/eq3/eq4` couplings — this
     is **not trivial** and is the proposal's main risk.
   - **One new entry** in `[seed_axioms].allowed`. The Lean-facing axiom
     `hSigmaPlusIntKernel_at_36_100` is the same shape as `hEq15_seed_3554`
     (a paper-faithful inequality at a specific c) but at a *different
     reducer* (sprint 045 instead of `valid_of_eq15`). No new free-floating
     axiom *family* — the trust shape is precedented.
   - **Risk that the oracle cannot be implemented as stated**: if
     `wang_k_kernel.py` cannot honestly verify the universal-quantifier
     statement (because Section2Assumptions's hidden constraints aren't
     expressible at the verified-interval level), the function should
     return `False` or raise; the candidate would then fail to evaluate
     and the workspace re-blocks pending `proposal_003`. This is acceptable
     — it converts the open question from "can we push c?" to "what
     analytical infrastructure is missing?" with a precise diagnostic.

6. **Follow-up sprint outline** section:
   - **If approved**:
     - Sprint 053 (planner): re-scope to "ship `Candidates/V52.lean` proving
       `ValidKorenblumBound (36/100)` using sprint 045's reducer with the
       new oracle".
     - Sprint 053 (generator): implement `verify_sigma_plus_int_kernel_at_c`
       in `Numerical_Library/wang_k_kernel.py` per the signature above
       (interval-arithmetic bound on the truncated series with rigorous
       tail bound; reject with explicit counter-witness if the bound
       exceeds 1); register the `[[oracles]]` entry; declare the Lean
       axiom in `Candidates/V52.lean`; write `theorem
       korenblum_constant_search : ValidKorenblumBound c_value` where
       `c_value : ℝ := 36/100` and the proof body invokes
       `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
       discharging the kernel cell via `hSigmaPlusIntKernel_at_36_100`.
     - Sprint 053 (evaluator): confirm `axioms_used ⊆ {seed} ∪
       {hSigmaPlusIntKernel_at_36_100}` and `score = 36/100 = 9/25 >
       1777/5000`.
   - **If rejected** (e.g. "implementation is not honestly verifiable;
     Section2Assumptions's eq2/eq3/eq4 coupling is essential"):
     - Sprint 053 (planner): file `proposal_003` requesting a paper-side
       enrichment of `KorenblumPaper.PaperAxioms` exposing the missing
       cross-coupling lemma (Shape A direction adapted to the per-`k`
       route). Concrete shape TBD by sprint 053's planner based on Alan's
       rejection note.
   - **Acceptance criteria for sprint 053 (in either branch)**: Lean
     candidate must evaluate-pass with `score > 1777/5000` AND
     `axioms_used` set contained in the post-approval expanded seed set.

7. **Status log** section:
   - `2026-05-02 created by Planner (sprint 052) following sprint 051's
     pre-staged decision tree on NEGATIVE per-k Scratch sweep evidence.`
   - Cite `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`
     and `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`'s
     status log (last bullet) as supporting evidence.

### Required content of the `Bulletin.md` line

Append exactly one line to `Bulletin.md`'s "Recent events" block, format:

```text
sprint_052 BLOCKED_NEEDS_HUMAN: filed proposal_002 narrowing proposal_001 Shape B per sprint 051's NEGATIVE evidence — precise oracle signature targeting c = 36/100 awaits Alan approval (oracle wraps sprint 045's reducer's kernel cell; rejection branch files proposal_003 for paper-side cross-coupling enrichment)
```

### Required content of the `Experience.md` entry

Append `### 2026-05-02 sprint_052` with prose covering:

- The pre-staged decision tree from sprint 051's contract directed
  filing `proposal_002` on a NEGATIVE result; sprint 051 returned
  NEGATIVE; sprint 052 executes that directive.
- The narrowed numerical targets read off sprint 051's table: target
  `c = 36/100` (largest integer-100ths c with E2/α²=0.05 gap > 0);
  passing-window slider `α² ∈ [0.05, ≈0.06]`; near-miss margin
  `+8.91e-4` (gap-to-RHS ratio `+11.5%`).
- The precise oracle signature filed: per-`k` series kernel at fixed
  `c = 36/100` with universally-quantified `(a, b)` matching sprint
  045's `h_witness` shape.
- The concrete human decision: approve (oracle implementation in
  `wang_k_kernel.py`) or reject (paper-side enrichment via proposal_003).
- The current obstacle to `c > 0.3554`: the workspace cannot
  numerically verify the per-`k` kernel's universal-`(a, b)` claim
  without either (a) verified-interval arithmetic that respects
  Section2Assumptions's cross-mode coupling, or (b) a paper-side
  lemma that exposes the cross-coupling at the Lean type level.
- The next move: wait for Alan's approval/rejection on proposal_002.
- What would unblock a c-push faster: explicit naming of the two
  routes (Numerical_Library implementation OR paper-side enrichment),
  with the observation that the per-`k` route's c-ceiling is hard-capped
  at `0.36` under any oracle that respects only `‖a‖²+‖b‖² ≤ 1` and
  `α² ≥ 0.05` — pushing strictly above 0.36 requires the cross-coupling.

## Acceptance criteria

1. `ProofRefinement/Korenblum/Proposals/proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`
   exists, follows the `Proposals/TEMPLATE.md` shape, and contains all
   seven required sections (Header, What's needed, Mathematical content,
   Win unlocked, Risk/trust cost, Follow-up sprint outline, Status log)
   with the specific content shapes detailed in "Concrete edits expected"
   above. Specifically, the proposal MUST literally name:
   - the target `c_value = 36/100`,
   - the oracle name `sigma_plus_int_kernel_at_36_100`,
   - the `Numerical_Library` function `verify_sigma_plus_int_kernel_at_c`
     in module `wang_k_kernel`,
   - the Lean axiom name `hSigmaPlusIntKernel_at_36_100`,
   - the consuming reducer
     `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`,
   - sprint 051's NEGATIVE evidence file
     `Scratch/sprint_051_per_k_series_kernel_canonical_extremals.txt`.
2. `ProofRefinement/Korenblum/Bulletin.md` has the new
   `sprint_052 BLOCKED_NEEDS_HUMAN: …` line appended to the recent-events
   block, matching the format specified above.
3. `ProofRefinement/Korenblum/Experience.md` has a new
   `### 2026-05-02 sprint_052` entry covering the five bullets specified
   above.
4. **No new Lean theorems, definitions, or axioms.** Greppable check: the
   diff for sprint 052 contains zero changes to any `.lean` file under
   `ProofRefinement/Korenblum/` or `KorenblumPaper/`.
5. **No edits to `lemma.toml`.** Greppable check: the diff contains zero
   changes to `ProofRefinement/Korenblum/lemma.toml`. The proposal
   *describes* the `[[oracles]]` entry that *would* be added on approval;
   it does not add it.
6. **No edits to `Numerical_Library/`.** The proposal *describes* the
   `verify_sigma_plus_int_kernel_at_c` function; it does not implement it.
7. **No new `Candidates/V*.lean` file.** Greppable check: the diff
   contains no `Candidates/V52.lean` or any other new candidate file.
8. **No edits to existing proposals.** Specifically: do **not** modify
   `proposal_001`'s `Status:` field or its `## Status log`. Both proposals
   remain `pending` after sprint 052.
9. **No edits to any Scratch file.** Sprint 051's Scratch artefact is the
   evidence cited; this sprint cites it without modification.
10. The `proposal_002` file's claimed `c_value = 36/100` is consistent
    with sprint 051's table: at `c = 0.36` under E2/α²=0.05 the gap is
    positive (`+8.91e-4`), and at any `c ≥ 0.37` under E2/α²=0.05 the gap
    is negative; the proposal must not claim a c-value above 0.36 (and
    must not claim a c-value at or below the seed 0.3554).

## Out of scope

- Add any new Lean theorem, definition, or axiom (including the
  `hSigmaPlusIntKernel_at_36_100` axiom — that is for the *next* sprint
  to declare *after* Alan approves the proposal).
- Edit `Reduction.lean`, `Main.lean`, `CandidateContract.lean`, or any
  other `.lean` file in the workspace or in `KorenblumPaper/`.
- Edit `lemma.toml` (no oracle registration; no seed-axiom expansion;
  no import-policy expansion). The proposal is the human-decidable
  precursor to those edits, not the edits themselves.
- Implement `verify_sigma_plus_int_kernel_at_c` in
  `Numerical_Library/wang_k_kernel.py`. The proposal *describes* the
  signature; implementation is for the next sprint after approval.
- Create `Candidates/V52.lean` or any new candidate file.
- File `proposal_003` or any other new proposal beyond `proposal_002`.
- Run the evaluator (`Evaluator.py`) — sprint 052 ships no candidate.
- Sweep additional `(a, b)` extremal families. Sprint 051's E0–E3 sweep
  is sufficient evidence for the proposal's c-ceiling claim. Higher-mode
  finite extremals (e.g. `a_0/b_3`, `a_0/b_1/b_3`) would be queueable
  as sibling Scratch sweeps to tighten the c-ceiling further, but they
  are deferred until after Alan's decision on `proposal_002`.
- Modify `proposal_001`'s `Status:` field. Both proposals remain
  `pending`.
- Test sprint 040's mixed kernel `c²·Σ⁺(c) ≤ ∫…` under E0–E3 (sibling
  to sprint 051). Reasonable in principle, but sprint 040's kernel is
  termwise dominated by sprint 045's at every `(c, k)` (the `1/(k+1)`
  weight is removed), so its sweep would yield strictly tighter
  positive evidence and not change `proposal_002`'s c-ceiling claim.
- Any change to the seed axiom set or the `valid_of_eq15` route at the
  current seed `c = 1777/5000`. Sprint 052's proposal targets a
  *different* `c` and a *different* reducer.

## Time budget

≤ 60 minutes runtime. Breakdown:

- ~10 min: re-read `proposal_001`, sprint 051's contract, sprint 045's
  reducer signature in `Reduction.lean`, and sprint 051's Scratch output
  to ground the proposal's numerical claims and oracle shape.
- ~25 min: write `proposal_002_per_k_sigma_plus_int_oracle_for_c_push.md`
  (~150–200 lines) per the seven-section template above.
- ~10 min: write the `Experience.md` entry.
- ~5 min: append the `Bulletin.md` line.
- ~10 min: buffer for cross-checks (verify Lean axiom shape against
  sprint 045's reducer signature; verify oracle wrapper signature is
  internally consistent; verify all ten acceptance-criteria items are
  literally satisfied by the file as drafted).

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
  (Note: there is no candidate to evaluate this sprint — the
  "READY_FOR_EVALUATION" marker is repurposed as "proposal_002 in place;
  workspace remains BLOCKED on `proposal_001` AND `proposal_002` until
  human action".)
- Proposal filed cleanly per all ten acceptance criteria:
  `STATUS=BLOCKED_NEEDS_HUMAN` with note "filed proposal_002 narrowing
  proposal_001 Shape B per sprint 051's NEGATIVE evidence; precise
  oracle signature at c = 36/100 awaits Alan approval; either approval
  branch (oracle implementation) or rejection branch (paper-side
  proposal_003) is the next-sprint move".
- Generator finds the oracle signature internally inconsistent (e.g.
  the `h_witness` shape in sprint 045's reducer has changed since this
  contract was written, or the proposed window `(37/100, 99/100)` does
  not satisfy `c < ρ₁ ≤ ρ₂ < 1`): `STATUS=BLOCKED` with explicit
  diagnostic; do not file a malformed proposal. The next planner
  rewrites the contract with a corrected signature.

## Notes for the Generator

* **The proposal is the deliverable.** Do not try to be helpful by
  pre-implementing the oracle, declaring the Lean axiom, or shipping a
  Candidates/V52.lean. Those are the *next* sprint's work, contingent on
  Alan's decision. This sprint's role is to produce the precise,
  human-decidable artifact.

* **The c-value 36/100 is a hard ceiling, not an aspiration.** Sprint
  051's E2 table shows `gap = -3.28e-4` at c = 0.37 under α² = 0.05.
  Any c above 36/100 would require additional cross-coupling not
  present in sprint 051's test, and the proposal must not claim
  reach beyond 0.36 without supporting evidence.

* **Use the exact axiom name `hSigmaPlusIntKernel_at_36_100`.** This
  matches the `hEq15_seed_3554` naming convention (paper-faithful
  inequality at a specific c) and makes the relationship to the
  consuming reducer `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`
  explicit at the name level.

* **Do not weaken the oracle to be `(a, b)`-specific.** A per-extremal
  oracle (e.g. "the kernel holds at c = 0.36 for E2 with α² = 0.05")
  is not consumable by sprint 045's reducer, which requires a universal
  `(a, b)`-quantifier matching `Section2Assumptions`. The oracle's
  Lean type must match the reducer's `h_witness` parameter shape
  literally.

* **Acknowledge the proposal's hardness honestly.** The Risk/trust cost
  section must explicitly state that implementing the oracle's universal
  claim in verified-interval arithmetic is non-trivial and may turn out
  to be infeasible — at which point the rejection-branch proposal_003
  becomes the path forward. This honesty is what the Bulletin's "report
  what is hard, not what is novel" directive asks for.

* **The proposal's Win section may not promise a c-push that has not
  yet been verified.** State `c_value = 36/100` as the *target*
  contingent on the oracle's implementation succeeding; do not state it
  as a guaranteed outcome. The honest statement is "if the oracle is
  approved AND implementable, the next sprint ships `Candidates/V52.lean`
  with `c_value = 36/100`; the workspace's first c-push above the seed".

* **Bulletin update.** Append exactly one line per the format above. Do
  not reflow or restructure.

* **No proposal renumbering.** This proposal is `proposal_002`. Do not
  invent a `proposal_003` or split into multiple files. Keep at most
  three pending proposals (currently two: proposal_001 and proposal_002).

* **Confirmation that this sprint does NOT tie V0.** Per the 2026-05-02
  directive forbidding structural Lean lemmas that tie V0's `c = 0.3554`,
  this sprint ships zero Lean lemmas (greppable check #4) and therefore
  cannot tie V0. The "win" delivered is *the precise human-decidable
  oracle signature that would unlock the workspace's first `c > 0.3554`
  candidate on approval*.

* **Confirmation that the workspace remains exhaustively blocked.** Per
  sprints 048/049/050/051's cumulative evidence, the only remaining route
  to `c > 0.3554` without trust-base expansion has been ruled out.
  Sprint 052's proposal is the precise trust-base-expansion ask. Without
  Alan's decision, no further sprint can advance the c-value, and any
  sprint that *does* try to advance (e.g. by adding an inline new axiom)
  would violate the trust discipline. Sprint 052's stop-condition
  `BLOCKED_NEEDS_HUMAN` is therefore terminal until proposal_002 is
  resolved.
