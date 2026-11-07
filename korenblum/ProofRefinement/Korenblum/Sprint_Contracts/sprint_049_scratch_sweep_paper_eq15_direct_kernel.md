# Sprint 049: Scratch sweep of Wang's *paper* equation `(15)` directly — third candidate kernel, distinct from sprint 048's two falsified shapes

**Created**: 2026-05-02 by Planner
**Parent candidate**: *(none — sprint 048 was roadmap-only and shipped no candidate; the latest evaluator-passing candidate remains `Candidates/V47.lean`)*
**Target file**: *(none — second roadmap/Scratch-only sprint; no Lean candidate is shipped this sprint)*
**Direction**: roadmap (Scratch numerical witness for a previously-untested kernel)

## Goal

Numerically sweep Wang's *paper-faithful* equation `(15)` directly — the
inequality

```
                       12 ρ³ (ρ² − c²)                  4 ρ³
   1   ≤   ∫_{c..split}   ─────────────  dρ   +   ∫_{split..1}  ─────  dρ
                            c⁶ Λ(c, ρ)                          c⁴ Λ(c, ρ)
```

with `split := branchSplit c = c · √(4/3)` and `Λ(c, ρ)` as in
`KorenblumPaper.WangCertificateCore.lean:16` — over a sweep of
`c ∈ {0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.42, 0.45, 0.48, 0.50}`. Identify
the largest `c` for which the inequality holds with margin `≥ 0.01` (relative
to the LHS `1`), and record whether the existing Lean reducer
`valid_of_eq15` (`Reduction.lean:93`) becomes a viable c-push route once a
matching higher-`c` seed axiom is approved.

This is the **third** candidate kernel investigation, structurally disjoint
from sprint 048's two falsified shapes:

| Sprint | Kernel LHS | Integrand | Disposition |
|---|---|---|---|
| 048 (sprint 014) | `c⁴` | `2ρ³ / Λ(c, ρ)` | falsified at seed (gap −7.75e-03) |
| 048 (sprint 017) | `c⁴/2` | `2ρ³ / Λ(c, ρ)` | barely positive at seed (+1.72e-04, 2.16 %), falsifies at all `c > 0.3554` |
| **049 (this sprint, paper `(15)` direct)** | **`1`** | **`12ρ³(ρ²−c²)/(c⁶Λ)` + `4ρ³/(c⁴Λ)`** | **untested — high prior of holding at `c > 0.3554` due to `1/c⁴`/`1/c⁶` denominator scaling** |

No Lean theorem is shipped this sprint. No edits to `lemma.toml`. No new
proposal is filed unless the sweep falsifies the kernel above the seed (in
which case `proposal_001` is updated with a "third kernel falsified too"
note that strengthens its case for human approval of Shape A or Shape B).

## Why

Sprint 048's roadmap-only sprint discovered that the two algebraically
re-arranged kernels currently used by closing reducers (`c⁴` shape,
`c⁴/2` shape) **both falsify above `c = 0.3554`**. That outcome blocked
sprint 048 with `STATUS=BLOCKED_NEEDS_HUMAN` and produced
`Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md` (Status:
pending) which names two structural shapes (A: `paper.eq4`-derived `η(c)`
shrinkage, B: per-`k` series oracle from sprint 045) for human review.

**That investigation never tested Wang's actual paper equation `(15)`.**
Sprint 048 tested the two *derived* sufficient conditions (closing
reducers built on the disk-side `c⁴/2 · Z_ρ` and `c⁴ · Z_c` bounds) but
not the literal `(15)` integral inequality the paper proves. The paper's
own kernel — `1 ≤ ∫_{c..split} 12ρ³(ρ²−c²)/(c⁶Λ) dρ + ∫_{split..1}
4ρ³/(c⁴Λ) dρ` — has structurally **different scaling**:

* **LHS is constant `1`** (not `c⁴` or `c⁴/2`).
* **Integrand on branch 2 has factor `1/c⁴`** (so the RHS *grows* as `c`
  rises — opposite to sprint 048's `2ρ³/Λ` integrand).
* **Integrand on branch 1 has factor `1/c⁶ · (ρ²−c²)`** which vanishes at
  `ρ = c` and grows as `c` rises.

The asymptotic behaviour as `c → 1⁻` is qualitatively different from
sprint 048's two shapes. The seed axiom `hEq15_seed_3554` already asserts
`(15)` at `c = 0.3554`, and the Lean reducer `valid_of_eq15` already
discharges `ValidKorenblumBound c` from any `Eq15ScalarBound K c` proof.
**If `(15)` numerically holds with margin at some `c > 0.3554`, the
c-push route is exactly: file a proposal for a new seed axiom
`hEq15_seed_<c'>` of the same shape as the existing `hEq15_seed_3554`,
and the existing `valid_of_eq15` reducer immediately discharges
`ValidKorenblumBound c'`.** No new closing reducer, no new oracle, no
disk-side bound improvement, no `paper.eq4`/`Σ⁺_int` machinery.

This is a substantially cheaper analytical chain than `proposal_001`'s
Shape A or Shape B. The single missing data point — does `(15)` hold
numerically at `c > 0.3554`? — is exactly what this sprint's `Scratch/`
script answers.

The bulletin's directive (2026-05-02) explicitly permits this kind of
exploratory Scratch sweep on a third candidate kernel that doesn't
require a proposal: per the human's instruction in the planner brief,
"the next sprint must either (i) gather more numerical evidence in
Scratch/ on a third candidate kernel that doesn't require a proposal,
or (ii) explicitly remain BLOCKED on human review". This sprint is
option (i).

## Roadmap context (carried forward from sprint 048)

This sprint does **not** supersede sprint 048's roadmap or invalidate
`proposal_001`. The relationship is:

* **Sprint 048's analysis stands**: closing reducers built on the `c⁴` /
  `c⁴/2` disk-side bounds *cannot* push `c > 0.3554` without a
  structural improvement.
* **Sprint 049 explores an orthogonal route**: the `valid_of_eq15`
  reducer in `Reduction.lean:93` is the *original* paper bridge and
  consumes the inequality `(15)` as a seed axiom. Sprint 049 tests
  whether `(15)` itself holds at higher `c`. If it does, the c-push
  route is "extend the seed axiom"; if it doesn't, sprint 048's
  conclusion (need Shape A or Shape B from `proposal_001`) is
  reinforced.
* **The two routes are decoupled**: even if `(15)` holds at `c = 0.40`,
  registering `hEq15_seed_<0.40>` requires human approval (it is a new
  free-floating axiom, scope expansion of the existing
  `[seed_axioms].allowed` set). So sprint 049's Lean follow-up sprint
  would file a proposal too — but a *different* proposal from
  `proposal_001`, with a strictly smaller trust-cost (one new seed
  axiom of identical shape to an already-approved one, vs a paper-side
  lemma derivation or a per-`k` numerical oracle).

## Concrete edits expected

This sprint produces **no Lean edits**. Deliverables:

- `ProofRefinement/Korenblum/Sprint_Contracts/sprint_049_scratch_sweep_paper_eq15_direct_kernel.md`:
  this contract (created by the planner — already in place when this
  contract is materialised).
- `ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.py`:
  Python script implementing the kernel sweep described in the
  "Implementation skeleton" section below.
- `ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.txt`:
  captured stdout of running the above script.
- *Optionally* `ProofRefinement/Korenblum/Proposals/proposal_002_extend_seed_eq15_to_higher_c.md`
  (Status: pending) **if and only if** the sweep confirms `(15)` holds
  with margin `≥ 0.01` at some `c ≥ 0.36`. This proposal would name the
  exact `c'` value, the matching new seed-axiom statement
  `hEq15_seed_<c'>`, and the route to a one-line `Candidates/V49.lean`
  invoking `valid_of_eq15` at the new `c'`. The proposal is a strictly
  *smaller* trust expansion than `proposal_001` Shape A or Shape B
  (one new constant axiom of identical shape to the already-approved
  `hEq15_seed_3554`, vs a paper-side lemma or a numerical oracle).
  The bulletin caps pending proposals at 3; we currently have 1
  pending (`proposal_001`), so adding `proposal_002` keeps us at 2/3.
- **No changes to any `.lean` file** under `ProofRefinement/Korenblum/`.
- **No changes to `lemma.toml`.**
- **No new `Candidates/V*.lean` file.**
- **No update to `proposal_001`** unless this sprint's sweep also
  falsifies, in which case append a one-paragraph "third kernel
  falsified" note to `proposal_001`'s status log (does not change
  `proposal_001`'s `Status` field).

## Acceptance criteria

1. `ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.py`
   exists and runs to completion as
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run --with scipy --with mpmath python3 ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.py`
   with no uncaught exceptions.
2. `ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.txt`
   exists and contains the script's printed sweep table including at
   minimum the rows `c ∈ {0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.42,
   0.45, 0.48, 0.50}`.
3. The output table contains, per row: `c`, `split = c·√(4/3)`,
   `M1 := ∫_{c..split} 12ρ³(ρ²−c²)/(c⁶Λ) dρ`,
   `M2 := ∫_{split..1} 4ρ³/(c⁴Λ) dρ`,
   `total := M1 + M2`,
   `gap := total − 1`,
   `rel := gap / 1 = gap`.
4. **Seed cross-check**: the row `c = 0.3554` reports `gap > 0` (since
   `hEq15_seed_3554` asserts the inequality holds at the seed, the
   numerical evaluation must agree up to a comfortable margin
   ≥ `0.001`). If the seed row's gap is negative or below `0.001`, the
   script must abort with a clearly-printed `SCRIPT BUG` message and
   the sprint is `BLOCKED` (not `BLOCKED_NEEDS_HUMAN`).
5. The script's stdout contains a clearly-printed bottom-line answer of
   one of the two forms:
   - `BEST c with gap >= 0.01 (paper eq15 direct): c = <value>`
     (the largest sweep `c > 0.3554` with margin `≥ 0.01`), or
   - `BEST c with gap >= 0.01 (paper eq15 direct): NONE -- kernel falsifies above 0.3554`
     (mirroring sprint 048's bottom-line message format).
6. The script must perform at least the following cross-checks and
   print a summary count of any soft warnings:
   - `Λ(c, ρ) ≥ 0.5` for every evaluated `(c, ρ)` (i.e.
     `paperLambda_ge_half` from `WangPaperSideConditions.lean:30`),
   - `0 < K(c, ρ)² < 1` for every evaluated `(c, ρ)` (so `Λ` is
     well-defined),
   - the integrand on branch-1 vanishes at `ρ = c⁺` (i.e. the factor
     `(ρ² − c²)`, verified by a single point evaluation at
     `ρ = c + 1e-6`).
7. **No new Lean theorems are added.** Greppable check: the diff for
   sprint 049 contains zero changes to any `.lean` file under
   `ProofRefinement/Korenblum/` or `KorenblumPaper/`.
8. **No edits to `lemma.toml`.** Greppable check: the diff contains
   zero changes to `ProofRefinement/Korenblum/lemma.toml`.
9. **No new `Candidates/V*.lean` file.** Greppable check: the diff
   contains no `Candidates/V49.lean` or any other new candidate file.
10. **Conditional proposal**: if and only if the bottom-line answer in
    criterion (5) reports a concrete `c ≥ 0.36`, a new file
    `ProofRefinement/Korenblum/Proposals/proposal_002_extend_seed_eq15_to_higher_c.md`
    exists with `Status: pending`, names the exact `c'` value, the
    Lean-facing seed-axiom statement, and the expected one-line
    candidate. If the sweep returns `NONE`, no `proposal_002` is created.
11. **Conditional proposal-001 status note**: if and only if the
    bottom-line answer reports `NONE`, a new bullet is appended to
    `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`'s
    `## Status log` section noting "2026-05-02 third candidate kernel
    (paper eq15 direct) also falsified above seed; structural
    improvement per Shape A or Shape B is now the only remaining
    route". The `Status:` field stays `pending`. If the sweep returns
    a positive `c'`, no update to `proposal_001` is needed.

## Out of scope

- Add any new Lean theorem, definition, or axiom.
- Edit `Reduction.lean`, `Main.lean`, `CandidateContract.lean`, or any
  other `.lean` file in the workspace or in `KorenblumPaper/`.
- Edit `lemma.toml` (no oracle registration; no seed-axiom expansion;
  no import-policy expansion).
- Create `Candidates/V49.lean` or any new candidate file.
- Implement any oracle wrapper in `Numerical_Library/` (the script
  uses `scipy.integrate.quad` directly — high-precision rigorous
  interval arithmetic via `mpmath`/`flint` is *optionally* welcome as
  a cross-check second pass but is not required for acceptance).
- Run the evaluator (`Evaluator.py`) — sprint 049 ships no candidate.
- Sweep `c < 0.3554` (uninteresting — even if `(15)` holds there, that
  is a regression).
- Push the sweep above `c = 0.50`. The integrand factor `1/c⁴` blows
  up as `c → 0` and is bounded as `c → 1⁻`, but the disk-side balance
  in the underlying paper proof breaks down somewhere; the script's
  table will show where the numerical RHS becomes infeasible (if it
  ever does) without a hard upper sweep bound.
- File a third proposal — the bulletin caps pending proposals at 3 and
  this sprint files at most one (`proposal_002`) conditional on the
  sweep outcome.
- Trace the full `Numerical_Library/wang_k_kernel.py` truncation
  envelope. The script truncates the `K(c, ρ)` infinite product at
  `N = 50` factors, which is comfortable overkill for a `Scratch/`
  numerical witness (per sprint 048's analysis: `c^100 ≈ 1e-30` for
  `c ≤ 0.5`).

## Time budget

≤ 45 minutes runtime. Breakdown:

- ~15 min: implement `sprint_049_paper_eq15_direct_kernel.py` (~120
  lines including the per-`(c, ρ)` `K` and `Λ` evaluators reused from
  sprint 048's branch-2 script, two `scipy.quad` calls per `c` row,
  table formatting, and the bottom-line decision logic);
- ~5 min: run it, capture stdout to `.txt` via `... | tee ...`;
- ~10 min: read the output, identify the largest `c` with `gap ≥ 0.01`,
  and decide between the two conditional follow-ups (criteria 10 vs
  11);
- ~10 min: if criterion 10 fires, draft `proposal_002`. If criterion
  11 fires, append the one-bullet status-log update to `proposal_001`;
- ~5 min: buffer for `uv` environment setup if scipy/mpmath not
  cached.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
  (Note: there is no candidate to evaluate this sprint — the
  "READY_FOR_EVALUATION" marker is repurposed as "Scratch artifacts in
  place; sprint 050 may proceed".)
- Scratch script returns negative seed gap: `STATUS=BLOCKED` (script
  bug — fix and rerun).
- Scratch script confirms `(15)` holds at `c ≥ 0.36` and `proposal_002`
  is filed: `STATUS=READY_FOR_EVALUATION` with a clear note in the
  refinement log that human review of `proposal_002` gates sprint 050.
- Scratch script falsifies `(15)` above seed and `proposal_001` is
  updated: `STATUS=BLOCKED_NEEDS_HUMAN` (the workspace is now blocked
  on human review of `proposal_001` for *all three* tested kernels;
  sprint 049's deliverable is the strengthened evidence base).

### Implementation notes for the Generator

* **Reuse sprint 048's `K(c, ρ)` and `Λ(c, ρ)` implementations
  verbatim.** They are correct and extensively cross-checked. The only
  novelty in the sprint 049 script is the integrand pair, the
  integration window split at `branchSplit c`, and the LHS constant
  `1`.

* **Implementation skeleton:**

  ```python
  # ProofRefinement/Korenblum/Scratch/sprint_049_paper_eq15_direct_kernel.py
  import math
  from scipy.integrate import quad

  N_TRUNC   = 50
  GAP_TARGET = 1e-2     # stricter than sprint 048's 1e-3 since LHS = 1
  EPS_WINDOW = 1e-3

  def paperFactor(c, rho, n):
      num = ((1.0 + rho**2 * c**(2*n+1)) *
             (1.0 + c**(2*n+3) / rho**2) *
             (1.0 + c**(2*n+2))**2)
      den = ((1.0 + rho**2 * c**(2*n)) *
             (1.0 + c**(2*n+2) / rho**2) *
             (1.0 + c**(2*n+1))**2)
      return num / den

  def K_truncated(c, rho, N=N_TRUNC):
      prod = 1.0
      for n in range(N):
          prod *= paperFactor(c, rho, n)
      return 2.0 * rho * (1.0 + c / rho**2) * prod

  _warnings = {"lambda_below_half": 0, "ksq_out_of_unit": 0}

  def Lambda(c, rho, N=N_TRUNC):
      Kv = K_truncated(c, rho, N)
      Ksq = Kv * Kv
      if not (0.0 < Ksq < 1.0):
          _warnings["ksq_out_of_unit"] += 1
          return float("inf")
      val = (1.0 + math.sqrt((1.0 + 3.0 * Ksq) / (1.0 - Ksq))) / 2.0
      if val < 0.5 - 1e-12:
          _warnings["lambda_below_half"] += 1
      return val

  def integrand1(rho, c):
      L = Lambda(c, rho)
      if math.isinf(L):
          return 0.0
      # Wang (15) branch-1 kernel: 12 rho^3 (rho^2 - c^2) / (c^6 * Lambda).
      return 12.0 * rho**3 * (rho**2 - c**2) / (c**6 * L)

  def integrand2(rho, c):
      L = Lambda(c, rho)
      if math.isinf(L):
          return 0.0
      # Wang (15) branch-2 kernel: 4 rho^3 / (c^4 * Lambda).
      return 4.0 * rho**3 / (c**4 * L)

  def branchSplit(c):
      return c * math.sqrt(4.0 / 3.0)

  def evaluate(c, eps=EPS_WINDOW):
      split = branchSplit(c)
      # Window inset on both sides of the split to keep rho strictly inside
      # (c, split) and (split, 1).
      M1, _ = quad(integrand1, c + eps, split - eps, args=(c,), limit=400)
      M2, _ = quad(integrand2, split + eps, 1.0 - eps, args=(c,), limit=400)
      total = M1 + M2
      gap = total - 1.0
      return split, M1, M2, total, gap

  def main():
      cs = [0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.42, 0.45, 0.48, 0.50]
      print("# Sprint 049 paper eq(15) direct kernel sweep")
      print(f"# N_TRUNC = {N_TRUNC}, EPS_WINDOW = {EPS_WINDOW}, "
            f"GAP_TARGET = {GAP_TARGET}")
      print()
      # Branch-1 vanishing cross-check at rho = c + 1e-6.
      c0 = 0.3554
      val_at_c = integrand1(c0 + 1e-6, c0)
      print(f"# Branch-1 integrand at rho=c+1e-6 (should ~0): "
            f"{val_at_c:.6e}")
      print()
      header = (f"{'c':>8} {'split':>10} "
                f"{'M1':>14} {'M2':>14} {'total':>14} "
                f"{'gap':>14} {'rel':>10}")
      print(header)
      print("-" * len(header))
      seed_gap = None
      best_c = None
      for c in cs:
          split, M1, M2, total, gap = evaluate(c)
          rel = gap / 1.0
          print(f"{c:>8.4f} {split:>10.4f} "
                f"{M1:>14.6e} {M2:>14.6e} {total:>14.6e} "
                f"{gap:>14.6e} {rel:>10.4f}")
          if abs(c - 0.3554) < 1e-9:
              seed_gap = gap
          if c > 0.3554 and gap >= GAP_TARGET:
              if best_c is None or c > best_c:
                  best_c = c
      print()
      print(f"# Soft-warning counts: {_warnings}")
      print()
      if seed_gap is None or seed_gap < 1e-3:
          print(f"SCRIPT BUG: seed cross-check failed (gap={seed_gap}) "
                "-- sprint contract acceptance criterion 4 violated.")
          return
      print(f"# Seed cross-check: c = 0.3554, gap = {seed_gap:.6e} (OK >0)")
      print()
      if best_c is not None:
          print(f"BEST c with gap >= {GAP_TARGET} (paper eq15 direct): "
                f"c = {best_c}")
      else:
          print(f"BEST c with gap >= {GAP_TARGET} (paper eq15 direct): "
                "NONE -- kernel falsifies above 0.3554")

  if __name__ == "__main__":
      main()
  ```

* **Why this kernel is *not* trivially equivalent to sprint 048's
  shapes.** Wang's `(15)` is the integrated form of `(12) + (13)` where
  `(12)` and `(13)` are the disk-side mass conditions on each branch.
  The closing reducers in sprint 014 / sprint 017 / sprint 023 derive
  *sufficient conditions* on a *single* aggregated kernel inequality of
  shape `disk-side-scalar ≤ ∫ 2ρ³/Λ` after algebraically rearranging
  the disk-side mass into a single closed-form `c⁴` (sprint 014) or
  `c⁴/2` (sprint 017) bound. That algebraic rearrangement
  *over-approximates* the disk-side mass in the worst direction: the
  proof bounds `diskExcess` from above by `c⁴ · sigmaZeroMinus c` (or
  `c⁴/2`), then drops the `Λ`-dependence of the disk-side mass entirely,
  then composes with an annulus lower bound. The original `(15)` keeps
  the disk-side and annulus-side `Λ`-coupling intact through the
  `1/c⁴`, `1/c⁶` weighting — which is *not* an over-approximation in
  the same direction. The sprint 048 result is therefore *not* a
  refutation of the original `(15)` inequality at `c > 0.3554`. The
  sweep is a genuine new data point.

* **Why `GAP_TARGET = 0.01` (vs sprint 048's `0.001`).** The LHS in
  `(15)` is `1` (not `c⁴/2 ≈ 0.008` at the seed); a relative margin of
  `1 %` of the LHS is `0.01` (vs sprint 048's `0.001` which is a `12 %`
  relative margin against `c⁴/2 = 0.008`). Both are "safely positive
  with margin"; the absolute target is what differs.

* **What success looks like:** if the script reports e.g.
  `BEST c with gap >= 0.01 (paper eq15 direct): c = 0.45`, then a
  follow-up sprint can:
  1. File `proposal_002_extend_seed_eq15_to_higher_c.md` (Status:
     pending) requesting human approval of a new seed axiom
     `hEq15_seed_<c'>` of the same shape as `hEq15_seed_3554`.
  2. After approval, ship `Candidates/V49.lean` as a one-line
     invocation of `valid_of_eq15` at `c = c'`. Expected `axioms_used`
     set: V0 minus `hEq15_seed_3554`, plus `hEq15_seed_<c'>`. Score:
     `c_value = c' > 1777/5000`. **This is the win the bulletin
     directive asks for.**

* **What failure looks like:** if the script reports `NONE`, then the
  paper's own `(15)` does not hold at higher `c` either, which strongly
  reinforces `proposal_001`'s case (Shape A's `paper.eq4`-derived
  `η(c)` shrinkage or Shape B's per-`k` series oracle become the only
  remaining structural routes). Append a one-bullet update to
  `proposal_001`'s `## Status log` in that case; the `Status:` field
  stays `pending`.

* **Why this is *not* outside scope.** The bulletin's
  "Scratch-first then Lean" rule explicitly invites this kind of
  exploratory numerical investigation; the planner brief explicitly
  authorises "gather more numerical evidence in Scratch/ on a third
  candidate kernel that doesn't require a proposal" as one of the two
  permitted next-sprint shapes. This sprint is exactly that, with the
  third kernel being the literal paper-eq-(15) inequality the seed
  axiom asserts at `c = 0.3554`.

* **What this sprint does *not* attempt.** Sprint 049 does not write
  any Lean. It does not register any oracle. It does not file
  `proposal_002` unconditionally — only if the sweep confirms the
  kernel holds with margin. It does not modify `proposal_001` unless
  the sweep falsifies the kernel. It does not test the sprint 020
  straddling-window kernel, the sprint 008 branch-1 sub-window kernel,
  or the sprint 045 per-`k` series kernel — those are reserved for
  follow-up sprints if and only if `(15)` direct also falsifies
  (in which case the next planner has three candidates to choose
  from for sprint 050's structural Scratch sweep).

* **Cross-check against sprint 048's `Λ` numbers.** Sprint 048's
  branch-2 script reports the spot check
  `c=0.3554 rho=0.5000 Lambda=3.475322e+01` and
  `c=0.4000 rho=0.6000 Lambda=5.596185e+01`. Sprint 049's script must
  reproduce these exact values (modulo `scipy.quad` rounding) in its
  spot-check section. If the `Λ` numbers diverge from sprint 048's by
  more than `1e-6`, the `K`/`Λ` implementation has been corrupted in
  the cut-and-paste from sprint 048; abort with a clear error.
