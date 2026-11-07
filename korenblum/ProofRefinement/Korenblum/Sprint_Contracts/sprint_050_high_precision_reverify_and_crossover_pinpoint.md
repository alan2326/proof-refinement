# Sprint 050: High-precision (`mpmath`) re-verification of the three falsified kernels and a fine-grained crossover-point pinpoint near the seed

**Created**: 2026-05-02 by Planner
**Parent candidate**: *(none — sprint 048 and sprint 049 were both roadmap/Scratch-only sprints with no Lean candidate; the latest evaluator-passing candidate remains `Candidates/V47.lean`)*
**Target file**: *(none — third roadmap/Scratch-only sprint in a row; no Lean candidate is shipped this sprint)*
**Direction**: roadmap (high-precision evidence-strengthening for `proposal_001`)

## Goal

Strengthen the evidence base for `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`
(Status: pending) by:

1. **Re-verifying** sprint 048's two falsifications (`c⁴` full-window kernel,
   `c⁴/2` branch-2 kernel) **and** sprint 049's literal Wang `(15)` kernel
   falsification using **`mpmath` interval arithmetic at `dps = 50` and
   product truncation `N_TRUNC = 200`** — to definitively settle whether
   the `scipy.quad` + `N_TRUNC = 50` results from sprints 048/049 are
   numerical artefacts or rigorous facts.
2. **Pinpointing the exact `c`-crossover** at which Wang's literal `(15)`
   transitions from positive gap (at the seed `c = 0.3554`) to negative
   gap (at `c = 0.36` per sprint 049) — by sweeping `c ∈ {0.3554, 0.3556,
   0.3560, 0.3565, 0.3570, 0.3580, 0.3590, 0.3600}` at high precision.
   This pins down whether the seed `c = 0.3554` is "at the brink" (cliff
   right above seed) or "comfortably positive but with a sharp transition"
   — informing how aggressive any structural improvement (Shape A's
   `η(c)` shrinkage from `proposal_001`) needs to be.
3. **Updating `proposal_001`'s `## Status log`** with the high-precision
   verification + crossover-point evidence, strengthening the case for
   human approval of Shape A or Shape B.

**This sprint produces no Lean theorem. It does not file a new proposal.
It updates `proposal_001`'s status log only.** The workspace remains
`BLOCKED_NEEDS_HUMAN` on `proposal_001` after this sprint.

## Why

The workspace state on 2026-05-02 (post sprint 049):

* **Sprint 048** numerically falsified two derived closing-reducer kernels
  above the seed:
  - `c⁴ ≤ ∫_{c..1} 2ρ³/Λ` (sprint 014's full-window kernel) — gap negative
    *even at the seed* (`-7.75e-03`, `-48.6 %` rel.).
  - `c⁴/2 ≤ ∫_{branchSplit c..1} 2ρ³/Λ` (sprint 017's branch-2 kernel) —
    gap barely positive at the seed (`+1.72e-04`, `+2.16 %` rel.) but
    strictly negative for every `c ∈ {0.36, …, 0.50}`.
* **Sprint 049** numerically falsified the literal Wang `(15)` integral
  inequality above the seed:
  - `1 ≤ ∫_{c..split} 12ρ³(ρ²−c²)/(c⁶Λ) + ∫_{split..1} 4ρ³/(c⁴Λ)` —
    gap comfortably positive at the seed (`+2.55e-02`, `+2.55 %` rel.)
    but immediately negative at `c = 0.36` (gap `-7.84e-02`, `-7.84 %` rel.).

The combined picture: **all three closed-form numerical kernels available
to the workspace falsify just above the seed `c = 0.3554`**. Sprint 049's
result is the most striking: the paper's *own* equation `(15)` — the
integral inequality the existing seed axiom `hEq15_seed_3554` literally
asserts — fails numerically at every `c > 0.3554` we tested.

The natural next question, asked by the human (Alan) when reviewing the
sprint-049 outcome: **is there a third novel numerical kernel candidate
that the prior sweeps haven't tested?**

### Enumeration of remaining numerical-kernel candidates (planner ultrathink)

The planner enumerated every closing reducer in `Reduction.lean` whose
kernel can be expressed as a closed-form, scalar-coefficient inequality
in `(c, ρ, ρ₁, ρ₂, …)` with no dependence on the unknown coefficient
sequences `(a_k, b_k)`:

| Reducer (sprint) | Kernel inequality | Relationship to tested kernels |
|---|---|---|
| 014 | `c⁴ ≤ ∫_{c..1} 2ρ³/Λ` | tested (sprint 048) — falsifies even at seed |
| 017 | `c⁴/2 ≤ ∫_{branchSplit c..1} 2ρ³/Λ` | tested (sprint 048) — falsifies above seed |
| 023 / 024 | same kernel as 017, larger paper-axiom signature | dominated by sprint 017's test |
| 008 | `1 ≤ ∫_{ρ₁..ρ₂} 12ρ³(ρ²−c²)/(c⁶Λ)`, `[ρ₁, ρ₂] ⊆ (c, branchSplit c]` | sub-window of sprint 049's `M1`; sprint 049 shows full `M1 = 3.9e-3 ≪ 1` at seed → sub-window cannot reach 1 → falsifies trivially |
| 018 | `1 ≤ ∫_{ρ₁..ρ₂} 4ρ³/(c⁴Λ)`, `[ρ₁, ρ₂] ⊆ (branchSplit c, 1)` | sub-window of sprint 049's `M2`; max sub-window = full window (non-negative integrand), so dominated by sprint 049's full-(15) test on `M2`-only side. Note: at seed, `M2 = 1.022 ≥ 1` *with* the `M1` contribution removed — but at `c = 0.36`, `M2 = 0.918 < 1` *without* `M1` — also fails |
| 020 | `1 ≤ ∫_{ρ₁..split} 12ρ³(ρ²−c²)/(c⁶Λ) + ∫_{split..ρ₂} 4ρ³/(c⁴Λ)`, straddling window | non-negative integrands on both pieces ⇒ full window `[c, 1]` maximises the RHS ⇒ dominated by sprint 049's literal-(15) test |
| 010 / 011-`atLeftEdge` / 012-`uniformSummable` | `(c⁶/6)/(ρ²−c²) ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ`, `ρ ∈ [ρ₁, ρ₂] ⊂ (c, branchSplit c]` (anchor on left edge) | at the worst-case anchor `ρ → branchSplit c`, `(c⁶/6)/((branchSplit c)² − c²) = (c⁶/6)/(c²/3) = c⁴/2` — so this kernel reduces to sprint 017's at the *only admissible right-endpoint* ⇒ dominated by sprint 017's test |
| 021 | decoupled `(c⁶/6)/(ρ_disk²−c²)·Z_{ρ_disk} ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ`, `ρ_disk ∈ (c, branchSplit c)` | Z-dependent on both sides; the Z-free version (worst case `Z_ρ = Z_{ρ_disk}`) reduces to sprint 010's kernel ⇒ dominated by sprint 017's test |
| 015 | `branch1SigmaKernel c ρ · ρ² · Z_ρ` disk bound | Z-dependent; closed-form RHS coincides with sprint 007's `(c⁶/6)/(ρ²−c²)·Z_ρ` after algebra ⇒ same scaling family as sprint 010 |
| 045 | `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ` (per-`k` series) | depends on `(a_k, b_k)`; **NOT closed-form numerical**; explicitly named in `proposal_001` Shape B as the route requiring the per-`k` numerical oracle |
| 040 | `c²·Σ⁺(c) ≤ ∫ 2ρ³·Z_ρ/Λ` (mixed-side) | same — depends on `(a_k, b_k)`; not closed-form numerical |
| sprint 015-derived branch-1 single-`Z` collapsed disk bound (sprints 007 / 022 / 029 / 031) | various `Z`-dependent shapes | all reduce, after extracting `Z_ρ`, to one of the closed-form kernels above |

**Conclusion of the enumeration: there is no untested closed-form,
adversarial-free numerical kernel.** Every closing reducer in
`Reduction.lean` whose kernel can be evaluated by a Python script (without
a per-`k` oracle on `(a_k, b_k)`) is dominated by — i.e. its kernel
inequality reduces to or is implied by — one of the three already-tested
kernel families: sprint 014's `c⁴` shape, sprint 017's `c⁴/2` shape, or
sprint 049's literal Wang `(15)` shape. All three have been numerically
falsified above the seed.

The remaining candidate routes — sprint 045's per-`k` series kernel and
sprint 040's mixed-side kernel — both depend on `(a_k, b_k)` and are
therefore *not* numerically tractable in `Scratch/` without committing
to a specific extremal sequence (which is research-level and beyond the
bounded-Generator-session budget).

### Decision: gather strengthening evidence and remain `BLOCKED_NEEDS_HUMAN`

Per the human's planner brief instruction:

> Decide concretely: is there a third novel numerical kernel candidate
> that the prior sweeps haven't tested? If so, queue another
> roadmap/Scratch sprint to explore it. If not — i.e., if the workspace
> genuinely has no untested kernel without proposal_001 approval — say
> so explicitly in the contract, gather any additional evidence that
> strengthens proposal_001, and remain BLOCKED.

The enumeration above is the *explicit acknowledgement* that **no such
third novel numerical kernel exists**. The sprint therefore takes the
"gather additional evidence" path. The two pieces of evidence this
sprint produces are:

1. **High-precision (`mpmath`, `dps = 50`, `N_TRUNC = 200`)
   re-verification of all three falsified kernels.** This rules out the
   possibility that `scipy.quad`'s adaptive Gauss-Kronrod tolerance or
   the `N_TRUNC = 50` truncation of the `K(c, ρ)` infinite product is
   responsible for the falsification. If the high-precision sweep
   reproduces the same sign pattern, the falsifications are rigorous
   facts, not numerical artefacts. (Both sprint 048 and sprint 049
   already cross-checked `Λ` values byte-for-byte at `dps ≈ 15`; this
   sprint's `dps = 50` is `> 3×` the precision of those checks.)
2. **Fine-grained crossover-point pinpoint near the seed for the
   literal Wang `(15)` kernel.** Sweep `c ∈ {0.3554, 0.3556, 0.3560,
   0.3565, 0.3570, 0.3580, 0.3590, 0.3600}` and report the gap at each
   point. This pins down the *width* of the positive-gap regime above
   the seed — i.e., does Wang's `(15)` go negative immediately above
   `c = 0.3554` (cliff at the seed) or hold positive up to e.g.
   `c ≈ 0.3556` before transitioning (smooth shoulder). The cliff vs.
   shoulder distinction directly informs how aggressive the structural
   `η(c)` shrinkage in `proposal_001` Shape A needs to be — a sharp
   cliff means the seed value `0.3554` is *itself* near the limit of
   the paper-faithful inequality and any push must come from a
   genuinely sharper structural bound.

This is *not* "queueing another roadmap sprint to explore a new kernel"
— the planner ultrathink concluded no such untested kernel exists. It is
the "remain BLOCKED with strengthened evidence" path.

## Concrete edits expected

This sprint produces **no Lean edits**. Deliverables:

- `ProofRefinement/Korenblum/Sprint_Contracts/sprint_050_high_precision_reverify_and_crossover_pinpoint.md`:
  this contract (created by the planner — already in place when this
  contract is materialised).
- `ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.py`:
  `mpmath`-based high-precision (`dps = 50`, `N_TRUNC = 200`) script
  that re-evaluates **all three** falsified kernels at the same `c`
  values sprints 048/049 used (`c ∈ {0.3554, 0.36, 0.37, 0.38, 0.39,
  0.40, 0.42, 0.45, 0.48, 0.50}`), printing a side-by-side comparison
  table of (a) the high-precision gap, (b) sprint 048/049's
  scipy-precision gap, (c) the absolute discrepancy between the two.
  See "Implementation skeleton (script 1)" below for the exact
  structure.
- `ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.txt`:
  captured stdout of the above script.
- `ProofRefinement/Korenblum/Scratch/sprint_050_eq15_crossover_pinpoint.py`:
  `mpmath`-based (`dps = 50`, `N_TRUNC = 200`) script that sweeps the
  literal Wang `(15)` kernel over the fine-grained `c` grid `c ∈
  {0.3554, 0.3556, 0.3560, 0.3565, 0.3570, 0.3580, 0.3590, 0.3600}`
  and prints the gap at each point. See "Implementation skeleton
  (script 2)" below.
- `ProofRefinement/Korenblum/Scratch/sprint_050_eq15_crossover_pinpoint.txt`:
  captured stdout of the above script.
- `ProofRefinement/Korenblum/Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`:
  append to the `## Status log` section a new dated bullet summarising
  the high-precision verification outcome and the crossover-point
  pinpoint outcome (no change to `Status:` field — stays `pending`).
  No other changes to `proposal_001`.
- **No changes to any `.lean` file** under `ProofRefinement/Korenblum/`
  or `KorenblumPaper/`.
- **No changes to `lemma.toml`.**
- **No new `Candidates/V*.lean` file.**
- **No new proposal file.** Specifically: this sprint does *not* file
  `proposal_002`. Both prior sprint-049-conditional routes for a
  `proposal_002` (extend the seed `(15)` axiom to a higher `c`) are
  *defeated* by sprint 049's own falsification of the literal `(15)`
  kernel above the seed, and this sprint's high-precision re-verify
  only strengthens that defeat.
- **No edits to `Bulletin.md` or `Experience.md`** (those are for the
  Generator, not the Planner; the planner's deliverable is the contract
  alone).

## Acceptance criteria

1. `ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.py`
   exists and runs to completion as
   `env UV_CACHE_DIR=korenblum/.uv-cache uv run --with mpmath python3 ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.py`
   with no uncaught exceptions.
2. `ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.txt`
   exists and contains the script's printed sweep table covering all
   three kernels (`c⁴` full-window, `c⁴/2` branch-2 window, literal
   Wang `(15)`) at the standard `c` grid `{0.3554, 0.36, 0.37, 0.38,
   0.39, 0.40, 0.42, 0.45, 0.48, 0.50}`. Each row of each kernel's
   table shall include columns: `c`, `mpmath gap`, `scipy gap`
   (read from sprint 048/049 output files or hard-coded), `|delta|`
   (absolute discrepancy).
3. The script's stdout shall contain a clearly-printed summary line for
   each kernel of the form
   `KERNEL <name>: high-precision sign agreement = AGREE/DISAGREE`
   where `AGREE` means every row's `mpmath gap` and the corresponding
   `scipy gap` from sprint 048/049 have the same sign, and `DISAGREE`
   otherwise. The expected outcome based on the planner's analysis is
   `AGREE` for all three kernels.
4. `ProofRefinement/Korenblum/Scratch/sprint_050_eq15_crossover_pinpoint.py`
   exists and runs to completion under the same `uv` invocation.
5. `ProofRefinement/Korenblum/Scratch/sprint_050_eq15_crossover_pinpoint.txt`
   exists and contains a printed table sweeping `c ∈ {0.3554, 0.3556,
   0.3560, 0.3565, 0.3570, 0.3580, 0.3590, 0.3600}` with columns
   `c`, `M1`, `M2`, `total = M1 + M2`, `gap = total − 1`, `rel = gap`.
6. The crossover script's stdout shall contain a clearly-printed
   bottom-line answer of one of the two forms:
   - `CROSSOVER: gap >= 1e-3 holds up to c = <value> (next c = <next_value> falsifies)` —
     pinning the exact rightmost `c` in the sweep with positive
     margin `≥ 1e-3`, plus the leftmost `c` with `gap < 1e-3`.
   - `CROSSOVER: gap < 1e-3 already at c = 0.3556 (no smooth shoulder)` —
     if even `c = 0.3556` fails the `gap ≥ 1e-3` margin.
7. The `mpmath`-based scripts must use `mpmath.mp.dps = 50` and
   product truncation `N_TRUNC = 200` for the `K(c, ρ)` infinite
   product. The integration must use `mpmath.quad` (not
   `scipy.integrate.quad`) — adaptive Gauss-Legendre with
   `mpmath`-precision endpoint evaluation.
8. The `mpmath`-based scripts must include a self-spot-check at
   `(c, ρ) = (0.3554, 0.5000)` and `(c, ρ) = (0.4000, 0.6000)` that
   prints `K`, `K^2`, and `Λ` at `dps = 50` and confirms agreement
   with sprint 048/049's spot-check values (`Λ(0.3554, 0.5) ≈
   3.475322e+01`, `Λ(0.4, 0.6) ≈ 5.596185e+01`) to within
   `relative tolerance 1e-12`.
9. After running both scripts, **append a new bullet to the `## Status
   log` section of `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`**
   that summarises:
   - the high-precision verification outcome (sign-agreement status
     for all three kernels at `dps = 50`, `N_TRUNC = 200`),
   - the literal-`(15)` crossover-point pinpoint result (the rightmost
     `c` with positive margin `≥ 1e-3`),
   - one sentence stating the implication for `proposal_001`'s Shape
     A (does the result tighten or relax the required `η(c)`
     schedule?) and Shape B.
   - The bullet shall not modify `proposal_001`'s `Status:` field.
10. **No new Lean theorems are added.** Greppable check: the diff for
    sprint 050 contains zero changes to any `.lean` file under
    `ProofRefinement/Korenblum/` or `KorenblumPaper/`.
11. **No edits to `lemma.toml`.** Greppable check: the diff contains
    zero changes to `ProofRefinement/Korenblum/lemma.toml`.
12. **No new `Candidates/V*.lean` file.** Greppable check: the diff
    contains no `Candidates/V50.lean` or any other new candidate file.
13. **No new proposal file.** Greppable check: the diff contains zero
    new files under `ProofRefinement/Korenblum/Proposals/` (only an
    in-place edit to the existing `proposal_001` is permitted).

## Out of scope

- Add any new Lean theorem, definition, or axiom.
- Edit `Reduction.lean`, `Main.lean`, `CandidateContract.lean`, or any
  other `.lean` file in the workspace or in `KorenblumPaper/`.
- Edit `lemma.toml` (no oracle registration; no seed-axiom expansion;
  no import-policy expansion).
- Create `Candidates/V50.lean` or any new candidate file.
- File `proposal_002` or any other new proposal — the planner's
  enumeration above shows there is no untested closed-form numerical
  kernel that would justify a new proposal.
- Modify `proposal_001`'s `Status:` field. Only the `## Status log`
  section is appended to.
- Implement an oracle wrapper in `Numerical_Library/`. The
  `mpmath`-based scripts in `Scratch/` are *exploratory* high-precision
  verifications, not Lean-facing oracles; they are invoked by the
  planner/generator pair via `uv run`, not by `Evaluator.py`.
- Run the evaluator (`Evaluator.py`) — sprint 050 ships no candidate.
- Sweep `c < 0.3554` (uninteresting — even if any kernel holds there,
  that is a regression).
- Test the per-`k` series kernel under an explicit extremal `(a, b)`
  sequence. The planner considered this candidate (proposal_001 Shape
  B's testing under e.g. a Hayman-extremal sequence) but concluded it
  exceeds a single bounded-Generator-session budget — selecting,
  computing, and validating an extremal sequence is a research move.
  That investigation is reserved for a follow-up sprint *after*
  `proposal_001` is human-reviewed.
- Audit `Numerical_Library/wang_k_kernel.py` for an existing
  high-precision implementation. Sprint 050's `mpmath`-based scripts
  are self-contained and reuse only the kernel formulas published in
  sprint 048's contract (which are themselves reproductions of
  `KorenblumPaper.WangKernelExact.lean:33`).

## Time budget

≤ 60 minutes runtime. Breakdown:

- ~15 min: implement `sprint_050_mpmath_reverify.py` (~150 lines —
  `mpmath`-based `K_truncated`, `Λ`, three kernel evaluators, side-by-side
  table formatting, sign-agreement check). Reuse the kernel formulas
  from sprint 048's branch-2 script and sprint 049's eq15 script
  *line-for-line*, swapping `math` → `mpmath.mp` and `scipy.quad` →
  `mpmath.quad`.
- ~10 min: run it (`mpmath.quad` with `dps = 50` and `N_TRUNC = 200`
  is `O(10×)` slower than `scipy.quad`; budget ~5–8 min wall-clock for
  the full sweep).
- ~10 min: implement `sprint_050_eq15_crossover_pinpoint.py` (~80
  lines — same `mpmath` machinery, finer `c` grid, simpler kernel
  evaluator just for the literal-(15) shape).
- ~5 min: run it.
- ~10 min: read both outputs, draft the one-bullet status-log update
  for `proposal_001`.
- ~10 min: buffer for `uv` environment setup if `mpmath` not cached;
  buffer for `mpmath.quad` precision adjustments if the default
  precision degree is insufficient.

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
  (Note: there is no candidate to evaluate this sprint — the
  "READY_FOR_EVALUATION" marker is repurposed as "high-precision
  evidence and crossover pinpoint in place; workspace remains BLOCKED
  on `proposal_001` review until human action".)
- Scratch script returns sign-disagreement for any kernel:
  `STATUS=BLOCKED` (means scipy-based sprints 048/049 had a numerical
  artefact — investigate and possibly file a corrective proposal,
  but this is unexpected per the planner's analysis).
- Crossover-point script confirms the literal-(15) gap goes negative
  immediately above the seed (no smooth shoulder): expected outcome,
  status remains `BLOCKED_NEEDS_HUMAN` per the bulletin directive
  (the workspace is now exhaustively confirmed-blocked on all three
  candidate kernels at `mpmath` precision).
- Both scripts complete and `proposal_001` status log is updated:
  `STATUS=BLOCKED_NEEDS_HUMAN` with note in the refinement log that
  "high-precision (`mpmath`, `dps=50`, `N_TRUNC=200`) re-verification
  of all three falsified kernels confirms scipy-precision results;
  literal-`(15)` crossover pinpointed at `c = <value>`; workspace
  remains blocked on human review of `proposal_001`".

### Implementation skeleton (script 1: `sprint_050_mpmath_reverify.py`)

```python
# ProofRefinement/Korenblum/Scratch/sprint_050_mpmath_reverify.py
import mpmath as mp

mp.mp.dps = 50
N_TRUNC = 200

# Reproduce sprints 048/049 K(c, rho) and Lambda(c, rho) at mpmath precision.
def paperFactor(c, rho, n):
    rho2 = rho * rho
    cn = c ** (2 * n)
    cnp1 = c ** (2 * n + 1)
    cnp2 = c ** (2 * n + 2)
    cnp3 = c ** (2 * n + 3)
    num = (mp.mpf(1) + rho2 * cnp1) * (mp.mpf(1) + cnp3 / rho2) * (mp.mpf(1) + cnp2) ** 2
    den = (mp.mpf(1) + rho2 * cn)   * (mp.mpf(1) + cnp2 / rho2) * (mp.mpf(1) + cnp1) ** 2
    return num / den

def K_truncated(c, rho, N=N_TRUNC):
    prod = mp.mpf(1)
    for n in range(N):
        prod *= paperFactor(c, rho, n)
    return mp.mpf(2) * rho * (mp.mpf(1) + c / (rho * rho)) * prod

def Lambda(c, rho, N=N_TRUNC):
    Kv = K_truncated(c, rho, N)
    Ksq = Kv * Kv
    if not (mp.mpf(0) < Ksq < mp.mpf(1)):
        return mp.inf
    return (mp.mpf(1) + mp.sqrt((mp.mpf(1) + 3 * Ksq) / (mp.mpf(1) - Ksq))) / 2

# Three integrand families.
def integrand_full_window(rho, c):
    L = Lambda(c, rho)
    if L == mp.inf:
        return mp.mpf(0)
    return 2 * rho ** 3 / L

def integrand_eq15_branch1(rho, c):
    L = Lambda(c, rho)
    if L == mp.inf:
        return mp.mpf(0)
    c4 = c ** 4
    c6 = c ** 6
    return 12 * rho ** 3 * (rho * rho - c * c) / (c6 * L)

def integrand_eq15_branch2(rho, c):
    L = Lambda(c, rho)
    if L == mp.inf:
        return mp.mpf(0)
    c4 = c ** 4
    return 4 * rho ** 3 / (c4 * L)

def branchSplit(c):
    return c * mp.sqrt(mp.mpf(4) / mp.mpf(3))

# scipy gap reference values from sprint 048/049 .txt files.
SCIPY_FULL_WINDOW = {
    mp.mpf("0.3554"): mp.mpf("-7.753555e-03"),
    mp.mpf("0.3600"): mp.mpf("-9.036740e-03"),
    mp.mpf("0.3700"): mp.mpf("-1.188190e-02"),
    mp.mpf("0.3800"): mp.mpf("-1.481336e-02"),
    mp.mpf("0.3900"): mp.mpf("-1.784381e-02"),
    mp.mpf("0.4000"): mp.mpf("-2.098629e-02"),
    mp.mpf("0.4200"): mp.mpf("-2.766118e-02"),
    mp.mpf("0.4500"): mp.mpf("-3.885782e-02"),
    mp.mpf("0.4800"): mp.mpf("-5.182311e-02"),
    mp.mpf("0.5000"): mp.mpf("-6.164789e-02"),
}
SCIPY_BRANCH2 = {
    mp.mpf("0.3554"): mp.mpf("1.722294e-04"),
    mp.mpf("0.3600"): mp.mpf("-6.900419e-04"),
    mp.mpf("0.3700"): mp.mpf("-2.562582e-03"),
    mp.mpf("0.3800"): mp.mpf("-4.438939e-03"),
    mp.mpf("0.3900"): mp.mpf("-6.327292e-03"),
    mp.mpf("0.4000"): mp.mpf("-8.236072e-03"),
    mp.mpf("0.4200"): mp.mpf("-1.214975e-02"),
    mp.mpf("0.4500"): mp.mpf("-1.839565e-02"),
    mp.mpf("0.4800"): mp.mpf("-2.531430e-02"),
    mp.mpf("0.5000"): mp.mpf("-3.042567e-02"),
}
SCIPY_EQ15 = {
    mp.mpf("0.3554"): mp.mpf("2.549473e-02"),
    mp.mpf("0.3600"): mp.mpf("-7.844188e-02"),
    mp.mpf("0.3700"): mp.mpf("-2.701106e-01"),
    mp.mpf("0.3800"): mp.mpf("-4.227617e-01"),
    mp.mpf("0.3900"): mp.mpf("-5.443155e-01"),
    mp.mpf("0.4000"): mp.mpf("-6.410529e-01"),
    mp.mpf("0.4200"): mp.mpf("-7.790426e-01"),
    mp.mpf("0.4500"): mp.mpf("-8.959734e-01"),
    mp.mpf("0.4800"): mp.mpf("-9.529615e-01"),
    mp.mpf("0.5000"): mp.mpf("-9.730666e-01"),
}

def evaluate_full_window(c, eps=mp.mpf("1e-3")):
    rho1 = c + eps
    rho2 = mp.mpf(1) - eps
    integral = mp.quad(lambda r: integrand_full_window(r, c), [rho1, rho2])
    lhs = c ** 4
    return integral - lhs

def evaluate_branch2(c, eps=mp.mpf("1e-3")):
    rho1 = branchSplit(c) + eps
    rho2 = mp.mpf(1) - eps
    integral = mp.quad(lambda r: integrand_full_window(r, c), [rho1, rho2])
    lhs = c ** 4 / 2
    return integral - lhs

def evaluate_eq15(c, eps=mp.mpf("1e-3")):
    split = branchSplit(c)
    M1 = mp.quad(lambda r: integrand_eq15_branch1(r, c), [c + eps, split - eps])
    M2 = mp.quad(lambda r: integrand_eq15_branch2(r, c), [split + eps, mp.mpf(1) - eps])
    return (M1 + M2) - mp.mpf(1)

# Spot checks (must agree with sprint 048/049 values).
spot_check_pairs = [(mp.mpf("0.3554"), mp.mpf("0.5"), mp.mpf("3.475322e+01")),
                    (mp.mpf("0.4"), mp.mpf("0.6"), mp.mpf("5.596185e+01"))]
print("# Spot checks (mpmath dps=50, N_TRUNC=200) -- verifying K/Lambda values")
for (c0, rho0, expected) in spot_check_pairs:
    L = Lambda(c0, rho0)
    rel_err = abs(L - expected) / expected
    status = "OK" if rel_err < mp.mpf("1e-12") else "FAIL"
    print(f"#   c={c0} rho={rho0} Lambda={mp.nstr(L, 12)} (sprint048={expected}, rel_err={mp.nstr(rel_err, 4)} -- {status})")
print()

cs = [mp.mpf("0.3554"), mp.mpf("0.36"), mp.mpf("0.37"), mp.mpf("0.38"),
      mp.mpf("0.39"), mp.mpf("0.40"), mp.mpf("0.42"), mp.mpf("0.45"),
      mp.mpf("0.48"), mp.mpf("0.50")]

for (kernel_name, evaluator, scipy_table) in [
    ("c^4 full-window (sprint 014)", evaluate_full_window, SCIPY_FULL_WINDOW),
    ("c^4/2 branch-2 (sprint 017)",  evaluate_branch2,     SCIPY_BRANCH2),
    ("paper eq(15) literal",          evaluate_eq15,        SCIPY_EQ15),
]:
    print(f"\n=== KERNEL: {kernel_name} ===")
    print(f"{'c':>8} {'mpmath gap':>22} {'scipy gap':>22} {'|delta|':>14} {'sign agree':>12}")
    print("-" * 86)
    sign_agree_all = True
    for c in cs:
        mp_gap = evaluator(c)
        sc_gap = scipy_table[c]
        delta = abs(mp_gap - sc_gap)
        sign_agree = (mp_gap > 0) == (sc_gap > 0)
        if not sign_agree:
            sign_agree_all = False
        print(f"{mp.nstr(c, 6):>8} {mp.nstr(mp_gap, 12):>22} {mp.nstr(sc_gap, 12):>22} {mp.nstr(delta, 6):>14} {str(sign_agree):>12}")
    print(f"\nKERNEL {kernel_name}: high-precision sign agreement = {'AGREE' if sign_agree_all else 'DISAGREE'}")
```

### Implementation skeleton (script 2: `sprint_050_eq15_crossover_pinpoint.py`)

```python
# ProofRefinement/Korenblum/Scratch/sprint_050_eq15_crossover_pinpoint.py
import mpmath as mp

mp.mp.dps = 50
N_TRUNC = 200
GAP_TARGET = mp.mpf("1e-3")
EPS_WINDOW = mp.mpf("1e-3")

# Reuse paperFactor / K_truncated / Lambda / integrand_eq15_branch{1,2} / branchSplit
# from sprint_050_mpmath_reverify.py -- import them or copy verbatim.
#
# (For a self-contained Scratch script the generator may copy the bodies
# verbatim.  For brevity here, only the new sweep loop is shown.)

def evaluate_eq15(c, eps=EPS_WINDOW):
    split = branchSplit(c)
    M1 = mp.quad(lambda r: integrand_eq15_branch1(r, c), [c + eps, split - eps])
    M2 = mp.quad(lambda r: integrand_eq15_branch2(r, c), [split + eps, mp.mpf(1) - eps])
    return M1, M2, (M1 + M2) - mp.mpf(1)

cs_fine = [mp.mpf("0.3554"), mp.mpf("0.3556"), mp.mpf("0.3560"),
           mp.mpf("0.3565"), mp.mpf("0.3570"), mp.mpf("0.3580"),
           mp.mpf("0.3590"), mp.mpf("0.3600")]

print(f"# Sprint 050 paper-eq(15) literal kernel: fine-grained crossover pinpoint")
print(f"# mpmath dps={mp.mp.dps}, N_TRUNC={N_TRUNC}, EPS_WINDOW={EPS_WINDOW}, GAP_TARGET={GAP_TARGET}")
print()
print(f"{'c':>10} {'M1':>22} {'M2':>22} {'total':>22} {'gap':>22}")
print("-" * 100)
last_positive_c = None
first_failing_c = None
for c in cs_fine:
    M1, M2, gap = evaluate_eq15(c)
    total = M1 + M2
    print(f"{mp.nstr(c, 6):>10} {mp.nstr(M1, 12):>22} {mp.nstr(M2, 12):>22} {mp.nstr(total, 12):>22} {mp.nstr(gap, 12):>22}")
    if gap >= GAP_TARGET:
        last_positive_c = c
    elif first_failing_c is None and last_positive_c is not None:
        first_failing_c = c
print()
if last_positive_c is not None and first_failing_c is not None:
    print(f"CROSSOVER: gap >= {GAP_TARGET} holds up to c = {last_positive_c} "
          f"(next c = {first_failing_c} falsifies)")
elif last_positive_c is not None and first_failing_c is None:
    print(f"CROSSOVER: gap >= {GAP_TARGET} holds across the entire fine sweep "
          f"(last sampled c = {last_positive_c} -- extend sweep upward)")
else:
    print(f"CROSSOVER: gap < {GAP_TARGET} already at c = 0.3556 (no smooth shoulder)")
```

### Notes for the Generator

* **Why `mpmath.quad` rather than `scipy.integrate.quad` with high tolerance.**
  `scipy.quad` truncates internally at machine double precision regardless of
  tolerance settings. `mpmath.quad` uses `mp.mp.dps` precision throughout,
  including in the integrand evaluation (where `K(c, ρ)`'s 200-factor
  product accumulates rounding errors faster at low precision). The
  point of this sprint is precisely to rule out that compounded rounding,
  not just the integration tolerance.

* **Why `N_TRUNC = 200` rather than sprint 048/049's `N_TRUNC = 50`.**
  The per-`n` factor `F_n(c, ρ) = 1 + O(c^(2n))` gives tail product
  `1 + O(c^(2N))`. At `c = 0.5`, `c^400 ≈ 10^{-121}`, far below
  `mpmath.mp.dps = 50`'s `~10^{-50}` precision floor. `N_TRUNC = 200`
  is `4×` overkill for `dps = 50`, matching sprint 048's `N = 50` for
  `dps ≈ 15`. Conservative.

* **Spot-check tolerance `1e-12`.** Sprint 048/049's spot-check `Λ`
  values are reported to 6–7 significant figures. The mpmath
  computation should agree to machine double precision (`~1e-15`)
  even though it's running at `dps = 50`, because the spot-check
  comparisons cast to standard `mpmath.mpf` and the discrepancy is
  bounded by the lower of the two precisions. `1e-12` is a very
  comfortable margin.

* **`mpmath.quad` precision degree.** `mpmath.quad` defaults to
  `degree = 6` Gauss-Legendre. For `dps = 50` and an integrand with
  no endpoint singularity (the `EPS_WINDOW = 1e-3` insets keep the
  branch-1 integrand `12ρ³(ρ²−c²)/(c⁶Λ)` away from its `ρ = c`
  vanishing point and the branch-2 integrand `4ρ³/(c⁴Λ)` away from
  `ρ = 1` — `Λ → ∞` as `ρ → 1` is *not* an integrable singularity
  for the integrand-modulating-by-`1/Λ` shape). Default `degree`
  should suffice. If acceptance criterion 8's `1e-12` spot-check
  tolerance fails, escalate `mpmath.quad`'s `maxdegree` parameter
  before investigating other sources.

* **Wall-clock budget.** `mpmath` at `dps = 50` and `N_TRUNC = 200`
  is `~50×` slower than scipy at default precision. Sprint 048's
  branch-2 sweep (10 `c` values, single integral each) ran in
  `< 5 s`. Sprint 050's `mpmath` re-verify (3 kernels × 10 `c`
  values × up to 2 integrals each = up to 60 integrations) should
  run in `~5–8 min`. If the Generator sees runtime exceeding 15 min,
  reduce `N_TRUNC` from 200 to 100 and document the change in the
  script's header comment. The result is still a substantial
  precision improvement over sprint 048/049's `N_TRUNC = 50`.

* **Status-log update template (criterion 9).** After running both
  scripts, append a bullet to `proposal_001`'s `## Status log`
  shaped roughly as:
  ```
  - 2026-05-02 high-precision (`mpmath`, `dps=50`, `N_TRUNC=200`)
    re-verification of all three falsified kernels:
    - `c^4` full-window (sprint 014): sign agreement = AGREE
    - `c^4/2` branch-2 (sprint 017): sign agreement = AGREE
    - paper eq(15) literal: sign agreement = AGREE
    All three sprint-048/049 falsifications above the seed `c = 0.3554`
    are rigorous facts at `mpmath` precision, not scipy-tolerance
    artefacts. Evidence file: `Scratch/sprint_050_mpmath_reverify.txt`.
    Fine-grained crossover-point pinpoint for the literal Wang `(15)`
    kernel: positive margin (gap >= 1e-3) holds at `c = <value>` and
    fails at `c = <value>` (i.e., the seed `c = 0.3554` is at a
    [cliff/smooth shoulder] of width ~`<delta_c>`). Implication for
    `proposal_001`: Shape A's required `η(c)` shrinkage is
    [stronger/the same/weaker] than the table in the proposal
    suggests; Shape B (per-`k` series oracle) remains the only
    alternative structural route. Status: still pending -- awaiting
    human review.
  ```
  Fill in the bracketed values from the script outputs. Keep the
  bullet to ~10 lines.

* **Confirmation that this sprint does NOT tie V0.** The 2026-05-02
  directive forbids structural Lean lemmas that tie V0's `c = 0.3554`.
  This sprint ships zero Lean lemmas (greppable check #10) and
  therefore cannot tie V0. The "win" delivered is *evidence-strengthening
  for proposal_001*, not a Lean theorem.

* **Confirmation that there is no untested third novel numerical
  kernel.** The "Why" section's enumeration table is the load-bearing
  honesty deliverable for this sprint. The Generator must NOT
  attempt to invent a fourth numerical kernel during execution — if
  the Generator finds an apparently-novel kernel during script
  implementation, escalate to `BLOCKED` and add a note for the next
  Planner. The bulletin-mandated "novelty per session" budget is
  better spent on `proposal_001` review by the human than on a
  Generator-side kernel-discovery move that the Planner has already
  ruled out.
