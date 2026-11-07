# Sprint 048: Roadmap to `c > 0.3554` — kernel selection, numerical Scratch witness, and oracle/proof gap analysis

**Created**: 2026-05-02 by Planner
**Parent candidate**: `Candidates/V47.lean`
**Target file**: *(none — roadmap-only sprint, no new candidate)*
**Direction**: roadmap

## Goal

Produce a written **roadmap to a `c_value > 1777/5000`** as the body of this
contract, plus at least one numerical `Scratch/` script that confirms (or
falsifies) the proposed kernel inequality at the candidate `(c, ρ₁, ρ₂)`. **No
new Lean theorem is shipped this sprint.** This is the explicit Step-1 sprint
the new bulletin directive (2026-05-02) demands before any further Lean work.

## Why

Forty-seven sprints, zero `c_value` improvement, zero `Scratch/` files, zero
`Proposals/` entries. The bulletin's new directive (2026-05-02) makes
**`c_value > 1777/5000` the only success criterion** for sprint 049 onward
and explicitly demands that sprint 048 be a roadmap-only sprint, not another
structural Lean lemma. This sprint discharges that directive.

## Roadmap to `c > 0.3554`

This section answers the six questions enumerated in the bulletin's directive,
in order.

### Q1 — Which existing closing reducer is the cheapest path to `c > 0.3554`?

**Pick: `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`** (sprint 017,
`Reduction.lean:2075`).

Comparison of the four leading candidates:

| Reducer | Paper-axiom signature | Oracle cells | Effective kernel inequality | Window |
|---|---|---|---|---|
| sprint 014 `valid_of_disk_eq3_eq4_annulus_eq8_eq9_full_window` | `{eq3, eq4, eq8, eq9}` | 0 | `c⁴ ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ` | `(c, 1)` |
| **sprint 017 `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`** | **`{eq6, eq8, eq9}`** | **0** | **`c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ`** | **`(branchSplit c, 1)`** |
| sprint 023 `valid_of_disk_eq2_eq3_eq4_collapse_annulus_eq8_eq9_branch2_window` | `{eq2, eq3, eq4, eq8, eq9}` | 0 | `c⁴/2 ≤ ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ` | `[branchSplit c, 1)` |
| sprint 045 `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window` | `{eq8, eq9}` | 0 | `Σ⁺_int(c) ≤ ∫_{ρ₁..ρ₂} 2ρ³·Z_ρ/Λ(c, ρ) dρ` | `(c, 1)` |

Sprint 017's kernel inequality is **strictly half** the LHS of sprint 014's
on **the same window family** `[ρ₁, ρ₂] ⊂ (branchSplit c, 1)`, because the
branch-2 disk bound `(c⁴/2) · Z_ρ` from `paper.eq6` is half of sprint 013's
`c⁴ · Z_c` bound. Sprint 023 has the **same** kernel as sprint 017 but a
larger paper-axiom signature. Sprint 045's kernel involves `Σ⁺_int(c)`, the
per-`k` series quantity that depends on the unknown `(a_k, b_k)` — it is
**not numerically tractable in `Scratch/` without an adversarial choice**, so
it cannot be falsified or confirmed by a Python script. Sprint 014 is
purely numerical but its kernel is **strictly weaker** than sprint 017's on
the branch-2 window. Therefore sprint 017 is the cheapest closed-form,
oracle-cell-free path to `c > 0.3554`.

### Q2 — What is the numerical kernel?

The kernel inequality to verify at the candidate `(c, ρ₁, ρ₂)`:

```
        c⁴/2  ≤  ∫_{ρ₁}^{ρ₂}  2ρ³ / Λ(c, ρ)  dρ
```

with the explicit definitions:

- `Λ(c, ρ) := (1 + sqrt((1 + 3·K(c,ρ)²) / (1 − K(c,ρ)²))) / 2`
  (`KorenblumPaper.WangCertificateCore.lean:16`),
- `K(c, ρ) := 2ρ · (1 + c/ρ²) · ∏_{n=0}^{∞} F_n(c, ρ)`
  with the per-`n` factor
  `F_n(c, ρ) := ((1 + ρ²·c^(2n+1)) · (1 + c^(2n+3)/ρ²) · (1 + c^(2n+2))²)
              / ((1 + ρ²·c^(2n)) · (1 + c^(2n+2)/ρ²) · (1 + c^(2n+1))²)`
  (`KorenblumPaper.WangKernelExact.lean:33`).

Window admissibility: `branchSplit c < ρ₁ ≤ ρ₂ < 1`, where
`branchSplit c := c · sqrt(4/3)`.

The seed `c_value = 0.3554` gives `branchSplit c_value ≈ 0.4103`, so any
sub-interval `[ρ₁, ρ₂] ⊂ (0.4103, 1)` is an admissible window.

### Q3 — Does the kernel hold with margin at some `c > 0.3554`?

This is the question the **`Scratch/sprint_048_branch2_kernel.py`** script
this sprint ships answers, by sweeping `c` upward from `0.3554` and reporting
the gap

```
        gap(c, ρ₁, ρ₂)  :=  ∫_{ρ₁}^{ρ₂}  2ρ³ / Λ(c, ρ)  dρ  −  c⁴/2
```

at the **maximal-window** choice `[ρ₁, ρ₂] = [branchSplit c + ε, 1 − ε]`
for a small fixed `ε`. The script:

1. Evaluates `K(c, ρ)` via the truncated product `K_N(c, ρ) := 2ρ · (1 + c/ρ²) ·
   ∏_{n=0}^{N−1} F_n(c, ρ)` for `N = 50` (overkill — the per-`n` factor
   `F_n → 1` geometrically as `c^(2n)·...` shrinks);
2. Evaluates `Λ_N(c, ρ) := (1 + sqrt((1 + 3·K_N²) / (1 − K_N²))) / 2`;
3. Numerically integrates `2ρ³/Λ_N(c, ρ)` over `[ρ₁, ρ₂]` via SciPy's
   `quad` with high tolerance;
4. Reports the gap and the relative margin `gap / (c⁴/2)`;
5. Sweeps `c ∈ {0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.41, 0.42, 0.45,
   0.48, 0.50}` and prints a table.

The hypothesis the script tests: **the kernel holds with comfortable margin
at the seed `c = 0.3554` and remains positive for some `c > 0.3554`**. If the
script confirms this, the largest `c` with `gap ≥ ε_target` (e.g. `0.001`) is
the candidate target for sprint 049. If the script *falsifies* this — i.e.
the gap is already negative at `c = 0.3554` on the branch-2 window — then
sprint 017 is **not** a path to `c > 0.3554` and a different candidate
must be chosen (see Q6 fallback list). Either outcome is informative; both
are recorded in `Scratch/sprint_048_branch2_kernel.txt`.

**Important:** the seed equation 15 uses sprint 017's *integrated* form
extended over the full disk `[0, 1)` plus the branch-1 sub-window. Sprint
017's branch-2-only kernel is structurally tighter (smaller LHS, smaller
window — but the integrand `2ρ³/Λ` is largest near `ρ = 1` where the
branch-2 window lives). The Scratch script's numerical answer is the
single most important data point for this sprint.

### Q4 — What is the trust gap between the Scratch witness and a Lean proof?

Sprint 017's reducer is **already in `Reduction.lean`** and discharges
`ValidKorenblumBound c` from a witness existential

```
∃ ρ₁ ρ₂ : ℝ,
   branchSplit c < ρ₁ ∧ ρ₁ ≤ ρ₂ ∧ ρ₂ < 1 ∧
   IntervalIntegrable (fun ρ' => 2 * ρ' ^ 3 / Λ(c, ρ')) volume ρ₁ ρ₂ ∧
   ... (small list of summability and `Z` integrability cells) ∧
   c^4 / 2 ≤ ∫ ρ' in ρ₁..ρ₂, 2 * ρ' ^ 3 / Λ(c, ρ')
```

(see `Reduction.lean:2075` for the exact signature; the precise cell list
must be re-verified by the generator before sprint 049 begins).

The trust gap from a Scratch numerical witness `gap(c*, ρ₁*, ρ₂*) > 0` to a
Lean proof of `c^4/2 ≤ ∫_{ρ₁*..ρ₂*} 2ρ³/Λ(c*, ρ)` decomposes as:

| Cell | Form | Discharge route |
|---|---|---|
| **A** | `c^4 / 2` evaluated at `c = c*` rational | `norm_num` (closed-form rational at known `c*`) |
| **B** | Lower bound on `∫_{ρ₁*..ρ₂*} 2ρ³/Λ(c*, ρ)` for fixed rational `(c*, ρ₁*, ρ₂*)` | **Oracle** — verified numerical integration with rigorous error bound (interval-arithmetic, e.g. `mpmath.quad` + interval `mpf` mode, or `scipy` + `flint`/`arb`) |
| **C** | Upper bound on `Λ(c*, ρ)` to upper-bound the integrand from above (note: we want `≤` on LHS so we want a **lower** bound on the integrand, hence an **upper** bound on `Λ`) | Already partially available via `paperLambda_le_of_witness` (`KorenblumPaper.WangCertificateCore.lean:134`) which consumes a rational `kSqUpper` certificate. Sprint 049 must produce such a certificate at `(c*, ρ₁*, ρ₂*)` and verify it via `lambdaUpperWitnessQ` (`WangCertificateCore.lean:22`) — this part is closed-form rational and provable by `norm_num` once the witness rationals are computed in `Scratch/` |
| **D** | The product `∏_{n=0}^{∞} F_n(c*, ρ)` for `K(c*, ρ)` — needs a tail-truncation oracle to bound `K_∞(c, ρ) ≤ K_N(c, ρ) · (1 + δ_N)` for some computable `δ_N → 0` | **Oracle** — `Numerical_Library/wang_k_kernel.py` likely already exposes a truncation-error bound (file is in the repo). Verify and register an entry. Or, alternatively, prove a Lean-side `K_truncation_envelope` lemma that bounds the tail in closed form |

Cells A, C are **closed-form rational** and provable in Lean by
`norm_num`/`polyrith`/`field_simp` + `nlinarith`. Cells B, D are **oracle
candidates** for the route-A choice in Q5.

### Q5 — Per-cell decision: oracle vs prove

| Cell | Route | Rationale |
|---|---|---|
| **A** (`c^4/2` evaluated at rational `c*`) | **B (prove)** — `norm_num` at the known rational `c*` | Trivially closed-form |
| **B** (lower bound on the integral over `[ρ₁*, ρ₂*]`) | **A (oracle)** with `[[oracles]]` entry `branch2_kernel_integral_lower` | Numerical integration with verified interval-arithmetic error bounds is exactly the kind of thing that requires a `Numerical_Library` wrapper. Lean cannot evaluate `∫ 2ρ³/Λ(c, ρ) dρ` symbolically (transcendental integrand). The oracle returns a rational `lowerBound` such that `lowerBound ≤ ∫ ... dρ`, certified by the oracle wrapper's interval-arithmetic computation |
| **C** (`Λ(c*, ρ) ≤ Λmax(c*)` envelope) | **B (prove)** via `paperLambda_le_of_witness` + a rational `kSqUpper` certificate | The Lean-side machinery is already in place. Sprint 049 only needs to *compute* a rational `kSqUpper` for `(c*, ρ₁*, ρ₂*)` in `Scratch/`, then plug it into the existing certificate path |
| **D** (`K_∞ ≤ K_N · (1 + δ)` tail bound) | **A (oracle)** with `[[oracles]]` entry `paperK_truncation_envelope` if `Numerical_Library/wang_k_kernel.py` already exposes this; otherwise, **B (prove)** a closed-form geometric tail bound `∏_{n=N}^∞ F_n(c, ρ) ≤ exp(geometric_tail)` | Sprint 049's first step is to *audit* `Numerical_Library/wang_k_kernel.py` to determine which route applies. Both are tractable |

**Concrete oracle entries for `lemma.toml` (queue for sprint 049):**

```toml
# Sprint 048 roadmap proposes the following oracle entries for sprint 049+
# (NOT YET REGISTERED — sprint 048 is roadmap-only, no edits to lemma.toml).
# [[oracles]]
# name = "branch2_kernel_integral_lower"
# python_module = "ProofRefinement.Korenblum.Numerical_Library.wang_box_math"
# python_function = "branch2_kernel_integral_lower"  # to be implemented
# returns = "ℚ"  # rational lower bound on ∫_{ρ₁..ρ₂} 2ρ³/Λ(c, ρ) dρ
# lean_axiom = "ProofRefinement.Korenblum.Numerical_Oracles.branch2_kernel_integral_lower_axiom"
#
# [[oracles]]
# name = "paperK_truncation_envelope"
# python_module = "ProofRefinement.Korenblum.Numerical_Library.wang_k_kernel"
# python_function = "paperK_truncation_envelope"  # may already exist; audit needed
# returns = "ℚ × ℕ"  # (δ, N) such that K_∞(c, ρ) ≤ K_N(c, ρ) · (1 + δ)
# lean_axiom = "ProofRefinement.Korenblum.Numerical_Oracles.paperK_truncation_envelope_axiom"
```

These are **not** registered this sprint. Sprint 049 will register them after
the Scratch witness lands.

### Q6 — What does the c-pushing candidate look like?

**ACTUAL OUTCOME (post-Scratch sweep):** *Both* the branch-2 and the
full-window kernels falsify above `c = 0.3554`. The numerical sweep
(`Scratch/sprint_048_branch2_kernel.txt` and
`Scratch/sprint_048_full_window_kernel.txt`) shows:

* **Branch-2 kernel (sprint 017)** — gap at the seed `c = 0.3554` is
  `+1.72e-04` (positive but tiny: relative margin `≈ 2.2 %`). For every
  larger `c` in the sweep `{0.36, 0.37, …, 0.50}` the gap is **strictly
  negative** and *monotonically more negative as `c` increases* (relative
  margin drops from `−8.2 %` at `c = 0.36` to `−97.4 %` at `c = 0.50`).
  The integrand `2ρ³/Λ(c, ρ)` shrinks as `c` grows because `Λ` blows up
  (the spot-check `Λ(0.40, 0.95) ≈ 312`), while the LHS `c⁴/2` grows
  as `c⁴`. The branch-2 window also shrinks at its left endpoint
  (`branchSplit c = c·√(4/3)`). The combined effect is decisively
  negative.
* **Full-window kernel (sprint 014)** — gap is **already negative** at
  the seed `c = 0.3554` (gap ≈ `−7.75e-03`, relative margin `−48.6 %`)
  and falls further with increasing `c`. Sprint 014's reducer is
  *strictly weaker* than sprint 017's at this `c`: doubling the LHS
  (`c⁴` vs `c⁴/2`) costs more than enlarging the integration window from
  `[branchSplit c, 1)` to `[c, 1)` gains. The integrand near `ρ = c`
  is small (because `2ρ³ ≈ 2c³` is small and the integration interval
  added is only `branchSplit c − c = c·(√(4/3) − 1) ≈ 0.155·c`).

  > Note: the script's `FAIL <0` annotation on the seed cross-check is
  > expected here, *not* a script bug. The cross-check was templated from
  > the branch-2 script where the seed equation 15 directly implies a
  > non-negative gap. For sprint 014's stricter `c⁴` LHS, the seed
  > equation 15 does **not** imply this kernel — sprint 014 needs the
  > full disk-side `c⁴` paper bound which is itself only barely tight.

**Triggers the contract's "second fallback" branch:** the gap is
sign-determinate near the seed for *both* of the two oracle-cell-free
closed-form reducers in `Reduction.lean`. A *structural* improvement
(not a numerical refinement of existing reducers) is required to push
`c > 0.3554`. That improvement is filed as `Proposals/proposal_001_tighter_disk_side_bound_for_c_push.md`.

**Sprint 049 cannot be a numerical c-push.** Sprint 049's contract must
either:

1. (a) wait for human approval of `proposal_001`, then do the structural
   work the proposal names; or
2. (b) explore an alternate closing reducer not in the four-reducer table
   of Q1 (e.g. `valid_of_disk_tsum_partition_drop_N2_annulus_eq8_eq9_full_window`,
   sprint 045) — which the Q1 analysis flagged as *not numerically
   tractable in `Scratch/`* without an adversarial choice for the
   per-`k` `(a_k, b_k)` series. That route is *not* an oracle-able
   `Scratch/` numerical witness, so it is **outside the bulletin's
   "Scratch-first then Lean" directive** until proposal-001 (or an
   equivalent) provides the missing structural ingredient.

The proposed sprint-049 candidate file `Candidates/V49.lean` therefore
**does not exist as a concrete plan** until the proposal is reviewed.

**For completeness, the original (now-defeated) Q6 plan was:**

> 1. **`c_value : ℝ := <c*>/<denom>`** — the largest rational `c*` for which
>    `Scratch/sprint_048_branch2_kernel.py` reports `gap ≥ 0.001`.
> 2. **New seed axiom** replacing `hEq15_seed_3554` with the kernel
>    inequality at the chosen `(c*, ρ₁*, ρ₂*)`, discharged by the registered
>    oracle `branch2_kernel_integral_lower`.
> 3. **New sink discharge route**: `valid_of_disk_eq6_annulus_eq8_eq9_branch2_window`
>    (sprint 017) with the new oracle axiom + closed-form `Λ` envelope.
> 4. **Expected `axioms_used` set**: V0 minus `hEq15_seed_3554`, plus the
>    two registered oracle axioms.
> 5. **Expected score**: `c_value > 1777/5000`.
>
> **Fallback to sprint 014**: same shape with `c⁴` instead of `c⁴/2` and
> window `[c + ε, 1 − ε]`.

Both bullets above are blocked by the Scratch-witness outcome.

## Concrete edits expected

This sprint produces **no Lean edits**. The expected deliverables are:

- `ProofRefinement/Korenblum/Sprint_Contracts/sprint_048_roadmap_to_c_above_3554.md`:
  this contract (created by the planner — already in place when this contract
  is materialised).
- `ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.py`: Python
  script computing `gap(c, ρ₁, ρ₂)` for sprint 017's branch-2 kernel and
  sweeping `c ∈ {0.3554, ..., 0.50}`. Implementation requirements:
  - Pure-Python `K(c, ρ)` via truncated product `K_N` with `N = 50`;
  - Pure-Python `Λ(c, ρ)` via the closed-form `(1 + sqrt(...))/2`;
  - `scipy.integrate.quad` for the integral (or `mpmath.quad` for
    high-precision verification — script may include both for cross-check);
  - Window: `[ρ₁, ρ₂] = [branchSplit(c) + 1e-3, 1 − 1e-3]`;
  - Output a printed table with columns `c`, `branchSplit(c)`, `ρ₁`, `ρ₂`,
    `c⁴/2`, `∫ 2ρ³/Λ`, `gap`, `gap / (c⁴/2)` (relative margin);
  - Cross-check the seed `c = 0.3554` first; if the gap there is negative,
    abort with a clear message.
- `ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.txt`: captured
  stdout of the above script run, committed alongside the script. (Captured
  via `python3 sprint_048_branch2_kernel.py | tee sprint_048_branch2_kernel.txt`
  or equivalent.)
- `ProofRefinement/Korenblum/Scratch/sprint_048_full_window_kernel.py`:
  fallback script for sprint 014's `c⁴ ≤ ∫_{c+ε..1−ε} 2ρ³/Λ(c, ρ) dρ` kernel.
  Same structure as the branch-2 script but with `c⁴` LHS and full window.
- `ProofRefinement/Korenblum/Scratch/sprint_048_full_window_kernel.txt`:
  captured stdout of the fallback script.
- *Optionally* (only if both kernel scripts falsify the hypothesis at
  `c > 0.3554`): `ProofRefinement/Korenblum/Proposals/proposal_001_<slug>.md`
  naming the structural ingredient needed to unblock a c-push that neither
  sprint 014 nor sprint 017's kernel can deliver.

## Acceptance criteria

1. `ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.py` exists
   and is executable as `python3 sprint_048_branch2_kernel.py` with no
   uncaught exceptions.
2. `ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.txt` exists
   and contains the script's printed sweep table including at minimum the
   `c = 0.3554` baseline row plus rows for `c ∈ {0.36, 0.37, 0.38, 0.39,
   0.40, 0.42, 0.45, 0.50}`.
3. `ProofRefinement/Korenblum/Scratch/sprint_048_full_window_kernel.py`
   exists and is executable as `python3 sprint_048_full_window_kernel.py`
   with no uncaught exceptions.
4. `ProofRefinement/Korenblum/Scratch/sprint_048_full_window_kernel.txt`
   exists and contains the fallback script's printed sweep table over the
   same `c` range.
5. The roadmap document in this contract (the `## Roadmap to c > 0.3554`
   section above) is materialised as part of the sprint contract file.
   Greppable check: this contract file contains the heading
   `## Roadmap to c > 0.3554` and answers all six sub-questions Q1–Q6.
6. The roadmap explicitly identifies:
   - The chosen closing reducer (sprint 017 or, if Q3's script forces a
     fallback, sprint 014);
   - The exact kernel inequality with all coefficients;
   - The candidate `c*` value derived from the Scratch sweep;
   - Per-cell oracle vs proof decisions.
7. **No new Lean theorems are added.** Greppable check: the diff for
   sprint 048 contains zero changes to any `.lean` file under
   `ProofRefinement/Korenblum/`. The diff is restricted to:
   - `Sprint_Contracts/sprint_048_roadmap_to_c_above_3554.md` (this file),
   - `Scratch/sprint_048_branch2_kernel.py` (and `.txt`),
   - `Scratch/sprint_048_full_window_kernel.py` (and `.txt`),
   - *Optionally* `Proposals/proposal_001_<slug>.md` if both kernels
     falsify the hypothesis.
8. **No edits to `lemma.toml`.** Oracle entries are *proposed* in this
   contract's Q5 but **not** registered until sprint 049. Greppable
   check: the diff contains zero changes to
   `ProofRefinement/Korenblum/lemma.toml`.
9. **No new candidate `Candidates/V48.lean`** is created. The roadmap
   sprint produces no Lean candidate. Greppable check: the diff contains
   no `Candidates/V48.lean` (or any new `Candidates/V*.lean`) file.
10. The Scratch script's stdout contains a clearly-printed bottom-line
    answer of the form
    `BEST c with gap >= 0.001 (branch-2 window): c = <value>`
    (or `BEST c with gap >= 0.001 (branch-2 window): NONE — kernel
    falsifies above 0.3554` if Q3's hypothesis fails).
11. If Q3's branch-2 script falsifies the hypothesis, the fallback
    full-window script must report its own bottom-line `BEST c` line.
12. If both scripts falsify, a `Proposals/proposal_001_<slug>.md` exists
    naming the structural ingredient needed to unblock the push, with
    `Status: pending`. (If at least one script confirms a `c > 0.3554`,
    no proposal is required this sprint.)

## Out of scope

- Add any new Lean theorem, definition, or axiom.
- Edit `Reduction.lean`, `Main.lean`, `CandidateContract.lean`, or any
  other `.lean` file in the workspace.
- Edit `lemma.toml`.
- Create `Candidates/V48.lean` or any new candidate file.
- Implement the registered oracles `branch2_kernel_integral_lower` or
  `paperK_truncation_envelope` themselves — those are sprint 049's
  job. Sprint 048 only specifies their interface.
- Run the evaluator (`Evaluator.py`) — sprint 048 ships no candidate.
- Audit `Numerical_Library/wang_k_kernel.py` for the existence of an
  existing truncation-envelope function. That audit happens at the
  start of sprint 049 and informs the Q5 route-A vs route-B decision
  for cell D.
- Sweep `c < 0.3554` (uninteresting — even if the kernel holds at
  `c = 0.30`, that is a regression).
- Push the `c` sweep above `c = 0.50`. Wang's bound is theoretically
  approached by `c → 1`, but the disk-side `c⁴/2` LHS grows as `c⁴`
  while the annulus integrand `2ρ³/Λ` grows only as `ρ³` and the
  integration window `[branchSplit c, 1] = [c·√(4/3), 1]` shrinks; the
  branch-2 kernel becomes infeasible somewhere above `c ≈ 0.5`. The
  script's table will show where the gap turns negative; that
  determines the upper end of the candidate sweep, not a hard upper
  bound at `0.50`.
- File more than one proposal. The bulletin caps pending proposals at
  three; sprint 048 files at most one (and only if both kernel scripts
  falsify).

## Time budget

≤ 60 minutes runtime. Breakdown:
- ~15 min: implement `sprint_048_branch2_kernel.py` (pure Python +
  scipy, ~80 lines including the sweep loop and table formatting);
- ~5 min: run it, capture stdout to `.txt`;
- ~10 min: implement `sprint_048_full_window_kernel.py` (~70 lines, very
  similar to the branch-2 script with kernel coefficient swapped from
  `c⁴/2` to `c⁴` and window extended);
- ~5 min: run it, capture stdout to `.txt`;
- ~10 min: read the table outputs, identify the largest `c` with
  `gap ≥ 0.001`, and update Q6 of this contract with the concrete
  `c_value` rational (e.g. `3600/10000` or `3700/10000`);
- ~10 min: if both scripts falsify, draft the `Proposals/proposal_001`
  entry; otherwise verify the contract is internally consistent with
  the script's bottom-line answer.
- ~5 min: buffer for environment setup (uv/pip dependencies for
  scipy/mpmath if not already cached).

## Stop conditions

- Acceptance criteria met: `STATUS=READY_FOR_EVALUATION`
  (Note: there is no candidate to evaluate this sprint — the
  "READY_FOR_EVALUATION" marker is repurposed as "roadmap and Scratch
  artifacts in place; sprint 049 may proceed".)
- Blocked within scope: `STATUS=BLOCKED`
- Needs human trust expansion: `STATUS=BLOCKED_NEEDS_HUMAN`

### Implementation notes for the Generator

* **Avoid the temptation to also ship a Lean theorem.** The bulletin
  directive is explicit: sprint 048 is roadmap-only. If the Scratch
  numerics confirm the kernel at some `c > 0.3554`, *do not* preemptively
  start writing the sprint-049 Lean candidate or registering oracles.
  That is sprint 049's contract scope. Sprint 048 ends with the Scratch
  artifacts and an updated Q6 in this contract.

* **Scratch script skeleton (branch-2):**
  ```python
  # ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.py
  import math
  from scipy.integrate import quad

  def paperFactor(c, rho, n):
      num = ((1 + rho**2 * c**(2*n+1)) *
             (1 + c**(2*n+3) / rho**2) *
             (1 + c**(2*n+2))**2)
      den = ((1 + rho**2 * c**(2*n)) *
             (1 + c**(2*n+2) / rho**2) *
             (1 + c**(2*n+1))**2)
      return num / den

  def K_truncated(c, rho, N=50):
      prod = 1.0
      for n in range(N):
          prod *= paperFactor(c, rho, n)
      return 2 * rho * (1 + c / rho**2) * prod

  def Lambda(c, rho, N=50):
      Ksq = K_truncated(c, rho, N) ** 2
      # Defensive: clamp Ksq to (0, 1) to avoid sqrt of negative.
      if Ksq >= 1.0:
          return float('inf')
      return (1 + math.sqrt((1 + 3 * Ksq) / (1 - Ksq))) / 2

  def integrand(rho, c):
      L = Lambda(c, rho)
      return 2 * rho**3 / L

  def branchSplit(c):
      return c * math.sqrt(4.0 / 3.0)

  def evaluate(c, eps=1e-3):
      rho1 = branchSplit(c) + eps
      rho2 = 1.0 - eps
      lhs = c**4 / 2
      rhs, _err = quad(integrand, rho1, rho2, args=(c,), limit=200)
      gap = rhs - lhs
      rel = gap / lhs if lhs > 0 else float('inf')
      return rho1, rho2, lhs, rhs, gap, rel

  if __name__ == "__main__":
      cs = [0.3554, 0.36, 0.37, 0.38, 0.39, 0.40, 0.42, 0.45, 0.48, 0.50]
      print(f"{'c':>8} {'split':>10} {'rho1':>10} {'rho2':>10} "
            f"{'c^4/2':>14} {'integral':>14} {'gap':>14} {'rel':>10}")
      best_c = None
      for c in cs:
          rho1, rho2, lhs, rhs, gap, rel = evaluate(c)
          print(f"{c:>8.4f} {branchSplit(c):>10.4f} {rho1:>10.4f} {rho2:>10.4f} "
                f"{lhs:>14.6e} {rhs:>14.6e} {gap:>14.6e} {rel:>10.4f}")
          if c > 0.3554 and gap >= 0.001:
              best_c = c
      if best_c is not None:
          print(f"\nBEST c with gap >= 0.001 (branch-2 window): c = {best_c}")
      else:
          print("\nBEST c with gap >= 0.001 (branch-2 window): "
                "NONE -- kernel falsifies above 0.3554")
  ```

* **Cross-checks the script must include:**
  - The seed `c = 0.3554` row's `gap` should be **non-negative** (since
    the seed equation 15 holds at this `c`, and sprint 017's branch-2
    kernel is *strictly weaker* than the full equation 15 — sprint 017
    drops the branch-1 contribution). If the seed row's gap is negative,
    the script has a bug.
  - The `Lambda(c, rho)` value should always satisfy `Lambda >= 0.5`
    (this is `paperLambda_ge_half` from `WangPaperSideConditions.lean:30`).
    Print a warning if any computed `Lambda < 0.5`.
  - `K(c, rho)^2` should always satisfy `0 < K^2 < 1` (otherwise the
    `sqrt` in `Lambda` is undefined or zero). Print a warning if any
    computed `K^2` falls outside `(0, 1)`.

* **Why `N = 50` for the product truncation:** the per-`n` factor
  `F_n(c, ρ)` is `1 + O(c^(2n))` for `c < 1`, so the tail product
  `∏_{n=N}^∞ F_n` is `1 + O(c^(2N))`. At `c = 0.50`, `c^100 ≈ 7.9e-31`,
  far below double-precision relative epsilon. At the seed `c = 0.3554`,
  `c^100 ≈ 1.0e-44`. `N = 50` is comfortable overkill for the Scratch
  numerical witness.

* **Fallback script differences:** identical structure but
  - LHS becomes `c**4` instead of `c**4 / 2`,
  - `rho1 = c + eps` (not `branchSplit(c) + eps`),
  - bottom-line message says `(full window)` instead of `(branch-2 window)`.

* **No `mpmath` requirement, but recommended cross-check:** if `mpmath`
  is available in the environment, add an optional second pass at higher
  precision (e.g. `mpmath.mp.dps = 50`) to verify the `quad` result is
  not a numerical artifact. Not required for acceptance.

* **Running the scripts:** the harness shell environment may need
  `pip install scipy` and (optionally) `pip install mpmath`. Use
  `env UV_CACHE_DIR=korenblum/.uv-cache uv run python3
  ProofRefinement/Korenblum/Scratch/sprint_048_branch2_kernel.py`
  to leverage the existing uv cache (matches the evaluator wrapper
  invocation pattern in the AGENT_BRIEF).

* **Updating Q6 with the concrete `c*`:** after running both scripts,
  *edit this contract's Q6* to replace the placeholder `c_value =
  3600/10000` with the actual largest `c` from the table that has
  `gap ≥ 0.001`. The Q6 update is part of the sprint deliverable.
