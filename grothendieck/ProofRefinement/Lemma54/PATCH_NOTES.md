# PATCH NOTES — Lemma 5.4 refinement framework (2026-05-03)

**Status:** binding for all future sprints. Planner / Generator / Evaluator
must read this file before reasoning about V9–V26 oracle values, and
treat the rules in [§4](#4-rules-binding-on-future-sprints) as gates,
not suggestions.

---

## 1. The bug (what went wrong)

**Every numerical oracle that backed V9–V26's `Cr_val` is non-rigorous
because of a silent truncation step in `eval_H_eta_at_acb`.**

Concretely: every oracle in
[`Numerical_Library/`](Numerical_Library/) — `m_phi`, `m_phi_prime`,
`m_pp`, `inv_F_p_z`, `u_zz`, `joint_phi_phip_invD2`, `uzz_phi_sq`,
`merged_uderiv` — calls

```python
from grothendieck.proof.certified.compute_cr_v2 import eval_H_eta_at_acb
```

`eval_H_eta_at_acb` evaluates `H_η(w) = arcsin(w) − φ(arcsin(w))/√(1−w²)`
where `φ` is **truncated at `K_max` terms with no rigorous tail bound**.
Its own docstring admits it:

> "Phi truncation error is heuristic (not rigorously bounded)."

Default `K_max = 80` (V26 used this). The b-series file
[`outputs/b_series_eta0p01_K250_dps100.json`](../../outputs/b_series_eta0p01_K250_dps100.json)
has 250 coefficients; inspection at K=249 shows `|b_k|^{1/k} ≈ 0.964`,
i.e. slow geometric decay. The "10⁻⁸ tail" claim assumes a decay rate
the proof has never verified — so the heuristic tail can be larger
than the certified bound itself for tight V25/V26 numbers
(`merged_uderiv_val = 37/5000000 ≈ 7.4·10⁻⁶`).

Because `_max_on_rect` uses interval arithmetic, the *truncated*
polynomial is bounded rigorously, but the **truncation tail is the
unbounded heuristic step** — interval arithmetic over a wrong
function gives a rigorous bound on the wrong thing.

This invalidates `Cr_val` for **every candidate from V9 onward** in the
sense of "arb-certified end-to-end". The Lean proofs are still
type-correct; the numerical assumptions they rest on are not certified.

(See [`Scratch/SESSION_SUMMARY.md`](Scratch/SESSION_SUMMARY.md) §"The
actual rigor gap" for the original write-up of this discovery.)

---

## 2. The patches (what we did about it)

### 2a. Truncation-free `H_η`, `H_η'`, `H_η''` evaluators

Built in [`Scratch/`](Scratch/), entirely independent of `eval_H_eta_at_acb`:

| Quantity | File | Method |
|---|---|---|
| `H_η(w)` at sharp `acb w` | [`h_eta_parallel_path.py`](Scratch/h_eta_parallel_path.py) | path-integration of `K_z` via `acb.integral` with adaptive Bernstein-ellipse error per panel |
| `H_η'(w)` at sharp `acb w` | [`h_prime_complex_certified.py`](Scratch/h_prime_complex_certified.py) | Price's-formula GL with closed-form Gaussian-tail bound on outer integrand (no `φ`-series anywhere) |
| `H_η''(w)` at sharp `acb w` | [`h_pp_complex_certified.py`](Scratch/h_pp_complex_certified.py) | Price 2nd-derivative formula + closed-form tail bound |
| `sup_Z \|Φ'(z)\|` over chunk `Z` | [`phi_prime_chunk_bound_certified.py`](Scratch/phi_prime_chunk_bound_certified.py) and [`phi_prime_chunk_bound_direct.py`](Scratch/phi_prime_chunk_bound_direct.py) | η²-tight chunk bound via real-positive majorant |
| `sup_Z \|Φ''(z)\|` over chunk `Z` | [`phi_pp_chunk_bound_eta_tight.py`](Scratch/phi_pp_chunk_bound_eta_tight.py) | η²-tight, post-anisotropic-Gaussian, post-`λ`-decay-fix |
| `sup_Z \|H_η''(z)\|` over chunk `Z` | [`h_eta_pp_chunk_bound_certified.py`](Scratch/h_eta_pp_chunk_bound_certified.py) | real-positive majorant chunk bound |

These are the **canonical truncation-free oracles for the V26
framework**. Everything below feeds off them.

### 2b. Production chunk certifier (with resume + parallelism)

[`Scratch/parallel_chunk_certifier.py`](Scratch/parallel_chunk_certifier.py)
wraps the above into an MP run that

- partitions ∂Ω into `n_per_edge × 4` chunks;
- exploits **V26 4-fold symmetry** (`H_η(z̄) = ̄H_η(z)`, `H_η(−z) = −H_η(z)`)
  so only Q1 chunks are computed primarily;
- saves incrementally every ~85 work units (resumable across crashes /
  cancellations);
- runs at 96 workers (cap; box has 128 cores but SSH chokes above 96).

### 2c. Joint per-`(p, w)`-cell merged oracle (post-LLM patches)

[`Scratch/joint_merged_uderiv.py`](Scratch/joint_merged_uderiv.py)
computes
`Cr = (1/2) · sup_{(p, w) ∈ [0, p_max]×∂Ω} |2·Φ·Φ'·D − DD·Φ²| / |D|³`
with the following rigor patches stacked in:

- **Denominator-fix**: `|D(p, w)| ≥ inf_w|H_0'| − p_hi · M_phi_p`
  (uses the chunk's certified `inf|H_0'|` and `M_phi_p`, no joint
  `D` interval blow-up).
- **2nd-order Taylor pad in `w`** for `Φ`, `Φ'`, `Φ''` using sharp
  midpoint values + Cauchy-derived `M_phi_ppp` for the remainder.
  Pad sizes: `Φ` ← `r³/6 · M_phi_ppp`, `Φ'` ← `r²/2 · M_phi_ppp`,
  `Φ''` ← `min(r · M_phi_ppp, M_phi_pp)`.
- **`min(interval, norm)` per cell**: keep the tighter of the
  interval-arithmetic numerator (recovers sign cancellation) and the
  triangle-norm form (no dependency blow-up).
- **`λ`-decay factor-of-2 fix** in `phi_pp_chunk_bound_eta_tight.py`:
  was `2·min(α,β)`, now `min(α,β)` per the parallelogram identity
  `(x−y)² + (x+y)² = 2(x²+y²)`. Earlier value was non-rigorous.
- **Anisotropic Gaussian moments** in `_integrate_poly_aniso` (same
  file): replace isotropic majorant with `min(aniso, iso)` per piece.

### 2d. Corner subdivision

[`Scratch/corner_subdivision_certifier.py`](Scratch/corner_subdivision_certifier.py)
splits corner / near-corner chunks 4-way (or 2-way for 1D edge
chunks) and recomputes oracles on sub-chunks, again exploiting V26
4-fold symmetry. Three rounds drove `Cr` from 34.47 → 0.383 over the
full 64 chunks.

### 2e. Cached, certified outputs

These are the **canonical post-patch numbers**. Future sprints should
read these JSONs rather than re-running the 158-min production:

| Cache | Cr | Contents |
|---|---|---|
| [`Cache/Backups/2026-05-03_production/`](Cache/Backups/2026-05-03_production/) | **34.47** (full 64 chunks, no subdivision) | Assembled chunks JSON + 4224-work-unit raw cache + joint-oracle Cr JSON + run log |
| [`Cache/Backups/2026-05-03_subdivision/`](Cache/Backups/2026-05-03_subdivision/) | round1 = 2.27, round2 = 1.23, **round3 = 0.383** | Three subdivision rounds branching from production |

Each backup directory has a `README.md` and `MANIFEST.sha256`.

### 2f. Naive-audit (per-candidate Cr re-evaluation)

[`Scratch/_naive_audit.py`](Scratch/_naive_audit.py) re-runs **each
candidate's exact `Cr_phi_*` formula** from
[`Proof/Lib/Lemma54_Paper.lean`](Proof/Lib/Lemma54_Paper.lean) using
the post-patch oracles — both per-chunk scalars (`M_phi`,
`M_phi_prime`, `M_pp`, `inv_F_p_z`, `u_zz_bound`) and per-cell joint
sups (`joint_phi_phip_invD2`, `uzz_phi_sq`, `merged_uderiv` — all with
the same Taylor-pad machinery as 2c).

Audit results are saved to:

- [`Cache/Backups/2026-05-03_subdivision/audit_naive_results.json`](Cache/Backups/2026-05-03_subdivision/audit_naive_results.json)
- [`Cache/Backups/2026-05-03_production/audit_naive_results.json`](Cache/Backups/2026-05-03_production/audit_naive_results.json)

### 2g. Numerical_Library/truncfree — the public API

The above machinery is exposed through a clean Python façade at
[`Numerical_Library/truncfree/`](Numerical_Library/truncfree/) so
sprints don't have to wire `sys.path` into `Scratch/` themselves:

```python
from Numerical_Library.truncfree import (
    round3, production, compute_bundle,           # bundle factories
    from_audit_json,                               # raw cache loader
    audit_candidate, audit_all_candidates,         # Cr_phi_* per candidate
    compute_M_phi_truncfree_bound,                 # OracleResult wrappers
    compute_M_phi_prime_truncfree_bound,
    compute_M_pp_truncfree_bound,
    compute_inv_F_p_z_truncfree_bound,
    compute_u_zz_bound_truncfree_bound,
    compute_joint_phi_phip_invD2_truncfree_bound,
    compute_uzz_phi_sq_truncfree_bound,
    compute_merged_uderiv_truncfree_bound,
)

b = round3()                          # millis: load cached audit JSON
print(b.summary())                    # eight oracles + inf|D|
res = b.as_oracle_result("M_phi")    # → OracleResult (Fraction + meta)

a = audit_candidate("V11", bundle=b)  # apply Cr_phi_uzz formula
# → CandidateAudit(V11, Cr_phi_uzz, Cr_decl=1, Cr_patched=3.255e-01, ratio=3.26e-01)
```

`compute_bundle(chunks_path, ...)` rebuilds from a fresh chunks JSON
and writes / re-reads `<chunks>__truncfree_audit.json` for cache
reuse. See
[`Numerical_Library/README.md`](Numerical_Library/README.md) for
the full API and recipe for adding new truncation-free oracles.

These `compute_*_truncfree_bound` functions do **not** import
`eval_H_eta_at_acb` and are the canonical R2-compliant entry points.
The deprecated `compute_*_bound` functions (top-level
`Numerical_Library/m_phi.py` etc.) carry a deprecation banner and
remain only for V0..V26 backwards-compat.

---

## 3. The audited values (Cr_patched per candidate)

`Cr_patched` is the *actual* value of each candidate's
`Cr_phi_*` formula evaluated with the truncation-free post-patch
oracles. **It is not a pass/fail; it is the patched score.** The
candidate's declared `Cr_val` is whatever rational the Lean file
encodes — the audit number replaces the K_max-truncated assumption,
nothing more.

Constants: `r = 23/25`, `R = 23/20` (`R_val_paper r ≤ 23/20`),
`p_max = 1`.

| V | Formula | `Cr_decl` | `Cr_patched` (production) | `Cr_patched` (round-3 subdiv) |
|---|---|---|---|---|
| 9  | `Cr_phi`                    | `5`        | 18.86   | 7.252    |
| 10 | `Cr_phi_invD`               | `2`        | 2.119   | 0.4852   |
| 11 | `Cr_phi_uzz`                | `1`        | 4.223   | 0.3255   |
| 12 | `Cr_phi_uzz_direct`         | `1/32`     | 4.223   | 0.3255   |
| 13 | `Cr_phi_uzz_direct`         | `1/300`    | 4.223   | 0.3255   |
| 14 | `Cr_phi_uzz_direct_joint`   | `1/1300`   | 5.203   | 0.2810   |
| 15 | `Cr_phi_uzz_direct_joint2`  | `1/2600`   | 26.93   | 0.4105   |
| 16 | `Cr_phi_uzz_direct_joint2`  | `1/3500`   | 26.93   | 0.4105   |
| 17 | `Cr_phi_uzz_direct_joint2`  | `1/3500`   | 26.93   | 0.4105   |
| 18 | `Cr_phi_uzz_direct_joint2`  | `1/11700`  | 26.93   | 0.4105   |
| 19 | `Cr_phi_uzz_direct_joint2`  | `1/31500`  | 26.93   | 0.4105   |
| 20 | `Cr_phi_uzz_direct_joint2`  | `1/66500`  | 26.93   | 0.4105   |
| 21 | `Cr_phi_uzz_direct_joint2`  | `1/71900`  | 26.93   | 0.4105   |
| 22 | `Cr_phi_uzz_direct_joint2`  | `1/124000` | 26.93   | 0.4105   |
| 23 | `Cr_phi_uzz_direct_joint2`  | `1/169000` | 26.93   | 0.4105   |
| 24 | `Cr_phi_uzz_direct_joint2`  | `1/169000` | 26.93   | 0.4105   |
| 25 | `Cr_phi_uzz_merged`         | `1/240000` | 26.93   | 0.3734   |
| 26 | `Cr_phi_uzz_merged`         | `1/268000` | 26.93   | 0.3734   |

Sanity checks (must hold; consistency proxy on the audit code):
`2·joint_phi_phip_invD2 + uzz_phi_sq ≥ merged_uderiv` everywhere;
`V25/V26 ≤ V24` everywhere (else there's a bug in the joint
evaluator). Both hold in both rows.

### 3a. Reading the table — V11..V26 are NOT obsolete

A subtle point that bit sprint_033 and is likely to bite future
sprints: **the column that matters for "what does the proof
actually certify" is `Cr_patched`, not `Cr_decl`.** The literal
`Cr_decl` is whatever rational the candidate writes in
`def Cr_val : ℝ := …`; it must be ≥ `Cr_patched` for the proof to
go through, and the smaller it is the better, but it is *not* the
quantity the math is trying to drive down. `Cr_patched` is.

Two consequences for planning:

**(a) Each V_K's row encodes a *formula × oracle constellation*,
not a "version number".** V11..V26 each chose a different
`Cr_phi_*` formula (different decomposition of `‖∂²_p F⁻¹‖` into
sup-norms / joint sups). These formula choices are NOT obsoleted
by V27. They live or die by whether their `Cr_patched` is small,
which in turn depends on whether the chosen decomposition
benefits from the underlying oracle structure. From the round-3
column:

- **V14's `Cr_phi_uzz_direct_joint`** has the smallest
  `Cr_patched = 0.2810` of any candidate — *smaller than V11's
  0.3255 and smaller than V25/V26's merged 0.3734*. The V14
  formula is structurally the tightest at round-3 chunks. A
  future sprint that re-baselines onto V14's formula could
  declare `Cr_val ≈ 1/3.5 ≈ 0.286` instead of V27's `1/3 = 0.333`
  — a real ~17% win without any new analytic input, just by
  switching formula. The Planner should consider this before
  doing more subdivision work.
- **V15..V24's `Cr_phi_uzz_direct_joint2`** evaluates to
  `0.4105` — looser than V11/V14/V25/V26 because it triangle-
  decomposes into joint + uzz_phi_sq without recovering the
  destructive cancellation in `2·Φ·Φ'·D − DD·Φ²`. These
  candidates' formulas are *worse* than V11's at round-3 chunks.
  But that's data: it tells the Planner "don't bother re-
  baselining onto joint2 unless the audit floor changes shape".
- **V25/V26's `Cr_phi_uzz_merged`** captures the merged numerator
  (with sign cancellation between joint and uzz pieces).
  `Cr_patched = 0.3734` is in between V11 and V14. The merged
  formulation only beats V14 when the per-cell cancellation is
  large enough to overcome the interval-arithmetic widening
  inherent in `min(interval, norm)` — at round-3 chunks the
  cancellation is ~9% (see §3 sanity), not enough.

**(b) Beating V27's `Cr_val = 1/3` requires *moving the audit
floor*, not literal-tightening.** V27 sits at the audit-floor
literal for the V11 formula. A "V28: Cr_val = 1/3.2" sprint
under V11's formula is invalid — the patched value is `0.3255`
and `1/3.2 = 0.3125 < 0.3255`, so G7.b will fail it. The Planner
must propose **structural** sprints to lower the audit floor
itself. Permitted directions (in order of historical effectiveness):

  1. **Re-baseline onto V14's formula** for an immediate ~17% win
     (literal `1/3.5` against `Cr_patched = 0.2810`). One-shot;
     does not require new oracles.
  2. **Subdivide further** (round 4: split V14's worst cells, or
     split next-tier corners). Each round historically halved
     `merged_uderiv`. The V11/V14 formula values
     (`M_phi_prime · M_phi · inv_F_p_z²` / `joint_phi_phip_invD2`)
     also tighten because chunk_radius shrinks.
  3. **Sharper joint-oracle evaluator** (e.g., 4th-order Taylor
     pad in `w` instead of 2nd-order, or a tighter `M_phi_ppp`
     bound). Reduces per-cell norm-form slack at corner chunks
     where `score_norm` currently wins over `score_interval`.
  4. **Anisotropic Φ'' bound** has already been applied (§2c);
     check `phi_pp_chunk_bound_eta_tight.py` for further η²-tight
     improvements.
  5. **Alternative contour** (octagonal, Cassini, …) that avoids
     the corner saturation entirely. Pinned by the user as a
     stretch direction.
  6. **Different decomposition** of the merged numerator — e.g.,
     a 3-way split that exposes more cancellation than the
     2-way merged. Open research question.

The fact that V12, V13, V15..V26 carry K_max-era literals
(`1/32`, `1/300`, …, `1/268000`) that are *all* far below their
`Cr_patched` does not mean those candidates are abandoned — it
means the K_max truncation hid `10×–10⁷×` of error in those rows
(see §1). Their *formula choices* may still be worth revisiting
once the audit floor drops by enough to accommodate them. For
example, if a future round-5 subdivision drives `merged_uderiv`
below `2/268000 = 7.46·10⁻⁶`, V26's literal `1/268000` becomes
reachable again.

**Summary for the Planner:** the candidate axis after the patch
is `(formula, oracle constellation, audit floor)`, not
`(literal Cr_val)`. V27 is the literal-tightened V11 baseline.
V28+ should pick a direction from the list above, not stop at
"V27 is optimal".

The headline number: with the truncation-free oracles + 3 rounds of
corner subdivision, **`Cr_patched(V26) = 0.3734`** — six orders of
magnitude looser than the `1/268000` literal. With production-only
chunks, `Cr_patched(V26) = 26.93`. The `K_max = 80` heuristic was
hiding a multiplicative factor of `10⁵–10⁷` of real bound error.

---

## 4. Rules (binding on future sprints)

These are **gates, not suggestions**. Violating any one of them
means the sprint's contract is invalid and the Evaluator must fail
the candidate.

### Rule R1 — No K_max truncation. Anywhere. Ever.

The Generator must **never** introduce, edit, or otherwise depend on
`eval_H_eta_at_acb`, `eval_phi_at_acb`, `eval_H_eta_deriv_at_acb`, or
any other helper in
[`grothendieck/proof/certified/compute_cr_v2.py`](../../grothendieck/proof/certified/compute_cr_v2.py)
that takes `K_max` as a parameter and produces an `acb` H_η output
without an explicitly-attached, rigorously-bounded tail term.

A new oracle that imports `eval_H_eta_at_acb` is **invalid by
construction**. Same for any other `phi_series`-Horner code path that
truncates without a tail bound.

The Evaluator's **G7 (rigor gate)** below enforces this mechanically.

### Rule R2 — Use the canonical truncation-free oracle suite.

Any sprint touching `H_η`, `H_η'`, `H_η''`, `Φ`, `Φ'`, `Φ''`, `D`,
`DD`, or any quotient thereof must use the [§2a](#2a-truncation-free-h_η-h_η-h_η-evaluators)
evaluators (path-integration / Price-formula) for sharp midpoint
values and the [§2a](#2a-truncation-free-h_η-h_η-h_η-evaluators)
chunk bounds for chunk suprema. The joint per-cell oracle is
[`Scratch/joint_merged_uderiv.py`](Scratch/joint_merged_uderiv.py)
(with all five patches in §2c).

### Rule R3 — Use the cached production / subdivision outputs.

Re-running the chunk certifier from cold takes 158 min on 96
workers. Don't. The two cached backups in `Cache/Backups/2026-05-03_*`
are the canonical inputs. New subdivision rounds branch from
`round3_v26_corner_split_v3.json`; new joint-oracle re-runs read
that JSON and emit a new `joint_merged_*.json` next to it.

If a sprint requires a different cache, the Generator must compute
it and append it under
`Cache/Backups/<date>_<purpose>/` with a `README.md` + `MANIFEST.sha256`,
following the pattern of the existing two. The contract must name
this directory in `Concrete edits expected:`.

### Rule R4 — Existing top-level `Numerical_Library/` oracles are deprecated.

[`Numerical_Library/m_phi.py`](Numerical_Library/m_phi.py),
[`m_phi_prime.py`](Numerical_Library/m_phi_prime.py),
[`m_pp.py`](Numerical_Library/m_pp.py),
[`inv_F_p_z.py`](Numerical_Library/inv_F_p_z.py),
[`u_zz.py`](Numerical_Library/u_zz.py),
[`joint_phi_phip_invD2.py`](Numerical_Library/joint_phi_phip_invD2.py),
[`uzz_phi_sq.py`](Numerical_Library/uzz_phi_sq.py),
[`merged_uderiv.py`](Numerical_Library/merged_uderiv.py)
all carry a `# DEPRECATED — see PATCH_NOTES.md` header. They are
kept *only* to satisfy V0.lean / V12-V26.lean's existing imports
during the audit transition. New candidates should not depend on
them.

**The replacement is** the
[`Numerical_Library/truncfree/`](Numerical_Library/truncfree/)
subpackage; see [§2g](#2g-numerical_librarytruncfree--the-public-api).
For a sprint that needs one of the existing eight quantities,
import the matching `compute_*_truncfree_bound(source="round3")`
function — it returns the same `OracleResult` shape as the
deprecated API.

For a sprint that needs a sup-norm bound on a *new* analytic
quantity, follow the recipe in
[`Numerical_Library/README.md`](Numerical_Library/README.md)
"Adding a NEW truncation-free oracle": add a per-chunk evaluator
under `Scratch/`, extend `TruncFreeBundle`, register a wrapper via
`_make_compute_fn(...)`, update `__init__.py`. The Generator must
**not** import `eval_H_eta_at_acb`, `eval_phi_at_acb`,
`eval_H_eta_deriv_at_acb`, or `eval_phi_and_deriv_at_acb` — G7.a
fails any candidate whose oracle path reaches those symbols.

### Rule R5 — `Cr_val` claims must be reproducible from the audit.

Any new candidate must include, in its file header, a comment of
the form:

```lean
/-
  AUDIT: Cr_phi_*(<oracles>) ≤ Cr_val under PATCH_NOTES rules.
  Source chunks: <Cache/Backups/.../*.json>
  Source audit:  <Cache/Backups/.../audit_naive_results.json>
  Cr_patched(this candidate) = <value> (vs Cr_val = <decl>)
-/
```

The Evaluator's **G7** below greps for this block. If the audit
JSON's `Cr_patched_float` for the candidate exceeds the
`Cr_val_float` it declares in the candidate file, **G7 fails**.
The K_max-era trick of "declare a small `Cr_val` and let the
truncated oracle satisfy it" is gone.

---

## 5. Where this file lives in the harness

The Planner reads `AGENT_BRIEF.md` and `Bulletin.md` first; both now
link here. The Generator reads `AGENT_BRIEF.md` and the contract;
the contract template will reference `PATCH_NOTES.md` as a binding
input. The Evaluator's G7 (added in
[`.claude/agents/refinement-evaluator.md`](../../.claude/agents/refinement-evaluator.md))
encodes R1 and R5 as `grep`-able gates.

If you (a future agent) believe one of R1–R5 should be relaxed:
**file a `Proposals/proposal_<NNN>_*.md`** explaining the math and
proposing a replacement gate. **Do not silently relax it in a
Sprint Contract.** The K_max gap is the exact sort of regression
this framework is meant to prevent in future, and the patch only
holds if the rules are treated as binding.
