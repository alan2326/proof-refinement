# Plan: Fully Lean-ify the paper's Lemma 5.4 proof

## Context for the agent picking this up

You are continuing a project that already has a complete, ~15,000-line Lean
formalization of the Grothendieck inequality in `LeanProof/`. That includes a
finished proof of Lemma 5.4 in `LeanProof/Lemma54.lean` (MVT-on-segment style,
~1067 lines, zero `sorry`s) plus all of Lemmas 5.3, 4.2, 4.3, 4.4 fully proved.
Every infrastructure lemma you might want — analyticity of `F_p`, F_inv
existence on a disk, closed-form bounds on `H_η`, Cauchy bounds, etc. — is
already there for you to import.

This task is straightforward: write a *second* proof of Lemma 5.4 that follows
the paper's strategy (Cauchy on a larger disk + identity (75) + Taylor in `p`)
instead of the MVT-on-segment route, and expose an explicit closed-form `Cr`
constant. You do not edit `LeanProof/`. You import from it.

Realistic scope: **~1 hour of focused work**, ~1000 lines new Lean. The
heavy lifting (analyticity, `lemma_5_3`, `bound_43_paper`, Cauchy
machinery) is already done.

**Read the paper proof first**: `assets/pdf/braverman.pdf`, §5, pages 21–24
(Lemma 5.3, Lemma 5.4, equations (75)–(76)). The paper proof is short and
tells you exactly what to formalize.

---

## Goal

Produce a Lean theorem `lemma_5_4_paper` whose `#print axioms` output
contains **only**:

1. Lean primitives (`propext`, `Classical.choice`, `Quot.sound`).
2. Numerical axioms of the form `M_val ≥ <fixed rational>`, where each `M_val`
   is registered in `ProofRefinement/Lemma54/lemma.toml` and backed by a
   `Numerical_Library/` oracle.

No structural axioms. Cauchy bounds, identity (75), Taylor remainder, and
`F_p` invertibility are all theorems.

The next refinement run's `V0.lean` then calls `lemma_5_4_paper` and is
the verified baseline (no `paper_taylor_argument*` axioms).

---

## Reusable assets (import-only)

### `LeanProof/Lemma53.lean`
- `lemma_5_3` — `F_inv` analytic on `disk r`, `F_p η p (F_inv z) = z`.
- `lemma_5_3_with_W_inv` — same plus `W_inv : ℂ → ℂ` analytic on `disk r`,
  `W_inv z ∈ closedBall 0 ((1+r)/2)`, `F_inv = sin ∘ W_inv`.
- `F_p_deriv` — `deriv (F_p η p) z = (1-p)·H_0' z + p·H_η' z`.
- `H0_deriv_ne_zero` — `deriv H_0 z ≠ 0` on `S`.
- `F_p_deriv_ne_zero_small_p` — for compact `K ⊆ S`, `(F_p η p)'` is nonzero
  on `K` for `p` small enough.

### `LeanProof/Lemma42.lean`
- `bound_43_paper a b : ℝ` — closed-form bound on `‖H_η z‖` for `z = a + bi ∈ S`.
- `H_eta_bound_paper` — `‖H_η z‖ ≤ bound_43_paper z.re z.im`.
- `H_eta_bounded_on_compact` — `∃ M, ∀ z ∈ K, ‖H_η η z‖ ≤ M`.

### `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Cauchy.lean`
- `cauchy_taylor_coeff_bound` — Cauchy's estimate, fully proved.
- `cauchy_taylor_coeff_bound_closedBall` — variant on closedBall.
- `norm_cos_le_cosh_of_mem_closedBall` — `‖cos z‖ ≤ cosh r` on `closedBall 0 r`.
- `M_H_bound η R := bound_43_paper (sinh R) (cosh R)` — closed-form M for `H_η`.

### Mathlib
- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
- `taylor_mean_remainder`, `taylor_mean_remainder_lagrange` (real-valued, in
  `Mathlib/Analysis/Calculus/Taylor.lean`).
- `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (works for `ℂ`-valued).
- `HasDerivAt.fun_inverse` / `HasFDerivAt.localInverse` for implicit
  differentiation.
- `AnalyticOnNhd.deriv`, `.iteratedDeriv`, `.comp`, `.smul`.
- `IsCompact.exists_bound_of_continuousOn`.

---

## Numerical axioms (the only axioms allowed)

Closed-form bounds we **prove** in Lean — no axiom:

| Quantity | Bound | Derivation |
|---|---|---|
| `‖F_inv z‖` for `z ∈ disk r₁` | `≤ sinh r₂` | `F_inv = sin ∘ W_inv`, `‖W_inv z‖ ≤ r₂`, `‖sin w‖ ≤ sinh ‖w‖` |
| `‖cos z‖` on `closedBall 0 r₁` | `≤ cosh r₁` | `norm_cos_le_cosh_of_mem_closedBall` |
| `‖H_η z‖` for `z ∈ sin(closedBall 0 r₂)` | `≤ M_H_bound η r₂` | `H_eta_bound_paper` |
| `‖H_0 z‖` for `z ∈ sin(closedBall 0 r₂)` | closed-form on `S` | direct |
| `‖H_0' z‖` on F_inv-image | `≤ 1/cos r₂` | `H_0 = arcsin`, `arcsin' = 1/cos`, principal branch |

Numerical axioms we **keep** (verifier checks each against the certified-arb pipeline):

| Axiom | Quantity bounded |
|---|---|
| `h_M_Hetap_num` | `sup ‖H_η' w‖` over `w ∈ sin(closedBall 0 r₂)` |
| `h_M_diff_num` (optional) | `sup ‖(H_η - H_0) w‖` over the same set |
| `h_M_diffp_num` | `sup ‖(H_η' - H_0') w‖` over the same set |

Each numerical axiom is registered in `lemma.toml` with a `compute_*_bound`
oracle. The verifier checks `declared ≥ oracle.bound`.

Throughout, fix `r₁ := (1+r)/2` and `r₂ := (3+r)/4`, so `r < r₁ < r₂ < 1`.

---

## File structure

New files in `ProofRefinement/Lemma54/Proof/Lib/`:

```
Lemma54_Paper.lean           -- main theorem (steps 1+7 glued)
Lemma54_Paper_RBound.lean    -- step 2: ‖F_inv‖ ≤ sinh r₂
Lemma54_Paper_Cauchy.lean    -- step 3: pointwise z-derivative bounds on F_inv
Lemma54_Paper_Identity.lean  -- step 4: identity (75)
Lemma54_Paper_Pderiv.lean    -- step 5: ∂²_p F_inv bound
Lemma54_Paper_Taylor.lean    -- step 6: Lagrange-form remainder in p
```

Each smaller file is independently checkable. The next-run candidate
`Runs/Run002/Candidates/V0.lean` imports `Lemma54_Paper` and wraps its main
theorem.

---

## Step-by-step

### Step 1 — F_inv on the outer disk (~20 lines)

Apply `lemma_5_3` at radius `r₁ = (1+r)/2`. `linarith` discharges
`0 < r₁ < 1`.

```lean
theorem F_inv_on_outer_disk (η : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ pr_paper > 0, ∀ p ∈ Set.Ioo 0 pr_paper,
      ∃ F_inv : ℂ → ℂ,
        AnalyticOnNhd ℂ F_inv (Metric.ball 0 ((1+r)/2)) ∧
        (∀ z ∈ Metric.ball 0 ((1+r)/2), F_p η p (F_inv z) = z) ∧
        (∀ z ∈ Metric.ball 0 ((1+r)/2), F_inv z ∈ S) ∧
        F_inv 0 = 0 := …
```

### Step 2 — R-bound (~80 lines)

Use `lemma_5_3_with_W_inv` at radius `r₁`, giving `W_inv z ∈ closedBall 0 r₂`.
Prove `norm_sin_le_sinh_norm` (parallel to `norm_cos_le_cosh_norm`, ~30 lines).
Then for `z ∈ disk r₁`, `‖F_inv z‖ = ‖sin (W_inv z)‖ ≤ sinh r₂`.

```lean
def R_val (r : ℝ) : ℝ := Real.sinh ((3 + r) / 4)

theorem norm_sin_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := …

theorem F_inv_norm_bound … :
    ∀ z ∈ disk r₁, ‖F_inv z‖ ≤ R_val r := …
```

At `r = 23/25`, `R_val ≈ 1.143`.

### Step 3 — Cauchy bounds on z-derivatives of F_inv (~300 lines)

For each `z₀ ∈ disk r`, recenter: `g w := F_inv (z₀ + w)` is analytic on
`ball 0 ρ` with `ρ := r₁ - ‖z₀‖ ≥ (1-r)/2`, and `‖g w‖ ≤ R_val r`.
Apply `cauchy_taylor_coeff_bound_closedBall` with `R := ρ`, `M := R_val r`,
`k = 1, 2`.

```lean
theorem F_inv_first_deriv_bound … :
    ∀ z₀ ∈ disk r, ‖deriv F_inv z₀‖ ≤ 2 * R_val r / (1 - r) := …

theorem F_inv_second_deriv_bound … :
    ∀ z₀ ∈ disk r, ‖iteratedDeriv 2 F_inv z₀‖ ≤ 8 * R_val r / (1 - r) ^ 2 := …
```

The `taylor_coeff g k → iteratedDeriv k F_inv z₀` conversion is a one-line
`HasDerivAt`-comp shift; write a small `taylor_coeff_recentered` helper if
useful.

### Step 4 — Identity (75) (~250 lines)

Differentiate `F_p η p (F_inv p z) = z` in `p` at fixed `z`. The chain rule
gives

```
∂_p F_inv = -(H_η - H_0)(F_inv) / (F_p)' (F_inv)
```

You need `(F_p)' (F_inv z) ≠ 0`. Apply `F_p_deriv_ne_zero_small_p` to the
compact set `K := closure (F_inv '' disk r) ⊆ S` to get a `p_inj > 0`;
intersect with `pr_paper`.

For a quantitative lower bound, use
```
‖(F_p)' w‖ ≥ ‖H_0' w‖ - p · ‖(H_η' - H_0') w‖ ≥ 1/cos r₂ - p · M_diffp_val
```
which is `≥ 1/(2 cos r₂)` for `p` small. Tighten `pr_paper` once more.

Use `HasDerivAt` in `p` only — joint analyticity in `(p, z)` is not needed.
The derivative-of-inverse formula follows from `F_p η p (F_inv p z) = z` and
`(F_p η p)'(F_inv p z) ≠ 0` via `HasFDerivAt.localInverse` or by
hand-rolling from `HasDerivAt` (both are short).

```lean
theorem F_p_deriv_lower_bound_at_F_inv … :
    ∀ z ∈ disk r, 1 / (2 * Real.cos r₂) ≤ ‖deriv (F_p η p) (F_inv z)‖ := …

theorem identity_75 … :
    ∀ z ∈ disk r, HasDerivAt (fun q : ℝ => F_inv_at q z)
      (-(H_eta η (F_inv z) - H0 (F_inv z)) / deriv (F_p η p) (F_inv z)) p := …
```

### Step 5 — Bound on ∂²_p F_inv (~250 lines)

Differentiate identity (75) once more. Substitute the explicit bounds:

- `‖∂_p F_inv‖ ≤ M_diff_val · 2 cos r₂` (from step 4)
- `‖(H_η - H_0)(F_inv)‖ ≤ M_diff_val`
- `‖(H_η' - H_0')(F_inv)‖ ≤ M_diffp_val`
- `‖(F_p)'' (F_inv)‖ ≤ closed-form bound from step 3 plus `bound_43_paper`
- `‖1 / (F_p)'(F_inv)‖ ≤ 2 cos r₂`

```lean
theorem F_inv_second_p_deriv_bound … :
    ∀ p ∈ Set.Ioo 0 pr_paper, ∀ z ∈ disk r,
      ‖iteratedDerivWithin 2 (fun q : ℝ => F_inv_at q z) (Set.Ioo 0 pr_paper) p‖
        ≤ Cr_aux := …
```

`Cr_aux` is a closed-form expression in `(M_diff_val, M_diffp_val, R_val, r, η)`.

### Step 6 — Taylor remainder in p (~150 lines)

For each fixed `z ∈ disk r`, define `e_z(p) := F_inv_at p z - sin z - p · ψ z`
where `ψ z := (z - H_η η (sin z)) · cos z`. Then `e_z(0) = 0` (because
`F_inv_at 0 = sin`) and `∂_p e_z(0) = 0` by definition of `ψ`.

Apply `taylor_mean_remainder_lagrange` (split `e_z` into real and imaginary
components if needed) using the bound from step 5 to get

```
‖e_z(p)‖ ≤ Cr_paper r · p^2,    Cr_paper r := Cr_aux / 2.
```

```lean
theorem error_bound_p2 … :
    ∀ p ∈ Set.Ioo 0 pr_paper, ∀ z ∈ disk r,
      ‖F_inv_at p z - Complex.sin z - ↑p * ((z - H_eta η (sin z)) * cos z)‖
        ≤ Cr_paper r * p^2 := …
```

### Step 7 — Glue + final theorem (~100 lines)

```lean
theorem lemma_5_4_paper (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ pr_paper > 0, ∀ p ∈ Set.Ioo 0 pr_paper, ∀ z ∈ disk r,
      ∃ F_inv : ℂ → ℂ,
        F_p η p (F_inv z) = z ∧
        ‖F_inv z - Complex.sin z - ↑p * ((z - H_eta η (sin z)) * cos z)‖
          ≤ Cr_paper r * p ^ 2
```

Then in `Runs/Run002/Candidates/V0.lean`:

```lean
def Cr_val : ℝ := <numerical instantiation of Cr_paper at r = 23/25>

theorem lemma_5_4_search : … := by
  -- Apply lemma_5_4_paper, push numerical M_*_val into Cr_paper.
  …
```

---

## Numerical instantiation at r = 23/25

| Symbol | Value | Source |
|---|---|---|
| `r` | `23/25 = 0.92` | given |
| `r₁ = (1+r)/2` | `24/25 = 0.96` | def |
| `r₂ = (3+r)/4` | `49/50 = 0.98` | def |
| `R_val = sinh r₂` | `≈ 1.143` | step 2, closed form |
| `M_H0p_val = 1 / cos r₂` | `≈ 4.97` | step 5, closed form |
| `M_Hetap_val` | oracle-backed | numerical axiom |
| `M_diff_val` | oracle-backed | numerical axiom |
| `M_diffp_val` | oracle-backed | numerical axiom |

The `M_*_val` numerical axioms are stated on `sin '' closedBall 0 r₂`, which
is strictly tighter than the rectangle `Ω(δ, B)` used in the certified
pipeline. Update the oracle inputs accordingly.

---

## Execution order

1. Read `assets/pdf/braverman.pdf` §5 first. ~10 minutes.
2. Step 1 — opens the proof. ~5 minutes.
3. Step 2 — closed-form `R_val`. ~10 minutes.
4. Step 3 — Cauchy bounds. ~15 minutes.
5. Step 4 — identity (75). ~15 minutes; the IFT form in Mathlib applies
   directly because we only need `HasDerivAt` in `p` at fixed `z`.
6. Step 5 — second p-derivative bound. ~10 minutes (mechanical once 4
   is done).
7. Step 6 — Taylor remainder. ~10 minutes.
8. Step 7 — glue + V0 candidate. ~5 minutes.
9. Verify `#print axioms lemma_5_4_paper` shows only Lean primitives + the
   declared numerical axioms.

Total: ~1 hour to get a clean compile and the right `#print axioms` output.

---

## Definition of done

- New files compile under `lake build`.
- `Runs/Run002/Candidates/V0.lean`'s `#print axioms` returns only:
  - `propext`, `Classical.choice`, `Quot.sound`,
  - the numerical axioms registered in `lemma.toml`.
- The strings `paper_taylor_argument`, `paper_taylor_argument_split`,
  `paper_taylor_argument_std`, `paper_taylor_argument_diff` are absent.
- The evaluator reports `PASS` with a numerical `Cr_val`.
- The three hypothesised seed axioms are removed from
  `lemma.toml`'s `seed_axioms.allowed`.

---

## References

- Paper: `assets/pdf/braverman.pdf`, §5 pp. 21–24 (Lemma 5.3, Lemma 5.4,
  equations (75)–(76)).
- Existing Lean: `LeanProof/Lemma54.lean` (MVT proof, full),
  `LeanProof/Lemma53.lean` (F_inv existence, full),
  `LeanProof/Lemma42.lean` (`bound_43_paper`, `H_eta_bound_paper`).
- Existing helpers:
  `ProofRefinement/Lemma54/Proof/Lib/Lemma54_Cauchy.lean`
  (`cauchy_taylor_coeff_bound`, `M_H_bound`).
