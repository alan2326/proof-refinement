# sprint_001_upper_cubic_taylor

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V0.lean` (score `1`)
**Target file:** `Candidates/V1.lean`
**Side:** `upper`
**Strict improvement required:** yes

## Goal

Replace V0's cubic estimator with the tight Taylor bound `sin x > x - x³/6`
(for `x > 0`) and drive `kappa` from `1` down to `2/3`. `lambda` stays at `0`.
This attacks a factor V0 did not touch — the cubic coefficient — rather than
grinding the `π ≤ 4` slack V0 already exploited.

## Rationale

V0 proves the upper conjunct through `Real.sin_gt_sub_cube`, which delivers
`x - x³/4 < sin x` on `(0, 1]`. Applied at `x = π / 2^(n+2)` and scaled by
`2^(n+2)`, this gives

    π - polygonLower n  <  π³ / (64 · 4^n)

then uses `π ≤ 4` to bound `π³ ≤ 64` and lands `kappa = 1`.

Two constants sit inside that chain: the cubic coefficient `1/4` (Mathlib's
convenience bound, not tight) and the ceiling on `π³`. V0 spent its budget on
the second one being loose enough that `1` closes; nothing has interrogated the
first. This sprint replaces the cubic estimator entirely.

The true fourth-degree Taylor lower bound is `sin x > x - x³/6` for every
`x > 0`. It is not the same chain as V0 with a smaller constant — it needs a
different proof (`strictMonoOn_of_deriv_pos` applied to
`f(x) = sin x - x + x³/6`), pulled through by `Real.one_sub_sq_div_two_lt_cos`
which delivers exactly `f'(x) = cos x - 1 + x²/2 > 0` for `x > 0`. Experience
already flags this lemma as available in this checkout and points at
`Real.lt_tan` in `Trigonometric/Bounds.lean` as a worked example of the same
pattern.

Rescaling: at `x = π / 2^(n+2)` and multiplying by `2^(n+2)`,

    π - polygonLower n  <  π³ / (96 · 4^n)

and with `π ≤ 4` giving `π³ ≤ 64`, we obtain

    π - polygonLower n  <  64 / (96 · 4^n)  =  (2/3) / 4^n

so `kappa = 2/3` closes the contract. Score: `1 → 2/3` (a 1/3 drop from a
single architectural swap, no numerical fiddling required).

Directive checks:

- **Architectural, not precision:** the estimator function is different. The
  `1/4 → 1/6` change is not a tweak of the same argument; it is a categorically
  different lower bound for `sin`, derived from a different Mathlib lemma along
  a different monotonicity descent.
- **Untouched factor:** V0 did not attempt any tightening of the cubic
  coefficient. This sprint hits the one factor V0's chain never interrogated,
  leaving the `π ≤ 4` factor and the depth-scaling factor for later sprints to
  attack independently.
- **Bounded to one session:** one small helper lemma
  (`sin_gt_sub_cube_div_six` or similar) plus the adapted upper-conjunct proof.
  The lower conjunct is unchanged from V0.

Concrete witness that this succeeds: with the tight Taylor coefficient `1/6`,
`4^n · (π - polygonLower n)` is monotonically ascending in `n` toward the
asymptotic value `π³/96 ≈ 0.3230`, well below `2/3 ≈ 0.667`. So `kappa = 2/3`
is not merely feasible, it has substantial headroom, meaning small imprecisions
in the arithmetic collapse do not endanger the sprint.

## Concrete edits expected

- `Candidates/V1.lean` — declares `def lambda : ℝ := 0` and
  `def kappa : ℝ := 2 / 3` on single lines. Proves the contract with an inline
  helper lemma `sin x > x - x^3 / 6` for `x > 0`, then adapts V0's rescaling
  arithmetic to the `1/6` coefficient. The lower conjunct is unchanged
  (`polygonLower_lt_pi`).
- `Experience.md` — append a `## sprint_001 — upper_cubic_taylor` entry noting
  which monotonicity route landed (or, if `BLOCKED`, the exact goal stuck on).

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, `V0.lean`, or any sprint contract is out of scope.

A derived-theorem file `Candidates/V1/SinCubicLower.lean` is **allowed but not
required**. Prefer inline unless the proof exceeds ~120 lines, in which case
lift the helper into that file. Either way it contains theorems only, no
axioms, and is imported only by `Candidates/V1.lean`.

## Acceptance criteria

- [ ] `Candidates/V1.lean` declares `def kappa : ℝ := 2 / 3` and
      `def lambda : ℝ := 0` on single lines
- [ ] `-- @parent V0` header present
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V1` succeeds
- [ ] evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
      (no `native_decide`, no project axiom, no `sorry`)
- [ ] `score = 2/3`, strictly below parent score `1`
- [ ] no import of `Mathlib.Analysis.Real.Pi.*`, bare `Mathlib`, or any of the
      text-blocked identifiers (`pi_lt_sqrtTwoAddSeries`,
      `pi_gt_sqrtTwoAddSeries`, `sqrtTwoAddSeries_step_up`/`_down`,
      `pi_lower_bound_start`, `pi_upper_bound_start`, `pi_gt_three`,
      `pi_gt_3141592`, `pi_lt_3141593`)

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V1
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V1.lean --no-log
```

## Notes / expected obstructions

- **The core helper** is a strict lower bound
  `∀ x, 0 < x → x - x^3 / 6 < Real.sin x`. Two known routes:
  1. Direct: `f x := Real.sin x - (x - x^3/6)`, `f 0 = 0`,
     `f' x = Real.cos x - 1 + x^2/2`, which is `> 0` for `x > 0` by
     `Real.one_sub_sq_div_two_lt_cos` (confirmed present in this checkout —
     Experience §env-notes). Then `strictMonoOn_of_deriv_pos` on `Set.Ici 0`
     gives `0 < f x` for `x > 0`. The derivative assembly is
     `Real.hasDerivAt_sin`, `hasDerivAt_pow`, `.div_const`, `.sub`. Read
     `Real.lt_tan`'s proof in `Trigonometric/Bounds.lean` for the boilerplate
     — Experience explicitly points at it as the template. `fun_prop` closes
     the `ContinuousOn` side goals.
  2. Search-first: try `lean_local_search` / `lean_loogle` for
     `sin _ > _ - _ ^ 3 / 6` before rolling your own. If Mathlib has an
     equivalent under a different name, use it. Do not spend more than one
     search pass before falling back to route 1 — the proof is short.

- **The rescaling arithmetic** is essentially V0's, with `4` replaced by `6`.
  The identity `2^(n+2) · (π/2^(n+2) - (π/2^(n+2))^3 / 6) = π - π^3 / (96 · 4^n)`
  closes with `field_simp; ring` after the `hpow` and `h4n` rewrites from V0
  (both listed in Experience §env-notes as one-liners).

- **The closing arithmetic** needs `π^3 / (96 · 4^n) ≤ (2/3) / 4^n`, i.e.
  `π^3 ≤ 64`. Same `pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 3` V0 uses,
  then `norm_num` to reduce `4^3` to `64`. Do not introduce a new π upper
  bound in this sprint — the point is to isolate the cubic-coefficient
  improvement so a future sprint can attack `π ≤ 4` separately.

- **`x ≤ 1` side condition:** unlike `Real.sin_gt_sub_cube`, the tight bound
  `sin x > x - x^3/6` holds for all `x > 0` (no ceiling needed), so the V0
  `hx1 : π / 2^(n+2) ≤ 1` step disappears. If the search returns a Mathlib
  lemma that requires `x ≤ 1`, that is fine — V0's `hx1` proof carries over
  verbatim — but the cleaner derivation from route 1 has no such restriction.

- **Do not touch the lower conjunct.** `simpa [lambda] using polygonLower_lt_pi n`
  still closes it, and any change there is out of scope. `lambda = 0` remains
  because a nontrivial `lambda > 0` needs a fifth-order Taylor argument
  (`sin x < x - x^3/6 + x^5/120`) plus a `π ≥ 3` lower bound; that is a
  separate future sprint, not this one.

- **If truly `BLOCKED`:** exit only after (a) stating the stuck goal with
  `lean_goal`, (b) trying at least two tactically distinct closes on it (not
  three `simp` flavours), and (c) writing the goal and what you tried into
  `Experience.md` so the next planner can attack it from a different angle
  rather than repeating your route.
