# sprint_001_deficit_monotonicity_lambda

**Rung type:** `architectural`

**Parent candidate:** `Candidates/V0.lean` (score `1`)
**Target file:** `Candidates/V1.lean`
**Side:** `lower`
**Strict improvement required:** yes

## Goal

Lift `lambda` off zero for the first time by proving that the scaled polygon
deficit `D n := 4 ^ n * (π - polygonLower n)` is **monotone non-decreasing in
`n`**, so that `D n ≥ D 0 = π - polygonLower 0 = π - 2√2` uniformly. `kappa`
stays at `1`; the whole score movement this sprint comes from the lower side.

Target: `lambda ≥ 23/100`, hence score `≤ 77/100`.

## Rationale

### Why the lower side, and why this route

The lower conjunct has never been touched — at `lambda = 0` it is discharged by
the trusted `polygonLower_lt_pi` and contributes nothing. Bulletin directive 3
asks that both sides move, and the lower side is where an entire structural
ingredient is missing rather than where a constant is loose.

The contract's admissible band is, for every `n`,

```
lambda  <  4 ^ n * (π - polygonLower n)  <  kappa
```

Write `N = 2 ^ (n+2)`, `x = π / N`, so `polygonLower n = N sin x` and

```
D n := 4 ^ n * (π - polygonLower n) = (π ^ 3 / 16) * (x - sin x) / x ^ 3.
```

`(x - sin x)/x ^ 3` decreases in `x` and `x` decreases in `n`, so **`D n`
increases in `n`**: numerically `D 0 ≈ 0.31317`, `D 1 ≈ 0.32050`,
`D 2 ≈ 0.32236`, rising to `π ^ 3 / 96 ≈ 0.32298`. Two consequences that should
shape the whole run:

1. The binding constraint on `lambda` is at `n = 0` and is **attained**. The
   exact ceiling is `lambda < π - 2√2 ≈ 0.3131655`. Nothing about larger `n`
   ever matters for the lower side.
2. Therefore a single monotonicity theorem *closes the analytic content of the
   lower side permanently*. Every later lower-side sprint reduces to sharpening
   one rational number, `π - polygonLower 0`.

That is why this is the right architectural rung rather than a Taylor-series
attack on the lower side. A quintic ladder (`sin x < x - x^3/6 + x^5/120`,
seeded by `Real.one_sub_sq_div_two_lt_cos`) also lifts `lambda`, but only to
about `0.22`, and it leaves the lower side still needing further analytic work
later. Monotonicity gets to the structural ceiling in one theorem.

### Why not the upper side this sprint

The upper chain in V0 is a product of two separately-replaceable factors: the
weak cubic `Real.sin_gt_sub_cube` (`x - x^3/4` where `x - x^3/6` is true) and
the crude `Real.pi_le_four` (where the truth is near `3.1416`). Those are worth
roughly a factor `1.5` and a factor `2.06` respectively and they are the obvious
next two rungs — but attacking them in the same session as the lower side would
blur the attribution in `frontier.csv` and would not fit a bounded session.
`kappa` is explicitly **out of scope** here and is reserved for sprint 002.

### The witness that this is provable

The hard step reduces to one clean one-variable inequality. Using
`polygonLower_eq_mul_sin` at depths `n` and `n+1`, and putting
`y := π / 2 ^ (n+3)` so that `π / 2 ^ (n+2) = 2 * y`:

```
polygonLower (n+1) = 2 ^ (n+3) * sin y
polygonLower n     = 2 ^ (n+2) * sin (2 * y) = 2 ^ (n+3) * sin y * cos y      (sin_two_mul)
3 * π              = 3 * 2 ^ (n+3) * y
```

so `D (n+1) ≥ D n` is equivalent to `4 * polygonLower (n+1) - polygonLower n ≤ 3 * π`,
which after dividing by `2 ^ (n+3) > 0` is exactly

```
sin y * (4 - cos y) ≤ 3 * y.
```

Set `φ y := 3 * y - sin y * (4 - cos y)`. Then `φ 0 = 0` and

```
φ' y = 3 - 4 cos y + cos (2 * y) = 3 - 4 c + (2 c ^ 2 - 1) = 2 * (c - 1) ^ 2 ≥ 0,   c = cos y.
```

The derivative is an **exact square**, so the monotonicity side goal is
`positivity`/`nlinarith`-trivial once the `HasDerivAt` term is assembled. This
is the same `strictMonoOn_of_deriv_pos` shape as `Real.lt_tan`, which
`Experience.md` points at as a worked example. On `Set.Ioo 0 π` we have
`cos y < 1`, so the derivative is strictly positive there if you prefer the
strict version; non-strict monotonicity is sufficient for the contract.

Numerically, the base case: `polygonLower 0 = 2 ^ 1 * √(2 - sqrtTwoAddSeries 0 0)
= 2 √2 ≈ 2.8284271`, and the trusted `polygonLower_lt_pi 1` gives
`π > polygonLower 1 = 4 √(2 - √2) ≈ 3.0614675`. Hence

```
π - 2√2 > 4 √(2 - √2) - 2 √2 ≈ 0.2330404 > 23/100
```

with about `0.003` of slack — comfortable for rational certification with five
decimal digits. Both radicals are `nlinarith`-with-`Real.sq_sqrt` work; there is
one level of nesting and no more.

## Concrete edits expected

- `Candidates/V1/DeficitMonotone.lean` — the derived theorems. Theorems and
  lemmas only, no `axiom`. Expected contents:
  - the one-variable inequality `sin y * (4 - cos y) ≤ 3 * y` on a domain
    containing every `π / 2 ^ (n+3)`;
  - the one-step deficit inequality
    `4 ^ n * (π - polygonLower n) ≤ 4 ^ (n+1) * (π - polygonLower (n+1))`;
  - the uniform bridge
    `π - polygonLower 0 ≤ 4 ^ n * (π - polygonLower n)` for all `n`.
- `Candidates/V1.lean` — `def lambda`, `def kappa`, the rational certification of
  `π - polygonLower 0`, and `polygon_pi_constant_search`. The upper conjunct may
  be carried over from `V0.lean` essentially verbatim.
- `Experience.md` — append the sprint entry.

Nothing else. Do **not** edit `lemma.toml` — the module path
`ProofRefinement.PolygonPi.Candidates.V1.DeficitMonotone` already matches an
allowed prefix and needs no registration. Editing `PolygonCore/`, `Proof/`,
`Evaluator.py`, `scripts/`, sprint contracts, or `Candidates/V0.lean` is out of
scope.

## Acceptance criteria

- [ ] `Candidates/V1.lean` declares `def lambda : ℝ := <rational>` and
      `def kappa : ℝ := 1` **each on a single line**, with
      `lambda ≥ 23/100`
- [ ] `Candidates/V1/DeficitMonotone.lean` exists and contains a theorem whose
      statement is (up to naming and argument order) `∀ n : ℕ,
      Real.pi - polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n)`, proved by
      induction from a one-step deficit inequality — **not** by a per-`n`
      Taylor estimate
- [ ] `Candidates/V1/DeficitMonotone.lean` contains a lemma of the shape
      `Real.sin y * (4 - Real.cos y) ≤ 3 * y` on an interval containing
      `Set.Ioc 0 (Real.pi / 8)`
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V1` succeeds
- [ ] the evaluator passes all twelve stages
- [ ] axiom closure of `polygon_pi_constant_search` is a subset of
      `{propext, Classical.choice, Quot.sound}`
- [ ] `score = kappa - lambda ≤ 77/100`, strictly below the parent score `1`

Optional stretch, only if the required criteria are already met and the session
still has room: certify `π > polygonLower 2 = 8 √(2 - √(2 + √2)) ≈ 3.1214452`
instead of `polygonLower 1`, which supports `lambda = 29/100`. This is a
numerical improvement on the same chain, so it is a bonus, never a substitute
for the monotonicity theorem, and it must not be the reason the sprint runs long.

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V1
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V1.lean --no-log
```

## Notes / expected obstructions

Read the `sprint_000` entry in `Experience.md` first — in particular the
confirmed-working lemma list, and the note that `div_le_div_iff` and
`mul_lt_mul_left` do **not** resolve in this Mathlib.

Specific things likely to cost time:

- **Index bookkeeping.** `polygonLower_eq_mul_sin` at index `n+1` produces
  `2 ^ (n + 1 + 2)`; you want `2 ^ (n + 3)`. Normalize once with `pow_succ` /
  `ring_nf` and keep a single `have hy : Real.pi / 2 ^ (n+2) = 2 * y` in hand
  rather than re-deriving it. The `4 ^ n = 2 ^ n * 2 ^ n` and
  `2 ^ (n+2) = 4 * 2 ^ n` idioms recorded in `Experience.md` close these
  identities in one step.
- **Base values.** `sqrtTwoAddSeries 0 0 = 0` and `sqrtTwoAddSeries 0 1 = √2`
  come from `simp [Real.sqrtTwoAddSeries]` plus `norm_num`; hence
  `polygonLower 0 = 2 * √2` and `polygonLower 1 = 4 * √(2 - √2)`.
- **Certifying `4 √(2 - √2) - 2 √2 > 23/100`.** Do it in two staged steps —
  first pin `√2` between rationals with `Real.sq_sqrt` + `nlinarith`, then pin
  `√(2 - √2)` from below using `Real.le_sqrt` / `Real.sqrt_le_sqrt` with the
  rational bound on `√2` already in context. Trying to hand the whole nested
  expression to one `nlinarith` call is the failure mode here.
- **Domain of the trig lemma.** `y = π / 2 ^ (n+3) ≤ π / 8` for every `n`, and
  `y > 0`. Proving the inequality on `Set.Icc 0 (π/2)` or on all of `Set.Ici 0`
  is fine; do not fight for the largest domain, take whichever makes the
  `ContinuousOn` / `interior` side goals cheapest. `fun_prop` handles the
  continuity obligations for `sin`/`cos`/polynomial combinations unaided.
- **Do not weaken the contract.** The lower conjunct is strict (`<`), but
  monotonicity only needs `≤`; strictness comes free from `lambda < π - 2√2`
  as a rational strict inequality. You do not need strict monotonicity in `n`.

If the deficit-monotonicity theorem turns out to be unreachable, record the
exact blocking goal in `Experience.md` — the fallback route for a later sprint
is the quintic Taylor ladder
`sin x > x - x^3/6` ⟹ `cos x < 1 - x^2/2 + x^4/24` ⟹ `sin x < x - x^3/6 + x^5/120`,
each step a `strictMonoOn_of_deriv_pos` argument seeded by the available
`Real.one_sub_sq_div_two_lt_cos`, which yields `lambda ≈ 0.22` by a completely
different chain. Do not start that ladder in this sprint.

**For the next planner:** `kappa` is untouched by design. The two unexamined
factors in the upper chain are the weak cubic `Real.sin_gt_sub_cube` (`x^3/4`
where `x^3/6` holds) and `Real.pi_le_four`. Sprint 002 should be `upper`.
