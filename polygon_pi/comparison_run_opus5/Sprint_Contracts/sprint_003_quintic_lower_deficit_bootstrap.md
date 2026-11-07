# sprint_003_quintic_lower_deficit_bootstrap

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V2.lean` (score `329947/10000000 = 0.0329947`)
**Target file:** `Candidates/V3.lean`
**Side:** `lower`
**Strict improvement required:** yes

## Goal

Give the **lower** side its own analytic ingredient — a quintic Taylor *upper*
bound on `sin`, hence a *lower* bound on the polygon deficit — and run it as a
bootstrap in the mirror image of sprint 002's upper-side one. This converts
`lambda` from "however many radical digits we felt like certifying" into a bound
that sits within `5 × 10⁻⁷` of its permanent ceiling `π − 2√2`, in one sprint.

`kappa` is not touched. `lambda` goes `29/100 → 313165/1000000`, score
`0.0329947 → 0.0098297`.

## Rationale

### The headroom is almost entirely on the lower side, and it is not a digit grind

Both sides now have exactly computable ceilings.

| side | current | permanent ceiling | headroom |
|---|---|---|---|
| `kappa` | `0.3229947` | `π³/96 = 0.32298205` (`sup_n 4ⁿ(π − Pₙ)`, not attained) | `1.27e-5` |
| `lambda` | `0.29` | `π − 2√2 = 0.31316553` (attained at `n = 0`) | `2.32e-2` |

The lower side holds **three orders of magnitude more** headroom than the upper
side. Note also a correction to `Experience.md`'s sprint_002 note: a higher-order
Taylor bound does **not** lower the upper-side floor. `4ⁿ(π − Pₙ) → π³/96` from
below, so `π³/96` is the exact infimum of admissible `kappa` no matter how many
Taylor terms are used. The upper side is finished to within `1.27e-5` forever.
Every remaining sprint in this workspace is a lower-side sprint.

### Three analytically distinct shapes were compared

**(A) Deeper radical certification of `polygonLower d`** — sprint_001's own
recommendation, and sprint_002's "Next" line. `d = 3` buys `lambda ≤ 0.30812`,
`d = 4` buys `0.31190`, and each level costs one more staged `nlinarith` at ~2
more decimal digits. *Objection:* this is a pure `precision` rung on the chain
sprint_001 already built — the same chain, one digit further along, which is
exactly the failure mode directive 1 names. It also caps out below this sprint's
result while costing comparable work.

**(B) Upper-side depth-3 bootstrap and/or a septic upper Taylor bound.**
*Objection:* worth at most `1.27e-5` combined (see the table), it is the same
chain sprint_002 just built, and per the correction above the septic term cannot
move the floor at all. Strictly dominated.

**(C) A lower bound on the deficit — this sprint.** The lower conjunct reduces
(sprint_001, exactly) to certifying `lambda < π − polygonLower 0`. There are only
two possible sources of a rational lower bound on `π`: certify `polygonLower d`
from below for larger `d` (that is (A)), or prove an inequality
`π − polygonLower n ≥ (something computable)` and add it to a certified
`polygonLower n`. The second source **does not exist anywhere in the workspace** —
`V2` has `deficit_le` and no companion. That is the untouched factor directive 2
asks for: the loop has interrogated the cubic constant, the `π`-bound factor, and
the radical digits, but never the *direction* of the Taylor estimate.

(C) wins on both novelty and yield: it introduces a genuinely new analytic
object, and it lands `lambda` within `5e-7` of a ceiling that can never be
exceeded, retiring the lower side the way sprint_002 retired the upper side.

### Why the numbers work out

`sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0` gives, by the identical algebra that
produced `deficit_le` (the `n` cancels the same way),

    π − polygonLower n  ≥  π³/(96 · 4ⁿ) − π⁵/(30720 · 4ⁿ · 4ⁿ).

At `n = 2` this is `≥ 0.020147457` against the true deficit `0.020147500` — an
error of `4.3e-8`. Added to a certified `polygonLower 2 ≥ 3.121445136` it pins
`π ≥ 3.141592597`, i.e. **`π` to 9 correct digits from the polygon itself**, with
no deeper radical than the one `V2` already certifies. Then

    π − 2√2  ≥  3.141592597 − 2.828427126  =  0.313165471,

against the true `0.313165528`. `lambda = 0.313165` clears it with margin
`4.7e-7`.

The `π⁵` correction term needs an *upper* bound on `π`, which
`Candidates/V2/CubicDeficit.lean` already proves (`pi_le_round_five`,
`π ≤ 3.1416336`). The two sides of the workspace feed each other for the first
time; nothing is circular, because `pi_le_round_five` never mentions the quintic
and `deficit_ge` is proved with `π³`, `π⁵` symbolic.

All constants below were verified in exact rational arithmetic; reproduce or
adjust them with a script in `Scratch/`.

## Concrete edits expected

- `Candidates/V3/DeficitMonotone.lean` — verbatim copy of `V2`'s, namespace
  renamed to `…Candidates.V3`. Unchanged content; it is what reduces the lower
  conjunct to `n = 0`.
- `Candidates/V3/CubicDeficit.lean` — verbatim copy of `V2`'s, namespace renamed.
  Still needed in full: `deficit_le` and `pi_cube_div_lt` carry the upper
  conjunct unchanged, `sub_sin_le_cube_div_six` is the *input* to the new quartic
  cosine bound, and `pi_le_round_five` supplies the `π⁵` upper bound.
- `Candidates/V3/QuinticDeficit.lean` — **new**, the whole content of this sprint
  (sections 1–5 below).
- `Candidates/V3.lean` — `lambda := 313165/1000000`, `kappa := 3229947/10000000`
  (unchanged), `-- @parent V2`. The lower conjunct's proof is `V2`'s with
  `lambda_lt_deficit_zero` re-proved from the new `pi_ge_round_five`; the upper
  conjunct is copied verbatim. The four-digit radical lemmas `sqrt_two_lt`,
  `sqrt_two_add_sqrt_two_lt`, `sqrt_two_sub_gt` currently in `V2.lean` move into
  `QuinticDeficit.lean` at 9 digits — keep exactly one definition per name, since
  all files share the namespace.
- `Experience.md` — append the sprint entry.

Nothing else. Do not edit `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, or `Candidates/V0*`, `V1*`, `V2*`.

## The mathematical plan, in the order to write it

### 1. `cos t ≤ 1 − t²/2 + t⁴/24`, globally, with **no** `MonotoneOn`

Do not reach for a second derivative or for `monotoneOn_of_deriv_nonneg` here.
The half-angle identity turns this into the cubic sine bound you already have:

- `rcases le_or_lt 12 (t ^ 2)`. In the `12 ≤ t ^ 2` branch,
  `1 − t²/2 + t⁴/24 − 1 = t²(t² − 12)/24 ≥ 0`, so
  `nlinarith [Real.cos_le_one t, sq_nonneg t]` closes it.
- In the `t ^ 2 < 12` branch, reduce to `0 ≤ t` first (`rcases le_or_lt 0 t`; the
  negative case is `simpa [Real.cos_neg] using key (-t) …`, since both sides are
  even). Set `u := t / 2`, so `u ≥ 0` and `u ^ 2 < 3`.
  - `hs : u − u ^ 3 / 6 ≤ Real.sin u` — this is
    `sub_sin_le_cube_div_six u` from `CubicDeficit.lean`, rearranged.
  - `hnn : 0 ≤ u − u ^ 3 / 6` — from `u ≥ 0` and `u ^ 2 < 3 < 6`, one `nlinarith`.
  - `hsq : (u − u ^ 3 / 6) ^ 2 ≤ Real.sin u ^ 2` — `pow_le_pow_left₀ hnn hs 2`.
  - `hc : Real.cos t = 1 − 2 * Real.sin u ^ 2` — from `Real.cos_two_mul (t/2)`
    (rewrite `2 * (t/2) = t`) plus `Real.sin_sq_add_cos_sq (t/2)`; plain
    `linarith`, since `cos (t/2) ^ 2` is a single atom.
  - Finish: `1 − 2(u − u³/6)² = 1 − 2u² + 2u⁴/3 − u⁶/18` and `u = t/2` makes
    `2u² = t²/2`, `2u⁴/3 = t⁴/24`. Give `nlinarith` the `u ^ 6 ≥ 0` hint
    explicitly (`pow_nonneg` / `even_pow`), and keep it to one product per call
    per the standing rule in `Experience.md`.

### 2. `sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0`

Now the cheap global idiom applies, because `χ' t = 1 − t²/2 + t⁴/24 − cos t` is
non-negative on *all* of `ℝ` by step 1 — no `MonotoneOn`, no `interior`, no
`Convex` side goal:

```
χ t := t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
```

State the derivative in the **raw combinator shape**
`1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - Real.cos x` (sprint_002's rule — do not
pre-simplify to `x ^ 2 / 2`), build it with
`hasDerivAt_id'`, `(hasDerivAt_pow 3 x)`, `(hasDerivAt_pow 5 x)` each fixed by a
`simpa` for the `Nat.cast` coefficient, `.div_const`, `.sub`, `.add`, then
`monotone_of_hasDerivAt_nonneg`. The non-negativity lemma is plain **`linarith`**
from step 1 (`3 * x ^ 2 / 6` and `x ^ 2 / 2` are the same linear multiple of the
atom `x ^ 2`; likewise `5 * x ^ 4 / 120` and `x ^ 4 / 24`). Extract with
`simp only [Real.sin_zero]` / `norm_num` / `linarith` exactly as
`sub_sin_le_cube_div_six` does.

### 3. `deficit_ge`

```lean
theorem deficit_ge (n : ℕ) :
    Real.pi ^ 3 / (96 * 4 ^ n) - Real.pi ^ 5 / (30720 * 4 ^ n * 4 ^ n)
      ≤ Real.pi - polygonLower n
```

State the `4 ^ n * 4 ^ n` form rather than `16 ^ n`; then the proof is
`deficit_le`'s line for line with the inequality reversed —
`mul_le_mul_of_nonneg_left` on the step-2 bound at `x = π / 2 ^ (n+2)`, the same
`hxN`, `hL`, `h4n : (4:ℝ) ^ n = 2 ^ n * 2 ^ n`, `hpow : (2:ℝ) ^ (n+2) = 4 * 2 ^ n`,
then `field_simp; ring`.

### 4. Nine-digit radical certification, *upper* direction

Same staged shape as before, one `nlinarith` per radical level, one
multiplication per call. Verified exact:

| lemma | statement |
|---|---|
| `sqrt_two_lt` | `√2 < 1414213563/1000000000` |
| `sqrt_two_add_sqrt_two_lt` | `√(2 + √2) < 1847759066/1000000000` |
| `sqrt_two_sub_gt` | `390180642/1000000000 < √(2 − √(2 + √2))` |
| `polygonLower_two_gt` | `3121445136/1000000000 < polygonLower 2` |

(True values `1.41421356237`, `1.84775906502`, `0.39018064403`,
`3.12144515226`.) The third stage is where the error is amplified: at 8 digits it
is *false*, so do not economise on digits there.

### 5. The lower bootstrap

First isolate the one big-number lemma so everything downstream stays small:

```lean
theorem pi_pow_five_div_lt : Real.pi ^ 5 / 7864320 < 3891496/100000000000
```

from `pow_le_pow_left₀ Real.pi_pos.le pi_le_round_five 5` plus `norm_num`
(true value `3.89122e-5`; the bound is `3.891496e-5`).

Then the step, with `deficit_ge 2` normalised by `norm_num`
(`96 * 4 ^ 2 = 1536`, `30720 * 4 ^ 2 * 4 ^ 2 = 7864320`):

```lean
theorem pi_ge_bootstrap_step (c : ℝ) (h0 : 0 ≤ c) (hc : c ≤ Real.pi) :
    3121445136/1000000000 + c ^ 3 / 1536 - 3891496/100000000000 ≤ Real.pi
```

(`pow_le_pow_left₀ h0 hc 3` for `c ^ 3 ≤ π ^ 3`, `polygonLower_two_gt`,
`pi_pow_five_div_lt`, one `linarith`.)

Seed with `polygonLower_two_gt` and `polygonLower_lt_pi 2`, then five rounds,
each `have h := pi_ge_bootstrap_step _ (by norm_num) prev; norm_num at h; linarith`:

| round | proved lower bound for `π` | slack in the exact check |
|---|---|---|
| 1 | `31412067/10000000` | `9.4e-9` |
| 2 | `62831703/20000000` (`3.14158515`) | `1.0e-8` |
| 3 | `78539811/25000000` (`3.14159244`) | `1.4e-8` |
| 4 | `314159259/100000000` | `5.0e-9` |
| 5 | `3141592597/1000000000` | `8.6e-10` |

Round 3 alone already clears the target `lambda`; rounds 4–5 buy the stretch.

### 6. `lambda`

`lambda_lt_deficit_zero : lambda < π − polygonLower 0` from
`polygonLower_zero_eq`, `pi_ge_round_five`, and `sqrt_two_lt`:
`3.141592597 − 2 × 1.414213563 = 0.313165471 > 0.313165`. The rest of
`polygon_pi_constant_search` is `V2`'s, unchanged.

## Acceptance criteria

- [ ] `Candidates/V3.lean` declares `def lambda : ℝ := 313165/1000000` and
      `def kappa : ℝ := 3229947/10000000`, each on a single line
- [ ] `Candidates/V3/QuinticDeficit.lean` contains a theorem stating
      `Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120` for `0 ≤ x`, proved with no
      numeric hypothesis on `π` anywhere in its dependency chain
- [ ] `Candidates/V3/QuinticDeficit.lean` contains a `deficit_ge`-shaped theorem
      lower-bounding `Real.pi - polygonLower n` uniformly in `n`, with `π`
      symbolic
- [ ] a theorem proving `Real.pi ≥ 3141592597/1000000000` (or better) exists and
      does not depend on any forbidden token or on `Mathlib.Analysis.Real.Pi`
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V3` succeeds
- [ ] the evaluator passes all twelve stages with `--no-log`
- [ ] axiom closure is exactly a subset of `{propext, Classical.choice, Quot.sound}`
- [ ] `strict_improvement = True` and `score ≤ 99/10000` (`0.0099`), i.e.
      `lambda ≥ 0.31316` with `kappa` unchanged
- [ ] **required floor:** even on a partial result, `lambda ≥ 3125/10000`, which
      is strictly better than the best achievable by deeper radical
      certification alone (`0.31190` at depth 4) — otherwise the architectural
      claim of this sprint is not demonstrated

Target `lambda = 313165/1000000` (score `98297/10000000 = 0.0098297`). The
theoretical optimum of the entire problem is `π³/96 − (π − 2√2) = 0.00981652`, so
a successful sprint lands within `1.4e-5` of it.

## Degraded outcome

If step 1 or step 2 genuinely blocks, do **not** silently substitute a deeper
radical certification and call the sprint done — that is candidate (A) above and
the planner rejected it. Ship whatever `lambda` you can certify, and write into
`Experience.md`: the exact goal state where it stopped, which of
`monotone_of_hasDerivAt_nonneg` / `monotoneOn_of_hasDerivWithinAt_nonneg` /
`monotoneOn_of_deriv_nonneg` you tried and their exact signatures in this
Mathlib, and whether `Real.cos_two_mul` / `Real.sin_sq_add_cos_sq` /
`Real.cos_le_one` resolved. That note is what lets sprint 004 attack the same
rung from the `MonotoneOn` side instead.

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V3
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V3.lean --no-log
```

A `Scratch/lower_bootstrap_v3.py` reproducing the rational iteration is
encouraged, in the style of `Scratch/bootstrap_iteration_v2.py`.

## Notes / expected obstructions

- Read `Experience.md`'s sprint_001 and sprint_002 entries in full before
  starting. Everything in this contract's plan is an inversion of something
  already recorded there; in particular the raw-combinator-shape rule for
  `HasDerivAt`, the "one `nlinarith` per radical level, one multiplication per
  `nlinarith`" rule, and the `4 ^ n` / `2 ^ (n+2)` cancellation recipe all apply
  verbatim.
- The one real novelty risk is step 1. The half-angle route is recommended
  precisely because it needs no new calculus lemma — it consumes
  `sub_sin_le_cube_div_six`, which is already proved and already in the build.
  If you nonetheless want the derivative route, `monotoneOn_of_deriv_nonneg` and
  `monotoneOn_of_hasDerivWithinAt_nonneg` were both confirmed present in sprint
  001; the cost is `ContinuousOn` and `interior (Set.Ici 0)` side goals that the
  global lemma does not have.
- Namespace hygiene: `V3.lean`, `V3/CubicDeficit.lean`, `V3/QuinticDeficit.lean`
  and `V3/DeficitMonotone.lean` all open `…Candidates.V3`, so a name may be
  defined only once across the four files. `CubicDeficit.lean` already owns
  `sqrt_two_gt`, `sqrt_two_lt_two`, `sqrt_two_add_sqrt_two_lt_two`,
  `sqrt_two_add_sqrt_two_gt`, `sqrt_two_sub_lt`, `polygonLower_two_eq`,
  `polygonLower_two_lt`; the new 9-digit family must use the complementary
  `_lt` / `_gt` names listed in section 4, and `polygonLower_two_eq` must not be
  redefined.
- `QuinticDeficit.lean` imports `Proof.Main` and `Candidates.V3.CubicDeficit`
  (sibling imports are permitted). No `lemma.toml` registration is required.
- Watch the direction of every rounding. The `π⁵` term enters with a minus sign,
  so it needs an **upper** bound on `π`; the `π³` term needs a **lower** bound;
  `2√2` needs an **upper** bound on `√2`; `polygonLower 2` needs a **lower**
  bound, hence an **upper** bound on `√(2 + √2)`, hence an **upper** bound on
  `√2`. Three of the four want `√2` from above — that is `sqrt_two_lt`, not
  `CubicDeficit`'s `sqrt_two_gt`.
- Do not weaken `kappa`. It must stay `3229947/10000000`; the evaluator compares
  `kappa - lambda` against the incumbent and a raised `kappa` would eat the gain.
