# Experience — Polygon-π refinement

Append-only. Generators and planners write here. The point is that a later sprint
should never have to rediscover a dead end, and should be able to pick up a
half-finished attack.

Format per entry:

```
## sprint_<NNN> — <slug>            [<STATUS>]
Goal:        one line
Tried:       what you actually did, tactic families and search terms
Outcome:     what worked / where it stopped, with the exact goal if blocked
Next:        the most promising unexplored angle, if you can name one
```

---

## sprint_000 — workspace setup            [INFRASTRUCTURE]

Goal: stand up the workspace with a fully proved baseline.

Tried: n/a — hand-built by the human before the loop started.

Outcome: `Candidates/V0.lean` proves `ValidPolygonBound 0 1`, score `1`, axiom
closure `{propext, Classical.choice, Quot.sound}`. The upper conjunct goes
through `Real.sin_gt_sub_cube` and `Real.pi_le_four` inline; the lower conjunct
is `polygonLower_lt_pi` directly, since `lambda = 0`.

Environment notes worth knowing before you start:

- This Mathlib is the **module-system** tree (Lean 4.28). Imports are written
  `public import M`, not `import M`. Your own candidate files use plain `import`
  and that is fine, but do not be surprised by the Mathlib sources.
- Lemma names have drifted. Confirmed **not** resolving in this version:
  `div_le_div_iff`, `mul_lt_mul_left` (as an iff on ℝ, it wants a
  `MulRightStrictMono` instance that is not found). Confirmed working:
  `mul_lt_mul_of_pos_left`, `pow_le_pow_left₀`, `le_div_iff₀`,
  `mul_div_mul_left`, `one_le_pow₀`, `Real.sq_sqrt`, `Real.sqrt_sq`,
  `Real.sqrt_le_sqrt`, `strictMonoOn_of_deriv_pos`, `Real.hasDerivAt_sin`,
  `Real.hasDerivAt_cos`, `hasDerivAt_pow`, `Set.self_mem_Ici`. When a name
  fails, grep the Mathlib tree rather than guessing a second time.
- `Real.one_sub_sq_div_two_lt_cos (hx : x ≠ 0) : 1 - x ^ 2 / 2 < cos x` and
  `Real.lt_tan (h1 : 0 < x) (h2 : x < π / 2) : x < tan x` are both available.
  `Real.lt_tan`'s proof in `Trigonometric/Bounds.lean` is a clean worked example
  of the `strictMonoOn_of_deriv_pos` pattern — read it before writing your own.
- `Real.sin_pi_over_two_pow_succ` and `Real.cos_pi_over_two_pow` survive and are
  `@[simp]`, so the nested radical and the trigonometric form are interchangeable.
- `fun_prop` handles the `ContinuousOn` side goals for polynomial-plus-`sin`/`cos`
  functions without help.
- The `4 ^ n` vs `2 ^ (n + 2)` conversion that comes up in every scaling argument:
  `have hpow : (2:ℝ) ^ (n+2) = 4 * 2 ^ n := by ring` together with
  `have h4n : (4:ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num`, then
  `field_simp; ring`. That combination closes the identity in one step.

Next: the first real sprint. Note the trusted surface contains no estimate at
all, so anything quantitative you want must be proved in candidate space — start
by asking which constant in V0's chain is loosest.

---

## sprint_001 — upper_cubic_taylor            [READY_FOR_EVALUATION]

Goal: replace V0's cubic estimator `sin x > x - x^3/4` with the tight Taylor
lower bound `sin x > x - x^3/6` (for `x > 0`), driving `kappa` from `1` to
`2/3`. `lambda` stays at `0`.

Tried: rolled the direct monotonicity route (Route 1 from the contract's Notes).
Defined `f t = sin t - t + t^3/6`; got `HasDerivAt f (cos t - 1 + t^2/2) t` by
assembling `Real.hasDerivAt_sin`, `hasDerivAt_id`, `hasDerivAt_pow 3` chained
through `.div_const 6`, `.sub`, `.add` and rewriting the resulting
`3 * t^2 / 6` down to `t^2 / 2` with `ring`. Positivity of the derivative on
`Set.Ioi 0` follows from `Real.one_sub_sq_div_two_lt_cos htne` plus `linarith`.
`strictMonoOn_of_deriv_pos (convex_Ici 0)` on `Set.Ici 0` (with
`interior_Ici : interior (Set.Ici 0) = Set.Ioi 0`) then gives
`f 0 < f x` for `0 < x`; since `f 0 = 0`, that's `x - x^3/6 < sin x`.
`ContinuousOn f (Set.Ici 0)` closed with `fun_prop` after a `change` to inline
the lambda. Did not attempt a Mathlib search first — the contract explicitly
notes Mathlib lacks a `_/6` variant (see the `_/4`'s docstring, which flags
`_/6` as the tighter bound left unproved).

Downstream rescaling is V0's arithmetic verbatim with `4 → 6` in the estimator,
`64 * 4^n → 96 * 4^n` in the collapsed identity, and `1/4^n → (2/3)/4^n` in the
final bound. The `hpow`/`h4n`/`field_simp; ring` combo (Experience §env-notes)
closes the identity. The `π ≤ 4` → `π^3 ≤ 64` step is unchanged, so this sprint
leaves that factor intact for a future architectural swap.

Outcome: `Candidates/V1.lean` builds, evaluator passes all twelve stages, axiom
closure is `{propext, Classical.choice, Quot.sound}`, score `2/3` (strict
improvement over V0's `1`). Interval width at depth 10 shrinks from
`1/1048576 ≈ 9.54e-07` to `1/1572864 ≈ 6.36e-07`.

Lint notes worth remembering: `Set.left_mem_Ici` is deprecated in favour of
`Set.self_mem_Ici`; the linter also complains about `show` when the term shape
changes (use `change`). Both bit me once on the first build.

Next: two obvious architectural attacks remain unopened. (a) The `π ≤ 4` factor
is still crude — replacing it with any `π ≤ c` for `c^3 < 64` immediately cuts
`kappa`. (b) The `lambda = 0` side has never been touched; the natural first
swing is the fifth-order Taylor upper bound `sin x < x - x^3/6 + x^5/120`, which
combined with a `π ≥ 3` lower bound would deliver a positive `lambda`. Neither
of these interferes with V1's chain, so each is a clean single-factor sprint.

---

## sprint_002 — lower_taylor5            [READY_FOR_EVALUATION]

Goal: open the `lambda` side. Prove the fifth-order Taylor upper bound
`sin x < x - x^3/6 + x^5/120` for `x > 0`, combine with `π > 3` (derived from
`polygonLower_lt_pi 1` and a nested-radical estimate), and land `lambda = 1/4`.
`kappa` stays at `2/3`. Score `2/3 → 5/12` (a `1/4` improvement).

Tried: followed the sprint contract directly.

* **`sin_lt_taylor5` via nested `strictMonoOn_of_deriv_pos`.** Two functions,
  outer `g t := t - t^3/6 + t^5/120 - sin t` and inner `h t := 1 - t^2/2 +
  t^4/24 - cos t`. `g 0 = h 0 = 0`, `g' = h`, and `h' = sin - (t - t^3/6)`
  which is positive by V1's `sin_gt_sub_cube_div_six`. Restated
  `sin_gt_sub_cube_div_six` verbatim from V1 in `Candidates/V2/Taylor.lean`
  (candidates never import each other). Derivative assembly is the V1
  template scaled up: `hasDerivAt_pow n`, `.div_const`, `.sub`, `.add`,
  `.deriv`, then `ring` to normalize the closed form. `fun_prop` closes
  every `ContinuousOn` side goal.

* **`three_lt_pi` = `3 < π` via depth-1 polygon.** `polygonLower 1 =
  4 · √(2 - √2)` (using `Real.sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 =
  √2`, which exists in Mathlib and is `simp`-tagged). Then `√2 < 23/16` from
  `sqrt_lt_sqrt` + `sqrt_sq` since `(23/16)^2 = 529/256 > 2`; so `2 - √2 >
  9/16`; so `√(2 - √2) > 3/4` by the same pattern; so `4 · √(2 - √2) > 3`.
  Chain closes via `polygonLower_lt_pi 1`. `norm_num` after `unfold
  polygonLower; rw [Real.sqrtTwoAddSeries_one]` collapses the `2^(1+1) = 4`.

* **Rescaling.** At `x = π/2^(n+2)`, `sin_lt_taylor5 hx` scaled by `2^(n+2)`
  gives `polygonLower n < π - π^3/(96·4^n) + π^5/(30720·16^n)`, closed by
  `rw [hpow, h16n, h4n]; field_simp; ring` with the V1 identities plus
  `h16n : 16^n = 4^n · 4^n = by rw [← mul_pow]; norm_num`. The final
  reduction to `polygonLower n + (1/4)/4^n < π` cross-multiplies by
  `30720·16^n > 0` (identity in `h_diff_id`), reducing the required
  nonnegativity to `π^5 + 7680·4^n ≤ 320·π^3·4^n`, which lifts from `4^n ≥ 1`
  and the pointwise `π^5 + 7680 ≤ 320·π^3` (from `π > 3` giving `π^3 > 27`
  and `π ≤ 4` giving `π^2 ≤ 16`, so `π^5 ≤ 16·π^3` and `320·π^3 - π^5 ≥
  304·π^3 > 304·27 = 8208 > 7680`). `nlinarith` with the product hint
  `(320π^3 - 7680)·(4^n - 1) ≥ 0` handled the lifting step in one shot.

Outcome: `Candidates/V2.lean` + `Candidates/V2/Taylor.lean` build, evaluator
passes all twelve stages, axiom closure is `{propext, Classical.choice,
Quot.sound}`, score `5/12` (strict improvement over V1's `2/3`). Interval
width at depth 10 shrinks from `6.36e-07` to `3.97e-07`.

Lint notes worth remembering (they bit me during this sprint too):
`hzero_h`/`hzero_g` prefer `change` over `show` when unfolding the `set`-bound
lambda; the `linter.style.show` warning is otherwise loud. `Real.cos_zero`
and `Real.sin_zero` are still `simp` lemmas but need to appear on the `rw`
line before `norm_num` when the goal has an explicit `Real.cos 0` or
`Real.sin 0` (positive powers of 0 fall to `norm_num` after).

Next: two architectural angles remain equally attractive. (a) The upper side's
`π ≤ 4` → `π^3 ≤ 64` factor is still V0-vintage; replacing `π ≤ 4` with any
tighter certified `π < c` (an independent Niven-style `π < 22/7` bound, or a
circumscribed polygon upper) immediately cuts `kappa` below `2/3`. (b) On the
lower side, the same `sin`-Taylor family goes further: `sin x > x - x^3/6 +
x^5/120 - x^7/5040`, combined with the `π > 3` piece already in V2, is a
straightforward architectural rung with the same nested-mono template used
here (V2's argument stops at depth 2; a 7th-order bound is depth 3). The
one-session bound holds either way; do not bundle.

---

## sprint_003 — upper_tan_pi_over_eight            [READY_FOR_EVALUATION]

Goal: attack the last V0-vintage quantitative piece in the upper conjunct —
`Real.pi_le_four ⇒ π^3 ≤ 64` — by introducing a strictly tighter upper bound
`π < 7/2` from `Real.lt_tan` at `π/8`. Drives `kappa` from `2/3 = 320/768` down
to `343/768`. `lambda` stays at `1/4`. Score `5/12 → 151/768` (a `169/768 ≈
0.220` strict drop).

Tried: took Route 2 from the contract (bound the `sin/cos` ratio directly,
never introducing `tan(π/8) = √2 − 1` in closed form). The proof lives in
`Candidates/V3/Tan.lean` and is ~85 lines.

* **The core lemma `pi_lt_seven_halves`.**
  `Real.lt_tan (h1 : 0 < π/8) (h2 : π/8 < π/2) : π/8 < tan(π/8)`. It suffices
  to show `tan(π/8) < 7/16` — then `π/8 < 7/16` gives `π < 7/2` by `linarith`.
  Rewriting `tan = sin/cos` with `cos(π/8) > 0` reduces the target to
  `16 sin(π/8) < 7 cos(π/8)`. Both sides positive, so equivalent (via
  `sq_lt_sq₀ ha hb : a^2 < b^2 ↔ a < b` for `a, b ≥ 0`) to
  `(16 sin(π/8))^2 < (7 cos(π/8))^2`, i.e. `256 sin²(π/8) < 49 cos²(π/8)`.
  Using the Mathlib closed forms `sin(π/8) = √(2-√2)/2` and
  `cos(π/8) = √(2+√2)/2` (both `@[simp]` in `Trigonometric/Basic.lean` — good
  to know they survive), squaring collapses to `256·(2-√2)/4 < 49·(2+√2)/4`,
  i.e. `414 < 305·√2`. Closed by `nlinarith` given `√2 > 7/5` as a hint,
  since `305·7/5 = 427 > 414`.

  The `√2 > 7/5` step is a two-liner via `sq_lt_sq₀` with `Real.sq_sqrt`.
  Analogous `√2 ≤ 2` (needed to keep `2 - √2 ≥ 0` in scope so `Real.sq_sqrt`
  applies) via `Real.sqrt_le_sqrt` and `Real.sqrt_sq` on 4 = 2².

* **The rescaling arithmetic.** Copied V2's upper-conjunct chain verbatim
  down to `π - polygonLower n < π^3/(96·4^n)`; then swapped
  `π^3 ≤ 64` for `π^3 ≤ 343/8` via `pow_le_pow_left₀ Real.pi_pos.le
  pi_lt_seven_halves.le 3` + `norm_num`; then the constant rearrangement
  `(343/8) / (96·4^n) = (343/768) / 4^n` needed `rw [div_div, div_div]; congr
  1; ring` — plain `field_simp` alone leaves `768 = 8·96` unclosed, and
  `field_simp; ring` was noisy; the explicit `div_div` route was cleanest.

* **The lower conjunct + `three_lt_pi` + `Taylor` helpers.** Restated
  verbatim from V2 in `Candidates/V3/Taylor.lean` and inline in V3.lean.
  Candidates are self-contained, so V3 does not import V2. Verbatim copy
  builds without modification.

Outcome: `Candidates/V3.lean` + `Candidates/V3/Tan.lean` + `Candidates/V3/Taylor.lean`
build; evaluator passes all twelve stages; axiom closure is
`{propext, Classical.choice, Quot.sound}`; score `151/768 ≈ 0.1966` (strict
improvement over V2's `5/12 ≈ 0.4167`). Interval width at depth 10 shrinks
from `3.97e-07` to `1.875e-07` — roughly halved.

Env notes worth remembering (added by this sprint):

- `Real.sin_pi_div_eight` and `Real.cos_pi_div_eight` are both `@[simp]` in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`. `sin_pi_div_sixteen`
  and `cos_pi_div_sixteen` are also there (relevant if a future sprint wants
  a tighter tan-based bound at `π/16`).
- `Real.tan_two_mul` lives in `Trigonometric.Arctan`, `Real.tan_pi_div_four`
  in `Trigonometric.Basic`. Both were candidates for Route 1a; not used
  because Route 2 (via closed-form `sin/cos` at `π/8`) is shorter.
- `sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 < b^2 ↔ a < b` is the clean
  un-squaring lemma when both sides are non-negative — much cleaner than
  `abs_lt_of_sq_lt_sq`. Lives in
  `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`.
- `Real.lt_tan` is available directly from `Trigonometric.Bounds`, which is
  already re-exported through `Proof.Main` (the trusted surface imports it
  transitively via `PolygonCore.Polygon`). No new import needed in V3.
- Contract's suggestion of `field_simp` to close constant identities like
  `(343/8) / (96·M) = (343/768) / M` can leave residual numerical goals; a
  `rw [div_div, div_div]; congr 1; ring` chain is more predictable.

Next: two clean architectural angles remain, each roughly a `2×` reduction
in score.

(a) **Lower side, tan symmetric.** The `three_lt_pi` piece in the lower
    conjunct is still crude (only `π > 3`). The same tan machinery gives
    tighter symmetric lower bounds: e.g. `Real.lt_tan` at `π/12` or
    `π/16`, combined with a `√3` or `√(2+√2)` rational bound, would push
    `three_lt_pi` up to something like `π > 3.05` or `π > 3.1`. That
    directly raises `lambda` — probably from `1/4` toward `3/8` or so —
    without touching V3's upper conjunct. Structurally symmetric to this
    sprint (same `Real.lt_tan` template).

(b) **Upper side, deeper polygon.** Instead of `π/8`, use `Real.lt_tan` at
    `π/16` (or `π/32`) with a `circumscribed`-polygon interpretation:
    `π < N · tan(π/N)` for larger `N`. `tan(π/16) = √(4 + 2√2) - √2 - 1` in
    closed form; the numerical bound approaches `π` more tightly. Same
    `√2 < 23/16`-plus-nested-radical arithmetic already in `three_lt_pi`.
    Would cut `kappa` further, probably below `1/3`, without touching
    the lower conjunct.

The single-file bound rules out bundling; pick one direction per sprint.
Do not attempt both in one V4.

---

## sprint_004 — lower_polygon_depth2            [READY_FOR_EVALUATION]

Goal: attack the last V2-vintage quantitative piece in the lower conjunct —
`three_lt_pi ⇒ π³ > 27` — by introducing a strictly tighter lower bound
`π > 31/10` from the depth-2 inscribed polygon
`polygonLower 2 = 8·√(2 - √(2 + √2))` and a triple-nested √2 chain. Drives
`lambda` from `1/4 = 192/768` up to `9/32 = 216/768`. `kappa` stays at
`343/768`. Score `151/768 → 127/768` (a `24/768 = 1/32 ≈ 0.0313` strict drop).

Structurally symmetric to sprint 003: that sprint used the depth-1
circumscribed polygon (`Real.lt_tan` at `π/8`) for an upper bound; this sprint
uses the depth-2 inscribed polygon (`polygonLower_lt_pi 2`) for the mirror
lower bound.

Tried: took Route 1 from the contract directly (search-first Route 0 unlikely
to hit — the blocked-name list already excludes the standard `pi_gt_…`
families).

* **`polygonLower 2 = 8·√(2 - √(2 + √2))` unfold.** Handy shortcut:
  `Real.sqrtTwoAddSeries_two` is already in
  `Trigonometric/Basic.lean` (right next to `_one`) and gives
  `sqrtTwoAddSeries 0 2 = √(2 + √2)` directly. Cleaner than
  `_succ`-then-`_one`. So `unfold polygonLower; rw [Real.sqrtTwoAddSeries_two];
  norm_num` closes the identity in three lines.

* **Rational bounds via `sqrt_lt_sqrt` + `sqrt_sq`, one layer per step.**
  - `√2 < 14143/10000` — same 5-line pattern as sprint 002/003
    (`sqrt_lt_sqrt (by norm_num) (by norm_num)` then `sqrt_sq`). `norm_num`
    closes `(14143/10000)² > 2`, i.e. `14143² = 200_024_449 > 200_000_000`.
  - `√(2+√2) < 18479/10000` — one layer deeper. First get
    `2 + √2 < (18479/10000)²` by `nlinarith [hsqrt2_lt]` (integer identity:
    `18479² = 341_473_441 > 341_430_000 = 34143·10⁴`), then `sqrt_lt_sqrt`
    + `sqrt_sq`.
  - `√(2 - √(2+√2)) > 31/80` — mirror direction. Radicand positivity from
    `√(2+√2) < 18479/10000 < 2`. `(31/80)² < 2 - √(2+√2)` by `nlinarith
    [h_outer_lt]` (`(31/80)² = 961/6400 = 15015.625/10⁵ < 15210/10⁵`).
    `sqrt_lt_sqrt` then `sqrt_sq` (upward).

* **Scale by 8.** `mul_lt_mul_of_pos_left` after rewriting
  `31/10 = 8 · (31/80)`. Chain closes with `polygonLower_lt_pi 2 + linarith`.

* **Rescaling arithmetic.** V3's lower-conjunct chain verbatim with three
  constant substitutions: `three_lt_pi → pi_gt_thirty_one_over_ten`,
  `7680 → 8640` (from `30720·(9/32)`), `27 → 29791/1000` (from `(31/10)³`).
  `hcore` becomes `304·(29791/1000) = 9_056_464/1000 = 9056.464 > 8640` — a
  ~5% slack, same shape as V3's `304·27 = 8208 > 7680` (6% slack). Same
  `nlinarith [hcore, h_prod]` + `field_simp; ring` closure that V3 uses.

* **Upper conjunct copied verbatim from V3.** No change to
  `pi_lt_seven_halves`, `sin_gt_sub_cube_div_six`, or the `π³ ≤ 343/8` chain.
  Bundling with a `pi_lt_seven_halves` tighten was explicitly ruled out by
  the contract's one-session bound.

Outcome: `Candidates/V4.lean` + `V4/Polygon.lean` + `V4/Tan.lean` +
`V4/Taylor.lean` all build; evaluator passes all twelve stages; axiom closure
is `{propext, Classical.choice, Quot.sound}`; score `127/768 ≈ 0.1654`
(strict improvement over V3's `151/768 ≈ 0.1966`). Interval width at depth
10 shrinks from `1.875 × 10⁻⁷` to `1.577 × 10⁻⁷`.

Env notes worth remembering (added by this sprint):

- `Real.sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = √(2 + √2)` is
  available in the same `Trigonometric/Basic.lean` block as `_one`, and
  saves a `sqrtTwoAddSeries_succ` unfold step at depth 2. Same shortcut
  should exist for depth 3 (`sqrtTwoAddSeries 0 3 = √(2 + √(2 + √2))`) via
  `_succ` + `_two`, if a future sprint wants a depth-3 argument.
- `sqrt_lt_sqrt` is not gcongr-tagged, so use it explicitly with the
  radicand-nonneg guard as first argument. `Real.sqrt_lt_sqrt hnn hbound`.
- `nlinarith` handles the "squared rational vs. squared rational" comparisons
  at each nested-radical layer without needing the numeric identity pre-baked
  as a separate `have`; the coefficients here (`10000`, `18479`, `80`) are
  well inside its comfort zone.
- Radicand positivity for the outermost sqrt (`2 - √(2+√2) ≥ 0`) is cleanest
  via the rational upper bound `√(2+√2) < 18479/10000 < 2` we already need
  for the tightness — no need to invoke `sqrtTwoAddSeries_lt_two`.

Next: three architectural angles remain roughly ordered by score impact.

(a) **Upper side, deeper polygon: tan at π/16.** The `pi_lt_seven_halves`
    factor (V3-vintage) is now the loosest single term in the upper chain.
    Same `Real.lt_tan` template as sprint 003, one polygon depth deeper.
    `sin(π/16) = √(2 - √(2 + √2))/2` and `cos(π/16) = √(2 + √(2 + √2))/2`
    both live in `Trigonometric/Basic.lean` (`sin_pi_div_sixteen`,
    `cos_pi_div_sixteen`, confirmed present in sprint 003 env notes). The
    triple-nested √2 arithmetic from this sprint's `V4/Polygon.lean` is
    directly reusable — bound `√(2 + √(2 + √2)) < ...` and `√(2 - √(2 + √2))
    > ...` via similar chains. Expected `kappa` drop from `343/768 ≈ 0.447`
    toward `~0.35` or below. Structurally symmetric to this sprint but on
    the upper side.

(b) **Lower side, 7th-order Taylor.** Extend `sin_lt_taylor5` to
    `sin x < x - x³/6 + x⁵/120 - x⁷/5040`. Combined with V4's
    `π > 31/10`, would let `lambda` rise further — but the improvement
    scales as `1/64^n` and is most binding at `n = 0`. Expected `lambda`
    gain: `0.28125` → `~0.31` or so. Precision-flavored, not architectural.

(c) **Combined `π² ≤ 49/4` bump on V4's lower conjunct.** The `hπ_sq_le :
    π² ≤ 16` step still uses `π ≤ 4` (V0-vintage). Swapping for
    `π ≤ 7/2 ⇒ π² ≤ 49/4` tightens `π⁵ ≤ (49/4)·π³` instead of
    `16·π³`, which relaxes the `304·π³` calculation to `((320 - 49/4))·π³
    = (1231/4)·π³`. Slightly less headroom needed. Would enable `lambda`
    slightly above `9/32` without any depth increase — a pure-precision
    followup for a later sprint.

Directive-1 flags (a) as architectural (new polygon depth + first use of
`sin_pi_div_sixteen`/`cos_pi_div_sixteen`); (b) and (c) are
precision-flavored. Do not bundle.

---

## sprint_005 — upper_tan_pi_over_sixteen            [READY_FOR_EVALUATION]

Goal: attack V4's last V3-vintage quantitative piece in the upper conjunct
— `pi_lt_seven_halves ⇒ π³ ≤ 343/8` — by introducing a strictly tighter upper
bound `π < 16/5` from `Real.lt_tan` at the depth-2 circumscribed-polygon
vertex angle `π/16`. Drives `kappa` from `343/768 ≈ 0.4466` down to
`128/375 ≈ 0.3413`. `lambda` stays at `9/32`. Score `127/768 → 721/12000`
(a `≈ 0.1053` strict drop, roughly 63% relative — the largest single-sprint
score reduction since sprint 003).

Structurally symmetric to sprint 004: that sprint used the depth-2
inscribed polygon (`polygonLower_lt_pi 2`) for a lower bound; this sprint
uses the depth-2 circumscribed polygon (`Real.lt_tan` at `π/16`) for the
mirror upper bound.

Tried: took Route 2 shape from the contract, mirroring V4/Tan.lean at one
polygon depth deeper.

* **`pi_lt_sixteen_fifths` via the sin/cos ratio at π/16.** `Real.lt_tan`
  at `π/16` gives `π/16 < tan(π/16)`. Reduce target `tan(π/16) < 1/5` to
  `5·sin(π/16) < cos(π/16)`, then square. Using the closed forms
  `sin(π/16) = √(2 - √(2+√2))/2` and `cos(π/16) = √(2 + √(2+√2))/2`
  (both `@[simp]` in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
  as sprint 003 env notes predicted, resolved without any name drift),
  squaring collapses to `25·(2 − s)/4 < (2 + s)/4` where `s = √(2 + √2)`,
  i.e. `48 < 26·s`, i.e. `s > 24/13`. Chain closes via `sqrt_two_gt_238_over_169`
  and `nlinarith` on `(24/13)² = 576/169 = 2 + 238/169 < 2 + √2`.

* **New lemma object: `sqrt_two_add_sqrt_two_gt_24_over_13`.** V4/Polygon.lean
  introduced only the **upper** bound `√(2+√2) < 18479/10000`. This sprint
  adds the mirror **lower** bound `√(2+√2) > 24/13`, using the sprint-004
  template inverted: `nlinarith` on the square, `Real.sqrt_lt_sqrt` +
  `Real.sqrt_sq` to bring both sides under sqrt. Numerical slack ≈ 0.0016
  — comfortable but tight enough that a coarser `√2 > 7/5` (sprint 003's
  witness) does not close it; the sharper `√2 > 238/169` is required.

* **Auxiliary `sqrt_two_add_sqrt_two_lt_two`.** Needed to keep
  `2 - √(2+√2) ≥ 0` in scope so `Real.sq_sqrt` applies to `sin²(π/16)`.
  Proved inline via `√2 < 2`; the contract suggested reusing V4's
  `18479/10000` upper bound but restating the trivial strict version was
  shorter (~15 lines) than mirroring the sharper chain.

* **Rescaling arithmetic — two constant substitutions on V4's upper chain.**
  V4's `π^3 ≤ 343/8` becomes `π^3 ≤ 4096/125` via
  `pow_le_pow_left₀ Real.pi_pos.le pi_lt_sixteen_fifths.le 3` + `norm_num`,
  handling `(16/5)^3 = 4096/125` cleanly. The constant rearrangement
  `(4096/125) / (96·4^n) = (128/375) / 4^n` **required a different
  pattern than V3/V4's `rw [div_div, div_div]; congr 1; ring`**: because
  the numerators differ (`4096` vs `128`), `congr 1` splits into an
  impossible `4096 = 128` subgoal. Cross-multiplication identity is
  `4096 · 375 = 128 · 12000 = 1_536_000`. Closed instead with
  `field_simp; ring` (with `4^n ≠ 0` from `positivity`). This is a
  reusable pattern for any future sprint where the numerator-scaling
  changes.

* **Lower conjunct copied verbatim from V4.** No change to
  `pi_gt_thirty_one_over_ten`, `sin_lt_taylor5`, or the `π^5 + 8640·4^n`
  chain. Bundling with a `pi_gt_thirty_one_over_ten` sharpen was explicitly
  ruled out by the one-session bound.

Outcome: `Candidates/V5.lean` + `V5/Tan.lean` + `V5/Taylor.lean` +
`V5/Polygon.lean` all build; evaluator passes all twelve stages; axiom
closure is `{propext, Classical.choice, Quot.sound}`; score
`721/12000 ≈ 0.0601` (strict improvement over V4's `127/768 ≈ 0.1654`).
Interval width at depth 10 shrinks from `1.577 × 10⁻⁷` to `5.729 × 10⁻⁸`,
cut by a factor of ~2.75.

Env notes worth remembering (added by this sprint):

- `Real.sin_pi_div_sixteen` and `Real.cos_pi_div_sixteen` are both `@[simp]`
  in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`, exactly as
  sprint 003 env notes predicted. No name drift.
- The V3/V4 constant-rearrangement pattern `rw [div_div, div_div]; congr 1;
  ring` only works when numerators match after the two `div_div` unfolds.
  When they don't, `field_simp; ring` (with a `4^n ≠ 0` witness from
  `positivity`) is the reliable alternative. Add this substitution to your
  toolkit when the tightening changes a numerator.
- `nlinarith [h_s_gt, Real.sqrt_nonneg _]` closes the squared inequality
  `25·(2 − s)/4 < (2 + s)/4` given `s > 24/13` without further help; slack
  `≈ 0.042` on that goal is well inside nlinarith's comfort zone.
- The `√(2+√2) > 24/13` bound needs `√2 > 238/169` (slack `≈ 0.006` on
  `(238/169)² < 2` and `≈ 0.0016` on `(24/13)² < 2 + √2`). A coarser
  `√2 > 7/5` witness (sprint 003) is **too loose** — it gives only
  `(24/13)² = 576/169 ≈ 3.408` vs `2 + 7/5 = 3.4`, wrong direction. Use
  `238/169` or sharper.

Next: three architectural angles remain, roughly ordered by expected impact.

(a) **Niven's `π < 22/7` via `∫₀¹ x⁴(1-x)⁴/(1+x²) dx > 0`.** Yields a
    marginally better `kappa` (`≈ 0.324` vs current `0.341`), and is
    architecturally a genuinely new chain (Riemann-integral estimate
    instead of trig closed form). Estimated multi-hundred lines of
    integral machinery. Risk of exceeding one session — reserve for after
    a lower-side rung lands.

(b) **Lower side, depth-3 inscribed polygon or 7th-order Taylor.** The
    lower-side ceiling is at `n = 0` where `(π − polygonLower 0)·4^0 =
    π − 2√2 ≈ 0.313`, current `lambda = 9/32 = 0.28125` leaves headroom
    `≤ 0.032`. Depth-3 (`polygonLower_lt_pi 3` with quadruple-nested
    √2 chain) or 7th-order Taylor (`sin x < x - x³/6 + x⁵/120 - x⁷/5040`)
    could raise `lambda` toward `~0.30`. Directive-3 (keep both sides
    moving) also favors a lower-side sprint next after two consecutive
    upper-side landings would break rotation. **Score gain modest
    (`≤ 0.032`), but rotation matters.**

(c) **Combined `π² ≤ 256/25` bump on V4's lower conjunct.** The
    `hπ_sq_le : π² ≤ 16` step still uses `π ≤ 4` (V0-vintage). Swapping
    for `π ≤ 16/5 ⇒ π² ≤ 256/25 = 10.24` (using this sprint's
    `pi_lt_sixteen_fifths`) tightens the `304·π³` computation. Pure
    precision, ~10 lines of change. Reserve for a bundled precision
    sprint.

Directive-3 rotation strongly favors (b) as the next sprint, since we've
now had `upper·3 / lower·2`. If (b) is chosen, the depth-3 nested-radical
chain (`sqrtTwoAddSeries_succ` applied once to `_two`) is architecturally
newer than the 7th-order Taylor extension; prefer depth-3 polygon.
