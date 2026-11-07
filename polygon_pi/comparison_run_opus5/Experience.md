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

## sprint_001 — deficit_monotonicity_lambda            [READY_FOR_EVALUATION]

Goal: lift `lambda` off `0` by proving the scaled deficit
`D n := 4 ^ n * (π - polygonLower n)` is monotone non-decreasing in `n`, so the
lower conjunct is binding only at `n = 0`. Target `lambda ≥ 23/100`.

Tried / what actually worked (everything below is in the shipped files, nothing
was abandoned):

- **The one-variable inequality `sin y * (4 - cos y) ≤ 3 * y` for `y ≥ 0`.**
  Do *not* reach for `strictMonoOn_of_deriv_pos` here. The derivative of
  `φ y := 3 * y - sin y * (4 - cos y)` is `2 * (cos y - 1) ^ 2`, which is an
  exact square and therefore only *non-negative*, vanishing at `y = 0` (and at
  every `2 k π`). The right tool is
  `monotone_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
  (hf' : 0 ≤ f') : Monotone f`
  from `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`. **Confirmed working in
  this Mathlib.** It gives global monotonicity on all of `ℝ` with *no*
  `ContinuousOn`, no `interior`, and no `Convex` side goal — a strictly cheaper
  route than the `Real.lt_tan` pattern whenever the derivative is globally
  non-negative. The `hf' : 0 ≤ f'` argument is a `Pi` order and
  `(fun y => <proof of 0 ≤ f' y>)` is accepted directly; no `Pi.le_def` rewrite
  needed. Also in the same file and confirmed present:
  `monotoneOn_of_deriv_nonneg`, `monotoneOn_of_hasDerivWithinAt_nonneg`,
  `strictMonoOn_of_hasDerivWithinAt_pos`, `strictMono_of_hasDerivAt_pos`.
- Assembling the `HasDerivAt`: `(hasDerivAt_id y).const_mul (3 : ℝ)` (needs
  `simpa` to fix the `3 * 1` shape), `Real.hasDerivAt_sin`,
  `(Real.hasDerivAt_cos y).const_sub (4 : ℝ)` (again `simpa`, to turn `-(-sin y)`
  into `sin y`), then `hlin.sub (hsin.mul hcos)`. State the derivative in the
  *unsimplified* product-rule form `3 - (cos y * (4 - cos y) + sin y * sin y)`;
  then `exact` closes it with no `simp` at all. Proving that form equals
  `2 * (cos y - 1) ^ 2` is `nlinarith [Real.sin_sq_add_cos_sq y]` in one line.
- **The one-step deficit inequality.** With `y := π / 2 ^ (n+3)`:
  `polygonLower (n+1) = 2 ^ (n+3) * sin y` is `rw [polygonLower_eq_mul_sin, hy]`
  and then *nothing* — `n + 1 + 2` and `n + 3` are definitionally equal, so the
  `rw` closes the goal by `rfl`. Do not add a `norm_num`; it errors with "No
  goals to be solved". `π / 2 ^ (n+2) = 2 * y` is
  `rw [hy, show ((2:ℝ) ^ (n+3)) = 2 * 2 ^ (n+2) by ring]; field_simp`.
  `Real.sin_two_mul` then gives `polygonLower n = 2 ^ (n+3) * (sin y * cos y)`
  with a plain `ring` (ring normalises `2 ^ (n+3)` and `2 ^ (n+2)` against each
  other unaided). Final rearrangement: `mul_le_mul_of_nonneg_left` twice, then
  `rw [..., show ((4:ℝ) ^ (n+1)) = 4 * 4 ^ n by ring]` and one `nlinarith`.
- **The uniform bridge** `π - polygonLower 0 ≤ 4 ^ n * (π - polygonLower n)` is a
  three-line induction: `| zero => simp`, `| succ k ih => exact ih.trans
  (deficit_step k)`.
- **Rational certification of the nested radical.** The staged recipe in the
  contract is right and each stage is a single `nlinarith` with exactly three
  hints — `Real.sq_sqrt <nonneg>`, `Real.sqrt_nonneg <arg>`, and the previously
  proved bound. No `Real.le_sqrt` / `Real.lt_sqrt` needed at all; the sign
  hypotheses plus `nlinarith` do the whole job, which sidesteps the name drift in
  that family. Chain used, all with 4-decimal rationals:
  `√2 < 1.4143`, `√(2 + √2) < 1.8478`, `√(2 - √(2 + √2)) > 0.3901`.
  Do *not* hand the whole nested expression to one `nlinarith`.
- `polygonLower 0 = 2 * √2` is `simp [polygonLower]` (nothing else needed);
  `polygonLower 2 = 8 * √(2 + √2 ... )` is
  `rw [polygonLower, Real.sqrtTwoAddSeries_two]; norm_num`.
  `Real.sqrtTwoAddSeries_one` / `_two` both exist and are usable by name.
- `div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a` **resolves** and is the
  right form here, because the deficit bound is stated as `4 ^ n * (…)` with the
  power on the *left*. `div_lt_iff₀` (unprimed) also resolves but puts the
  multiplication the other way round and then `linarith` cannot match the atoms.

Outcome: **success, first build attempt for both files.** `Candidates/V1.lean`
ships `lambda = 29/100` (the contract's optional stretch, not just the required
`23/100`) and `kappa = 1`, score `71/100` against the parent's `1`. Evaluator
pre-check with `--no-log`: all stages PASS, axiom closure exactly
`{propext, Classical.choice, Quot.sound}`, `strict_improvement=True`.

Structural consequence worth carrying forward: **the lower side is now
analytically closed.** Monotonicity makes the binding constraint `n = 0` and it
is attained, so the exact ceiling for `lambda` is
`π - polygonLower 0 = π - 2√2 = 0.31316…`, forever. Any future lower-side sprint
is purely "prove a sharper rational lower bound for `π`", i.e. certify
`polygonLower d` from below for a larger `d`, and nothing else. The ladder of
what each depth buys, for planning:

| depth `d` used in `polygonLower_lt_pi d` | best `lambda` |
|---|---|
| 1 | `0.2330…` |
| 2 | `0.2930…`  ← shipped (`29/100`) |
| 3 | `0.3081…` |
| 4 | `0.3117…` |
| ∞ | `0.31316…` (hard ceiling) |

Each extra depth is one more `nlinarith` stage of the same staged shape, plus
more decimal digits in the rationals (the error in the inner radical is
amplified by the outer `√(2 - ·)`, so budget ~2 extra digits per level).
Diminishing returns after `d = 3`.

Next: `kappa`, per the contract's own note. The two unexamined factors in the
upper chain are `Real.sin_gt_sub_cube` (gives `x - x ^ 3 / 4` where
`x - x ^ 3 / 6` is true — worth a factor `1.5`) and `Real.pi_le_four` (worth a
factor `≈ 2.06`). The `monotone_of_hasDerivAt_nonneg` idiom recorded above is
exactly what the `sin x < x - x ^ 3 / 6 + x ^ 5 / 120` ladder needs, and it is
cheaper than the `strictMonoOn_of_deriv_pos` route the earlier notes point at —
start there. A rational upper bound on `π` can be obtained in candidate space
from `polygonLower` at depth `d` plus the *upper* companion of the deficit
argument (`4 ^ n * (π - polygonLower n) < kappa`), i.e. from the same
one-variable machinery run in the other direction.

---

## sprint_002 — cubic_deficit_pi_bootstrap            [READY_FOR_EVALUATION]

Goal: replace the entire upper chain — global cubic `x - sin x ≤ x ^ 3 / 6`
(no domain hypothesis) giving the uniform `π - polygonLower n ≤ π ^ 3 / (96·4 ^ n)`,
then bootstrap the resulting depth-2 bound against itself to sharpen `π` and
close `kappa`. Required `kappa ≤ 2/3`, target `33/100`, stretch `3231/10000`.

Outcome: **success, both files built on the second attempt** (one lemma failed
first time, see below). `Candidates/V2.lean` ships `lambda = 29/100` and
`kappa = 3229947/10000000`, score `329947/10000000 = 0.0329947` — past the
stretch bar (`0.0331`), against the parent's `0.71`. Evaluator `--no-log`: all
stages PASS, axiom closure exactly `{propext, Classical.choice, Quot.sound}`,
`strict_improvement=True`. Five bootstrap rounds used (the rounded iteration
reaches its fixed point at round 5; rounds 6+ are identical, so five is exactly
the right number).

### What worked, in the order it was written

- **The global cubic.** `ψ t := t ^ 3 / 6 - t + sin t`. State the derivative in
  the raw combinator shape `3 * x ^ 2 / 6 - 1 + cos x` — *not* `x ^ 2 / 2 - …` —
  and then

  ```lean
  have hpow : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  exact ((hpow.div_const 6).sub (hasDerivAt_id' (x := x))).add (Real.hasDerivAt_sin x)
  ```

  closes it with no `simp`. The one `simpa` is needed only to turn
  `hasDerivAt_pow`'s `(↑3 : ℝ) * x ^ (3 - 1)` into `3 * x ^ 2` — the `Nat.cast 3`
  vs `OfNat 3` mismatch is real and `exact` will not bridge it, so do not skip
  that step. **`hasDerivAt_id' : HasDerivAt (fun x => x) 1 x` resolves** and is
  the right one here (`hasDerivAt_id` gives `HasDerivAt id 1 x`, whose `fun t =>
  t ^ 3 / 6 - id t` shape then has to be unfolded).
- `Real.one_sub_sq_div_two_lt_cos (hx : x ≠ 0) : 1 - x ^ 2 / 2 < cos x` is
  present and is all the derivative sign needs:
  `rcases eq_or_ne x 0 with rfl | hx`, `norm_num` on the `rfl` branch, plain
  **`linarith`** (not `nlinarith`) on the other — `3 * x ^ 2 / 6` and `x ^ 2 / 2`
  are the same linear multiple of the atom `x ^ 2`, so linarith sees it. The
  `Real.sin_lt`-based fallback route in the contract was not needed.
- `monotone_of_hasDerivAt_nonneg hasDerivAt_psi fun x => psiDeriv_nonneg x`
  again worked with zero side goals, as sprint_001 recorded. Extracting
  `x - sin x ≤ x ^ 3 / 6` from `psi_monotone hx` is
  `simp only [Real.sin_zero] at h; norm_num at h; linarith`.
- **The `n` cancellation.** Exactly the shape sprint_001 recorded, and it went
  through unmodified. Multiply the cubic at `x = π / 2 ^ (n+2)` by `2 ^ (n+2)`
  with `mul_le_mul_of_nonneg_left`, then rewrite both sides:
  `hxN : 2 ^ (n+2) * (π / 2 ^ (n+2)) = π` by `field_simp`, LHS by
  `rw [polygonLower_eq_mul_sin, mul_sub, hxN]` (nothing after — it closes by
  `rfl`), RHS by `rw [hpow, h4n]; field_simp; ring` with the recorded
  `hpow : (2:ℝ) ^ (n+2) = 4 * 2 ^ n` and `h4n : (4:ℝ) ^ n = 2 ^ n * 2 ^ n`.
  Then `rw [hL, hR] at hmul; exact hmul`. No `ring_nf`, no case analysis on `n`.
- **The bootstrap.** Two lemmas, deliberately separate so the ordering is
  visible: `deficit_le` (symbolic `π ^ 3`, no numeric input at all) and
  `pi_le_bootstrap_step (c : ℝ) (hc : Real.pi ≤ c) : Real.pi ≤ 31214464/10000000
  + c ^ 3 / 1536`. Inside the step, `norm_num at h0` *does* normalise
  `deficit_le 2`'s `π ^ 3 / (96 * 4 ^ 2)` to the `1536` form directly — no
  `rw [show …]` needed. `pow_le_pow_left₀ Real.pi_pos.le hc 3` supplies
  `π ^ 3 ≤ c ^ 3` and one `linarith` finishes.
- **Each round is three lines**: `have h := pi_le_bootstrap_step _ prev;
  norm_num at h; linarith`. `norm_num` cubes the 8-digit numerator (21-digit
  intermediates) without complaint. Rounds, each rounded up to 7 decimals:
  `4 → 3.1631131 → 3.1420505 → 3.1416417 → 3.1416338 → 3.1416336 (fixed point)`.
- **Final numeric close**: `pi_cube_div_lt : π ^ 3 / 96 < 3229947/10000000` via
  `pow_le_pow_left₀` on `pi_le_round_five`, then `norm_num at h3 ⊢; linarith`.
  In the contract proof, avoid dividing: prove
  `(π - polygonLower n) * 4 ^ n ≤ π ^ 3 / 96` by a two-step `calc`
  (`mul_le_mul_of_nonneg_right (deficit_le n) h4n.le`, then `field_simp`), and
  convert with **`lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b`**, which
  resolves in this Mathlib. Strictness comes entirely from the rational `kappa`
  sitting above the certified `π ^ 3 / 96`; the Taylor inequality stays `≤`.

### Lemma-name and tactic drift hit this sprint

- `hasDerivAt_id'` — resolves; use it in preference to `hasDerivAt_id` when the
  function is written `fun t => t` rather than `id`.
- `lt_div_iff₀` — resolves (companion of the `div_lt_iff₀'` sprint_001 found).
- `pow_le_pow_left₀`, `mul_le_mul_of_nonneg_left/right`, `Real.sq_sqrt`,
  `Real.sqrt_nonneg`, `Real.sqrtTwoAddSeries_two`, `Real.pi_le_four`,
  `Real.one_sub_sq_div_two_lt_cos`, `monotone_of_hasDerivAt_nonneg` — all fine.
- **The one genuine failure.** `√(2 + √2) < 2` handed to `nlinarith` with the
  four "obvious" hints (`sq_sqrt` and `sqrt_nonneg` for both radicals) fails —
  it needs *two* independent products (`t ≥ 2` squared, then `√2 ≥ 2` squared)
  and does not find the pair. Splitting off `sqrt_two_lt_two : √2 < 2` as its
  own one-line `nlinarith` and passing it as a hint makes the outer call a
  single product and it succeeds immediately. General rule, consistent with
  sprint_001's staged-radical note: **one `nlinarith` per radical level, and one
  multiplication per `nlinarith`.**

### Direction of the radical certification — both families now exist

`V2` needs both. They are in different files to avoid a namespace clash (both
files open the same namespace, so a name may only be defined once):

- `Candidates/V2/CubicDeficit.lean` — the *new* direction, for the **upper**
  bound on `polygonLower 2`: `sqrt_two_gt` (`√2 > 1.4142135`),
  `sqrt_two_add_sqrt_two_gt` (`> 1.8477590`), `sqrt_two_sub_lt`
  (`√(2 - √(2+√2)) < 0.3901808`), plus `sqrt_two_lt_two` and
  `sqrt_two_add_sqrt_two_lt_two` (nonnegativity only), and
  `polygonLower_two_eq` / `polygonLower_two_lt`.
- `Candidates/V2.lean` — `V1`'s original direction, for the **lower** conjunct:
  `sqrt_two_lt`, `sqrt_two_add_sqrt_two_lt`, `sqrt_two_sub_gt`.

The 7-digit inequalities are tight (margins `1.8e-7` and `6e-8` at the second
and third stages) but `nlinarith` on exact rationals does not care.

### Where the upper side now stands, and what is left

`Scratch/bootstrap_iteration_v2.py` reproduces the iteration in exact rational
arithmetic. The important structural fact for the next planner:

- The bootstrap's fixed point is `0.3229947`; the true `π ^ 3 / 96` is
  `0.3229820`. The `1.25e-5` gap is **not** slack in `p₂ = 3.1214464` (that is
  only `1.25e-6` off the true `polygonLower 2`, and its contribution to `kappa`
  is `~4e-7`). It is slack in the *cubic deficit bound itself* at depth 2:
  `π ^ 3 / 1536 = 0.0201862` versus the true deficit `0.0201475`. So
  **certifying `polygonLower 2` to more digits buys essentially nothing**, and
  neither does a sixth bootstrap round.
- The two things that would move it: (a) bootstrap at depth 3 instead of 2
  (deficit slack falls by `4×`, so `kappa → ~0.322985`, worth `~1e-5`), which
  costs one more `nlinarith` radical stage at `~9` digits; (b) the quintic
  `sin x ≥ x - x ^ 3 / 6 + x ^ 5 / 120`... in the useful direction,
  `x - sin x ≤ x ^ 3 / 6 - x ^ 5 / 120 + x ^ 7 / 5040`, which is one more rung of
  the same `monotone_of_hasDerivAt_nonneg` ladder and would lower the *floor*
  `π ^ 3 / 96` itself. Both are worth `< 1.3e-5`.
- Meanwhile the lower side's remaining headroom is `29/100 → π - 2√2 =
  0.3131655`, i.e. `0.0232` — **three orders of magnitude more**. Sprint 003
  should be `lower`, and by sprint_001's ladder it is a depth-3 (`0.3081`) or
  depth-4 (`0.3117`) rational certification with no new analysis: extend the
  staged `nlinarith` chain in `V2.lean` by one or two levels, budgeting ~2 extra
  decimal digits per level, and nothing else changes.

Next: lower side, depth 3 or 4. Hold the quintic and the Richardson
extrapolation until the lower side is within `10 ^ -4` of `π - 2√2`.

---

## sprint_003 — quintic_lower_deficit_bootstrap            [READY_FOR_EVALUATION]

Goal: give the **lower** side its own analytic ingredient — a quintic Taylor
*upper* bound on `sin`, hence a *lower* bound on the polygon deficit — and
bootstrap it, mirroring sprint 002's upper-side bootstrap. Target
`lambda = 313165/1000000`, required floor `lambda ≥ 3125/10000`.

Outcome: **success, every file built on the first attempt.**
`Candidates/V3.lean` ships `lambda = 313165/1000000` and
`kappa = 3229947/10000000` (untouched), score `98297/10000000 = 0.0098297`
against the parent `V2`'s `0.0329947`. Evaluator `--no-log`: all twelve stages
PASS, axiom closure exactly `{propext, Classical.choice, Quot.sound}`,
`strict_improvement=True`. The contract's plan was followed literally and every
constant in it verified in exact rational arithmetic first
(`Scratch/lower_bootstrap_v3.py`); nothing had to be re-derived.

### What worked, in the order it was written

- **`cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24`, globally, with no new calculus.**
  The half-angle route is genuinely cheap and is the recommendation to carry
  forward: *do not* build a second-derivative argument for an even Taylor rung
  when the odd rung below it is already proved. Shape:
  `rcases le_or_gt 12 (t ^ 2)`; the far branch is
  `nlinarith [Real.cos_le_one t, sq_nonneg t]` (the RHS minus `1` is
  `t ^ 2 (t ^ 2 - 12) / 24 ≥ 0`); the near branch substitutes `t = 2 u` and
  squares the cubic sine bound.
- **`obtain ⟨u, rfl⟩ : ∃ u : ℝ, t = 2 * u := ⟨t / 2, by ring⟩`** is much better
  than `set u := t / 2 with hu` for the half-angle substitution: it rewrites `t`
  everywhere at once (goal *and* both hypotheses `0 ≤ t`, `t ^ 2 < 12`), so no
  `rw [hu]` juggling is needed and `Real.cos_two_mul u` matches the goal's
  `Real.cos (2 * u)` syntactically.
- `Real.cos_two_mul (x : ℝ) : cos (2 * x) = 2 * cos x ^ 2 - 1` and
  `Real.sin_sq_add_cos_sq` both resolve; `cos (2u) = 1 - 2 sin u ^ 2` is one
  **`linarith`** from the pair (`cos u ^ 2` is a single atom to linarith, so no
  `nlinarith` is needed).
- The final step of the quartic bound is **plain `linarith`**, not `nlinarith`:
  after `rw [hc]` the goal is linear in the monomials
  `{sin u ^ 2, u ^ 2, u ^ 4, u ^ 6}`, given `hsq : (u - u ^ 3 / 6) ^ 2 ≤ sin u ^ 2`
  (from `pow_le_pow_left₀ hnn hs 2`) and `pow_nonneg hu0 6`. linarith's
  preprocessing expands `(u - u ^ 3 / 6) ^ 2` for you. Same trick for
  `0 ≤ u - u ^ 3 / 6`: hand it `mul_nonneg hu0 (… : 0 ≤ 6 - u ^ 2)` and use
  `linarith`, since `u * (6 - u ^ 2)` normalises to `6u - u ^ 3`.
- **Evenness branch**: `simpa` is unreliable at turning `(-t) ^ 4` into `t ^ 4`
  (`neg_sq` covers the square, the fourth power is not a simp normal form). Use
  explicit `have e2 : (-t) ^ 2 = t ^ 2 := by ring` /
  `have e4 : (-t) ^ 4 = t ^ 4 := by ring` and
  `rw [Real.cos_neg, e2, e4] at h`.
- **The quintic.** `χ t := t - t ^ 3 / 6 + t ^ 5 / 120 - sin t`, derivative in
  raw combinator shape `1 - 3 * x ^ 2 / 6 + 5 * x ^ 4 / 120 - cos x`, built as
  `(((hasDerivAt_id' (x := x)).sub (h3.div_const 6)).add (h5.div_const 120)).sub
  (Real.hasDerivAt_sin x)` with `h3`/`h5` each `simpa using hasDerivAt_pow k x`.
  Non-negativity of the derivative is one **`linarith [cos_le_quartic x]`**.
  `monotone_of_hasDerivAt_nonneg` again, zero side goals. The extraction is
  sprint 002's `simp only [Real.sin_zero]; norm_num at h; linarith`, verbatim.
- **`deficit_ge`** is `deficit_le` line for line with the sign flipped. Keep the
  `4 ^ n * 4 ^ n` form (not `16 ^ n`) and the RHS
  `π - π ^ 3 / (96 * 4 ^ n) + π ^ 5 / (30720 * 4 ^ n * 4 ^ n)`; then
  `rw [hpow, h4n]; field_simp; ring` closes the scaling identity unchanged from
  sprint 002, and the last step is `rw [hL, hR] at hmul; linarith` (`linarith`
  rather than `exact`, because the statement is a rearrangement).
- **The lower bootstrap.** Isolating `pi_pow_five_div_lt : π ^ 5 / 7864320 <
  3891496/100000000000` first is worth it — do it as
  `pow_le_pow_left₀ Real.pi_pos.le pi_le_round_five 5` plus a *separate*
  `have hb : (31416336/10000000 : ℝ) ^ 5 < 7864320 * (3891496/100000000000) := by
  norm_num`, then `linarith`. Running `norm_num at h5 ⊢` instead risks norm_num
  reshaping the goal's division; the two-`have` form is division-free for
  linarith and needs no reshaping at all.
- `pi_ge_bootstrap_step (c) (h0 : 0 ≤ c) (hc : c ≤ π)` needs the extra `0 ≤ c`
  hypothesis that the *upper* step did not (`pow_le_pow_left₀ h0 hc 3` bounds
  `c ^ 3 ≤ π ^ 3` in the lower direction). `norm_num at h0'` normalises
  `deficit_ge 2`'s `96 * 4 ^ 2` **and** `30720 * 4 ^ 2 * 4 ^ 2` to `1536` /
  `7864320` in one go, exactly as sprint 002 found for the cubic.
- Each round is again three lines,
  `have h := pi_ge_bootstrap_step _ (by norm_num) prev; norm_num at h; linarith`.
  Seed is `(polygonLower_two_gt.trans (polygonLower_lt_pi 2)).le`.

### Lemma-name drift hit this sprint

- **`le_or_lt` does not exist in this Mathlib.** Use
  `le_or_gt (a b : α) : a ≤ b ∨ b < a` (`Mathlib/Order/Defs/LinearOrder.lean`).
  `lt_or_ge` is also there. Add this to the drift list alongside
  `div_le_div_iff` and `mul_lt_mul_left`.
- Confirmed working, on top of the earlier lists: `Real.cos_two_mul`,
  `Real.sin_sq_add_cos_sq`, `Real.cos_le_one`, `Real.cos_neg`, `pow_nonneg`,
  `pow_le_pow_left₀` (as `(ha) (hab) (n)`), `mul_nonneg`, `sq_nonneg`,
  `hasDerivAt_id'`, `monotone_of_hasDerivAt_nonneg`.

### Digit budget for the nine-digit radical chain — do not economise

The staged bounds shipped in `V3/QuinticDeficit.lean`, with their exact margins
(from `Scratch/lower_bootstrap_v3.py`):

| stage | bound | margin |
|---|---|---|
| `sqrt_two_lt` | `√2 < 1.414213563` | `A ^ 2 - 2 = 1.77e-9` |
| `sqrt_two_add_sqrt_two_lt` | `√(2 + √2) < 1.847759066` | `B ^ 2 - (2 + A) = 2.99e-9` |
| `sqrt_two_sub_gt` | `√(2 - √(2 + √2)) > 0.390180642` | `(2 - B) - C ^ 2 = 6.08e-10` |

At **eight** digits the third stage is false: the best 8-digit pair gives
`(2 - B₈) - C₈ ^ 2 = -3.2e-8`. The error is amplified by roughly `1/(2C) ≈ 1.28`
per level *and* by the subtraction `2 - B`, which cancels a leading digit — so
budget the digits at the outer radical, not the inner one. Each stage is still a
single `nlinarith` with three hints and the one-multiplication-per-call rule.

### Where the problem now stands

Both sides are now within `1.3e-5` of ceilings that no amount of further work in
this family can cross:

| side | shipped | permanent ceiling / floor | gap |
|---|---|---|---|
| `kappa` | `0.3229947` | `π ^ 3 / 96 = 0.32298205` (exact infimum, not attained) | `1.27e-5` |
| `lambda` | `0.313165` | `π - 2√2 = 0.31316553` (attained at `n = 0`) | `5.3e-7` |

Score `0.0098297` against the theoretical optimum
`π ^ 3 / 96 - (π - 2√2) = 0.00981652`, i.e. `1.32e-5` away, and **essentially
all of the remaining gap is now on the upper side** — the mirror image of the
situation sprint 003 inherited.

The correction to the sprint_002 note is worth repeating, since it is what makes
`kappa` the only live target: `4 ^ n (π - polygonLower n) ↗ π ^ 3 / 96`, so
`π ^ 3 / 96` is the exact infimum of admissible `kappa` **for any Taylor order**.
A septic bound cannot lower it. The only thing that can close the upper gap is a
sharper *numeric* bound on `π ^ 3 / 96`, i.e. a sharper upper bound on `π`, and
`V3` now has both directions of the deficit available to produce one.

Next (upper side, and it is a small, arithmetic-only sprint): the upper
bootstrap's fixed point `3.1416336` is `4.1e-5` above `π`, and that slack is
entirely the depth-2 cubic deficit slack (`π ^ 3 / 1536 = 0.0201862` vs the true
`0.0201475`). Two independent fixes, both now cheap:
(a) reuse `deficit_ge` — `π ≤ polygonLower 2 + π ^ 3 / 1536` can be replaced by
    the *quartic-corrected* upper deficit `x - sin x ≤ x ^ 3 / 6 - x ^ 5 / 120 +
    x ^ 7 / 5040`, one more rung of the same ladder (`sin x ≥ x - x ^ 3 / 6 +
    x ^ 5 / 120 - x ^ 7 / 5040` from `cos t ≥ 1 - t ^ 2 / 2 + t ^ 4 / 24 -
    t ^ 6 / 720`, which the half-angle trick again produces from the quintic);
(b) simply feed `pi_ge_round_five` into the *existing* upper chain: `V3` already
    proves `π ≥ 3.141592597`, and `pi_cube_div_lt` only needs the upper side, so
    the reachable `kappa` is set by how tight `pi_le_round_*` can be made. With
    the depth-2 deficit slack removed by (a), one bootstrap round from
    `3.141592597` would give `π ≤ 3.1415927` and `kappa ≈ 0.3229822`, i.e.
    `1.2e-5` of the remaining `1.32e-5`.
Either lands the score within `~1e-6` of the theoretical optimum, after which
the problem is closed to the precision of the radical digits and further sprints
are pure digit grinds.

---

## sprint_004 — cosine_anchor_pi_inversion            [READY_FOR_EVALUATION]

Goal: stop extracting `π` from the polygon *deficit* at depth 2 and extract it
from the anchor identity `cos (π / 2 ^ (k+1)) = sqrtTwoAddSeries 0 k / 2` at
`k = 5`, inverted through `V3`'s already-proved global quartic
`cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24`. Target `kappa = 3229821/10000000`,
stretch `32298206/100000000`, plus a free widening of `lambda` to
`313165471/1000000000`.

Outcome: **success, every file built on the first attempt, and the stretch
`kappa` landed.** `Candidates/V4.lean` ships `lambda = 313165471/1000000000`
and `kappa = 32298206/100000000`, score `9816589/1000000000 = 0.009816589`
against the parent `V3`'s `0.0098297`. Evaluator `--no-log`: all twelve stages
PASS, axiom closure exactly `{propext, Classical.choice, Quot.sound}`,
`strict_improvement=True`. Every constant in the contract was re-verified in
exact `Fraction` arithmetic against 60-digit values first
(`Scratch/cosine_anchor_v4.py`); **none of the contract's predicted constants
was wrong**, including all five radical margins to two significant figures.

### The structural claim the sprint was testing is confirmed

**On the `+`-nested chain `s_{k+1} = √(2 + s_k)` the certification error
contracts; it does not grow.** Twelve decimal places of `√2` propagate outward
to `s₅` with margin to spare, and the margins *increase* after the first stage
rather than shrinking:

| stage | bound (12 dp) | margin `(2 + a_{k-1}) - a_k ^ 2` |
|---|---|---|
| `s1_gt` | `1.414213562373` | `2.69e-13` |
| `s2_gt` | `1.847759065022` | `2.02e-12` |
| `s3_gt` | `1.961570560806` | `1.23e-12` |
| `s4_gt` | `1.990369453344` | `1.11e-12` |
| `s5_gt` | `1.997590912410` | `9.84e-13` |

Contrast `V3`'s `√(2 - s_n)` chain, which needed +2 decimal digits *per level*
and was false at eight digits after only three stages. The reason is the
subtraction: `2 - s_n` cancels a leading digit, `2 + s_n` does not, and the
outer `√` then contracts by `1/(2 s) ≈ 1/4`. **Rule for future planners: prefer
anchors built from `+`-nesting; depth is essentially free on them, and
expensive on the `2 - ·` side.** Each stage is still a single `nlinarith` with
exactly the three hints `Real.sq_sqrt <nonneg>`, `Real.sqrt_nonneg _`, previous
stage — the one-multiplication-per-call rule from sprint 002 held everywhere.

### What worked, in the order it was written

- **`Real.cos_pi_over_two_pow (n : ℕ) : cos (π / 2 ^ (n + 1)) =
  sqrtTwoAddSeries 0 n / 2`** — present, `@[simp]`, and the index convention is
  exactly this. No fallback through `polygonLower_eq_mul_sin` was needed. At
  `n = 5` it gives `cos (π / 2 ^ (5 + 1)) = s₅ / 2`; get to `cos (π / 64)` with
  a separate `have h64 : Real.pi / 2 ^ (5 + 1) = Real.pi / 64 := by norm_num`
  and `rwa [h64] at h`. Do **not** use `norm_num at h` directly: it would also
  fire the `sqrtTwoAddSeries` simp set on the right-hand side.
- **The outward recursion is definitional and `rfl` proves it at numerals.**
  `lemma series_succ (n : ℕ) : Real.sqrtTwoAddSeries 0 (n + 1) =
  Real.sqrt (2 + Real.sqrtTwoAddSeries 0 n) := rfl` typechecks, and so do the
  five specialisations `series_two := series_succ 1` etc. with literal indices
  (`Nat` literal reduction is not a problem). This matters because
  **`Real.sqrtTwoAddSeries_succ` peels the series from the wrong end**:
  it says `x.sqrtTwoAddSeries (n+1) = (√(2 + x)).sqrtTwoAddSeries n`, which
  moves the base point inward, not the radical outward. That lemma is useless
  for a staged certification; the `rfl` form is what you want.
- `Real.sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 = √2` resolves and is the
  base case; `rw` it and the stage is `V1`'s one-line `√2` `nlinarith`.
  `Real.sqrtTwoAddSeries_zero`, `_nonneg`, `_lt_two` all resolve too, but the
  non-negativity side conditions come more cheaply from the previous stage by
  `linarith` (`0 ≤ 2 + s_k` from `a_k < s_k` with `a_k > 0`).
- **`quartic_antitone`** — the contract's three-line recipe is right and needs
  no tuning. The point is the factorisation
  `(1 - a²/2 + a⁴/24) - (1 - b²/2 + b⁴/24) = (b² - a²)(1/2 - (a² + b²)/24)`;
  prove the two factors non-negative separately with `nlinarith` and then
  `nlinarith [mul_nonneg h1 h2]`, where after ring normalisation the hint *is*
  the goal so there is no search.
- **The inversion is `by_contra` + `push_neg` + four `have`s + one `linarith`,
  with no iteration.** `push_neg` turns `¬ (π ≤ P)` into `P < π` cleanly.
  `linarith` chains `L < cos (π/64) ≤ h(π/64) ≤ h(r) < L` without help: it
  treats `(Real.pi/64) ^ 2` and `^ 4` as the same atoms in `cos_le_quartic
  (Real.pi/64)` and in `quartic_antitone`'s conclusion, because both are stated
  with the literal term `Real.pi / 64`.
- **`cos_le_quartic` used at full strength for the first time.** `V3` proved it
  globally and then only ever consumed it as a derivative sign for the quintic.
  Worth noting as a general habit: a globally-stated Taylor rung is a numeric
  tool as well as a monotonicity tool, and this workspace had one sitting unused
  for a sprint.
- **The final numeric close** is sprint 003's two-`have`, division-free pattern
  and it handled the cube of an eleven-digit numerator (33-digit intermediates)
  without complaint:
  `pow_le_pow_left₀ Real.pi_pos.le pi_le_sharp 3`, then a separate
  `have hb : (31415926848/10000000000 : ℝ) ^ 3 < 96 * (32298206/100000000) := by
  norm_num`, then `linarith`. Likewise `hr`, whose fourth power of a nine-digit
  numerator is a 37-digit rational compared at a margin of `4.33e-12` — exact
  rational `norm_num` does not care about tightness at all.
- **`lambda` cost nothing.** `V3` already proved `pi_ge_round_five` and
  `sqrt_two_lt`; `3.141592597 - 2 · 1.414213563 = 0.313165471` exactly and the
  existing `linarith [sqrt_two_lt, pi_ge_round_five]` closes the wider literal
  unchanged. `V3` had simply rounded its own lemmas down to six digits.

### Lemma-name drift hit this sprint

None new. Everything used resolved on the first try:
`Real.cos_pi_over_two_pow`, `Real.sqrtTwoAddSeries_one`, `Real.sq_sqrt`,
`Real.sqrt_nonneg`, `Real.pi_le_four`, `Real.pi_pos`, `pow_le_pow_left₀`,
`div_lt_iff₀'`, `lt_div_iff₀`, `mul_le_mul_of_nonneg_right`, `mul_nonneg`,
`push_neg`, `by_contra`. The one trap was semantic rather than nominal —
`Real.sqrtTwoAddSeries_succ` exists but recurses in the unhelpful direction
(see above).

### Numbers, for the next planner

`Scratch/cosine_anchor_v4.py` reproduces everything in exact rational
arithmetic. Error budget of `pi_le_sharp`, `π ≤ 3.1415926848`, which is
`3.12e-8` high:

| source | contribution |
|---|---|
| quartic truncation `y ^ 6 / 720` at `y = π/64`, amplified by `64 / sin(π/64)` | `2.5e-8` |
| twelve-digit radical certification | `< 4e-10` |
| rounding to a ten-digit literal `r = 0.0490873857` | the remainder |

So the *only* way to sharpen this further is more depth (`k = 6` cuts the
truncation term by `64×` and the radical chain stays cheap — this is the free
knob the sine anchor never had) or a sextic cosine rung. Both would move
`kappa` from `1.6e-9` above the floor to something like `1e-10`, i.e. buy under
`1.5e-9` of score. **Not worth a sprint.**

### Where the problem now stands

| side | shipped | permanent ceiling / floor | gap |
|---|---|---|---|
| `kappa` | `0.32298206` | `π ^ 3 / 96 = 0.32298204875…` (exact infimum, unattained) | `1.6e-9` |
| `lambda` | `0.313165471` | `π - 2√2 = 0.31316552884…` (attained at `n = 0`) | `5.8e-8` |

Score `0.009816589` against the theoretical optimum `0.00981651991…`: `7.0e-8`
away, from `1.32e-5` at the start of the sprint. Both remaining gaps are
decimal digits, and the larger of the two (`lambda`) is now the `5.8e-8` slack
in `pi_ge_round_five`, which is the depth-2 quintic bootstrap — the very thing
this sprint removed from the *upper* side.

Next, and this is the honest reading: **the analytic phase is over and so is
the numeric one.** A `lambda` push is available and would be worth `5.8e-8`
(feed the new `pi_le_sharp` back through `pi_ge_bootstrap_step`, or better,
build a *sine* anchor lower bound on `π` the same one-shot way from
`sin (π/2^(k+2)) = √(2 - s_k)/2` and the quintic — but that is the
badly-conditioned radical again, so more likely just one more bootstrap round
now that the `π ^ 5` correction can use the far sharper `pi_le_sharp`). It is
`< 1e-7` of score. The genuinely useful remaining work is **infrastructure**:
formalize the two optimality statements — `4 ^ n (π - polygonLower n) ↗ π ^ 3 / 96`
so that no admissible `kappa` lies below the floor, and
`π - polygonLower 0` attained so that no admissible `lambda` lies above the
ceiling — and let the harness declare the problem closed with a proof rather
than with a plateau in `frontier.csv`.

---

## sprint_005 — optimality_certificate            [READY_FOR_EVALUATION]

Goal: prove the **converse** — that the admissible set of the scored contract is
exactly `{0 ≤ lam < π − 2√2} × {π ^ 3 / 96 < kap}` — so that the benchmark's
optimum is a theorem rather than a docstring, and certify that optimum from both
sides. P0 (the certificate) and P1 (`valid_of_bracket`) required; P2 (depth-3
lower anchor) and P3 (secondary depth-10 contract) gated optional.

Outcome: **success; P0, P1, P2 and P3 all landed.** `Candidates/V5.lean` ships
`lambda = 313165527/1000000000`, `kappa = 32298206/100000000`, score
`9816533/1000000000 = 0.009816533` against `V4`'s `0.009816589`, plus the
secondary frontier `kappaDepth10 − lambdaDepth10 = 2.2e-8` (depth-10 reported
width `2.10e-14`). Evaluator `--no-log`: all twelve stages PASS, stage 8
(secondary contract) PASS for the first time in the run, axiom closure exactly
`{propext, Classical.choice, Quot.sound}` on all eleven exported theorems,
`strict_improvement=True`. Every constant was re-verified in exact `Fraction`
arithmetic first (`Scratch/optimality_certificate_v5.py`, which reruns the whole
sprint's numerics and asserts each margin); **none of the contract's predicted
constants was wrong**, including all four new radical margins and all three
depth-3 correction terms to two significant figures.

Two of the three files that had to be written built on the **first** attempt.
`Optimality.lean` needed one edit: a `ring` after a `field_simp` that had already
closed the goal ("No goals to be solved"). That is the only failure of the whole
sprint.

### The Archimedean step, which the contract flagged as the likeliest failure

It was not a failure. Both names resolve unchanged:

- **`exists_nat_gt (x : R) : ∃ n : ℕ, x < n`** — root namespace, in
  `Mathlib/Algebra/Order/Archimedean/Basic.lean` §`StrictOrderedSemiring`. It
  applies to `ℝ` with no instance trouble and needs no import beyond what
  `Proof/Main.lean` already pulls in.
- **`one_le_pow₀ (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n`** — note `n` is **implicit**,
  so it is `one_le_pow₀ (by norm_num)` with no index argument.

`nat_le_four_pow : (n : ℝ) ≤ 4 ^ n` is five lines exactly as predicted:
`| zero => norm_num`, then `have h1 : (1:ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)`,
`have hsucc : (4:ℝ) ^ (k+1) = 4 * 4 ^ k := by ring`, `push_cast`, `rw [hsucc]`,
`linarith`. Do **not** `rw [pow_succ]` — the `ring`-proved `have` is more
predictable about which side the `4` lands on.

Also noted while searching, and worth knowing for any future "∃ n, x < f n"
argument: **`add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : ∃ n, x < (y+1) ^ n`**
is right next to `exists_nat_gt` and would have given `∃ n : ℕ, x < 4 ^ n` in one
step (`y := 3`). The induction was kept because it has no instance risk, but the
lemma is there if a successor wants it.

### The converse itself — what it cost, and what it collapses

`admissible_kappa_ge : ValidPolygonBound lam kap → π ^ 3 / 96 ≤ kap` is
`by_contra`, `push_neg`, one `exists_nat_gt`, two divisions cleared, one
`linarith`. **Twenty lines, and completely symbolic** — `π ^ 3` and `π ^ 5` never
receive a numeric value and every quantity cancels, exactly as the contract
insisted. The two clearing steps, with the signatures confirmed in this Mathlib
(`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`):

    div_lt_iff₀  (hc : 0 < c) : b / c < a ↔ b < a * c
    lt_div_iff₀  (hc : 0 < c) : a < b / c ↔ a * c < b
    div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
    lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b

The final contradiction is a plain `linarith`: the two hypotheses are
`π ^ 5 < 4 ^ n * (30720 * ε)` and `ε * (30720 * 4 ^ n) < π ^ 5`, whose monomials
`4 ^ n · π ^ 3` and `4 ^ n · kap` ring-normalise to the same atoms on both sides.
No `nlinarith` needed anywhere in the file.

**The structural payoff is real.** With `valid_of_bracket` in place the contract
proof in `V5.lean` is three lines and mentions no polygon:

```lean
theorem polygon_pi_constant_search : ValidPolygonBound lambda kappa :=
  valid_of_bracket (by norm_num [lambda]) lambda_lt_ceiling
    (by rw [kappa]; exact pi_cube_div_lt_sharp)
```

Everything a successor sprint can change is now on one of two one-dimensional
axes. `valid_iff_bracket_of_ne` packages both directions as an `iff` under the
hypothesis `π ^ 3 / 96 ≠ kap` (the single undetermined boundary point).

### P2 — the depth-3 lower anchor, with measured margins

Landed exactly on the contract's predicted literal and score. **All four radical
stages and all three depth-3 lemmas built on the first attempt**, single
`nlinarith` with three hints each, one multiplication per call.

| lemma | bound | measured margin |
|---|---|---|
| `s1_lt` | `s₁ < 1.414213562374` | `a₁² − 2 = 2.56e-12` |
| `s2_lt` | `s₂ < 1.847759065023` | `a₂² − (2 + a₁) = 6.71e-13` |
| `s3_lt` | `s₃ < 1.961570560807` | `a₃² − (2 + a₂) = 1.69e-12` |
| `sqrt_two_sub_s3_gt` | `√(2 − s₃) > 0.196034280657` | `(2 − a₃) − c² = 2.93e-13` |
| `pi_cube_div_6144_gt` | `π ³/6144 > 0.005046594239` | `5.33e-14` |
| `pi_pow_five_div_depth_three_lt` | `π ⁵/125829120 < 2.432027e-6` | `8.73e-13` |
| `pi_ge_depth_three` | `π ≥ 3.141592652724` | `0` (exact sum), `8.66e-10` below true π |

Confirmations worth carrying forward:

- **The `2 − ·` side is survivable at depth 3** if the inner chain is `+`-nested.
  Sprint 004's rule ("prefer `+`-nesting; depth is expensive on the `2 − ·`
  side") is right about the *outer* stage only: twelve digits inward carried
  through with `≥ 6.7e-13`, and the single subtraction cost about half an order
  of magnitude, ending at `2.93e-13`. Contrast `V3`'s chain, which put the
  subtraction at depth 2 *and* used only nine digits and was false at eight.
  So: twelve digits buys you one `2 − ·` step at depth 3. Budget accordingly.
- **`polygonLower_three_eq` needs the power rewritten separately.** The contract's
  warning is real; the safe form is
  `have h : (2:ℝ) ^ (3 + 1) = 16 := by norm_num; rw [polygonLower, h]`.
  A bare `norm_num` after `rw [polygonLower]` risks firing the
  `sqrtTwoAddSeries` simp set on the argument. `congr 1` also works.
- **Weaken before you exponentiate.** `pi_le_sharp.trans (by norm_num)` from
  `3.1415926848` down to `3.1415927` costs `9e-14` of a `2.43e-6` term and
  replaces 55-digit intermediates with 40-digit ones. `norm_num` would have
  managed either, but the habit is worth keeping.
- **No iteration at depth 3.** Both correction terms in `deficit_ge 3` come from
  bounds already in the file, so there is no fixed point and no bootstrap — the
  same one-shot structure sprint 004 found for the upper side, now on the lower.
  `norm_num at h` on `deficit_ge 3` normalises `96 * 4 ^ 3 → 6144` and
  `30720 * 4 ^ 3 * 4 ^ 3 → 125829120` in one go and leaves `polygonLower 3`
  alone, exactly as it did at `n = 2` in sprints 002/003.

### P3 — the secondary depth-10 frontier

Also landed, and it is genuinely cheap: `deficit_scaled_ge 10` plus
`pi_cube_div_gt` plus one `π ⁵` tail bound, and the upper conjunct is literally
`(polygon_pi_constant_search.2.2 10).2` after `rw`ing `kappaDepth10 = kappa`.

    4 ^ 10 (π − polygonLower 10)  ≥  0.32298204848 − 9.500103e-9
                                  =  0.322982038979897  >  lambdaDepth10

margin `9.80e-10`; `π ⁵/(30720 · 4 ¹⁰) = π ⁵/32212254720 < 9.500103e-9` with
margin `9.4e-16`. Secondary score `2.2e-8`, reported depth-10 width `2.10e-14`
against the main frontier's `9.36e-9`. **Getting `deficit_scaled_ge 10`'s
`Real.pi ^ 5 / (30720 * 4 ^ 10)` to match the tail lemma is purely syntactic** —
state the tail lemma with the same `30720 * 4 ^ 10` and do the
`norm_num`-to-`32212254720` normalisation *inside* its proof, not in the caller;
then `linarith` aligns the atoms without help.

### A numeric correction to sprint 004's own Experience entry

Sprint 004's closing table says `kappa = 0.32298206` is `1.6e-9` above the floor
`π ^ 3 / 96 = 0.322982048753…`. **It is `1.125e-8` above.** The `1.6e-9` is the
margin of `pi_cube_div_lt_sharp` against `(3.1415926848) ^ 3 / 96 =
0.3229820584…`, i.e. against the *certified* value, not against the floor. The
consequence for planning is the opposite of what sprint 004 concluded: after
`V5`, of the `1.309e-8` of remaining score, **`1.125e-8` is on `kappa`** and only
`1.844e-9` on `lambda`. Sprint 004's "not worth a sprint" verdict on a `k = 6`
cosine anchor was based on the wrong number — it is worth `~1.1e-8`, which is
85% of everything left. `V4.lean`'s docstring carries the same error; it is
read-only now, and `V5.lean`'s docstring states the correction.

### Where the problem now stands

| side | shipped | permanent ceiling / floor | gap |
|---|---|---|---|
| `kappa` | `0.32298206` | `π ^ 3 / 96 = 0.32298204875312…` (proved infimum, unattained) | `1.125e-8` |
| `lambda` | `0.313165527` | `π − 2√2 = 0.31316552884360…` (proved supremum, attained at `n = 0`) | `1.844e-9` |

Score `0.009816533` against the optimum `0.009816519909519986`: `1.309e-8` away,
and the optimum itself is now bracketed by machine-checked theorems,
`9816488/1000000000 < π ^ 3 / 96 − (π − 2√2) < kappa − lambda`.

Next, in descending value, and all of it is digits:

1. **The `k = 6` cosine anchor** (`Real.cos_pi_over_two_pow 6`, one more `+`-nested
   stage `s6_gt`, then §5 of `CosineAnchor.lean` verbatim at `π/128`). The
   inverted truncation error is `2 ^ (k+1) · y ⁶/720 / sin y ≈ y ⁴ · π/720`, so it
   falls by **`16×`** per level, not `64×`: `2.53e-8` at `k = 5`, `1.58e-9` at
   `k = 6` (measured, not estimated). Multiplied by `d(π ³/96)/dπ = 3π ²/96 =
   0.3084` that puts `kappa` at about `0.3229820492`. Worth `~1.08e-8` of the
   `1.309e-8` remaining — by far the largest single item left, and cheap: the
   radical chain contracts, so twelve digits still suffice, and the inversion is
   the same one-step `by_contra`/`quartic_antitone`/`linarith` with `1/16`
   replaced by `1/32` and a new ten-digit `r`.
2. **`lambda = 313165527976/1000000000000`**, which `V5` already proves and then
   rounds away (`pi_ge_depth_three − 2 · s1_lt` is exactly that, and the
   inequality is strict). Worth `9.76e-10` for a one-line change. `V5` shipped
   the contract's nine-digit literal deliberately, to execute the sprint as
   written; the free digits are still there.
3. A depth-4 lower anchor. `√(2 − s₄)` needs `s₄` from above and the subtraction
   `2 − s₄ = 0.0096…` cancels two digits, so budget ~15 decimal places; worth at
   most the remaining `1.8e-9` on `lambda`.

There is no remaining item that is not a rational re-certification, and
`admissible_score_gt_rat` now bounds how much any of them can ever be worth.
