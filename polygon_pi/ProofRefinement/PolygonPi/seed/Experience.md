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
