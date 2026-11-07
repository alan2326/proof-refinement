# sprint_005_upper_tan_pi_over_sixteen

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V4.lean` (score `127/768`)
**Target file:** `Candidates/V5.lean`
**Side:** `upper`
**Strict improvement required:** yes

## Goal

Attack the V3-vintage `pi_lt_seven_halves` factor — now the loosest single term
in the incumbent's chain. Prove a strictly tighter `π < 16/5` from
`Real.lt_tan` at `x = π/16` (the depth-2 *circumscribed* polygon vertex angle),
then substitute this bound for `pi_lt_seven_halves` in V4's upper-conjunct
arithmetic. Drives `kappa` from `343/768 ≈ 0.4466` down to `128/375 ≈ 0.3413`.
`lambda` stays at `9/32`. Score `127/768 → 721/12000` (a `≈ 0.1053` strict
drop, roughly 63% relative — the largest single-sprint score reduction since
sprint 003).

## Rationale

Three directives converge on this sprint before any other:

1. **Standing directive 3 (keep both sides moving).** Recent side rotation was
   `upper (001) → lower (002) → upper (003) → lower (004)`. Sprint 005
   alternates back to upper. Continuing on the lower side would produce
   `upper·2 / lower·3` and make the run unbalanced.

2. **Standing directive 2 (interrogate every constant).** V4's upper chain has
   the same three quantitative pieces V3 introduced: the cubic Taylor
   coefficient `1/6` (V1-vintage, essentially optimal for a cubic sin lower
   bound), the depth-scaling factor (structural, cannot move), and the
   `π < 7/2 ⇒ π³ ≤ 343/8` factor (V3-vintage, sole `kappa` driver, untouched
   since sprint 003). The Taylor factor cannot help `kappa` asymptotically —
   the leading term of `π − polygonLower n` is `π³/(96·4^n)`, and higher-order
   Taylor bounds add `-π⁵/(30720·16^n) + …` terms that vanish faster than
   `1/4^n` and therefore cannot shrink the `n → ∞` bound `kappa/1`. **Only a
   tighter `π < c` moves `kappa`.** That single fact, plus the fact that the
   `π < 7/2` factor is now the sole V3-vintage piece in the incumbent, makes
   this the correct next target under directive 2.

3. **Standing directive 1 (architectural over precision).** This sprint
   introduces a **new circumscribed-polygon depth (n = 2)** as an upper-bound
   source, with a **triple-nested radical topology** never seen on the upper
   side of the workspace. Sprint 003 used `Real.lt_tan` at `π/8` (depth-1
   circumscribed, single-nested `√2`). This sprint uses `Real.lt_tan` at
   `π/16` (depth-2 circumscribed) with the closed forms
   `sin(π/16) = √(2 - √(2 + √2))/2` and `cos(π/16) = √(2 + √(2 + √2))/2`
   from `Real.sin_pi_div_sixteen` / `Real.cos_pi_div_sixteen`. Not a "grind
   the same knob" precision push — new Mathlib lemmas, new radical-arithmetic
   chain, and (importantly) **the first LOWER bound on `√(2 + √2)` in the
   workspace**: V4/Polygon.lean introduced only the upper bound
   `√(2 + √2) < 18479/10000`. This sprint's mirror ingredient
   `√(2 + √2) > 24/13` is a new proof object.

The mechanism is the dual of sprint 004 at the same polygon depth. Sprint 004
turned the `π > 3` V2-vintage lower into `π > 31/10` via the **inscribed**
polygon at depth 2 (`polygonLower_lt_pi 2`). Sprint 005 turns the `π < 7/2`
V3-vintage upper into `π < 16/5` via the **circumscribed** polygon at depth 2
(`Real.lt_tan` at `π/16`). Same directive-2 logic (attack the untouched sole
remaining V3-vintage bound), opposite side, structurally symmetric ingredients
— inscribed depth 2 vs. circumscribed depth 2.

### Why not the alternatives

- **Depth-3 inscribed polygon (lower side, symmetric to sprint 004).** Would
  give `π > c` for some `c > 31/10` and marginally bump `lambda`. But the
  lower-conjunct ceiling is at `n = 0`, where `(π − polygonLower 0)·4^0 =
  π − 2√2 ≈ 0.313`. Current `lambda = 9/32 = 0.28125`, leaving headroom
  `≤ 0.032` under the current Taylor 5 bound and Taylor 7 gives `≤ 0.017`
  additional. Score gain is at best `≈ 0.017`, versus this sprint's `≈ 0.105`.
  Directive 1 also prefers the analytically new pi/16 chain over another pi/N
  inscribed depth.
- **Niven-style `π < 22/7` via `∫₀¹ x⁴(1-x)⁴/(1+x²) dx > 0`.** Yields a
  better kappa (`≈ 0.324` vs. this sprint's `≈ 0.341`), and is architecturally
  a genuinely new chain (Riemann-integral estimate instead of trig closed
  form). But formalization is a multi-hundred-line integral-machinery push
  with a real risk of exceeding one session. Reserve for a later sprint after
  the cheaper `pi/16` rung has landed and the score frontier makes the
  additional `~0.017` from Niven worth the risk.
- **7th-order Taylor lower on `sin`.** Cannot help `kappa` asymptotically (see
  directive 2 note above). Precision-flavored on the lower side; marginal
  even there.
- **`π² ≤ 49/4` in V4's lower conjunct.** Pure precision. Would push `lambda`
  a tick above `9/32`; small, and belongs in a bundled precision sprint after
  the next architectural upper rung, not now.

### Concrete witness that `kappa = 128/375` succeeds

**Step 1 — `pi_lt_sixteen_fifths : Real.pi < 16 / 5`.** Numerically
`16·tan(π/16) ≈ 3.1826`, comfortably below `16/5 = 3.2`. The formal chain (all
steps close with `nlinarith` / `norm_num` from `Real.sq_sqrt` guards):

- `√2 > 238/169` because `238² = 56_644 < 57_122 = 2 · 169²`. (Slack `478`.)
- Hence `2 + √2 > 2 + 238/169 = 576/169 = (24/13)²`.
- `√(2 + √2) > 24/13` because `(24/13)² < 2 + √2` (previous line) via
  `Real.sqrt_lt_sqrt` on `((24/13))² < 2 + √2` and `Real.sqrt_sq` on the
  positive base. **New ingredient** — V4/Polygon.lean has only the upper
  bound `√(2 + √2) < 18479/10000`; this is its mirror-direction sibling.
- Both `sin(π/16), cos(π/16) > 0` and the squared closed forms
  `sin²(π/16) = (2 − √(2+√2))/4`, `cos²(π/16) = (2 + √(2+√2))/4` follow from
  `Real.sin_pi_div_sixteen` / `Real.cos_pi_div_sixteen` + `Real.sq_sqrt` on
  the radicands (each `≥ 0` via `√(2+√2) < 18479/10000 < 2` and `√(2+√2) > 0`
  respectively). **The `√(2+√2) < 2` guard is easy — either use the previous
  upper bound from V4's chain (restated here, not imported), or the trivial
  `Real.sqrtTwoAddSeries_lt_two`.**
- Squared inequality `25 · sin²(π/16) < cos²(π/16)`. Substituting the closed
  forms and multiplying by `4`: `25·(2 − √(2+√2)) < 2 + √(2+√2)`, i.e.
  `50 − 25·s < 2 + s` where `s = √(2 + √2)`, i.e. `48 < 26·s`, i.e.
  `s > 48/26 = 24/13`. Established in the previous bullet. Close with a
  `nlinarith` hint of the form `nlinarith [h_s_gt_24_13, Real.sqrt_nonneg _]`.
- Un-square via `sq_lt_sq₀` (both `5·sin(π/16) ≥ 0` and `cos(π/16) ≥ 0` by
  positivity) to get `5 · sin(π/16) < cos(π/16)`.
- Rewrite as `tan(π/16) < 1/5` using `Real.tan_eq_sin_div_cos` and
  `div_lt_iff₀ hcos_pos`.
- `Real.lt_tan h1 h2 : π/16 < tan(π/16)` (with `h1 : 0 < π/16` by
  `positivity`, `h2 : π/16 < π/2` by `linarith [Real.pi_pos]`).
- Chain: `π/16 < tan(π/16) < 1/5`, hence `π < 16/5`.

**Step 2 — plug `pi_lt_sixteen_fifths` into V4's upper conjunct with
`kappa = 128/375`.**

V4's upper conjunct reduces (after V1's cubic-Taylor rescaling) to
`π − polygonLower n < π³/(96·4^n)`. Replacing `π^3 ≤ 343/8` with
`π^3 ≤ (16/5)^3 = 4096/125` via
`pow_le_pow_left₀ Real.pi_pos.le pi_lt_sixteen_fifths.le 3`:

    π − polygonLower n  <  (4096/125) / (96·4^n)  =  4096 / (12000·4^n)
                        =  128 / (375·4^n)

so `kappa = 128/375` closes the upper conjunct. The constant simplification
`(4096/125)/(96·M) = (128/375)/M` needs the same `rw [div_div, div_div];
congr 1; ring` pattern V3 used (`field_simp` alone leaves `375 = 3·125`
unclosed).

Numerical headroom on the `s > 24/13` step: `s = √(2 + √2) ≈ 1.84776`,
`24/13 ≈ 1.84615`, slack `≈ 0.00161`. On the un-squaring step `5·sin(π/16) <
cos(π/16)`: LHS `≈ 0.99456`, RHS `≈ 0.98079`... wait, LHS > RHS numerically?
Let me recheck. `sin(π/16) ≈ 0.19509`, so `5·sin(π/16) ≈ 0.97545`.
`cos(π/16) ≈ 0.98079`. LHS `< RHS` by `≈ 0.00534`. That is the binding slack.
The squared form `25·(2 − s) < 2 + s` has `LHS = 25·(2 − 1.84776) = 3.806`,
`RHS = 2 + 1.84776 = 3.84776`, slack `≈ 0.042`. All three slacks
(`√2 > 238/169`: 0.006; `s > 24/13`: 0.002; `tan < 1/5`: 0.001) are
comfortable but the last is tightest — no knife-edge, but generator should
not further slacken the `24/13` witness.

### Score arithmetic

- Parent score: `343/768 − 9/32 = 343/768 − 216/768 = 127/768`.
- New score: `128/375 − 9/32`. LCM(375, 32) = 12000. So
  `128/375 = 4096/12000` and `9/32 = 3375/12000`. New score
  `= (4096 − 3375)/12000 = 721/12000`. In lowest terms: `gcd(721, 12000) =
  gcd(7·103, 2⁵·3·5³) = 1`, so `721/12000`.
- Strict drop: `127/768 − 721/12000`. LCM(768, 12000) = 96000.
  `127/768 = 15875/96000`, `721/12000 = 5768/96000`, drop `= 10107/96000
  ≈ 0.1053`. About 63% relative — largest single-sprint score drop since
  sprint 003's `169/768 ≈ 0.220`.
- Interval width at depth 10:
  `(721/12000) / 4^10 = 721 / 12_582_912_000 ≈ 5.729 × 10⁻⁸`
  (vs V4's `127/805_306_368 ≈ 1.577 × 10⁻⁷`) — cut by a factor of ~2.75.

## Concrete edits expected

- `Candidates/V5.lean` — declares `def lambda : ℝ := 9 / 32` and
  `def kappa : ℝ := 128 / 375` on single lines, with `-- @parent V4` header.
  Proves the contract by:
  * (upper) V4's upper-conjunct proof shape with two substitutions:
    - `pi_lt_seven_halves` → `pi_lt_sixteen_fifths`
    - `343/8` → `4096/125` in the `pow_le_pow_left₀` step, and
      `(343/768) → (128/375)` in the constant rearrangement (same
      `rw [div_div, div_div]; congr 1; ring` pattern);
  * (lower) V4's lower-conjunct proof verbatim (identical `sin_lt_taylor5`,
    identical `pi_gt_thirty_one_over_ten`, identical rescaling).
- `Candidates/V5/Tan.lean` — **recommended**, not mandatory. Contains the new
  `pi_lt_sixteen_fifths` proof plus the new √2 / √(2 + √2) lower-bound
  helpers (`sqrt_two_gt_238_over_169`, `sqrt_two_add_sqrt_two_gt_24_over_13`).
  Theorems only, no `axiom`s. Imported only by `Candidates/V5.lean`.
  Estimated ~140 lines.
- `Candidates/V5/Taylor.lean` — near-verbatim copy of
  `Candidates/V4/Taylor.lean` (`sin_gt_sub_cube_div_six` and
  `sin_lt_taylor5`). Candidates are self-contained, so V5 must not import
  V4. ~170 lines.
- `Candidates/V5/Polygon.lean` — near-verbatim copy of
  `Candidates/V4/Polygon.lean` (`pi_gt_thirty_one_over_ten` and its √2 /
  √(2+√2) helpers). Same self-containment reason. ~115 lines.
- `Experience.md` — append the `## sprint_005 — upper_tan_pi_over_sixteen`
  entry per the format at the top of that file.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
`Candidates/V2/Taylor.lean`, `Candidates/V3.lean`, `Candidates/V3/Tan.lean`,
`Candidates/V3/Taylor.lean`, `Candidates/V4.lean`, `Candidates/V4/Polygon.lean`,
`Candidates/V4/Tan.lean`, `Candidates/V4/Taylor.lean`, or any sprint contract
is out of scope.

Do **not** register `Candidates/V5/*.lean` in `lemma.toml`; the allowed
prefixes already cover `ProofRefinement.PolygonPi.Candidates.V5.*`.

## Acceptance criteria

- [ ] `Candidates/V5.lean` declares `def kappa : ℝ := 128 / 375` and
      `def lambda : ℝ := 9 / 32` on single lines
- [ ] `-- @parent V4` header present on line 1
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V5` succeeds
- [ ] evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
      (no `native_decide`, no project axiom, no `sorry`, no `opaque`)
- [ ] `score = 721/12000`, strictly below parent score `127/768`
- [ ] no import of `Mathlib.Analysis.Real.Pi.*`, bare `Mathlib`, or any
      text-blocked identifier (`pi_lt_sqrtTwoAddSeries`,
      `pi_gt_sqrtTwoAddSeries`, `sqrtTwoAddSeries_step_up`/`_down`,
      `pi_lower_bound_start`, `pi_upper_bound_start`, `pi_gt_three`,
      `pi_gt_3141592`, `pi_lt_3141593`)
- [ ] no import of `Candidates/V0.lean` … `Candidates/V4.lean` or any
      `Candidates/V<M>/*.lean` for `M ≤ 4` (candidates are self-contained)

## Bounded pre-checks the generator may run

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds \
  --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi

lake build ProofRefinement.PolygonPi.Candidates.V5
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V5.lean --no-log
```

## Notes / expected obstructions

### The core lemma: `pi_lt_sixteen_fifths : Real.pi < 16 / 5`

Route 2 from sprint 003 (bound the `sin/cos` ratio directly) is the
recommended shape — it avoids proving `tan(π/16) = √(2 + √2) − 1 − …` in
closed form. Sprint 003 established this template on `π/8`; port it to
`π/16` with only the depth-2 nested radical adjustment.

Structure (mirror of V4/Tan.lean's `pi_lt_seven_halves`, one polygon depth
deeper):

1. `have h1 : (0 : ℝ) < Real.pi / 16 := by positivity`
2. `have h2 : Real.pi / 16 < Real.pi / 2 := by linarith [Real.pi_pos]`
3. `have htan_lb : Real.pi / 16 < Real.tan (Real.pi / 16) := Real.lt_tan h1 h2`
4. `have hcos_pos : (0 : ℝ) < Real.cos (Real.pi / 16) :=`
   `Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩`
5. `have hsin_pos : (0 : ℝ) < Real.sin (Real.pi / 16) :=`
   `Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])`
6. Squared closed forms (`Real.sin_pi_div_sixteen`, `Real.cos_pi_div_sixteen`
   both `@[simp]` in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
   per Experience §sprint_003 env-notes):
   ```
   have hsin_sq : Real.sin (Real.pi / 16) ^ 2
                = (2 - Real.sqrt (2 + Real.sqrt 2)) / 4 := by
     rw [Real.sin_pi_div_sixteen, div_pow, Real.sq_sqrt h_radicand_minus_nn]
     norm_num
   have hcos_sq : Real.cos (Real.pi / 16) ^ 2
                = (2 + Real.sqrt (2 + Real.sqrt 2)) / 4 := by
     rw [Real.cos_pi_div_sixteen, div_pow, Real.sq_sqrt h_radicand_plus_nn]
     norm_num
   ```
   with radicand-nonnegativity guards:
   * `h_radicand_plus_nn : 0 ≤ 2 + √(2 + √2)` from `Real.sqrt_nonneg _` and
     `linarith`.
   * `h_radicand_minus_nn : 0 ≤ 2 - √(2 + √2)` from an *upper* bound on
     `√(2+√2)`. Cheapest source: state
     `have h_upper : Real.sqrt (2 + Real.sqrt 2) < 2` inline, using
     `Real.sqrtTwoAddSeries_lt_two` (Experience §sprint_000 confirms it
     survives) — or restate the `18479/10000` bound from V4/Polygon.lean
     inline (do not import V4). The generator may pick whichever is shorter.
7. The key numerical bound `√(2 + √2) > 24/13`:
   ```
   lemma sqrt_two_add_sqrt_two_gt_24_over_13 :
       (24 / 13 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
     have hsqrt2 : (238 / 169 : ℝ) < Real.sqrt 2 := by
       have h : (238 / 169 : ℝ) ^ 2 < Real.sqrt 2 ^ 2 := by
         rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
       exact (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg 2)).mp h
     have h_bound : ((24 / 13 : ℝ)) ^ 2 < 2 + Real.sqrt 2 := by
       have := hsqrt2; nlinarith
     have h_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
       have := Real.sqrt_nonneg 2; linarith
     have h1 : Real.sqrt (((24 / 13 : ℝ)) ^ 2)
                 < Real.sqrt (2 + Real.sqrt 2) :=
       Real.sqrt_lt_sqrt (by positivity) h_bound
     rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 24 / 13)] at h1
   ```
   Numerics that close by `norm_num` inside `nlinarith`:
   * `238² = 56_644 < 57_122 = 2·169²`, so `(238/169)² < 2`.
   * `(24/13)² = 576/169 = 2 + 238/169`, so `(24/13)² < 2 + √2` follows
     directly from `√2 > 238/169` by `nlinarith`.
8. Squared inequality `25 · sin²(π/16) < cos²(π/16)`:
   ```
   have h_sq_lt : (5 * Real.sin (Real.pi / 16)) ^ 2
                < (Real.cos (Real.pi / 16)) ^ 2 := by
     have hexpand : (5 * Real.sin (Real.pi / 16)) ^ 2
                  = 25 * Real.sin (Real.pi / 16) ^ 2 := by ring
     rw [hexpand, hsin_sq, hcos_sq]
     nlinarith [sqrt_two_add_sqrt_two_gt_24_over_13, Real.sqrt_nonneg (2 + Real.sqrt 2)]
   ```
   The `nlinarith` closes the algebraic identity `25·(2−s)/4 < (2+s)/4`
   (equivalent to `48 < 26·s`) given the hint `s > 24/13`.
9. Un-square:
   ```
   have h_lin : 5 * Real.sin (Real.pi / 16) < Real.cos (Real.pi / 16) :=
     (sq_lt_sq₀ (by positivity) hcos_pos.le).mp h_sq_lt
   ```
10. Rewrite as `tan(π/16) < 1/5`:
    ```
    have h_tan_lt : Real.tan (Real.pi / 16) < 1 / 5 := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos_pos]
      linarith
    ```
11. Chain: `Real.pi / 16 < Real.tan (Real.pi / 16) < 1 / 5`, so
    `Real.pi < 16 · (1/5) = 16/5`. Close with `linarith [htan_lb, h_tan_lt]`.

### Rescaling arithmetic — nearly V4 verbatim (upper conjunct)

V4's upper conjunct already reaches `π − polygonLower n < π³/(96·4^n)` via
`sin_gt_sub_cube_div_six` and the same `hpow`/`h4n`/`field_simp; ring` chain
that will be copied over. Two constants change:

- V4's `hpi3 : Real.pi ^ 3 ≤ 343 / 8` becomes `hpi3 : Real.pi ^ 3 ≤ 4096 /
  125` via
  ```
  have h := pow_le_pow_left₀ Real.pi_pos.le pi_lt_sixteen_fifths.le 3
  -- h : Real.pi ^ 3 ≤ (16/5) ^ 3
  norm_num at h  -- collapses (16/5)^3 to 4096/125
  linarith
  ```
- V4's `hbound : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (343 / 768) / 4 ^ n` becomes
  `hbound : Real.pi ^ 3 / (96 * 4 ^ n) ≤ (128 / 375) / 4 ^ n`. The
  arithmetic identity is `(4096/125) / (96·M) = (128/375) / M`, closed by
  the same pattern V3/V4 used:
  ```
  have h1 : Real.pi ^ 3 / (96 * 4 ^ n)
              ≤ (4096 / 125) / (96 * 4 ^ n) := by gcongr
  have h2 : (4096 / 125 : ℝ) / (96 * 4 ^ n) = (128 / 375) / 4 ^ n := by
    rw [div_div, div_div]; congr 1; ring
  linarith
  ```
  Numerical check: `4096 / (125·96) = 4096/12000 = 128/375` (divide top and
  bottom by 32). `ring` handles the constant `12000 = 96·125` and
  `375 = 3·125` refactoring automatically.

### The lower conjunct is unchanged

V4's lower-conjunct proof is preserved word-for-word. It uses only
`sin_lt_taylor5`, `pi_gt_thirty_one_over_ten`, and the depth-10 rescaling
arithmetic — none of which are altered by this sprint. **Do not also try to
tighten `pi_gt_thirty_one_over_ten` or upgrade `hπ_sq_le : π² ≤ 16` here**;
those are future lower-side / precision sprints. Bundling would break the
one-session bound.

Note: `pi_lt_sixteen_fifths` (proved fresh in this sprint) is strictly
stronger than the `Real.pi_le_four` that V4's lower conjunct uses inside
`hπ_sq_le`. Substituting the tighter bound in the lower conjunct would
(numerically) also help `lambda` — `π² ≤ (16/5)² = 256/25 = 10.24` instead
of `π² ≤ 16`. But that changes the `(320 − 16)·π³ = 304·π³` calculation and
requires reworking V4's `hcore`/`h_lift` arithmetic. Leave it alone in this
sprint. The lambda-side story is a separate rung.

### Do not import prior candidates

`Candidates/V5.lean` never imports `Candidates/V<M>.lean` for `M ≤ 4`.
Restate `sin_gt_sub_cube_div_six`, `sin_lt_taylor5` (in
`Candidates/V5/Taylor.lean`, near-verbatim copy of V4's) and
`pi_gt_thirty_one_over_ten` with its √2 / √(2+√2) upper helpers (in
`Candidates/V5/Polygon.lean`, near-verbatim copy of V4's). The new
`pi_lt_sixteen_fifths` and its √2 / √(2+√2) **lower** helpers go in
`Candidates/V5/Tan.lean`. This keeps each candidate's axiom closure and
import audit localized.

### Length budget

Estimated across all four V5 files:
- `V5.lean`: ~155 lines (V4.lean structure with two constant substitutions
  in the upper conjunct; lower conjunct verbatim)
- `V5/Tan.lean`: ~140 lines (new `pi_lt_sixteen_fifths` ~90 lines + `√2 >
  238/169` ~15 lines + `√(2+√2) > 24/13` ~30 lines)
- `V5/Polygon.lean`: ~115 lines (verbatim copy of V4/Polygon.lean, ~115
  lines)
- `V5/Taylor.lean`: ~170 lines (verbatim copy of V4/Taylor.lean, ~167 lines)

Total ~580 lines. Every file well within the 2000-line and 100 KB caps.

### Import closure

`Real.lt_tan`, `Real.tan_eq_sin_div_cos`, `Real.cos_pos_of_mem_Ioo`,
`Real.sin_pos_of_pos_of_lt_pi`, `Real.sin_pi_div_sixteen`,
`Real.cos_pi_div_sixteen`, `Real.sqrt_lt_sqrt`, `Real.sqrt_sq`,
`Real.sq_sqrt`, `sq_lt_sq₀` are all already reachable through V4's existing
imports (V4/Tan.lean uses `Real.lt_tan`, `Real.tan_eq_sin_div_cos`,
`Real.cos_pos_of_mem_Ioo`, `Real.sin_pos_of_pos_of_lt_pi`,
`Real.sin_pi_div_eight`, `Real.cos_pi_div_eight` — and `_div_sixteen` lives
in the same `Trigonometric/Basic.lean` block per Experience §sprint_003
env-notes). No new Mathlib import should be needed. If the import closure
check surfaces a new prefix that ends up under `Mathlib.Analysis.Real.Pi.*`,
stop and re-plan; do not paper over.

### If truly `BLOCKED`

Exit only after (a) stating the stuck goal with `lean_goal`, (b) trying at
least two tactically distinct closes on it (not three `simp` flavours), and
(c) writing the exact goal and what you tried into `Experience.md` so the
next planner can attack it from a different angle.

Suspect the following as the likeliest sticking points, in order:

1. **The `Real.sin_pi_div_sixteen` / `Real.cos_pi_div_sixteen` lookup.**
   Experience §sprint_003 env-notes confirms them present in
   `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`, but if a name
   has drifted, grep the Mathlib tree in that file for `sin (π / 16)`. If
   the closed-form lemma is missing entirely, derive `sin²(π/16)` and
   `cos²(π/16)` from the half-angle identities and
   `Real.cos_pi_div_eight = √(2+√2)/2`:
   * `cos(2x) = 1 − 2·sin²(x)`, so
     `sin²(π/16) = (1 − cos(π/8))/2 = (1 − √(2+√2)/2)/2 = (2 − √(2+√2))/4`.
   * `cos(2x) = 2·cos²(x) − 1`, so
     `cos²(π/16) = (1 + cos(π/8))/2 = (2 + √(2+√2))/4`.
   Same closed forms, no `_div_sixteen` name required — costs ~30 extra
   lines using `Real.cos_two_mul` and half-angle algebra.
2. **The `nlinarith` step in `sqrt_two_add_sqrt_two_gt_24_over_13`.** If it
   hangs on `(24/13)² < 2 + √2` given `√2 > 238/169`, split manually:
   `have : (24 / 13 : ℝ) ^ 2 = 2 + 238 / 169 := by norm_num`, then
   `linarith`. The identity `(24/13)² = 576/169 = 2 + 238/169 =
   (338 + 238)/169` is exact.
3. **`hcos_pos.le` or `hcos_pos` in the un-square.** If `sq_lt_sq₀` demands
   `≤` and you have `<`, use `.le` explicitly. Same lint pattern V4/Tan.lean
   uses at `h_lhs_nn` / `h_rhs_nn`.
4. **The `(16/5)^3 = 4096/125` collapse.** `norm_num at h` should handle it,
   but if `h`'s shape confuses norm_num, precompute:
   `have h16_5_cubed : ((16 / 5 : ℝ)) ^ 3 = 4096 / 125 := by norm_num` and
   rewrite explicitly. Same escape hatch sprint 003 used at its `norm_num
   at h` step (see Experience §sprint_003 env-notes on the `rw [div_div,
   div_div]; congr 1; ring` fallback).
