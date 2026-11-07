# sprint_004_lower_polygon_depth2

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V3.lean` (score `151/768`)
**Target file:** `Candidates/V4.lean`
**Side:** `lower`
**Strict improvement required:** yes

## Goal

Attack the last V0-vintage quantitative piece in the *lower* conjunct: the
`three_lt_pi` factor (V2 vintage; unchanged since sprint 002) still bottoms out
at `π > 3`. Prove a strictly tighter `π > 31/10` from `polygonLower_lt_pi 2`
plus a nested √2 chain, then lift `lambda` from `1/4 = 192/768` to
`9/32 = 216/768`. `kappa` stays at `343/768`. Score `151/768 → 127/768` (a
`24/768 ≈ 0.0313` strict drop, ~16% relative).

## Rationale

Three directives converge on this sprint before any other:

1. **Standing directive 3 (keep both sides moving).** Recent side rotation was
   `upper (001) → lower (002) → upper (003)`. Sprint 004 alternates back to
   lower. Continuing on the upper side would produce upper-upper-upper against a
   single lower touch and make the run one-sided in fact regardless of directive
   text.
2. **Standing directive 2 (interrogate every constant).** V3's lower chain has
   four quantitative pieces: the cubic Taylor coefficient (V1 tightened it), the
   fifth-order Taylor coefficient (V2 opened it), the `π² ≤ 16` bound (from
   `π ≤ 4`; loose but marginal), and the `π > 3` bound (from `polygonLower 1`;
   loose and *binding*). Sprint 002 opened `lambda` with `π > 3` as its only
   quantitative π-lower input, and nothing since has revisited it. The `π > 3`
   piece is the loosest single factor in the entire lambda derivation — closing
   it is the single largest lever.
3. **Standing directive 1 (architectural over precision).** This sprint
   introduces a **new polygon depth (n = 2)** as a lower-bound source, with a
   **triple-nested radical topology** never seen in the workspace. Sprint 002
   used `polygonLower 1 = 4·√(2 - √2)` (double-nested). This sprint uses
   `polygonLower 2 = 8·√(2 - √(2 + √2))` (triple-nested) and needs a genuinely
   new radical-arithmetic chain to bound it from below. Not a "grind the same
   knob" precision push — a new analytic ingredient (a deeper inscribed polygon
   entering the proof for the first time) with new intermediate objects
   (`sqrtTwoAddSeries 0 2`, `Real.sqrtTwoAddSeries_succ`).

The mechanism is dual to sprint 003. Sprint 003 turned the `π ≤ 4` V0-vintage
upper into `π < 7/2` via a **circumscribed** polygon vertex angle at `π/8`
(`Real.lt_tan`). Sprint 004 turns the `π > 3` V2-vintage lower into `π > 31/10`
via the **inscribed** polygon at `π/16` (`polygonLower_lt_pi 2`). Same
directive-2 logic (attack an unchallenged bound), opposite side, structurally
symmetric ingredients — inscribed vs. circumscribed at the next polygon depth.

### Concrete witness that `lambda = 9/32` succeeds

**Step 1 — `pi_gt_thirty_one_over_ten : (31 : ℝ) / 10 < Real.pi`.** Numerically
`polygonLower 2 = 16·sin(π/16) ≈ 3.1214`, comfortably above `31/10 = 3.1`. The
formal chain (all steps close with `nlinarith` / `norm_num` from `Real.sq_sqrt`
guards):

- `√2 < 14143/10000` because `(14143)² = 200_024_449 > 200_000_000 = 2·(10000)²`.
- Hence `2 + √2 < 2 + 14143/10000 = 34143/10000`.
- `√(2+√2) < 18479/10000` because `(18479)² = 341_473_441 > 341_430_000 =
  (34143/10000)·(10000)²`. (The step is a straight `Real.sqrt_lt_sqrt` +
  `Real.sqrt_sq` combo against `(18479/10000)²` as the upper witness, then
  `linarith` from the previous line.)
- Hence `2 - √(2+√2) > 2 - 18479/10000 = 1521/10000`.
- `√(2-√(2+√2)) > 31/80` because `(31/80)² = 961/6400 = 15_015.625/100_000
  < 15_210/100_000 = 1521/10000`. (Same `sqrt_lt_sqrt` + `sqrt_sq` chain, now
  in the > direction via `sq_lt_sq₀`.)
- `polygonLower 2 = 2^(2+1) · √(2 - sqrtTwoAddSeries 0 2)
  = 8 · √(2 - √(2 + √2))` after unfolding `polygonLower` and rewriting
  `sqrtTwoAddSeries 0 2 = √(2 + sqrtTwoAddSeries 0 1) = √(2 + √2)` via
  `Real.sqrtTwoAddSeries_succ` and `Real.sqrtTwoAddSeries_one`.
- Hence `polygonLower 2 > 8 · (31/80) = 31/10`.
- `polygonLower_lt_pi 2` closes `Real.pi > 31/10` by `linarith`.

**Step 2 — plug `pi_gt_thirty_one_over_ten` into V3's lower conjunct with
`lambda = 9/32`.**

V3's lower conjunct reduces (after V2's Taylor-5 rescaling) to needing
`(320·π³ - 8640) · 4^n > π^5` uniformly in `n` (with V3's `8640 = 30720 ·
(1/4)` replaced by `30720 · (9/32) = 8640`... same number, coincidence). Wait —
different: V3 needs `30720 · (1/4) = 7680`, this sprint needs
`30720 · (9/32) = 8640`. The `1/4 → 9/32` bump changes the target from `7680`
to `8640`.

At `n = 0` (the binding case, as in V3's `hcore`):

    320 · π³ - π⁵ > 8640     (target)

Split as V3 does: bound `π⁵ ≤ 16·π³` via `π² ≤ 16` (from `Real.pi_le_four`;
same V0-vintage bound V3 still uses in this spot, no need to switch to
`π² ≤ 49/4`), so

    320·π³ - π⁵ ≥ (320 - 16)·π³ = 304·π³.

Using `π > 31/10`, so `π³ > (31/10)³ = 29791/1000`:

    304·π³ > 304 · 29791/1000 = 9_056_464/1000 = 9056.464 > 8640.

Headroom `9056.464 - 8640 = 416.464`, i.e., ~5% slack. Compare V3 with the
loose `π > 3` bound: `304 · 27 = 8208 > 7680` gave 6% slack for `lambda = 1/4`.
Same shape, same tactic (`nlinarith` with the product hint), just a stronger
π-lower feeding in.

For `n ≥ 1`, V3's `h_lift` step `(320·π³ - 8640) · (4^n - 1) ≥ 0` +
`(320·π³ - 8640) > π⁵` lifts the `n = 0` case to all `n`. Copy V3's shape
verbatim with `7680 → 8640` and `27 → 29791/1000`.

### Score arithmetic

- Parent score: `343/768 − 1/4 = 343/768 − 192/768 = 151/768`.
- New score: `343/768 − 9/32 = 343/768 − 216/768 = 127/768`.
- Strict drop: `151/768 − 127/768 = 24/768 = 1/32 ≈ 0.0313`. ~16% relative.
- Interval width at depth 10:
  `(127/768) / 4^10 = 127 / 805_306_368 ≈ 1.577 × 10⁻⁷`
  (vs V3's `151/805_306_368 ≈ 1.875 × 10⁻⁷`) — a strict tightening.

### Why not other lower-side moves

- **7th-order Taylor lower on sin.** Tightens the correction term
  `- π⁵/(30720·16^n)` further but the improvement shrinks as `1/64^n`; the
  binding constraint at `n = 0` is dominated by the `π > 3 → π³ > 27` looseness,
  not by higher-order Taylor slack. Directive 1 flags this as precision-flavored,
  and the score gain is marginal (`≤ 0.01`).
- **Tighter `π² ≤ 49/4` from V3's `pi_lt_seven_halves`.** Alone, this only
  moves lambda from `1/4` to about `0.27` — not enough to reach `9/32 = 0.28125`.
  And it's a pure arithmetic tightening of an existing V3 witness (precision,
  not architectural). Can be combined with the depth-2 π-lower in a *later*
  sprint if useful; do not bundle here.
- **Tan-anchored π-lower (e.g., `Real.lt_tan` at π/12 to derive
  `π < 12·tan(π/12) = 12·(2 - √3)`).** Wrong direction: `Real.lt_tan` gives
  *upper* bounds on π, not lower. There is no direct `Real.tan_lt` lower-π
  analogue in the workspace's permitted-module set, and the Mathlib route via
  `Real.pi_gt_3141592` is on the text-blocked list. The inscribed-polygon
  route (this sprint) is the natural lower-side ingredient.

### Directive checks

- **Architectural, not precision:** first use of `polygonLower 2` (n = 2) as a
  proof ingredient; first triple-nested radical `√(2 - √(2 + √2))` in the
  workspace; first use of `Real.sqrtTwoAddSeries_succ`. Structurally symmetric
  to sprint 003 (sprint 003 introduced the depth-1 circumscribed polygon;
  sprint 004 introduces the depth-2 inscribed polygon).
- **Untouched factor:** the `π > 3` bound has been the sole quantitative π-lower
  input to the lambda derivation since sprint 002. It is the largest single
  slack in V3's lower chain (bumping `π > 3` to `π > 31/10` changes `π³ > 27`
  to `π³ > 29.791`, i.e., ~10% tighter, which is the multiplicative gap between
  `304·27 = 8208` and `304·29.791 = 9056.464`).
- **Bounded to one session:** one new lemma (`pi_gt_thirty_one_over_ten`) plus
  the reuse of V3's lower-conjunct arithmetic with `1/4 → 9/32` and
  `27 → 29791/1000` substitutions. Upper conjunct is copied verbatim.

## Concrete edits expected

- `Candidates/V4.lean` — declares `def lambda : ℝ := 9 / 32` and
  `def kappa : ℝ := 343 / 768` on single lines, with `-- @parent V3` header.
  Proves the contract by:
  * (upper) V3's upper-conjunct proof verbatim (identical `sin_gt_sub_cube_div_six`,
    identical `pi_lt_seven_halves`, identical rescaling arithmetic to
    `π - polygonLower n < (343/768)/4^n`);
  * (lower) V3's lower-conjunct structure with two substitutions:
    - `three_lt_pi` → `pi_gt_thirty_one_over_ten`
    - `1/4 → 9/32` in the target, `7680 → 8640` in the intermediate arithmetic,
      `27 → 29791/1000` in the `hcore` step (which V3 has as `304 * 27 = 8208
      > 7680`; now becomes `304 · (31/10)³ = 9056.464 > 8640`).
- `Candidates/V4/Polygon.lean` — **recommended**, not mandatory. Isolate the
  new `pi_gt_thirty_one_over_ten` proof and the √2 / √(2+√2) / √(2-√(2+√2))
  helper lemmas (theorems only, no `axiom`s). Imported only by
  `Candidates/V4.lean`. Estimated ~90 lines.
- `Candidates/V4/Tan.lean` — near-verbatim copy of `Candidates/V3/Tan.lean`
  (`pi_lt_seven_halves` and its two √2 helpers). Candidates are self-contained,
  so V4 must not import V3. ~100 lines.
- `Candidates/V4/Taylor.lean` — near-verbatim copy of
  `Candidates/V3/Taylor.lean` (`sin_gt_sub_cube_div_six` and `sin_lt_taylor5`).
  ~170 lines.
- `Experience.md` — append the `## sprint_004 — lower_polygon_depth2` entry.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
`Candidates/V2/Taylor.lean`, `Candidates/V3.lean`, `Candidates/V3/Tan.lean`,
`Candidates/V3/Taylor.lean`, or any sprint contract is out of scope.

Do **not** register `Candidates/V4/*.lean` in `lemma.toml`; the allowed prefixes
already cover `ProofRefinement.PolygonPi.Candidates.V4.*`.

## Acceptance criteria

- [ ] `Candidates/V4.lean` declares `def kappa : ℝ := 343 / 768` and
      `def lambda : ℝ := 9 / 32` on single lines
- [ ] `-- @parent V3` header present on line 1
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V4` succeeds
- [ ] evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
      (no `native_decide`, no project axiom, no `sorry`, no `opaque`)
- [ ] `score = 127/768`, strictly below parent score `151/768`
- [ ] no import of `Mathlib.Analysis.Real.Pi.*`, bare `Mathlib`, or any
      text-blocked identifier (`pi_lt_sqrtTwoAddSeries`,
      `pi_gt_sqrtTwoAddSeries`, `sqrtTwoAddSeries_step_up`/`_down`,
      `pi_lower_bound_start`, `pi_upper_bound_start`, `pi_gt_three`,
      `pi_gt_3141592`, `pi_lt_3141593`)
- [ ] no import of `Candidates/V0.lean`, `Candidates/V1.lean`,
      `Candidates/V2.lean`, `Candidates/V2/Taylor.lean`, `Candidates/V3.lean`,
      `Candidates/V3/Tan.lean`, or `Candidates/V3/Taylor.lean`
      (candidates are self-contained)

## Bounded pre-checks the generator may run

```bash
lake build ProofRefinement.PolygonPi.Candidates.V4
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V4.lean --no-log
```

## Notes / expected obstructions

### The core lemma: `pi_gt_thirty_one_over_ten : (31 : ℝ) / 10 < Real.pi`

Two routes are viable. Try the search-first route (Route 0) before writing
either.

**Route 0 — search first.** Before proving anything, run `lean_local_search`
/ `lean_loogle` for `Real.pi > _` in permitted modules (not under
`Mathlib.Analysis.Real.Pi`). If a `Real.three_lt_pi_of_...` or similar exists
in `Trigonometric.Basic`/`Bounds` with a rational bound ≥ 31/10, use it
directly. Do not spend more than one search pass; the blocked-name list
already excludes the standard `pi_gt_...` families, so an unblocked variant
is unlikely.

**Route 1 — inscribed polygon at depth 2 (recommended).**

Structural mirror of sprint 002's `three_lt_pi`, at one deeper polygon level.
Sprint 002 used `polygonLower 1 = 4·√(2 - √2)` with the double-nested chain
`√2 < 23/16 → 2 - √2 > 9/16 → √(2 - √2) > 3/4 → polygonLower 1 > 3`. Sprint
004 uses `polygonLower 2 = 8·√(2 - √(2 + √2))` with the triple-nested chain
below.

1. **Unfold `polygonLower 2`.**
   ```
   have hpoly : polygonLower 2
       = 8 * Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
     unfold polygonLower
     rw [show Real.sqrtTwoAddSeries 0 2
             = Real.sqrt (2 + Real.sqrt 2) from by
           rw [Real.sqrtTwoAddSeries_succ, Real.sqrtTwoAddSeries_one]]
     norm_num
   ```
   `Real.sqrtTwoAddSeries_succ` states
   `sqrtTwoAddSeries x (n+1) = √(2 + sqrtTwoAddSeries x n)`. Experience
   §sprint_000 lists it as available (`Real.sqrtTwoAddSeries_succ,
   _monotone_left, _lt_two, _nonneg are all available`).

2. **`√2 < 14143/10000`.** Copy sprint 002 / sprint 003's `sqrt_lt_sqrt` +
   `sqrt_sq` pattern:
   ```
   have h_sqrt2_lt : Real.sqrt 2 < 14143/10000 := by
     have h1 : Real.sqrt 2 < Real.sqrt ((14143/10000 : ℝ) ^ 2) :=
       Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
     rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 14143/10000)] at h1
     exact h1
   ```
   The `norm_num` closes `(14143/10000)² > 2`, i.e., `14143² = 200_024_449
   > 200_000_000`.

3. **`√(2 + √2) < 18479/10000`.** Same shape, one layer deeper:
   ```
   have h_2pss_lt : Real.sqrt (2 + Real.sqrt 2) < 18479/10000 := by
     -- (18479/10000)² = 341_473_441/10^8
     -- 2 + √2 < 2 + 14143/10000 = 34143/10000 = 341_430_000/10^8
     -- 341_430_000 < 341_473_441 ✓
     have hbound : 2 + Real.sqrt 2 < (18479/10000 : ℝ) ^ 2 := by
       have := h_sqrt2_lt; nlinarith
     have h1 : Real.sqrt (2 + Real.sqrt 2)
                < Real.sqrt ((18479/10000 : ℝ) ^ 2) := by
       apply Real.sqrt_lt_sqrt _ hbound
       linarith [Real.sqrt_nonneg 2]
     rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 18479/10000)] at h1
   ```

4. **`√(2 - √(2 + √2)) > 31/80`.** Opposite direction — use `sq_lt_sq₀`
   as in sprint 003:
   ```
   have h_inner_gt : (31/80 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
     have h_radicand_lb : ((31/80 : ℝ)) ^ 2 < 2 - Real.sqrt (2 + Real.sqrt 2) := by
       have := h_2pss_lt; nlinarith  -- (31/80)² = 961/6400 vs 1521/10000
     have h_nn : (0 : ℝ) ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
       have hle := Real.sqrtTwoAddSeries_lt_two (n := 2)  -- IF it applies
       -- fallback: h_2pss_lt gives √(2+√2) < 18479/10000 < 2, so 2 - _ > 0
       have : Real.sqrt (2 + Real.sqrt 2) < 2 := by linarith [h_2pss_lt]
       linarith
     have h1 : Real.sqrt (((31/80 : ℝ)) ^ 2)
                < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
       Real.sqrt_lt_sqrt (by positivity) h_radicand_lb
     rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 31/80)] at h1
   ```

5. **Multiply by 8.**
   ```
   have h_poly_gt : (31/10 : ℝ) < polygonLower 2 := by
     rw [hpoly]
     have : (31/10 : ℝ) = 8 * (31/80) := by norm_num
     rw [this]
     exact mul_lt_mul_of_pos_left h_inner_gt (by norm_num)
   ```

6. **Close with `polygonLower_lt_pi`.**
   ```
   linarith [polygonLower_lt_pi 2, h_poly_gt]
   ```

**Note on the `norm_num` bound calculations.** All the squared checks —
`14143² > 2·10000²`, `18479² > 341_430_000`, `(31/80)² < 1521/10000` — are
integer / rational identities well within `norm_num`'s comfort zone. If a
particular `nlinarith` line hangs, split it manually and hand `norm_num` the
squared identity, then finish with `linarith`.

### Rescaling arithmetic — nearly V3 verbatim

V3's lower conjunct already reaches
`polygonLower n < π - π³/(96·4^n) + π⁵/(30720·16^n)` via
`sin_lt_taylor5` and the same `hpow`/`h4n`/`h16n`/`field_simp; ring` chain
that will be copied over. Only two constants change:

- V3's `h_diff_id` closes
  `π³/(96·4^n) - π⁵/(30720·16^n) - (1/4)/4^n = ...`.
  In V4, replace `(1/4)/4^n` with `(9/32)/4^n`. The `field_simp; ring` line
  will still close it — the constant on the RHS numerator becomes
  `320·π³·4^n - π⁵ - 8640·4^n` (V3 has `- 7680·4^n`). Delete the outdated
  numeric comments; the tactic proof itself does not care.
- V3's `hcore` says `π⁵ + 7680 ≤ 320·π³` using
  `304·27 = 8208 > 7680`. In V4, restate as `π⁵ + 8640 ≤ 320·π³` and use
  `304 · (31/10)³ = 304 · 29791/1000 = 9_056_464/1000`, compared to `8640 =
  8_640_000/1000`. The `nlinarith` hint should include:
  ```
  nlinarith [hπ_cube_gt, hπ_sq_le, hπ_5_le, mul_pos hπpos hπpos,
             hπ_lt_seven_halves]
  ```
  where `hπ_cube_gt : (31/10 : ℝ)^3 < π³` is derived from
  `pi_gt_thirty_one_over_ten` via `pow_lt_pow_left`+`norm_num` (or
  `nlinarith` directly).

### The upper conjunct is unchanged

V3's upper-conjunct proof is preserved word-for-word. It uses only
`sin_gt_sub_cube_div_six`, `pi_lt_seven_halves`, and the depth-10 rescaling
arithmetic — none of which are altered by this sprint. **Do not also try to
tighten `pi_lt_seven_halves` here**; that is a future upper-side architectural
sprint (attack depth-2 circumscribed polygon via `Real.lt_tan` at `π/16`).
Bundling would break the one-session bound.

### Do not import prior candidates

`Candidates/V4.lean` never imports `Candidates/V<M>.lean` for `M < 4`. Restate
`sin_gt_sub_cube_div_six`, `sin_lt_taylor5` (in `Candidates/V4/Taylor.lean`,
near-verbatim copy of V3's) and `pi_lt_seven_halves` (in
`Candidates/V4/Tan.lean`, near-verbatim copy of V3's). The new
`pi_gt_thirty_one_over_ten` and its √2 helpers go in
`Candidates/V4/Polygon.lean`. This keeps each candidate's axiom closure and
import audit localized.

### Length budget

Estimated across all four V4 files:
- `V4.lean`: ~200 lines (V3.lean structure with two constant substitutions)
- `V4/Polygon.lean`: ~90 lines (`pi_gt_thirty_one_over_ten` + 3 helper
  lemmas)
- `V4/Tan.lean`: ~100 lines (verbatim copy of V3/Tan.lean, ~104 lines)
- `V4/Taylor.lean`: ~170 lines (verbatim copy of V3/Taylor.lean, ~167 lines)

Total ~560 lines. Every file well within the 2000-line and 100 KB caps.

### Import closure

`Real.sqrtTwoAddSeries_succ`, `Real.sqrtTwoAddSeries_one`,
`Real.sqrt_lt_sqrt`, `Real.sqrt_sq`, `Real.sq_sqrt`, `sq_lt_sq₀` are all
already reachable through V3's existing imports (V3's Tan.lean already uses
`Real.sq_sqrt` / `sq_lt_sq₀`, and V3's three_lt_pi in the main file already
uses `Real.sqrtTwoAddSeries_one` and `Real.sqrt_lt_sqrt`). No new Mathlib
import should be needed. If the import closure check surfaces a new prefix
that ends up under `Mathlib.Analysis.Real.Pi.*`, stop and re-plan; do not
paper over.

### If truly `BLOCKED`

Exit only after (a) stating the stuck goal with `lean_goal`, (b) trying at
least two tactically distinct closes on it (not three `simp` flavours), and
(c) writing the exact goal and what you tried into `Experience.md` so the
next planner can attack it from a different angle.

Suspect the following as the likeliest sticking points, in order:

1. **The `Real.sqrtTwoAddSeries_succ` name.** Experience §sprint_000 lists it
   as available, but if the exact name has drifted, grep the Mathlib tree in
   `Analysis/SpecialFunctions/Sqrt.lean` / `Trigonometric/Basic.lean` for the
   real definition (`sqrtTwoAddSeries x (n+1) = √(2 + sqrtTwoAddSeries x n)`)
   — a plain `simp [Real.sqrtTwoAddSeries]` unfold plus `Real.sqrtTwoAddSeries_one`
   is a fallback that does not depend on the recursor lemma name.
2. **The `2 - √(2 + √2) ≥ 0` positivity guard.** Needed for the outer
   `sqrt_lt_sqrt` to apply. Either use `Real.sqrtTwoAddSeries_lt_two`
   (if available with the right index) or derive it from
   `√(2 + √2) < 18479/10000 < 2` via `linarith`.
3. **The `nlinarith [hπ_cube_gt, ...]` hcore step.** If it hangs with the
   default hints, split into two lines:
   `have : 304 * ((31/10) : ℝ) ^ 3 = 9_056_464 / 1000 := by norm_num`
   then `linarith` from the pre-computed bound. Same shape V3 used at
   `have h304pi3 : 304 * (27 : ℝ) < 304 * Real.pi ^ 3`.
4. **The bump in `h_diff_id`'s RHS constant.** V3's line is `rw [h16n];
   field_simp; ring`. Same line works in V4 with `1/4 → 9/32`; the constant
   `7680 → 8640` is absorbed by `ring`. If `ring` complains about a
   `denominator` mismatch, add an intermediate `have : (9/32 : ℝ) / 4^n =
   9 / (32 * 4^n) := by field_simp; ring` before the main `rw`.
