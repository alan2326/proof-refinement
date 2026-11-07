# sprint_003_upper_tan_pi_over_eight

**Rung type:** `architectural`
**Parent candidate:** `Candidates/V2.lean` (score `5/12`)
**Target file:** `Candidates/V3.lean`
**Side:** `upper`
**Strict improvement required:** yes

## Goal

Attack the `π ≤ 4` factor that has been V0-vintage since sprint 000. Prove a
strictly tighter upper `π < 7/2` from `Real.lt_tan` at `x = π/8` (the depth-1
*circumscribed* polygon vertex angle), then substitute this bound for
`Real.pi_le_four` in V2's upper-conjunct arithmetic. Drives `kappa` from `2/3`
down to `343/768`. `lambda` stays at `1/4`. Score `5/12 → 151/768` (a
`169/768 ≈ 0.220` drop).

## Rationale

Two directives converge on this sprint before any other:

1. **Standing directive 2 (interrogate every constant).** V2's upper chain has
   three quantitative pieces: the cubic Taylor coefficient `1/6` (V1 tightened
   it), the depth-scaling factor (unchanged from V0 by design), and the
   `π ≤ 4 ⇒ π³ ≤ 64` factor (never interrogated). Experience's `sprint_002`
   "Next" note calls this out by name — *"the upper side's `π ≤ 4 → π³ ≤ 64`
   factor is still V0-vintage; replacing `π ≤ 4` with any tighter certified
   `π < c` immediately cuts `kappa` below `2/3`"*. That is exactly this sprint.
2. **Standing directive 3 (keep both sides moving).** V0→V1 was upper, V1→V2
   was lower. V2→V3 alternates back to upper. Both sides remain in play.

The mechanism is a **new analytic ingredient**, not a variant of any prior
chain:

- V0 used `Real.sin_gt_sub_cube` (Mathlib's convenience cubic).
- V1 used `sin x > x − x³/6` (tight cubic Taylor lower via
  `strictMonoOn_of_deriv_pos`).
- V2 introduced `sin x < x − x³/6 + x⁵/120` (fifth-order Taylor upper).
- This sprint introduces `π/8 < tan(π/8)` (tan-based upper on `π`, dual to
  V1/V2's sin-based lower ingredients). It uses `Real.lt_tan`, which
  Experience §env-notes confirms is present in this Mathlib and explicitly
  recommends as a worked `strictMonoOn_of_deriv_pos` example. Nothing prior
  in the loop has touched `tan`.

Whereas V0/V1/V2 all constrain `π − polygonLower n` from above via a `sin`
Taylor bound, this sprint constrains `π` from above via a `tan` bound at a
concrete rational multiple of `π`. Structurally new.

Directive checks:

- **Architectural, not precision:** new Mathlib lemma (`Real.lt_tan`), new
  trigonometric species (tan), first candidate to bound `π` from above by
  anything other than `Real.pi_le_four`. Not the same chain with a smaller
  constant — the closed form `tan(π/8) = √2 − 1` and the `√2 < 23/16` step
  are wired together in a way V0/V1/V2 do not use.
- **Untouched factor:** the `π ≤ 4 ⇒ π³ ≤ 64` factor is the only V0-vintage
  quantitative piece still standing in the incumbent chain.
- **Bounded to one session:** one lemma `pi_lt_seven_halves`, plus the reuse
  of V2's upper-conjunct arithmetic with `π³ ≤ 64` replaced by `π³ ≤ 343/8`.
  Everything else in V2 (including the entire lower conjunct, `three_lt_pi`,
  and both Taylor bounds in `Candidates/V2/Taylor.lean`) is copied forward.

### Concrete witness that `kappa = 343/768` succeeds

`tan(π/8) = √2 − 1` (standard closed form; derivable from half-angle since
`cos(π/4) = √2/2`, giving `sin²(π/8) = (2−√2)/4`, `cos²(π/8) = (2+√2)/4`, hence
`tan²(π/8) = (2−√2)/(2+√2) = (2−√2)²/2 = 3 − 2√2 = (√2 − 1)²`). Then

    π  <  8 · tan(π/8)  =  8 · (√2 − 1).

Using `√2 < 23/16` (already proved inside V2's `three_lt_pi`),

    8 · (√2 − 1)  <  8 · (23/16 − 1)  =  8 · 7/16  =  7/2.

So `π < 7/2`, hence `π³ ≤ (7/2)³ = 343/8`. In V1's rescaling identity
`π − polygonLower n < π³ / (96 · 4^n)`, this yields

    π − polygonLower n  <  (343/8) / (96 · 4^n)  =  343 / (768 · 4^n),

so `kappa = 343/768` closes the upper conjunct. Numerically
`π³ ≈ 31.006 ≪ 42.875 = (7/2)³`, so there is a factor of ~1.38 of headroom on
`π³`, and the `√2 < 23/16` bound itself has slack (`√2 ≈ 1.4142 < 1.4375`).
Both cushions are wide enough that no tactic knife-edge is expected.

### Score arithmetic

- Parent score: `2/3 − 1/4 = 5/12 = 320/768`.
- New score: `343/768 − 1/4 = 343/768 − 192/768 = 151/768`.
- Strict drop: `320/768 − 151/768 = 169/768 ≈ 0.220`. Substantial.
- Interval width at depth 10:
  `(151/768) / 4^10 = 151/805306368 ≈ 1.875 × 10⁻⁷`
  (vs V2's `5/12582912 ≈ 3.97 × 10⁻⁷`) — roughly halved.

## Concrete edits expected

- `Candidates/V3.lean` — declares `def lambda : ℝ := 1 / 4` and
  `def kappa : ℝ := 343 / 768` on single lines, with `-- @parent V2` header.
  Proves the contract by:
  * (upper) V1/V2's rescaling arithmetic verbatim through
    `π − polygonLower n < π³ / (96 · 4^n)`, then closing with
    `pi_lt_seven_halves` and the substitution `π³ ≤ 343/8`;
  * (lower) V2's proof verbatim (identical Taylor 5 upper bound, identical
    `three_lt_pi`, identical rescaling), copied over — candidates are
    self-contained, so V3 does not import V2.
- `Candidates/V3/Tan.lean` — **recommended**, not mandatory. Isolate the new
  `pi_lt_seven_halves` proof (and any tan-related helpers). Theorems only,
  no `axiom`s, imported only by `Candidates/V3.lean`.
- `Candidates/V3/Taylor.lean` — **recommended if V3.lean gets crowded**.
  Restate `sin_gt_sub_cube_div_six` and `sin_lt_taylor5` (near-verbatim copy
  of V2's `Taylor.lean` — do not import V2). Same self-containment rule.
- `Experience.md` — append the `## sprint_003 — upper_tan_pi_over_eight` entry.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, `Candidates/V0.lean`, `Candidates/V1.lean`, `Candidates/V2.lean`,
`Candidates/V2/Taylor.lean`, or any sprint contract is out of scope.

Do **not** register `Candidates/V3/Tan.lean` or `Candidates/V3/Taylor.lean`
in `lemma.toml`; the allowed prefixes already cover
`ProofRefinement.PolygonPi.Candidates.V3.*`.

## Acceptance criteria

- [ ] `Candidates/V3.lean` declares `def kappa : ℝ := 343 / 768` and
      `def lambda : ℝ := 1 / 4` on single lines
- [ ] `-- @parent V2` header present on line 1
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V3` succeeds
- [ ] evaluator passes all twelve stages
- [ ] axiom closure is a subset of `{propext, Classical.choice, Quot.sound}`
      (no `native_decide`, no project axiom, no `sorry`, no `opaque`)
- [ ] `score = 151/768`, strictly below parent score `5/12`
- [ ] no import of `Mathlib.Analysis.Real.Pi.*`, bare `Mathlib`, or any
      text-blocked identifier (`pi_lt_sqrtTwoAddSeries`,
      `pi_gt_sqrtTwoAddSeries`, `sqrtTwoAddSeries_step_up`/`_down`,
      `pi_lower_bound_start`, `pi_upper_bound_start`, `pi_gt_three`,
      `pi_gt_3141592`, `pi_lt_3141593`)
- [ ] no import of `Candidates/V0.lean`, `Candidates/V1.lean`, or
      `Candidates/V2.lean` (candidates are self-contained)

## Bounded pre-checks the generator may run

```bash
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds \
  --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi

lake build ProofRefinement.PolygonPi.Candidates.V3
env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V3.lean --no-log
```

## Notes / expected obstructions

### The core lemma: `pi_lt_seven_halves : Real.pi < 7/2`

Two routes are equally viable. Try the search-first route (Route 0) before
writing either.

**Route 0 — search first.** Before proving anything, run `lean_local_search`
/ `lean_loogle` for `Real.pi < _` and `tan (π / _)` in Mathlib. If a
`Real.pi_lt_c` with `c ≤ 7/2` exists in a *permitted* module (not under
`Mathlib.Analysis.Real.Pi`), use it directly. `Real.pi_lt_315` may or may not
exist as a name; if it does and lives in `Trigonometric.Bounds` or similar,
score is a two-line change. Do not spend more than one search pass; if
nothing surfaces, fall through to Route 1.

**Route 1 — `Real.lt_tan` at π/8, closed-form tan.**

1. `have h1 : (0 : ℝ) < Real.pi / 8 := by positivity`
2. `have h2 : Real.pi / 8 < Real.pi / 2 := by`
     `apply div_lt_div_of_pos_left Real.pi_pos <;> norm_num` (or use
     `div_lt_div_iff_of_pos_left` — check the ambient name; a
     `linarith`-plus-`Real.pi_pos` finish also works).
3. `have htan_lb : Real.pi / 8 < Real.tan (Real.pi / 8) := Real.lt_tan h1 h2`.
4. Prove `Real.tan (Real.pi / 8) = Real.sqrt 2 - 1`. Two sub-routes:
   * **Sub-route 1a (double-angle solve).** `Real.tan_two_mul` gives
     `tan(π/4) = 2·tan(π/8) / (1 − tan²(π/8))`. Combined with
     `Real.tan_pi_div_four = 1` (search — it should exist; if not, derive from
     `sin_pi_div_four = cos_pi_div_four = √2/2`), this yields
     `tan²(π/8) + 2·tan(π/8) − 1 = 0`. Positivity of `tan(π/8)` (since
     `π/8 ∈ (0, π/2)` — use `Real.tan_pos_of_pos_of_lt_pi_div_two` if
     available, or `Real.sin_pos_of_pos_of_lt_pi` and `Real.cos_pos_of_mem_Ioo`
     to build `tan > 0` manually) picks the positive root `√2 − 1`.
   * **Sub-route 1b (sin/cos explicit).** Use `polygonLower_eq_mul_sin 1`
     and `unfold polygonLower; rw [Real.sqrtTwoAddSeries_one]` (this is
     already done inside V2's `three_lt_pi` — copy the shape) to extract
     `Real.sin (Real.pi / 8) = Real.sqrt (2 - Real.sqrt 2) / 2`. For
     `Real.cos (Real.pi / 8)`, use `Real.cos_pi_over_two_pow` if it applies
     at the right index (Experience §env-notes confirms it survives and is
     `@[simp]`; the exact statement may be
     `Real.cos (π / 2^(n+1)) = sqrtTwoAddSeries 0 n / 2` or similar —
     `lean_local_search` on `cos (Real.pi / 2 ^ _)` will pin it down). Then
     `Real.tan_eq_sin_div_cos` reduces `tan(π/8)` to
     `√(2-√2)/√(2+√2)`. Simplify to `√2 − 1` via
     `(2-√2)/(2+√2) = (2-√2)²/((2+√2)(2-√2)) = (2-√2)²/2`, i.e.
     `tan(π/8)² = (2-√2)²/2 = 3 - 2√2 = (√2 - 1)²`, then take the positive
     square root using `Real.sqrt_sq` and `sq_nonneg` guards.
5. `have h8tan_lt : 8 * (Real.sqrt 2 - 1) < 7 / 2 := by`
     `have hsqrt2 : Real.sqrt 2 < 23/16 := ...`
     `linarith`
   The `√2 < 23/16` step is 4 lines from `Real.sqrt_lt_sqrt`+`Real.sqrt_sq`,
   already written twice in V2 (`three_lt_pi`); copy the shape.
6. Combine 3, 4, 5:
     `Real.pi < 8 * Real.tan (Real.pi/8) = 8 * (√2 - 1) < 7/2`.

**Route 2 — bypass explicit `tan(π/8)` value; bound `sin/cos` ratio directly.**

Instead of proving `tan(π/8) = √2 − 1`, prove `16·sin(π/8) < 7·cos(π/8)`
directly by squaring (both sides positive; `pow_lt_pow_iff_left` or
`sq_lt_sq'` unsquares afterwards):

    (16·sin(π/8))²  =  256 · (2-√2)/4  =  64·(2-√2)
    (7·cos(π/8))²   =  49  · (2+√2)/4  =  (49/4)·(2+√2)

so the squared inequality is `256·(2-√2) < 49·(2+√2)`, i.e.
`512 - 256·√2 < 98 + 49·√2`, i.e. `414 < 305·√2`. Use
`√2 > 7/5` (from `(7/5)² = 49/25 < 2` — one `norm_num` after
`Real.lt_sqrt`), so `305 · (7/5) = 427 > 414`. Combine with
`Real.lt_tan` to close `π · cos(π/8) < 8 · sin(π/8) < (7/2) · cos(π/8)`,
then divide by `cos(π/8) > 0`.

Route 2 avoids the `tan(π/8) = √2 − 1` derivation entirely; it is longer at
the arithmetic step but shorter overall because it never introduces `tan` as
a symbolic quantity that needs simplifying.

**Which to try first:** Route 1a is cleanest **if** `Real.tan_two_mul` and
`Real.tan_pi_div_four` both resolve on this Mathlib version. If either
misses, Route 2 is unconditionally available — it needs only `Real.lt_tan`,
`Real.tan_eq_sin_div_cos`, `Real.cos_pos_of_mem_Ioo`, and the sin/cos
closed forms at π/8 (which fall out of the same nested-radical machinery
V2 already uses in `three_lt_pi`).

### Rescaling arithmetic — copied straight from V1/V2

At `x = π/2^(n+2)` and multiplied by `2^(n+2)`, V1's `sin_gt_sub_cube_div_six`
gives

    2^(n+2) · (π/2^(n+2) - (π/2^(n+2))³ / 6)  <  polygonLower n

and V1's identity `hid` (with `hpow`, `h4n`, `field_simp; ring`) collapses
the LHS to `π - π³ / (96 · 4^n)`. This is exactly V2's upper-conjunct
`hid`; copy it verbatim. Then instead of `π^3 ≤ 64`, use
`π^3 ≤ 343/8` via `pow_le_pow_left₀ Real.pi_pos.le pi_lt_seven_halves.le 3`
followed by `norm_num` to reduce `(7/2)^3`. Close with

    π³ / (96 · 4^n)  ≤  (343/8) / (96 · 4^n)  =  343 / (768 · 4^n)

by `gcongr` and a `field_simp; ring` on the constant simplification, then
`linarith` against `π - polygonLower n < π³ / (96 · 4^n)`.

### The lower conjunct is unchanged

V2's lower-conjunct proof is preserved word-for-word. It uses only
`sin_lt_taylor5`, `three_lt_pi`, `Real.pi_le_four`, and the depth-10
rescaling arithmetic — none of which are altered by this sprint. **Do not
also try to tighten `three_lt_pi` here**; that is a future lower-side
architectural sprint (attack `π > polygonLower 2` or use the new
`pi_lt_seven_halves` machinery symmetrically). Bundling would break the
one-session bound.

Note: V2's lower-conjunct proof uses `Real.pi_le_four`, not
`pi_lt_seven_halves`. Substituting the tighter bound in the lower conjunct
would (numerically) also help lambda, but only marginally, and it costs a
non-trivial rework of V2's `hcore`/`h_lift` arithmetic. Leave it alone in
this sprint. The lambda-side story is a separate architectural rung.

### Do not import prior candidates

`Candidates/V<N>.lean` never imports `Candidates/V<M>.lean` for `M < N`.
Restate `sin_gt_sub_cube_div_six` and `sin_lt_taylor5` (from V2's
`Taylor.lean`) inside `Candidates/V3/Taylor.lean` — a near-verbatim copy is
fine. Same for `three_lt_pi`. This keeps each candidate's axiom closure and
import audit localized.

### Length budget

Estimated: `pi_lt_seven_halves` ~100 lines (Route 1a) or ~120 lines (Route 2);
restated Taylor helpers ~180 lines (verbatim copy of V2/Taylor.lean);
restated `three_lt_pi` ~35 lines; upper- and lower-conjunct arithmetic ~120
lines. Total ~440-500 lines across V3.lean + V3/Tan.lean + V3/Taylor.lean.
Well within the 2000-line-per-file evaluator cap and the 100 KB size cap.

### `Real.lt_tan` import closure

Experience §env-notes confirms `Real.lt_tan` is available in
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`. Before adding the
import to V3 or V3/Tan.lean, run the closure check listed above under
"Bounded pre-checks" and confirm no `Mathlib.Analysis.Real.Pi.*` module
appears in the transitive dependency list. If it does — an unlikely but
possible transitive leak — fall back to whichever specific sub-lemma of
`Real.lt_tan` sits in a cleaner module, or extract the tan monotonicity
argument inline from the pattern shown in Experience §sprint_000. Do **not**
just drop the import and give up; the underlying `strictMonoOn_of_deriv_pos`
argument is copyable from V1/V2 templates.

### If truly `BLOCKED`

Exit only after (a) stating the stuck goal with `lean_goal`, (b) trying at
least two tactically distinct closes on it (not three `simp` flavours), and
(c) writing the exact goal and what you tried into `Experience.md` so the
next planner can attack it from a different angle. In particular, if the
`tan(π/8) = √2 − 1` derivation blocks, the natural pivot is Route 2 (bound
the sin/cos ratio directly) — do not exit without at least attempting the
alternative route.

Suspect the following as the likeliest sticking points, in order:

1. **The `Real.tan_pi_div_four` lookup.** If it does not resolve, derive
   `tan(π/4) = 1` from `Real.tan_eq_sin_div_cos`, `Real.sin_pi_div_four`,
   `Real.cos_pi_div_four`, and `field_simp; ring`. Three lines.
2. **`cos(π/8) > 0`** for the divide step. Use
   `Real.cos_pos_of_mem_Ioo ⟨(by linarith [Real.pi_pos]), (by linarith
   [Real.pi_pos])⟩` with the interval `(-π/2, π/2)`.
3. **Squaring inequalities with mixed signs.** `sq_lt_sq'` and
   `pow_lt_pow_iff_left` (for `n = 2`, positive-base variant) both work;
   if the name churn bites, fall back to
   `nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), ha, hb]` where `ha, hb`
   are the positivity witnesses.
