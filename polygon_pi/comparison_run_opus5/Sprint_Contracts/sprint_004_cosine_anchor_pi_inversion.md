# sprint_004_cosine_anchor_pi_inversion

**Rung type:** `architectural`
_(new analytic ingredient: a second, independent route from the nested radical to
a numeric bound on `π` — a **cosine anchor** inverted through an *already proved*
Taylor bound, replacing the iterative deficit bootstrap on the upper side. See
"Honesty about the rung type" below; the planner is aware this is the last
genuinely architectural move the problem admits.)_

**Parent candidate:** `Candidates/V3.lean` (score `98297/10000000 = 0.0098297`)
**Target file:** `Candidates/V4.lean`
**Side:** `both` (kappa is the substantive move; lambda is a free literal widening)
**Strict improvement required:** yes

## Goal

Stop extracting the numeric value of `π` from the polygon *deficit* at depth 2 and
start extracting it from the identity `cos (π / 2 ^ (k+1)) = sqrtTwoAddSeries 0 k / 2`
at depth `k = 5`, inverting `V3`'s existing global quartic bound
`cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24`. This gives `π ≤ 3.1415926848` in one
non-iterative step and drops `kappa` from `0.3229947` to `0.3229821`, i.e. to
`4.2e-8` above the permanent floor `π ^ 3 / 96 = 0.32298204875…`. Together with a
free widening of the `lambda` literal to the value `V3`'s own lemmas already
prove, the score goes `0.0098297 → 0.009816629`, which is `1.1e-7` from the
theoretical optimum `π ^ 3 / 96 - (π - 2√2) = 0.00981651991…`.

## Rationale

### Where the remaining gap is

`Experience.md` (sprint 003) establishes that both sides are ceilinged forever:
`4 ^ n (π - polygonLower n) ↗ π ^ 3 / 96`, so no rational `kappa ≤ π ^ 3 / 96` is
admissible and no Taylor order can lower that floor; and `lambda < π - 2√2` is
attained at `n = 0`. Of the `1.32e-5` of score still on the table, `1.27e-5` is on
`kappa` and all of it is one number: **how sharply can this workspace certify an
upper bound on `π`.**

### Which factor has not been interrogated

Sprints 002 and 003 both attacked the *Taylor order* of the deficit expansion
(cubic, then quintic). The standing directive says explicitly not to attack the
same factor a third time. The factor nobody has touched is the **anchor**: every
numeric bound on `π` so far has come from `sin (π / 2 ^ (n+2)) = √(2 - s_n) / 2`
(equivalently `polygonLower n`) at **depth 2**, and the two consequences of that
choice have never been questioned:

1. *The anchor forces an iteration.* `π ≤ p₂⁺ + π ^ 3 / 1536` is self-referential,
   so `V2` needed five bootstrap rounds, and the fixed point is pinned `4.1e-5`
   above `π` by the truncation error of the Taylor bound **at depth 2**. Raising
   the Taylor order (the septic rung) is the obvious fix and is worth the same
   `1.26e-5` — but it is the third consecutive sprint on the same factor and
   costs three new monotonicity ladders (sextic `cos` ≥, septic `sin` ≥, octic
   `cos` ≤) before a single digit moves.
2. *The anchor is badly conditioned.* `√(2 - s_n)` subtracts two nearly equal
   quantities: `2 - s₂ = 0.152…`, `2 - s₄ = 0.0096…`. Sprint 003 measured the
   cost — "at **eight** digits the third stage is false", "budget ~2 extra digits
   per level" — and that is exactly why nobody went deeper than depth 2.

The cosine anchor `cos (π / 2 ^ (k+1)) = s_k / 2` has neither problem. `s_k` is
built by `+`-nesting only, so the certification error *contracts* by a factor
`≈ 4` per level instead of growing (verified below: twelve decimal places at
`√2` still leaves `1e-12` of margin at `s₅`), and the resulting inequality in
`π` is a plain quartic that inverts in one step with no fixed-point iteration at
all. **Depth becomes a free knob for the first time in this workspace**, and the
Taylor order that was expensive to raise stops mattering: at `y = π / 64` the
already-proved quartic has truncation error `y ^ 6 / 720 = 1.94e-11`, which is
three orders of magnitude better than the septic rung would buy at depth 2.

### Alternatives considered and rejected

- **(A) Septic/octic Taylor rung + re-run the depth-2 bootstrap at 12 digits.**
  Reaches the same `kappa ≈ 0.322982`. Rejected: third sprint in a row on the
  Taylor-order factor; needs three new monotonicity ladders where this sprint
  needs none; and it still has to re-certify `√(2 - s₂)` at 12 digits *through*
  the cancellation, which is the fragile part sprint 003 warned about.
- **(B) Same chain, deeper depth (bootstrap at depth 3 or 4).** A pure precision
  push, explicitly costed in sprint 002's notes at `< 1.3e-5`, and it pays the
  cancellation penalty at every extra level. Dominated by this sprint on both
  cost and novelty.
- **(C) Richardson / two-depth extrapolation of `4 ^ n (π - polygonLower n)` to
  cancel the `π ^ 5` term.** Analytically pretty, but the bootstrap already
  solves the fixed point exactly; extrapolation removes a term the iteration has
  already absorbed and buys nothing on either side.
- **(D) Circumscribed polygon via `Real.lt_tan` (`π < N tan (π/N)`).** Genuinely
  different, and Mathlib's `Real.lt_tan` is confirmed present — but the
  circumscribed error is `≈ π ^ 3 / (3 N ^ 2)`, so reaching `1e-8` needs
  `N > 25000`, i.e. depth 13. Not runnable in a session.
- **(E) Anchor at `cos (π/4) = √2 / 2`.** Same idea with only one radical, but
  `y = 0.785` makes the quartic truncation `3.2e-4`; worse than the incumbent.
  Depth is what makes the anchor sharp, which is the point of picking `k = 5`.

## Concrete edits expected

- `Candidates/V4/DeficitMonotone.lean` — copy of `V3`'s, namespace renamed to
  `…Candidates.V4`. Unchanged content.
- `Candidates/V4/CubicDeficit.lean` — copy of `V3`'s, namespace renamed.
  Unchanged content (it still supplies `sub_sin_le_cube_div_six`, `deficit_le`
  and, via the old bootstrap, `pi_le_round_five` which `QuinticDeficit` consumes).
- `Candidates/V4/QuinticDeficit.lean` — copy of `V3`'s, namespace renamed.
  Unchanged content (it supplies `cos_le_quartic`, `sqrt_two_lt` and
  `pi_ge_round_five`).
- `Candidates/V4/CosineAnchor.lean` — **new**. The whole substance of the sprint:
  the anchor identity, the five-stage `+`-nested radical certification, the
  antitone quartic, the inversion, and the new `π ^ 3 / 96` bound.
- `Candidates/V4.lean` — `-- @parent V3`, new `kappa` / `lambda`, contract proof
  structurally identical to `V3`'s with `pi_cube_div_lt` replaced by the new
  bound.
- `Experience.md` — append the sprint entry, including whichever of the
  predicted constants below turned out to be wrong.

Nothing else. Editing `PolygonCore/`, `Proof/`, `Evaluator.py`, `lemma.toml`,
`scripts/`, or any older candidate is out of scope for every sprint.

## The plan, with every constant pre-verified in exact arithmetic

All of the following were checked by the planner in exact `Fraction` arithmetic
against 60-digit `mpmath` values. Margins are given so the generator can tell a
formalization failure from a wrong number.

### 1. The anchor identity

```lean
Real.cos (Real.pi / 2 ^ (k + 1)) = Real.sqrtTwoAddSeries 0 k / 2
```

`Real.cos_pi_over_two_pow` is confirmed present in this Mathlib
(`AGENT_BRIEF.md` "What the trusted surface gives you" toolkit list, and
`Experience.md` sprint_000: "`Real.sin_pi_over_two_pow_succ` and
`Real.cos_pi_over_two_pow` survive and are `@[simp]`"). `#check` it first and
adapt to its index convention; you need the instance that produces
`cos (π / 64)`.

**Fallback if the index convention fights you** (self-contained, uses only the
trusted surface): from `polygonLower n = 2 ^ (n+1) * √(2 - sqrtTwoAddSeries 0 n)`
(definitional) and `polygonLower_eq_mul_sin` you get
`sin (π / 2 ^ (n+2)) = √(2 - s_n) / 2`; then `cos² = 1 - sin² = (2 + s_n)/4`,
`cos (π / 2 ^ (n+2)) ≥ 0`, and `Real.sqrtTwoAddSeries_succ` give
`cos (π / 2 ^ (n+2)) = s_{n+1} / 2`.

### 2. Five-stage lower certification of the `+`-nested radical, 12 decimal places

`s_k := Real.sqrtTwoAddSeries 0 k`, `s_{k+1} = √(2 + s_k)` by
`Real.sqrtTwoAddSeries_succ` (confirmed available). Prove, in order:

| lemma | statement | `a_k ^ 2` vs `2 + a_{k-1}` margin |
|---|---|---|
| `s1_gt` | `1414213562373/1000000000000 < s 1` | `2.69e-13` |
| `s2_gt` | `1847759065022/1000000000000 < s 2` | `2.02e-12` |
| `s3_gt` | `1961570560806/1000000000000 < s 3` | `1.24e-12` |
| `s4_gt` | `1990369453344/1000000000000 < s 4` | `1.11e-12` |
| `s5_gt` | `1997590912410/1000000000000 < s 5` | `9.84e-13` |

Each stage is **one** `nlinarith` with exactly three hints — `Real.sq_sqrt <the
argument's nonnegativity>`, `Real.sqrt_nonneg _`, and the previous stage — per the
"one `nlinarith` per radical level, one multiplication per call" rule from sprint
002. Non-negativity of `2 + s_k` follows from the previous stage's bound (or from
`Real.sqrtTwoAddSeries_nonneg`). `s 1` needs `Real.sqrtTwoAddSeries_one` plus a
`norm_num` to clear `2 + 0`. Note the errors **contract**: `a_k` is a truncation
of `s_k` to twelve decimals at every level, no extra digits are needed going
outward, and this is the structural claim the sprint is testing.

True values, for reference:
`s1 = 1.414213562373095…`, `s2 = 1.847759065022573…`,
`s3 = 1.961570560806460…`, `s4 = 1.990369453344393…`,
`s5 = 1.997590912410344…`.

### 3. The cosine value

```lean
theorem cos_pi_div_64_gt : (998795456205/1000000000000 : ℝ) < Real.cos (Real.pi / 64)
```

from step 1 at `k = 5` and `s5_gt`. True value `cos (π/64) = 0.99879545620517239…`;
the certified bound is `1.72e-13` below it.

### 4. The quartic is antitone on the relevant range

```lean
lemma quartic_antitone {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/16) :
    1 - b ^ 2 / 2 + b ^ 4 / 24 ≤ 1 - a ^ 2 / 2 + a ^ 4 / 24
```

The identity that makes this one step is

    (1 - a²/2 + a⁴/24) - (1 - b²/2 + b⁴/24) = (b² - a²) * (1/2 - (a² + b²)/24),

both factors non-negative because `a ≤ b` and `a² + b² ≤ 2/256 ≪ 12`. Recipe:
`have h1 : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith`,
`have h2 : 0 ≤ 1/2 - (a ^ 2 + b ^ 2)/24 := by nlinarith`, then
`nlinarith [mul_nonneg h1 h2]` — after ring normalisation the hint *is* the goal,
so no search is required.

### 5. The inversion

```lean
theorem pi_le_sharp : Real.pi ≤ 31415926848/10000000000   -- 3.1415926848
```

Proof shape (`by_contra`, four facts, no iteration):

- `hy : Real.pi / 64 ≤ 1/16` from `Real.pi_le_four` (confirmed present; `V3`
  already uses it).
- `hq : Real.cos (Real.pi / 64) ≤ 1 - (π/64) ^ 2 / 2 + (π/64) ^ 4 / 24` — this is
  `cos_le_quartic` from the copied `QuinticDeficit.lean`, **used at full strength
  for the first time**: `V3` proved it globally and then only ever consumed it as
  a derivative sign.
- assume `31415926848/10000000000 < Real.pi`, so `r ≤ π/64` with
  `r := 490873857/10000000000`; `quartic_antitone` gives
  `1 - (π/64)²/2 + (π/64)⁴/24 ≤ 1 - r²/2 + r⁴/24`.
- `hr : 1 - r ^ 2 / 2 + r ^ 4 / 24 < 998795456205/1000000000000` by `norm_num`
  (exact rational margin `4.33e-12`; both sides are rationals, so the tightness
  is irrelevant to `norm_num`).
- chain `L < cos (π/64) ≤ h(π/64) ≤ h(r) < L`, contradiction by `linarith`.

`64 * r = 3.1415926848`, which is `3.12e-8` above `π`. The quartic truncation
contributes `1.94e-11 / sin(π/64) · 64 = 2.5e-8` of that and the radical
certification `< 4e-10`; the rest is rounding to a ten-digit literal.

### 6. The new upper coefficient

```lean
theorem pi_cube_div_lt_sharp : Real.pi ^ 3 / 96 < 3229821/10000000
```

by `pow_le_pow_left₀ Real.pi_pos.le pi_le_sharp 3` then `norm_num` / `linarith`
(the incumbent's `pi_cube_div_lt` proof, verbatim, with the new input). Check:
`(3.1415926848) ^ 3 / 96 = 0.32298205838…`, margin below `0.3229821` is
`4.16e-8`. Keep the old `pi_cube_div_lt` in the copied `CubicDeficit.lean` under
its own name — do not rename or delete it, and do not let the two names collide.

### 7. The candidate

```lean
def lambda : ℝ := 313165471/1000000000
def kappa  : ℝ := 3229821/10000000
```

`lambda` needs **no new mathematics at all**: `V3` already proves
`pi_ge_round_five : 3.141592597 ≤ π` and `sqrt_two_lt : √2 < 1.414213563`, and
`3.141592597 - 2 · 1.414213563 = 0.313165471` exactly, with strictness supplied by
the `√2` bound. `V3` simply left `4.71e-7` of proved headroom unspent in a
six-digit literal. `lambda_lt_deficit_zero` is unchanged apart from the literal.

The contract proof itself is `V3`'s, unchanged, with `pi_cube_div_lt` replaced by
`pi_cube_div_lt_sharp`.

Resulting score: `3229821/10000000 - 313165471/1000000000 = 0.009816629`, against
the parent's `0.0098297` and the theoretical optimum `0.00981651991…`.

## Acceptance criteria

- [ ] `Candidates/V4.lean` declares `def kappa : ℝ := <literal>` and
      `def lambda : ℝ := <literal>` on single lines, with
      `kappa ≤ 3229830/10000000` and `lambda ≥ 313165471/1000000000`
      _(required floor)_
- [ ] target: `kappa = 3229821/10000000` and `lambda = 313165471/1000000000`,
      score `9816629/1000000000 = 0.009816629`
- [ ] optional stretch, only if `pi_le_sharp` lands at `3.1415926848` or better:
      `kappa = 32298206/100000000` (margin above the floor is then only `1.6e-9`
      — verify with `norm_num` before committing to it, and fall back to
      `3229821/10000000` at the first sign of trouble)
- [ ] `Candidates/V4/CosineAnchor.lean` contains `pi_le_sharp` proving
      `Real.pi ≤ 3.1415926848` (or sharper) **without** any bootstrap iteration,
      and without using `polygonLower` or `deficit_le` anywhere in its proof
- [ ] the five radical stages are stated at twelve decimal places and each is a
      single `nlinarith`; if any stage needs more digits than the table above,
      record the measured margin in `Experience.md` (that would falsify the
      "errors contract on the `+`-nested chain" claim, which is the analytic
      point of this sprint)
- [ ] `lake build ProofRefinement.PolygonPi.Candidates.V4` succeeds
- [ ] the evaluator passes all twelve stages with `--no-log`
- [ ] axiom closure is exactly a subset of `{propext, Classical.choice, Quot.sound}`
- [ ] `score < 98297/10000000` (strict improvement, enforced)

## Bounded pre-checks the generator may run

```bash
# the one lemma the sprint depends on that the planner could not verify directly
echo '#check @Real.cos_pi_over_two_pow
#check @Real.sqrtTwoAddSeries_succ
#check @Real.sqrtTwoAddSeries_one
#check @Real.sqrtTwoAddSeries_nonneg' # run these inside a scratch Lean file

lake build ProofRefinement.PolygonPi.Candidates.V4

env UV_CACHE_DIR=polygon_pi/.uv-cache \
  uv run ProofRefinement/PolygonPi/Evaluator.py \
  --file ProofRefinement/PolygonPi/Candidates/V4.lean --no-log

# only if you add a Mathlib import that V3 did not already have
python3 ProofRefinement/PolygonPi/scripts/polygonpi_import_closure.py \
  <module> --blocked-exact Mathlib --blocked-prefix Mathlib.Analysis.Real.Pi
```

No new Mathlib import is expected: `sqrtTwoAddSeries` and its lemmas are already
in `Proof/Main.lean`'s closure (`V3/CubicDeficit.lean` uses
`Real.sqrtTwoAddSeries_two` with no extra import), and `cos_pi_over_two_pow`
lives beside them.

## Notes / expected obstructions

- **Read first:** `Experience.md` sprints 002 and 003 in full. The digit-budget
  table, the "one `nlinarith` per radical level, one multiplication per call"
  rule, and the drift list (`le_or_lt` does not exist — use `le_or_gt`;
  `div_le_div_iff` and `mul_lt_mul_left` do not resolve) all apply verbatim here.
- **The likeliest failure is step 1**, the anchor identity, not the arithmetic.
  Budget the fallback derivation in §1 and do not spend the session fighting the
  index convention of `cos_pi_over_two_pow`; the fallback route through
  `polygonLower_eq_mul_sin` + `sin² + cos² = 1` + `cos ≥ 0` is entirely within the
  trusted surface and `Real.sin_sq_add_cos_sq` / `Real.cos_two_mul` are both
  confirmed working from sprint 003.
- **Do not re-run or extend either bootstrap.** The lower bootstrap's `5.7e-8`
  error is `3.4e-8` truncation plus `1.6e-8` from `p₂⁻`; tightening it buys under
  `2e-8` of score against the `1.26e-5` this sprint is aimed at. Grinding it is
  exactly the loop's characteristic failure mode. Copy `QuinticDeficit.lean`
  unchanged.
- **Do not try to prove a septic/octic Taylor rung.** It is not needed: the
  already-proved global quartic is sharper at `π/64` than a septic rung would be
  at `π/16`, by three orders of magnitude. If you find yourself writing a fourth
  `monotone_of_hasDerivAt_nonneg` ladder, you have left the contract.
- **`norm_num` on the cube of a ten-digit literal** produces ~31-digit
  intermediates. Sprint 002 confirmed `norm_num` handles 21-digit intermediates
  without complaint and sprint 003 pushed further; if it stalls, isolate the
  numeric fact as its own `have … : ((31415926848/10000000000 : ℝ)) ^ 3 < 96 *
  (3229821/10000000) := by norm_num` and finish with division-free `linarith`,
  which is the two-`have` pattern sprint 003 recommends over `norm_num at h ⊢`.
- **Namespace hygiene when copying.** All four derived files and the candidate
  share one namespace, so each name may be defined once. Rename the namespace to
  `…Candidates.V4` in all copies and give the new results fresh names
  (`pi_le_sharp`, `pi_cube_div_lt_sharp`) rather than shadowing `pi_le_round_five`
  or `pi_cube_div_lt`.

## Honesty about the rung type, and what is left after this

This is declared `architectural` because the ingredient is new — a second,
independent anchor for the numeric value of `π`, a one-shot inversion in place of
a fixed-point iteration, and a radical chain whose conditioning is *opposite* to
the incumbent's — and because it removes the depth-2 deficit bound from the upper
bound's critical path entirely rather than improving a constant inside it. It is
not a numerical push in disguise: no constant of the incumbent's chain is being
re-tightened, and the incumbent's chain is not used.

What is nonetheless true, and the next planner should not be misled about it:
the *score* consequence is numeric, because sprint 003 already proved that the
analytic phase is over. After this sprint the frontier is expected to sit
`1.1e-7` from a proved-optimal `0.00981651991…`, with `kappa` `4.2e-8` above a
floor it can never reach and `lambda` `5.8e-8` below a ceiling it can never
reach. **Every remaining sprint is a digit grind**, and each is worth under
`1e-7`. Sprint 005 should therefore be `infrastructure`, not `precision`:
the useful remaining work is to formalize the two optimality statements
(`4 ^ n (π - polygonLower n) → π ^ 3 / 96` from below, so no admissible `kappa`
is below the floor; and `π - polygonLower 0` is attained, so no admissible
`lambda` is above the ceiling) so the harness can declare the problem closed with
a proof rather than with a plateau in `frontier.csv`.
