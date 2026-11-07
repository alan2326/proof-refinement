# Bulletin — Polygon-π refinement

Volatile. The planner reads this first. The human edits the priority block; the
sprint driver appends one line per sprint.

## Frontier

| | value |
|---|---|
| incumbent candidate | `Candidates/V5.lean` |
| incumbent `kappa` | `128/375` |
| incumbent `lambda` | `9/32` |
| incumbent score (`kappa - lambda`, minimize) | `721/12000 = 0.060083333` |
| reported interval width at depth 10 | `721/12582912000 = 5.729993e-08` |
| axiom closure | `{propext, Classical.choice, Quot.sound}` |
| sprints run | 5 |

## Standing priority directive (human-maintained)

1. **Prefer architectural rungs over precision pushes.** A sprint that
   introduces a genuinely new analytic ingredient is worth more than one that
   moves a digit. Every contract must declare `Rung type:
   architectural | precision | infrastructure`, and a `precision` sprint must
   justify itself against the last `architectural` one in its Rationale.

2. **Interrogate every constant in the current chain, not just the obvious one.**
   The baseline's upper bound is a product of several separately-replaceable
   factors. If you have been attacking the same factor for two sprints, attack a
   different one.

3. **Keep both sides moving.** The score is `kappa - lambda`. The `lambda` side
   starts at `0` and is completely unexplored, but it is not a free lunch either
   — do not let the run become one-sided in either direction. `frontier.csv`
   records a `side` column and a one-sided run will be obvious in the report.

4. **A failed sprint with a precise obstruction note is a useful sprint.** Write
   what you tried into `Experience.md` so the next planner can attack the same
   goal from a different angle instead of repeating yours.

## Sprint log

_(one line per sprint, appended by the driver skill)_

| sprint | slug | rung | side | outcome | score | what changed |
|---|---|---|---|---|---|---|
| sprint_001 | upper_cubic_taylor | architectural | upper | PASS | score 2/3 | replaced V0's `x - x³/4 < sin x` with the Taylor bound `x - x³/6 < sin x`, cutting `kappa` from 1 to 2/3 |
| sprint_002 | lower_taylor5 | architectural | lower | PASS | score 5/12 | opened the lower side with `sin x < x - x³/6 + x⁵/120` plus a `π > 3` witness, lifting `lambda` from 0 to 1/4 |
| sprint_003 | upper_tan_pi_over_eight | architectural | upper | PASS | score 151/768 | replaced the V0-vintage `π ≤ 4` with `π < 7/2` via `Real.lt_tan` at `π/8`, cutting `kappa` to 343/768 |
| sprint_004 | lower_polygon_depth2 | architectural | lower | PASS | score 127/768 | sharpened the π lower witness from 3 to 31/10 via the depth-2 inscribed polygon's triple-nested radical, lifting `lambda` to 9/32 |
| sprint_005 | upper_tan_pi_over_sixteen | architectural | upper | PASS | score 721/12000 | tightened `π < 7/2` to `π < 16/5` via `Real.lt_tan` at `π/16`, needing the first lower bound on `√(2+√2)`; `kappa` to 128/375 |
