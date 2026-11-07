# Bulletin — Polygon-π refinement

Volatile. The planner reads this first. The human edits the priority block; the
sprint driver appends one line per sprint.

## Frontier

| | value |
|---|---|
| incumbent candidate | `Candidates/V0.lean` |
| incumbent `kappa` | `1` |
| incumbent `lambda` | `0` |
| incumbent score (`kappa - lambda`, minimize) | `1` |
| reported interval width at depth 10 | `1/1048576 = 9.536743e-07` |
| axiom closure | `{propext, Classical.choice, Quot.sound}` |
| sprints run | 0 |

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
