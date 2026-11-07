# Polygon-π refinement — results summary

Generated from `ProofRefinement/PolygonPi/Refinement_Log/log.jsonl`.

Benchmark depth 10 — the inscribed regular 4096-gon.


## Headline

- best candidate: `Candidates/V5.lean`
- `kappa = 16149103/50000000`, `lambda = 313165527/1000000000`
- score `kappa - lambda = 9816533/1000000000` = 0.009816533000
- reported interval width = `9816533/1048576000000000` = 9.361775e-09
- gap to analytic floor = 0.000000013090
- improvement over the baseline score of 1: 101.8690x
- of a total available headroom of 101.8691x
- axiom closure: `Classical.choice, Quot.sound, propext`

## The reported theorem

```
polygonLower 10 + lambda / 4 ^ 10  <  π  <  polygonLower 10 + kappa / 4 ^ 10
lambda = 313165527/1000000000
kappa  = 16149103/50000000
width  = 9816533/1048576000000000
```

## Sprint counts

- log records: 6
- passing: 6
- failing: 0
- improvements by rung type: architectural 4, infrastructure 1
- improvements by side: both 2, lower 2, upper 1

## Frontier trajectory

| candidate | kappa | lambda | score | width @ depth 10 | rung | side | improved |
|---|---|---|---|---|---|---|---|
| `V0` | 1 | 0 | 1 | 9.536743e-07 | architectural | lower | None |
| `V1` | 1 | 29/100 | 71/100 | 6.771088e-07 | architectural | lower | True |
| `V2` | 3229947/10000000 | 29/100 | 329947/10000000 | 3.146620e-08 | architectural | upper | True |
| `V3` | 3229947/10000000 | 62633/200000 | 98297/10000000 | 9.374332e-09 | architectural | lower | True |
| `V4` | 16149103/50000000 | 313165471/1000000000 | 9816589/1000000000 | 9.361829e-09 | architectural | both | True |
| `V5` | 16149103/50000000 | 313165527/1000000000 | 9816533/1000000000 | 9.361775e-09 | infrastructure | both | True |

## Replay

```bash
./ProofRefinement/PolygonPi/scripts/verify_all.sh
```

## Known limitation

Per-model-call token and dollar accounting is not obtainable from inside this harness, so cost reporting is wall-clock and Lean-compile CPU only.
