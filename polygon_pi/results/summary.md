# Polygon-π refinement — results summary

Generated from `ProofRefinement/PolygonPi/Refinement_Log/log.jsonl`.

Benchmark depth 10 — the inscribed regular 4096-gon.


## Headline

- best candidate: `Candidates/V5.lean`
- `kappa = 128/375`, `lambda = 9/32`
- score `kappa - lambda = 721/12000` = 0.060083333333
- reported interval width = `721/12582912000` = 5.729993e-08
- gap to analytic floor = 0.050266813424
- improvement over the baseline score of 1: 16.6436x
- of a total available headroom of 101.8691x
- axiom closure: `Classical.choice, Quot.sound, propext`

## The reported theorem

```
polygonLower 10 + lambda / 4 ^ 10  <  π  <  polygonLower 10 + kappa / 4 ^ 10
lambda = 9/32
kappa  = 128/375
width  = 721/12582912000
```

## Sprint counts

- log records: 6
- passing: 6
- failing: 0
- improvements by rung type: architectural 5
- improvements by side: lower 2, upper 3

## Frontier trajectory

| candidate | kappa | lambda | score | width @ depth 10 | rung | side | improved |
|---|---|---|---|---|---|---|---|
| `V0` | 1 | 0 | 1 | 9.536743e-07 | architectural | upper | None |
| `V1` | 2/3 | 0 | 2/3 | 6.357829e-07 | architectural | upper | True |
| `V2` | 2/3 | 1/4 | 5/12 | 3.973643e-07 | architectural | lower | True |
| `V3` | 343/768 | 1/4 | 151/768 | 1.875063e-07 | architectural | upper | True |
| `V4` | 343/768 | 9/32 | 127/768 | 1.577040e-07 | architectural | lower | True |
| `V5` | 128/375 | 9/32 | 721/12000 | 5.729993e-08 | architectural | upper | True |

## Replay

```bash
./ProofRefinement/PolygonPi/scripts/verify_all.sh
```

## Known limitation

Per-model-call token and dollar accounting is not obtainable from inside this harness, so cost reporting is wall-clock and Lean-compile CPU only.
