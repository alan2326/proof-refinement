# Polygon-pi warm-up

The small end-to-end example from the paper: bracket pi between the
half-perimeter of the inscribed regular 2^(n+2)-gon plus lambda/4^n and plus
kappa/4^n, for every n, and make kappa - lambda small. There is no numerical
backend. Every constant is proved in Lean.

| Path | Contents |
| --- | --- |
| `PolygonCore/` | `polygonLower` and its two basic facts |
| `ProofRefinement/PolygonPi/Proof/` | the candidate contract and the trusted surface |
| `ProofRefinement/PolygonPi/Candidates/` | V0 to V5 of the primary run (Claude Sonnet 5, five sprints). V5 certifies kappa = 128/375, lambda = 9/32, score 721/12000 |
| `ProofRefinement/PolygonPi/Evaluator.py` | the evaluator (standard library only) |
| `results/` | frontier, summary, and telemetry of the primary run |
| `environment/` | tool-version fingerprints of the machine the run used |
| `comparison_run_opus5/` | candidates, contracts, verdicts, and notes of the comparison run with Claude Opus 5 as planner and generator (score 9816533/10^9) |

## Build and check

```bash
lake exe cache get
lake build
lake build ProofRefinement.PolygonPi.Candidates.V5
python3 ProofRefinement/PolygonPi/Evaluator.py --file ProofRefinement/PolygonPi/Candidates/V5.lean --no-log
```

The run's answer key (`validation-private/`, which the agents never saw) is not
included.
