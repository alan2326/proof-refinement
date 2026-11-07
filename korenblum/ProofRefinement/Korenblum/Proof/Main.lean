import ProofRefinement.Korenblum.Proof.CandidateContract
import ProofRefinement.Korenblum.Proof.Reduction

/-!
# Korenblum Proof Tail

The Korenblum harness keeps the downstream proof tail minimal.

- `CandidateContract.lean` defines the final theorem shape.
- `Reduction.lean` proves one generic paper-faithful bridge from Wang's
  equation `(15)` to the final disk-vs-annulus statement.

Candidates are expected to export the final theorem directly, so this file is a
lightweight entrypoint rather than a large post-processing layer. The `(15)`
bridge is a convenience for the seed route, not a restriction on future
candidates.
-/
