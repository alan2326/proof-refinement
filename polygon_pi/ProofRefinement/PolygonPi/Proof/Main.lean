/-
# The one module candidates import

`Candidates/V<N>.lean` starts with

    import ProofRefinement.PolygonPi.Proof.Main

and nothing else from the project. Everything reachable from here is trusted and
read-only: the polygon definition, the trusted lower bound, the scored contract,
and the pinned benchmark interval.

The trusted surface is deliberately minimal: it fixes what the problem *is* and
supplies nothing that bears on how good a bound you can prove. No estimate of
any kind is provided here, and none will be added on request. Any lemma a
candidate needs is a lemma the candidate proves — in its own file, or in a
derived-theorem file under `Candidates/V<N>/`.
-/
import ProofRefinement.PolygonPi.Proof.Surface
import ProofRefinement.PolygonPi.Proof.CandidateContract
import ProofRefinement.PolygonPi.Proof.FixedDepth
