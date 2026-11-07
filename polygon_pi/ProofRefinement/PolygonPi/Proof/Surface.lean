/-
# The single trusted entry point

Candidates never import `PolygonCore.*` directly; they import
`ProofRefinement.PolygonPi.Proof.Main`, which reaches the trusted surface
through this re-export. Keeping one entry point means the trusted surface can be
audited by reading a single import list.

Everything reachable from here is read-only to the refinement loop.
-/
import PolygonCore.Polygon
import PolygonCore.LowerBound
