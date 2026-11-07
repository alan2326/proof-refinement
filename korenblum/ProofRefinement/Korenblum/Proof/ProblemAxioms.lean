import KorenblumPaper.PaperAxioms
import KorenblumPaper.PaperEq15

/-!
# Problem Axioms Veneer

This file is only a thin convenience layer over the built
`KorenblumPaper.PaperAxioms` surface. It re-exports a few names used by
the current seed and contract so candidates can import a short, stable path.

It does **not** define the search space and it does **not** force candidates to
go through equation `(15)`. Candidates may prove
`ProofRefinement.Korenblum.ValidKorenblumBound c_value` by any route, subject
to the import policies recorded in `lemma.toml`.
-/

open MeasureTheory

noncomputable section

namespace ProofRefinement.Korenblum.ProblemAxioms

open KorenblumPaper

abbrev Eq15ScalarBound := PaperAxioms.Eq15ScalarBound
abbrev Section2Assumptions := PaperAxioms.Section2Assumptions
abbrev diskExcess := PaperAxioms.diskExcess
abbrev annulusExcess := PaperAxioms.annulusExcess

end ProofRefinement.Korenblum.ProblemAxioms
