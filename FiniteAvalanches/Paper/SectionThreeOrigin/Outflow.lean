import FiniteAvalanches.Paper.SectionThree.Outflow
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Paper.SectionThreeOrigin
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem outflow_origin {N : ℕ}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S) :
    (puncturedCountingMeasure (origin N)).real
      {g | ¬markedSites S ⊆ core g.val ∧ markedSites S ⊆ core (inverse g).val} ≤
    ∑ C : PositiveCoreShape (origin N) S,
      (puncturedCountingMeasure (origin N)).real (coreEvent C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)) := by
  exact FiniteAvalanches.Paper.SectionThree.outflow (origin N) S hN

end
end FiniteAvalanches.Paper.SectionThreeOrigin
