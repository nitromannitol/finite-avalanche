import FiniteAvalanches.Paper.Providers.OutflowProvider

namespace FiniteAvalanches.Paper.SectionThree
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem outflow {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (puncturedCountingMeasure o).real
      {g | ¬markedSites S ⊆ core g.val ∧ markedSites S ⊆ core (inverse g).val} ≤
    ∑ C : PositiveCoreShape o S,
      (puncturedCountingMeasure o).real (coreEvent C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)) := by
  exact FiniteAvalanches.SourceFinite.outflow_le_component_contact o S hN

end
end FiniteAvalanches.Paper.SectionThree
