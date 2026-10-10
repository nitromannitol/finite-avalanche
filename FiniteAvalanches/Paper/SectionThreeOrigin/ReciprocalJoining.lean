import FiniteAvalanches.Paper.SectionThree.ReciprocalJoining
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Paper.SectionThreeOrigin
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem reciprocal_joining_origin {N : ℕ}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S) :
    (∀ (C : PositiveCoreShape (origin N) S) (t : InnerTrees C.val),
      (WiredTrees.law N).real {u | ∃ hne :
        (WiredTrees.graph N).ancestorOf u none (markedVertices S)
          (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) ≠ none,
        (WiredTrees.graph N).past u none
          ((WiredTrees.graph N).ancestorOf u none (markedVertices S)
            (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN))) hne =
            insideSupport C.val ∧
        (WiredTrees.graph N).internalEdges (insideSupport C.val) u.val = t.val} =
      (Fintype.card (OuterTrees C.val) : ℝ) / Fintype.card (FiniteWired.Recurrent N) *
        (∑ v ∈ ((WiredTrees.graph N).componentSpan t (markedVertices S)
          ((marked_subset_iff S C.val).mp C.property.1)).toFinset,
          ((WiredTrees.graph N).crossingAt (insideSupport C.val) v).card)) ∧
    (∑ C : PositiveCoreShape (origin N) S,
      (puncturedCountingMeasure (origin N)).real (coreEvent C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C))) =
      ∫ u, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) u
        ∂WiredTrees.law N := by
  exact FiniteAvalanches.Paper.SectionThree.reciprocal_joining (origin N) S hN

end
end FiniteAvalanches.Paper.SectionThreeOrigin
