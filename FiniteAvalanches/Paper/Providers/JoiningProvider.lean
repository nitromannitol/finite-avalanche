import FiniteAvalanches.Sandpile.Components.Marked.ContactLaw
import FiniteAvalanches.Sandpile.Components.TreeMass
import FiniteAvalanches.Sandpile.TreeLaw

namespace FiniteAvalanches.SourceFinite
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem reciprocal_joining_probability {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S)
    (C : PositiveCoreShape o S) (t : InnerTrees C.val) :
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
        ((WiredTrees.graph N).crossingAt (insideSupport C.val) v).card) := by
  rw [card_original_recurrent_eq_treeCount]
  have h := WiredTrees.joining_probability_past N (insideSupport C.val) (markedVertices S)
    (show none ∉ insideSupport C.val by simp [insideSupport, insideVertex])
    (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN))
    ((marked_subset_iff S C.val).mp C.property.1) t
  rw [inside_complement] at h
  exact h

theorem reciprocal_joining_identity {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (∑ C : PositiveCoreShape o S,
      (puncturedCountingMeasure o).real (coreEvent C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C))) =
    ∫ u, WiredTrees.reciprocal N (markedVertices S)
      (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) u
      ∂WiredTrees.law N :=
  (integral_reciprocal_eq_core_mass S (Marked.source_mem_of_marked_neighbors S hN)).symm

theorem reciprocal_joining {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (∀ (C : PositiveCoreShape o S) (t : InnerTrees C.val),
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
    (∑ C : PositiveCoreShape o S,
      (puncturedCountingMeasure o).real (coreEvent C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C))) =
      ∫ u, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) u
        ∂WiredTrees.law N :=
  ⟨reciprocal_joining_probability o S hN, reciprocal_joining_identity o S hN⟩

end
end FiniteAvalanches.SourceFinite
