import FiniteAvalanches.Sandpile.Components.BoundaryCopies
import FiniteAvalanches.Sandpile.Components.Marked.OriginalVertices

/-! Original-copy contact is first proved pointwise on the complete induced tree
carrier. Uniform measures are transported only after this predicate identity. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open scoped Classical
noncomputable section

theorem source_mem_of_marked_neighbors {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) : o ∈ S := by
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp (hN (Finset.mem_insert_self _ _))
  exact (FiniteWired.site_injective N he) ▸ hx

theorem inner_contact_iff_degree_contact {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset (FiniteWired.Active N)) (hS : markedSites S ⊆ C.val)
    (t : (inducedGraph (insideSupport C)).SpanningTree) :
    ((WiredTrees.graph N).admissibleEdges (insideSupport C)
      ((WiredTrees.graph N).componentSpan (innerInducedTreeEquiv C t)
        (Components.markedVertices S) ((marked_subset_iff S C).mp hS))).Nonempty ↔
      ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C)).span t (markedVertices C (markedSites S)) := by
  rw [admissible_nonempty_iff_degree_contact C _
    ((WiredTrees.graph N).componentSpan_subset (innerInducedTreeEquiv C t)
      (Components.markedVertices S) ((marked_subset_iff S C).mp hS)), original_marked_span C S hS t]
  constructor
  · rintro ⟨v,hd,w,hw,he⟩
    exact ⟨v,hd,(Subtype.ext he : w = v) ▸ hw⟩
  · rintro ⟨v,hd,hv⟩
    exact ⟨v,hd,v,hv,rfl⟩

theorem inside_contact_iff_degree_contact {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) (C : PositiveCoreShape o S)
    (t : (inducedGraph (insideSupport C.val)).SpanningTree) :
    innerInducedTreeEquiv C.val t ∈
      (WiredTrees.graph N).insideContact (positiveSupportEquiv S ho C) ↔
      ∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t (markedVertices C.val (markedSites S)) :=
  inner_contact_iff_degree_contact C.val S C.property.1 t

theorem inside_contact_preimage {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) (C : PositiveCoreShape o S) :
    (innerInducedTreeEquiv C.val) ⁻¹'
      (WiredTrees.graph N).insideContact (positiveSupportEquiv S ho C) =
      {t | ∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t (markedVertices C.val (markedSites S))} := by
  ext t
  exact inside_contact_iff_degree_contact S ho C t

end
end FiniteAvalanches.Sandpile.Components.Marked
