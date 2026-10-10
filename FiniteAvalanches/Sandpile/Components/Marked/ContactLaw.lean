import FiniteAvalanches.Sandpile.Components.Marked.InnerTreeLaw
import FiniteAvalanches.Trees.CertificateLaw
import FiniteAvalanches.Sandpile.Components.Marked.BoundaryLaw
import FiniteAvalanches.Sandpile.Components.PopulatedRange

/-! The literal whole core-fiber omission law equals original-copy component
contact. The source neighborhood derives source membership and exclusion from
the deficient-degree boundary. Only shape conditioning is used; the original
recurrent normalization remains in the supplied counting measure. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem core_fiber_omission_eq_component_contact {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (C : PositiveCoreShape o S)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    coreFiberLaw ((populatedMarkedPositiveEquiv S).symm C).val
      {g | ¬ markedSites S ⊆ heldInterior g.val.val C.val} =
    (WiredTrees.graph N).componentLaw
      (positiveSupportEquiv S (source_mem_of_marked_neighbors S hN) C)
      ((WiredTrees.graph N).insideContact
        (positiveSupportEquiv S (source_mem_of_marked_neighbors S hN) C)) := by
  let dE : DecidableEq (InducedEdge (insideSupport C.val)) := inferInstance
  letI : Nonempty (InnerTrees C.val) := Fintype.card_pos_iff.mp C.property.2.1
  let nf : Nonempty (@FiniteAvalanches.Trees.Multigraph.SpanningTree
      (insideSupport C.val) (InducedEdge (insideSupport C.val)) _ _ dE
      (inducedGraph (insideSupport C.val))) :=
    Nonempty.map (innerInducedTreeEquiv C.val).symm inferInstance
  letI : Nonempty (CoreField o C.val.val) :=
    (core_nonempty_iff_tree_cards C.val).mpr C.property.2
  letI : LinearOrder (InducedEdge (insideSupport C.val)) :=
    LinearOrder.lift' (Fintype.equivFin (InducedEdge (insideSupport C.val)))
      (Fintype.equivFin (InducedEdge (insideSupport C.val))).injective
  letI : DecidableEq (InducedEdge (insideSupport C.val)) := LinearOrder.toDecidableEq
  letI := inner_tree_nonempty_of_core C.val
  change FiniteAvalanches.uniformMeasure (CoreField o C.val.val)
    {g | ¬ markedSites S ⊆ heldInterior g.val.val C.val} = _
  have he := core_uniform_marked_event C.val (markedSites S) C.property.1
    (hN (Finset.mem_insert_self _ _)) true
  simp only [decide_eq_true_eq] at he
  have hb : {t : (inducedGraph (insideSupport C.val)).SpanningTree |
      ∃ b ∈ boundaryVertices C.val,
        b.val ∈ (inducedGraph (insideSupport C.val)).span t (markedVertices C.val (markedSites S))} =
      {t | ∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t (markedVertices C.val (markedSites S))} := by
    ext t
    exact marked_boundary_contact_iff C.val (markedSites S) C.property.1 hN t
  rw [hb] at he
  let A : Set (@FiniteAvalanches.Trees.Multigraph.SpanningTree
      (insideSupport C.val) (InducedEdge (insideSupport C.val)) _ _ dE
      (inducedGraph (insideSupport C.val))) :=
    {t | ∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
      v ∈ @FiniteAvalanches.Trees.Multigraph.span _ _ _ _ dE
        (inducedGraph (insideSupport C.val)) t (markedVertices C.val (markedSites S))}
  have hp := congrArg (fun μ => μ A)
    ((inducedGraph (insideSupport C.val)).tree_law_map_spanning_tree_decidable_equiv
      LinearOrder.toDecidableEq dE (nf := nf))
  rw [Measure.map_apply (measurable_of_finite _) (by trivial)] at hp
  have ha : ((inducedGraph (insideSupport C.val)).spanningTreeDecidableEquiv
      LinearOrder.toDecidableEq dE) ⁻¹' A =
      {t | ∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t (markedVertices C.val (markedSites S))} := by
    ext t
    change (∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
      v ∈ @FiniteAvalanches.Trees.Multigraph.span _ _ _ _ dE
        (inducedGraph (insideSupport C.val))
        ((inducedGraph (insideSupport C.val)).spanningTreeDecidableEquiv
          LinearOrder.toDecidableEq dE t) (markedVertices C.val (markedSites S))) ↔ _
    rw [FiniteAvalanches.Trees.Multigraph.spanning_tree_decidable_equiv_span]
    rfl
  rw [ha] at hp
  have ht := congrArg (fun μ => μ ((WiredTrees.graph N).insideContact
    (positiveSupportEquiv S (source_mem_of_marked_neighbors S hN) C)))
    (inner_induced_tree_law S (source_mem_of_marked_neighbors S hN) C)
  rw [Measure.map_apply (measurable_of_finite _) (by trivial),
    inside_contact_preimage S (source_mem_of_marked_neighbors S hN) C] at ht
  exact he.trans (hp.trans ht)

theorem core_fiber_omission_real_eq_component_contact {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (C : PositiveCoreShape o S)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (coreFiberLaw ((populatedMarkedPositiveEquiv S).symm C).val).real
      {g | ¬ markedSites S ⊆ heldInterior g.val.val C.val} =
    ((WiredTrees.graph N).componentLaw
      (positiveSupportEquiv S (source_mem_of_marked_neighbors S hN) C)).real
      ((WiredTrees.graph N).insideContact
        (positiveSupportEquiv S (source_mem_of_marked_neighbors S hN) C)) :=
  congrArg ENNReal.toReal (core_fiber_omission_eq_component_contact S C hN)

end
end FiniteAvalanches.Sandpile.Components.Marked
