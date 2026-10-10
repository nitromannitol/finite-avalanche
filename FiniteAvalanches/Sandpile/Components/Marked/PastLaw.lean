import FiniteAvalanches.Sandpile.Components.Marked.Events

/-! Literal contact with the full uniform vertex-past union, conditioned only
on actual core shape. Source membership follows from the paper's marked neighborhood. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem core_shape_marked_past_event {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S)
    (q : Bool) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | decide (¬ S ⊆ heldInterior h.val C) = q} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | decide (∃ v ∈ markedVertices C S,
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C))
          (innerRoot C) t (boundaryVertices C)) = q} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
  letI := inner_tree_nonempty_of_core C
  have ho : FiniteWired.site o ∈ S := hN (Finset.mem_insert_self _ _)
  have he : {t : (inducedGraph (insideSupport C)).SpanningTree |
      decide (∃ v ∈ markedVertices C S,
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C))
          (innerRoot C) t (boundaryVertices C)) = q} =
      {t | decide (∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)) = q} := by
    ext t
    change (decide (∃ v ∈ markedVertices C S,
      v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C))
        (innerRoot C) t (boundaryVertices C)) = q) ↔ _
    simp only [past_meets_marked_iff_boundary_span C S ho t]
    rfl
  rw [he]
  exact core_shape_marked_event C hc S hS ho q

theorem core_shape_marked_past_omission {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | ∃ v ∈ markedVertices C S,
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C))
          (innerRoot C) t (boundaryVertices C)} := by
  simpa only [decide_eq_true_eq] using core_shape_marked_past_event C hc S hS hN true

theorem core_shape_marked_past_containment {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | S ⊆ heldInterior h.val C} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | ¬ ∃ v ∈ markedVertices C S,
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C))
          (innerRoot C) t (boundaryVertices C)} := by
  simpa only [decide_eq_false_iff_not, not_not] using core_shape_marked_past_event C hc S hS hN false

end
end FiniteAvalanches.Sandpile.Components.Marked
