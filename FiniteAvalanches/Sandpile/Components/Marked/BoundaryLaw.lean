import FiniteAvalanches.Sandpile.Components.Marked.Events
import FiniteAvalanches.Sandpile.Components.Marked.Boundary

/-! The shape-only marked law uses every induced boundary vertex, including the
root coordinate in the carrier. Its exclusion from the boundary is proved from
N[o] ⊆ S ⊆ C; degree is the actual original-copy induced degree. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem core_shape_full_boundary_contact {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
  letI := inner_tree_nonempty_of_core C
  have he : {t : (inducedGraph (insideSupport C)).SpanningTree |
      ∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)} =
      {t | ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)} := by
    ext t
    exact marked_boundary_contact_iff C S hS hN t
  rw [← he]
  exact core_shape_marked_omission C hc S hS hN

/-- Exact real event probability, on the same complete finite carriers. -/
theorem core_shape_full_boundary_contact_toReal {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    (ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C}).toReal =
    ((inducedGraph (insideSupport C)).treeLaw
      {t | ∃ v : insideSupport C, Burning.degree (inducedGraph (insideSupport C)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)}).toReal :=
  congrArg ENNReal.toReal (core_shape_full_boundary_contact C hc S hS hN)

end
end FiniteAvalanches.Sandpile.Components.Marked
