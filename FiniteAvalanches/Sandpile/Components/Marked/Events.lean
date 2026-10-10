import FiniteAvalanches.Sandpile.Components.Marked.Law

/-! Literal omission and containment probabilities for the paper's finite marked S.
Its source membership follows from N[o] ⊆ S. Only actual core shape is conditioned on. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem core_shape_marked_omission {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | ∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
  letI := inner_tree_nonempty_of_core C
  simpa only [decide_eq_true_eq] using core_shape_marked_event C hc S hS
    (hN (Finset.mem_insert_self _ _)) true

theorem core_shape_marked_containment {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | S ⊆ heldInterior h.val C} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | ¬ ∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
  letI := inner_tree_nonempty_of_core C
  simpa only [decide_eq_false_iff_not, not_not] using core_shape_marked_event C hc S hS
    (hN (Finset.mem_insert_self _ _)) false

/-- The real probability agrees with the same literal tree event. -/
theorem core_shape_marked_omission_toReal {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ S) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    (ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C}).toReal =
    ((inducedGraph (insideSupport C)).treeLaw
      {t | ∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)}).toReal := by
  exact congrArg ENNReal.toReal (core_shape_marked_omission C hc S hS hN)

/-- Zero fibers retain zero for both literal events, for every marked set. -/
theorem zero_core_shape_omission_containment {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (hc : puncturedCountingMeasure o (coreEvent C) = 0)
    (S : Finset Site2) :
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | ¬ S ⊆ heldInterior h.val C} = 0 ∧
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | S ⊆ heldInterior h.val C} = 0 := by
  rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hc]
  exact ⟨rfl,rfl⟩

end
end FiniteAvalanches.Sandpile.Components.Marked
