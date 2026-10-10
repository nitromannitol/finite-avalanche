import FiniteAvalanches.Sandpile.Components.Marked.Sites
import FiniteAvalanches.Sandpile.Components.HeldPastLaw

/-! Actual lattice marked containment under conditioning only on core shape.
The finite fiber remains complete and retains the original recurrent denominator.
An impossible fiber has zero conditional measure; tree probability is formed only
once an actual core field proves that its induced tree carrier is populated. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem nonempty_core_of_mass_ne_zero {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) :
    Nonempty (CoreField o C.val) := by
  by_contra hn
  letI : IsEmpty (CoreField o C.val) := not_nonempty_iff.mp hn
  apply hc
  rw [punctured_counting_apply]
  change (Nat.card (CoreField o C.val) : ℝ≥0∞) / Fintype.card (FiniteWired.Recurrent N) = 0
  rw [Nat.card_of_isEmpty, Nat.cast_zero, ENNReal.zero_div]

/-- Both omission and containment, on every complete finite field/tree fiber. -/
theorem core_uniform_marked_event {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)]
    [LinearOrder (InducedEdge (insideSupport C))] (S : Finset Site2)
    (hS : S ⊆ C.val) (ho : FiniteWired.site o ∈ S) (q : Bool) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    FiniteAvalanches.uniformMeasure (CoreField o C.val)
      {h | decide (¬ S ⊆ heldInterior h.val.val C) = q} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | decide (∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)) = q} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI := inner_tree_nonempty_of_core C
  let event : Set (Finset (insideSupport C)) :=
    {T | decide (∃ v ∈ markedVertices C S, v ∈ T) = q}
  have he := congrArg (fun μ : Measure (Finset (insideSupport C)) => μ event)
    (core_shape_held_past_law C (boundaryVertices C))
  rw [Measure.map_apply (measurable_of_finite _) (by trivial),
    Measure.map_apply (measurable_of_finite _) (by trivial)] at he
  have hf : (fun h : CoreField o C.val =>
      (Burning.heldBurning (inducedGraph (insideSupport C))
        (Finset.univ.erase (innerRoot C)) (coreGraphFieldEquiv C h).2.val
        (boundaryVertices C)).image Subtype.val) ⁻¹' event =
      {h | decide (¬ S ⊆ heldInterior h.val.val C) = q} := by
    ext h
    change (decide (∃ v ∈ markedVertices C S,
      v ∈ (Burning.heldBurning (inducedGraph (insideSupport C))
        (Finset.univ.erase (innerRoot C)) (coreGraphFieldEquiv C h).2.val
        (boundaryVertices C)).image Subtype.val) = q) ↔ _
    simp only [← marked_omitted_iff_stop_meets C h S hS]
    rfl
  have ht : (fun t : (inducedGraph (insideSupport C)).SpanningTree =>
      Burning.canonicalPastUnion (inducedGraph (insideSupport C)) (innerRoot C)
        t (boundaryVertices C)) ⁻¹' event =
      {t | decide (∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)) = q} := by
    ext t
    change (decide (∃ v ∈ markedVertices C S, v ∈ Burning.canonicalPastUnion
      (inducedGraph (insideSupport C)) (innerRoot C) t (boundaryVertices C)) = q) ↔ _
    simp only [past_meets_marked_iff_boundary_span C S ho t]
    rfl
  rw [hf,ht] at he
  exact he

/-- Shape is the entire conditioning event, with no wave transition restriction. -/
theorem core_shape_marked_event {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [LinearOrder (InducedEdge (insideSupport C))]
    (hc : puncturedCountingMeasure o (coreEvent C) ≠ 0) (S : Finset Site2)
    (hS : S ⊆ C.val) (ho : FiniteWired.site o ∈ S) (q : Bool) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | decide (¬ S ⊆ heldInterior h.val C) = q} =
    (inducedGraph (insideSupport C)).treeLaw
      {t | decide (∃ b ∈ boundaryVertices C,
        b.val ∈ (inducedGraph (insideSupport C)).span t (markedVertices C S)) = q} := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI : Nonempty (CoreField o C.val) := nonempty_core_of_mass_ne_zero C hc
  letI := inner_tree_nonempty_of_core C
  rw [← core_shape_conditioning C,
    Measure.map_apply (measurable_of_finite _) (by trivial)]
  exact core_uniform_marked_event C S hS ho q

/-- Impossible/disconnected actual shape fibers stay zero, without a fake tree law. -/
theorem zero_core_shape_marked_event {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (hc : puncturedCountingMeasure o (coreEvent C) = 0)
    (S : Finset Site2) (q : Bool) :
    ProbabilityTheory.cond (puncturedCountingMeasure o) (coreEvent C)
      {h | decide (¬ S ⊆ heldInterior h.val C) = q} = 0 := by
  rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hc]
  rfl

end
end FiniteAvalanches.Sandpile.Components.Marked
