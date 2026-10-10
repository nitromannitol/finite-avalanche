import FiniteAvalanches.Sandpile.Waves.ReciprocalBound

namespace FiniteAvalanches.SourceFinite
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem outflow_le_component_contact {N : ℕ} (o : FiniteWired.Active N)
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
  rw [punctured_counting_real_eq_normalized_sum]
  have h := normalized_inverse_transitions_le_reciprocal o S hN
  rw [integral_reciprocal_eq_core_mass S
    (Marked.source_mem_of_marked_neighbors S hN)] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ¬markedSites S ⊆ core g.val ∧ markedSites S ⊆ core (inverse g).val
  all_goals simp only [Set.mem_setOf_eq, hg, if_false]

end
end FiniteAvalanches.SourceFinite
