import FiniteAvalanches.Sandpile.Components.Marked.ContactLaw
import FiniteAvalanches.Sandpile.Waves.HeldEventBound

/-! Complete finite legal avalanches admit the actual reciprocal estimate with
the large-wave omission error. The error retains the original counting mass;
its edge-insertion bound and infinite-volume passage are separate obligations. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The entire actual held-omission count is the ordinary-tree reciprocal expectation. -/
theorem normalized_held_omissions_eq_reciprocal {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (∑ g : Punctured N o,
      (if markedSites S ⊆ core g.val ∧
        ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
      Fintype.card (FiniteWired.Recurrent N) =
    ∫ t, WiredTrees.reciprocal N (markedVertices S)
      (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
      ∂WiredTrees.law N := by
  rw [normalized_held_omissions_eq_positive_tree_range,
    integral_reciprocal_eq_core_mass S (Marked.source_mem_of_marked_neighbors S hN)]
  apply Finset.sum_congr rfl
  intro C _
  rw [Marked.core_fiber_omission_real_eq_component_contact S C hN]

/-- Any punctured event keeps the original recurrent denominator, rather than its own total mass. -/
theorem punctured_counting_real_eq_normalized_sum {N : ℕ} (o : FiniteWired.Active N)
    (A : Set (Punctured N o)) :
    (puncturedCountingMeasure o).real A =
      (∑ g : Punctured N o, (if g ∈ A then 1 else 0 : ℝ)) /
        Fintype.card (FiniteWired.Recurrent N) := by
  change (puncturedCountingMeasure o A).toReal = _
  rw [punctured_counting_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.sum_boole _ _).symm

/-- The actual inverse transition count is bounded without conditioning on that transition. -/
theorem normalized_inverse_transitions_le_reciprocal {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (∑ g : Punctured N o,
      (if ¬markedSites S ⊆ core g.val ∧ markedSites S ⊆ core (inverse g).val
        then 1 else 0 : ℝ)) / Fintype.card (FiniteWired.Recurrent N) ≤
      ∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N := by
  have ht : (∑ h : Punctured N o,
      (if ¬markedSites S ⊆ core h.val ∧ markedSites S ⊆ core (inverse h).val
        then 1 else 0 : ℝ)) ≤
      ∑ g : Punctured N o,
        (if markedSites S ⊆ core g.val ∧
          ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ) := by
    let q : Punctured N o → ℝ := fun h =>
      if ¬markedSites S ⊆ core h.val ∧ markedSites S ⊆ core (inverse h).val then 1 else 0
    change (∑ h : Punctured N o, q h) ≤ _
    calc
      _ = ∑ g : Punctured N o, q (forward g) := (waveEquiv.sum_comp q).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro g _
        dsimp only [q]
        rw [inverse_forward]
        by_cases hg : ¬markedSites S ⊆ core (forward g).val ∧ markedSites S ⊆ core g.val
        · have hb : markedSites S ⊆ core g.val ∧
            ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) :=
            ⟨hg.2, fun h => hg.1 (h.trans (held_interior_subset_core_forward g _))⟩
          rw [if_pos hg, if_pos hb]
        · rw [if_neg hg]
          positivity
  calc
    _ ≤ (∑ g : Punctured N o,
        (if markedSites S ⊆ core g.val ∧
          ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
        Fintype.card (FiniteWired.Recurrent N) :=
      div_le_div_of_nonneg_right ht (Nat.cast_nonneg _)
    _ = _ := normalized_held_omissions_eq_reciprocal o S hN

/-- The bounded finite estimate uses the complete avalanche and the exact large-wave error. -/
theorem finite_avalanche_leaves_probability_le_reciprocal {N : ℕ}
    (o : FiniteWired.Active N) (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (FiniteWired.law N).real {η | finiteAvalancheLeaves o B η} ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N) +
      (∑ g : Punctured N o,
        (if ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) := by
  have h := finite_avalanche_leaves_probability_le_held o (markedSites S) B
    (fun x hx => hN (Finset.mem_insert_of_mem hx))
  rw [add_div, normalized_held_omissions_eq_reciprocal o S hN] at h
  exact h

/-- The same error is the literal large-core omission event under the non-probability measure. -/
theorem finite_avalanche_leaves_probability_le_reciprocal_add_omission {N : ℕ}
    (o : FiniteWired.Active N) (S : Finset (FiniteWired.Active N)) (B : Finset Site2)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (FiniteWired.law N).real {η | finiteAvalancheLeaves o B η} ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N) +
      (puncturedCountingMeasure o).real
        {g | ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B} := by
  rw [punctured_counting_real_eq_normalized_sum]
  convert finite_avalanche_leaves_probability_le_reciprocal o S B hN using 1
  congr 2
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ¬markedSites S ⊆ core g.val ∧ ¬core g.val ⊆ B
  · simp only [Set.mem_setOf_eq, hg]
  · simp only [Set.mem_setOf_eq, hg, if_false]

end
end FiniteAvalanches.Sandpile.Waves
