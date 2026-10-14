import FiniteAvalanches.Sandpile.Components.CurrentShapeTwoForest
import FiniteAvalanches.Sandpile.Components.Marked.ContactLaw
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

/-! The current outflow proof counts whole shape fibers, uses held burning,
and weights the copied-tree completions by the reciprocal contact count. -/

namespace FiniteAvalanches.Paper.CurrentOutflow

open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.Components.CurrentShapeTwoForest
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem integral_reciprocal_eq_current_shape_mass {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) :
    (∫ t, WiredTrees.reciprocal N (markedVertices S) (marked_vertices_nonempty S ho) t
      ∂WiredTrees.law N) =
      ∑ C : PositiveCoreShape o S,
        (puncturedCountingMeasure o).real (coreEvent C.val) *
          ((WiredTrees.graph N).componentLaw (positiveSupportEquiv S ho C)).real
            ((WiredTrees.graph N).insideContact (positiveSupportEquiv S ho C)) := by
  rw [WiredTrees.reciprocal_identity]
  rw [← Equiv.sum_comp (positiveSupportEquiv S ho)]
  apply Finset.sum_congr rfl
  intro C _
  rw [core_event_tree_mass_compl_current]
  rfl

theorem normalized_held_omissions_eq_reciprocal_current {N : ℕ} (o : FiniteWired.Active N)
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
    integral_reciprocal_eq_current_shape_mass S (Marked.source_mem_of_marked_neighbors S hN)]
  apply Finset.sum_congr rfl
  intro C _
  rw [Marked.core_fiber_omission_real_eq_component_contact S C hN]

/-- Every missed mark is in the final unburned set, since the burned part topples. -/
theorem forward_outflow_sum_le_held_sum {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset Site2) :
    (∑ g : Punctured N o,
      (if S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val then 1 else 0 : ℝ)) ≤
      ∑ g : Punctured N o,
        (if S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ) := by
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val
  · have hh : S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val) :=
      ⟨hg.1, fun hs => hg.2 (hs.trans (held_interior_subset_core_forward g _))⟩
    rw [if_pos hg, if_pos hh]
  · rw [if_neg hg]
    split_ifs <;> norm_num

/-- Exact current outflow statement on the original punctured and wired-tree carriers. -/
theorem outflow_card_le_treeCount_mul_reciprocal {N : ℕ}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S) :
    (Nat.card {g : Punctured N (origin N) //
      markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, WiredTrees.reciprocal N (markedVertices S)
          (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
          ∂WiredTrees.law N := by
  have hforward :
      (∑ g : Punctured N (origin N),
        (if markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val
          then 1 else 0 : ℝ)) / Fintype.card (FiniteWired.Recurrent N) ≤
      ∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N := by
    calc
      _ ≤ (∑ g : Punctured N (origin N),
          (if markedSites S ⊆ core g.val ∧
            ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) :=
        div_le_div_of_nonneg_right (forward_outflow_sum_le_held_sum (origin N) (markedSites S))
          (Nat.cast_nonneg _)
      _ = _ := normalized_held_omissions_eq_reciprocal_current (origin N) S hN
  have hcard :
      (∑ g : Punctured N (origin N),
        (if markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val
          then 1 else 0 : ℝ)) =
      (Nat.card {g : Punctured N (origin N) //
        markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val} : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.sum_boole _ _
  rw [hcard] at hforward
  have hden : (0 : ℝ) < Fintype.card (FiniteWired.Recurrent N) := by
    exact_mod_cast Fintype.card_pos
  have hraw := (div_le_iff₀ hden).mp hforward
  rw [card_original_recurrent_eq_treeCount] at hraw
  simpa only [mul_comm] using hraw

end
end FiniteAvalanches.Paper.CurrentOutflow
