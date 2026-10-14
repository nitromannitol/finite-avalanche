import FiniteAvalanches.Sandpile.Components.ShapeInjection
import FiniteAvalanches.Paper.Current.GuardedOutflow

/-! The outflow bound from forward restriction and the held-burning count. -/
namespace FiniteAvalanches.Paper.InjectionOutflow
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.Components.ShapeInjection
open FiniteAvalanches.Sandpile.SourceCounting
open TreeMeasurability11 TreeMeasurability11.CurrentDomain
open scoped Classical BigOperators ENNReal
noncomputable section

theorem normalized_held_omissions_le_reciprocal {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (∑ g : Punctured N o,
      (if markedSites S ⊆ core g.val ∧
        ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
      Fintype.card (FiniteWired.Recurrent N) ≤
    ∫ t, WiredTrees.reciprocal N (markedVertices S)
      (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
      ∂WiredTrees.law N := by
  rw [sum_held_omissions_eq_positive, Finset.sum_div,
    WiredTrees.reciprocal_identity,
    ← Equiv.sum_comp (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN))]
  apply Finset.sum_le_sum
  intro C _
  have hi := div_le_div_of_nonneg_right (card_held_missing_le_tree_weight S C hN)
    (Nat.cast_nonneg (Fintype.card (FiniteWired.Recurrent N)) : (0 : ℝ) ≤ _)
  rw [card_original_recurrent_eq_treeCount] at hi
  have hout :
      Fintype.card ((WiredTrees.graph N).ComponentTree
        ((positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C).val)ᶜ) =
      Fintype.card (OuterTrees C.val) := by
    change Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport C.val)ᶜ) = _
    rw [inside_complement]
  have hin :
      Fintype.card ((WiredTrees.graph N).ComponentTree
        ((positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C).val)) =
      Fintype.card (InnerTrees C.val) := rfl
  rw [card_original_recurrent_eq_treeCount, hout, hin]
  convert hi using 1; ring

/-- The same current outflow type, now consuming a restriction injection. -/
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
        div_le_div_of_nonneg_right
          (CurrentOutflow.forward_outflow_sum_le_held_sum (origin N) (markedSites S))
          (Nat.cast_nonneg _)
      _ ≤ _ := normalized_held_omissions_le_reciprocal (origin N) S hN
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

theorem outflow_le_guarded_source_reciprocal {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) :
    (Nat.card {g : Punctured N (origin N) //
      sourceMarks r ⊆ core g.val ∧ ¬sourceMarks r ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N := by
  have h := outflow_card_le_treeCount_mul_reciprocal
    (activeMarks N r) (marked_neighborhood hr hrN)
  rw [markedSites_activeMarks hr hrN] at h
  have he :
      (fun t => WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _
          (Marked.source_mem_of_marked_neighbors _ (marked_neighborhood hr hrN))) t) =
      (fun t => sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t) := by
    funext t
    exact (FiniteAvalanches.Sandpile.Source.finite_reciprocal_eq_finiteZN hr hrN t).trans
      (sourceFiniteReciprocal_eq_auxiliary N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t).symm
  rw [he] at h
  exact h

end
end FiniteAvalanches.Paper.InjectionOutflow
