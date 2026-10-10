import FiniteAvalanches.Sandpile.Components.FiberMeasure
import FiniteAvalanches.Sandpile.Components.Supports

/-! The positive tree range in the reciprocal count is exactly the populated
whole-core range in the original-normalized omission sum. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section
variable {N : ℕ} {o : FiniteWired.Active N}

theorem core_nonempty_iff_component_trees (C : ComponentShape o) :
    Nonempty (CoreField o C.val) ↔ Nonempty (InnerTrees C) ∧ Nonempty (OuterTrees C) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨(coreTreeEquiv C h).2⟩, ⟨(coreTreeEquiv C h).1⟩⟩
  · rintro ⟨⟨i⟩, ⟨d⟩⟩
    exact ⟨(coreTreeEquiv C).symm (d, i)⟩

theorem core_nonempty_iff_tree_cards (C : ComponentShape o) :
    Nonempty (CoreField o C.val) ↔
      0 < Fintype.card (InnerTrees C) ∧ 0 < Fintype.card (OuterTrees C) := by
  rw [core_nonempty_iff_component_trees, Fintype.card_pos_iff, Fintype.card_pos_iff]

theorem core_empty_iff_tree_card_zero (C : ComponentShape o) :
    IsEmpty (CoreField o C.val) ↔
      Fintype.card (InnerTrees C) = 0 ∨ Fintype.card (OuterTrees C) = 0 := by
  rw [← not_nonempty_iff, core_nonempty_iff_tree_cards]
  omega

/-- Every populated actual core shape containing the actual finite marked set. -/
abbrev PopulatedMarkedCoreShape (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) :=
  {C : PopulatedCoreShape o // markedSites S ⊆ C.val.val}

/-- Both inverse maps retain the literal shape, not a selected family of fields. -/
def populatedMarkedPositiveEquiv (S : Finset (FiniteWired.Active N)) :
    PopulatedMarkedCoreShape o S ≃ PositiveCoreShape o S where
  toFun C := ⟨C.val.val, C.property,
    (core_nonempty_iff_tree_cards C.val.val).mp C.val.property⟩
  invFun C := ⟨⟨C.val, (core_nonempty_iff_tree_cards C.val).mpr C.property.2⟩, C.property.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- Removing the false marked-subset branches retains exactly populated marked fibers. -/
theorem normalized_held_omissions_eq_marked_fibers (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) :
    (∑ g : Punctured N o,
      (if markedSites S ⊆ core g.val ∧
        ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
      Fintype.card (FiniteWired.Recurrent N) =
      ∑ C : PopulatedMarkedCoreShape o S,
        (puncturedCountingMeasure o).real (coreEvent C.val.val) *
          (coreFiberLaw C.val).real {g | ¬markedSites S ⊆ heldInterior g.val.val C.val.val} := by
  rw [normalized_held_omissions_eq_core_probabilities]
  apply Finset.sum_congr_set {C : PopulatedCoreShape o | markedSites S ⊆ C.val.val}
  · intro C hC
    exact if_pos (show markedSites S ⊆ C.val.val from hC)
  · intro C hC
    exact if_neg (show ¬markedSites S ⊆ C.val.val from hC)

/-- The normalized actual omission sum has exactly the manuscript's positive tree-count range.
The probability inside each summand still denotes a whole actual field fiber. -/
theorem normalized_held_omissions_eq_positive_tree_range (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) :
    (∑ g : Punctured N o,
      (if markedSites S ⊆ core g.val ∧
        ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) /
      Fintype.card (FiniteWired.Recurrent N) =
      ∑ C : PositiveCoreShape o S,
        (puncturedCountingMeasure o).real (coreEvent C.val) *
          (coreFiberLaw ((populatedMarkedPositiveEquiv S).symm C).val).real
            {g | ¬markedSites S ⊆ heldInterior g.val.val C.val} := by
  rw [normalized_held_omissions_eq_marked_fibers]
  exact (Equiv.sum_comp (populatedMarkedPositiveEquiv S).symm _).symm

/-- Zero tree fibers contribute actual zero core mass, with the original denominator unchanged. -/
theorem core_event_zero_of_empty_component (C : ComponentShape o)
    (h : Fintype.card (InnerTrees C) = 0 ∨ Fintype.card (OuterTrees C) = 0) :
    puncturedCountingMeasure o (coreEvent C) = 0 := by
  letI := (core_empty_iff_tree_card_zero C).mpr h
  rw [punctured_counting_apply]
  change (Nat.card (CoreField o C.val) : ℝ≥0∞) / _ = 0
  rw [Nat.card_of_isEmpty, Nat.cast_zero, ENNReal.zero_div]

end
end FiniteAvalanches.Sandpile.Components
