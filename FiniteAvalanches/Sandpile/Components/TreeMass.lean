import FiniteAvalanches.Sandpile.Components.Measure
import FiniteAvalanches.Sandpile.Components.Trees
import FiniteAvalanches.Sandpile.Components.WiredTrees
import FiniteAvalanches.Sandpile.TreeLaw

/-! The original recurrent-count denominator and the two actual component
allowed counts equal the corresponding copied-edge tree counts by proved maps.
The actual core event's counting measure therefore has the manuscript coefficient. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem card_original_recurrent_eq_treeCount (N : ℕ) :
    Fintype.card (FiniteWired.Recurrent N) = WiredTrees.treeCount N :=
  Fintype.card_congr (originalRecurrentTreeEquiv N)

theorem card_inner_graph_allowed_eq_trees {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : Nat.card (InnerGraphAllowed C) = Fintype.card (InnerTrees C) := by
  rw [Nat.card_congr (innerGraphTreeEquiv C), Nat.card_eq_fintype_card]

theorem card_outer_graph_allowed_eq_trees {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : Nat.card (OuterGraphAllowed C) = Fintype.card (OuterTrees C) := by
  rw [Nat.card_congr (outerGraphTreeEquiv C), Nat.card_eq_fintype_card]

/-- Every actual punctured atom has the original common mass tau_N inverse. -/
theorem punctured_counting_singleton_treeCount {N : ℕ} (o : FiniteWired.Active N)
    (h : Punctured N o) :
    puncturedCountingMeasure o {h} = (WiredTrees.treeCount N : ℝ≥0∞)⁻¹ := by
  rw [punctured_counting_singleton, card_original_recurrent_eq_treeCount]

theorem core_event_tree_mass {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    puncturedCountingMeasure o (coreEvent C) =
      (Fintype.card (InnerTrees C) : ℝ≥0∞) * Fintype.card (OuterTrees C) /
        WiredTrees.treeCount N := by
  rw [core_event_mass, card_inner_graph_allowed_eq_trees, card_outer_graph_allowed_eq_trees,
    card_original_recurrent_eq_treeCount, mul_comm]

theorem core_event_tree_mass_real {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (puncturedCountingMeasure o).real (coreEvent C) =
      (Fintype.card (InnerTrees C) : ℝ) * Fintype.card (OuterTrees C) /
        WiredTrees.treeCount N := by
  change (puncturedCountingMeasure o (coreEvent C)).toReal = _
  rw [core_event_tree_mass, ENNReal.toReal_div, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]

/-- The complement in the original vertex carrier includes canonical sink none. -/
theorem core_event_tree_mass_compl {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (puncturedCountingMeasure o).real (coreEvent C) =
      (Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport C)) : ℝ) *
        Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport C)ᶜ) /
          WiredTrees.treeCount N := by
  rw [inside_complement]
  exact core_event_tree_mass_real C

/-- Exact positive-support equivalence, with zero mass on disconnected components. -/
theorem core_event_mass_pos_iff {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    0 < (puncturedCountingMeasure o).real (coreEvent C) ↔
      0 < Fintype.card (InnerTrees C) ∧ 0 < Fintype.card (OuterTrees C) := by
  rw [core_event_tree_mass_compl]
  simpa only [inside_complement] using WiredTrees.product_mass_pos_iff N (insideSupport C)

end
end FiniteAvalanches.Sandpile.Components
