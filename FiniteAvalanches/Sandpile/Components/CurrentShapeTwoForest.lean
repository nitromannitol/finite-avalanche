import FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction
import FiniteAvalanches.Trees.TwoForestPairing
import FiniteAvalanches.Sandpile.Components.FiberMeasure
import FiniteAvalanches.Sandpile.Components.TreeMass

/-! The current shape-mass identity counts the actual rooted two-forests by
restricting the sandpile, applying both burning maps, and uniting the copied edges. -/

namespace FiniteAvalanches.Sandpile.Components.CurrentShapeTwoForest

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction MeasureTheory
open scoped Classical ENNReal
noncomputable section

abbrev ShapeTwoForest {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (WiredTrees.graph N).TwoForestOn (insideSupport C) (some o) none

/-- The source-containing shape and the canonical sink give the two actual roots. -/
def shapeTreePairEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerTrees C × OuterTrees C ≃ ShapeTwoForest C := by
  let e : OuterTrees C ≃ (WiredTrees.graph N).ComponentTree (insideSupport C)ᶜ :=
    Equiv.subtypeEquivRight (fun _ => by rw [inside_complement C])
  exact (Equiv.prodCongr (Equiv.refl (InnerTrees C)) e).trans
    ((WiredTrees.graph N).componentTreePairEquiv C.property.2
      (show none ∉ insideSupport C from False.elim))

theorem shape_tree_pair_edges {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (p : InnerTrees C × OuterTrees C) :
    (shapeTreePairEquiv C p).val = p.1.val ∪ p.2.val := rfl

theorem shape_tree_pair_first_component {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (p : InnerTrees C × OuterTrees C) (x : FiniteWired.Vertex N) :
    (WiredTrees.graph N).reaches (shapeTreePairEquiv C p).val x (some o) ↔
      x ∈ insideSupport C := (shapeTreePairEquiv C p).property.2 x

theorem shape_tree_pair_second_component {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (p : InnerTrees C × OuterTrees C) (x : FiniteWired.Vertex N) :
    (WiredTrees.graph N).reaches (shapeTreePairEquiv C p).val x none ↔
      x ∈ outsideSupport C := by
  rw [← inside_complement C]
  exact (WiredTrees.graph N).twoForest_reaches_second_iff
    (show none ∉ insideSupport C from False.elim) (shapeTreePairEquiv C p) x

/-- Both literal field restrictions and burning maps are consumed before union. -/
def sourceShapeForestEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    CoreField o C.val ≃ ShapeTwoForest C :=
  (sourceTreeEquiv C).trans (shapeTreePairEquiv C)

theorem card_shape_two_forests {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (ShapeTwoForest C) = Nat.card (InnerTrees C) * Nat.card (OuterTrees C) := by
  rw [← Nat.card_congr (shapeTreePairEquiv C), Nat.card_prod]

/-- The current shape count equals the number of actual two-component copied forests. -/
theorem card_core_eq_two_forest {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) = Nat.card (ShapeTwoForest C) :=
  Nat.card_congr (sourceShapeForestEquiv C)

/-- The current tree-product coefficient is recovered from the actual forest pairing. -/
theorem core_event_tree_mass_current {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) :
    (puncturedCountingMeasure o).real (coreEvent C) =
      (Fintype.card (InnerTrees C) : ℝ) * Fintype.card (OuterTrees C) /
        WiredTrees.treeCount N := by
  rw [core_event_real_eq_card, card_core_eq_two_forest C, card_shape_two_forests C,
    Nat.cast_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    card_original_recurrent_eq_treeCount]

theorem core_event_tree_mass_compl_current {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) :
    (puncturedCountingMeasure o).real (coreEvent C) =
      (Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport C)) : ℝ) *
        Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport C)ᶜ) /
          WiredTrees.treeCount N := by
  simpa only [inside_complement] using core_event_tree_mass_current C

end
end FiniteAvalanches.Sandpile.Components.CurrentShapeTwoForest
