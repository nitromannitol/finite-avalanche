import FiniteAvalanchesProofs.TreeContinuity
import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability

set_option autoImplicit false
open LatticeProb MeasureTheory Filter
open scoped Classical ENNReal
open TreeMeasurability11 FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice

namespace FiniteAvalanches.Trees.Lattice.Source

/-- Joint expectation and fixed-edge cut continuity for the wired uniform spanning tree. -/
theorem tree_continuity :
    (∀ (S : Finset (Site 2)) (hS : S.Nonempty),
      Tendsto (fun N : ℕ => ∫ t, finiteZN N S hS t ∂WiredTrees.law N) atTop
        (nhds (∫ T, infiniteReciprocal S hS T ∂endedUST))) ∧
    (∀ (o : Site 2) (f : LatticeEdge) (M : ℕ),
      Tendsto (fun N : ℕ => (WiredTrees.law N) (finiteCutEscape o f M N)) atTop
        (nhds (endedUST (infiniteCutEscape o f M)))) := by
  exact FiniteAvalanchesProofs.TreeContinuity.tree_continuity

end FiniteAvalanches.Trees.Lattice.Source
