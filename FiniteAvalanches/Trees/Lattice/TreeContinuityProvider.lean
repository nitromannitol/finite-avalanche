import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability
import FiniteAvalanches.Trees.Lattice.ReciprocalExpectationLimit
import FiniteAvalanches.Trees.Lattice.FixedCutProbabilityLimit

set_option autoImplicit false
open LatticeProb MeasureTheory Filter
open scoped Classical ENNReal
open TreeMeasurability11 FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice

namespace JointTreeContinuity

/-- Joint expectation and fixed-edge cut continuity for the wired uniform spanning tree. -/
theorem tree_continuity :
    (∀ (S : Finset (Site 2)) (hS : S.Nonempty),
      Tendsto (fun N : ℕ => ∫ t, finiteZN N S hS t ∂WiredTrees.law N) atTop
        (nhds (∫ T, infiniteReciprocal S hS T ∂endedUST))) ∧
    (∀ (o : Site 2) (f : LatticeEdge) (M : ℕ),
      Tendsto (fun N : ℕ => (WiredTrees.law N) (finiteCutEscape o f M N)) atTop
        (nhds (endedUST (infiniteCutEscape o f M)))) :=
  ⟨fun S hS => ReciprocalLimit15.actual_reciprocal_expectation_limit S hS,
    fun o f M => FixedCutLimit12.actual_fixed_cut_probability_limit o f M⟩

end JointTreeContinuity
