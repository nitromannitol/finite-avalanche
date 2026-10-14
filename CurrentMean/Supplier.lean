import CurrentMean.GuardedAveraging
import FiniteAvalanchesCurrent.ForestReciprocalV5

/-! One uniform guarded source expectation bound from the current complete forest proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentMean
open LatticeProb MeasureTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.SourceCounting
open TreeMeasurability11.CurrentDomain
open scoped Classical
noncomputable section

/-- The same exponent and constant precede every mark scale and valid finite volume. -/
theorem uniform_source_reciprocal_bound :
    ∃ a C : ℝ, 0 < a ∧
      ∀ r : ℕ, ∀ hr : 2 ≤ r, ∀ N : ℕ, ∀ hrN : r ≤ N,
        (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N) ≤
          C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a,C,ha,hforest⟩ :=
    FiniteAvalanches.Paper.CurrentSource.forest_reciprocal_cofinite
  refine ⟨a,max C 0,ha,?_⟩
  intro r hr N hrN
  exact source_mean_le_of_forest a C ha hforest r hr N hrN

/-- The first valid volume is included in the very same uniform supplier. -/
theorem uniform_source_reciprocal_bound_endpoint :
    ∃ a C : ℝ, 0 < a ∧ ∀ r : ℕ, ∀ hr : 2 ≤ r,
      (∫ t, sourceFiniteReciprocal r (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr le_rfl hx) t ∂WiredTrees.law r) ≤
        C * Real.rpow (Real.log ((r : ℝ) + 2)) (-a) := by
  obtain ⟨a,C,ha,hbound⟩ := uniform_source_reciprocal_bound
  exact ⟨a,C,ha,fun r hr => hbound r hr r le_rfl⟩

end
end FiniteAvalanches.Paper.CurrentMean
