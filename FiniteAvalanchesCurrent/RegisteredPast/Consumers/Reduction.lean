import FiniteAvalanchesCurrent.RegisteredPast.Reduction


set_option autoImplicit false
namespace FiniteAvalanchesCurrent.RegisteredPast.Consumers
open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

theorem reciprocal_reduction_limsup_application :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r + 2 ≤ M →
      (Sandpile.FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal (M : ℝ) < extendedCount (Sandpile.FullInteger.radius η 0)} ≤
        (limsup (fun N : ℕ => ∫ t, TreeMeasurability11.finiteZN N (sourceMarks r)
          (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop) +
        C * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  exact FiniteAvalanches.Paper.RegisteredPast.FullInteger.reciprocal_reduction_limsup

end
end FiniteAvalanchesCurrent.RegisteredPast.Consumers
