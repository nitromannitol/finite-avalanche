import CurrentSource.FullIntegerLaw
import CurrentRegisteredPast.FullFiniteLimsupReduction

set_option autoImplicit false
namespace FiniteAvalanches.Paper.RegisteredPast.FullInteger
open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter
open FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

/-- The finite reciprocal reduction on the full integer sandpile carrier. -/
theorem reciprocal_reduction_limsup :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r + 2 ≤ M →
      (Sandpile.FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal (M : ℝ) < extendedCount (Sandpile.FullInteger.radius η 0)} ≤
        (limsup (fun N : ℕ => ∫ t, TreeMeasurability11.finiteZN N (sourceMarks r)
          (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop) +
        C * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC⟩ := RegisteredPast.RadiusReductionFull.reciprocal_reduction_limsup_current
  refine ⟨C, ?_⟩
  intro r hr M hM
  rw [Sandpile.FullInteger.sourceLaw_real_radius_tail_eq 0 (M : ℝ) (Nat.cast_nonneg M)]
  exact hC r hr M hM

end
end FiniteAvalanches.Paper.RegisteredPast.FullInteger
