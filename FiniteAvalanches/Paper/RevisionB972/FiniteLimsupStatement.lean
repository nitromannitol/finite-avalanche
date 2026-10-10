import FiniteAvalanches.Paper.RevisionB972.FiniteLimsupReduction

set_option autoImplicit false
namespace FiniteAvalanches.Paper.RevisionB972
open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Components Trees.Lattice TreeMeasurability11 FiniteAvalanches.Sandpile.Source
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

/-- A universal finite-volume reciprocal bound for the complete avalanche radius. -/
theorem reciprocal_reduction_limsup_v2 :
    ∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∀ M : ℕ, r + 2 ≤ M →
      (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal (M : ℝ) < extendedCount (radius η 0)} ≤
        (Filter.limsup
          (fun N : ℕ => ∫ t, finiteZN N (sourceMarks r)
            (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) atTop) +
        C * (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  exact reciprocal_reduction_limsup

end
end FiniteAvalanches.Paper.RevisionB972
