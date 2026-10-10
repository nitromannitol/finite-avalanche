import FiniteAvalanches.Sandpile.SourceCounting.MainOriginCofinite
import FiniteAvalanchesFrozen.ForestReciprocalCofiniteV4
import FiniteAvalanches.Sandpile.Law.BoxLimit
import FiniteAvalanches.Sandpile.ExtendedObservables
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open scoped ENNReal

set_option autoImplicit false

namespace FiniteAvalanchesProofs.MainOriginV3

theorem finite_avalanches_origin_v3 :
  (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
    ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
  ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
    ∀ R : ℝ, 0 ≤ R →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
      C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact FiniteAvalanches.ConditioningMain.main_origin_of_cofinite_reciprocal
    FiniteAvalanches.Wilson.Lattice.SourceTargets.forest_reciprocal_cofinite_v4

end FiniteAvalanchesProofs.MainOriginV3
