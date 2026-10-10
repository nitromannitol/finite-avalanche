import FiniteAvalanchesProofs.MainOriginV3
import FiniteAvalanches.Sandpile.Law.BoxLimit
import FiniteAvalanches.Sandpile.ExtendedObservables
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open scoped ENNReal

set_option autoImplicit false

namespace FiniteAvalanchesFrozen.Main

theorem finite_avalanches_origin_v3 :
  (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
    ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
  ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
    ∀ R : ℝ, 0 ≤ R →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
      C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact FiniteAvalanchesProofs.MainOriginV3.finite_avalanches_origin_v3

end FiniteAvalanchesFrozen.Main
