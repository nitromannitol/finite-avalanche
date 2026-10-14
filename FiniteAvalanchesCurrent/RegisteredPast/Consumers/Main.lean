import FiniteAvalanchesCurrent.RegisteredPast.Main


open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanchesCurrent.RegisteredPast.Consumers

theorem finite_avalanches_origin_application :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin

end FiniteAvalanchesCurrent.RegisteredPast.Consumers
