import CurrentRegisteredPast.FullIntegerMainConsumer

open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanchesCurrent.RegisteredPast.Main

/-- Adding one grain at the origin stabilizes almost surely under the stationary
law on integer sandpiles, with a universal logarithmic bound for its radius. -/
theorem finite_avalanches_origin :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
        {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact FiniteAvalanches.RegisteredPast.FullIntegerChecks.internal_current_main

end FiniteAvalanchesCurrent.RegisteredPast.Main
