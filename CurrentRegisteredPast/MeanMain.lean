import CurrentMean.Supplier
import CurrentRegisteredPast.MainApplications

/-! The current Main assembly consumes the source expectation supplier internally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.RegisteredPast.MeanMain
open LatticeProb MeasureTheory FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

                                                                                     
theorem main_origin :
    (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
      ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
      ∀ R : ℝ, 0 ≤ R →
        (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
        C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact RegisteredPast.Applications.exact_origin_application_of_source_bound CurrentMean.uniform_source_reciprocal_bound

end
end FiniteAvalanches.Paper.RegisteredPast.MeanMain
