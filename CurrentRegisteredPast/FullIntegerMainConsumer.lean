import CurrentSource.FullIntegerLaw
import CurrentRegisteredPast.MeanMain

                                                                                 
                                                                                 
                                                                               

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.RegisteredPast.FullIntegerChecks
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

private theorem interpret_complete_nn_main
    (hNN : (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
        ∃ w : List Site2, Sandpile.Stabilizes η (oneGrain (0 : Site2)) w) ∧
      ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
        (infiniteVolumeLaw : Measure StableField).real
          {η | ENNReal.ofReal R < extendedCount (FiniteAvalanches.radius η (0 : Site2))} ≤
          C * Real.rpow (Real.log (R + 2)) (-a)) :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
      ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
        (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
          {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
          C * Real.rpow (Real.log (R + 2)) (-a) := by
  refine ⟨FullInteger.sourceLaw_stabilizes_ae_of_nn hNN.1, ?_⟩
  obtain ⟨a, ha, C, hC⟩ := hNN.2
  refine ⟨a, ha, C, ?_⟩
  intro R hR
  rw [FullInteger.sourceLaw_real_radius_tail_eq 0 R hR]
  exact hC R hR

                                                                              
                                                                             
theorem internal_current_main :
    (∀ᵐ η ∂(FullInteger.sourceLaw : Measure (Site2 → ℤ)),
      ∃ w : List Site2, RawFull.Stabilizes η (oneGrain (0 : Site2)) w) ∧
      ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
        (FullInteger.sourceLaw : Measure (Site2 → ℤ)).real
          {η | ENNReal.ofReal R < extendedCount (FullInteger.radius η (0 : Site2))} ≤
          C * Real.rpow (Real.log (R + 2)) (-a) :=
  interpret_complete_nn_main FiniteAvalanches.Paper.RegisteredPast.MeanMain.main_origin

end
end FiniteAvalanches.RegisteredPast.FullIntegerChecks
