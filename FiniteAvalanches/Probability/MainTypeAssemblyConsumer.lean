import FiniteAvalanches.Probability.CanonicalMainFinitenessAssembly

/-! INTERNAL term-level application to the exact manifested th:main TYPE.
The quarantined main module and reserved provider are not imported or consumed.
The sole origin-radius-tail predecessor remains an explicit internal input. -/
namespace FiniteAvalanches.Probability.MainTailTransfer
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
  FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

/-- Exact frozen main conclusion assembled from canonical stronger common-set output;
this is conditional on the sole origin-radius estimate, not the closed paper root. -/
theorem internal_frozen_main_type_of_origin_radius_tail
    (hRadius : ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      (infiniteVolumeLaw : Measure StableField) {η | (M : WithTop ℕ) < radius η 0} ≤
        ENNReal.ofReal (C * Real.log (M + 2)^(-a))) :
  ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
    (∀ (o : Site2) (R : ℝ), 0 ≤ R →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal R < extendedCount (radius η o)} +
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
        C * Real.rpow (Real.log (R + 2)) (-a)) ∧
    (∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField), ∀ o : Site2,
      ∃ w : List Site2, Stabilizes η (oneGrain o) w) ∧
    (∀ (o : Site2) (p : ℝ) (hp : 0 < p), p < a →
      (∫⁻ η, logMomentIntegrand ⟨p, hp⟩ (radius η o)
        ∂(infiniteVolumeLaw : Measure StableField)) +
      (∫⁻ η, logMomentIntegrand ⟨p, hp⟩ (totalTopplings η o)
        ∂(infiniteVolumeLaw : Measure StableField)) < ⊤) := by
  obtain ⟨a, ha, C, _hC, Ω, hΩmeas, hΩprob, htail, hfinite, hmom⟩ :=
    internal_canonical_main_of_origin_radius_tail hRadius
  refine ⟨a, ha, C, htail, ?_, ?_⟩
  · have hmem : ∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField), η ∈ Ω :=
      (mem_ae_iff_prob_eq_one hΩmeas).mpr hΩprob
    filter_upwards [hmem] with η hη
    intro o
    obtain ⟨w, hw, _, _⟩ := hfinite η hη o
    exact ⟨w, hw⟩
  · intro o p hp hpa
    exact hmom o ⟨p, hp⟩ hpa

end
end FiniteAvalanches.Probability.MainTailTransfer

#check @FiniteAvalanches.Probability.MainTailTransfer.internal_frozen_main_type_of_origin_radius_tail
#print axioms FiniteAvalanches.Probability.MainTailTransfer.internal_shared_main_target_of_origin_nat_radius_tail
#print axioms FiniteAvalanches.Probability.MainTailTransfer.internal_canonical_main_of_origin_radius_tail
#print axioms FiniteAvalanches.Probability.MainTailTransfer.internal_frozen_main_type_of_origin_radius_tail
