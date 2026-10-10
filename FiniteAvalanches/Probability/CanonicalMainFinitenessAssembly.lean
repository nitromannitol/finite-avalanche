import FiniteAvalanches.Probability.MainTailAssembly
import FiniteAvalanches.Sandpile.Law.BoxLimit

/-! INTERNAL assembly of the manuscript main theorem after its origin radius estimate.
The sole mathematical predecessor is the displayed radius-tail bound on canonical μ.
MainTailAssembly already proves the deterministic Q transfer and the layer-cake moments;
this module consumes those proofs and discharges invariance for the registered actual law.
No claim that the new paper radius estimate has been proved is made here. -/
namespace FiniteAvalanches.Probability.MainTailTransfer

open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
  FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal
noncomputable section

/-- One exponent, one tail constant, and one measurable probability-one set work for
ALL sources. On that set the actual ordered legal list gives both actual observables.
Real nonnegative thresholds include zero; the canonical extended moments retain TOP
on every failure field. The sole unproved predecessor remains explicitly an input. -/
theorem internal_canonical_main_of_origin_radius_tail
    (hRadius : ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      (infiniteVolumeLaw : Measure StableField) {η | (M : WithTop ℕ) < radius η 0} ≤
        ENNReal.ofReal (C * Real.log (M + 2)^(-a))) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ Ω : Set StableField,
      MeasurableSet Ω ∧ (infiniteVolumeLaw : Measure StableField) Ω = 1 ∧
      (∀ (o : Site2) (R : ℝ), 0 ≤ R →
        (infiniteVolumeLaw : Measure StableField).real
            {η | ENNReal.ofReal R < extendedCount (radius η o)} +
          (infiniteVolumeLaw : Measure StableField).real
            {η | ENNReal.ofReal R < extendedCount (totalTopplings η o)} ≤
          C * Real.log (R + 2)^(-a)) ∧
      (∀ η ∈ Ω, ∀ o : Site2, ∃ w : List Site2,
        Stabilizes η (oneGrain o) w ∧
        radius η o = (countsRadius o (listCounts w) : WithTop ℕ) ∧
        totalTopplings η o = (w.length : WithTop ℕ)) ∧
      (∀ (o : Site2) (p : {p : ℝ // 0 < p}), p.val < a →
        (∫⁻ η, logMomentIntegrand p (radius η o)
          ∂(infiniteVolumeLaw : Measure StableField)) +
        (∫⁻ η, logMomentIntegrand p (totalTopplings η o)
          ∂(infiniteVolumeLaw : Measure StableField)) < ⊤) := by
  have hinv : ∀ z : Site2, MeasurePreserving (FiniteAvalanches.translate z)
      (infiniteVolumeLaw : Measure StableField) (infiniteVolumeLaw : Measure StableField) := by
    intro z
    refine ⟨measurable_translate z, ?_⟩
    have htranslate : FiniteAvalanches.translate z = _root_.translate (-z) := by
      funext η x
      simp only [FiniteAvalanches.translate, _root_.translate, sub_neg_eq_add]
    rw [htranslate]
    exact isTranslationInvariant_infiniteVolumeLaw (-z)
  obtain ⟨a, ha, C, hC, htail, hae, hmom⟩ :=
    internal_shared_main_target_of_origin_nat_radius_tail
      (infiniteVolumeLaw : Measure StableField) hinv hRadius
  let Ω : Set StableField := {η | ∀ o : Site2, FiniteStabilizable η o}
  have hΩmeas : MeasurableSet Ω := measurableSet_every_source
  have hΩprob : (infiniteVolumeLaw : Measure StableField) Ω = 1 :=
    (mem_ae_iff_prob_eq_one hΩmeas).mp hae
  refine ⟨a, ha, C, hC, Ω, hΩmeas, hΩprob, htail, ?_, hmom⟩
  intro η hη o
  obtain ⟨w, hw⟩ := hη o
  exact ⟨w, hw, radius_of_stabilizes hw, totalTopplings_of_stabilizes hw⟩

end
end FiniteAvalanches.Probability.MainTailTransfer

#check @FiniteAvalanches.Probability.MainTailTransfer.internal_canonical_main_of_origin_radius_tail
#print axioms FiniteAvalanches.Probability.MainTailTransfer.internal_canonical_main_of_origin_radius_tail
