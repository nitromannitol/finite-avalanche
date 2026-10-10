import FiniteAvalanches.Trees.Measure

/-! A genuine finite equivalence transports the entire uniform measure, not
only one event. Nonempty carriers are required before forming probability. -/
namespace FiniteAvalanches
open MeasureTheory
open scoped Classical ENNReal
noncomputable section

theorem uniform_measure_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    (uniformMeasure α).map e = uniformMeasure β := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _),
    uniformMeasure_apply, uniformMeasure_apply, Nat.card_congr e]
  have he : e ⁻¹' ({b} : Set β) = {e.symm b} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq_symm_apply]
  rw [he, Nat.card_unique (α := ({e.symm b} : Set α)),
    Nat.card_unique (α := ({b} : Set β))]

end
end FiniteAvalanches
