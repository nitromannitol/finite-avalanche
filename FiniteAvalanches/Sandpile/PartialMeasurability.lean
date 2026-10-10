import FiniteAvalanches.Sandpile.Measurability

/-! Measurability of the literal finite legal odometer and partial addition.
The countable count carrier has the discrete sigma-algebra. -/

namespace FiniteAvalanches.Sandpile

open LatticeProb LatticeProb.Sandpile FiniteAvalanches MeasureTheory
open scoped Classical

local instance : MeasurableSpace Counts := ⊤

local instance (ξ : Counts) : MeasurableSpace (StabilizationDomain ξ) :=
  inferInstanceAs (MeasurableSpace {η : StableField // ∃ w, Stabilizes η ξ w})

theorem measurableSet_stabilization_domain (ξ : Counts) :
    MeasurableSet {η : StableField | ∃ w, Stabilizes η ξ w} := by
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun w => measurableSet_stabilizes ξ w)

theorem odometer_fiber (ξ u : Counts) :
    (odometer ξ) ⁻¹' {u} =
      ⋃ w : List Site2, {η : StabilizationDomain ξ |
        Stabilizes η.val ξ w ∧ listCounts w = u} := by
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := odometer_spec ξ η
    exact ⟨w, hw, he.trans h⟩
  · rintro ⟨w, hw, he⟩
    exact (odometer_eq_counts ξ η hw).trans he

theorem measurable_odometer (ξ : Counts) : Measurable (odometer ξ) := by
  apply measurable_to_countable'
  intro u
  rw [odometer_fiber ξ u]
  exact MeasurableSet.iUnion fun w =>
    ((measurableSet_stabilizes ξ w).preimage measurable_subtype_coe).inter
      (MeasurableSet.const _)

theorem measurable_addition (ξ : Counts) : Measurable (addition ξ) := by
  apply measurable_pi_lambda
  intro x
  have hh : Measurable (fun η : StabilizationDomain ξ => ((η.val x).val : ℤ)) :=
    (measurable_of_countable (fun a : Fin 4 => (a.val : ℤ))).comp
      ((measurable_pi_apply x).comp measurable_subtype_coe)
  have hu : Measurable (fun u : Counts => lap (fun y => (u y : ℤ)) x) :=
    measurable_of_countable _
  have hf : Measurable (fun η : StabilizationDomain ξ =>
      initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x) :=
    (hh.add measurable_const).add (hu.comp (measurable_odometer ξ))
  apply measurable_to_countable'
  intro a
  have he : (fun η : StabilizationDomain ξ => addition ξ η x) ⁻¹' {a} =
      (fun η : StabilizationDomain ξ =>
        initial η.val ξ x + lap (fun y => (odometer ξ η y : ℤ)) x) ⁻¹' {(a.val : ℤ)} := by
    ext η
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
    rw [← addition_eq ξ η x]
    exact_mod_cast (Iff.rfl : (addition ξ η x).val = a.val ↔
      (addition ξ η x).val = a.val)
  rw [he]
  exact hf (measurableSet_singleton _)


end FiniteAvalanches.Sandpile
