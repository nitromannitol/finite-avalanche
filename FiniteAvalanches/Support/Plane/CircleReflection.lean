import FiniteAvalanches.Support.Plane.PlaneCircleIsotopy

/-!
# Reflection and circle orientation

Reversing the circle parameter exchanges the two possible monotonicity
classes of a circle homeomorphism.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- The quotient map is injective on the open unit interval. -/
theorem circle_coe_injective_on_open :
    Function.Injective (fun x : Ioo (0 : ℝ) 1 => ((x : ℝ) : AddCircle (1 : ℝ))) := by
  intro x y h
  apply Subtype.ext
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
    (by simpa only [zero_add] using Ioo_subset_Ico_self x.property)
    (by simpa only [zero_add] using Ioo_subset_Ico_self y.property)).mp
  exact h

/-- Reflection of the open unit interval. -/
def openIntervalReflection (x : Ioo (0 : ℝ) 1) : Ioo (0 : ℝ) 1 :=
  ⟨1 - x, by constructor <;> linarith [x.property.1, x.property.2]⟩

/-- Reflection strictly reverses the order on the open unit interval. -/
theorem openIntervalReflection_strictAnti : StrictAnti openIntervalReflection := by
  intro x y h
  change 1 - (y : ℝ) < 1 - (x : ℝ)
  have hxy : (x : ℝ) < y := h
  linarith

/-- Reflection of a circle parameter is represented by `1 - x` on the cut. -/
theorem circle_coe_openIntervalReflection (x : Ioo (0 : ℝ) 1) :
    (((openIntervalReflection x : ℝ) : AddCircle (1 : ℝ))) =
      -((x : ℝ) : AddCircle (1 : ℝ)) := by
  change (((1 - (x : ℝ) : ℝ) : AddCircle (1 : ℝ))) = _
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]

/-- Reversing the circle parameter precomposes the normalized cut map with
reflection of the open interval. -/
theorem circleCutMap_normalized_reflect
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) (x : Ioo (0 : ℝ) 1) :
    circleCutMap (normalizedCircleHomeomorph ((Homeomorph.neg _).trans F))
      (normalizedCircleHomeomorph_zero _) x =
    circleCutMap (normalizedCircleHomeomorph F) (normalizedCircleHomeomorph_zero F)
      (openIntervalReflection x) := by
  apply circle_coe_injective_on_open
  change (((circleCutMap (normalizedCircleHomeomorph ((Homeomorph.neg _).trans F))
      (normalizedCircleHomeomorph_zero _) x : ℝ) : AddCircle (1 : ℝ))) =
    (((circleCutMap (normalizedCircleHomeomorph F) (normalizedCircleHomeomorph_zero F)
      (openIntervalReflection x) : ℝ) : AddCircle (1 : ℝ)))
  rw [circleCutMap_apply, circleCutMap_apply, circle_coe_openIntervalReflection]
  change F (-((x : ℝ) : AddCircle (1 : ℝ))) + -F (-0) =
    F (-((x : ℝ) : AddCircle (1 : ℝ))) + -F 0
  rw [neg_zero]

/-- A circle homeomorphism or its reflection has increasing normalized cut. -/
theorem circle_homeomorph_normalized_cut_or_reflect
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    StrictMono (circleCutMap (normalizedCircleHomeomorph F)
        (normalizedCircleHomeomorph_zero F)) ∨
      StrictMono (circleCutMap (normalizedCircleHomeomorph ((Homeomorph.neg _).trans F))
        (normalizedCircleHomeomorph_zero _)) := by
  rcases circleCutMap_strictMono_or_strictAnti (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F) with h | h
  · exact Or.inl h
  · right
    intro x y hxy
    rw [circleCutMap_normalized_reflect, circleCutMap_normalized_reflect]
    exact h (openIntervalReflection_strictAnti hxy)

end FiniteAvalanches.Electrical.StatementGeometry
