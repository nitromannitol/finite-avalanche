import FiniteAvalanches.Support.Plane.CircleCylinder
import Mathlib.Topology.Order.IntermediateValue

/-!
# Cutting the circle at a fixed point

Removing the basepoint from the additive circle gives an open interval.
Every basepoint-fixing circle homeomorphism therefore acts on the interval
by a strictly increasing or strictly decreasing homeomorphism.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Cutting the additive circle at zero gives the open unit interval. -/
noncomputable def circleCutCoordinates :
    Ioo (0 : ℝ) 1 ≃ₜ ({0}ᶜ : Set (AddCircle (1 : ℝ))) := by
  let e := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).toHomeomorphSourceTarget
  exact (Homeomorph.setCongr (by simp)).trans (e.trans (Homeomorph.setCongr (by simp)))

/-- The cut coordinate sends a point to its class modulo one. -/
theorem circleCutCoordinates_apply (x : Ioo (0 : ℝ) 1) :
    ((circleCutCoordinates x : ({0}ᶜ : Set (AddCircle (1 : ℝ)))) : AddCircle (1 : ℝ)) =
      ((x : ℝ) : AddCircle (1 : ℝ)) := by
  rfl

/-- A circle homeomorphism fixing zero restricts to the cut interval. -/
noncomputable def circleCutMap (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hF : F 0 = 0) : Ioo (0 : ℝ) 1 ≃ₜ Ioo (0 : ℝ) 1 := by
  let G : ({0}ᶜ : Set (AddCircle (1 : ℝ))) ≃ₜ ({0}ᶜ : Set (AddCircle (1 : ℝ))) :=
    F.subtype (by
      intro x
      simp only [mem_compl_iff, mem_singleton_iff]
      rw [← hF, F.injective.eq_iff, hF])
  exact circleCutCoordinates.trans (G.trans circleCutCoordinates.symm)

/-- The cut map represents the original circle map. -/
theorem circleCutMap_apply (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hF : F 0 = 0) (x : Ioo (0 : ℝ) 1) :
    (((circleCutMap F hF x : ℝ) : AddCircle (1 : ℝ))) = F ((x : ℝ) : AddCircle (1 : ℝ)) := by
  have h := congrArg (fun y : ({0}ᶜ : Set (AddCircle (1 : ℝ))) =>
    (y : AddCircle (1 : ℝ)))
    (circleCutCoordinates.apply_symm_apply ((F.subtype (p := fun z => z ∈ ({0}ᶜ : Set (AddCircle (1 : ℝ))) )
      (q := fun z => z ∈ ({0}ᶜ : Set (AddCircle (1 : ℝ)))) (by
        intro z
        simp only [mem_compl_iff, mem_singleton_iff]
        rw [← hF, F.injective.eq_iff, hF])) (circleCutCoordinates x)))
  rw [circleCutCoordinates_apply] at h
  exact h

/-- The cut map of a basepoint-fixing circle homeomorphism has one of the two
possible orientations. -/
theorem circleCutMap_strictMono_or_strictAnti
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) (hF : F 0 = 0) :
    StrictMono (circleCutMap F hF) ∨ StrictAnti (circleCutMap F hF) := by
  let g := circleCutMap F hF
  let u : ℝ → ℝ := fun x => if hx : x ∈ Ioo (0 : ℝ) 1 then (g ⟨x, hx⟩ : ℝ) else 0
  have hu : ContinuousOn u (Ioo (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : Ioo (0 : ℝ) 1 => u x)
    have h : (fun x : Ioo (0 : ℝ) 1 => u x) = fun x => (g x : ℝ) := by
      funext x
      simp only [u, dif_pos x.property]
    rw [h]
    exact continuous_subtype_val.comp g.continuous
  have hi : InjOn u (Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    simp only [u, dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (g.injective (Subtype.ext hxy))
  have h := hu.strictMonoOn_of_injOn_Ioo (by norm_num) hi
  rcases h with h | h
  · left
    intro x y hxy
    have h' := h x.property y.property hxy
    change (g x : ℝ) < (g y : ℝ)
    simpa only [u, dif_pos x.property, dif_pos y.property] using h'
  · right
    intro x y hxy
    have h' := h x.property y.property hxy
    change (g y : ℝ) < (g x : ℝ)
    simpa only [u, dif_pos x.property, dif_pos y.property] using h'

end FiniteAvalanches.Electrical.StatementGeometry
