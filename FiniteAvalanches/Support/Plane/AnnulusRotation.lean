import FiniteAvalanches.Support.Plane.CircleAnnulusExtension

/-!
# Rotation of an annulus

Rotations of the circle extend across the annulus while fixing the inner
boundary. This removes the fixed-basepoint condition from the annulus extension.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A circle rotation extends across the annulus, preserving radii and fixing
the inner boundary. -/
theorem exists_annulus_homeomorph_of_rotation (a : AddCircle (1 : ℝ)) :
    ∃ H : closedUnitAnnulus ≃ₜ closedUnitAnnulus,
      (∀ z, ‖(H z : ℂ)‖ = ‖(z : ℂ)‖) ∧
      (∀ z, H (annulusCoordinates (0, z)) = annulusCoordinates (0, z)) ∧
      (∀ z, H (annulusCoordinates (1, z)) = annulusCoordinates (1, z + a)) := by
  obtain ⟨r, _, hr⟩ := AddCircle.eq_coe_Ico a
  let E : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) :=
    fun t => Equiv.addRight (((t : ℝ) * r : ℝ) : AddCircle (1 : ℝ))
  have hE : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => E p.1 p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) =>
      p.2 + (((p.1 : ℝ) * r : ℝ) : AddCircle (1 : ℝ)))
    exact continuous_snd.add ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  have hEi : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (E p.1).symm p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) =>
      p.2 - (((p.1 : ℝ) * r : ℝ) : AddCircle (1 : ℝ)))
    exact continuous_snd.sub ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  let G := cylinderHomeomorph E hE hEi
  let H := annulusCoordinates.symm.trans (G.trans annulusCoordinates)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro z
    change ‖(annulusCoordinates (G (annulusCoordinates.symm z)) : ℂ)‖ = ‖(z : ℂ)‖
    rw [annulusCoordinates_norm]
    change 1 + (annulusCoordinates.symm z).1 = ‖(z : ℂ)‖
    conv_rhs => rw [← annulusCoordinates.apply_symm_apply z]
    rw [annulusCoordinates_norm]
  · intro z
    change annulusCoordinates (G (annulusCoordinates.symm (annulusCoordinates (0, z)))) = _
    rw [annulusCoordinates.symm_apply_apply]
    change annulusCoordinates (0, z + (((0 : ℝ) * r : ℝ) : AddCircle (1 : ℝ))) = _
    simp only [zero_mul, AddCircle.coe_zero, add_zero]
  · intro z
    change annulusCoordinates (G (annulusCoordinates.symm (annulusCoordinates (1, z)))) = _
    rw [annulusCoordinates.symm_apply_apply]
    change annulusCoordinates (1, z + (((1 : ℝ) * r : ℝ) : AddCircle (1 : ℝ))) = _
    rw [one_mul, hr]

/-- Normalize a circle homeomorphism by sending its value at zero back to zero. -/
def normalizedCircleHomeomorph (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ) :=
  F.trans (Homeomorph.addRight (-F 0))

/-- The normalized circle homeomorphism fixes zero. -/
theorem normalizedCircleHomeomorph_zero (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    normalizedCircleHomeomorph F 0 = 0 := by
  simp [normalizedCircleHomeomorph]

/-- Every circle homeomorphism whose normalized cut map is increasing extends
across an annulus, fixing the inner boundary and preserving radii. -/
theorem exists_annulus_homeomorph_of_normalized_circle_homeomorph
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F))) :
    ∃ H : closedUnitAnnulus ≃ₜ closedUnitAnnulus,
      (∀ z, ‖(H z : ℂ)‖ = ‖(z : ℂ)‖) ∧
      (∀ z, H (annulusCoordinates (0, z)) = annulusCoordinates (0, z)) ∧
      (∀ z, H (annulusCoordinates (1, z)) = annulusCoordinates (1, F z)) := by
  obtain ⟨G, hGn, hGi, hGo⟩ := exists_annulus_homeomorph_of_circle_homeomorph
    (normalizedCircleHomeomorph F) (normalizedCircleHomeomorph_zero F) hinc
  obtain ⟨R, hRn, hRi, hRo⟩ := exists_annulus_homeomorph_of_rotation (F 0)
  refine ⟨G.trans R, ?_, ?_, ?_⟩
  · intro z
    change ‖(R (G z) : ℂ)‖ = ‖(z : ℂ)‖
    rw [hRn, hGn]
  · intro z
    change R (G (annulusCoordinates (0, z))) = _
    rw [hGi, hRi]
  · intro z
    change R (G (annulusCoordinates (1, z))) = _
    rw [hGo, hRo]
    congr 2
    simp [normalizedCircleHomeomorph]

end FiniteAvalanches.Electrical.StatementGeometry
