import FiniteAvalanches.Support.Plane.IntervalExtension
import FiniteAvalanches.Support.Plane.AnnulusCoordinates

/-!
# Extending a circle homeomorphism over an annulus

A basepoint-fixing circle homeomorphism whose cut map is increasing extends
across a closed annulus, fixing the other boundary and preserving radii.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- An increasing cut map extends to the closed interval and represents the
original circle homeomorphism at every parameter. -/
theorem exists_interval_homeomorph_of_circleCutMap
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) (hF : F 0 = 0)
    (hinc : StrictMono (circleCutMap F hF)) :
    ∃ f : unitInterval ≃ₜ unitInterval, StrictMono f ∧
      ∀ x : unitInterval,
        (((f x : unitInterval) : ℝ) : AddCircle (1 : ℝ)) = F ((x : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨f, hf, hfi⟩ := exists_unitInterval_homeomorph_of_openInterval (circleCutMap F hF) hinc
  have hf0 : f 0 = 0 := by
    obtain ⟨x, hx⟩ := f.surjective 0
    have h : f 0 ≤ f x := hf.monotone (show 0 ≤ x from x.property.1)
    rw [hx] at h
    exact le_antisymm h (f 0).property.1
  have hf1 : f 1 = 1 := by
    obtain ⟨x, hx⟩ := f.surjective 1
    have h : f x ≤ f 1 := hf.monotone (show x ≤ 1 from x.property.2)
    rw [hx] at h
    exact le_antisymm (f 1).property.2 h
  refine ⟨f, hf, ?_⟩
  intro x
  by_cases hx0 : x = 0
  · subst x
    rw [hf0]
    change ((0 : ℝ) : AddCircle (1 : ℝ)) = F ((0 : ℝ) : AddCircle (1 : ℝ))
    simpa only [AddCircle.coe_zero] using hF.symm
  by_cases hx1 : x = 1
  · subst x
    simpa only [hf1, OneMemClass.coe_one, AddCircle.coe_period] using hF.symm
  have hxi : (x : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_le_of_ne x.property.1 (fun h => hx0 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne x.property.2 (fun h => hx1 (Subtype.ext h))
  have hi := hfi ⟨x, hxi⟩
  change (f x : ℝ) = (circleCutMap F hF ⟨x, hxi⟩ : ℝ) at hi
  rw [hi]
  exact circleCutMap_apply F hF ⟨x, hxi⟩

/-- An increasing basepoint-fixing circle homeomorphism extends over the
annulus, fixes its inner boundary, and preserves each radius. -/
theorem exists_annulus_homeomorph_of_circle_homeomorph
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) (hF : F 0 = 0)
    (hinc : StrictMono (circleCutMap F hF)) :
    ∃ H : closedUnitAnnulus ≃ₜ closedUnitAnnulus,
      (∀ z, ‖(H z : ℂ)‖ = ‖(z : ℂ)‖) ∧
      (∀ z, H (annulusCoordinates (0, z)) = annulusCoordinates (0, z)) ∧
      (∀ z, H (annulusCoordinates (1, z)) = annulusCoordinates (1, F z)) := by
  obtain ⟨f, hf, hrep⟩ := exists_interval_homeomorph_of_circleCutMap F hF hinc
  obtain ⟨H, hnorm, hinner, houter⟩ := exists_annulus_homeomorph_of_interval_homeomorph f hf
  refine ⟨H, hnorm, hinner, ?_⟩
  intro z
  obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico z
  let t : unitInterval := ⟨x, ⟨hx.1, hx.2.le⟩⟩
  have hout := houter t
  rw [hrep t] at hout
  exact hout

end FiniteAvalanches.Electrical.StatementGeometry
