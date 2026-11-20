import FiniteAvalanches.Support.Plane.CircleCylinder
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Radial coordinates on a closed annulus

The closed annulus between radii one and two is homeomorphic to the product
of the unit interval and the additive circle.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- The closed complex annulus between radii one and two. -/
def closedUnitAnnulus : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

/-- Radial coordinates on the closed annulus. -/
noncomputable def annulusCoordinates :
    unitInterval × AddCircle (1 : ℝ) ≃ₜ closedUnitAnnulus := by
  let C := AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)
  let f : unitInterval × AddCircle (1 : ℝ) → closedUnitAnnulus := fun p =>
    ⟨(1 + (p.1 : ℝ)) • (C p.2 : ℂ), by
      have hn : ‖(C p.2 : ℂ)‖ = 1 := Circle.norm_coe _
      have hp : 0 ≤ 1 + (p.1 : ℝ) := by linarith [p.1.property.1]
      simp only [closedUnitAnnulus, mem_setOf_eq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hp, hn, mul_one]
      exact ⟨by linarith [p.1.property.1], by linarith [p.1.property.2]⟩⟩
  have hnorm (p : unitInterval × AddCircle (1 : ℝ)) : ‖(f p : ℂ)‖ = 1 + p.1 := by
    have hp : 0 ≤ 1 + (p.1 : ℝ) := by linarith [p.1.property.1]
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, Circle.norm_coe, mul_one]
  have hinj : Function.Injective f := by
    intro p q hpq
    have ht : p.1 = q.1 := by
      apply Subtype.ext
      have h := congrArg (fun z : closedUnitAnnulus => ‖(z : ℂ)‖) hpq
      rw [hnorm, hnorm] at h
      linarith
    have hC : (C p.2 : ℂ) = C q.2 := by
      have h := congrArg (fun z : closedUnitAnnulus => (z : ℂ)) hpq
      change (1 + (p.1 : ℝ)) • (C p.2 : ℂ) = (1 + (q.1 : ℝ)) • (C q.2 : ℂ) at h
      rw [← ht] at h
      exact (smul_right_injective ℂ (by linarith [p.1.property.1] : (1 + (p.1 : ℝ)) ≠ 0)) h
    have hz : p.2 = q.2 := C.injective (Subtype.ext hC)
    exact Prod.ext ht hz
  have hsurj : Function.Surjective f := by
    intro z
    have hz : z.val ≠ 0 := by
      intro h
      have := z.property.1
      simp only [h, norm_zero] at this
      norm_num at this
    let w : ({0}ᶜ : Set ℂ) := ⟨z, by simpa using hz⟩
    let R := homeomorphUnitSphereProd ℂ
    let a : unitInterval := ⟨‖z.val‖ - 1, by
      constructor <;> linarith [z.property.1, z.property.2]⟩
    let b : AddCircle (1 : ℝ) := C.symm (R w).1
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    change (1 + (a : ℝ)) • (C b : ℂ) = z.val
    have hr : (R w).2.val • ((R w).1 : ℂ) = z.val := by
      have h := congrArg (fun x : ({0}ᶜ : Set ℂ) => (x : ℂ)) (R.symm_apply_apply w)
      change (R w).2.val • ((R w).1 : ℂ) = z.val at h
      exact h
    have hs : (R w).2.val = ‖z.val‖ := by
      simp only [R, homeomorphUnitSphereProd_apply_snd_coe, w]
    simpa only [a, b, C.apply_symm_apply, hs, add_sub_cancel] using hr
  let e : unitInterval × AddCircle (1 : ℝ) ≃ closedUnitAnnulus :=
    Equiv.ofBijective f ⟨hinj, hsurj⟩
  apply Continuous.homeoOfEquivCompactToT2 (f := e)
  change Continuous f
  apply Continuous.subtype_mk
  exact (continuous_const.add (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp (C.continuous.comp continuous_snd))

/-- The norm is the radial coordinate plus one. -/
theorem annulusCoordinates_norm (p : unitInterval × AddCircle (1 : ℝ)) :
    ‖(annulusCoordinates p : ℂ)‖ = 1 + p.1 := by
  change ‖(1 + (p.1 : ℝ)) •
    (AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num) p.2 : ℂ)‖ = _
  have hp : 0 ≤ 1 + (p.1 : ℝ) := by linarith [p.1.property.1]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, Circle.norm_coe, mul_one]

/-- An increasing interval homeomorphism induces a radius-preserving annulus
homeomorphism that is the identity on the inner circle and realizes the induced
circle homeomorphism on the outer circle. -/
theorem exists_annulus_homeomorph_of_interval_homeomorph
    (f : unitInterval ≃ₜ unitInterval) (hf : StrictMono f) :
    ∃ H : closedUnitAnnulus ≃ₜ closedUnitAnnulus,
      (∀ z, ‖(H z : ℂ)‖ = ‖(z : ℂ)‖) ∧
      (∀ z, H (annulusCoordinates (0, z)) = annulusCoordinates (0, z)) ∧
      (∀ x : unitInterval,
        H (annulusCoordinates (1, ((x : ℝ) : AddCircle (1 : ℝ)))) =
          annulusCoordinates (1, (((f x : unitInterval) : ℝ) : AddCircle (1 : ℝ)))) := by
  obtain ⟨G, hG, hG0, hG1⟩ := exists_circle_cylinder_homeomorph f hf
  let H := annulusCoordinates.symm.trans (G.trans annulusCoordinates)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro z
    change ‖(annulusCoordinates (G (annulusCoordinates.symm z)) : ℂ)‖ = ‖(z : ℂ)‖
    rw [annulusCoordinates_norm, hG]
    conv_rhs => rw [← annulusCoordinates.apply_symm_apply z]
    rw [annulusCoordinates_norm]
  · intro z
    change annulusCoordinates (G (annulusCoordinates.symm (annulusCoordinates (0, z)))) = _
    rw [annulusCoordinates.symm_apply_apply, hG0]
  · intro x
    change annulusCoordinates (G (annulusCoordinates.symm
      (annulusCoordinates (1, ((x : ℝ) : AddCircle (1 : ℝ)))))) = _
    rw [annulusCoordinates.symm_apply_apply, hG1]

end FiniteAvalanches.Electrical.StatementGeometry
