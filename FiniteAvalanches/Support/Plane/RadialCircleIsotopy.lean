import FiniteAvalanches.Support.Plane.CircleIsotopy
import Mathlib.Topology.Order.ProjIcc

/-!
# Radial circle isotopies on the punctured plane

A circle isotopy acts on polar angles with a radial cutoff, fixing a disk and
preserving the radial coordinate.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Polar coordinates on the punctured complex plane, with radius first. -/
noncomputable def puncturedPolarCoordinates :
    ({0}ᶜ : Set ℂ) ≃ₜ Ioi (0 : ℝ) × AddCircle (1 : ℝ) :=
  (homeomorphUnitSphereProd ℂ).trans
    (((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)).symm.prodCongr
      (Homeomorph.refl _)).trans (Homeomorph.prodComm _ _))

/-- The radius coordinate in the polar homeomorphism is the norm. -/
theorem puncturedPolarCoordinates_radius (x : ({0}ᶜ : Set ℂ)) :
    ((puncturedPolarCoordinates x).1 : ℝ) = ‖(x : ℂ)‖ := by
  exact homeomorphUnitSphereProd_apply_snd_coe ℂ x

/-- A continuous radial cutoff which is zero for radius at most one and one
for radius at least two. -/
noncomputable def radialCutoff (r : Ioi (0 : ℝ)) : unitInterval :=
  projIcc (0 : ℝ) 1 zero_le_one ((r : ℝ) - 1)

/-- The radial cutoff is continuous. -/
theorem continuous_radialCutoff : Continuous radialCutoff :=
  continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)

/-- The cutoff vanishes on the unit disk. -/
theorem radialCutoff_eq_zero (r : Ioi (0 : ℝ)) (hr : (r : ℝ) ≤ 1) :
    radialCutoff r = 0 := by
  apply projIcc_eq_zero.mpr
  linarith

/-- The cutoff equals one outside the disk of radius two. -/
theorem radialCutoff_eq_one (r : Ioi (0 : ℝ)) (hr : 2 ≤ (r : ℝ)) :
    radialCutoff r = 1 := by
  apply projIcc_eq_one.mpr
  linarith

/-- A circle isotopy extends to a radius-preserving punctured-plane isotopy
which fixes the unit disk, with jointly continuous inverse maps. -/
theorem exists_punctured_radial_isotopy
    (A : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ))
    (hA : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => A p.1 p.2))
    (hAi : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (A p.1).symm p.2))
    (hA0 : ∀ z, A 0 z = z) :
    ∃ H : unitInterval → ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ),
      Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => H p.1 p.2) ∧
      Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => (H p.1).symm p.2) ∧
      (∀ (s : unitInterval) (x : ({0}ᶜ : Set ℂ)), ‖(x : ℂ)‖ ≤ 1 → H s x = x) ∧
      (∀ (s : unitInterval) (x : ({0}ᶜ : Set ℂ)), ‖(H s x : ℂ)‖ = ‖(x : ℂ)‖) ∧
      (∀ x, H 0 x = x) ∧
      (∀ s x, (puncturedPolarCoordinates (H s x)).2 =
        A (s * radialCutoff (puncturedPolarCoordinates x).1) (puncturedPolarCoordinates x).2) := by
  let R := puncturedPolarCoordinates
  let e : unitInterval → Ioi (0 : ℝ) → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) :=
    fun s r => A (s * radialCutoff r)
  have he (s : unitInterval) : Continuous (fun p : Ioi (0 : ℝ) × AddCircle (1 : ℝ) =>
      e s p.1 p.2) := by
    change Continuous (fun p : Ioi (0 : ℝ) × AddCircle (1 : ℝ) =>
      A (s * radialCutoff p.1) p.2)
    exact hA.comp ((continuous_const.mul (continuous_radialCutoff.comp continuous_fst)).prodMk
      continuous_snd)
  have hei (s : unitInterval) : Continuous (fun p : Ioi (0 : ℝ) × AddCircle (1 : ℝ) =>
      (e s p.1).symm p.2) := by
    change Continuous (fun p : Ioi (0 : ℝ) × AddCircle (1 : ℝ) =>
      (A (s * radialCutoff p.1)).symm p.2)
    exact hAi.comp ((continuous_const.mul (continuous_radialCutoff.comp continuous_fst)).prodMk
      continuous_snd)
  let K : unitInterval → (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) ≃ₜ
      (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) := fun s => cylinderHomeomorph (e s) (he s) (hei s)
  let H : unitInterval → ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ) :=
    fun s => R.trans ((K s).trans R.symm)
  have hjoint : Continuous (fun p : unitInterval × (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) =>
      K p.1 p.2) := by
    change Continuous (fun p : unitInterval × (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) =>
      (p.2.1, A (p.1 * radialCutoff p.2.1) p.2.2))
    exact continuous_snd.fst.prodMk (hA.comp
      ((continuous_fst.mul (continuous_radialCutoff.comp continuous_snd.fst)).prodMk
        continuous_snd.snd))
  have hjointi : Continuous (fun p : unitInterval × (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) =>
      (K p.1).symm p.2) := by
    change Continuous (fun p : unitInterval × (Ioi (0 : ℝ) × AddCircle (1 : ℝ)) =>
      (p.2.1, (A (p.1 * radialCutoff p.2.1)).symm p.2.2))
    exact continuous_snd.fst.prodMk (hAi.comp
      ((continuous_fst.mul (continuous_radialCutoff.comp continuous_snd.fst)).prodMk
        continuous_snd.snd))
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => R.symm (K p.1 (R p.2)))
    exact R.symm.continuous.comp (hjoint.comp (continuous_fst.prodMk (R.continuous.comp continuous_snd)))
  · change Continuous (fun p : unitInterval × ({0}ᶜ : Set ℂ) => R.symm ((K p.1).symm (R p.2)))
    exact R.symm.continuous.comp (hjointi.comp (continuous_fst.prodMk (R.continuous.comp continuous_snd)))
  · intro s x hx
    have hc : radialCutoff (R x).1 = 0 := radialCutoff_eq_zero _ (by
      simpa only [R, puncturedPolarCoordinates_radius] using hx)
    change R.symm (K s (R x)) = x
    have hk : K s (R x) = R x := by
      apply Prod.ext
      · rfl
      · change A (s * radialCutoff (R x).1) (R x).2 = (R x).2
        rw [hc, mul_zero, hA0]
    rw [hk, R.symm_apply_apply]
  · intro s x
    rw [← puncturedPolarCoordinates_radius (H s x), ← puncturedPolarCoordinates_radius x]
    change ((R (R.symm (K s (R x)))).1 : ℝ) = ((R x).1 : ℝ)
    rw [R.apply_symm_apply]
    rfl
  · intro x
    change R.symm (K 0 (R x)) = x
    have hk : K 0 (R x) = R x := by
      apply Prod.ext
      · rfl
      · change A (0 * radialCutoff (R x).1) (R x).2 = (R x).2
        rw [zero_mul, hA0]
    rw [hk, R.symm_apply_apply]
  · intro s x
    change (R (R.symm (K s (R x)))).2 = _
    rw [R.apply_symm_apply]
    rfl

end FiniteAvalanches.Electrical.StatementGeometry
