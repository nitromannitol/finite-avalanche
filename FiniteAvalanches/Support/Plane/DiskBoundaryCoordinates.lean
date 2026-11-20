import FiniteAvalanches.Support.Plane.OrientedDiskPasting
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Polar coordinates on a disk boundary

The boundary of the radius-two disk is homeomorphic to the additive circle,
with the angle given by punctured polar coordinates.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- A point is on the disk boundary exactly when its complex norm is two. -/
theorem mem_frontier_complexDisk (z : Plane) :
    z ∈ frontier complexDisk ↔ ‖Complex.equivRealProdCLM.symm z‖ = 2 := by
  let C : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph
  change z ∈ frontier (C '' Metric.closedBall (0 : ℂ) 2) ↔ _
  rw [← C.image_frontier, C.image_eq_preimage_symm]
  simp only [mem_preimage, frontier_closedBall _ (by norm_num : (2 : ℝ) ≠ 0),
    Metric.mem_sphere, dist_zero_right]
  rfl

/-- The fixed radius in punctured polar coordinates for the disk boundary. -/
def diskBoundaryRadius : Ioi (0 : ℝ) := ⟨2, by norm_num⟩

/-- Convert an additive-circle parameter into a point of the disk boundary. -/
def diskBoundaryPoint (t : AddCircle (1 : ℝ)) : frontier complexDisk := by
  let x := puncturedPolarCoordinates.symm (diskBoundaryRadius, t)
  refine ⟨Complex.equivRealProdCLM x, ?_⟩
  rw [mem_frontier_complexDisk, Complex.equivRealProdCLM.symm_apply_apply]
  rw [← puncturedPolarCoordinates_radius x, Homeomorph.apply_symm_apply]
  rfl

/-- Regard a boundary point as a nonzero complex number. -/
def diskBoundaryPunctured (z : frontier complexDisk) : ({0}ᶜ : Set ℂ) := by
  refine ⟨Complex.equivRealProdCLM.symm z, ?_⟩
  simp only [mem_compl_iff, mem_singleton_iff]
  intro hz
  have hn := (mem_frontier_complexDisk z).1 z.property
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- Polar angle identifies the disk boundary with the additive circle. -/
def diskBoundaryCircle : AddCircle (1 : ℝ) ≃ₜ frontier complexDisk where
  toFun := diskBoundaryPoint
  invFun z := (puncturedPolarCoordinates (diskBoundaryPunctured z)).2
  left_inv := by
    intro t
    have h : diskBoundaryPunctured (diskBoundaryPoint t) =
        puncturedPolarCoordinates.symm (diskBoundaryRadius, t) := by
      apply Subtype.ext
      simp only [diskBoundaryPunctured, diskBoundaryPoint,
        Complex.equivRealProdCLM.symm_apply_apply]
    change (puncturedPolarCoordinates (diskBoundaryPunctured (diskBoundaryPoint t))).2 = t
    rw [h, Homeomorph.apply_symm_apply]
  right_inv := by
    intro z
    apply Subtype.ext
    change Complex.equivRealProdCLM
      (puncturedPolarCoordinates.symm
        (diskBoundaryRadius, (puncturedPolarCoordinates (diskBoundaryPunctured z)).2) : ℂ) = z
    have hr : (puncturedPolarCoordinates (diskBoundaryPunctured z)).1 = diskBoundaryRadius := by
      apply Subtype.ext
      rw [puncturedPolarCoordinates_radius]
      exact (mem_frontier_complexDisk z).1 z.property
    rw [← hr, Prod.mk.eta, Homeomorph.symm_apply_apply]
    exact Complex.equivRealProdCLM.apply_symm_apply z
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.equivRealProdCLM.continuous.comp
      (continuous_subtype_val.comp
        (puncturedPolarCoordinates.symm.continuous.comp (continuous_const.prodMk continuous_id)))
  continuous_invFun := by
    apply Continuous.snd
    apply puncturedPolarCoordinates.continuous.comp
    apply Continuous.subtype_mk
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_subtype_val

/-- The polar angle of a boundary point is its circle coordinate. -/
theorem diskBoundaryCircle_symm_apply (z : frontier complexDisk) :
    diskBoundaryCircle.symm z = (puncturedPolarCoordinates (diskBoundaryPunctured z)).2 := rfl

end
end FiniteAvalanches.Electrical.StatementGeometry
