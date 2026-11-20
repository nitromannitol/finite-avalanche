import FiniteAvalanches.Support.Plane.HomeomorphPasting
import FiniteAvalanches.Support.Plane.ComplexOrientedChart

/-!
# Oriented charts agreeing on a disk

A plane homeomorphism whose restriction to a disk has an increasing circle
boundary map agrees on that disk with an oriented chart.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- The radius-two complex disk in product coordinates. -/
def complexDisk : Set Plane :=
  Complex.equivRealProdCLM '' Metric.closedBall (0 : ℂ) 2

/-- Membership in the disk is expressed by the complex norm. -/
theorem mem_complexDisk (z : Plane) :
    z ∈ complexDisk ↔ ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 := by
  let C : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph
  change z ∈ C '' Metric.closedBall (0 : ℂ) 2 ↔ _
  rw [C.image_eq_preimage_symm]
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  rfl

/-- A disk-preserving homeomorphism with an increasing polar boundary map
agrees throughout the disk with an oriented chart. -/
theorem exists_orientedChart_agree_on_complexDisk
    (f : Plane ≃ₜ Plane) (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F)))
    (himage : f '' complexDisk = complexDisk)
    (hboundary : ∀ x : ({0}ᶜ : Set ℂ), ‖(x : ℂ)‖ = 2 →
      f (Complex.equivRealProdCLM x) = Complex.equivRealProdCLM
        (puncturedPolarCoordinates.symm
          ((puncturedPolarCoordinates x).1, F (puncturedPolarCoordinates x).2) : ℂ)) :
    ∃ c : OrientedChart, ∀ x ∈ complexDisk, c.map x = f x := by
  obtain ⟨c, _, hnorm, hradial⟩ := exists_orientedChart_with_radial_action F hinc
  have hcmem (z : Plane) : c.map z ∈ complexDisk ↔ z ∈ complexDisk := by
    rw [mem_complexDisk, mem_complexDisk]
    have h := hnorm (Complex.equivRealProdCLM.symm z)
    simpa only [Complex.equivRealProdCLM.apply_symm_apply] using Iff.of_eq (congrArg (· ≤ 2) h)
  have hcimage : c.map '' complexDisk = complexDisk := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hcmem x).2 hx
    · intro hz
      refine ⟨c.map.symm z, ?_, c.map.apply_symm_apply z⟩
      exact (hcmem _).1 (by simpa only [c.map.apply_symm_apply] using hz)
  have hcompact : IsCompact complexDisk :=
    (isCompact_closedBall (0 : ℂ) 2).image Complex.equivRealProdCLM.continuous
  have hfrontier (z : Plane) (hz : z ∈ frontier complexDisk) : f z = c.map z := by
    let C : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph
    have hz' : z ∈ C '' frontier (Metric.closedBall (0 : ℂ) 2) := by
      rw [C.image_frontier]
      exact hz
    obtain ⟨w, hw, rfl⟩ := hz'
    have hw2 : ‖w‖ = 2 := by
      have hw' := Metric.frontier_closedBall_subset_sphere hw
      simpa only [Metric.mem_sphere, dist_zero_right] using hw'
    have hw0 : w ≠ 0 := by
      intro h
      simp only [h, norm_zero] at hw2
      norm_num at hw2
    let x : ({0}ᶜ : Set ℂ) := ⟨w, by simpa only [mem_compl_iff, mem_singleton_iff] using hw0⟩
    change f (Complex.equivRealProdCLM x) = c.map (Complex.equivRealProdCLM x)
    rw [hboundary x hw2, hradial x (by linarith [hw2])]
  exact exists_orientedChart_agree_on_compact f c complexDisk hcompact
    (himage.trans hcimage.symm) hfrontier

end
end FiniteAvalanches.Electrical.StatementGeometry
