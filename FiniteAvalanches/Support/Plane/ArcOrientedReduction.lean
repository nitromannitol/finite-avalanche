import FiniteAvalanches.Support.Plane.DiskReflection
import FiniteAvalanches.Support.Plane.ChartConstruction
import FiniteAvalanches.Support.Plane.ChartOrientation

/-!
# Oriented straightening from a disk image

An oriented realization of the image of a disk upgrades a plane homeomorphism
straightening an arc to an oriented straightening of that arc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- If an oriented chart realizes the image of the disk, a homeomorphism
agrees on the disk with an oriented chart up to reflection of the domain. -/
theorem exists_orientedChart_agree_on_complexDisk_of_image
    (f : Plane ≃ₜ Plane) (c : OrientedChart)
    (hc : c.map '' complexDisk = f '' complexDisk) :
    (∃ d : OrientedChart, ∀ x ∈ complexDisk, d.map x = f x) ∨
    (∃ d : OrientedChart, ∀ x ∈ complexDisk, d.map x = f (planeReflection x)) := by
  let g := f.trans c.map.symm
  have hg : g '' complexDisk = complexDisk := by
    change (c.map.symm ∘ f) '' complexDisk = complexDisk
    rw [image_comp, ← hc, ← image_comp]
    simp only [Homeomorph.symm_comp_self, image_id]
  rcases exists_orientedChart_agree_on_complexDisk_or_reflect g hg with h | h
  · left
    obtain ⟨d, hd⟩ := h
    refine ⟨d.trans c, ?_⟩
    intro x hx
    change c.map (d.map x) = f x
    rw [hd x hx]
    exact c.map.apply_symm_apply (f x)
  · right
    obtain ⟨d, hd⟩ := h
    refine ⟨d.trans c, ?_⟩
    intro x hx
    change c.map (d.map x) = f (planeReflection x)
    rw [hd x hx]
    exact c.map.apply_symm_apply (f (planeReflection x))

/-- The reflection fixes the horizontal axis pointwise. -/
theorem planeReflection_horizontal (t : ℝ) : planeReflection (t, 0) = (t, 0) := by
  apply Complex.equivRealProdCLM.symm.injective
  simp [planeReflection, Complex.equivRealProdCLM_symm_apply]

/-- The horizontal unit segment is contained in the radius-two disk. -/
theorem horizontal_unit_segment_mem_complexDisk (t : unitInterval) :
    (t.val, 0) ∈ complexDisk := by
  rw [mem_complexDisk]
  change ‖(t.val : ℂ)‖ ≤ 2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  linarith [t.property.2]

/-- A straightening whose inverse disk image has an oriented realization has
an oriented parameter-preserving straightening. -/
theorem exists_orientedChart_straightening_of_disk_image
    (gamma : unitInterval → Plane) (f : Plane ≃ₜ Plane)
    (hf : ∀ t, f (gamma t) = (t.val, 0))
    (c : OrientedChart) (hc : c.map '' complexDisk = f.symm '' complexDisk) :
    ∃ d : OrientedChart, ∀ t, d.map (gamma t) = (t.val, 0) := by
  have hgamma (t : unitInterval) : f.symm (t.val, 0) = gamma t := by
    rw [← hf t, f.symm_apply_apply]
  rcases exists_orientedChart_agree_on_complexDisk_of_image f.symm c hc with h | h
  · obtain ⟨d, hd⟩ := h
    refine ⟨d.symm, ?_⟩
    intro t
    apply d.map.injective
    change d.map (d.map.symm (gamma t)) = d.map (t.val, 0)
    rw [d.map.apply_symm_apply, hd _ (horizontal_unit_segment_mem_complexDisk t), hgamma]
  · obtain ⟨d, hd⟩ := h
    refine ⟨d.symm, ?_⟩
    intro t
    apply d.map.injective
    change d.map (d.map.symm (gamma t)) = d.map (t.val, 0)
    rw [d.map.apply_symm_apply, hd _ (horizontal_unit_segment_mem_complexDisk t),
      planeReflection_horizontal, hgamma]

end
end FiniteAvalanches.Electrical.StatementGeometry
