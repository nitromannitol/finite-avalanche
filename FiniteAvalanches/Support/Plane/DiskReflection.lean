import FiniteAvalanches.Support.Plane.DiskBoundaryCoordinates
import FiniteAvalanches.Support.Plane.CircleReflection

/-!
# Reflection of disk boundary maps

Complex conjugation preserves the disk and reverses its angular coordinate.
Consequently every disk-preserving homeomorphism agrees on the disk with an
oriented chart after at most one reflection of its domain.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- Reflection of the plane across the real axis in complex coordinates. -/
def planeReflection : Plane ≃ₜ Plane :=
  Complex.equivRealProdCLM.symm.toHomeomorph.trans
    (Complex.conjCLE.toHomeomorph.trans Complex.equivRealProdCLM.toHomeomorph)

/-- Plane reflection preserves the closed disk. -/
theorem planeReflection_image_complexDisk : planeReflection '' complexDisk = complexDisk := by
  have hmem (x : Plane) : planeReflection x ∈ complexDisk ↔ x ∈ complexDisk := by
    rw [mem_complexDisk, mem_complexDisk]
    change ‖starRingEnd ℂ (Complex.equivRealProdCLM.symm x)‖ ≤ 2 ↔ _
    rw [Complex.norm_conj]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hmem y).2 hy
  · intro hx
    refine ⟨planeReflection.symm x, (hmem _).1 ?_, planeReflection.apply_symm_apply x⟩
    simpa only [planeReflection.apply_symm_apply] using hx

/-- Plane reflection negates the angular parameter of each boundary point. -/
theorem planeReflection_diskBoundaryCircle (t : AddCircle (1 : ℝ)) :
    planeReflection (diskBoundaryCircle t : Plane) = diskBoundaryCircle (-t) := by
  change Complex.equivRealProdCLM (starRingEnd ℂ
    ((2 : ℝ) • (AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num) t : ℂ))) =
    Complex.equivRealProdCLM
      ((2 : ℝ) • (AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num) (-t) : ℂ))
  congr 1
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

/-- The circle boundary map represents the plane action at boundary points. -/
theorem diskBoundaryCircle_map (f : Plane ≃ₜ Plane) (hf : f '' complexDisk = complexDisk)
    (t : AddCircle (1 : ℝ)) :
    (diskBoundaryCircle (diskBoundaryMap f hf t) : Plane) = f (diskBoundaryCircle t) := by
  have h := diskBoundaryMap_apply f hf (diskBoundaryCircle t)
  rw [diskBoundaryCircle.symm_apply_apply] at h
  have h' := congrArg (fun z : AddCircle (1 : ℝ) => (diskBoundaryCircle z : Plane)) h
  simpa only [diskBoundaryCircle.apply_symm_apply] using h'

/-- Reflection induces negation as its boundary circle map. -/
theorem diskBoundaryMap_planeReflection :
    diskBoundaryMap planeReflection planeReflection_image_complexDisk = Homeomorph.neg _ := by
  ext t
  apply diskBoundaryCircle.injective
  apply Subtype.ext
  change (diskBoundaryCircle (diskBoundaryMap planeReflection planeReflection_image_complexDisk t) : Plane) =
    diskBoundaryCircle (-t)
  rw [diskBoundaryCircle_map, planeReflection_diskBoundaryCircle]

/-- Every disk-preserving homeomorphism, possibly after reflecting its domain,
agrees on the disk with an oriented chart. -/
theorem exists_orientedChart_agree_on_complexDisk_or_reflect
    (f : Plane ≃ₜ Plane) (hf : f '' complexDisk = complexDisk) :
    (∃ c : OrientedChart, ∀ x ∈ complexDisk, c.map x = f x) ∨
    (∃ c : OrientedChart, ∀ x ∈ complexDisk, c.map x = f (planeReflection x)) := by
  let g := planeReflection.trans f
  have hg : g '' complexDisk = complexDisk := by
    change (f ∘ planeReflection) '' complexDisk = complexDisk
    rw [image_comp, planeReflection_image_complexDisk, hf]
  have hmap : diskBoundaryMap g hg =
      (Homeomorph.neg _).trans (diskBoundaryMap f hf) := by
    ext t
    apply diskBoundaryCircle.injective
    apply Subtype.ext
    change (diskBoundaryCircle (diskBoundaryMap g hg t) : Plane) =
      diskBoundaryCircle (diskBoundaryMap f hf (-t))
    rw [diskBoundaryCircle_map, diskBoundaryCircle_map]
    change f (planeReflection (diskBoundaryCircle t)) = _
    rw [planeReflection_diskBoundaryCircle]
  rcases circle_homeomorph_normalized_cut_or_reflect (diskBoundaryMap f hf) with h | h
  · exact Or.inl (exists_orientedChart_agree_on_complexDisk_of_boundaryMap f hf h)
  · right
    rw [← hmap] at h
    exact exists_orientedChart_agree_on_complexDisk_of_boundaryMap g hg h

end
end FiniteAvalanches.Electrical.StatementGeometry
