import FiniteAvalanches.Support.Plane.AnnulusRotation

/-!
# Isotopy of circle homeomorphisms

A circle homeomorphism with increasing normalized cut is joined to the
identity by a jointly continuous family of equivalences and their inverses.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A circle homeomorphism with increasing normalized cut is isotopic to the
identity, with jointly continuous forward and inverse families. -/
theorem exists_circle_isotopy_of_normalized_cut
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F))) :
    ∃ E : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ),
      Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => E p.1 p.2) ∧
      Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (E p.1).symm p.2) ∧
      (∀ z, E 0 z = z) ∧ (∀ z, E 1 z = F z) := by
  obtain ⟨f, hf, hrep⟩ := exists_interval_homeomorph_of_circleCutMap
    (normalizedCircleHomeomorph F) (normalizedCircleHomeomorph_zero F) hinc
  obtain ⟨A, hA, hAi, hA0, hA1⟩ := exists_addCircle_isotopy_of_interval_homeomorph f hf
  obtain ⟨r, _, hr⟩ := AddCircle.eq_coe_Ico (F 0)
  let q : unitInterval → AddCircle (1 : ℝ) := fun t => (((t : ℝ) * r : ℝ) : AddCircle (1 : ℝ))
  have hq : Continuous q := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_subtype_val.mul continuous_const)
  let E : unitInterval → AddCircle (1 : ℝ) ≃ AddCircle (1 : ℝ) :=
    fun t => (A t).trans (Equiv.addRight (q t))
  have hE : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => E p.1 p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => A p.1 p.2 + q p.1)
    exact hA.add (hq.comp continuous_fst)
  have hEi : Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (E p.1).symm p.2) := by
    change Continuous (fun p : unitInterval × AddCircle (1 : ℝ) => (A p.1).symm (p.2 - q p.1))
    exact hAi.comp (continuous_fst.prodMk (continuous_snd.sub (hq.comp continuous_fst)))
  refine ⟨E, hE, hEi, ?_, ?_⟩
  · intro z
    change A 0 z + q 0 = z
    rw [hA0]
    change z + (((0 : ℝ) * r : ℝ) : AddCircle (1 : ℝ)) = z
    simp only [zero_mul, AddCircle.coe_zero, add_zero]
  · intro z
    obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico z
    let t : unitInterval := ⟨x, ⟨hx.1, hx.2.le⟩⟩
    change A 1 ((x : ℝ) : AddCircle (1 : ℝ)) + q 1 = F ((x : ℝ) : AddCircle (1 : ℝ))
    have h := hA1 t
    change A 1 ((x : ℝ) : AddCircle (1 : ℝ)) = _ at h
    rw [h, hrep t]
    change normalizedCircleHomeomorph F ((x : ℝ) : AddCircle (1 : ℝ)) + q 1 = _
    change (F ((x : ℝ) : AddCircle (1 : ℝ)) + -F 0) +
      (((1 : ℝ) * r : ℝ) : AddCircle (1 : ℝ)) = _
    simp only [one_mul, hr, neg_add_cancel_right]

end FiniteAvalanches.Electrical.StatementGeometry
