import FiniteAvalanches.Support.Plane.CircleReflection
import FiniteAvalanches.Electrical.Geometry.OrientedDrawing

/-!
# Oriented charts from complex-plane isotopies

A jointly continuous isotopy and inverse on the complex plane define an
oriented chart in product coordinates.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical.Source

/-- Transfer an isotopy of the complex plane to an oriented chart in product
coordinates. -/
noncomputable def orientedChartOfComplexIsotopy (G : unitInterval → ℂ ≃ₜ ℂ)
    (hG : Continuous (fun p : unitInterval × ℂ => G p.1 p.2))
    (hGi : Continuous (fun p : unitInterval × ℂ => (G p.1).symm p.2))
    (hG0 : ∀ z, G 0 z = z) : OrientedChart := by
  let C : Plane ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let K : unitInterval → Plane ≃ₜ Plane := fun t => C.trans ((G t).trans C.symm)
  refine ⟨K 1, K, ?_, ?_, ?_, rfl⟩
  · change Continuous (fun p : unitInterval × Plane => C.symm (G p.1 (C p.2)))
    exact C.symm.continuous.comp (hG.comp (continuous_fst.prodMk (C.continuous.comp continuous_snd)))
  · change Continuous (fun p : unitInterval × Plane => C.symm ((G p.1).symm (C p.2)))
    exact C.symm.continuous.comp (hGi.comp (continuous_fst.prodMk (C.continuous.comp continuous_snd)))
  · apply Homeomorph.ext
    intro x
    change C.symm (G 0 (C x)) = x
    rw [hG0, C.symm_apply_apply]

/-- The chart map is the endpoint of the original complex isotopy conjugated
by the complex and real-product coordinate maps. -/
theorem orientedChartOfComplexIsotopy_map (G : unitInterval → ℂ ≃ₜ ℂ)
    (hG : Continuous (fun p : unitInterval × ℂ => G p.1 p.2))
    (hGi : Continuous (fun p : unitInterval × ℂ => (G p.1).symm p.2))
    (hG0 : ∀ z, G 0 z = z) (z : ℂ) :
    (orientedChartOfComplexIsotopy G hG hGi hG0).map (Complex.equivRealProdCLM z) =
      Complex.equivRealProdCLM (G 1 z) := by
  change Complex.equivRealProdCLM (G 1 (Complex.equivRealProdCLM.symm
    (Complex.equivRealProdCLM z))) = _
  rw [Complex.equivRealProdCLM.symm_apply_apply]

/-- An increasing circle homeomorphism is realized by an oriented chart that
fixes the unit disk and acts by the given circle map at radii at least two. -/
theorem exists_orientedChart_of_circle_homeomorph
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F))) :
    ∃ c : OrientedChart,
      (∀ z : ℂ, ‖z‖ ≤ 1 → c.map (Complex.equivRealProdCLM z) = Complex.equivRealProdCLM z) ∧
      (∀ z : ℂ, ‖Complex.equivRealProdCLM.symm (c.map (Complex.equivRealProdCLM z))‖ = ‖z‖) ∧
      (∀ (x : ({0}ᶜ : Set ℂ)), 2 ≤ ‖(x : ℂ)‖ →
        ∃ y : ({0}ᶜ : Set ℂ),
          c.map (Complex.equivRealProdCLM x) = Complex.equivRealProdCLM y ∧
          (puncturedPolarCoordinates y).2 = F (puncturedPolarCoordinates x).2) := by
  obtain ⟨G, hG, hGi, hfix, hstart, hnorm, hangle⟩ :=
    exists_plane_isotopy_of_circle_homeomorph F hinc
  refine ⟨orientedChartOfComplexIsotopy G hG hGi hstart, ?_, ?_, ?_⟩
  · intro z hz
    rw [orientedChartOfComplexIsotopy_map, hfix 1 z hz]
  · intro z
    rw [orientedChartOfComplexIsotopy_map, Complex.equivRealProdCLM.symm_apply_apply,
      hnorm]
  · intro x hx
    obtain ⟨y, hy, hang⟩ := hangle x hx
    refine ⟨y, ?_, hang⟩
    rw [orientedChartOfComplexIsotopy_map, hy]

/-- An increasing circle homeomorphism extends to an oriented chart whose
radial action is explicit outside the disk of radius two. -/
theorem exists_orientedChart_with_radial_action
    (F : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hinc : StrictMono (circleCutMap (normalizedCircleHomeomorph F)
      (normalizedCircleHomeomorph_zero F))) :
    ∃ c : OrientedChart,
      (∀ z : ℂ, ‖z‖ ≤ 1 → c.map (Complex.equivRealProdCLM z) = Complex.equivRealProdCLM z) ∧
      (∀ z : ℂ, ‖Complex.equivRealProdCLM.symm (c.map (Complex.equivRealProdCLM z))‖ = ‖z‖) ∧
      (∀ (x : ({0}ᶜ : Set ℂ)), 2 ≤ ‖(x : ℂ)‖ →
        c.map (Complex.equivRealProdCLM x) = Complex.equivRealProdCLM
          (puncturedPolarCoordinates.symm
            ((puncturedPolarCoordinates x).1, F (puncturedPolarCoordinates x).2) : ℂ)) := by
  obtain ⟨c, hfix, hnorm, hangle⟩ := exists_orientedChart_of_circle_homeomorph F hinc
  refine ⟨c, hfix, hnorm, ?_⟩
  intro x hx
  obtain ⟨y, hy, hang⟩ := hangle x hx
  rw [hy]
  congr 1
  apply congrArg Subtype.val
  apply puncturedPolarCoordinates.injective
  apply Prod.ext
  · simp only [Homeomorph.apply_symm_apply, Prod.fst]
    apply Subtype.ext
    rw [puncturedPolarCoordinates_radius, puncturedPolarCoordinates_radius]
    have h := hnorm (x : ℂ)
    rw [hy, Complex.equivRealProdCLM.symm_apply_apply] at h
    exact h
  · simpa only [Homeomorph.apply_symm_apply, Prod.snd] using hang

end FiniteAvalanches.Electrical.StatementGeometry
