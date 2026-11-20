import FiniteAvalanches.Support.Plane.CircleQuotient

/-!
# Extending circle isotopies over a cylinder

A jointly continuous circle isotopy and its inverse define a homeomorphism of
the cylinder, preserving its interval coordinate and acting on its boundary.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

/-- A jointly continuous family of equivalences with jointly continuous inverse
induces a homeomorphism of the product preserving the first coordinate. -/
def cylinderHomeomorph {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    (e : T → X ≃ X) (he : Continuous (fun p : T × X => e p.1 p.2))
    (hei : Continuous (fun p : T × X => (e p.1).symm p.2)) : T × X ≃ₜ T × X where
  toFun p := (p.1, e p.1 p.2)
  invFun p := (p.1, (e p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk he
  continuous_invFun := continuous_fst.prodMk hei

/-- An increasing interval homeomorphism extends to a homeomorphism of the
additive-circle cylinder, fixing one boundary and inducing the map on the other. -/
theorem exists_circle_cylinder_homeomorph
    (f : unitInterval ≃ₜ unitInterval) (hf : StrictMono f) :
    ∃ H : unitInterval × AddCircle (1 : ℝ) ≃ₜ unitInterval × AddCircle (1 : ℝ),
      (∀ p, (H p).1 = p.1) ∧
      (∀ z, H (0, z) = (0, z)) ∧
      (∀ x : unitInterval,
        H (1, ((x : ℝ) : AddCircle (1 : ℝ))) =
          (1, (((f x : unitInterval) : ℝ) : AddCircle (1 : ℝ)))) := by
  obtain ⟨e, he, hei, he0, he1⟩ := exists_addCircle_isotopy_of_interval_homeomorph f hf
  refine ⟨cylinderHomeomorph e he hei, fun _ => rfl, ?_, ?_⟩
  · intro z
    change (0, e 0 z) = (0, z)
    rw [he0]
  · intro x
    change (1, e 1 ((x : ℝ) : AddCircle (1 : ℝ))) = _
    rw [he1]

end FiniteAvalanches.Electrical.StatementGeometry
