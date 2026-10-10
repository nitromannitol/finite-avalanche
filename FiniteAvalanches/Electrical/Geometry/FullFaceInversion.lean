import FiniteAvalanches.External.PlanePuncturedFaceTransport
import FiniteAvalanches.Electrical.Geometry.PunctureTransport

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.PunctureTransport
open StatementGeometry Source BSST DrawingContraction
noncomputable section
variable {V E : Type} [instV : Fintype V] [instE : Fintype E] {J : CopiedGraph V E}

/-- Restricting to every original copy changes no point or curve. -/
theorem restrictDrawing_id (Q : Drawing J) :
    restrictDrawing Q id Function.injective_id (fun _ => rfl) (fun _ => rfl) = Q :=
  drawing_eq_of_points_curves _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- The registered inversion transports every full-graph complement face. -/
theorem full_face_inversion_transport (Q : Drawing J) (F : Face Q) :
  ∃ p : Plane, ∃ hp : p ∉ drawingTrace Q,
    p ∈ faceRegion Q F ∧
    ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
      (∀ z : {z : Plane // z ≠ p},
        (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
      ∃ D' : Drawing J,
        (∀ v, D'.point v = (c ⟨Q.point v, by
          intro heq
          apply hp
          exact heq ▸ (Or.inl (Set.mem_range_self v) : Q.point v ∈ drawingTrace Q)⟩).val) ∧
        (∀ e t, D'.curve e t = (c ⟨Q.curve e t, by
          intro heq
          apply hp
          exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
            Q.curve e t ∈ drawingTrace Q)⟩).val) ∧
        ∃ faces : Face Q ≃ Face D',
          (∀ G : Face Q, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ faceRegion Q G ↔ (c z).val ∈ faceRegion D' (faces G)) ∧
          (∀ G : Face Q, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ closure (faceRegion Q G) ↔
              (c z).val ∈ closure (faceRegion D' (faces G))) ∧
          (∀ G : Face Q, ∀ v : V, incident Q v G ↔ incident D' v (faces G)) ∧
          (∀ e : E, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
            Q.curve e t ∈ closure (Q.curve e '' S) ↔
              D'.curve e t ∈ closure (D'.curve e '' S)) ∧
          ¬Bornology.IsBounded (faceRegion D' (faces F)) := by
  have h := External.plane_punctured_face_transport J J Q id
    Function.injective_id (fun _ => rfl) (fun _ => rfl)
  exact h F

end
end FiniteAvalanches.Electrical.PunctureTransport
