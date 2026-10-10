import FiniteAvalanches.Electrical.Geometry.ConnectedDrawingQuotient
import FiniteAvalanches.Electrical.Geometry.BSST

set_option autoImplicit false

open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source (Plane drawingTrace)
open FiniteAvalanches.Electrical.BSST (Face faceRegion incident)
open FiniteAvalanches.Electrical.DrawingContraction (restrictDrawing)

namespace FiniteAvalanches.External

/-- Punctured-plane inversion transports all copied curves and complement faces. -/
axiom plane_punctured_face_transport : (
  ∀ {V E E₀ : Type} [Fintype V] [Fintype E] [Fintype E₀]
    (J : CopiedGraph V E) (K : CopiedGraph V E₀) (D : Drawing J)
    (i : E₀ → E) (hi : Function.Injective i)
    (hl : ∀ e, J.left (i e) = K.left e)
    (hr : ∀ e, J.right (i e) = K.right e)
    (F : Face (restrictDrawing D i hi hl hr)),
  let R := restrictDrawing D i hi hl hr
  ∃ p : Plane, ∃ hp : p ∉ drawingTrace D,
    p ∈ faceRegion R F ∧
    ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
      (∀ z : {z : Plane // z ≠ p},
        (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
      ∃ D' : Drawing J,
        (∀ v, D'.point v = (c ⟨D.point v, by
          intro heq
          apply hp
          exact heq ▸ (Or.inl (Set.mem_range_self v) : D.point v ∈ drawingTrace D)⟩).val) ∧
        (∀ e t, D'.curve e t = (c ⟨D.curve e t, by
          intro heq
          apply hp
          exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
            D.curve e t ∈ drawingTrace D)⟩).val) ∧
        let R' := restrictDrawing D' i hi hl hr
        ∃ faces : Face R ≃ Face R',
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ faceRegion R G ↔ (c z).val ∈ faceRegion R' (faces G)) ∧
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ closure (faceRegion R G) ↔
              (c z).val ∈ closure (faceRegion R' (faces G))) ∧
          (∀ G : Face R, ∀ v : V, incident R v G ↔ incident R' v (faces G)) ∧
          (∀ e : E, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
            D.curve e t ∈ closure (D.curve e '' S) ↔
              D'.curve e t ∈ closure (D'.curve e '' S)) ∧
          ¬Bornology.IsBounded (faceRegion R' (faces F))
  )

end FiniteAvalanches.External
