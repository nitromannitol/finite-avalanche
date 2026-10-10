import FiniteAvalanches.Electrical.Geometry.BSST

set_option autoImplicit false

open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source (Plane drawingTrace EdgeChart)
open FiniteAvalanches.Electrical.BSST (Face faceRegion negativeChartFace positiveChartFace)

namespace FiniteAvalanches.External

/-- Explicit holomorphic puncture transport preserves both actual oriented chart faces. -/
axiom plane_punctured_chart_face_transport : (∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (Q : Drawing J)
    (p : Plane) (hp : p ∉ drawingTrace Q)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (_hformula : ∀ z : {z : Plane // z ≠ p},
      (c z).val =
        ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
         -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2)))
    (Q' : Drawing J)
    (_hcurve : ∀ e t, Q'.curve e t = (c ⟨Q.curve e t, by
      intro heq
      apply hp
      exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
        Q.curve e t ∈ drawingTrace Q)⟩).val)
    (faces : Face Q ≃ Face Q')
    (_hregion : ∀ F : Face Q, ∀ z : {z : Plane // z ≠ p},
      z.val ∈ faceRegion Q F ↔ (c z).val ∈ faceRegion Q' (faces F))
    (e : E) (original : EdgeChart Q e) (transported : EdgeChart Q' e),
    faces (negativeChartFace Q e original) = negativeChartFace Q' e transported ∧
    faces (positiveChartFace Q e original) = positiveChartFace Q' e transported)

end FiniteAvalanches.External
