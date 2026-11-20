import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Data.Set.Finite.Lemmas
import FiniteAvalanches.Support.Plane.VertexFaceConnectivity
import FiniteAvalanches.Support.Plane.ChartConstruction
import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity

/-! Face incidence and edge-connectedness around a vertex of a finite plane drawing. -/

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

/-- Pure finite plane vertex-star topology on actual complement-component faces. -/
theorem plane_vertex_face_star : ∀ (V E : Type) [Fintype V] [Fintype E] [Nonempty E]
    (J : CopiedGraph V E) (D : Drawing J),
    (∀ u v, J.reaches Finset.univ u v) →
    ∀ x : V,
      {F : Face D | incident D x F}.Nonempty ∧
      {F : Face D | incident D x F}.Finite ∧
      (∀ F : Face D, incident D x F ↔
        ∃ e : E, (J.left e = x ∨ J.right e = x) ∧ F ∈ edgeFaces D e) ∧
      (∀ F G : Face D, incident D x F → incident D x G →
        Relation.ReflTransGen
          (fun A B : Face D => ∃ e : E,
            (J.left e = x ∨ J.right e = x) ∧
            A ∈ edgeFaces D e ∧ B ∈ edgeFaces D e) F G) := by
  intro V E _ _ _ J D hconn x
  have hx := exists_incident_copy J (J.supportGraph_preconnected_of_reaches hconn) x
  refine ⟨(vertex_incident_faces_finite_nonempty D x).1,
    (vertex_incident_faces_finite_nonempty D x).2, ?_, ?_⟩
  · intro F
    exact incident_iff_exists_incident_edge D x hx F
  · intro F G hF hG
    exact vertex_face_star_connected D x F G hF hG

end FiniteAvalanches.External
