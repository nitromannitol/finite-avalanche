import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Data.Set.Finite.Lemmas

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

/-- Pure finite plane vertex-star topology on actual complement-component faces. -/
axiom plane_vertex_face_star : ∀ (V E : Type) [Fintype V] [Fintype E] [Nonempty E]
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
            A ∈ edgeFaces D e ∧ B ∈ edgeFaces D e) F G)

end FiniteAvalanches.External
