import FiniteAvalanches.Electrical.Geometry.BSSTStream
import FiniteAvalanches.Electrical.Plane.Incidence

/-! Polar dual copies on the actual complementary regions of a given outer arc. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Source
open StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The full geometric dual has one original-ID copy, including the added arc,
from the actual physical right face to the actual physical left face. -/
def augmentedDual {D : PlaneEmbedding J} {alpha beta : V} (A : OuterArc D alpha beta) :
    CopiedGraph A.embedding.Face (E ⊕ Unit) :=
  ⟨A.embedding.rightFace, A.embedding.leftFace⟩

/-- Removing ONLY the distinguished dual copy retains every original wire, even
when its two geometric face endpoints coincide. No coordinate or edge is chosen. -/
def polarDual {D : PlaneEmbedding J} {alpha beta : V} (A : OuterArc D alpha beta) :
    CopiedGraph A.embedding.Face E :=
  ⟨fun e => A.embedding.rightFace (.inl e), fun e => A.embedding.leftFace (.inl e)⟩

/-- Zero stream ground is on the right of the actual alpha-to-beta outer arc. -/
def polarGround {D : PlaneEmbedding J} {alpha beta : V} (A : OuterArc D alpha beta) :
    A.embedding.Face := A.embedding.rightFace (.inr ())

/-- Unit injection is on the left of the SAME actual outer arc. -/
def polarSource {D : PlaneEmbedding J} {alpha beta : V} (A : OuterArc D alpha beta) :
    A.embedding.Face := A.embedding.leftFace (.inr ())

/-- Both dual carriers preserve precisely the original E IDs and their incidence. -/
theorem polarDual_copy {D : PlaneEmbedding J} {alpha beta : V}
    (A : OuterArc D alpha beta) (e : E) :
    (polarDual A).left e = (augmentedDual A).left (.inl e) ∧
      (polarDual A).right e = (augmentedDual A).right (.inl e) := ⟨rfl,rfl⟩

/-- The half-open Drawing's permissive loop carrier causes no extra hypothesis:
full source arc injectivity already excludes a loop in a PlaneEmbedding. -/
theorem PlaneEmbedding.endpoints_ne (D : PlaneEmbedding J) (e : E) : J.left e ≠ J.right e := by
  intro he
  have hc : D.drawing.curve e ⟨0,by norm_num⟩ = D.drawing.curve e ⟨1,by norm_num⟩ := by
    rw [D.drawing.start,D.drawing.finish,he]
  have ht := congrArg Subtype.val (D.edge_injective e hc)
  norm_num at ht

end
end FiniteAvalanches.Electrical.Source
