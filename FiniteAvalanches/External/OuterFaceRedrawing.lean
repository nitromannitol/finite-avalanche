import FiniteAvalanches.Electrical.Geometry.BSST

namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical

/-- A simple path on the unbounded face can be redrawn on the disk boundary
on the identical original copied graph, allowing rearrangement at cutvertices. -/
axiom outer_face_simple_path_disk_redrawing : (∀ {W A : Type} [Fintype W] [Fintype A]
  (J : CopiedGraph W A) (D : Drawing J),
  (supportGraph J.left J.right).Preconnected →
  ∀ (m : ℕ) (path : Fin (m+1) → W), Function.Injective path →
  ∀ (copies : Fin m → A),
  (∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
    (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ)) →
  ∀ F : BSST.Face D, ¬Bornology.IsBounded (BSST.faceRegion D F) →
  (∀ i t, D.curve (copies i) t ∈ frontier (BSST.faceRegion D F)) →
  ∃ D' : Drawing J, (∀ x, D'.point x ∈ disk) ∧
    (∀ e t, D'.curve e t ∈ disk) ∧ (∀ i t, D'.curve (copies i) t ∈ circle))

end FiniteAvalanches.External
