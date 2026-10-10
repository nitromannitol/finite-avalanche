import FiniteAvalanches.Electrical.Geometry.OrientedDrawing

namespace FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.StatementGeometry
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The full drawn finite graph is compact, including every copied arc and vertex. -/
theorem drawingTrace_isCompact (D : Drawing J) : IsCompact (drawingTrace D) :=
  (Set.finite_range D.point).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (D.continuous e))

/-- The actual face carrier is the complement of a closed embedded graph. -/
theorem drawingTrace_isClosed (D : Drawing J) : IsClosed (drawingTrace D) :=
  (drawingTrace_isCompact D).isClosed

end FiniteAvalanches.Electrical.Source
