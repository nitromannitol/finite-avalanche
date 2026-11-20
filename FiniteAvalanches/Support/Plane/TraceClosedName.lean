import FiniteAvalanches.Electrical.Geometry.DrawingProperness

/-!
# Closedness of the drawn trace for the punctured transport

The closedness of the trace of a plane drawing is stated in the source namespace
and, for the statement-geometry support modules, again in that namespace. This
module gives the punctured transport namespace its own name for the statement,
so that the short name keeps a single meaning there when both namespaces are open.
-/

namespace FiniteAvalanches.Electrical.PunctureTransport

open FiniteAvalanches.Electrical.StatementGeometry

/-- The trace of a plane drawing is closed. -/
theorem drawingTrace_isClosed {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) : IsClosed (Source.drawingTrace D) :=
  Source.drawingTrace_isClosed D

end FiniteAvalanches.Electrical.PunctureTransport
