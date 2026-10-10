import FiniteAvalanches.Electrical.Geometry.SourceHDual
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
set_option autoImplicit false

namespace FiniteAvalanches.External

/-- Both chart-side faces are incident to the whole nonloop copied curve. -/
axiom plane_edge_chart_incidence : (∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (R : Drawing J) (e : E) (c : EdgeChart R e),
  J.left e ≠ J.right e →
  Set.range (R.curve e) ⊆ closure (faceRegion R (positiveChartFace R e c)) ∧
  Set.range (R.curve e) ⊆ closure (faceRegion R (negativeChartFace R e c)) )

end FiniteAvalanches.External
