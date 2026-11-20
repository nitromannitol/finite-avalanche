import FiniteAvalanches.Electrical.Geometry.SourceHDual
import FiniteAvalanches.Support.Plane.EdgeFaceIncidence
import FiniteAvalanches.Support.Plane.HalfOpenLocalStraightening

/-! Chart-side incidence along a plane edge, proved from local straightening. -/
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
set_option autoImplicit false

namespace FiniteAvalanches.External

/-- Both chart-side faces are incident to the whole nonloop copied curve. -/
theorem plane_edge_chart_incidence : (∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (R : Drawing J) (e : E) (c : EdgeChart R e),
  J.left e ≠ J.right e →
  Set.range (R.curve e) ⊆ closure (faceRegion R (positiveChartFace R e c)) ∧
  Set.range (R.curve e) ⊆ closure (faceRegion R (negativeChartFace R e c)) ) := by
  intro V E _ _ J R e c hne
  exact chart_faces_incident_of_straightenable_subarcs R e c
    (fun t ht0 ht1 => R.exists_interior_straightening e t ht0 ht1)

end FiniteAvalanches.External
