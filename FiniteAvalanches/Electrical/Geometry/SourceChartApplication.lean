import FiniteAvalanches.Electrical.Geometry.EdgeCharts
import FiniteAvalanches.External.ArcStraightening
import FiniteAvalanches.External.BSST
import Lean

namespace FiniteAvalanches.Electrical.ChartExistence
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section

/-- Exact ordinary successor: supply the audited pure standard internally.
The actual chosen face remains unbounded; no face redrawing is asserted. -/
theorem source_outer_arc_of_unbounded_face
    {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E) (D : Drawing J)
    (hloop : ∀ e, J.left e ≠ J.right e)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (F : BSST.Face D)
    (ha : BSST.incident D alpha F) (hb : BSST.incident D beta F)
    (hu : ¬Bornology.IsBounded (BSST.faceRegion D F)) :
    ∃ charts : ∀ e, EdgeChart D e,
      ∃ O : OuterArc (planeEmbeddingOfCharts D hloop charts) alpha beta, O.face = F := by
  obtain ⟨charts⟩ := consume_arc_straightening FiniteAvalanches.External.parametrized_plane_arc_straightening D hloop
  obtain ⟨A⟩ := (FiniteAvalanches.External.bsst_square_tiling J D hc alpha beta hne F ha hb hu).1
  obtain ⟨augCharts⟩ := consume_auxiliary_straightening FiniteAvalanches.External.parametrized_plane_arc_straightening D hloop alpha beta hne F A
  let P := planeEmbeddingOfCharts D hloop charts
  let Q := planeEmbeddingOfCharts A.drawing (by
    intro z
    cases z with
    | inl e => exact hloop e
    | inr _ => exact hne) augCharts
  let O : OuterArc P alpha beta := {
    face := F
    alpha_incident := ha
    beta_incident := hb
    unbounded := hu
    embedding := Q
    point_eq := A.point_eq
    curve_eq := A.curve_eq
    interior_in_face := A.interior_in_face }
  exact ⟨charts, O, rfl⟩

end
end FiniteAvalanches.Electrical.ChartExistence

