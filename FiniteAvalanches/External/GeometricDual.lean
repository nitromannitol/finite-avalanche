import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.External.TwoPoleTopology

/-! Classical geometric duality for finite connected plane multigraph drawings. -/
set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

/-- The dual retains every original edge copy, crosses it once, and its faces
correspond to the original vertices with reversed double-dual orientation. -/
axiom finite_plane_geometric_dual :
∀ {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (J : CopiedGraph V E) (D : Drawing J)
    (charts : ∀ e : E, Source.EdgeChart D e)
    (_hc : (supportGraph J.left J.right).Preconnected),
    ∃ finiteFaces : Fintype (Face D),
      letI : Fintype (Face D) := finiteFaces
      let dualGraph : CopiedGraph (Face D) E :=
        ⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩
      ∃ dualDrawing : Drawing dualGraph,
      ∃ dualCharts : ∀ e : E, Source.EdgeChart dualDrawing e,
      ∃ vertexFaces : V ≃ Face dualDrawing,
        (∀ F : Face D, dualDrawing.point F ∈ faceRegion D F) ∧
        (∀ v : V, D.point v ∈ faceRegion dualDrawing (vertexFaces v)) ∧
        (∀ (e f : E) (s t : ArcParameter),
          D.curve e s = dualDrawing.curve f t ↔
            e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
        (∀ (e : E) (t : ArcParameter),
          (t.val < 1 / 2 →
            dualDrawing.curve e t ∈ faceRegion D (dualGraph.left e)) ∧
          (1 / 2 < t.val →
            dualDrawing.curve e t ∈ faceRegion D (dualGraph.right e))) ∧
        (∀ e : E, ∃ radius : ℝ, 0 < radius ∧ radius < (charts e).radius ∧
          ∀ t : ArcParameter, |t.val - 1 / 2| < radius →
            (charts e).chart.map (dualDrawing.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
        (∀ e : E,
          positiveChartFace dualDrawing e (dualCharts e) = vertexFaces (J.left e) ∧
          negativeChartFace dualDrawing e (dualCharts e) = vertexFaces (J.right e))

end FiniteAvalanches.External
