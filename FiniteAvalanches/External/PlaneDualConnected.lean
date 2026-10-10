import FiniteAvalanches.Electrical.Geometry.BSST

set_option autoImplicit false
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

namespace FiniteAvalanches.External

/-- The supporting graph of the geometric dual of a connected plane graph is connected. -/
axiom finite_plane_dual_connected : (∀ {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
      (J : CopiedGraph V E) (D : Drawing J)
      (charts : ∀ e : E, Source.EdgeChart D e)
      (_hc : (supportGraph J.left J.right).Preconnected),
      let dualGraph : CopiedGraph (Face D) E :=
        ⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩
      (supportGraph dualGraph.left dualGraph.right).Preconnected : Prop)

end FiniteAvalanches.External
