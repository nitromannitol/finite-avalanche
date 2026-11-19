import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.HalfOpenLocalStraightening
import FiniteAvalanches.Support.Plane.DualConnectedIncidence

set_option autoImplicit false
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

namespace FiniteAvalanches.External

/-- The supporting graph of the geometric dual of a connected plane graph is connected. -/
theorem finite_plane_dual_connected : (∀ {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
      (J : CopiedGraph V E) (D : Drawing J)
      (charts : ∀ e : E, Source.EdgeChart D e)
      (_hc : (supportGraph J.left J.right).Preconnected),
      let dualGraph : CopiedGraph (Face D) E :=
        ⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩
      (supportGraph dualGraph.left dualGraph.right).Preconnected : Prop) := by
  intro V E _ _ _ J D charts hc
  exact chartDualGraph_preconnected_of_straightenable_subarcs D charts
    (fun e t ht0 ht1 => D.exists_interior_straightening e t ht0 ht1)

end FiniteAvalanches.External
