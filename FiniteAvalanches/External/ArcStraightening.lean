import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import FiniteAvalanches.Support.Plane.OrientedArcStraightening

set_option autoImplicit false
namespace FiniteAvalanches.External

/-- Classical parametrized planar arc extension with a jointly continuous isotopy and inverse. -/
theorem parametrized_plane_arc_straightening :
∀ gamma : FiniteAvalanches.Electrical.StatementGeometry.ArcParameter →
    FiniteAvalanches.Electrical.Source.Plane,
  Continuous gamma → Function.Injective gamma →
    ∃ c : FiniteAvalanches.Electrical.Source.OrientedChart,
      ∀ t : FiniteAvalanches.Electrical.StatementGeometry.ArcParameter,
        c.map (gamma t) = (t.val, 0) :=
  fun gamma hc hi =>
    FiniteAvalanches.Electrical.StatementGeometry.exists_orientedChart_arc_straightening gamma hc hi

end FiniteAvalanches.External
