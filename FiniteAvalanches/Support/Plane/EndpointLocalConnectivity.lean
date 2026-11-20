import FiniteAvalanches.Support.Plane.ArcComponentPreservation
import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Local connectivity near an arc endpoint

Janiszewski's theorem controls the complement of a short initial subarc in a
ball, giving connected neighborhoods of an endpoint in the arc complement.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric

/-- Adjoining an arc along a preconnected intersection preserves each component
of the complement of a compact plane set. -/
theorem connectedComponentIn_compl_union_path
    {K : Set (ℝ × ℝ)} {x y a b : ℝ × ℝ}
    (hK : IsCompact K) (p : Path x y) (hp : Function.Injective p)
    (hPK : IsPreconnected (range p ∩ K))
    (ha : a ∉ range p ∪ K) (hb : b ∉ range p ∪ K)
    (hconn : b ∈ connectedComponentIn Kᶜ a) :
    b ∈ connectedComponentIn (range p ∪ K)ᶜ a := by
  simpa only [union_empty] using
    (connectedComponentIn_compl_union_path_two hK isCompact_empty p hp hPK
      (by simp only [inter_empty]; exact isPreconnected_empty)
      (by simpa only [union_empty] using ha)
      (by simpa only [union_empty] using hb)
      (by simpa only [union_empty] using hconn))

end FiniteAvalanches.Electrical.StatementGeometry
