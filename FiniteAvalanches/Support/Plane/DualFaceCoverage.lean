import FiniteAvalanches.Support.Plane.DualAssembly
import FiniteAvalanches.Support.Plane.HalfOpenLocalStraightening

/-!
# Face coverage in finite plane drawings

The two chart faces of the edges cover the faces of a finite plane drawing.
The same fact gives surjectivity of a vertex-to-face map with the prescribed
oriented incidences.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST

/-- A finite drawing with an edge has at most two faces per copied edge. -/
theorem finite_faces_and_card_le {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {J : CopiedGraph V E} (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    Finite (Face D) ∧ Nat.card (Face D) ≤ 2 * Fintype.card E :=
  finite_faces_and_card_le_of_straightenable_subarcs D charts
    (fun e t ht0 ht1 => D.exists_interior_straightening e t ht0 ht1)

/-- Every face of a finite plane drawing occurs on one side of an edge chart. -/
theorem chartFace_surjective {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    {J : CopiedGraph V E} (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    Function.Surjective (Sum.elim (fun e => positiveChartFace D e (charts e))
      (fun e => negativeChartFace D e (charts e))) :=
  chartFace_surjective_of_straightenable_subarcs D charts
    (fun e t ht0 ht1 => D.exists_interior_straightening e t ht0 ht1)

/-- A vertex-to-face map covering both chart sides at every edge is surjective. -/
theorem vertexFace_surjective {V W E : Type} [Fintype V] [Fintype W] [Fintype E]
    [Nonempty E] {J : CopiedGraph V E} {J' : CopiedGraph W E} (D' : Drawing J')
    (charts : ∀ e, EdgeChart D' e) (vertexFace : V → Face D')
    (hinc : ∀ e, positiveChartFace D' e (charts e) = vertexFace (J.left e) ∧
      negativeChartFace D' e (charts e) = vertexFace (J.right e)) :
    Function.Surjective vertexFace :=
  vertexFace_surjective_of_straightenable_subarcs D' charts vertexFace hinc
    (fun e t ht0 ht1 => D'.exists_interior_straightening e t ht0 ht1)

end FiniteAvalanches.Electrical.StatementGeometry
