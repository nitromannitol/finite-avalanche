import FiniteAvalanches.Support.Plane.CopiedTreeCardinality
import FiniteAvalanches.Support.Plane.DualFaceCoverage
import FiniteAvalanches.External.PlaneTreeComplement
import FiniteAvalanches.Electrical.Trees.CopiedTreeExistence

/-!
# Vertices of a geometric double dual

The two tree-complement equivalences show that the original graph and the
chart-defined double dual have spanning trees with the same copied edges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST
open scoped Classical

/-- A double-dual vertex-face map with the prescribed incidences is injective. -/
theorem vertexFace_injective_of_dual_drawing {V E : Type} [Fintype V] [Fintype E]
    [Nonempty E] (J : CopiedGraph V E) (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) [Fintype (Face D)]
    (hconn : (supportGraph J.left J.right).Preconnected)
    (Q : Drawing (⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E))
    (dualCharts : ∀ e, EdgeChart Q e) (vertexFace : V → Face Q)
    (hinc : ∀ e, positiveChartFace Q e (dualCharts e) = vertexFace (J.left e) ∧
      negativeChartFace Q e (dualCharts e) = vertexFace (J.right e)) :
    Function.Injective vertexFace := by
  classical
  let K : CopiedGraph (Face D) E := ⟨fun e => negativeChartFace D e (charts e),
    fun e => positiveChartFace D e (charts e)⟩
  let H : CopiedGraph (Face Q) E := ⟨fun e => negativeChartFace Q e (dualCharts e),
    fun e => positiveChartFace Q e (dualCharts e)⟩
  letI : Finite (Face Q) := (finite_faces_and_card_le Q dualCharts).1
  letI : Fintype (Face Q) := Fintype.ofFinite (Face Q)
  have hV : Nonempty V := ⟨J.left (Classical.choice ‹Nonempty E›)⟩
  letI : Nonempty V := hV
  have hJ : ∀ x y, J.reaches Finset.univ x y := fun x y =>
    J.reaches_univ_of_supportGraph_reachable (hconn x y)
  obtain ⟨T⟩ := J.nonempty_spanningTree_of_reaches hJ
  have hKt : (Set.univ : Set (Face D)).Nonempty ∧
      (∀ x y, K.reaches T.valᶜ x y) ∧
      ∀ e ∈ T.valᶜ, ¬K.reaches (T.valᶜ.erase e) (K.left e) (K.right e) :=
    (External.finite_plane_tree_complement J D charts Set.univ_nonempty hJ
      (inferInstance : Fintype (Face D)) T.val).mp T.property
  have hK : ∀ x y, K.reaches Finset.univ x y := fun x y =>
    CopiedGraph.TwoCopy.reaches_mono K (Finset.subset_univ _) (hKt.2.1 x y)
  have hHt := (External.finite_plane_tree_complement K Q dualCharts (face_nonempty D) hK
    (inferInstance : Fintype (Face Q)) T.valᶜ).mp hKt
  have hHt' : (Set.univ : Set (Face Q)).Nonempty ∧
      (∀ x y, H.reaches T.val x y) ∧
      ∀ e ∈ T.val, ¬H.reaches (T.val.erase e) (H.left e) (H.right e) := by
    simpa only [compl_compl] using hHt
  let U : H.SpanningTree := ⟨T.val, hHt'⟩
  have hcard : Fintype.card V = Fintype.card (Face Q) :=
    (J.spanningTree_card_add_one T).symm.trans (H.spanningTree_card_add_one U)
  exact ((Fintype.bijective_iff_surjective_and_card vertexFace).mpr
    ⟨vertexFace_surjective Q dualCharts vertexFace hinc, hcard⟩).1

end FiniteAvalanches.Electrical.StatementGeometry
