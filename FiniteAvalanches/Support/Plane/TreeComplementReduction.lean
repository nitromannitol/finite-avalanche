import FiniteAvalanches.Support.Plane.TreeComplement
import FiniteAvalanches.External.PlaneDualConnected
import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity

/-!
# The plane tree-complement reduction

Dual connectivity and the finite graph argument reduce the plane tree
complement theorem to the edge-path duality relation.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST
open scoped Classical

/-- The spanning-tree complement equivalence follows from the edge-path duality
relation for all edge sets. -/
theorem tree_complement_iff_of_edge_path_duality
    {V E : Type} [Fintype V] [Fintype E]
    (G : CopiedGraph V E) (D : Drawing G) (charts : ∀ e, EdgeChart D e)
    (hV : (Set.univ : Set V).Nonempty) (hG : ∀ x y, G.reaches Finset.univ x y)
    (finiteFaces : Fintype (Face D))
    (hdual : ∀ (A : Finset E) e, e ∉ A →
      (G.reaches A (G.left e) (G.right e) ↔
        ¬ (⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
          (Aᶜ.erase e) (negativeChartFace D e (charts e))
          (positiveChartFace D e (charts e)))) :
    letI : Fintype (Face D) := finiteFaces
    ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ e ∈ S, ¬ G.reaches (S.erase e) (G.left e) (G.right e)) ↔
      ((Set.univ : Set (Face D)).Nonempty ∧
        (∀ x y, (⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches Sᶜ x y) ∧
        ∀ e ∈ Sᶜ, ¬ (⟨fun e => negativeChartFace D e (charts e),
          fun e => positiveChartFace D e (charts e)⟩ : CopiedGraph (Face D) E).reaches
          (Sᶜ.erase e) (negativeChartFace D e (charts e))
          (positiveChartFace D e (charts e))) := by
  letI : Fintype (Face D) := finiteFaces
  intro S
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    let K : CopiedGraph (Face D) E := ⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩
    have hKgraph : (supportGraph K.left K.right).Preconnected :=
      External.finite_plane_dual_connected G D charts (G.supportGraph_preconnected_of_reaches hG)
    have hK : ∀ x y, K.reaches Finset.univ x y := fun x y =>
      K.reaches_univ_of_supportGraph_reachable (hKgraph x y)
    exact G.spanningTree_compl_iff_of_edge_path_duality K hV (face_nonempty D) hG hK hdual S
  · letI : IsEmpty E := not_nonempty_iff.mp hE
    exact tree_complement_iff_of_isEmpty G D charts hV hG finiteFaces S

end FiniteAvalanches.Electrical.StatementGeometry
