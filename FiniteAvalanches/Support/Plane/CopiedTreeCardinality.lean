import FiniteAvalanches.Electrical.Trees.LoopTransport
import FiniteAvalanches.Sandpile.Burning.SpanningTree

/-!
# Cardinality of copied-edge spanning trees

A spanning tree has one fewer edge copy than vertices, even when the ambient
copied graph admits loops and parallel edges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph

open scoped Classical

/-- A spanning tree of a finite copied graph has one fewer copy than vertices. -/
theorem spanningTree_card_add_one {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (T : J.SpanningTree) : T.val.card + 1 = Fintype.card V := by
  classical
  letI : DecidableEq {e : E // J.left e ≠ J.right e} := J.nonloopCopyDec
  let U := J.nonloopTreeEquiv T
  have hc := (J.nonloopGraph.toSimple_isTree U.property).card_edgeFinset
  rw [FiniteAvalanches.Sandpile.Burning.copied_edge_finset, Finset.card_image_of_injOn
    (J.nonloopGraph.edge_injOn_of_is_forest U.property.2.2.2)] at hc
  have hcard : U.val.card = T.val.card := by
    have h := congrArg Finset.card (J.nonloopTreeEquiv_lift T)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
    exact h
  rw [hcard] at hc
  exact hc

end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
