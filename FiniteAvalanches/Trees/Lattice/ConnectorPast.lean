import FiniteAvalanches.Trees.ConnectorPast
import FiniteAvalanches.Trees.ConnectorTree
import FiniteAvalanches.Trees.RootedPathTail
import FiniteAvalanches.Sandpile.TreeLaw

open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The connector roots below the common ancestor are exactly the marked span. -/
theorem connectorRootSupport_inter_descendants_eq_span (t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty) :
    G.connectorRootSupport t r S hS ∩
      G.descendants t r (G.ancestorOf t r S hS) = G.span t S := by
  let hT := G.toSimple_isTree t.property
  let a := G.ancestorOf t r S hS
  have hc := commonAncestor_spec hT r S hS
  have ha : a ∈ G.span t S := commonAncestor_mem_connectingSubtree hT r S hS
  ext x
  constructor
  · rintro ⟨hxR, hxD⟩
    rcases hxR with hxK | hxP
    · exact hxK
    · have hxA : ancestor hT r x a := by
        change x ∈ (path hT r a).support
        rw [path_reverse hT r a, SimpleGraph.Walk.support_reverse, List.mem_reverse]
        exact hxP
      have hxa : x = a := ancestor_antisymm hT hxA hxD
      rw [hxa]
      exact ha
  · intro hxK
    exact ⟨Or.inl hxK, connectingSubtree_subset_descendants hT r S hc.1 hxK⟩

end FiniteAvalanches.Trees.Multigraph

namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Trees.RootedPaths

/-- Removing every observed connector copy leaves the actual ancestor past as
the component attached to the marked zero roots. -/
theorem finite_zero_root_component_eq_past (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    (graph N).oneVertices (t.val \ (graph N).connectorCopies t none S hS)
      ((graph N).span t S) =
        (graph N).past t none ((graph N).ancestorOf t none S hS) hne := by
  have hs : none ∈ (graph N).connectorRootSupport t none S hS :=
    Or.inr (SimpleGraph.Walk.end_mem_support _)
  have ha : (graph N).ancestorOf t none S hS ∈
      (graph N).connectorRootSupport t none S hS :=
    Or.inl (commonAncestor_mem_connectingSubtree
      ((graph N).toSimple_isTree t.property) none S hS)
  have hzero : (graph N).connectorRootSupport t none S hS ∩
      (graph N).past t none ((graph N).ancestorOf t none S hS) hne =
        (graph N).span t S := by
    rw [(graph N).past_eq_descendants,
      (graph N).connectorRootSupport_inter_descendants_eq_span]
  have hdict := Multigraph.oneVertices_sdiff_connector_eq_past (graph N) t
    ((graph N).connectorRootSupport t none S hS)
    ((graph N).connectorCopies t none S hS)
    ((graph N).is_tree_connectorCopies t none S hS)
    ((graph N).connectorCopies_subset t none S hS) hs ha hne
  rw [hzero] at hdict
  exact hdict

end FiniteAvalanches.ConditioningConsumer

#check @FiniteAvalanches.Trees.Multigraph.connectorRootSupport_inter_descendants_eq_span
#print axioms FiniteAvalanches.Trees.Multigraph.connectorRootSupport_inter_descendants_eq_span
#check @FiniteAvalanches.ConditioningConsumer.finite_zero_root_component_eq_past
#print axioms FiniteAvalanches.ConditioningConsumer.finite_zero_root_component_eq_past
