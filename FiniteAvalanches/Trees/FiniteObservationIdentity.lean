import FiniteAvalanches.Trees.ConnectorObservation
import FiniteAvalanches.Sandpile.TreeLaw

set_option autoImplicit false
open FiniteAvalanches.Trees
open scoped Classical
namespace FiniteAvalanches.Sandpile.WiredTrees

/-- Exact finite source connector-observation event, with every original copy
retained. This is the finite prerequisite of rd:conditional-law, not that law. -/
theorem finite_connector_subset_iff_observation (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (_hne : (graph N).ancestorOf t₀ none S hS ≠ none)
    (t : (graph N).SpanningTree) :
    ((graph N).internalEdges ((graph N).span t₀ S) t₀.val ∪
      (graph N).rootPathCopies t₀ ((graph N).ancestorOf t₀ none S hS) none) ⊆ t.val ↔
    (graph N).span t S = (graph N).span t₀ S ∧
    (graph N).internalEdges ((graph N).span t S) t.val =
      (graph N).internalEdges ((graph N).span t₀ S) t₀.val ∧
    (graph N).ancestorOf t none S hS = (graph N).ancestorOf t₀ none S hS ∧
    (graph N).rootPathCopies t ((graph N).ancestorOf t none S hS) none =
      (graph N).rootPathCopies t₀ ((graph N).ancestorOf t₀ none S hS) none :=
  Multigraph.Observation11.connector_subset_iff_observation (graph N) t₀ t none S hS

end FiniteAvalanches.Sandpile.WiredTrees
