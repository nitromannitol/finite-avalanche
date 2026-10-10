import FiniteAvalanches.Trees.ConnectorAtomConditional
import FiniteAvalanches.Trees.ConnectorTree
import FiniteAvalanches.Trees.RootedPathTail
import FiniteAvalanches.Sandpile.TreeLaw

open scoped Classical ENNReal
namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees
noncomputable section

/-- Contacts use every ambient copy, including copies absent from the forest. -/
def ambientColorContacts {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (K Γ : Set V) (F : Finset E) : ℕ :=
  (Finset.univ.filter fun e =>
    (G.left e ∈ K ∧ ∃ z ∈ Γ, G.reaches F (G.right e) z) ∨
    (G.right e ∈ K ∧ ∃ z ∈ Γ, G.reaches F (G.left e) z)).card

/-- The actual marked connector supplies the tree and positivity prerequisites
for its finite conditional ambient-color count. -/
theorem finite_connector_ambient_count (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree) (D : Set ℕ) :
    let G := graph N
    let K := G.span t₀ S
    let R := G.connectorRootSupport t₀ none S hS
    let H := G.connectorCopies t₀ none S hS
    let Γ := R \ K
    ProbabilityTheory.cond G.treeLaw {t | H ⊆ t.val}
        {t | H ⊆ t.val ∧ ambientColorContacts G K Γ (t.val \ H) ∈ D} =
      (Nat.card {F : G.RootedForest R // ambientColorContacts G K Γ F.val ∈ D} : ℝ≥0∞) /
        Nat.card (G.RootedForest R) := by
  dsimp only
  exact Multigraph.treeLaw_cond_connector_count_event (graph N)
    ((graph N).connectorRootSupport t₀ none S hS)
    ((graph N).connectorCopies t₀ none S hS)
    ((graph N).is_tree_connectorCopies t₀ none S hS) t₀
    ((graph N).connectorCopies_subset t₀ none S hS)
    {F | ambientColorContacts (graph N) ((graph N).span t₀ S)
      ((graph N).connectorRootSupport t₀ none S hS \ (graph N).span t₀ S) F ∈ D}

/-- The rootward tail strictly after the finite common ancestor avoids the span. -/
theorem finite_ancestor_tail_disjoint (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree) :
    Disjoint {x | RootedPaths.ancestor ((graph N).toSimple_isTree t.property)
      none x ((graph N).ancestorOf t none S hS) ∧
      x ≠ (graph N).ancestorOf t none S hS} ((graph N).span t S) :=
  RootedPaths.commonAncestor_strict_root_path_disjoint
    ((graph N).toSimple_isTree t.property) none S hS

end
end FiniteAvalanches.ConditioningConsumer

#check @FiniteAvalanches.ConditioningConsumer.ambientColorContacts
#print axioms FiniteAvalanches.ConditioningConsumer.ambientColorContacts
#check @FiniteAvalanches.ConditioningConsumer.finite_connector_ambient_count
#print axioms FiniteAvalanches.ConditioningConsumer.finite_connector_ambient_count
#check @FiniteAvalanches.ConditioningConsumer.finite_ancestor_tail_disjoint
#print axioms FiniteAvalanches.ConditioningConsumer.finite_ancestor_tail_disjoint
