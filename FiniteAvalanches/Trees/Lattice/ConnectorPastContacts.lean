import FiniteAvalanches.Trees.Lattice.ConnectorPast
import FiniteAvalanches.Trees.Lattice.ConnectorAmbientCount
import FiniteAvalanches.Trees.ForestProjection.ColorEvents

open scoped Classical
namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Trees.RootedPaths
noncomputable section

/-- The other connector roots generate exactly the complement of the ancestor past. -/
theorem finite_one_root_component_eq_compl_past (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    (graph N).oneVertices (t.val \ (graph N).connectorCopies t none S hS)
      ((graph N).connectorRootSupport t none S hS \ (graph N).span t S) =
        ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)ᶜ := by
  let G := graph N
  let K := G.span t S
  let R := G.connectorRootSupport t none S hS
  let H := G.connectorCopies t none S hS
  let Γ := R \ K
  have hpart : K ∪ Γ = R := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hdis : Disjoint K Γ := Set.disjoint_left.mpr (fun _ hx hΓ => hΓ.2 hx)
  let F : G.RootedForest R :=
    G.connectorCompletionEquiv R H (G.is_tree_connectorCopies t none S hS)
      ⟨t, G.connectorCopies_subset t none S hS⟩
  let F' : G.RootedForest (K ∪ Γ) := ⟨F.val, by rw [hpart]; exact F.property⟩
  have hcol := G.oneVertices_eq_compl_zeroVertices K Γ hdis F'
  change G.oneVertices (t.val \ H) Γ = (G.oneVertices (t.val \ H) K)ᶜ at hcol
  rw [finite_zero_root_component_eq_past N S hS t hne] at hcol
  exact hcol

/-- The full ambient color-contact count is the actual copied past-boundary count. -/
theorem finite_ambient_contacts_eq_past_admissible (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    ambientColorContacts (graph N) ((graph N).span t S)
      ((graph N).connectorRootSupport t none S hS \ (graph N).span t S)
      (t.val \ (graph N).connectorCopies t none S hS) =
        ((graph N).admissibleEdges
          ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
          ((graph N).span t S)).card := by
  have hcol := finite_one_root_component_eq_compl_past N S hS t hne
  have hK : (graph N).span t S ⊆
      (graph N).past t none ((graph N).ancestorOf t none S hS) hne := by
    rw [(graph N).past_eq_descendants]
    exact connectingSubtree_subset_descendants ((graph N).toSimple_isTree t.property)
      none S (commonAncestor_spec ((graph N).toSimple_isTree t.property) none S hS).1
  unfold ambientColorContacts Multigraph.admissibleEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (((graph N).left e ∈ (graph N).span t S ∧
      (graph N).right e ∈ (graph N).oneVertices
        (t.val \ (graph N).connectorCopies t none S hS)
        ((graph N).connectorRootSupport t none S hS \ (graph N).span t S)) ∨
    ((graph N).right e ∈ (graph N).span t S ∧
      (graph N).left e ∈ (graph N).oneVertices
        (t.val \ (graph N).connectorCopies t none S hS)
        ((graph N).connectorRootSupport t none S hS \ (graph N).span t S))) ↔ _
  rw [hcol, (graph N).admissible_iff_of_subset hK]
  rfl

end
end FiniteAvalanches.ConditioningConsumer

#check @FiniteAvalanches.ConditioningConsumer.finite_one_root_component_eq_compl_past
#print axioms FiniteAvalanches.ConditioningConsumer.finite_one_root_component_eq_compl_past
#check @FiniteAvalanches.ConditioningConsumer.finite_ambient_contacts_eq_past_admissible
#print axioms FiniteAvalanches.ConditioningConsumer.finite_ambient_contacts_eq_past_admissible
