import FiniteAvalanches.Trees.Lattice.ConnectorAmbientCount

namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section

/-- The entire ambient-copy count is the copied boundary count when the actual
one components complement C and K lies in C. -/
theorem ambientColorContacts_eq_admissible {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (K Γ C : Set V) (F : Finset E)
    (hK : K ⊆ C) (hcolor : G.oneVertices F Γ = Cᶜ) :
    ambientColorContacts G K Γ F = (G.admissibleEdges C K).card := by
  have hm (v : V) : (∃ z ∈ Γ, G.reaches F v z) ↔ v ∉ C :=
    Set.ext_iff.mp hcolor v
  unfold ambientColorContacts Multigraph.admissibleEdges
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro e _
  rw [hm, hm]
  exact (G.admissible_iff_of_subset hK e).symm

end
end FiniteAvalanches.ConditioningConsumer
