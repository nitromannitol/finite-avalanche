import FiniteAvalanches.Trees.ForestColorSourceProvider

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace FiniteAvalanches.Statements
open FiniteAvalanches.Trees

/-- Removing one roots or adding zero roots decreases the one-colored vertex set
under the original copied uniform rooted-forest laws. Both comparisons admit
actual joint monotone couplings. -/
theorem forest_color_monotonicity
    {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (A C : Set V) (hAC : Disjoint A C) (hA : A.Nonempty) (hC : C.Nonempty) :
  (∀ (C' : Set V), C' ⊆ C → C'.Nonempty →
    (∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A ∪ C') | G.oneVertices F.val C' ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C')) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = if G.is_rooted_forest (A ∪ C') S then
        (Nat.card (G.RootedForest (A ∪ C')) : ℝ)⁻¹ else 0) ∧
      (∀ T, ∑ S, q S T = if G.is_rooted_forest (A ∪ C) T then
        (Nat.card (G.RootedForest (A ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, q S T ≠ 0 → G.is_rooted_forest (A ∪ C') S ∧
        G.is_rooted_forest (A ∪ C) T ∧ G.oneVertices S C' ⊆ G.oneVertices T C))) ∧
  (∀ (A' : Set V), A ⊆ A' → Disjoint A' C →
    (∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A' ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A' ∪ C)) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = if G.is_rooted_forest (A' ∪ C) S then
        (Nat.card (G.RootedForest (A' ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∀ T, ∑ S, q S T = if G.is_rooted_forest (A ∪ C) T then
        (Nat.card (G.RootedForest (A ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, q S T ≠ 0 → G.is_rooted_forest (A' ∪ C) S ∧
        G.is_rooted_forest (A ∪ C) T ∧ G.oneVertices S C ⊆ G.oneVertices T C))) := by
  exact G.finite_color_monotonicity_with_couplings hconn A C hAC hA hC

end FiniteAvalanches.Statements
