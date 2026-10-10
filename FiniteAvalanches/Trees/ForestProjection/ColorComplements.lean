import FiniteAvalanches.Trees.ForestProjection.ColorEvents

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The actual increasing zero event has complementary original uniform color probability. -/
theorem sum_uniformRootedForestMass_zeroComplementEvent (A C : Set V)
    (hAC : Disjoint A C) (hR : (A ∪ C).Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (H : Set (Set V)) :
    ∑ F : Finset E, Set.indicator (G.forestZeroComplementEvent A H)
      (G.uniformRootedForestMass (A ∪ C) hR hconn) F =
      1 - (Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A ∪ C)) := by
  rw [G.sum_uniformRootedForestMass_event]
  have he : {F : G.RootedForest (A ∪ C) // F.val ∈ G.forestZeroComplementEvent A H} ≃
      {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∉ H} :=
    Equiv.subtypeEquivRight (G.forestZeroComplementEvent_on_rootedForest A C hAC H)
  rw [Nat.card_congr he]
  have hadd : Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∉ H} +
      Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∈ H} =
        Nat.card (G.RootedForest (A ∪ C)) := by
    simp only [Nat.card_eq_fintype_card]
    have h := Fintype.card_congr (Equiv.sumCompl
      (fun F : G.RootedForest (A ∪ C) => G.oneVertices F.val C ∈ H))
    rw [Fintype.card_sum] at h
    exact (Nat.add_comm _ _).trans h
  have haddReal : (Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∉ H} : ℝ) +
      Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∈ H} =
        Nat.card (G.RootedForest (A ∪ C)) := by exact_mod_cast hadd
  have hne : (Nat.card (G.RootedForest (A ∪ C)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (G.rootedForest_count_pos (A ∪ C) hR hconn)
  apply (div_eq_iff hne).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
  linarith only [haddReal]

end FiniteAvalanches.Trees.Multigraph
