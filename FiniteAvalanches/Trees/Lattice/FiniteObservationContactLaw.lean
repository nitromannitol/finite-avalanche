import FiniteAvalanches.Trees.Lattice.FiniteContactStatistic

/-! The exact copied observation law, now on the literal lattice contact
statistic of every actual forest in its full uniform carrier. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- Both the conditioning and the arbitrary-forest count dictionary are
proved internally; the full original-copy forest denominator is unchanged. -/
theorem finite_whole_observation_contact_forest_law (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) (D : Set ℕ) :
    let G := graph N
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card ∈ D} =
      finiteUniformLaw roots N
        {F | contacts Ksites (finiteForestField roots N F).2 ∈ D} := by
  have he : ({F : FiniteForest (observationRootPair N S hS t₀ hne₀) N |
      ambientColorContacts (graph N) ((graph N).span t₀ S)
        (wiredOne (observationRootPair N S hS t₀ hne₀) N) F.val ∈ D} : Set _) =
      {F | contacts (activeSites N ((graph N).span t₀ S))
        (finiteForestField (observationRootPair N S hS t₀ hne₀) N F).2 ∈ D} := by
    ext F
    simp only [Set.mem_setOf_eq]
    rw [observation_forest_contact_count]
  exact (finite_whole_observation_uniform_forest_law N S hS t₀ hne₀ D).trans
    (congrArg (fun A => finiteUniformLaw (observationRootPair N S hS t₀ hne₀) N A) he)

end
end FiniteAvalanches.ConditioningConsumer
