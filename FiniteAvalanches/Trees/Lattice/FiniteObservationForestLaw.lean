import FiniteAvalanches.Trees.Lattice.FiniteObservationCount
import FiniteAvalanches.Trees.Lattice.ObservationRootPair

/-! The exact finite observation law expressed on the canonical uniform
original-copy rooted-forest carrier of its actual lattice root pair. -/
namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- All source geometry and conditioning are discharged before the remaining
finite-to-lattice Wilson color-law dictionary is needed. -/
theorem finite_whole_observation_uniform_forest_law (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) (D : Set ℕ) :
    let G := graph N
    let K := G.span t₀ S
    let roots := observationRootPair N S hS t₀ hne₀
    ProbabilityTheory.cond (law N)
        {t | G.copiedConnectorObservation t₀ t none S hS}
        {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
          (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
            (G.span t S)).card ∈ D} =
      finiteUniformLaw roots N
        {F | ambientColorContacts G K (wiredOne roots N) F.val ∈ D} := by
  dsimp only
  rw [finiteUniformLaw, FiniteAvalanches.uniformMeasure_apply]
  have h := finite_whole_observation_past_count N S hS t₀ hne₀ D
  dsimp only at h
  rw [← observationRootPair_wiredOne N S hS t₀ hne₀,
    ← observationRootPair_wiredRoots N S hS t₀ hne₀] at h
  exact h

end
end FiniteAvalanches.ConditioningConsumer
