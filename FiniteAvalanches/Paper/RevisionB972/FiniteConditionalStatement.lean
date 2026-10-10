import FiniteAvalanches.Sandpile.SourceCounting.ConditionalContactLaw

namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

theorem finite_conditional_contact_count_law {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) (D : Set ℕ) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card ∈ D} =
      wilsonColorLaw roots {σ | contacts Ksites σ ∈ D} := by
  exact (source_marks_conditional_contact_law hr hrN t₀ hne₀ D).2.2.2.2

end
end FiniteAvalanches.ConditioningConsumer
