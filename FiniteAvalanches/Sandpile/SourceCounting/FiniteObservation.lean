import FiniteAvalanches.Trees.Lattice.FiniteObservationCount
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

/-! A genuine application to the manuscript's origin, four neighbors, and
horizontal marked vertex in the actual wired box. -/
namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components
open scoped Classical ENNReal
noncomputable section

/-- The complete source marked set is retained, and its actual copied observation
has the normalized conditional past-count law on the nonsink event. -/
theorem source_marks_and_conditional_past_count {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) (D : Set ℕ) :
    markedSites (activeMarks N r) = sourceMarks r ∧
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := G.span t₀ S
    let R := G.connectorRootSupport t₀ none S hS
    let Γ := R \ K
    ProbabilityTheory.cond (law N) {t | G.copiedConnectorObservation t₀ t none S hS}
        {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
          (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
            (G.span t S)).card ∈ D} =
      (Nat.card {F : G.RootedForest R // ambientColorContacts G K Γ F.val ∈ D} : ℝ≥0∞) /
        Nat.card (G.RootedForest R) := by
  refine ⟨markedSites_activeMarks hr hrN, ?_⟩
  exact finite_whole_observation_past_count N (markedVertices (activeMarks N r))
    (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t₀ hne₀ D

/-- The atom is populated by the observed tree, on the literal source marks. -/
theorem source_whole_observation_positive (N r : ℕ) (t₀ : (graph N).SpanningTree) :
    0 < law N {t | (graph N).copiedConnectorObservation t₀ t none
      (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r))} :=
  finite_whole_observation_pos N (markedVertices (activeMarks N r))
    (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t₀

end
end FiniteAvalanches.ConditioningConsumer
