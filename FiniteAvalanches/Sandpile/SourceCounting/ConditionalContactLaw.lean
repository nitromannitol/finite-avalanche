import FiniteAvalanches.Trees.Lattice.FiniteConditionalContactLaw
import FiniteAvalanches.Trees.Lattice.ObservationRootSites
import FiniteAvalanches.Sandpile.SourceCounting.FiniteObservation

/-! Literal application at b972 rd:conditional-law, with the six manuscript
marks and exact zero roots, strict tail, whole exterior and populated atom. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The actual finite conditional contact-law application on the source marks.
There is no copy-count, observation, restart, or Wilson-law premise. -/
theorem source_marks_conditional_contact_law {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) (D : Set ℕ) :
    markedSites (activeMarks N r) = sourceMarks r ∧
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    roots.zero = (Ksites : Set (Site 2)) ∧
    roots.one = {x | ¬FiniteWired.inBox N x} ∪
      {x | FiniteWired.inBox N x ∧ wiredSite N x ∈ G.orderedAncestorTail t₀ none S hS} ∧
    0 < law N {t | G.copiedConnectorObservation t₀ t none S hS} ∧
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card ∈ D} =
      wilsonColorLaw roots {σ | contacts Ksites σ ∈ D} := by
  refine ⟨markedSites_activeMarks hr hrN, ?_⟩
  dsimp only
  exact ⟨observationRootPair_zero_eq_activeSites N _ _ t₀ hne₀,
    observationRootPair_one_eq_exterior_union_tail N _ _ t₀ hne₀,
    finite_whole_observation_pos N _ _ t₀,
    finite_whole_observation_conditional_contact_law N _ _ t₀ hne₀ D⟩

end
end FiniteAvalanches.ConditioningConsumer
