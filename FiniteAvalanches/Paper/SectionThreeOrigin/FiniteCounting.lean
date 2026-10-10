import FiniteAvalanches.Paper.SectionThree.FiniteCounting
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Paper.SectionThreeOrigin
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem finite_counting_origin {M N : ℕ} (_hMN : M ≤ N)
    (S W : Finset (FiniteWired.Active N))
    (F : Finset (FiniteWired.Edge N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S)
    (hSW : S ⊆ W)
    (_hEndpoints : ∀ f ∈ F, (∃ x ∈ W, (WiredTrees.graph N).left f = some x) ∧
      (∃ y ∈ W, (WiredTrees.graph N).right f = some y))
    (hConnected : ∀ x ∈ W, ∀ y ∈ W,
      (WiredTrees.graph N).reaches F (some x) (some y)) :
    (FiniteWired.law N).real (finiteAvalancheLeaves (origin N) (boxSites M)) ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N) +
      ∑ f ∈ F, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
        ¬cutSites (origin N) t f ⊆ boxSites M} := by
  exact FiniteAvalanches.Paper.SectionThree.finite_counting _hMN (origin N) S W F hN hSW
    _hEndpoints hConnected

end
end FiniteAvalanches.Paper.SectionThreeOrigin
