import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths
import FiniteAvalanches.Sandpile.Components.CutSites

namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem finite_source_counting {N r M : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (FiniteWired.law N).real (finiteAvalancheLeaves (origin N) (boxSites M)) ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) +
      ∑ f ∈ sourceEdges N r hrN, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
          ¬cutSites (origin N) t f ⊆ boxSites M} :=
  finite_avalanche_leaves_probability_le_reciprocal_add_cutSites
    (origin N) (activeMarks N r) (boxSites M) (sourceEdges N r hrN)
    (marked_neighborhood hr hrN) (sourceEdges_reaches_marks hr hrN)

end
end FiniteAvalanches.Sandpile.SourceCounting
