import FiniteAvalanches.Paper.Revision4498.FiniteApplications

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revision4498
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory Filter
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees.Lattice.PastTail
open FiniteAvalanches.Wilson.Lattice
open scoped Classical BigOperators ENNReal
noncomputable section

theorem outflow_card_le_treeCount_mul_reciprocal {N : ℕ}
    (S : Finset (FiniteWired.Active N))
    (hN : insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites S) :
    (Nat.card {g : Punctured N (origin N) //
      markedSites S ⊆ core g.val ∧ ¬markedSites S ⊆ core (forward g).val} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, WiredTrees.reciprocal N (markedVertices S)
          (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
          ∂WiredTrees.law N := by
  exact FiniteAvalanches.Paper.Revised.outflow_card_le_treeCount_mul_reciprocal S hN

end
end FiniteAvalanches.Paper.Revision4498
