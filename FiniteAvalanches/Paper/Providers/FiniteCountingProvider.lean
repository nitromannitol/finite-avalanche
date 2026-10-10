import FiniteAvalanches.Sandpile.Components.CutSites

namespace FiniteAvalanches.Paper.Providers
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem finite_counting {M N : ℕ} (_hMN : M ≤ N)
    (o : FiniteWired.Active N) (S W : Finset (FiniteWired.Active N))
    (F : Finset (FiniteWired.Edge N))
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S)
    (hSW : S ⊆ W)
    (_hEndpoints : ∀ f ∈ F, (∃ x ∈ W, (WiredTrees.graph N).left f = some x) ∧
      (∃ y ∈ W, (WiredTrees.graph N).right f = some y))
    (hConnected : ∀ x ∈ W, ∀ y ∈ W,
      (WiredTrees.graph N).reaches F (some x) (some y)) :
    (FiniteWired.law N).real (finiteAvalancheLeaves o (boxSites M)) ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices S)
        (marked_vertices_nonempty S (Marked.source_mem_of_marked_neighbors S hN)) t
        ∂WiredTrees.law N) +
      ∑ f ∈ F, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some o) none ∧
        ¬cutSites o t f ⊆ boxSites M} := by
  have ho : o ∈ S := Marked.source_mem_of_marked_neighbors S hN
  have hF : ∀ y ∈ S, (WiredTrees.graph N).reaches F (some o) (some y) :=
    fun y hy => hConnected o (hSW ho) y (hSW hy)
  exact finite_avalanche_leaves_probability_le_reciprocal_add_cutSites
    o S (boxSites M) F hN hF

end
end FiniteAvalanches.Paper.Providers
