import FiniteAvalanches.Trees.Lattice.FiniteContactStatistic

namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The zero roots are exactly the finite literal site set used by contacts. -/
theorem observationRootPair_zero_eq_activeSites (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) :
    (observationRootPair N S hS t₀ hne₀).zero =
      (activeSites N ((graph N).span t₀ S) : Set (Site 2)) := by
  ext y
  constructor
  · intro hy
    have hbox := observationRootPair_zero_inBox N S hS t₀ hne₀ hy
    change wiredSite N y ∈ (graph N).span t₀ S at hy
    rw [wiredSite, dif_pos hbox] at hy
    exact (site_mem_activeSites N _ (FiniteWired.activeOfSite N y hbox)).mpr hy
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    change wiredSite N (FiniteWired.site a) ∈ (graph N).span t₀ S
    rw [wiredSite_active]
    exact (Finset.mem_filter.mp ha).2

end
end FiniteAvalanches.ConditioningConsumer
