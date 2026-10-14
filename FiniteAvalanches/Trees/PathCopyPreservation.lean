import FiniteAvalanches.Trees.PathCopies

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph.Observation11
open FiniteAvalanches.Trees.RootedPaths SimpleGraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

private theorem original_copy_of_path_edge (t : G.SpanningTree) (x y : V)
    (e : Sym2 V) (he : e ∈ (path (G.toSimple_isTree t.property) x y).edges) :
    ∃ f ∈ G.rootPathCopies t x y, G.edge f = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨f, hf, h | h⟩ := (path (G.toSimple_isTree t.property) x y).adj_of_mem_edges he
    all_goals
      have hfe : G.edge f = s(a,b) := by
        simp only [Multigraph.edge, h.1, h.2] <;> exact Sym2.eq_swap
      refine ⟨f, Finset.mem_filter.mpr ⟨hf, ?_⟩, hfe⟩
      rwa [hfe]

/-- Containing every original path copy preserves the unique path's vertices,
ordered simple edges, and all its original copy IDs. -/
theorem path_data_of_copy_subset (t₀ t : G.SpanningTree) (x y : V)
    (h : G.rootPathCopies t₀ x y ⊆ t.val) :
    (path (G.toSimple_isTree t.property) x y).support =
      (path (G.toSimple_isTree t₀.property) x y).support ∧
    (path (G.toSimple_isTree t.property) x y).edges =
      (path (G.toSimple_isTree t₀.property) x y).edges ∧
    G.rootPathCopies t x y = G.rootPathCopies t₀ x y := by
  let p := path (G.toSimple_isTree t₀.property) x y
  have hm : ∀ e ∈ p.edges, e ∈ (G.toSimple t.val).edgeSet := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := original_copy_of_path_edge G t₀ x y e he
    change (G.toSimple t.val).Adj (G.left f) (G.right f)
    exact ⟨f, h hf, Or.inl ⟨rfl,rfl⟩⟩
  have hp : (p.transfer (G.toSimple t.val) hm).IsPath := by
    rw [Walk.isPath_def, Walk.support_transfer]
    exact (path_isPath (G.toSimple_isTree t₀.property) x y).support_nodup
  have hpath := path_eq (G.toSimple_isTree t.property) _ hp
  have hs : (path (G.toSimple_isTree t.property) x y).support = p.support := by
    rw [hpath, Walk.support_transfer]
  have he : (path (G.toSimple_isTree t.property) x y).edges = p.edges := by
    rw [hpath, Walk.edges_transfer]
  refine ⟨hs, he, ?_⟩
  ext f
  constructor
  · intro hf
    obtain ⟨hft, hfe⟩ := Finset.mem_filter.mp hf
    rw [he] at hfe
    obtain ⟨g, hg, hgf⟩ := original_copy_of_path_edge G t₀ x y (G.edge f) hfe
    have hfg : f = g := G.edge_injOn_of_is_forest t.property.2.2.2 hft (h hg) hgf.symm
    exact hfg ▸ hg
  · intro hf
    obtain ⟨_, hfe⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨h hf, by rwa [he]⟩

                                                                                 
theorem pathCopies_subset_internal (t : G.SpanningTree) (x y : V) (K : Set V)
    (hk : ∀ z ∈ (path (G.toSimple_isTree t.property) x y).support, z ∈ K) :
    G.rootPathCopies t x y ⊆ G.internalEdges K t.val := by
  intro f hf
  obtain ⟨hft,hfe⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_filter.mpr ⟨hft,
    hk _ ((path (G.toSimple_isTree t.property) x y).fst_mem_support_of_mem_edges hfe),
    hk _ ((path (G.toSimple_isTree t.property) x y).snd_mem_support_of_mem_edges hfe)⟩

end
end FiniteAvalanches.Trees.Multigraph.Observation11
